use crate::config::{Args, ShowTriggers};
use crate::context::{ArchContextX, ContextX, ErasureInfo};
use crate::debugger::Debugger;
use crate::spans::{SpanContext, SpanContextX};
use crate::user_filter::UserFilter;
use crate::util::error;
use crate::verus_items::VerusItems;
use crate::profiler::{QuantifierProfiler, Instantiation};
use air::ast::{Command, CommandX, Commands, StmtX, BindX, BinderX, QueryX, DeclX};
use air::context::{QueryContext, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics};
use air::profiler::Profiler;
use rustc_errors::{DiagnosticBuilder, EmissionGuarantee};
use rustc_hir::OwnerNode;
use air::ast::ExprX;
use rustc_interface::interface::Compiler;
use vir::messages::{
    message, note, note_bare, Message, MessageLabel, MessageLevel, MessageX, ToAny,
};

use num_format::{Locale, ToFormattedString};
use rustc_error_messages::MultiSpan;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LOCAL_CRATE;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::Write;
use std::sync::Arc;
use std::time::{Duration, Instant};
use vir::context::GlobalCtx;

use crate::buckets::{Bucket, BucketId};
use vir::ast::{Fun, Function, Ident, Krate, Mode, VirErr, Visibility};
use vir::ast_util::{fun_as_friendly_rust_name, is_visible_to};
use vir::def::{CommandsWithContext, CommandsWithContextX, SnapPos};
use vir::func_to_air::SstMap;
use vir::prelude::PreludeConfig;
use vir::recursion::Node;
use vir::update_cell::UpdateCell;

const RLIMIT_PER_SECOND: u32 = 3000000;

pub(crate) struct Reporter<'tcx> {
    spans: SpanContext,
    compiler_diagnostics: &'tcx rustc_errors::Handler,
    source_map: &'tcx rustc_span::source_map::SourceMap,
}

impl<'tcx> Reporter<'tcx> {
    pub(crate) fn new(spans: &SpanContext, compiler: &'tcx Compiler) -> Self {
        Reporter {
            spans: spans.clone(),
            compiler_diagnostics: compiler.session().diagnostic(),
            source_map: compiler.session().source_map(),
        }
    }
}

/// N.B.: The compiler performs deduplication on diagnostic messages, so reporting an error twice,
/// or emitting the same note twice will be surpressed (even if separated in time by other
/// errors/notes)
impl air::messages::Diagnostics for Reporter<'_> {
    fn report_as(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");

        let mut v: Vec<Span> = Vec::new();
        for sp in &msg.spans {
            if let Some(span) = self.spans.from_air_span(&sp, Some(self.source_map)) {
                v.push(span);
            }
        }
        while let Some(i) = v.iter().position(|a| v.iter().any(|b| a != b && a.contains(*b))) {
            // Remove i in favor of the more specific spans contained by i
            v.remove(i);
        }

        let mut multispan = MultiSpan::from_spans(v);

        for MessageLabel { note, span: sp } in &msg.labels {
            if let Some(span) = self.spans.from_air_span(&sp, Some(self.source_map)) {
                multispan.push_span_label(span, note.clone());
            } else {
                dbg!(&note, &sp.as_string);
            }
        }

        fn emit_with_diagnostic_details<'a, G: EmissionGuarantee>(
            mut diag: DiagnosticBuilder<'a, G>,
            multispan: MultiSpan,
            help: &Option<String>,
        ) {
            diag.span = multispan;
            if let Some(help) = help {
                diag.help(help);
            }
            diag.emit();
        }

        match level {
            MessageLevel::Note => emit_with_diagnostic_details(
                self.compiler_diagnostics.struct_note_without_error(&msg.note),
                multispan,
                &msg.help,
            ),
            MessageLevel::Warning => emit_with_diagnostic_details(
                self.compiler_diagnostics.struct_warn(&msg.note),
                multispan,
                &msg.help,
            ),
            MessageLevel::Error => emit_with_diagnostic_details(
                self.compiler_diagnostics.struct_err(&msg.note),
                multispan,
                &msg.help,
            ),
        }
    }

    fn report(&self, msg: &ArcDynMessage) {
        let vir_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as(msg, vir_msg.level)
    }

    fn report_now(&self, msg: &ArcDynMessage) {
        let vir_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as(msg, vir_msg.level)
    }

    fn report_as_now(&self, msg: &ArcDynMessage, msg_as: MessageLevel) {
        self.report_as(msg, msg_as)
    }
}

/// A reporter message that is being collected by the main thread
pub(crate) enum ReporterMessage {
    Message(usize, Message, MessageLevel, bool),
    // Debugger(),
    Done(usize),
}

/// A reporter that forwards messages on an mpsc channel
pub(crate) struct QueuedReporter {
    bucket_id: usize,
    queue: std::sync::mpsc::Sender<ReporterMessage>,
}

impl QueuedReporter {
    pub(crate) fn new(bucket_id: usize, queue: std::sync::mpsc::Sender<ReporterMessage>) -> Self {
        Self { bucket_id, queue }
    }

    pub(crate) fn done(&self) {
        self.queue.send(ReporterMessage::Done(self.bucket_id)).expect("could not send!");
    }
}

impl air::messages::Diagnostics for QueuedReporter {
    fn report_as(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg: Message =
            msg.clone().downcast().expect("unexpected value in Any -> Message conversion");
        self.queue
            .send(ReporterMessage::Message(self.bucket_id, msg, level, false))
            .expect("could not send the message!");
    }

    fn report_as_now(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg: Message =
            msg.clone().downcast().expect("unexpected value in Any -> Message conversion");
        self.queue
            .send(ReporterMessage::Message(self.bucket_id, msg, level, true))
            .expect("could not send the message!");
    }

    fn report(&self, msg: &ArcDynMessage) {
        let air_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as(msg, air_msg.level)
    }

    fn report_now(&self, msg: &ArcDynMessage) {
        let air_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as_now(msg, air_msg.level)
    }
}

#[derive(Default)]
pub struct BucketStats {
    /// cummulative time in AIR to verify the bucket (this includes SMT solver time)
    pub time_air: Duration,
    /// time to initialize the SMT solver
    pub time_smt_init: Duration,
    /// cummulative time of all SMT queries
    pub time_smt_run: Duration,
    /// total time to verify the bucket
    pub time_verify: Duration,
}

pub struct Verifier {
    /// this is the actual number of threads used for verification. This will be set to the
    /// minimum of the requested threads and the number of buckets to verify
    pub num_threads: usize,
    pub encountered_vir_error: bool,
    pub count_verified: u64,
    pub count_errors: u64,
    pub args: Args,
    pub user_filter: Option<UserFilter>,
    pub erasure_hints: Option<crate::erase::ErasureHints>,

    /// total real time to verify all activated buckets of the crate, including real time for
    /// the parallel bucket verification
    pub time_verify_crate: Duration,
    /// sequential part of the crate verification before parallel verification
    pub time_verify_crate_sequential: Duration,
    /// total sequantial time spent constructing teh VIR
    pub time_vir: Duration,
    /// the time it took convert the VIR from rust AST
    pub time_vir_rust_to_vir: Duration,
    /// time spent in hir when creating the VIR for the crate
    pub time_hir: Duration,
    /// execution times for each bucket run in parallel
    pub bucket_times: HashMap<BucketId, BucketStats>,

    // If we've already created the log directory, this is the path to it:
    created_log_dir: Arc<std::sync::Mutex<Option<std::path::PathBuf>>>,
    vir_crate: Option<Krate>,
    crate_names: Option<Vec<String>>,
    vstd_crate_name: Option<Ident>,
    air_no_span: Option<vir::messages::Span>,
    current_crate_module_ids: Option<Vec<vir::ast::Path>>,
    buckets: HashMap<BucketId, Bucket>,

    // proof debugging purposes
    expand_flag: bool,
    pub expand_targets: Vec<Message>,
}

fn report_chosen_triggers(
    diagnostics: &impl air::messages::Diagnostics,
    chosen: &vir::context::ChosenTriggers,
) {
    diagnostics
        .report(&note(&chosen.span, "automatically chose triggers for this expression:").to_any());

    for (n, trigger) in chosen.triggers.iter().enumerate() {
        let note = format!("  trigger {} of {}:", n + 1, chosen.triggers.len());
        let msg = note_bare(note);
        let msg: ArcDynMessage = trigger.iter().fold(msg, |m, (s, _)| {
            let m: &vir::messages::MessageX =
                m.downcast_ref().expect("unexpected value in Any -> Message conversion");
            m.primary_span(s)
        });
        diagnostics.report(&msg);
    }
}

pub(crate) fn io_vir_err(msg: String, err: std::io::Error) -> VirErr {
    error(format!("{msg}: {err}"))
}

pub fn module_name(module: &vir::ast::Path) -> String {
    module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::")
}

impl Verifier {
    pub fn new(args: Args) -> Verifier {
        Verifier {
            num_threads: 1,
            encountered_vir_error: false,
            count_verified: 0,
            count_errors: 0,
            args,
            user_filter: None,
            erasure_hints: None,
            time_verify_crate: Duration::new(0, 0),
            time_verify_crate_sequential: Duration::new(0, 0),
            time_hir: Duration::new(0, 0),
            time_vir: Duration::new(0, 0),
            time_vir_rust_to_vir: Duration::new(0, 0),

            bucket_times: HashMap::new(),

            created_log_dir: Arc::new(std::sync::Mutex::new(None)),
            vir_crate: None,
            crate_names: None,
            vstd_crate_name: None,
            air_no_span: None,
            current_crate_module_ids: None,
            buckets: HashMap::new(),

            expand_flag: false,
            expand_targets: vec![],
        }
    }

    pub fn from_self(&self) -> Verifier {
        Verifier {
            num_threads: 1,
            encountered_vir_error: false,
            count_verified: 0,
            count_errors: 0,
            args: self.args.clone(),
            user_filter: self.user_filter.clone(),
            erasure_hints: self.erasure_hints.clone(),

            time_verify_crate: Duration::new(0, 0),
            time_verify_crate_sequential: Duration::new(0, 0),
            time_hir: Duration::new(0, 0),
            time_vir: Duration::new(0, 0),
            time_vir_rust_to_vir: Duration::new(0, 0),
            bucket_times: HashMap::new(),
            created_log_dir: self.created_log_dir.clone(),
            vir_crate: self.vir_crate.clone(),
            crate_names: self.crate_names.clone(),
            vstd_crate_name: self.vstd_crate_name.clone(),
            air_no_span: self.air_no_span.clone(),
            current_crate_module_ids: self.current_crate_module_ids.clone(),
            buckets: self.buckets.clone(),
            expand_flag: self.expand_flag,
            expand_targets: self.expand_targets.clone(),
        }
    }

    /// merges two verifiers by summing up times and verified stats from other into self.
    pub fn merge(&mut self, other: Self) {
        self.count_verified += other.count_verified;
        self.count_errors += other.count_errors;
        self.time_vir += other.time_vir;
        self.time_vir_rust_to_vir += other.time_vir_rust_to_vir;
        self.bucket_times.extend(other.bucket_times);
    }

    fn get_bucket<'a>(&'a self, bucket_id: &BucketId) -> &'a Bucket {
        self.buckets.get(bucket_id).expect("expected valid BucketId")
    }

    fn create_log_file(
        &mut self,
        bucket_id_opt: Option<&BucketId>,
        suffix: &str,
    ) -> Result<File, VirErr> {
        let dir_path = {
            let mut created_log_dir =
                self.created_log_dir.lock().expect("failed to lock created_log_dir");
            if let Some(dir_path) = &*created_log_dir {
                dir_path.clone()
            } else {
                let dir = std::path::PathBuf::from(if let Some(dir) = &self.args.log_dir {
                    dir.clone()
                } else {
                    crate::config::LOG_DIR.to_string()
                });
                if dir.exists() {
                    if dir.is_dir() {
                        let entries = std::fs::read_dir(&dir).map_err(|err| {
                            io_vir_err(format!("could not read directory {}", dir.display()), err)
                        })?;
                        for entry in entries {
                            if let Ok(entry) = entry {
                                if entry.path().is_file() {
                                    std::fs::remove_file(entry.path()).map_err(|err| {
                                        io_vir_err(
                                            format!("could not remove file {}", dir.display()),
                                            err,
                                        )
                                    })?;
                                }
                            }
                        }
                    } else {
                        return Err(error(format!(
                            "{} exists and is not a directory",
                            dir.display()
                        )));
                    }
                }
                std::fs::create_dir_all(&dir).map_err(|err| {
                    io_vir_err(format!("could not create directory {}", dir.display()), err)
                })?;
                *created_log_dir = Some(dir.clone());
                dir
            }
        };
        let prefix = match bucket_id_opt {
            None => "crate".to_string(),
            Some(bucket_id) => bucket_id.to_log_string(),
        };
        let path = std::path::Path::new(&dir_path).join(format!("{prefix}{suffix}"));
        match File::create(path.clone()) {
            Ok(file) => Ok(file),
            Err(err) => Err(io_vir_err(format!("could not open file {path:?}"), err)),
        }
    }

    /// Use when we expect our call to Z3 to always succeed
    /// If it doesn't, it's an internal error, not a failure
    /// to validate user code.
    fn check_internal_result(result: ValidityResult) {
        match result {
            ValidityResult::Valid => {}
            ValidityResult::TypeError(err) => {
                panic!("internal error: ill-typed AIR code: {}", err)
            }
            _ => panic!("internal error: decls should not generate queries ({:?})", result),
        }
    }

    fn print_profile_stats(
        &self,
        diagnostics: &impl air::messages::Diagnostics,
        profiler: QuantifierProfiler,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
    ) {
        // let num_quants = profiler.quant_count();
        // let total = profiler.total_instantiations();
        let max = 10;
        // let msg = format!(
        //     "Observed {} total instantiations of user-level quantifiers",
        //     total.to_formatted_string(&Locale::en)
        // );
        // diagnostics.report(&note_bare(&msg).to_any());

        // for (index, cost) in profiler.iter().take(max).enumerate() {
        //     // Report the quantifier
        //     let count = cost.instantiations;
        //     let note = format!(
        //         "Cost * Instantiations: {} (Instantiated {} times - {}% of the total, cost {}) top {} of {} user-level quantifiers.\n",
        //         count * cost.cost,
        //         count.to_formatted_string(&Locale::en),
        //         100 * count / total,
        //         cost.cost,
        //         index + 1,
        //         num_quants
        //     );
        //     let bnd_info = qid_map
        //         .get(&cost.quant)
        //         .expect(format!("Failed to find quantifier {}", cost.quant).as_str());
        //     let mut msg = note_bare(note);

        //     // Summarize the triggers it used
        //     let triggers = &bnd_info.trigs;
        //     for trigger in triggers.iter() {
        //         msg = trigger.iter().fold(msg, |m, e| m.primary_span(&e.span));
        //     }
        //     msg = msg.secondary_label(
        //         &bnd_info.span,
        //         "Triggers selected for this quantifier".to_string(),
        //     );

        //     diagnostics.report(&msg.to_any());
        // }

        // Report potential explicit instantiations to reduce SMT burden
        // ZL TODO: refactor this
        for (index, inst) in profiler.instantiations.iter().enumerate() {
            // Report the quantifier
            let bnd_info = qid_map
                .get(&inst.qid)
                .expect(format!("Failed to find quantifier {}", inst.qid).as_str());

            // // let Some(span) = self.spans.from_air_span(&bnd_info.span.raw_span, Some(self.source_map));
            // // let span = from_raw_span(&bnd_info.span.raw_span);

            // let mut msg = note_bare("Could use explicit quantifier instantiations to improve SMT stability");
            // msg = msg.secondary_label(
            //     &bnd_info.span,
            //     "Try instantiation: <todo>",
            //     // format!("Try instantiation: ({})", inst.terms.connect(", ")),
            // );
            // println!("instantiations: {:?}", inst.terms);
            // diagnostics.report(&msg.to_any());

            println!("instantiations: {:?} {} used: {} {:?}", bnd_info.span.as_string, inst.qid, inst.in_unsat_core.get(), inst.terms);

            // let mut multi = MultiSpan::from_span(span);
            // multi.push_span_label(span, "Quantifier introduced to context here".to_string());
            // diagnostics.span_note_without_error(span, &msg);
            // diagnostics.note_without_error(&format!("Try instantiation: ({})", inst.terms.connect(", ")));
        }
    }

    // TODO: variable capturing
    fn substitute_expr(&self, substitution: &HashMap<String, &air::ast::Expr>, expr: &air::ast::Expr) -> air::ast::Expr {
        match expr.as_ref() {
            ExprX::Var(id) => {
                if let Some(&substitute) = substitution.get(id.as_ref()) {
                    substitute.clone()
                } else {
                    expr.clone()
                }
            },

            ExprX::Const(_) | ExprX::Old(_, _) => expr.clone(),

            ExprX::Apply(id, exprs) =>
                Arc::new(ExprX::Apply(id.clone(), self.substitute_exprs(substitution, exprs))),

            ExprX::ApplyLambda(typ, expr, exprs) =>
                Arc::new(ExprX::ApplyLambda(typ.clone(), self.substitute_expr(substitution, expr), self.substitute_exprs(substitution, exprs))),

            ExprX::Unary(op, expr) =>
                Arc::new(ExprX::Unary(op.clone(), self.substitute_expr(substitution, expr))),

            ExprX::Binary(op, expr1, expr2) =>
                Arc::new(ExprX::Binary(op.clone(), self.substitute_expr(substitution, expr1), self.substitute_expr(substitution, expr2))),

            ExprX::Multi(op, exprs) =>
                Arc::new(ExprX::Multi(op.clone(), self.substitute_exprs(substitution, exprs))),

            ExprX::IfElse(expr1, expr2, expr3) =>
                Arc::new(ExprX::IfElse(
                    self.substitute_expr(substitution, expr1),
                    self.substitute_expr(substitution, expr2),
                    self.substitute_expr(substitution, expr3),
                )),

            ExprX::LabeledAxiom(label, expr) =>
                Arc::new(ExprX::LabeledAxiom(label.clone(), self.substitute_expr(substitution, expr))),

            ExprX::LabeledAssertion(err, expr) =>
                Arc::new(ExprX::LabeledAssertion(err.clone(), self.substitute_expr(substitution, expr))),

            ExprX::Bind(bind, expr) => {
                let mut shadowed_substitution = substitution.clone();

                let new_bind = match bind.as_ref() {
                    BindX::Let(binders) => {
                        let new_binders = binders
                            .iter()
                            .map(|binder|
                                Arc::new(BinderX { name: binder.name.clone(), a: self.substitute_expr(substitution, &binder.a) })
                            )
                            .collect::<Vec<_>>();

                        for binder in binders.iter() {
                            shadowed_substitution.remove(binder.name.as_ref());
                        }

                        Arc::new(BindX::Let(Arc::new(new_binders)))
                    },

                    BindX::Lambda(binders, _, _) => {
                        for binder in binders.iter() {
                            shadowed_substitution.remove(binder.name.as_ref());
                        }
                        bind.clone()
                    },

                    // TODO: what is the SMT encoding of this?
                    BindX::Choose(binders, triggers, qid, expr) => {
                        for binder in binders.iter() {
                            shadowed_substitution.remove(binder.name.as_ref());
                        }

                        Arc::new(BindX::Choose(
                            binders.clone(),
                            triggers.clone(),
                            qid.clone(),
                            self.substitute_expr(substitution, expr),
                        ))
                    },

                    BindX::Quant(quant, binders, triggers, qid) => {
                        for binder in binders.iter() {
                            shadowed_substitution.remove(binder.name.as_ref());
                        }

                        bind.clone()
                    },
                };
                let new_body = self.substitute_expr(&shadowed_substitution, expr);
                Arc::new(ExprX::Bind(new_bind, new_body))
            }
        }
    }

    // Same as above but for Exprs
    fn substitute_exprs(&self, substitution: &HashMap<String, &air::ast::Expr>, exprs: &air::ast::Exprs) -> air::ast::Exprs {
        Arc::new(exprs.iter().map(|expr| self.substitute_expr(substitution, expr)).collect())
    }

    // Replace universally quantified formulas in expr with instantiations specified in instantiations
    fn instantiate_expr(&self, instantiations: &HashMap<String, Vec<Arc<Instantiation>>>, expr: &air::ast::Expr) -> air::ast::Expr {
        match expr.as_ref() {
            ExprX::Const(_) | ExprX::Var(_) | ExprX::Old(_, _) => expr.clone(),

            ExprX::Apply(id, exprs) =>
                Arc::new(ExprX::Apply(id.clone(), self.instantiate_exprs(instantiations, exprs))),

            ExprX::ApplyLambda(typ, expr, exprs) =>
                Arc::new(ExprX::ApplyLambda(typ.clone(), self.instantiate_expr(instantiations, expr), self.instantiate_exprs(instantiations, exprs))),

            ExprX::Unary(op, expr) =>
                Arc::new(ExprX::Unary(op.clone(), self.instantiate_expr(instantiations, expr))),

            ExprX::Binary(op, expr1, expr2) =>
                Arc::new(ExprX::Binary(op.clone(), self.instantiate_expr(instantiations, expr1), self.instantiate_expr(instantiations, expr2))),

            ExprX::Multi(op, exprs) =>
                Arc::new(ExprX::Multi(op.clone(), self.instantiate_exprs(instantiations, exprs))),

            ExprX::IfElse(expr1, expr2, expr3) =>
                Arc::new(ExprX::IfElse(
                    self.instantiate_expr(instantiations, expr1),
                    self.instantiate_expr(instantiations, expr2),
                    self.instantiate_expr(instantiations, expr3),
                )),

            ExprX::LabeledAxiom(label, expr) =>
                Arc::new(ExprX::LabeledAxiom(label.clone(), self.instantiate_expr(instantiations, expr))),

            ExprX::LabeledAssertion(err, expr) =>
                Arc::new(ExprX::LabeledAssertion(err.clone(), self.instantiate_expr(instantiations, expr))),

            ExprX::Bind(bind, body) => {
                let mut new_body = self.instantiate_expr(instantiations, body);

                match bind.as_ref() {
                    BindX::Let(binders) => {
                        let new_binders = binders
                            .iter()
                            .map(|binder|
                                Arc::new(BinderX { name: binder.name.clone(), a: self.instantiate_expr(instantiations, &binder.a) })
                            )
                            .collect::<Vec<_>>();

                        let new_bind = Arc::new(BindX::Let(Arc::new(new_binders)));

                        Arc::new(ExprX::Bind(new_bind, new_body))
                    },

                    BindX::Lambda(_, _, _) => Arc::new(ExprX::Bind(bind.clone(), new_body)),

                    // TODO: what is the SMT encoding of this?
                    BindX::Choose(binders, triggers, qid, expr) => {
                        let new_bind = Arc::new(BindX::Choose(
                            binders.clone(),
                            triggers.clone(),
                            qid.clone(),
                            self.instantiate_expr(instantiations, expr),
                        ));

                        Arc::new(ExprX::Bind(new_bind, new_body))
                    },

                    // If there is no QID, we just ignore this quantifier
                    BindX::Quant(quant, binders, triggers, None) =>
                        Arc::new(ExprX::Bind(bind.clone(), new_body)),

                    BindX::Quant(quant, binders, triggers, Some(qid)) => {
                        if let Some(instantiations) = instantiations.get(qid.as_ref()) {
                            let mut substituted_exprs = Vec::new();

                            for instantiation in instantiations {
                                assert!(instantiation.terms.len() == binders.len());

                                let mut substitution = HashMap::new();
                                for (binder, term) in binders.iter().zip(instantiation.terms.iter()) {
                                    substitution.insert(binder.name.to_string(), term);
                                }

                                let substituted_expr = self.substitute_expr(&substitution, &new_body);
                                substituted_exprs.push(substituted_expr);
                            }

                            Arc::new(ExprX::Multi(air::ast::MultiOp::And, Arc::new(substituted_exprs)))
                        } else {
                            Arc::new(ExprX::Bind(bind.clone(), new_body))
                        }
                    }
                }
            }
        }
    }

    // Same as above but for Exprs
    fn instantiate_exprs(&self, instantiations: &HashMap<String, Vec<Arc<Instantiation>>>, exprs: &air::ast::Exprs) -> air::ast::Exprs {
        Arc::new(exprs.iter().map(|expr| self.instantiate_expr(instantiations, expr)).collect())
    }

    fn instantiate_query_helper(
        &self,
        instantiation_map: &HashMap<String, Vec<Arc<Instantiation>>>,
        new_stmts: &mut Vec<air::ast::Stmt>,
        new_axioms: &mut Vec<air::ast::Decl>,
        stmts: &air::ast::Stmts,
    ) {
        for stmt in stmts.iter() {
            match stmt.as_ref() {
                // If we have a assume statement starting with a universal quantifier
                // look up the corresponding QID in the instantiation map
                // If found, replace it with instantiations
                StmtX::Assume(expr) => {
                    if let ExprX::Bind(bind, body) = expr.as_ref() {
                        if let BindX::Quant(
                            air::ast::Quant::Forall,
                            binders,
                            triggers,
                            Some(qid),
                        ) = bind.as_ref() {
                            if let Some(instantiations) = instantiation_map.get(qid.as_ref()) {
                                println!("used quantifier {:?}, qid {:?}", stmt, qid);
                                for instantiation in instantiations {
                                    assert!(instantiation.terms.len() == binders.len());

                                    let mut substitution = HashMap::new();
                                    for (binder, term) in binders.iter().zip(instantiation.terms.iter()) {
                                        substitution.insert(binder.name.to_string(), term);
                                    }

                                    let substituted_expr = self.substitute_expr(&substitution, &body);
                                    new_axioms.push(Arc::new(DeclX::Axiom(
                                        Arc::new(ExprX::Apply(
                                            // A hack to ask AIR to name these instances
                                            Arc::new("!".to_string()),
                                            Arc::new(vec![
                                                substituted_expr,
                                                Arc::new(ExprX::Var(Arc::new(":named".to_string()))),
                                                // ZL TODO: add a def for this constant
                                                Arc::new(ExprX::Var(Arc::new("named-instance-".to_string() + &instantiation.index.to_string()))),
                                            ])
                                        ))
                                    )));
                                }

                                // continue;
                            } // TODO: should we still keep the quantifiers in this case?
                            else {
                                println!("unused quantifier {:?}, qid {:?}", stmt, qid);
                            }

                            continue;
                            // new_axioms.push(Arc::new(DeclX::Axiom(self.instantiate_expr(instantiations, expr))));
                        }
                    }

                    new_stmts.push(stmt.clone());
                },

                StmtX::Block(stmts) => self.instantiate_query_helper(instantiation_map, new_stmts, new_axioms, stmts),

                StmtX::Assert(span, expr) => new_stmts.push(stmt.clone()),

                // TODO: what do these do?
                StmtX::Havoc(_) => new_stmts.push(stmt.clone()),
                StmtX::Snapshot(_) => new_stmts.push(stmt.clone()),
                StmtX::DeadEnd(_) => new_stmts.push(stmt.clone()),
                StmtX::Switch(_) => new_stmts.push(stmt.clone()),
                StmtX::Assign(_, _) => new_stmts.push(stmt.clone()),
            }
        }
    }

    // Same as above but for Stmt and only instantiates Assume statements
    // and the instantiated Assume statements are converted into Axioms for convenience
    fn instantiate_query(&self, instantiations: &HashMap<String, Vec<Arc<Instantiation>>>, query: &air::ast::Query)
    -> air::ast::Query {

        let stmts = match query.assertion.as_ref() {
            StmtX::Block(stmts) => stmts,
            _ => return query.clone(), // nothing to change
        };

        let mut new_stmts = Vec::new();
        let mut new_axioms = Vec::new();

        self.instantiate_query_helper(instantiations, &mut new_stmts, &mut new_axioms, stmts);

        Arc::new(QueryX {
            local: Arc::new(query.local.iter().cloned().chain(new_axioms.iter().cloned()).collect()),
            assertion: Arc::new(StmtX::Block(Arc::new(new_stmts))),
        })
    }

    /// Check the result of a query that was based on user input.
    /// Success/failure will (eventually) be communicated back to the user.
    /// Returns true if there was at least one Invalid resulting in an error.
    fn check_result_validity(
        &mut self,
        bucket_id: &BucketId,
        reporter: &impl air::messages::Diagnostics,
        source_map: Option<&SourceMap>,
        level: MessageLevel,
        air_context: &mut air::context::Context,
        assign_map: &HashMap<*const vir::messages::Span, HashSet<Arc<std::string::String>>>,
        snap_map: &Vec<(vir::messages::Span, SnapPos)>,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
        command: &Command,
        context: &(&vir::messages::Span, &str),
        is_singular: bool,
        no_pop: bool, // ZL TODO: hacky
    ) -> bool {
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});

        let report_long_running = || {
            let mut counter = 0;
            let report_fn: Box<dyn FnMut(std::time::Duration) -> ()> = Box::new(move |elapsed| {
                let msg =
                    format!("{} has been running for {} seconds", context.1, elapsed.as_secs());
                let msg = if counter % 5 == 0 { note(&context.0, msg) } else { note_bare(msg) };
                reporter.report_now(&msg.to_any());
                counter += 1;
            });
            (std::time::Duration::from_secs(2), report_fn)
        };
        let is_check_valid = matches!(**command, CommandX::CheckValid(_));
        let time0 = Instant::now();
        #[cfg(feature = "singular")]
        let mut result = if !is_singular {
            air_context.command(
                &*message_interface,
                reporter,
                &command,
                QueryContext { report_long_running: Some(&mut report_long_running()) },
            )
        } else {
            crate::singular::check_singular_valid(
                air_context,
                &command,
                context.0,
                QueryContext { report_long_running: Some(&mut report_long_running()) },
            )
        };

        #[cfg(not(feature = "singular"))]
        let mut result = air_context.command(
            &*message_interface,
            reporter,
            &command,
            QueryContext { report_long_running: Some(&mut report_long_running()) },
        );

        let time1 = Instant::now();
        let bucket_time = self.bucket_times.get_mut(bucket_id).expect("bucket time not found");
        bucket_time.time_air += time1 - time0;

        let mut is_first_check = true;
        let mut checks_remaining = self.args.multiple_errors;
        let mut only_check_earlier = false;
        let mut invalidity = false;
        loop {
            match result {
                ValidityResult::Valid => {
                    if (is_check_valid && is_first_check && level == MessageLevel::Error)
                        || is_singular
                    {
                        self.count_verified += 1;
                    }
                    break;
                }
                ValidityResult::TypeError(err) => {
                    panic!("internal error: generated ill-typed AIR code: {}", err);
                }
                ValidityResult::Canceled => {
                    if is_first_check && level == MessageLevel::Error {
                        self.count_errors += 1;
                        invalidity = true;
                    }
                    let mut msg = format!("{}: Resource limit (rlimit) exceeded", context.1);
                    if !self.args.profile && !self.args.profile_all {
                        msg.push_str("; consider rerunning with --profile for more details");
                    }
                    reporter.report(&message(level, msg, &context.0).to_any());
                    // if self.args.profile {
                    //     let profiler = Profiler::new(message_interface, reporter);
                    //     self.print_profile_stats(reporter, profiler, qid_map);
                    // }
                    break;
                }
                ValidityResult::Invalid(air_model, error) => {
                    if air_model.is_none() {
                        // singular_invalid case
                        self.count_errors += 1;
                        reporter.report_as(&error, level);
                        break;
                    }
                    let air_model = air_model.unwrap();

                    if is_first_check && level == MessageLevel::Error {
                        self.count_errors += 1;
                        invalidity = true;
                    }
                    let error: Message = error.downcast().unwrap();
                    if !self.expand_flag || vir::split_expression::is_split_error(&error) {
                        reporter.report_as(&error.clone().to_any(), level);
                    }

                    if level == MessageLevel::Error {
                        if self.args.expand_errors {
                            assert!(!self.expand_flag);
                            self.expand_targets.push(error.clone());
                        }

                        if self.args.debug {
                            if let Some(source_map) = source_map {
                                let mut debugger =
                                    Debugger::new(air_model, assign_map, snap_map, source_map);
                                debugger.start_shell(air_context);
                            } else {
                                reporter.report(&message(
                                    MessageLevel::Warning,
                                    "no source map available for debugger. Try running single threaded.",
                                    &context.0,
                                ).to_any());
                            }
                        }
                    }

                    if self.args.multiple_errors == 0 {
                        break;
                    }
                    is_first_check = false;
                    if !only_check_earlier {
                        checks_remaining -= 1;
                        if checks_remaining == 0 {
                            only_check_earlier = true;
                        }
                    }

                    let time0 = Instant::now();
                    result = air_context.check_valid_again(
                        reporter,
                        only_check_earlier,
                        QueryContext { report_long_running: Some(&mut report_long_running()) },
                    );
                    let time1 = Instant::now();

                    let bucket_time =
                        self.bucket_times.get_mut(bucket_id).expect("bucket time not found");
                    bucket_time.time_air += time1 - time0;
                }
                ValidityResult::UnexpectedOutput(err) => {
                    panic!("unexpected output from solver: {}", err);
                }
            }
        }
        if level == MessageLevel::Error && checks_remaining == 0 {
            let msg = format!(
                "{}: not all errors may have been reported; rerun with a higher value for --multiple-errors to find other potential errors in this function",
                context.1
            );
            reporter.report(&note(context.0, msg).to_any());
        }

        if is_check_valid && !is_singular && !no_pop {
            air_context.finish_query();
        }

        invalidity
    }

    fn run_commands(
        &mut self,
        bucket_id: &BucketId,
        diagnostics: &impl air::messages::Diagnostics,
        air_context: &mut air::context::Context,
        commands: &Vec<Command>,
        comment: &str,
    ) {
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
        }
        for command in commands.iter() {
            let time0 = Instant::now();
            Self::check_internal_result(air_context.command(
                &vir::messages::VirMessageInterface {},
                diagnostics,
                &command,
                Default::default(),
            ));
            let time1 = Instant::now();

            let bucket_time = self.bucket_times.get_mut(bucket_id).expect("bucket time not found");
            bucket_time.time_air += time1 - time0;
        }
    }

    /// Returns true if there was at least one Invalid resulting in an error.
    fn run_commands_queries(
        &mut self,
        reporter: &impl air::messages::Diagnostics,
        source_map: Option<&SourceMap>,
        level: MessageLevel,
        air_context: &mut air::context::Context,
        commands_with_context: CommandsWithContext,
        assign_map: &HashMap<*const vir::messages::Span, HashSet<Arc<String>>>,
        snap_map: &Vec<(vir::messages::Span, SnapPos)>,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
        bucket_id: &BucketId,
        function_name: &Fun,
        comment: &str,
        desc_prefix: Option<&str>,
        no_pop: bool,
    ) -> bool {
        let user_filter = self.user_filter.as_ref().unwrap();
        let includes_function = user_filter.includes_function(function_name);
        if !includes_function {
            return false;
        }

        let mut invalidity = false;
        let CommandsWithContextX { span, desc, commands, prover_choice, skip_recommends: _ } =
            &*commands_with_context;
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
            air_context.comment(&span.as_string);
        }
        let desc = desc_prefix.unwrap_or("").to_string() + desc;
        for command in commands.iter() {
            let result_invalidity = self.check_result_validity(
                bucket_id,
                reporter,
                source_map,
                level,
                air_context,
                assign_map,
                snap_map,
                qid_map,
                &command,
                &(span, &desc),
                *prover_choice == vir::def::ProverChoice::Singular,
                no_pop,
            );
            invalidity = invalidity || result_invalidity;
        }

        invalidity
    }

    fn new_air_context_with_prelude<'m>(
        &mut self,
        message_interface: Arc<dyn air::messages::MessageInterface>,
        diagnostics: &impl air::messages::Diagnostics,
        bucket_id: &BucketId,
        query_function_path_counter: Option<(&vir::ast::Path, usize)>,
        is_rerun: bool,
        prelude_config: vir::prelude::PreludeConfig,
    ) -> Result<air::context::Context, VirErr> {
        let mut air_context = air::context::Context::new(message_interface.clone());
        air_context.set_ignore_unexpected_smt(self.args.ignore_unexpected_smt);
        air_context.set_debug(self.args.debug);
        air_context.set_profile(self.args.profile);
        air_context.set_profile_all(self.args.profile_all);

        let rerun_msg = if is_rerun { "_rerun" } else { "" };
        let count_msg = query_function_path_counter
            .map(|(_, ref c)| format!("_{:02}", c))
            .unwrap_or("".to_string());
        let expand_msg = if self.expand_flag { "_expand" } else { "" };

        if self.args.log_all || self.args.log_air_initial {
            let file = self.create_log_file(
                Some(bucket_id),
                format!(
                    "{}{}{}{}",
                    rerun_msg,
                    count_msg,
                    expand_msg,
                    crate::config::AIR_INITIAL_FILE_SUFFIX
                )
                .as_str(),
            )?;
            air_context.set_air_initial_log(Box::new(file));
        }
        if self.args.log_all || self.args.log_air_final {
            let file = self.create_log_file(
                Some(bucket_id),
                format!(
                    "{}{}{}{}",
                    rerun_msg,
                    count_msg,
                    expand_msg,
                    crate::config::AIR_FINAL_FILE_SUFFIX
                )
                .as_str(),
            )?;
            air_context.set_air_final_log(Box::new(file));
        }
        if self.args.log_all || self.args.log_smt {
            let file = self.create_log_file(
                Some(bucket_id),
                format!(
                    "{}{}{}{}",
                    rerun_msg,
                    count_msg,
                    expand_msg,
                    crate::config::SMT_FILE_SUFFIX
                )
                .as_str(),
            )?;
            air_context.set_smt_log(Box::new(file));
        }

        // air_recommended_options causes AIR to apply a preset collection of Z3 options
        air_context.set_z3_param("air_recommended_options", "true");
        air_context.set_rlimit(self.args.rlimit.saturating_mul(RLIMIT_PER_SECOND));
        for (option, value) in self.args.smt_options.iter() {
            air_context.set_z3_param(&option, &value);
        }

        air_context.blank_line();
        air_context.comment("Prelude");
        for command in vir::context::Ctx::prelude(prelude_config).iter() {
            Self::check_internal_result(air_context.command(
                &*message_interface,
                diagnostics,
                &command,
                Default::default(),
            ));
        }

        air_context.blank_line();
        air_context.comment(&("MODULE '".to_string() + &bucket_id.friendly_name() + "'"));

        Ok(air_context)
    }

    fn new_air_context_with_bucket_context<'m>(
        &mut self,
        message_interface: Arc<dyn air::messages::MessageInterface>,
        ctx: &vir::context::Ctx,
        diagnostics: &impl air::messages::Diagnostics,
        bucket_id: &BucketId,
        function_path: &vir::ast::Path,
        datatype_commands: Commands,
        assoc_type_decl_commands: Commands,
        trait_commands: Commands,
        assoc_type_impl_commands: Commands,
        function_decl_commands: Arc<Vec<(Commands, String)>>,
        function_spec_commands: Arc<Vec<(Commands, String)>>,
        function_axiom_commands: Arc<Vec<(Commands, String)>>,
        is_rerun: bool,
        context_counter: usize,
        span: &vir::messages::Span,
    ) -> Result<air::context::Context, VirErr> {
        let mut air_context = self.new_air_context_with_prelude(
            message_interface.clone(),
            diagnostics,
            bucket_id,
            Some((function_path, context_counter)),
            is_rerun,
            PreludeConfig { arch_word_bits: self.args.arch_word_bits },
        )?;

        // Write the span of spun-off query
        air_context.comment(&span.as_string);
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(
                &*message_interface,
                diagnostics,
                &command,
                Default::default(),
            ));
        }

        // set up bucket context
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &assoc_type_decl_commands,
            &("Associated-Type-Decls".to_string()),
        );
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &datatype_commands,
            &("Datatypes".to_string()),
        );
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &trait_commands,
            &("Traits".to_string()),
        );
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &assoc_type_impl_commands,
            &("Associated-Type-Impls".to_string()),
        );
        for commands in &*function_decl_commands {
            self.run_commands(bucket_id, diagnostics, &mut air_context, &commands.0, &commands.1);
        }
        for commands in &*function_spec_commands {
            self.run_commands(bucket_id, diagnostics, &mut air_context, &commands.0, &commands.1);
        }
        for commands in &*function_axiom_commands {
            self.run_commands(bucket_id, diagnostics, &mut air_context, &commands.0, &commands.1);
        }
        Ok(air_context)
    }

    // Verify a single bucket
    fn verify_bucket(
        &mut self,
        reporter: &impl air::messages::Diagnostics,
        krate: &Krate,
        source_map: Option<&SourceMap>,
        bucket_id: &BucketId,
        ctx: &mut vir::context::Ctx,
        quant_profiler: &mut QuantifierProfiler,
    ) -> Result<(Duration, Duration), VirErr> {
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});

        let mut air_context = self.new_air_context_with_prelude(
            message_interface.clone(),
            reporter,
            bucket_id,
            None,
            false,
            PreludeConfig { arch_word_bits: self.args.arch_word_bits },
        )?;
        if self.args.solver_version_check {
            air_context
                .set_expected_solver_version(crate::consts::EXPECTED_SOLVER_VERSION.to_string());
        }

        let mut spunoff_time_smt_init = Duration::ZERO;
        let mut spunoff_time_smt_run = Duration::ZERO;

        let module = &ctx.module();
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(
                &*message_interface,
                reporter,
                &command,
                Default::default(),
            ));
        }

        let assoc_type_decl_commands =
            vir::assoc_types_to_air::assoc_type_decls_to_air(ctx, &krate.traits);
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &assoc_type_decl_commands,
            &("Associated-Type-Decls".to_string()),
        );

        let datatype_commands = vir::datatype_to_air::datatypes_and_primitives_to_air(
            ctx,
            &krate
                .datatypes
                .iter()
                .cloned()
                .filter(|d| is_visible_to(&d.x.visibility, module))
                .collect(),
        );
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &datatype_commands,
            &("Datatypes".to_string()),
        );

        let trait_commands = vir::traits::traits_to_air(ctx, &krate);
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &trait_commands,
            &("Traits".to_string()),
        );

        let assoc_type_impl_commands =
            vir::assoc_types_to_air::assoc_type_impls_to_air(ctx, &krate.assoc_type_impls);
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &assoc_type_impl_commands,
            &("Associated-Type-Impls".to_string()),
        );

        let mk_fun_ctx = |f: &Function, checking_spec_preconditions: bool| {
            Some(vir::context::FunctionCtx {
                checking_spec_preconditions,
                checking_spec_preconditions_for_non_spec: checking_spec_preconditions
                    && f.x.mode != Mode::Spec,
                module_for_chosen_triggers: f.x.owning_module.clone(),
                current_fun: f.x.name.clone(),
            })
        };

        let mut function_decl_commands = vec![];
        let mut function_spec_commands = vec![];
        let mut function_axiom_commands = vec![];

        // Declare the function symbols
        for function in &krate.functions {
            ctx.fun = mk_fun_ctx(&function, false);
            if !is_visible_to(&function.x.visibility, module) || function.x.attrs.is_decrease_by {
                continue;
            }
            let commands = vir::func_to_air::func_name_to_air(ctx, reporter, &function)?;
            let comment =
                "Function-Decl ".to_string() + &fun_as_friendly_rust_name(&function.x.name);
            self.run_commands(bucket_id, reporter, &mut air_context, &commands, &comment);
            function_decl_commands.push((commands.clone(), comment.clone()));
        }
        ctx.fun = None;

        // Collect function definitions
        let mut funs: HashMap<Fun, (Function, Visibility)> = HashMap::new();
        for function in &krate.functions {
            assert!(!funs.contains_key(&function.x.name));
            let vis = function.x.visibility.clone();
            if !is_visible_to(&vis, module) || function.x.attrs.is_decrease_by {
                continue;
            }
            let restricted_to = if function.x.publish.is_none() {
                // private to owning_module
                function.x.owning_module.clone()
            } else {
                // public
                None
            };
            let vis_abs = Visibility { restricted_to, ..vis };
            funs.insert(function.x.name.clone(), (function.clone(), vis_abs));
        }

        // For spec functions, check termination and declare consequence axioms.
        // For proof/exec functions, declare requires/ensures.
        // Declare them in SCC (strongly connected component) sorted order so that
        // termination checking precedes consequence axioms for each SCC.
        let mut fun_axioms: HashMap<Fun, Commands> = HashMap::new();
        let mut fun_ssts = UpdateCell::new(HashMap::new());
        for scc in &ctx.global.func_call_sccs.as_ref().clone() {
            let scc_nodes = ctx.global.func_call_graph.get_scc_nodes(scc);
            let mut scc_fun_nodes: Vec<Fun> = Vec::new();
            for node in scc_nodes.into_iter() {
                match node {
                    Node::Fun(f) => scc_fun_nodes.push(f),
                    _ => {}
                }
            }
            // Declare requires/ensures
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let (function, _vis_abs) = &funs[f];

                ctx.fun = mk_fun_ctx(&function, false);
                let decl_commands =
                    vir::func_to_air::func_decl_to_air(ctx, reporter, &fun_ssts, &function)?;
                ctx.fun = None;
                let comment = "Function-Specs ".to_string() + &fun_as_friendly_rust_name(f);
                self.run_commands(bucket_id, reporter, &mut air_context, &decl_commands, &comment);
                function_spec_commands.push((decl_commands.clone(), comment.clone()));
            }

            // Check termination
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let (function, vis_abs) = &funs[f];

                ctx.fun = mk_fun_ctx(&function, false);
                let bucket = self.get_bucket(bucket_id);
                let not_verifying_owning_bucket = !bucket.contains(&function.x.name);

                let (decl_commands, check_commands, new_fun_ssts) =
                    vir::func_to_air::func_axioms_to_air(
                        ctx,
                        reporter,
                        fun_ssts,
                        &function,
                        is_visible_to(&vis_abs, module),
                        not_verifying_owning_bucket,
                    )?;
                fun_ssts = new_fun_ssts;
                fun_axioms.insert(f.clone(), decl_commands);
                ctx.fun = None;

                if not_verifying_owning_bucket {
                    continue;
                }
                let invalidity = self.run_commands_queries(
                    reporter,
                    source_map,
                    MessageLevel::Error,
                    &mut air_context,
                    Arc::new(CommandsWithContextX {
                        span: function.span.clone(),
                        desc: "termination proof".to_string(),
                        commands: check_commands,
                        prover_choice: vir::def::ProverChoice::DefaultProver,
                        skip_recommends: false,
                    }),
                    &HashMap::new(),
                    &vec![],
                    &ctx.global.qid_map.borrow(),
                    bucket_id,
                    &function.x.name,
                    &("Function-Termination ".to_string() + &fun_as_friendly_rust_name(f)),
                    Some("function termination: "),
                    false,
                );
                let check_recommends = function.x.attrs.check_recommends;
                if (invalidity && !self.args.no_auto_recommends_check) || check_recommends {
                    // Rerun failed query to report possible recommends violations
                    // or (optionally) check recommends for spec function bodies
                    ctx.fun = mk_fun_ctx(&function, true);
                    let (commands, snap_map, new_fun_ssts) = vir::func_to_air::func_def_to_air(
                        ctx,
                        reporter,
                        fun_ssts,
                        &function,
                        vir::func_to_air::FuncDefPhase::CheckingSpecs,
                        true,
                    )?;
                    ctx.fun = None;
                    fun_ssts = new_fun_ssts;
                    let level = if invalidity { MessageLevel::Note } else { MessageLevel::Warning };
                    let s = "Function-Decl-Check-Recommends ";
                    for command in commands.iter().map(|x| &*x) {
                        self.run_commands_queries(
                            reporter,
                            source_map,
                            level,
                            &mut air_context,
                            command.clone(),
                            &HashMap::new(),
                            &snap_map,
                            &ctx.global.qid_map.borrow(),
                            bucket_id,
                            &function.x.name,
                            &(s.to_string() + &fun_as_friendly_rust_name(&function.x.name)),
                            Some("recommends check: "),
                            false,
                        );
                    }
                }
            }

            // Declare consequence axioms
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let decl_commands = &fun_axioms[f];
                let comment = "Function-Axioms ".to_string() + &fun_as_friendly_rust_name(f);
                self.run_commands(bucket_id, reporter, &mut air_context, &decl_commands, &comment);
                function_axiom_commands.push((decl_commands.clone(), comment.clone()));
                funs.remove(f);
            }
        }
        assert!(funs.len() == 0);

        let function_decl_commands = Arc::new(function_decl_commands);
        let function_spec_commands = Arc::new(function_spec_commands);
        let function_axiom_commands = Arc::new(function_axiom_commands);
        // Create queries to check the validity of proof/exec function bodies
        let no_auto_recommends_check = self.args.no_auto_recommends_check;
        let expand_errors_check = self.args.expand_errors;
        self.expand_targets = vec![];
        for function in &krate.functions {
            let bucket = self.get_bucket(bucket_id);
            if !bucket.contains(&function.x.name) {
                continue;
            }
            let check_validity = &mut |recommends_rerun: bool,
                                       expands_rerun: bool,
                                       mut fun_ssts: SstMap|
             -> Result<(bool, SstMap), VirErr> {
                let mut spinoff_context_counter = 1;
                ctx.fun = mk_fun_ctx(&function, recommends_rerun);
                ctx.expand_flag = expands_rerun;
                self.expand_flag = expands_rerun;
                if expands_rerun {
                    ctx.debug_expand_targets = self.expand_targets.drain(..).collect();
                }
                let (commands, snap_map, new_fun_ssts) = vir::func_to_air::func_def_to_air(
                    ctx,
                    reporter,
                    fun_ssts,
                    &function,
                    vir::func_to_air::FuncDefPhase::CheckingProofExec,
                    recommends_rerun,
                )?;
                fun_ssts = new_fun_ssts;
                let level = if recommends_rerun || expands_rerun {
                    MessageLevel::Note
                } else {
                    MessageLevel::Error
                };
                let s =
                    if recommends_rerun { "Function-Check-Recommends " } else { "Function-Def " };

                let mut function_invalidity = false;
                for command in commands.iter().map(|x| &*x) {
                    let CommandsWithContextX {
                        span,
                        desc: _,
                        commands: _,
                        prover_choice,
                        skip_recommends,
                    } = &**command;
                    if recommends_rerun && *skip_recommends {
                        continue;
                    }
                    if *prover_choice == vir::def::ProverChoice::Singular {
                        #[cfg(not(feature = "singular"))]
                        panic!(
                            "Found singular command when Verus is compiled without Singular feature"
                        );

                        #[cfg(feature = "singular")]
                        if air_context.singular_log.is_none() {
                            let file = self.create_log_file(
                                Some(bucket_id),
                                crate::config::SINGULAR_FILE_SUFFIX,
                            )?;
                            air_context.singular_log = Some(file);
                        }
                    }
                    let mut spinoff_z3_context;
                    let do_spinoff = (*prover_choice == vir::def::ProverChoice::Nonlinear)
                        || (*prover_choice == vir::def::ProverChoice::BitVector);
                    let query_air_context = if do_spinoff {
                        spinoff_z3_context = self.new_air_context_with_bucket_context(
                            message_interface.clone(),
                            ctx,
                            reporter,
                            bucket_id,
                            &(function.x.name).path,
                            datatype_commands.clone(),
                            assoc_type_decl_commands.clone(),
                            trait_commands.clone(),
                            assoc_type_impl_commands.clone(),
                            function_decl_commands.clone(),
                            function_spec_commands.clone(),
                            function_axiom_commands.clone(),
                            recommends_rerun,
                            spinoff_context_counter,
                            &span,
                        )?;
                        // for bitvector, only one query, no push/pop
                        if *prover_choice == vir::def::ProverChoice::BitVector {
                            spinoff_z3_context.disable_incremental_solving();
                        }
                        spinoff_context_counter += 1;
                        &mut spinoff_z3_context
                    } else {
                        &mut air_context
                    };
                    let desc_prefix = recommends_rerun.then(|| "recommends check: ");
                    
                    println!("\ncommands {:?} {:?}\n", function.x.name.path, command.commands);

                    let command_invalidity = self.run_commands_queries(
                        reporter,
                        source_map,
                        level,
                        query_air_context,
                        command.clone(),
                        &HashMap::new(),
                        &snap_map,
                        &ctx.global.qid_map.borrow(),
                        bucket_id,
                        &function.x.name,
                        &(s.to_string() + &fun_as_friendly_rust_name(&function.x.name)),
                        desc_prefix,
                        false,
                    );
                    if do_spinoff {
                        let (time_smt_init, time_smt_run) = query_air_context.get_time();
                        spunoff_time_smt_init += time_smt_init;
                        spunoff_time_smt_run += time_smt_run;
                    }

                    // ZL TODO: Gather more profiling information about the QI
                    // by running the command again with explicit instantiations
                    let new_instantiations = quant_profiler.process_function(&function.x.name.path);
                    let mut organized_instantiations = HashMap::new();

                    for new_instantiation in new_instantiations {
                        if !organized_instantiations.contains_key(&new_instantiation.qid) {
                            organized_instantiations.insert(new_instantiation.qid.to_string(), Vec::new());
                        }

                        organized_instantiations.get_mut(&new_instantiation.qid).expect("").push(new_instantiation.clone());

                        // println!("found new instantiation {:?}", new_instantiation.clone());
                    }

                    let instantiated_command = Arc::new(CommandsWithContextX {
                        span: command.span.clone(),
                        desc: command.desc.clone(),
                        commands: Arc::new(command.commands.iter()
                            .map(|cmd| match cmd.as_ref() {
                                CommandX::CheckValid(query) =>
                                    Arc::new(CommandX::CheckValid(self.instantiate_query(&organized_instantiations, query))),

                                _ => cmd.clone(),
                            })
                            .collect()),
                        prover_choice: command.prover_choice,
                        skip_recommends: command.skip_recommends,
                    });
                    println!("\ninstantiated commands {:?} {:?}\n", function.x.name.path, instantiated_command.commands);

                    println!("\nrunning instantiated commands for unsat core");
                    let instantiated_command_invalidity = self.run_commands_queries(
                        reporter,
                        source_map,
                        MessageLevel::Error,
                        query_air_context,
                        instantiated_command.clone(),
                        &HashMap::new(),
                        &snap_map,
                        &ctx.global.qid_map.borrow(),
                        bucket_id,
                        &function.x.name,
                        &(s.to_string() + &fun_as_friendly_rust_name(&function.x.name) + " (QI profiler)"),
                        desc_prefix,
                        true, // pop later! (very hacky)
                    );
                    // println!("instantiated commands invalidity: {} {}", instantiated_command_invalidity, command_invalidity);

                    if instantiated_command_invalidity != command_invalidity {
                        panic!("instantiated command leads to inconsistent validity results: {} {}", instantiated_command_invalidity, command_invalidity);
                    }

                    // Query the prover for unsat core
                    let result = query_air_context.command(
                        &*message_interface,
                        reporter,
                        &Arc::new(CommandX::GetUnsatCore),
                        Default::default(),
                    );
                    match result {
                        ValidityResult::UnexpectedOutput(unsat_core_string) => {
                            println!("unsat core: {}", unsat_core_string);

                            for instance_name in unsat_core_string.split(' ') {
                                if instance_name.starts_with("named-instance-") {
                                    let instance_index = instance_name.chars().skip("named-instance-".len()).collect::<String>().parse::<usize>().unwrap();
                                    quant_profiler.mark_instance_used(instance_index);
                                    println!("instance {} is used", instance_index);
                                }
                            }
                        },

                        _ => {
                            println!("failed to get unsat core: {:?}", result);
                        }
                    }

                    query_air_context.finish_query();

                    function_invalidity = function_invalidity || command_invalidity;
                }
                Ok((function_invalidity, fun_ssts))
            };
            let (function_invalidity, new_fun_ssts) = check_validity(false, false, fun_ssts)?;
            fun_ssts = new_fun_ssts;
            if function_invalidity && expand_errors_check {
                fun_ssts = check_validity(false, true, fun_ssts)?.1;
            }
            if function_invalidity && !no_auto_recommends_check {
                fun_ssts = check_validity(true, false, fun_ssts)?.1;
            }
        }
        ctx.fun = None;

        let (time_smt_init, time_smt_run) = air_context.get_time();

        Ok((time_smt_init + spunoff_time_smt_init, time_smt_run + spunoff_time_smt_run))
    }

    fn verify_bucket_outer(
        &mut self,
        reporter: &impl air::messages::Diagnostics,
        krate: &Krate,
        source_map: Option<&SourceMap>,
        bucket_id: &BucketId,
        mut global_ctx: vir::context::GlobalCtx,
        quant_profiler: &mut QuantifierProfiler,
    ) -> Result<vir::context::GlobalCtx, VirErr> {
        let time_verify_start = Instant::now();

        self.bucket_times.insert(bucket_id.clone(), Default::default());

        let bucket_name = bucket_id.friendly_name();
        let user_filter = self.user_filter.as_ref().unwrap();
        if self.args.trace || !user_filter.is_everything() {
            let functions_msg =
                if user_filter.is_function_filter() { " (selected functions)" } else { "" };
            reporter
                .report_now(&note_bare(format!("verifying {bucket_name}{functions_msg}")).to_any());
        }

        let (pruned_krate, mono_abstract_datatypes, lambda_types, bound_traits) =
            vir::prune::prune_krate_for_module(
                &krate,
                bucket_id.module(),
                bucket_id.function(),
                &self.vstd_crate_name,
            );
        let mut ctx = vir::context::Ctx::new(
            &pruned_krate,
            global_ctx,
            bucket_id.module().clone(),
            mono_abstract_datatypes,
            lambda_types,
            bound_traits,
            self.args.debug,
        )?;
        let poly_krate = vir::poly::poly_krate_for_module(&mut ctx, &pruned_krate);
        if self.args.log_all || self.args.log_vir_poly {
            let mut file =
                self.create_log_file(Some(&bucket_id), crate::config::VIR_POLY_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &poly_krate, &self.args.vir_log_option);
        }

        let (time_smt_init, time_smt_run) =
            self.verify_bucket(reporter, &poly_krate, source_map, bucket_id, &mut ctx, quant_profiler)?;

        global_ctx = ctx.free();

        let time_verify_end = Instant::now();

        let mut time_bucket = self.bucket_times.get_mut(bucket_id).expect("bucket should exist");
        time_bucket.time_smt_init = time_smt_init;
        time_bucket.time_smt_run = time_smt_run;
        time_bucket.time_verify = time_verify_end - time_verify_start;

        if self.args.trace {
            reporter.report_now(
                &note_bare(format!("done with {:}", bucket_id.friendly_name())).to_any(),
            );
        }

        Ok(global_ctx)
    }

    // Verify one or more modules in a crate
    fn verify_crate_inner(
        &mut self,
        compiler: &Compiler,
        spans: &SpanContext,
    ) -> Result<(), VirErr> {
        let time_verify_sequential_start = Instant::now();

        let reporter = Reporter::new(spans, compiler);
        let krate = self.vir_crate.clone().expect("vir_crate should be initialized");
        let air_no_span = self.air_no_span.clone().expect("air_no_span should be initialized");

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate(&krate);

        let interpreter_log_file =
            Arc::new(std::sync::Mutex::new(if self.args.log_all || self.args.log_interpreter {
                Some(self.create_log_file(None, crate::config::INTERPRETER_FILE_SUFFIX)?)
            } else {
                None
            }));
        let mut global_ctx = vir::context::GlobalCtx::new(
            &krate,
            air_no_span.clone(),
            self.args.rlimit,
            interpreter_log_file,
            self.vstd_crate_name.clone(),
            self.args.arch_word_bits,
        )?;
        vir::recursive_types::check_traits(&krate, &global_ctx)?;
        let krate = vir::ast_simplify::simplify_krate(&mut global_ctx, &krate)?;

        if self.args.log_all || self.args.log_vir_simple {
            let mut file = self.create_log_file(None, crate::config::VIR_SIMPLE_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &krate, &self.args.vir_log_option);
        }

        let mut quant_profiler = QuantifierProfiler::new();

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate_simplified(&krate);

        // The 'user_filter' handles the filter provided on the command line
        // (--verify-module, --verify-funciton, etc.)
        // Whereas the 'buckets' are the way we group obligations for parallelizing
        // and context pruning.
        // Buckets usually fall along module boundaries, but the user can create
        // more buckets using #[spinoff_prover] can create
        // more buckets.
        //
        // For example, suppose module M has functions a, b, c, d.
        // with a and b both marked spinoff_prover.
        // Then we would create buckets {a}, {b}, and {c, d}.
        //
        // We don't need to create any buckets for stuff that we don't intend
        // to verify. However, we can't shrink any existing bucket based on the
        // the user_filter.
        // For example, suppose the user includes a filter `--verify-function c`.
        // Then, we can drop the {a} and {b} buckets.
        // HOWEVER, we still create the entire {c, d} bucket.
        // We skip the d-related queries when we get to them; however, we still
        // include d in the bucket because d influences the context.
        // Our objective is to generate the same queries for c that we'd otherwise
        // get if we were running verification on the whole module.
        // If the user wants to reduce the context used for d, then they can use
        // the spinoff_prover attribute.

        let user_filter = self.user_filter.as_ref().unwrap();
        let module_ids_to_verify: Vec<vir::ast::Path> = {
            let current_crate_module_ids = self
                .current_crate_module_ids
                .as_ref()
                .expect("current_crate_module_ids should be initialized");
            user_filter.filter_module_ids(current_crate_module_ids)?
        };
        let buckets = crate::buckets::get_buckets(&krate, &module_ids_to_verify);
        let buckets = user_filter.filter_buckets(buckets);
        let bucket_ids: Vec<BucketId> = buckets.iter().map(|p| p.0.clone()).collect();
        self.buckets = buckets.into_iter().collect();

        let time_verify_sequential_end = Instant::now();
        self.time_verify_crate_sequential =
            time_verify_sequential_end - time_verify_sequential_start;

        let source_map = compiler.session().source_map();

        self.num_threads = std::cmp::min(self.args.num_threads, bucket_ids.len());
        if self.num_threads > 1 {
            panic!("threading disabled");
        //     // create the multiple producers, single consumer queue
        //     let (sender, receiver) = std::sync::mpsc::channel();

        //     // collect the buckets and create the task queueu
        //     let mut tasks = VecDeque::with_capacity(bucket_ids.len());
        //     let mut messages: Vec<(bool, Vec<(Message, MessageLevel)>)> = Vec::new();
        //     for (i, bucket_id) in bucket_ids.iter().enumerate() {
        //         // give each bucket its own log file
        //         let interpreter_log_file = Arc::new(std::sync::Mutex::new(
        //             if self.args.log_all || self.args.log_vir_simple {
        //                 Some(self.create_log_file(
        //                     Some(bucket_id),
        //                     crate::config::INTERPRETER_FILE_SUFFIX,
        //                 )?)
        //             } else {
        //                 None
        //             },
        //         ));

        //         // give each task a queued reporter to identify the bucket that is sending messages
        //         let reporter = QueuedReporter::new(i, sender.clone());

        //         tasks.push_back((
        //             bucket_id.clone(),
        //             global_ctx.from_self_with_log(interpreter_log_file),
        //             reporter,
        //         ));
        //         messages.push((false, Vec::new()));
        //     }

        //     // protect the taskq with a mutex
        //     let taskq = std::sync::Arc::new(std::sync::Mutex::new(tasks));

        //     // create the worker threads
        //     let mut workers = Vec::new();
        //     for _tid in 0..self.num_threads {
        //         // we create a clone of the verifier here to pass each thread its own local
        //         // copy as we modify fields in the verifier struct. later, we merge the results
        //         let mut thread_verifier = self.from_self();
        //         let thread_taskq = taskq.clone();
        //         let thread_krate = krate.clone(); // is an Arc<T>

        //         let worker = std::thread::spawn(move || {
        //             let mut completed_tasks: Vec<GlobalCtx> = Vec::new();
        //             loop {
        //                 let mut tq = thread_taskq.lock().unwrap();
        //                 let elm = tq.pop_front();
        //                 drop(tq);
        //                 if let Some((bucket_id, task, reporter)) = elm {
        //                     let res = thread_verifier.verify_bucket_outer(
        //                         &reporter,
        //                         &thread_krate,
        //                         None,
        //                         &bucket_id,
        //                         task,
        //                         &mut quant_profiler,
        //                     );
        //                     reporter.done(); // we've verified the bucket, send the done message
        //                     match res {
        //                         Ok(res) => {
        //                             completed_tasks.push(res);
        //                         }
        //                         Err(e) => return Err(e),
        //                     }
        //                 } else {
        //                     break;
        //                 }
        //             }
        //             Ok::<(Verifier, Vec<GlobalCtx>), VirErr>((thread_verifier, completed_tasks))
        //         });
        //         workers.push(worker);
        //     }

        //     // start handling messages, we keep track of the current active bucket for which we
        //     // print messages immediately, while buffering other messages from the other buckets
        //     let mut active_bucket = None;
        //     let mut num_done = 0;
        //     let reporter = Reporter::new(spans, compiler);
        //     loop {
        //         let msg = receiver.recv().expect("receiving message failed");
        //         match msg {
        //             ReporterMessage::Message(id, msg, level, now) => {
        //                 if now {
        //                     // if the message should be reported immediately, do so
        //                     // this is used for printing notices for long running queries
        //                     reporter.report_as(&msg.to_any(), level);
        //                     continue;
        //                 }

        //                 if let Some(m) = active_bucket {
        //                     // if it's the active bucket, print the message
        //                     if id == m {
        //                         reporter.report_as(&msg.to_any(), level);
        //                     } else {
        //                         let msgs = messages.get_mut(id).expect("message id out of range");
        //                         msgs.1.push((msg, level));
        //                     }
        //                 } else {
        //                     // no active bucket, print this message and set the bucket as the
        //                     // active one
        //                     active_bucket = Some(id);
        //                     reporter.report_as(&msg.to_any(), level);
        //                 }
        //             }
        //             ReporterMessage::Done(id) => {
        //                 // the done message is sent by the thread whenever it is done with verifying
        //                 // a bucket, we mark the bucket as done here.
        //                 {
        //                     // record that the bucket is done
        //                     let msgs = messages.get_mut(id).expect("message id out of range");
        //                     msgs.0 = true;
        //                 }

        //                 // if it is the active bucket, mark it as done, and reset the active bucket
        //                 if let Some(m) = active_bucket {
        //                     if m == id {
        //                         assert!(
        //                             messages
        //                                 .get_mut(id)
        //                                 .expect("message id out of range")
        //                                 .1
        //                                 .is_empty()
        //                         );
        //                         active_bucket = None;
        //                     }
        //                 }

        //                 // try to pick a new active bucket here, the first one that has any messages
        //                 if active_bucket.is_none() {
        //                     for (i, msgs) in messages.iter_mut().enumerate() {
        //                         if msgs.1.is_empty() {
        //                             continue;
        //                         }
        //                         // drain and print all messages of the bucket
        //                         for (msg, level) in msgs.1.drain(..) {
        //                             reporter.report_as(&msg.to_any(), level);
        //                         }
        //                         // if the bucket wasn't done, make it active and handle next message
        //                         if !msgs.0 {
        //                             active_bucket = Some(i);
        //                             break;
        //                         }
        //                     }
        //                 }

        //                 num_done = num_done + 1;
        //             }
        //         }

        //         if num_done == bucket_ids.len() {
        //             break;
        //         }
        //     }

        //     // join with all worker threads, theys should all have exited by now.
        //     // merge the verifier and global contexts
        //     for worker in workers {
        //         let res = worker.join().unwrap();
        //         match res {
        //             Ok((verifier, res)) => {
        //                 for r in res {
        //                     global_ctx.merge(r);
        //                 }
        //                 self.merge(verifier);
        //             }
        //             Err(e) => return Err(e),
        //         }
        //     }

        //     // print remaining messages
        //     for msgs in messages.drain(..) {
        //         for (msg, level) in msgs.1 {
        //             reporter.report_as(&msg.to_any(), level);
        //         }
        //     }
        } else {
            for bucket_id in &bucket_ids {
                global_ctx = self.verify_bucket_outer(
                    &reporter,
                    &krate,
                    Some(source_map),
                    bucket_id,
                    global_ctx,
                    &mut quant_profiler,
                )?;
            }
        }

        if self.args.profile_all {
            // let profiler =
            //     Profiler::new(Arc::new(vir::messages::VirMessageInterface {}), &reporter);
            // self.print_profile_stats(&reporter, profiler, &global_ctx.qid_map.borrow());
            self.print_profile_stats(&reporter, quant_profiler, &global_ctx.qid_map.borrow());
        } else if self.args.profile && self.count_errors == 0 {
            let msg = note_bare(
                "--profile reports prover performance data only when rlimts are exceeded, use --profile-all to always report profiler results",
            );
            reporter.report(&msg.to_any());
        }

        // Log/display triggers
        if self.args.log_all || self.args.log_triggers {
            let mut file = self.create_log_file(None, crate::config::TRIGGERS_FILE_SUFFIX)?;
            let chosen_triggers = global_ctx.get_chosen_triggers();
            for triggers in chosen_triggers {
                writeln!(file, "{:#?}", triggers).expect("error writing to trigger log file");
            }
        }
        let chosen_triggers = global_ctx.get_chosen_triggers();
        let mut low_confidence_triggers = None;
        for chosen in chosen_triggers {
            match (self.args.show_triggers, module_ids_to_verify.contains(&chosen.module)) {
                (ShowTriggers::Selective, true) if chosen.low_confidence => {
                    report_chosen_triggers(&reporter, &chosen);
                    low_confidence_triggers = Some(chosen.span);
                }
                (ShowTriggers::Module, true) => {
                    report_chosen_triggers(&reporter, &chosen);
                }
                (ShowTriggers::Verbose, _) => {
                    report_chosen_triggers(&reporter, &chosen);
                }
                _ => {}
            }
        }
        if let Some(span) = low_confidence_triggers {
            let msg = "Verus printed one or more automatically chosen quantifier triggers\n\
                because it had low confidence in the chosen triggers.\n\
                To suppress these messages, do one of the following:\n  \
                (1) manually annotate a single desired trigger using #[trigger]\n      \
                (example: forall|i: int, j: int| f(i) && #[trigger] g(i) && #[trigger] h(j)),\n  \
                (2) manually annotate multiple desired triggers using #![trigger ...]\n      \
                (example: forall|i: int| #![trigger f(i)] #![trigger g(i)] f(i) && g(i)),\n  \
                (3) accept the automatically chosen trigger using #![auto]\n      \
                (example: forall|i: int, j: int| #![auto] f(i) && g(i) && h(j))\n  \
                (4) use the --triggers-silent command-line option to suppress all printing of triggers.\n\
                (Note: triggers are used by the underlying SMT theorem prover to instantiate quantifiers;\n\
                the theorem prover instantiates a quantifier whenever some expression matches the\n\
                pattern specified by one of the quantifier's triggers.)\
                ";
            reporter.report(&note(&span, msg).to_any());
        }

        Ok(())
    }

    pub(crate) fn verify_crate<'tcx>(
        &mut self,
        compiler: &Compiler,
        spans: &SpanContext,
    ) -> Result<(), VirErr> {
        // Verify crate
        let time_verify_crate_start = Instant::now();

        let result =
            if !self.args.no_verify { self.verify_crate_inner(&compiler, spans) } else { Ok(()) };

        let time_verify_crate_end = Instant::now();
        self.time_verify_crate = time_verify_crate_end - time_verify_crate_start;

        result
    }

    fn construct_vir_crate<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        verus_items: Arc<VerusItems>,
        spans: &SpanContext,
        other_crate_names: Vec<String>,
        other_vir_crates: Vec<Krate>,
        diagnostics: &impl air::messages::Diagnostics,
        crate_name: String,
    ) -> Result<bool, (VirErr, Vec<vir::ast::VirErrAs>)> {
        let time0 = Instant::now();

        match rustc_hir_analysis::check_crate(tcx) {
            Ok(()) => {}
            Err(_) => {
                return Ok(false);
            }
        }

        let hir = tcx.hir();
        hir.par_body_owners(|def_id| tcx.ensure().check_match(def_id.to_def_id()));
        tcx.ensure().check_private_in_public(());
        hir.par_for_each_module(|module| {
            tcx.ensure().check_mod_privacy(module);
        });

        self.air_no_span = {
            let no_span = hir
                .krate()
                .owners
                .iter()
                .filter_map(|oi| {
                    oi.as_owner().as_ref().and_then(|o| {
                        if let OwnerNode::Crate(c) = o.node() {
                            Some(c.spans.inner_span)
                        } else {
                            None
                        }
                    })
                })
                .next()
                .expect("OwnerNode::Crate missing");
            Some(vir::messages::Span {
                raw_span: crate::spans::to_raw_span(no_span),
                id: 0,
                data: vec![],
                as_string: "no location".to_string(),
            })
        };

        let time1 = Instant::now();
        self.time_hir = time1 - time0;

        let time0 = Instant::now();

        let mut crate_names: Vec<String> = vec![crate_name];
        crate_names.extend(other_crate_names.into_iter());
        let mut vir_crates: Vec<Krate> = other_vir_crates;
        // TODO vec![vir::builtins::builtin_krate(&self.air_no_span.clone().unwrap())];

        let erasure_info = ErasureInfo {
            hir_vir_ids: vec![],
            resolved_calls: vec![],
            resolved_exprs: vec![],
            resolved_pats: vec![],
            direct_var_modes: vec![],
            external_functions: vec![],
            ignored_functions: vec![],
        };
        let erasure_info = std::rc::Rc::new(std::cell::RefCell::new(erasure_info));
        let import_len = self.args.import.len();
        let vstd_crate_name = if import_len > 0 || self.args.export.is_some() {
            Some(Arc::new(vir::def::VERUSLIB.to_string()))
        } else {
            None
        };
        let ctxt = Arc::new(ContextX {
            tcx,
            krate: hir.krate(),
            erasure_info,
            spans: spans.clone(),
            vstd_crate_name: vstd_crate_name.clone(),
            arch: Arc::new(ArchContextX { word_bits: self.args.arch_word_bits }),
            verus_items,
            diagnostics: std::rc::Rc::new(std::cell::RefCell::new(Vec::new())),
        });
        let multi_crate = self.args.export.is_some() || import_len > 0;
        crate::rust_to_vir_base::MULTI_CRATE
            .with(|m| m.store(multi_crate, std::sync::atomic::Ordering::Relaxed));

        let map_err_diagnostics =
            |err: VirErr| (err, ctxt.diagnostics.borrow_mut().drain(..).collect());

        // Convert HIR -> VIR
        let time1 = Instant::now();
        let vir_crate = crate::rust_to_vir::crate_to_vir(&ctxt).map_err(map_err_diagnostics)?;
        let time2 = Instant::now();
        let vir_crate = vir::ast_sort::sort_krate(&vir_crate);
        self.current_crate_module_ids = Some(vir_crate.module_ids.clone());

        // Export crate if requested.
        let crate_metadata = crate::import_export::CrateMetadata {
            crate_id: spans.local_crate.to_u64(),
            original_files: spans.local_files.clone(),
        };
        crate::import_export::export_crate(&self.args, crate_metadata, vir_crate.clone())
            .map_err(map_err_diagnostics)?;

        let user_filter =
            UserFilter::from_args(&self.args, &vir_crate).map_err(map_err_diagnostics)?;
        self.user_filter = Some(user_filter);

        // Gather all crates and merge them into one crate.
        // REVIEW: by merging all the crates into one here, we end up rechecking well_formed/modes
        // of the library crates, which were already checked when they were exported.
        // If this turns out to be slow, we could keep the library crates separate from
        // the new crate.  (We do need to have all the crate definitions available in some form,
        // because well_formed and modes checking look up definitions from libraries.)
        vir_crates.push(vir_crate);
        let vir_crate = vir::ast_simplify::merge_krates(vir_crates).map_err(map_err_diagnostics)?;

        if self.args.log_all || self.args.log_vir {
            let mut file = self
                .create_log_file(None, crate::config::VIR_FILE_SUFFIX)
                .map_err(map_err_diagnostics)?;
            vir::printer::write_krate(&mut file, &vir_crate, &self.args.vir_log_option);
        }
        let path_to_well_known_item = crate::def::path_to_well_known_item(&ctxt);

        let vir_crate = vir::traits::demote_foreign_traits(&path_to_well_known_item, &vir_crate)
            .map_err(map_err_diagnostics)?;
        let check_crate_result =
            vir::well_formed::check_crate(&vir_crate, &mut ctxt.diagnostics.borrow_mut());
        for diag in ctxt.diagnostics.borrow_mut().drain(..) {
            match diag {
                vir::ast::VirErrAs::Warning(err) => {
                    diagnostics.report_as(&err.to_any(), MessageLevel::Warning)
                }
                vir::ast::VirErrAs::Note(err) => {
                    diagnostics.report_as(&err.to_any(), MessageLevel::Note)
                }
            }
        }
        check_crate_result.map_err(|e| (e, Vec::new()))?;
        let vir_crate = vir::autospec::resolve_autospec(&vir_crate).map_err(|e| (e, Vec::new()))?;
        let erasure_modes =
            vir::modes::check_crate(&vir_crate, true).map_err(|e| (e, Vec::new()))?;

        self.vir_crate = Some(vir_crate.clone());
        self.crate_names = Some(crate_names);
        self.vstd_crate_name = vstd_crate_name;

        let erasure_info = ctxt.erasure_info.borrow();
        let hir_vir_ids = erasure_info.hir_vir_ids.clone();
        let resolved_calls = erasure_info.resolved_calls.clone();
        let resolved_exprs = erasure_info.resolved_exprs.clone();
        let resolved_pats = erasure_info.resolved_pats.clone();
        let direct_var_modes = erasure_info.direct_var_modes.clone();
        let external_functions = erasure_info.external_functions.clone();
        let ignored_functions = erasure_info.ignored_functions.clone();
        let erasure_hints = crate::erase::ErasureHints {
            vir_crate,
            hir_vir_ids,
            resolved_calls,
            resolved_exprs,
            resolved_pats,
            erasure_modes,
            direct_var_modes,
            external_functions,
            ignored_functions,
        };
        self.erasure_hints = Some(erasure_hints);

        let time4 = Instant::now();
        self.time_vir = time4 - time0;
        self.time_vir_rust_to_vir = time2 - time1;

        Ok(true)
    }
}

// TODO: move the callbacks into a different file, like driver.rs
pub(crate) struct VerifierCallbacksEraseMacro {
    pub(crate) verifier: Verifier,
    /// start time of the rustc compilation
    pub(crate) rust_start_time: Instant,
    /// time when entered the `after_expansion` callback
    pub(crate) rust_end_time: Option<Instant>,
    /// start time of lifetime analysys
    pub(crate) lifetime_start_time: Option<Instant>,
    /// end time of lifetime analysys
    pub(crate) lifetime_end_time: Option<Instant>,
    pub(crate) rustc_args: Vec<String>,
    pub(crate) file_loader:
        Option<Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>>,
    pub(crate) build_test_mode: bool,
}

pub(crate) static BODY_HIR_ID_TO_REVEAL_PATH_RES: std::sync::RwLock<
    Option<
        HashMap<
            rustc_span::def_id::DefId,
            (Option<rustc_hir::def::Res>, crate::hir_hide_reveal_rewrite::ResOrSymbol),
        >,
    >,
> = std::sync::RwLock::new(None);

fn hir_crate<'tcx>(tcx: TyCtxt<'tcx>, _: ()) -> rustc_hir::Crate<'tcx> {
    let mut crate_ = (rustc_interface::DEFAULT_QUERY_PROVIDERS.hir_crate)(tcx, ());
    crate::hir_hide_reveal_rewrite::hir_hide_reveal_rewrite(&mut crate_, tcx);
    crate_
}

impl rustc_driver::Callbacks for VerifierCallbacksEraseMacro {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_session, providers, _extern_providers| {
            providers.hir_crate = hir_crate;
        });
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        self.rust_end_time = Some(Instant::now());

        if !compiler.session().compile_status().is_ok() {
            return rustc_driver::Compilation::Stop;
        }

        let _result = queries.global_ctxt().expect("global_ctxt").enter(|tcx| {
            let crate_name = tcx.crate_name(LOCAL_CRATE).as_str().to_owned();

            let imported = match crate::import_export::import_crates(&self.verifier.args) {
                Ok(imported) => imported,
                Err(err) => {
                    assert!(err.spans.len() == 0);
                    assert!(err.level == MessageLevel::Error);
                    compiler.session().diagnostic().err(&err.note);
                    self.verifier.encountered_vir_error = true;
                    return;
                }
            };
            let verus_items =
                Arc::new(crate::verus_items::from_diagnostic_items(&tcx.all_diagnostic_items(())));
            let spans = SpanContextX::new(
                tcx,
                compiler.session().local_stable_crate_id(),
                compiler.session().source_map(),
                imported.metadatas.into_iter().map(|c| (c.crate_id, c.original_files)).collect(),
            );
            {
                let reporter = Reporter::new(&spans, compiler);
                if self.verifier.args.trace {
                    reporter.report_now(&note_bare("preparing crate for verification").to_any());
                }
                if let Err((err, mut diagnostics)) = self.verifier.construct_vir_crate(
                    tcx,
                    verus_items.clone(),
                    &spans,
                    imported.crate_names,
                    imported.vir_crates,
                    &reporter,
                    crate_name.clone(),
                ) {
                    reporter.report_as(&err.to_any(), MessageLevel::Error);
                    self.verifier.encountered_vir_error = true;

                    for diag in diagnostics.drain(..) {
                        match diag {
                            vir::ast::VirErrAs::Warning(err) => {
                                reporter.report_as(&err.to_any(), MessageLevel::Warning)
                            }
                            vir::ast::VirErrAs::Note(err) => {
                                reporter.report_as(&err.to_any(), MessageLevel::Note)
                            }
                        }
                    }
                    return;
                }
                if !compiler.session().compile_status().is_ok() {
                    return;
                }
                self.lifetime_start_time = Some(Instant::now());
                let status = if self.verifier.args.no_lifetime {
                    Ok(vec![])
                } else {
                    let log_lifetime =
                        self.verifier.args.log_all || self.verifier.args.log_lifetime;
                    let lifetime_log_file = if log_lifetime {
                        let file = self
                            .verifier
                            .create_log_file(None, crate::config::LIFETIME_FILE_SUFFIX);
                        match file {
                            Err(err) => {
                                reporter.report_as(&err.to_any(), MessageLevel::Error);
                                self.verifier.encountered_vir_error = true;
                                return;
                            }
                            Ok(file) => Some(file),
                        }
                    } else {
                        None
                    };
                    crate::lifetime::check_tracked_lifetimes(
                        tcx,
                        verus_items,
                        &spans,
                        self.verifier.erasure_hints.as_ref().expect("erasure_hints"),
                        lifetime_log_file,
                    )
                };
                self.lifetime_end_time = Some(Instant::now());
                match status {
                    Ok(msgs) => {
                        if msgs.len() > 0 {
                            self.verifier.encountered_vir_error = true;
                            // We found lifetime errors.
                            // We could print them immediately, but instead,
                            // let's first run rustc's standard lifetime checking
                            // because the error messages are likely to be better.
                            let file_loader =
                                std::mem::take(&mut self.file_loader).expect("file_loader");
                            let compile_status = crate::driver::run_with_erase_macro_compile(
                                self.rustc_args.clone(),
                                file_loader,
                                false,
                                self.build_test_mode,
                            );
                            if compile_status.is_err() {
                                return;
                            }
                            for msg in &msgs {
                                reporter.report(&msg.clone().to_any());
                            }
                            return;
                        }
                    }
                    Err(err) => {
                        reporter.report_as(&err.to_any(), MessageLevel::Error);
                        self.verifier.encountered_vir_error = true;
                        return;
                    }
                }
            }

            if !compiler.session().compile_status().is_ok() {
                return;
            }

            match self.verifier.verify_crate(compiler, &spans) {
                Ok(()) => {}
                Err(err) => {
                    let reporter = Reporter::new(&spans, compiler);
                    reporter.report_as(&err.to_any(), MessageLevel::Error);
                    self.verifier.encountered_vir_error = true;
                }
            }
        });
        rustc_driver::Compilation::Stop
    }
}
