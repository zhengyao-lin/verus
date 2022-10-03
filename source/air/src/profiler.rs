//! Analyzes prover performance of the SMT solver

use std::io::{BufRead, Read};
use std::collections::BTreeMap;
use z3tracer::model::QuantCost;
use z3tracer::syntax::{Term, QiFrame, Meaning};
use z3tracer::{Model, ModelConfig};

pub const PROVER_LOG_FILE: &str = "verus-prover-trace.log";

pub const INST_TARGET_QUANT_PREFIX: &str = "inst_";
pub const USER_QUANT_PREFIX: &str = "user_";
pub const INTERNAL_QUANT_PREFIX: &str = "internal_";

#[derive(Debug)]
pub struct QuantInstantiation {
    pub qid: String,
    pub terms: Vec<String>,
}

#[derive(Debug)]
/// Profiler for processing and displaying SMT performance data
pub struct Profiler {
    //log_path: String,
    quantifier_stats: Vec<QuantCost>,
    pub explicit_instantiations: Vec<QuantInstantiation>, // this includes quantifiers that can be used as targets for suggesting explicit instantiations
}

impl Profiler {
    /// Instantiate a new (singleton) profiler
    pub fn new() -> Profiler {
        let path = PROVER_LOG_FILE;

        // Count the number of lines
        let file = std::io::BufReader::new(
            std::fs::File::open(path).expect("Failed to open prover trace log"),
        );
        let line_count = file.lines().count();

        // println!("{}", std::fs::read_to_string(path).expect("Unable to read file"));

        // Reset to actually parse the file
        let file = std::io::BufReader::new(
            std::fs::File::open(path).expect("Failed to open prover trace log"),
        );
        let mut model_config = ModelConfig::default();
        model_config.parser_config.skip_z3_version_check = true;
        model_config.parser_config.ignore_invalid_lines = true;
        model_config.skip_log_consistency_checks = true;
        let mut model = Model::new(model_config);
        println!("Analyzing prover log...");
        let _ = model
            .process(Some(path.to_string()), file, line_count)
            .expect("Error processing prover trace");
        println!("... analysis complete\n");

        // Analyze the quantifer costs
        let quant_costs = model.quant_costs();
        
        let mut user_quant_costs = quant_costs
            .into_iter()
            .filter(|cost| cost.quant.starts_with(USER_QUANT_PREFIX))
            .collect::<Vec<_>>();
        user_quant_costs.sort_by_key(|v| v.instantiations * v.cost);
        user_quant_costs.reverse();

        let mut explicit_instantiations = Vec::new();

        for (qi_key, quant_inst) in model.instantiations() {
            let quant_id = quant_inst.frame.quantifier();
            let quant_term = model
                .term(&quant_id)
                .expect(format!("failed to find {:?} in the profiler's model", quant_id).as_str());

            if let Term::Quant { name: quant_name, .. } = quant_term {
                if !quant_name.starts_with(INST_TARGET_QUANT_PREFIX) {
                    continue;
                }

                // model.log_instance(*qi_key).expect("failed to log stuff");
                // println!("User QI instance: {:?}, {:?}, {:?}", qi_key, quant_name, quant_inst);

                match &quant_inst.frame {
                    QiFrame::NewMatch { terms, .. } => {
                        // let venv = BTreeMap::new();
                        let term_strings = terms
                            .iter()
                            .map(|term_id| Profiler::sexp_to_rust_exp(&model, &model.term_data(term_id).expect("failed to unparse term").term))
                            .collect::<Option<Vec<_>>>();
                        
                        if let Some(term_strings) = term_strings {
                            explicit_instantiations.push(QuantInstantiation { qid: quant_name.clone(), terms: term_strings });
                        }
                    },
                    _ => {
                        println!("unsupported")
                    }
                }
            }
        }

        Profiler { quantifier_stats: user_quant_costs, explicit_instantiations: explicit_instantiations }
    }

    fn sexp_to_rust_exp(model: &Model, term: &Term) -> Option<String> {
        match term {
            // ZL TODO: use the constants in vir::def once we move this to a better place
            Term::App { name, args, meaning }
            if [ "I", "B", "S", "C", "%I", "%B", "&S", "%C" ].contains(&name.as_str()) &&
               args.len() == 1 => {
                Profiler::sexp_to_rust_exp(model, &model.term_data(&args[0]).expect("term not found").term)
            }

            // Local variable, ends with @ and the actual name is the one separated by ~
            Term::App { name, args, meaning }
            if name.ends_with("@") &&
               name.contains('~') &&
               args.is_empty() => {
                name.split('~').nth(0).map(|s| s.to_string())
            }

            // Global
            Term::App { name, args, meaning }
            if name.ends_with("?") &&
               name.contains('.') => {
                let name = name.split('.').nth(0)?;

                if args.is_empty() {
                    Some(name.to_string())
                } else {
                    let arg_string = args.iter()
                        .map(|id| Profiler::sexp_to_rust_exp(model, &model.term_data(id).ok()?.term))
                        .collect::<Option<Vec<_>>>()?;
                    Some(format!("{}({})", name, arg_string.join(", ")))
                }
            }

            Term::App { name, args, meaning }
            if name.as_str() == "Int" &&
               args.is_empty() => {
                meaning.as_ref().map(|Meaning { theory: _, sexp }| sexp.to_string())
            }

            // ZL TODO: Builtin expressions such as Mul

            _ => {
                // let venv = BTreeMap::new();
                // let name = model.term_to_sexp(&venv, term).expect("unable to print s-expression");
                println!("unsupported s-expression: {:?}", term);
                None
            }
        }
    }

    pub fn quant_count(&self) -> usize {
        self.quantifier_stats.len()
    }

    pub fn total_instantiations(&self) -> u64 {
        self.quantifier_stats.iter().fold(0, |acc, cost| acc + cost.instantiations)
    }

    pub fn print_raw_stats(&self) {
        for cost in &self.quantifier_stats {
            let count = cost.instantiations;
            println!(
                "Instantiated {} {} times ({}% of the total)",
                cost.quant,
                count,
                100 * count / self.total_instantiations()
            );
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &QuantCost> + '_ {
        self.quantifier_stats.iter()
    }
}
