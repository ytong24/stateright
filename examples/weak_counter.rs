//! Demonstrates **weak simulation** in the refinement mapping framework.
//!
//! The abstract spec carries an internal `last_actor` field — bookkeeping
//! that records which thread took the most recent transition. The concrete
//! model has no access to that information (it's a simpler two-thread
//! counter), so any refinement mapping has to make something up for
//! `last_actor`.
//!
//! - Under **strict** `Observable` (the entire abstract state is
//!   observable), the refinement check fails: the mapping sets
//!   `last_actor = None` always, but the abstract's transitions
//!   produce `Some(thread)`. The mismatch is visible, so the check
//!   rejects the mapping.
//!
//! - Under **weak** `Observable` (project away `last_actor`), the same
//!   mapping succeeds. The bookkeeping is hidden from the contract, so
//!   the concrete only has to simulate the `(pc, counter)` pair — which
//!   it does faithfully.
//!
//! This is the canonical pattern for weak simulation: keep internal
//! ghost/bookkeeping fields in the abstract spec (for clarity or for
//! stating invariants), but restrict the refinement obligation to the
//! fields that are part of the observable contract.

mod abstract_model {
    use stateright::Model;

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub enum ThreadState {
        Start,
        Done,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct Action(pub usize);

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct State {
        pub pc: Vec<ThreadState>,
        pub counter: u32,
        /// Internal bookkeeping — tracks which thread took the last
        /// transition. Part of the abstract spec but NOT part of the
        /// observable contract under weak simulation.
        pub last_actor: Option<usize>,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct Counter {
        pub threads: usize,
    }

    impl Model for Counter {
        type State = State;
        type Action = Action;

        fn init_states(&self) -> Vec<Self::State> {
            vec![State {
                pc: vec![ThreadState::Start; self.threads],
                counter: 0,
                last_actor: None,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            for (idx, ts) in state.pc.iter().enumerate() {
                if *ts == ThreadState::Start {
                    actions.push(Action(idx));
                }
            }
        }

        fn next_state(&self, last: &Self::State, action: Self::Action) -> Option<Self::State> {
            let Action(idx) = action;
            let mut next = last.clone();
            next.pc[idx] = ThreadState::Done;
            next.counter += 1;
            next.last_actor = Some(idx);
            Some(next)
        }
    }
}

mod concrete_model {
    use stateright::Model;

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub enum ThreadState {
        Start,
        Done,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct Action(pub usize);

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct State {
        pub pc: Vec<ThreadState>,
        pub counter: u32,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct Counter {
        pub threads: usize,
    }

    impl Model for Counter {
        type State = State;
        type Action = Action;

        fn init_states(&self) -> Vec<Self::State> {
            vec![State {
                pc: vec![ThreadState::Start; self.threads],
                counter: 0,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            for (idx, ts) in state.pc.iter().enumerate() {
                if *ts == ThreadState::Start {
                    actions.push(Action(idx));
                }
            }
        }

        fn next_state(&self, last: &Self::State, action: Self::Action) -> Option<Self::State> {
            let Action(idx) = action;
            let mut next = last.clone();
            next.pc[idx] = ThreadState::Done;
            next.counter += 1;
            Some(next)
        }
    }
}

fn project_pc(c: &[concrete_model::ThreadState]) -> Vec<abstract_model::ThreadState> {
    c.iter()
        .map(|s| match s {
            concrete_model::ThreadState::Start => abstract_model::ThreadState::Start,
            concrete_model::ThreadState::Done => abstract_model::ThreadState::Done,
        })
        .collect()
}

/// Refinement mapping under **strict** Observable. Refinement should FAIL.
mod strict {
    use super::*;
    use stateright::refinement_mapping::{RefinementMapping, RefinementModel};
    use stateright::{Checker, Model};

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct Mapper {
        pub abstract_model: abstract_model::Counter,
    }

    impl RefinementMapping<concrete_model::Counter, abstract_model::Counter> for Mapper {
        type AuxState = ();
        /// Strict Observable = full abstract state, including `last_actor`.
        type Observable = abstract_model::State;

        fn abstract_model(&self) -> &abstract_model::Counter {
            &self.abstract_model
        }

        fn init_aux_state(&self, _: &concrete_model::State) {}

        fn advance_aux_state(
            &self,
            _: &concrete_model::State,
            _: &(),
            _: &concrete_model::Action,
            _: &concrete_model::State,
        ) {
        }

        fn refinement_map(&self, c: &concrete_model::State, _: &()) -> abstract_model::State {
            abstract_model::State {
                pc: project_pc(&c.pc),
                counter: c.counter,
                // The concrete has no idea which thread last acted, so the
                // mapping cannot produce the "right" value here.
                last_actor: None,
            }
        }

        fn observe(&self, a: &abstract_model::State) -> abstract_model::State {
            a.clone()
        }
    }

    pub fn run_check(num_threads: usize) {
        let concrete = concrete_model::Counter {
            threads: num_threads,
        };
        let abstract_ = abstract_model::Counter {
            threads: num_threads,
        };
        let mapper = Mapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        let checker = model.checker().threads(num_cpus::get()).spawn_bfs().join();
        match checker.discovery("check_simulation") {
            Some(_) => println!(
                "  Refinement FAILED — counterexample found (expected for strict Observable)."
            ),
            None => println!(
                "  Refinement passed — unexpected for strict Observable with garbage `last_actor`."
            ),
        }
        println!("  State count: {}", checker.state_count());
    }

    pub fn run_serve(num_threads: usize) {
        let concrete = concrete_model::Counter {
            threads: num_threads,
        };
        let abstract_ = abstract_model::Counter {
            threads: num_threads,
        };
        let mapper = Mapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        model
            .checker()
            .threads(num_cpus::get())
            .serve("127.0.0.1:3000");
    }
}

/// Refinement mapping under **weak** Observable. Refinement should PASS.
mod weak {
    use super::*;
    use stateright::refinement_mapping::{RefinementMapping, RefinementModel};
    use stateright::{Checker, Model};

    /// Observable projection: everything in the abstract state EXCEPT
    /// `last_actor`. This is the contract the refinement preserves.
    #[derive(Clone, Debug, Eq, PartialEq)]
    pub struct Obs {
        pub pc: Vec<abstract_model::ThreadState>,
        pub counter: u32,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    pub struct Mapper {
        pub abstract_model: abstract_model::Counter,
    }

    impl RefinementMapping<concrete_model::Counter, abstract_model::Counter> for Mapper {
        type AuxState = ();
        type Observable = Obs;

        fn abstract_model(&self) -> &abstract_model::Counter {
            &self.abstract_model
        }

        fn init_aux_state(&self, _: &concrete_model::State) {}

        fn advance_aux_state(
            &self,
            _: &concrete_model::State,
            _: &(),
            _: &concrete_model::Action,
            _: &concrete_model::State,
        ) {
        }

        fn refinement_map(&self, c: &concrete_model::State, _: &()) -> abstract_model::State {
            abstract_model::State {
                pc: project_pc(&c.pc),
                counter: c.counter,
                last_actor: None,
            }
        }

        fn observe(&self, a: &abstract_model::State) -> Obs {
            Obs {
                pc: a.pc.clone(),
                counter: a.counter,
            }
        }
    }

    pub fn run_check(num_threads: usize) {
        let concrete = concrete_model::Counter {
            threads: num_threads,
        };
        let abstract_ = abstract_model::Counter {
            threads: num_threads,
        };
        let mapper = Mapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        let checker = model.checker().threads(num_cpus::get()).spawn_bfs().join();
        match checker.discovery("check_simulation") {
            Some(_) => println!(
                "  Refinement FAILED — unexpected, `last_actor` should be hidden by Observable."
            ),
            None => println!("  Refinement passed (expected for weak Observable)."),
        }
        println!("  State count: {}", checker.state_count());
    }

    pub fn run_serve(num_threads: usize) {
        let concrete = concrete_model::Counter {
            threads: num_threads,
        };
        let abstract_ = abstract_model::Counter {
            threads: num_threads,
        };
        let mapper = Mapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        model
            .checker()
            .threads(num_cpus::get())
            .serve("127.0.0.1:3000");
    }
}

fn main() -> Result<(), pico_args::Error> {
    env_logger::init_from_env(env_logger::Env::default().default_filter_or("info"));

    let mut args = pico_args::Arguments::from_env();
    let num_threads = 2;
    match args.subcommand()?.as_deref() {
        Some("strict") => {
            println!("Strict Observable — refinement SHOULD fail:");
            strict::run_check(num_threads);
        }
        Some("weak") => {
            println!("Weak Observable — refinement SHOULD pass:");
            weak::run_check(num_threads);
        }
        Some("strict-serve") => {
            println!("Strict Observable — serving counterexample SVG at http://127.0.0.1:3000");
            strict::run_serve(num_threads);
        }
        Some("weak-serve") => {
            println!("Weak Observable — serving at http://127.0.0.1:3000");
            weak::run_serve(num_threads);
        }
        _ => {
            println!("USAGE:");
            println!(
                "  ./weak_counter strict          # check strict Observable (expected to fail)"
            );
            println!("  ./weak_counter weak            # check weak Observable (expected to pass)");
            println!("  ./weak_counter strict-serve    # serve counterexample SVG on port 3000");
            println!("  ./weak_counter weak-serve      # serve SVG on port 3000");
        }
    }

    Ok(())
}
