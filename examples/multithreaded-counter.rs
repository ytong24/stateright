//! This file contains an example of refinement mappings from this [blog post](https://www.hillelwayne.com/post/refinement/) by Hillel Wayne.
//!
//! In this file, we will have an abstract model for a multithreaded counter, a bad implementation that DOES NOT correctly implement the counter, and a good implementation which correctly implements the counter. For more details, please check the above nice blog post.
//!
//! We will show that the bad implementation will fail the refinement checking, while the good implementation will pass. Interestingly, we'll also see that the good implementation actually refines the bad implementation.
//!
//! The TLA+ specification for the abstract model:
//! ```tla+
//! ---- MODULE abstract ----
//! EXTENDS Integers, Sequences
//!
//! VARIABLES pc, counter
//! vars == <<pc, counter>>
//!
//! \* Two threads
//! Threads == 1..2
//!
//! \* State transition action
//! Trans(thread, from, to) ==
//!   /\ pc[thread] = from
//!   /\ pc' = [pc EXCEPT ![thread] = to]
//!
//! \* Both threads start in the `start` state
//! Init ==
//!   /\ pc = [t \in Threads |-> "start"]
//!   /\ counter = 0
//!
//! Next ==
//!   \* Pick one thread
//!   \/ \E t \in Threads:
//!      \* Move it to `done`
//!      /\ Trans(t, "start", "done")
//!      \* Increment counter
//!      /\ counter' = counter + 1
//!
//! Spec == Init /\ [][Next]_vars
//!
//! ====
//! ```
//!
//!
//!
//! The TLA+ for the bad implementation:
//! ```tla+
//! ---- MODULE bad ----
//! EXTENDS Integers, Sequences
//!
//! VARIABLES pc, counter, tmp
//! vars == <<pc, counter, tmp>>
//!
//! Threads == 1..2
//!
//! States == {"start", "inc", "done"}
//!
//! Trans(thread, from, to) ==
//!   /\ pc[thread] = from
//!   /\ pc' = [pc EXCEPT ![thread] = to]
//!
//! Init ==
//!   /\ pc = [t \in Threads |-> "start"]
//!   /\ counter = 0
//!   /\ tmp = [t \in Threads |-> 0]
//!
//! GetCounter(t) ==
//!   /\ tmp' = [tmp EXCEPT ![t] = counter]
//!   /\ UNCHANGED counter
//!
//! IncCounter(t) ==
//!   /\ counter' = tmp[t] + 1
//!   /\ UNCHANGED tmp
//!
//! Next ==
//!   \/ \E t \in Threads:
//!     \* Step to get the counter value
//!     \/ /\ Trans(t, "start", "inc")
//!        /\ GetCounter(t)
//!     \* Step to increment the counter
//!     \/ /\ Trans(t, "inc", "done")
//!        /\ IncCounter(t)
//!
//! Spec == Init /\ [][Next]_vars
//! ====
//! ```
//!
//!
//! The TLA+ for the good implementation:
//! ```tla+
//! ---- MODULE good ----
//! EXTENDS Integers, Sequences
//!
//! VARIABLES pc, counter, tmp, lock
//! vars == <<pc, counter, tmp, lock>>
//!
//! Threads == 1..2
//!
//! States == {"start", "inc", "done"}
//!
//! Trans(thread, from, to) ==
//!   /\ pc[thread] = from
//!   /\ pc' = [pc EXCEPT ![thread] = to]
//!
//! Init ==
//!   /\ pc = [t \in Threads |-> "start"]
//!   /\ counter = 0
//!   /\ tmp = <<0, 0>>
//!   /\ lock = 0
//!
//! AcquireLock(t) ==
//!   /\ lock = 0
//!   /\ lock' = t
//!
//! ReleaseLock(t) ==
//!   /\ lock = t
//!   /\ lock' = 0
//!
//! GetCounter(t) ==
//!   /\ tmp' = [tmp EXCEPT ![t] = counter]
//!   /\ UNCHANGED counter
//!
//! IncCounter(t) ==
//!   /\ counter' = tmp[t] + 1
//!   /\ UNCHANGED tmp
//!
//! Next ==
//!   \/ \E t \in Threads:
//!     \/ /\ Trans(t, "start", "inc")
//!        /\ GetCounter(t)
//!        /\ AcquireLock(t)
//!     \/ /\ Trans(t, "inc", "done")
//!        /\ IncCounter(t)
//!        /\ ReleaseLock(t)
//!
//! Spec == Init /\ [][Next]_vars
//!
//! Mapping ==
//!   INSTANCE abstract WITH
//!     counter <- counter,
//!     pc <- [t \in Threads |->
//!       IF pc[t] = "inc" THEN "start"
//!       ELSE pc[t]
//!       ]
//!
//! Refinement == Mapping!Spec
//!
//! ====
//! ```
//!

mod abstract_model {
    use stateright::Model;

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum CounterAction {
        Trans(usize), // Transfer the TransitionState of the thread with usize index.
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum TransitionState {
        Start,
        Done,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct CounterState {
        pub pc: Vec<TransitionState>,
        pub counter: usize,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct Counter {
        pub threads: usize,
    }

    impl Model for Counter {
        type State = CounterState;

        type Action = CounterAction;

        fn init_states(&self) -> Vec<Self::State> {
            vec![CounterState {
                pc: vec![TransitionState::Start; self.threads],
                counter: 0,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            state
                .pc
                .iter()
                .enumerate()
                .for_each(|(idx, transition_state)| {
                    // we can transfer all the threads whose transition states are not Done.
                    if *transition_state != TransitionState::Done {
                        actions.push(CounterAction::Trans(idx));
                    }
                });
        }

        fn next_state(
            &self,
            last_state: &Self::State,
            action: Self::Action,
        ) -> Option<Self::State> {
            let mut state = last_state.clone();
            let CounterAction::Trans(idx) = action;

            if last_state.pc[idx] == TransitionState::Done {
                panic!(
                    "Panic! Trying to transfer thread {}, but its state is already Done.",
                    idx
                );
            }

            // turn the idx thread into Done, and increment the counter.
            state.pc[idx] = TransitionState::Done;
            state.counter += 1;

            Some(state)
        }
    }
}

mod bad_impl {
    use stateright::Model;

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum CounterAction {
        GetCounter(usize), // get the global counter to update the thread's local counter
        IncCounter(usize), // update the global counter based on the thread's local counter
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum TransitionState {
        Start,
        Inc,
        Done,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct CounterState {
        pub pc: Vec<TransitionState>,
        pub counter: usize,
        pub tmp: Vec<usize>, // local counter for each thread
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct Counter {
        pub threads: usize,
    }

    impl Model for Counter {
        type State = CounterState;

        type Action = CounterAction;

        fn init_states(&self) -> Vec<Self::State> {
            vec![CounterState {
                pc: vec![TransitionState::Start; self.threads],
                counter: 0,
                tmp: vec![0; self.threads],
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            state.pc.iter().enumerate().for_each(
                |(idx, transition_state)| match transition_state {
                    // if the thread is Start, it can perform GetCounter.
                    TransitionState::Start => actions.push(CounterAction::GetCounter(idx)),
                    // if the thread is Inc, it can perform IncCounter.
                    TransitionState::Inc => actions.push(CounterAction::IncCounter(idx)),
                    // if the thread is Done, it can do nothing.
                    TransitionState::Done => (),
                },
            );
        }

        fn next_state(
            &self,
            last_state: &Self::State,
            action: Self::Action,
        ) -> Option<Self::State> {
            let mut state = last_state.clone();

            match action {
                CounterAction::GetCounter(idx) => {
                    // transfer the thread state into Inc
                    state.pc[idx] = TransitionState::Inc;
                    // update my local counter as the global counter
                    state.tmp[idx] = last_state.counter;
                }
                CounterAction::IncCounter(idx) => {
                    // transfer the thread state into Done
                    state.pc[idx] = TransitionState::Done;
                    // update the global counter based on my local counter
                    state.counter = last_state.tmp[idx] + 1;
                }
            }

            Some(state)
        }
    }
}

mod good_impl {
    use std::usize;

    use stateright::Model;

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum CounterAction {
        LockAndGetCounter(usize),
        ReleaseAndIncCounter(usize),
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum TransitionState {
        Start,
        Inc,
        Done,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct CounterState {
        pub pc: Vec<TransitionState>,
        pub counter: usize,
        pub tmp: Vec<usize>,
        pub lock: usize, // indicate which thread is holding the lock. if it's free, set the value to usize::MAX.
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct Counter {
        pub threads: usize,
    }

    impl Model for Counter {
        type State = CounterState;

        type Action = CounterAction;

        fn init_states(&self) -> Vec<Self::State> {
            vec![CounterState {
                pc: vec![TransitionState::Start; self.threads],
                counter: 0,
                tmp: vec![0; self.threads],
                lock: usize::MAX,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            (0..self.threads).into_iter().for_each(|idx| {
                // if transition state is Start and lock is MAX, we can perform LockAndGetCounter action
                if state.pc[idx] == TransitionState::Start && state.lock == usize::MAX {
                    actions.push(CounterAction::LockAndGetCounter(idx));
                    return;
                }
                // if transition state is Inc and lock is me, we can perform ReleaseAndIncCounter action
                if state.pc[idx] == TransitionState::Inc && state.lock == idx {
                    actions.push(CounterAction::ReleaseAndIncCounter(idx));
                    return;
                }
                // otherwise, no action can be performed
            });
        }

        fn next_state(
            &self,
            last_state: &Self::State,
            action: Self::Action,
        ) -> Option<Self::State> {
            let mut state = last_state.clone();

            match action {
                CounterAction::LockAndGetCounter(idx) => {
                    // update transition state to Inc
                    state.pc[idx] = TransitionState::Inc;
                    // update local counter with the global counter
                    state.tmp[idx] = last_state.counter;
                    // acquire lock
                    state.lock = idx;
                }
                CounterAction::ReleaseAndIncCounter(idx) => {
                    // update transition state to Done
                    state.pc[idx] = TransitionState::Done;
                    // update global counter using local counter
                    state.counter = last_state.tmp[idx] + 1;
                    // releae lock
                    state.lock = usize::MAX;
                }
            };

            Some(state)
        }
    }
}

mod try_bad_refine_abstract {
    use stateright::{
        refinement_mapping::{RefinementMapping, RefinementModel},
        Checker, Model,
    };

    use crate::{abstract_model, bad_impl};

    #[derive(Debug, Hash, Clone, PartialEq)]
    pub(crate) struct Bad2AbstractMapper {
        abstract_model: abstract_model::Counter,
    }

    // no auxiliary state is needed.
    // Mapping ==
    //   INSTANCE abstract WITH
    //     counter <- counter,
    //     pc <- [t \in Threads |->
    //       IF pc[t] = "inc" THEN "start"
    //       ELSE pc[t]
    //       ]
    impl RefinementMapping<bad_impl::Counter, abstract_model::Counter> for Bad2AbstractMapper {
        type AuxState = ();

        fn abstract_model(&self) -> &abstract_model::Counter {
            &self.abstract_model
        }

        fn init_aux_state(
            &self,
            _concrete: &<bad_impl::Counter as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn advance_aux_state(
            &self,
            _last_concrete: &<bad_impl::Counter as stateright::Model>::State,
            _last_aux: &Self::AuxState,
            _action: &<bad_impl::Counter as stateright::Model>::Action,
            _next_concrete: &<bad_impl::Counter as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn map_state(
            &self,
            concrete: &<bad_impl::Counter as stateright::Model>::State,
            _aux: &Self::AuxState,
        ) -> <abstract_model::Counter as stateright::Model>::State {
            abstract_model::CounterState {
                pc: concrete
                    .pc
                    .iter()
                    .map(|s| match s {
                        bad_impl::TransitionState::Start => abstract_model::TransitionState::Start,
                        bad_impl::TransitionState::Inc => abstract_model::TransitionState::Start,
                        bad_impl::TransitionState::Done => abstract_model::TransitionState::Done,
                    })
                    .collect(),
                counter: concrete.counter,
            }
        }
    }

    pub fn refinement_checker_serve(
        num_threads: usize,
    ) -> std::sync::Arc<
        impl Checker<RefinementModel<bad_impl::Counter, abstract_model::Counter, Bad2AbstractMapper>>,
    > {
        let concrete = bad_impl::Counter {
            threads: num_threads,
        };
        let abstractt = abstract_model::Counter {
            threads: num_threads,
        };
        let mapper = Bad2AbstractMapper {
            abstract_model: abstractt,
        };
        let refinement_model = RefinementModel::new(concrete, mapper);
        let checker = refinement_model
            .checker()
            .threads(num_cpus::get())
            .serve("127.0.0.1:3000");

        checker
    }
}

mod good_refine_abstract {
    use stateright::{
        refinement_mapping::{RefinementMapping, RefinementModel},
        Checker, Model,
    };

    use crate::{abstract_model, good_impl};

    #[derive(Debug, Hash, Clone, PartialEq)]
    pub(crate) struct Good2AbstractMapper {
        abstract_model: abstract_model::Counter,
    }

    // no auxiliary state is needed
    // Mapping ==
    //   INSTANCE abstract WITH
    //     counter <- counter,
    //     pc <- [t \in Threads |->
    //       IF pc[t] = "inc" THEN "start"
    //       ELSE pc[t]
    //       ]
    impl RefinementMapping<good_impl::Counter, abstract_model::Counter> for Good2AbstractMapper {
        type AuxState = ();

        fn abstract_model(&self) -> &abstract_model::Counter {
            &self.abstract_model
        }

        fn init_aux_state(
            &self,
            _concrete: &<good_impl::Counter as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn advance_aux_state(
            &self,
            _last_concrete: &<good_impl::Counter as stateright::Model>::State,
            _last_aux: &Self::AuxState,
            _action: &<good_impl::Counter as stateright::Model>::Action,
            _next_concrete: &<good_impl::Counter as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn map_state(
            &self,
            concrete: &<good_impl::Counter as stateright::Model>::State,
            _aux: &Self::AuxState,
        ) -> <abstract_model::Counter as stateright::Model>::State {
            abstract_model::CounterState {
                pc: concrete
                    .pc
                    .iter()
                    .map(|s| match s {
                        good_impl::TransitionState::Start => abstract_model::TransitionState::Start,
                        good_impl::TransitionState::Inc => abstract_model::TransitionState::Start,
                        good_impl::TransitionState::Done => abstract_model::TransitionState::Done,
                    })
                    .collect(),
                counter: concrete.counter,
            }
        }
    }

    pub fn refinement_checker_serve(
        num_threads: usize,
    ) -> std::sync::Arc<
        impl Checker<RefinementModel<good_impl::Counter, abstract_model::Counter, Good2AbstractMapper>>,
    > {
        let concrete = good_impl::Counter {
            threads: num_threads,
        };
        let abstractt = abstract_model::Counter {
            threads: num_threads,
        };
        let mapper = Good2AbstractMapper {
            abstract_model: abstractt,
        };
        let refinement_model = RefinementModel::new(concrete, mapper);
        let checker = refinement_model
            .checker()
            .threads(num_cpus::get())
            .serve("127.0.0.1:3000");

        checker
    }
}

mod good_refine_bad {
    use stateright::{
        refinement_mapping::{RefinementMapping, RefinementModel},
        Checker, Model,
    };

    use crate::{bad_impl, good_impl};

    #[derive(Debug, Hash, Clone, PartialEq)]
    pub(crate) struct Good2BadMapper {
        abstract_model: bad_impl::Counter,
    }

    // no auxiliary state is needed
    impl RefinementMapping<good_impl::Counter, bad_impl::Counter> for Good2BadMapper {
        type AuxState = ();

        fn abstract_model(&self) -> &bad_impl::Counter {
            &self.abstract_model
        }

        fn init_aux_state(
            &self,
            _concrete: &<good_impl::Counter as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn advance_aux_state(
            &self,
            _last_concrete: &<good_impl::Counter as stateright::Model>::State,
            _last_aux: &Self::AuxState,
            _action: &<good_impl::Counter as stateright::Model>::Action,
            _next_concrete: &<good_impl::Counter as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn map_state(
            &self,
            concrete: &<good_impl::Counter as stateright::Model>::State,
            _aux: &Self::AuxState,
        ) -> <bad_impl::Counter as stateright::Model>::State {
            bad_impl::CounterState {
                pc: concrete
                    .pc
                    .iter()
                    .map(|s| match s {
                        good_impl::TransitionState::Start => bad_impl::TransitionState::Start,
                        good_impl::TransitionState::Inc => bad_impl::TransitionState::Inc,
                        good_impl::TransitionState::Done => bad_impl::TransitionState::Done,
                    })
                    .collect(),
                counter: concrete.counter,
                tmp: concrete.tmp.clone(),
            }
        }
    }

    pub fn refinement_checker_serve(
        num_threads: usize,
    ) -> std::sync::Arc<
        impl Checker<RefinementModel<good_impl::Counter, bad_impl::Counter, Good2BadMapper>>,
    > {
        let concrete = good_impl::Counter {
            threads: num_threads,
        };
        let abstractt = bad_impl::Counter {
            threads: num_threads,
        };
        let mapper = Good2BadMapper {
            abstract_model: abstractt,
        };
        let refinement_model = RefinementModel::new(concrete, mapper);
        let checker = refinement_model
            .checker()
            .threads(num_cpus::get())
            .serve("127.0.0.1:3000");

        checker
    }
}

fn main() -> Result<(), pico_args::Error> {
    env_logger::init_from_env(env_logger::Env::default().default_filter_or("info")); // `RUST_LOG=${LEVEL}` env variable to override

    let mut args = pico_args::Arguments::from_env();
    let num_threads = 2;
    match args.subcommand()?.as_deref() {
        Some("b2a") => {
            println!(
                "Checking refinement from bad implementation to abstract model. Serving on: http://127.0.0.1:3000"
            );
            try_bad_refine_abstract::refinement_checker_serve(num_threads);
        }
        Some("g2a") => {
            println!(
                "Checking refinement from good implementation to abstract model. Serving on: http://127.0.0.1:3000"
            );
            good_refine_abstract::refinement_checker_serve(num_threads);
        }
        Some("g2b") => {
            println!(
                "Checking refinement from good implementation to bad implementation. Serving on: http://127.0.0.1:3000"
            );
            good_refine_bad::refinement_checker_serve(num_threads);
        }
        _ => {
            println!("Supported arguments:");
            println!("  b2a");
            println!("  g2a");
            println!("  g2b");
        }
    }

    Ok(())
}
