//! This file is the MinMax example of Lamport's paper [Auxiliary Variables in TLA+](https://lamport.azurewebsites.net/pubs/auxiliary.pdf) which discusses refinement mappings and auxiliary variables in TLA+.
//!
//! # MinMax
//! A user presents a server with a sequence of integer inputs.
//! The server responds to each input value *i* with one of the following outputs:
//! *Hi* if *i* is the largest number input so far,
//! *Lo* if it’s the smallest number input so far,
//! *Both* if it’s both,
//! and *None* if it’s neither.
//! We declare *Hi* , *Lo*, *Both*, and *None* in a constants statement. They are assumed not to be integers.
//!
//! ## MinMax1
//! Our first specification appears in a module named MinMax 1.
//! It describes the interaction of the user and the server with two variables: a variable x to hold an input or a response, and a variable turn that indicates whether it’s the user’s turn to input a value or the server’s turn to respond.
//! The specification also uses a variable y to hold the set of values input so far.
//! ```tla+
//!
//! ------------------------------- MODULE MinMax1 ------------------------------
//! (***************************************************************************)
//! (* This module and modules MinMax2 and MinMax2H are used as examples in    *)
//! (* Sections 1 and 2 of the paper "Auxiliary Variables in TLA+".            *)
//! (*                                                                         *)
//! (* This module specifies a tiny system in which a user presents a server   *)
//! (* with a sequence of integer inputs, and the server responds to each      *)
//! (* input value i with with one of the following outputs: Hi if i is the    *)
//! (* largest number input so far, Lo if it's the smallest number input so    *)
//! (* far, Both if it's both, and None if it's neither.                       *)
//! (*                                                                         *)
//! (* The module is part of an example illustrating the use of a history      *)
//! (* variable.  The example includes this module, module MinMax2, and module *)
//! (* MinMax2H which adds a history variable to the specification of MinMax2  *)
//! (* and shows that the resulting specification implements implements the    *)
//! (* specification of the current module under a suitable refinement         *)
//! (* mapping.                                                                *)
//! (***************************************************************************)
//! EXTENDS Integers
//!
//! (***************************************************************************)
//! (* We define setMax(S) and setMin(S) to be largest and smallest value in a *)
//! (* nonempty finite set S of integers.                                      *)
//! (***************************************************************************)
//! setMax(S) == CHOOSE t \in S : \A s \in S : t >= s
//! setMin(S) == CHOOSE t \in S : \A s \in S : t =< s
//!
//! (***************************************************************************)
//! (* The possible values that can be returned by the system are declared to  *)
//! (* be constants, which we assume are not integers.                         *)
//! (***************************************************************************)
//! CONSTANTS Lo, Hi, Both, None
//! ASSUME {Lo, Hi, Both, None} \cap Int = { }
//!
//! (***************************************************************************)
//! (* The the value of the variable x is the value input by the user or the   *)
//! (* value output by the system, the variable `turn' indicating which.  The  *)
//! (* variable y holds the set of all values input thus far.  We consider x   *)
//! (* and `turn' to be externally visible and y to be internal.               *)
//! (***************************************************************************)
//! VARIABLES x, turn, y
//! vars == <<x, turn, y>>
//!
//! (***************************************************************************)
//! (* The initial predicate Init:                                             *)
//! (***************************************************************************)
//! Init ==  /\ x = None
//!          /\ turn = "input"
//!          /\ y = {}
//!
//! (***************************************************************************)
//! (* The user's input action:                                                *)
//! (***************************************************************************)
//! InputNum ==  /\ turn = "input"
//!              /\ turn' = "output"
//!              /\ x' \in Int
//!              /\ y' = y
//!
//! (***************************************************************************)
//! (* The systems response action:                                            *)
//! (***************************************************************************)
//! Respond == /\ turn = "output"
//!            /\ turn' = "input"
//!            /\ y' = y \cup {x}
//!            /\ x' = IF x = setMax(y') THEN IF x = setMin(y') THEN Both ELSE Hi  
//!                                      ELSE IF x = setMin(y') THEN Lo   ELSE None
//!
//! (***************************************************************************)
//! (* The next-state action:                                                  *)
//! (***************************************************************************)  
//! Next == InputNum \/ Respond
//!
//! (***************************************************************************)
//! (* The specification, which is a safety property (it asserts no liveness   *)
//! (* condition).                                                             *)
//! (***************************************************************************)
//! Spec == Init /\ [][Next]_vars
//! -----------------------------------------------------------------------------
//! (***************************************************************************)
//! (* Below, we check that specification Spec implements specification Spec   *)
//! (* of module MinMax2 under a suitable refinement mapping.  The following   *)
//! (* definitions of Infinity and MinusInfinity are copied from module        *)
//! (* MinMax2.                                                                *)
//! (***************************************************************************)
//! Infinity      == CHOOSE n : n \notin Int
//! MinusInfinity == CHOOSE n : n \notin (Int \cup {Infinity})
//!
//! M == INSTANCE MinMax2
//!         WITH min <- IF y = {} THEN Infinity      ELSE setMin(y),
//!              max <- IF y = {} THEN MinusInfinity ELSE setMax(y)
//!
//! (***************************************************************************)
//! (* The following theorem asserts that Spec implements the specification    *)
//! (* Spec of module MinMax2 under the refinement mapping defined by the      *)
//! (* INSTANCE statement.  The theorem can be checked with TLC using a model  *)
//! (* having M!Spec as the temporal property to be checked.                   *)
//! (***************************************************************************)
//! THEOREM Spec => M!Spec
//! =============================================================================
//!
//! ```
//!
//!
//! ## MinMax2
//! The specification of our system in module MinMax 1 uses the variable y to remember the set of all values that the user has input.
//! Module MinMax 2 specifies the same user/server interaction that remembers only the smallest and largest values input so far,
//! using the variables min and max.
//!
//! ```tla+
//! ------------------------------ MODULE MinMax2 -------------------------------
//! (***************************************************************************)
//! (* This module specifies a system with the same interaction between a user *)
//! (* and a server as the one in module MinMax1, but instead of remembering   *)
//! (* the entire set of inputs, it uses two variables min and max to keep the *)
//! (* largest and smallest values input thus far.  Initially min equals       *)
//! (* Infinity and max equals MinusInfinity, where Infinity and MinusInfinity *)
//! (* are two values that are considered greater than and less than any       *)
//! (* integer, respectively.                                                  *)
//! (***************************************************************************)
//! EXTENDS Integers, Sequences
//!
//! CONSTANTS Lo, Hi, Both, None
//! ASSUME {Lo, Hi, Both, None} \cap Int = { }
//!
//! Infinity      == CHOOSE n : n \notin Int
//! MinusInfinity == CHOOSE n : n \notin (Int \cup {Infinity})
//!
//! (***************************************************************************)
//! (* The operators IsLeq and IsGeq extend =< and >=, respectively, to have   *)
//! (* the correct meaning when Infinity or MinusInfinity is one of the        *)
//! (* arguments.                                                              *)
//! (***************************************************************************)
//! IsLeq(i, j) == (j = Infinity) \/ (i =< j)
//! IsGeq(i, j) == (j = MinusInfinity) \/ (i >= j)
//!
//! (***************************************************************************)
//! (* The rest of the specification is straightforward.                       *)
//! (***************************************************************************)
//! VARIABLES x, turn, min, max
//! vars == <<x, turn, min, max>>
//!
//! Init ==  /\ x = None
//!          /\ turn = "input"
//!          /\ min = Infinity
//!          /\ max = MinusInfinity
//!
//! InputNum ==  /\ turn = "input"
//!              /\ turn' = "output"
//!              /\ x' \in Int
//!              /\ UNCHANGED <<min, max>>
//!
//! Respond  ==  /\ turn = "output"
//!              /\ turn' = "input"
//!              /\ min' = IF IsLeq(x, min) THEN x ELSE min
//!              /\ max' = IF IsGeq(x, max) THEN x ELSE max
//!              /\ x' = IF x = max' THEN IF x = min' THEN Both ELSE Hi  
//!                                  ELSE IF x = min' THEN Lo   ELSE None
//!           
//! Next == InputNum \/ Respond
//!
//! Spec == Init /\ [][Next]_vars
//! =============================================================================
//!
//! ```
//!

use stateright::Checker;

mod min_max1 {
    use stateright::Model;

    use crate::min_max2;

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum Turn {
        Input,
        Output,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum Response {
        Lo,
        Hi,
        Both,
        None,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum XType {
        Input(usize),
        Output(Response),
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct MinMax1State {
        pub x: Option<XType>,
        pub turn: Turn,
        pub y: Vec<usize>,

        pub idx: usize,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub(crate) enum MinMax1Action {
        InputNum,
        Respond,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct MinMax1 {
        pub user_input: Vec<usize>,
    }

    impl Model for MinMax1 {
        type State = MinMax1State;

        type Action = MinMax1Action;

        fn init_states(&self) -> Vec<Self::State> {
            vec![MinMax1State {
                x: None,
                turn: Turn::Input,
                y: vec![],
                idx: 0,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            match state.turn {
                Turn::Input => actions.push(MinMax1Action::InputNum),
                Turn::Output => actions.push(MinMax1Action::Respond),
            }
        }

        fn next_state(
            &self,
            last_state: &Self::State,
            action: Self::Action,
        ) -> Option<Self::State> {
            if last_state.idx == self.user_input.len() {
                return None;
            }

            let mut state = last_state.clone();

            match action {
                MinMax1Action::InputNum => {
                    // turn' = output
                    state.turn = Turn::Output;
                    // x' \in Int
                    state.x = Some(XType::Input(self.user_input[last_state.idx]));
                    state.idx += 1;
                    // y' = y. keep y unchanged.
                }
                MinMax1Action::Respond => {
                    // turn' = "input"
                    state.turn = Turn::Input;
                    // y' = y \union {x}
                    if let Some(XType::Input(x)) = last_state.x {
                        state.y.push(x);

                        // x' = IF x = Max(y')
                        //      THEN IF x = Min(y') THEN Both ELSE Hi
                        //      ELSE IF x = Min(y') THEN Lo ELSE None
                        let y_max = *state.y.iter().max().unwrap();
                        let y_min = *state.y.iter().min().unwrap();
                        if x == y_max && x == y_min {
                            state.x = Some(XType::Output(Response::Both))
                        } else if x == y_max {
                            state.x = Some(XType::Output(Response::Hi))
                        } else if x == y_min {
                            state.x = Some(XType::Output(Response::Lo))
                        } else {
                            state.x = Some(XType::Output(Response::None))
                        }
                    }
                }
            }

            Some(state)
        }
    }

    impl From<min_max2::Response> for Response {
        fn from(value: min_max2::Response) -> Self {
            match value {
                min_max2::Response::Lo => Self::Lo,
                min_max2::Response::Hi => Self::Hi,
                min_max2::Response::Both => Self::Both,
                min_max2::Response::None => Self::None,
            }
        }
    }

    impl From<min_max2::XType> for XType {
        fn from(value: min_max2::XType) -> Self {
            match value {
                min_max2::XType::Input(x) => Self::Input(x),
                min_max2::XType::Output(response) => Self::Output(response.into()),
            }
        }
    }

    impl From<min_max2::Turn> for Turn {
        fn from(value: min_max2::Turn) -> Self {
            match value {
                min_max2::Turn::Input => Self::Input,
                min_max2::Turn::Output => Self::Output,
            }
        }
    }
}

mod min_max2 {
    use std::{
        cmp::{max, min},
        usize,
    };

    use stateright::Model;

    use crate::min_max1;

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum Turn {
        Input,
        Output,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum Response {
        Lo,
        Hi,
        Both,
        None,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) enum XType {
        Input(usize),
        Output(Response),
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct MinMax2State {
        pub x: Option<XType>,
        pub turn: Turn,
        pub min: usize,
        pub max: usize,

        pub idx: usize,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub(crate) enum MinMax2Action {
        InputNum,
        Respond,
    }

    #[derive(Debug, Clone, Hash, PartialEq)]
    pub(crate) struct MinMax2 {
        pub user_input: Vec<usize>,
    }

    impl Model for MinMax2 {
        type State = MinMax2State;

        type Action = MinMax2Action;

        fn init_states(&self) -> Vec<Self::State> {
            vec![MinMax2State {
                x: None,
                turn: Turn::Input,
                min: usize::MAX, // set initial min as MAX
                max: usize::MIN, // set initial max as MIN
                idx: 0,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            match state.turn {
                Turn::Input => actions.push(MinMax2Action::InputNum),
                Turn::Output => actions.push(MinMax2Action::Respond),
            }
        }

        fn next_state(
            &self,
            last_state: &Self::State,
            action: Self::Action,
        ) -> Option<Self::State> {
            if last_state.idx == self.user_input.len() {
                return None;
            }

            let mut state = last_state.clone();

            match action {
                MinMax2Action::InputNum => {
                    // turn' = "output"
                    state.turn = Turn::Output;
                    // x' \in Int
                    state.x = Some(XType::Input(self.user_input[last_state.idx]));
                    state.idx += 1;
                    // UNCHANGED <<min, max>>
                }
                MinMax2Action::Respond => {
                    // turn' = "input"
                    state.turn = Turn::Input;
                    if let Some(XType::Input(x)) = last_state.x {
                        // min' = IF IsLeq(x, min) THEN x ELSE min
                        state.min = min(x, last_state.min);
                        // max' = IF IsGeq(x, max) THEN x ELSE max
                        state.max = max(x, last_state.max);
                        // x' = IF x = max' THEN IF x = min' THEN Both ELSE Hi ELSE IF x = min' THEN Lo ELSE None
                        let resp = if x == state.max && x == state.min {
                            Response::Both
                        } else if x == state.max {
                            Response::Hi
                        } else if x == state.min {
                            Response::Lo
                        } else {
                            Response::None
                        };
                        state.x = Some(XType::Output(resp));
                    }
                }
            }

            Some(state)
        }
    }

    impl From<min_max1::Response> for Response {
        fn from(value: min_max1::Response) -> Self {
            match value {
                min_max1::Response::Lo => Self::Lo,
                min_max1::Response::Hi => Self::Hi,
                min_max1::Response::Both => Self::Both,
                min_max1::Response::None => Self::None,
            }
        }
    }

    impl From<min_max1::XType> for XType {
        fn from(value: min_max1::XType) -> Self {
            match value {
                min_max1::XType::Input(x) => Self::Input(x),
                min_max1::XType::Output(response) => Self::Output(response.into()),
            }
        }
    }

    impl From<min_max1::Turn> for Turn {
        fn from(value: min_max1::Turn) -> Self {
            match value {
                min_max1::Turn::Input => Self::Input,
                min_max1::Turn::Output => Self::Output,
            }
        }
    }
}

mod one_refine_two {
    // try to build refinement mapping from MinMax1 to MinMax2.
    // That is, we treat MinMax1 as concrete implementation and MinMax2 as abstract model

    use stateright::{
        refinement_mapping::{RefinementMapping, RefinementModel},
        Checker, Model,
    };

    use crate::{min_max1::*, min_max2::*};

    #[derive(Debug, Hash, Clone, PartialEq)]
    pub(crate) struct Mapper1to2 {
        abstract_model: MinMax2,
    }

    /// We don't need auxiliary states to build MinMax1 to MinMax2
    /// M == INSTANCE MinMax2
    ///     WITH min <- IF y = {} THEN Infinity ELSE setMin(y),
    ///         max <- IF y = {} THEN MinusInfinity ELSE setMax(y).
    impl RefinementMapping<MinMax1, MinMax2> for Mapper1to2 {
        type AuxState = ();

        fn abstract_model(&self) -> &MinMax2 {
            &self.abstract_model
        }

        fn init_aux_state(
            &self,
            _concrete: &<MinMax1 as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn advance_aux_state(
            &self,
            _last_concrete: &<MinMax1 as stateright::Model>::State,
            _last_aux: &Self::AuxState,
            _action: &<MinMax1 as stateright::Model>::Action,
            _next_concrete: &<MinMax1 as stateright::Model>::State,
        ) -> Self::AuxState {
            ()
        }

        fn map_state(
            &self,
            concrete: &<MinMax1 as stateright::Model>::State,
            _aux: &Self::AuxState,
        ) -> <MinMax2 as stateright::Model>::State {
            MinMax2State {
                x: concrete.x.clone().map(|x| x.into()),
                turn: concrete.turn.clone().into(),
                min: *concrete.y.iter().min().unwrap_or(&usize::MAX),
                max: *concrete.y.iter().max().unwrap_or(&usize::MIN),
                idx: concrete.idx,
            }
        }
    }

    pub fn refinement_checker(
        user_input: Vec<usize>,
    ) -> impl Checker<RefinementModel<MinMax1, MinMax2, Mapper1to2>> {
        let concrete = MinMax1 {
            user_input: user_input.clone(),
        };
        let abstractt = MinMax2 { user_input };
        let mapper = Mapper1to2 {
            abstract_model: abstractt,
        };
        let refinement_model = RefinementModel::new(concrete, mapper);
        let checker = refinement_model
            .checker()
            .threads(num_cpus::get())
            .spawn_dfs();

        checker
    }

    pub fn refinement_serve(
        user_input: Vec<usize>,
    ) -> std::sync::Arc<impl Checker<RefinementModel<MinMax1, MinMax2, Mapper1to2>>> {
        let concrete = MinMax1 {
            user_input: user_input.clone(),
        };
        let abstractt = MinMax2 { user_input };
        let mapper = Mapper1to2 {
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

mod two_refine_one {
    use stateright::{
        refinement_mapping::{RefinementMapping, RefinementModel},
        Checker, Model,
    };

    use crate::{
        min_max1::{MinMax1, MinMax1State},
        min_max2::{MinMax2, MinMax2Action, XType},
    };

    #[derive(Debug, Hash, Clone, PartialEq)]
    pub(crate) struct Mapper2to1 {
        abstract_model: MinMax1,
    }

    /// we need auxiliary state to have refinement mapping from MinMax2 to MinMax1,
    /// because MinMax2 only stores the min and max, while MinMax1 stores all the history.
    /// so, our auxiliary state for MinMax2 is basically a history that store all the values MinMax2 has seen so far.
    ///
    /// M == INSTANCE MinMax1 WITH y <- h

    type History = Vec<usize>;

    impl RefinementMapping<MinMax2, MinMax1> for Mapper2to1 {
        type AuxState = History;

        fn abstract_model(&self) -> &MinMax1 {
            &self.abstract_model
        }

        fn init_aux_state(
            &self,
            _concrete: &<MinMax2 as stateright::Model>::State,
        ) -> Self::AuxState {
            // initally, the history is an empty vec
            vec![]
        }

        fn advance_aux_state(
            &self,
            last_concrete: &<MinMax2 as stateright::Model>::State,
            last_aux: &Self::AuxState,
            action: &<MinMax2 as stateright::Model>::Action,
            _next_concrete: &<MinMax2 as stateright::Model>::State,
        ) -> Self::AuxState {
            let mut new_aux = last_aux.clone();

            // NOTE: the following code is incorrect for the refinement mapping. Using the code will fail the refinement model checking.
            // match action {
            //     MinMax2Action::InputNum => {
            //         // the newly inserted number is the next_concrete.x
            //         if let Some(XType::Input(n)) = next_concrete.x {
            //             new_aux.push(n);
            //         } else {
            //             panic!("State transition doesn't match with action. Action is InputNum, but next_state.x is not XType::Input.")
            //         }
            //     }
            //     MinMax2Action::Respond => {} // no update is needed if action is Respond
            // }

            match action {
                MinMax2Action::InputNum => {} // no update is needed if action is InputNum
                MinMax2Action::Respond => {
                    // the newly inserted number is the last_concrete.x
                    if let Some(XType::Input(n)) = last_concrete.x {
                        new_aux.push(n);
                    } else {
                        panic!("State transition doesn't match with action. Action is Respond, but last_concrete.x is not XType::Input.")
                    }
                }
            }

            new_aux
        }

        fn map_state(
            &self,
            concrete: &<MinMax2 as stateright::Model>::State,
            aux: &Self::AuxState,
        ) -> <MinMax1 as stateright::Model>::State {
            MinMax1State {
                x: concrete.x.clone().map(|x| x.into()),
                turn: concrete.turn.clone().into(),
                y: aux.clone(),
                idx: concrete.idx,
            }
        }
    }

    pub fn refinement_checker(
        user_input: Vec<usize>,
    ) -> impl Checker<RefinementModel<MinMax2, MinMax1, Mapper2to1>> {
        let concrete = MinMax2 {
            user_input: user_input.clone(),
        };
        let abstractt = MinMax1 { user_input };
        let mapper = Mapper2to1 {
            abstract_model: abstractt,
        };
        let refinement_model = RefinementModel::new(concrete, mapper);
        let checker = refinement_model
            .checker()
            .threads(num_cpus::get())
            .spawn_dfs();

        checker
    }

    pub fn refinement_serve(
        user_input: Vec<usize>,
    ) -> std::sync::Arc<impl Checker<RefinementModel<MinMax2, MinMax1, Mapper2to1>>> {
        let concrete = MinMax2 {
            user_input: user_input.clone(),
        };
        let abstractt = MinMax1 { user_input };
        let mapper = Mapper2to1 {
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
    let user_input = vec![4, 1, 2, 3];
    match args.subcommand()?.as_deref() {
        Some("12") => {
            println!("Checking refinement from MinMax1 to MinMax2...");
            let checker = one_refine_two::refinement_checker(user_input).join();
            println!("Finish. State count: {}", checker.state_count());
        }
        Some("21") => {
            println!("Checking refinement from MinMax2 to MinMax1...");
            let checker = two_refine_one::refinement_checker(user_input).join();
            println!("Finish. State count: {}", checker.state_count());
        }
        Some("12-serve") => {
            println!(
                "Checking refinement from MinMax1 to MinMax2. Serving on: http://127.0.0.1:3000"
            );
            one_refine_two::refinement_serve(user_input);
        }
        Some("21-serve") => {
            println!(
                "Checking refinement from MinMax2 to MinMax1. Serving on: http://127.0.0.1:3000"
            );
            two_refine_one::refinement_serve(user_input);
        }
        _ => {
            println!("USAGE:");
            println!("  ./min_max 12");
            println!("  ./min_max 21");
        }
    }

    Ok(())
}
