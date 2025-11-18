use crate::{Model, Property};
use std::marker::PhantomData;

pub trait RefinementMapping<C, A>
where
    C: Model,
    A: Model,
{
    type AuxState; // the auxiliary state for concrete model

    fn abstract_model(&self) -> &A;

    fn init_aux_state(&self, concrete: &C::State) -> Self::AuxState;

    fn advance_aux_state(
        &self,
        last_concrete: &C::State,
        last_aux: &Self::AuxState,
        action: &C::Action,
        next_concrete: &C::State,
    ) -> Self::AuxState;

    fn map_state(&self, concrete: &C::State, aux: &Self::AuxState) -> A::State;
}

#[derive(Debug, Clone, Hash, PartialEq, PartialOrd)]
pub struct RefinementModelState<C, A, Map>
where
    C: Model,
    A: Model,
    Map: RefinementMapping<C, A>,
{
    concrete_state: C::State,
    aux_state: Map::AuxState,
    mapped_abstract_state: A::State,

    // since "always" property will be checked after every state transition, we only need to store
    // the prev and the cur state for refinement mapping check.
    // prev is None when model state is the initial state. otherwise, it shouldn't be None.
    prev_mapped_abstract_state: Option<A::State>,
}

#[derive(Debug)]
pub struct RefinementModel<C, A, Map>
where
    C: Model,
    A: Model,
    A::State: PartialEq,
    Map: RefinementMapping<C, A>,
{
    concrete: C,
    mapper: Map,
    _phatom: PhantomData<A>,
}

impl<C, A, Map> RefinementModel<C, A, Map>
where
    C: Model,
    A: Model,
    A::State: PartialEq,
    Map: RefinementMapping<C, A>,
{
    pub fn new(concrete: C, mapper: Map) -> Self {
        Self {
            concrete,
            mapper,
            _phatom: PhantomData,
        }
    }

    fn check_simulation(model: &Self, state: &RefinementModelState<C, A, Map>) -> bool {
        //
        // (prev_mapped_abstract) ----------abstract_action-----------> (cur_mapped_abstract)
        //          ^                                                           ^
        //          |                                                           |
        //          f                                                           f
        //          |                                                           |
        //          |                                                           |
        // (prev_concrete, prev_aux) ---------concrete_action--------> (cur_concrete, cur_aux)
        //
        // To prove correspondence, we need to prove that:
        // prev_mapped_abstract ------------abstract_action------------> mapped_abstract
        //                                                                      ||
        //                                                                      ||
        // (prev_concrete, prev_aux) --> (cur_concrete, cur_aux) --f--> cur_mapped_abstract

        let abstract_model = model.mapper.abstract_model();
        let cur_mapped_abstract = &state.mapped_abstract_state;
        match &state.prev_mapped_abstract_state {
            Some(prev_mapped_abstract) => {
                if prev_mapped_abstract == cur_mapped_abstract {
                    // stuttering step
                    return true;
                }
                // check L-simulation
                abstract_model
                    .next_states(prev_mapped_abstract)
                    .iter()
                    .any(|mapped_abstract| mapped_abstract == cur_mapped_abstract)
            }
            None => {
                // check if cur_mapped_abstract is a valid initial states of the abstract model
                abstract_model
                    .init_states()
                    .iter()
                    .any(|valid_init| valid_init == cur_mapped_abstract)
            }
        }
    }
}

impl<C, A, Map> Model for RefinementModel<C, A, Map>
where
    C: Model,
    C::Action: Clone,
    C::State: Clone,
    A: Model,
    A::State: Clone + PartialEq,
    Map: RefinementMapping<C, A>,
    Map::AuxState: Clone,
{
    type State = RefinementModelState<C, A, Map>;

    type Action = C::Action;

    fn init_states(&self) -> Vec<Self::State> {
        self.concrete
            .init_states()
            .into_iter()
            .map(|concrete_state| {
                let aux_state = self.mapper.init_aux_state(&concrete_state);
                let mapped_abstract_state = self.mapper.map_state(&concrete_state, &aux_state);
                RefinementModelState {
                    concrete_state,
                    aux_state,
                    mapped_abstract_state,
                    prev_mapped_abstract_state: None,
                }
            })
            .collect()
    }

    fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
        // action should be the same as the concrete model's action
        self.concrete.actions(&state.concrete_state, actions);
    }

    fn next_state(&self, last_state: &Self::State, action: Self::Action) -> Option<Self::State> {
        let next_concrete = self
            .concrete
            .next_state(&last_state.concrete_state, action.clone())?;
        let next_aux = self.mapper.advance_aux_state(
            &last_state.concrete_state,
            &last_state.aux_state,
            &action,
            &next_concrete,
        );
        let next_mapped_abstract = self.mapper.map_state(&next_concrete, &next_aux);

        Some(RefinementModelState {
            concrete_state: next_concrete,
            aux_state: next_aux,
            mapped_abstract_state: next_mapped_abstract,
            prev_mapped_abstract_state: Some(last_state.mapped_abstract_state.clone()),
        })
    }

    fn properties(&self) -> Vec<Property<Self>> {
        vec![Property::always("check_simulation", Self::check_simulation)]
    }
}
