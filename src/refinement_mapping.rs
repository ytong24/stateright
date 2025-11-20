use crate::{fingerprint, Model, Property};
use std::{
    collections::HashMap,
    fmt::{Debug, Write},
    hash::Hash,
    marker::PhantomData,
};

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

    // use this field to print out all the possible next states by providing the prev_mapped_abstract_state to the abstract model.
    debug_from_prev_all: Vec<A::State>,
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

    // helper function for producing svg
    fn escape_html(input: &str) -> String {
        let mut escaped = String::with_capacity(input.len());
        for ch in input.chars() {
            match ch {
                '&' => escaped.push_str("&amp;"),
                '<' => escaped.push_str("&lt;"),
                '>' => escaped.push_str("&gt;"),
                '"' => escaped.push_str("&quot;"),
                '\'' => escaped.push_str("&#x27;"),
                _ => escaped.push(ch),
            }
        }
        escaped
    }
}

impl<C, A, Map> Model for RefinementModel<C, A, Map>
where
    C: Model,
    C::Action: Clone,
    C::State: Clone + Debug + Hash,
    A: Model,
    A::State: Clone + PartialEq + Debug + Hash,
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
                    debug_from_prev_all: vec![],
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

        let debug_from_prev_all = self
            .mapper
            .abstract_model()
            .next_states(&last_state.mapped_abstract_state);

        Some(RefinementModelState {
            concrete_state: next_concrete,
            aux_state: next_aux,
            mapped_abstract_state: next_mapped_abstract,
            prev_mapped_abstract_state: Some(last_state.mapped_abstract_state.clone()),
            debug_from_prev_all,
        })
    }

    fn properties(&self) -> Vec<Property<Self>> {
        vec![Property::always("check_simulation", Self::check_simulation)]
    }

    fn as_svg(&self, path: crate::Path<Self::State, Self::Action>) -> Option<String> {
        let steps = path.into_vec();
        if steps.is_empty() {
            return None;
        }

        #[derive(Clone)]
        struct NodeMeta {
            label: String,
            title: String,
        }

        let mut abstract_slots: HashMap<u64, usize> = HashMap::new();
        let mut abstract_nodes = Vec::new();
        let mut concrete_nodes = Vec::new();
        let mut mapping_slots = Vec::new();

        let build_title = |kind: &str, idx: usize, fp: u64, value: String| -> String {
            format!(
                "{kind} state #{idx}\nfingerprint=0x{fp:016x}\n{value}",
                value = value
            )
        };

        for (step_idx, (state, _)) in steps.iter().enumerate() {
            // Concrete node metadata always uses the step index.
            let concrete_fp = fingerprint(&state.concrete_state).get();
            concrete_nodes.push(NodeMeta {
                label: format!("C{step_idx}"),
                title: build_title(
                    "Concrete",
                    step_idx,
                    concrete_fp,
                    format!("{:#?}", state.concrete_state),
                ),
            });

            // Abstract nodes dedupe via fingerprint/slot.
            let abstract_fp = fingerprint(&state.mapped_abstract_state).get();
            let slot = *abstract_slots.entry(abstract_fp).or_insert_with(|| {
                let slot_idx = abstract_nodes.len();
                abstract_nodes.push(NodeMeta {
                    label: format!("A{slot_idx}"),
                    title: build_title(
                        "Abstract",
                        slot_idx,
                        abstract_fp,
                        format!("{:#?}", state.mapped_abstract_state),
                    ),
                });
                slot_idx
            });
            mapping_slots.push(slot);
        }

        let horizontal_gap = 150usize;
        let vertical_gap = 160usize;
        let left_padding = 140usize;
        let right_padding = 120usize;
        let top_padding = 80usize;
        let radius = 22usize;

        let span = std::cmp::max(
            abstract_nodes.len().saturating_sub(1),
            concrete_nodes.len().saturating_sub(1),
        );
        let width = left_padding + right_padding + horizontal_gap.saturating_mul(span);
        let height = top_padding * 2 + vertical_gap;
        let abstract_y = top_padding;
        let concrete_y = top_padding + vertical_gap;

        let mut svg = String::new();
        let _ = write!(
            &mut svg,
            "<svg version='1.1' baseProfile='full' width='{width}' height='{height}' \
           viewBox='0 0 {width} {height}' xmlns='http://www.w3.org/2000/svg'>"
        );
        let _ = write!(
          &mut svg,
          "<defs>\
             <marker id='refinement-arrow' markerWidth='12' markerHeight='10' refX='12' refY='5' orient='auto'>\
               <polygon points='0 0, 12 5, 0 10' class='svg-ref-edge-head'/>\
             </marker>\
           </defs>"
      );
        let _ = write!(
            &mut svg,
            "<text class='svg-ref-label' x='20' y='{abstract_y}'>Abstract Model</text>\
           <text class='svg-ref-label' x='20' y='{concrete_y}'>Concrete Model</text>"
        );

        // Concrete transition edges (solid, sequential).
        for window in (0..concrete_nodes.len()).collect::<Vec<_>>().windows(2) {
            if let [left, right] = window {
                let _ = write!(
                  &mut svg,
                  "<line x1='{x1}' y1='{con_y}' x2='{x2}' y2='{con_y}' class='svg-ref-edge' marker-end='url(#refinement-arrow)'/>",
                  x1 = left_padding + left * horizontal_gap,
                  x2 = left_padding + right * horizontal_gap,
                  con_y = concrete_y,
              );
            }
        }

        // Abstract transition edges (solid between slot ordering).
        for window in (0..abstract_nodes.len()).collect::<Vec<_>>().windows(2) {
            if let [left, right] = window {
                let _ = write!(
                  &mut svg,
                  "<line x1='{x1}' y1='{abs_y}' x2='{x2}' y2='{abs_y}' class='svg-ref-edge' marker-end='url(#refinement-arrow)'/>",
                  x1 = left_padding + left * horizontal_gap,
                  x2 = left_padding + right * horizontal_gap,
                  abs_y = abstract_y,
              );
            }
        }

        // Mapping lines from each concrete state to its abstract slot.
        for (step_idx, slot_idx) in mapping_slots.into_iter().enumerate() {
            let _ = write!(
                &mut svg,
                "<line x1='{x1}' y1='{y1}' x2='{x2}' y2='{y2}' class='svg-ref-mapping-line'/>",
                x1 = left_padding + step_idx * horizontal_gap,
                y1 = concrete_y - radius,
                x2 = left_padding + slot_idx * horizontal_gap,
                y2 = abstract_y + radius,
            );
        }

        // Emit abstract circles.
        for (slot_idx, node) in abstract_nodes.iter().enumerate() {
            let x = left_padding + slot_idx * horizontal_gap;
            let _ = write!(
                &mut svg,
                "<g class='svg-ref-node'>\
                 <circle class='svg-ref-state-circle' cx='{x}' cy='{abstract_y}' r='{radius}'>\
                   <title>{title}</title>\
                 </circle>\
                 <text class='svg-ref-state-text' x='{x}' y='{abstract_y}'>{label}</text>\
               </g>",
                title = Self::escape_html(&node.title),
                label = Self::escape_html(&node.label),
            );
        }

        // Emit concrete circles.
        for (step_idx, node) in concrete_nodes.iter().enumerate() {
            let x = left_padding + step_idx * horizontal_gap;
            let _ = write!(
                &mut svg,
                "<g class='svg-ref-node'>\
                 <circle class='svg-ref-state-circle' cx='{x}' cy='{concrete_y}' r='{radius}'>\
                   <title>{title}</title>\
                 </circle>\
                 <text class='svg-ref-state-text' x='{x}' y='{concrete_y}'>{label}</text>\
               </g>",
                title = Self::escape_html(&node.title),
                label = Self::escape_html(&node.label),
            );
        }

        svg.push_str("</svg>");
        Some(svg)
    }
}
