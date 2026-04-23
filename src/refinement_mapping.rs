use crate::{fingerprint, Model, Property};
use std::{
    collections::HashMap,
    fmt::{Debug, Write},
    hash::Hash,
    marker::PhantomData,
};

/// A refinement mapping from concrete model `C` into abstract model `A`.
///
/// A refinement mapping is defined by:
///
/// - an [`AuxState`](Self::AuxState) that evolves alongside the concrete
///   execution (Lamport's *auxiliary variables* — see Abadi & Lamport,
///   "The Existence of Refinement Mappings", 1991);
/// - [`refinement_map`](Self::refinement_map): the function `f` that picks
///   the abstract-state representative for a given `(concrete, aux)` pair;
/// - [`Observable`](Self::Observable) + [`observe`](Self::observe): the
///   observable interface — the contract the refinement preserves. The
///   refinement check compares only observations, so `Observable` names
///   what the concrete is required to simulate about the abstract.
///
/// Strict L-simulation is the special case where
/// `type Observable = A::State` and `fn observe(a) { a.clone() }` — every
/// field of the mapped abstract state is part of the contract. Choosing a
/// smaller `Observable` projects internal bookkeeping out of the check.
pub trait RefinementMapping<C, A>
where
    C: Model,
    A: Model,
{
    /// Auxiliary / history state carried alongside the concrete execution.
    /// Needed whenever the refinement mapping cannot be determined from
    /// the current concrete state alone.
    type AuxState;

    /// The observable interface — the contract the refinement preserves.
    type Observable: Clone + Eq + Debug;

    fn abstract_model(&self) -> &A;

    fn init_aux_state(&self, concrete: &C::State) -> Self::AuxState;

    fn advance_aux_state(
        &self,
        last_concrete: &C::State,
        last_aux: &Self::AuxState,
        action: &C::Action,
        next_concrete: &C::State,
    ) -> Self::AuxState;

    /// The refinement mapping `f`: pick the abstract-state representative
    /// for this `(concrete, aux)` pair. Load-bearing for L-simulation
    /// search — the check needs a concrete `A::State` to pass to
    /// `abstract_model.next_states(...)`.
    fn refinement_map(&self, concrete: &C::State, aux: &Self::AuxState) -> A::State;

    /// Project an abstract state to its observable interface. Called on
    /// both sides of the refinement check:
    ///
    /// - concrete observations flow through `observe(refinement_map(c, aux))`
    /// - abstract observations flow through `observe(a)` directly.
    fn observe(&self, a: &A::State) -> Self::Observable;
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

    // Since "always" properties are checked after every state transition, we
    // only need the previous and current mapped abstract states to verify
    // simulation. `prev` is `None` at initial states; non-`None` afterwards.
    prev_mapped_abstract_state: Option<A::State>,

    // Debug aid: all possible next abstract states reachable from
    // `prev_mapped_abstract_state` via the abstract model. Useful for
    // diagnosing which abstract transition (if any) matched.
    debug_from_prev_all: Vec<A::State>,
}

#[derive(Debug)]
pub struct RefinementModel<C, A, Map>
where
    C: Model,
    A: Model,
    Map: RefinementMapping<C, A>,
{
    concrete: C,
    mapper: Map,
    _phantom: PhantomData<A>,
}

impl<C, A, Map> RefinementModel<C, A, Map>
where
    C: Model,
    A: Model,
    Map: RefinementMapping<C, A>,
{
    pub fn new(concrete: C, mapper: Map) -> Self {
        Self {
            concrete,
            mapper,
            _phantom: PhantomData,
        }
    }

    fn check_simulation(model: &Self, state: &RefinementModelState<C, A, Map>) -> bool {
        //
        // (prev_mapped_abstract) ---------- abstract transition ---------> (cur_mapped_abstract)
        //          ^                                                              ^
        //          |                                                              |
        //          f                                                              f
        //          |                                                              |
        //          |                                                              |
        // (prev_concrete, prev_aux) --- concrete transition --> (cur_concrete, cur_aux)
        //
        // Weak L-simulation on `Observable`:
        //   observe(prev_mapped_abstract) == observe(cur_mapped_abstract)    (stutter)
        //   OR
        //   there exists an abstract transition from `prev_mapped_abstract`
        //   whose next state's observation equals
        //   `observe(cur_mapped_abstract)`.

        let abstract_model = model.mapper.abstract_model();
        let cur_abs = &state.mapped_abstract_state;
        let cur_obs = model.mapper.observe(cur_abs);

        match &state.prev_mapped_abstract_state {
            Some(prev_abs) => {
                if model.mapper.observe(prev_abs) == cur_obs {
                    // stutter on the observable
                    return true;
                }
                abstract_model
                    .next_states(prev_abs)
                    .iter()
                    .any(|next_abs| model.mapper.observe(next_abs) == cur_obs)
            }
            None => abstract_model
                .init_states()
                .iter()
                .any(|init_abs| model.mapper.observe(init_abs) == cur_obs),
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
    Map::AuxState: Clone + Hash + Debug,
{
    type State = RefinementModelState<C, A, Map>;

    type Action = C::Action;

    fn init_states(&self) -> Vec<Self::State> {
        self.concrete
            .init_states()
            .into_iter()
            .map(|concrete_state| {
                let aux_state = self.mapper.init_aux_state(&concrete_state);
                let mapped_abstract_state = self.mapper.refinement_map(&concrete_state, &aux_state);
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
        let next_mapped_abstract = self.mapper.refinement_map(&next_concrete, &next_aux);

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

        let build_title = |kind: &str, idx: usize, fp: u64, value: String| -> String {
            format!(
                "{kind} state #{idx}\nfingerprint=0x{fp:016x}\n{value}",
                value = value
            )
        };

        // Concrete layer: dedup by full-state fingerprint.
        // Abstract layer: dedup by Observable equivalence (linear scan).
        // Middle layer: one node per step (no dedup).
        let mut concrete_slots: HashMap<u64, usize> = HashMap::new();

        let mut abstract_nodes: Vec<(Map::Observable, NodeMeta)> = Vec::new();
        let mut concrete_nodes: Vec<NodeMeta> = Vec::new();
        let mut middle_nodes: Vec<NodeMeta> = Vec::new();

        let mut abstract_path_slots: Vec<usize> = Vec::new();
        let mut concrete_path_slots: Vec<usize> = Vec::new();

        for (step_idx, (state, _)) in steps.iter().enumerate() {
            // Concrete (deduped by fingerprint)
            let concrete_fp = fingerprint(&state.concrete_state).get();
            let concrete_slot = *concrete_slots.entry(concrete_fp).or_insert_with(|| {
                let slot = concrete_nodes.len();
                concrete_nodes.push(NodeMeta {
                    label: format!("C{slot}"),
                    title: build_title(
                        "Concrete",
                        slot,
                        concrete_fp,
                        format!("{:#?}", state.concrete_state),
                    ),
                });
                slot
            });
            concrete_path_slots.push(concrete_slot);

            // Concrete + Aux (per step, no dedup)
            let combo_fp =
                fingerprint(&(state.concrete_state.clone(), state.aux_state.clone())).get();
            middle_nodes.push(NodeMeta {
                label: format!("CA{step_idx}"),
                title: build_title(
                    "Concrete+Aux",
                    step_idx,
                    combo_fp,
                    format!(
                        "Concrete: {:#?}\nAux: {:#?}",
                        state.concrete_state, state.aux_state
                    ),
                ),
            });

            // Abstract (deduped by Observable equivalence via linear scan)
            let obs = self.mapper.observe(&state.mapped_abstract_state);
            let abstract_slot = match abstract_nodes
                .iter()
                .position(|(existing_obs, _)| *existing_obs == obs)
            {
                Some(slot) => slot,
                None => {
                    let slot = abstract_nodes.len();
                    let abs_fp = fingerprint(&state.mapped_abstract_state).get();
                    let title = build_title(
                        "Abstract",
                        slot,
                        abs_fp,
                        format!(
                            "Observable: {:#?}\n\nMapped abstract state: {:#?}",
                            obs, state.mapped_abstract_state
                        ),
                    );
                    abstract_nodes.push((
                        obs.clone(),
                        NodeMeta {
                            label: format!("A{slot}"),
                            title,
                        },
                    ));
                    slot
                }
            };
            abstract_path_slots.push(abstract_slot);
        }

        let last_state = &steps.last().unwrap().0;
        let last_is_valid = Self::check_simulation(self, last_state);

        let horizontal_gap = 150usize;
        let vertical_gap = 120usize;
        let left_padding = 140usize;
        let right_padding = 120usize;
        let top_padding = 80usize;
        let radius = 22usize;

        let span = std::cmp::max(
            std::cmp::max(
                abstract_nodes.len().saturating_sub(1),
                concrete_nodes.len().saturating_sub(1),
            ),
            middle_nodes.len().saturating_sub(1),
        );
        let width = left_padding + right_padding + horizontal_gap.saturating_mul(span);
        let height = top_padding * 3 + vertical_gap * 2;
        let abstract_y = top_padding;
        let middle_y = abstract_y + vertical_gap;
        let concrete_y = middle_y + vertical_gap;

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
            "<text class='svg-ref-label' x='20' y='{abstract_y}'>Abstract</text>\
           <text class='svg-ref-label' x='12' y='{middle_y}'>Concrete+Aux</text>\
           <text class='svg-ref-label' x='20' y='{concrete_y}'>Concrete</text>"
        );

        // Concrete transitions (deduped path)
        for i in 1..concrete_path_slots.len() {
            let x1 = left_padding + concrete_path_slots[i - 1] * horizontal_gap;
            let x2 = left_padding + concrete_path_slots[i] * horizontal_gap;
            let _ = write!(
                &mut svg,
                "<line x1='{x1}' y1='{concrete_y}' x2='{x2}' y2='{concrete_y}' \
                 class='svg-ref-edge' marker-end='url(#refinement-arrow)'/>",
            );
        }

        // Middle transitions (per step)
        for step_idx in 1..middle_nodes.len() {
            let x1 = left_padding + (step_idx - 1) * horizontal_gap;
            let x2 = left_padding + step_idx * horizontal_gap;
            let _ = write!(
                &mut svg,
                "<line x1='{x1}' y1='{middle_y}' x2='{x2}' y2='{middle_y}' \
                 class='svg-ref-edge' marker-end='url(#refinement-arrow)'/>",
            );
        }

        // Abstract transitions (deduped path, last edge dashed if invalid)
        for i in 1..abstract_path_slots.len() {
            let x1 = left_padding + abstract_path_slots[i - 1] * horizontal_gap;
            let x2 = left_padding + abstract_path_slots[i] * horizontal_gap;
            let mut class = "svg-ref-edge";
            let mut cross = None;
            if i == abstract_path_slots.len() - 1 && !last_is_valid {
                class = "svg-ref-edge svg-ref-edge-invalid";
                let mid_x = (x1 + x2) / 2;
                let size = 10;
                cross = Some((
                    mid_x - size,
                    mid_x + size,
                    abstract_y - size,
                    abstract_y + size,
                ));
            }
            let _ = write!(
                &mut svg,
                "<line x1='{x1}' y1='{abstract_y}' x2='{x2}' y2='{abstract_y}' \
                 class='{class}' marker-end='url(#refinement-arrow)'/>",
            );
            if let Some((mx1, mx2, my1, my2)) = cross {
                let _ = write!(
                  &mut svg,
                  "<line x1='{mx1}' y1='{my1}' x2='{mx2}' y2='{my2}' class='svg-ref-invalid-cross'/>\
                   <line x1='{mx1}' y1='{my2}' x2='{mx2}' y2='{my1}' class='svg-ref-invalid-cross'/>",
              );
            }
        }

        // Concrete -> middle mappings (per step)
        for (step_idx, &slot_idx) in concrete_path_slots.iter().enumerate() {
            let concrete_x = left_padding + slot_idx * horizontal_gap;
            let middle_x = left_padding + step_idx * horizontal_gap;
            let _ = write!(
              &mut svg,
              "<line x1='{concrete_x}' y1='{concrete_y_minus}' x2='{middle_x}' y2='{middle_y_plus}' \
                 class='svg-ref-mapping-line'/>",
              concrete_y_minus = concrete_y - radius,
              middle_y_plus = middle_y + radius,
          );
        }

        // Middle -> abstract mappings (per step)
        for (step_idx, &slot_idx) in abstract_path_slots.iter().enumerate() {
            let middle_x = left_padding + step_idx * horizontal_gap;
            let abstract_x = left_padding + slot_idx * horizontal_gap;
            let _ = write!(
              &mut svg,
              "<line x1='{middle_x}' y1='{middle_y_minus}' x2='{abstract_x}' y2='{abstract_y_plus}' \
                 class='svg-ref-mapping-line'/>",
              middle_y_minus = middle_y - radius,
              abstract_y_plus = abstract_y + radius,
          );
        }

        // Abstract nodes
        for (slot_idx, (_, node)) in abstract_nodes.iter().enumerate() {
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

        // Middle nodes
        for (step_idx, node) in middle_nodes.iter().enumerate() {
            let x = left_padding + step_idx * horizontal_gap;
            let _ = write!(
                &mut svg,
                "<g class='svg-ref-node'>\
                 <circle class='svg-ref-state-circle' cx='{x}' cy='{middle_y}' r='{radius}'>\
                   <title>{title}</title>\
                 </circle>\
                 <text class='svg-ref-state-text' x='{x}' y='{middle_y}'>{label}</text>\
               </g>",
                title = Self::escape_html(&node.title),
                label = Self::escape_html(&node.label),
            );
        }

        // Concrete nodes
        for (slot_idx, node) in concrete_nodes.iter().enumerate() {
            let x = left_padding + slot_idx * horizontal_gap;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Checker;

    // ------------------------------------------------------------
    // Toy concrete/abstract pair used by all tests below.
    //
    // Abstract: a monotonic counter plus an internal `ticks` field that
    // increments on every step. `ticks` is "bookkeeping" — depending on
    // the mapper's choice of Observable it may or may not be part of the
    // refinement contract.
    //
    // Concrete: the same counter without `ticks` (the concrete doesn't
    // track it). A mapper has to decide how to populate `ticks` in the
    // mapped abstract state.
    // ------------------------------------------------------------

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct AbsState {
        counter: u32,
        ticks: u32,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct AbsAction;

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct AbsModel {
        max_counter: u32,
    }

    impl Model for AbsModel {
        type State = AbsState;
        type Action = AbsAction;

        fn init_states(&self) -> Vec<Self::State> {
            vec![AbsState {
                counter: 0,
                ticks: 0,
            }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            if state.counter < self.max_counter {
                actions.push(AbsAction);
            }
        }

        fn next_state(&self, last: &Self::State, _: Self::Action) -> Option<Self::State> {
            Some(AbsState {
                counter: last.counter + 1,
                ticks: last.ticks + 1,
            })
        }
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct ConState {
        counter: u32,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct ConAction;

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct ConModel {
        max_counter: u32,
    }

    impl Model for ConModel {
        type State = ConState;
        type Action = ConAction;

        fn init_states(&self) -> Vec<Self::State> {
            vec![ConState { counter: 0 }]
        }

        fn actions(&self, state: &Self::State, actions: &mut Vec<Self::Action>) {
            if state.counter < self.max_counter {
                actions.push(ConAction);
            }
        }

        fn next_state(&self, last: &Self::State, _: Self::Action) -> Option<Self::State> {
            Some(ConState {
                counter: last.counter + 1,
            })
        }
    }

    // --- Test 1: strict simulation (Observable = AbsState). The mapper
    // sets `ticks = 0` always, which does NOT match the abstract's
    // progression. Under the strict Observable this is visible and the
    // check must fail. ---

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct StrictGarbageMapper {
        abstract_model: AbsModel,
    }

    impl RefinementMapping<ConModel, AbsModel> for StrictGarbageMapper {
        type AuxState = ();
        type Observable = AbsState;

        fn abstract_model(&self) -> &AbsModel {
            &self.abstract_model
        }

        fn init_aux_state(&self, _: &ConState) {}
        fn advance_aux_state(&self, _: &ConState, _: &(), _: &ConAction, _: &ConState) {}

        fn refinement_map(&self, c: &ConState, _: &()) -> AbsState {
            AbsState {
                counter: c.counter,
                ticks: 0, // garbage
            }
        }

        fn observe(&self, a: &AbsState) -> AbsState {
            a.clone()
        }
    }

    #[test]
    fn strict_observable_fails_when_bookkeeping_diverges() {
        let concrete = ConModel { max_counter: 3 };
        let abstract_ = AbsModel { max_counter: 3 };
        let mapper = StrictGarbageMapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        let checker = model.checker().spawn_bfs().join();
        assert!(
            checker.discovery("check_simulation").is_some(),
            "strict Observable should fail when refinement_map produces garbage ticks"
        );
    }

    // --- Test 2: weak simulation — Observable hides `ticks`. Same broken
    // mapper logic as test 1, now the check passes because bookkeeping is
    // invisible. ---

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct CounterObs {
        counter: u32,
    }

    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct WeakTicksMapper {
        abstract_model: AbsModel,
    }

    impl RefinementMapping<ConModel, AbsModel> for WeakTicksMapper {
        type AuxState = ();
        type Observable = CounterObs;

        fn abstract_model(&self) -> &AbsModel {
            &self.abstract_model
        }

        fn init_aux_state(&self, _: &ConState) {}
        fn advance_aux_state(&self, _: &ConState, _: &(), _: &ConAction, _: &ConState) {}

        fn refinement_map(&self, c: &ConState, _: &()) -> AbsState {
            AbsState {
                counter: c.counter,
                ticks: 0, // still garbage — but ignored by `observe`
            }
        }

        fn observe(&self, a: &AbsState) -> CounterObs {
            CounterObs { counter: a.counter }
        }
    }

    #[test]
    fn weak_observable_passes_when_bookkeeping_hidden() {
        let concrete = ConModel { max_counter: 3 };
        let abstract_ = AbsModel { max_counter: 3 };
        let mapper = WeakTicksMapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        let checker = model.checker().spawn_bfs().join();
        assert!(
            checker.discovery("check_simulation").is_none(),
            "Observable projecting away `ticks` should accept the mapping"
        );
    }

    // --- Test 3: L-simulation match via `observe` across a longer trace.
    // Every concrete step must find an abstract transition whose next
    // state's observation matches — exercising the `any` search, not
    // just stutters. ---

    #[test]
    fn weak_observable_matches_abstract_transitions() {
        let concrete = ConModel { max_counter: 8 };
        let abstract_ = AbsModel { max_counter: 8 };
        let mapper = WeakTicksMapper {
            abstract_model: abstract_,
        };
        let model = RefinementModel::new(concrete, mapper);
        let checker = model.checker().spawn_bfs().join();
        assert!(
            checker.discovery("check_simulation").is_none(),
            "L-simulation should match via observe across the full trace"
        );
        assert!(checker.state_count() >= 8);
    }
}
