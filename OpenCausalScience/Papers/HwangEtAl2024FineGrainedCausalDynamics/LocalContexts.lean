module
public import Std

/-!
# Hwang et al. (2024), supported contexts and fixed variables

Definitions 4–5 and 9 and Lemmas 4–5 of the October 2026 correction.
For a discrete transition law, a set of coordinates is sufficient when
assignments agreeing on those coordinates have identical output laws on the
supported part of the context. The results concern one next-state
coordinate. Applying them coordinatewise gives the corresponding graph
statements.
-/

namespace OpenCausalScience.Papers.HwangEtAl2024FineGrainedCausalDynamics.LocalContexts

@[expose] public section

variable {Index Value Law : Type}

/-- A sufficient input set determines the conditional law on the supported
part of the context. The context argument includes its positive-weight
restriction. -/
def sufficient (kernel : (Index → Value) → Law) (context : (Index → Value) → Prop)
    (inputs : Index → Prop) : Prop :=
  ∀ x x', context x → context x' →
    (∀ i, inputs i → x i = x' i) → kernel x = kernel x'

/-- Every sufficient input set stays sufficient when restricting to a
positive-probability subcontext. -/
theorem sufficient_of_subcontext {kernel : (Index → Value) → Law}
    {outer inner : (Index → Value) → Prop} {inputs : Index → Prop}
    (subcontext : ∀ x, inner x → outer x)
    (h : sufficient kernel outer inputs) :
    sufficient kernel inner inputs :=
  fun x x' hx hx' agree => h x x' (subcontext x hx) (subcontext x' hx') agree

/-- Under local faithfulness on the subcontext, its local parent set is a
subset of each sufficient input set on the larger context. -/
theorem local_parents_of_subcontext {kernel : (Index → Value) → Law}
    {outer inner : (Index → Value) → Prop} {outerParents innerParents : Index → Prop}
    (subcontext : ∀ x, inner x → outer x)
    (outerSufficient : sufficient kernel outer outerParents)
    (innerFaithful : ∀ inputs, sufficient kernel inner inputs →
      ∀ i, innerParents i → inputs i) :
    ∀ i, innerParents i → outerParents i :=
  innerFaithful outerParents (sufficient_of_subcontext subcontext outerSufficient)

/-- Removing a coordinate fixed throughout the supported context preserves
sufficiency, so it cannot be a member of an inclusion-minimal parent set. -/
theorem remove_fixed_input {kernel : (Index → Value) → Law}
    {context : (Index → Value) → Prop} {inputs : Index → Prop}
    (coordinate : Index) (value : Value)
    (fixed : ∀ x, context x → x coordinate = value)
    (h : sufficient kernel context inputs) :
    sufficient kernel context (fun i => inputs i ∧ i ≠ coordinate) := by
  classical
  intro x x' hx hx' agree
  apply h x x' hx hx'
  intro i hi
  by_cases equal : i = coordinate
  · subst i
    exact (fixed x hx).trans (fixed x' hx').symm
  · exact agree i ⟨hi, equal⟩

/-- In a discrete context, a positive atom supplies a positive singleton
subcontext. If the same parent set is required to satisfy local faithfulness
there, it is empty. This is the obstruction to a nonempty canonical LCG in
the discrete case. -/
theorem canonical_context_with_positive_atom_has_no_parents
    (kernel : (Index → Value) → Law) (weight : (Index → Value) → Rat)
    (context : (Index → Value) → Prop) (parents : Index → Prop)
    (atom : Index → Value) (included : context atom) (mass : 0 < weight atom)
    (canonical : ∀ inner : (Index → Value) → Prop,
      (∀ x, inner x → context x) →
      (∃ x, inner x ∧ 0 < weight x) →
      ∀ inputs, sufficient kernel (fun x => inner x ∧ 0 < weight x) inputs →
        ∀ i, parents i → inputs i) :
    ∀ i, ¬ parents i := by
  have singletonSufficient :
      sufficient kernel (fun x => x = atom ∧ 0 < weight x) (fun _ => False) := by
    rintro x x' ⟨rfl, _⟩ ⟨rfl, _⟩ _
    rfl
  exact canonical (fun x => x = atom) (fun _ h => h.symm ▸ included)
    ⟨atom, rfl, mass⟩ (fun _ => False) singletonSufficient

end

end OpenCausalScience.Papers.HwangEtAl2024FineGrainedCausalDynamics.LocalContexts
