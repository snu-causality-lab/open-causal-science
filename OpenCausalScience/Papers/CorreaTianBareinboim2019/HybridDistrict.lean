module
public import OpenCausalScience.Graph.MixedSeparationExecutable
public import OpenCausalScience.Papers.CorreaTianBareinboim2019.PopulationMargin

/-! # The two sources in R-38's district formula

Correa, Tian and Bareinboim (AAAI 2019), Theorem 3 and equation (6).
Inside the ancestors of the selection district a vertex uses the
recovered population prefix. Outside those ancestors it uses the
selected prefix. The closed child set in the eligibility test
includes the unavailable vertices themselves.

Source: https://causalai.net/r38.pdf#page=4
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2019.HybridDistrict

open PopulationMargin (divide_mul_of_cross)

@[expose] public section

variable {n : Nat}

/-- Extend a supplied population margin by vertices separated from
selection given the population variables. Supply the induced current
graph as G. -/
def extendedPopulation (G : MixedGraph n) (active base : Fin n → Bool)
    (selection v : Fin n) : Bool :=
  active v && (v != selection) &&
    (base v || G.mSeparated (· == v) (· == selection) base)

theorem mem_extended_population_iff (G : MixedGraph n) (active base : Fin n → Bool)
    (selection v : Fin n) :
    extendedPopulation G active base selection v = true ↔
      active v = true ∧ v ≠ selection ∧
        (base v = true ∨ ¬ G.WalkConnected (· == v) (· == selection) base) := by
  simp [extendedPopulation, Bool.and_eq_true, Bool.or_eq_true, and_assoc,
    MixedGraph.m_separated_iff_no_walk]

/-- Closed child membership in the current graph. -/
def childOfUnavailable (G : MixedGraph n) (active available : Fin n → Bool) (v : Fin n) : Bool :=
  !available v || (List.finRange n).any fun u =>
    active u && !available u && G.edge u false v true

def eligible (G : MixedGraph n) (active ancestors available : Fin n → Bool)
    (district : List (Fin n)) : Bool :=
  district.all fun v => !(ancestors v && childOfUnavailable G active available v)

theorem eligible_iff_available (G : MixedGraph n) (active ancestors available : Fin n → Bool)
    (district : List (Fin n)) :
    eligible G active ancestors available district = true ↔
      ∀ v ∈ district, ancestors v = true →
        available v = true ∧
          ∀ u, active u = true → G.edge u false v true = true → available u = true := by
  simp only [eligible, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    childOfUnavailable, Bool.or_eq_false_iff, List.any_eq_false, List.mem_finRange,
    true_implies, Bool.not_eq_false', Bool.and_eq_false_iff]
  constructor
  · intro safe v here ancestor
    rcases safe v here with outside | ⟨ready, parents⟩
    · simp [ancestor] at outside
    · refine ⟨ready, fun u activeU edge => ?_⟩
      cases value : available u
      · exact (parents u (by simp [activeU, value, edge])).elim
      · rfl
  · intro covered v here
    cases ancestor : ancestors v
    · exact .inl rfl
    · obtain ⟨ready, parents⟩ := covered v here ancestor
      refine .inr ⟨ready, fun u => ?_⟩
      cases activeU : active u
      · simp
      · cases edge : G.edge u false v true
        · simp
        · simp [parents u activeU edge]

/-- One ratio in the two products in equation (6). Each prefix is
indexed at the corresponding position of the common vertex order. -/
structure PrefixCell where
  withCurrent : Rat
  withoutCurrent : Rat

def PrefixCell.ratio (cell : PrefixCell) : Rat :=
  cell.withCurrent / cell.withoutCurrent

def factor {V : Type} (district : List V) (ancestors : V → Bool)
    (population selected : V → PrefixCell) : Rat :=
  (district.map fun v => if ancestors v then (population v).ratio else (selected v).ratio).prod

theorem ratio_eq_of_cross (cell : PrefixCell) (value : Rat)
    (supported : cell.withoutCurrent ≠ 0)
    (cross : cell.withCurrent = value * cell.withoutCurrent) :
    cell.ratio = value := by
  simpa only [PrefixCell.ratio, Rat.mul_one] using
    (divide_mul_of_cross (c := 1) supported (by simpa only [Rat.mul_one] using cross))

/-- The hybrid formula composes the two local prefix identities.
They are the probability premises of the check. -/
theorem hybrid_factor_eq {V : Type} (district : List V) (ancestors : V → Bool)
    (population selected : V → PrefixCell) (truth : V → Rat)
    (populationCells : ∀ v ∈ district, ancestors v = true →
      (population v).withoutCurrent ≠ 0 ∧
        (population v).withCurrent = truth v * (population v).withoutCurrent)
    (selectedCells : ∀ v ∈ district, ancestors v = false →
      (selected v).withoutCurrent ≠ 0 ∧
        (selected v).withCurrent = truth v * (selected v).withoutCurrent) :
    factor district ancestors population selected = (district.map truth).prod := by
  unfold factor
  congr 1
  apply List.map_congr_left
  intro v member
  cases before : ancestors v
  · obtain ⟨supported, cross⟩ := selectedCells v member before
    simpa only [before, Bool.false_eq_true, ↓reduceIte] using
      ratio_eq_of_cross (selected v) (truth v) supported cross
  · obtain ⟨supported, cross⟩ := populationCells v member before
    simpa only [before, ↓reduceIte] using ratio_eq_of_cross (population v) (truth v) supported cross

end
end OpenCausalScience.Papers.CorreaTianBareinboim2019.HybridDistrict
