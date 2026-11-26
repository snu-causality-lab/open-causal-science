module
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # Finite counterfactual unnesting

Correa, Lee and Bareinboim (2021), Theorem 4, equation (21).
For each unit, evaluate the settings of the natural intervention
and partition the nested event by that assignment.
Source: https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=8
-/

namespace OpenCausalScience.Papers.CorreaLeeBareinboim2021.Unnesting

open TianPearl2003.AncestralMarginal (Setting evaluate mass sum_masses_of_partition)

@[expose] public section

variable {Ω : Type} {Assignment : Type} [DecidableEq Assignment]

/-- Every cell uses the same unit for the natural assignment and the
response under the corresponding fixed assignment. -/
theorem sum_joint_cells_eq_nested_mass
    (atoms : List Ω) (weight : Ω → Rat) (assignments : List Assignment)
    (nodup : assignments.Nodup) (natural : Ω → Assignment)
    (exhaustive : ∀ unit ∈ atoms, natural unit ∈ assignments)
    (responseEvent : Ω → Assignment → Bool) :
    (assignments.map fun assignment =>
      mass atoms weight (fun unit => responseEvent unit assignment &&
        decide (natural unit = assignment))).sum =
    mass atoms weight (fun unit => responseEvent unit (natural unit)) := by
  rw [← sum_masses_of_partition assignments nodup atoms weight natural exhaustive
    (fun unit => responseEvent unit (natural unit))]
  congr 1
  apply List.map_congr_left
  intro assignment _
  congr 1
  funext unit
  by_cases equal : natural unit = assignment
  · simp [equal]
  · simp [equal]

/-- Source-law equivalence for exact identification. The weights can
encode finite rational models with differing exogenous supports. -/
def IdentifiedBy {Model Sources : Type} (data : Model → Sources)
    (estimand : Model → Rat) : Prop :=
  ∀ first second, data first = data second → estimand first = estimand second

/-- Identification of every summand is sufficient for identification of
the nested queried cell under the same collection of source laws. -/
theorem identified_nested_of_identified_joint_cells
    {Model Sources : Type} (data : Model → Sources) (atoms : Model → List Ω)
    (weight : Model → Ω → Rat) (assignments : List Assignment) (nodup : assignments.Nodup)
    (natural : Model → Ω → Assignment)
    (exhaustive : ∀ m unit, unit ∈ atoms m → natural m unit ∈ assignments)
    (responseEvent : Model → Ω → Assignment → Bool)
    (identified : ∀ a ∈ assignments, IdentifiedBy data (fun m =>
      mass (atoms m) (weight m) (fun unit => responseEvent m unit a &&
        decide (natural m unit = a)))) :
    IdentifiedBy data (fun m => mass (atoms m) (weight m)
      (fun unit => responseEvent m unit (natural m unit))) := by
  intro first second sameData
  dsimp only
  rw [← sum_joint_cells_eq_nested_mass (atoms first) (weight first) assignments nodup
        (natural first) (exhaustive first) (responseEvent first),
      ← sum_joint_cells_eq_nested_mass (atoms second) (weight second) assignments nodup
        (natural second) (exhaustive second) (responseEvent second)]
  congr 1
  apply List.map_congr_left
  intro assignment present
  exact identified assignment present first second sameData

/-- Compose the inherited per-unit settings with one candidate
assignment of the coordinates being unnested. -/
def applyAssignment {n : Nat} (coordinates : Fin n → Bool) (assignment : Fin n → Bool)
    (inherited : Setting n) : Setting n :=
  fun v => if coordinates v then some (assignment v) else inherited v

/-- Equation (21) for a finite ranked binary SCM. The listed assignments
must cover the natural choices on the supplied units exactly once.
The natural values may themselves come from other intervention worlds. -/
theorem ranked_scm_unnesting {n : Nat} (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool)
    (atoms : List Ω) (weight : Ω → Rat) (coordinates : Fin n → Bool)
    (inherited : Ω → Setting n) (assignments : List Assignment)
    (nodup : assignments.Nodup) (values : Assignment → Fin n → Bool) (natural : Ω → Assignment)
    (exhaustive : ∀ unit ∈ atoms, natural unit ∈ assignments)
    (event : (Fin n → Bool) → Bool) :
    (assignments.map fun a => mass atoms weight (fun unit =>
      event (evaluate G mechanism unit (applyAssignment coordinates (values a) (inherited unit))) &&
        decide (natural unit = a))).sum =
    mass atoms weight (fun unit => event
      (evaluate G mechanism unit (applyAssignment coordinates (values (natural unit)) (inherited unit)))) :=
  sum_joint_cells_eq_nested_mass atoms weight assignments nodup natural exhaustive
    (fun unit a => event (evaluate G mechanism unit (applyAssignment coordinates (values a) (inherited unit))))

end

end OpenCausalScience.Papers.CorreaLeeBareinboim2021.Unnesting
