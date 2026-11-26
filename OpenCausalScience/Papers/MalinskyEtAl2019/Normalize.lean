module
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # The last step of PS-IDC

Malinsky, Shpitser and Richardson (2019), Algorithm 1, line 2.
If the reduced joint is represented by identified cells, summing its
cells over the outcome gives the remaining evidence mass.
Source: https://proceedings.mlr.press/v89/malinsky19b/malinsky19b.pdf#page=8
-/

namespace OpenCausalScience.Papers.MalinskyEtAl2019.Normalize

open TianPearl2003.AncestralMarginal (mass sum_masses_of_partition)

@[expose] public section

variable {Ω Y : Type} [DecidableEq Y]

/-- The denominator equals the mass of the remaining evidence. -/
theorem reduced_joint_sum_eq_evidence (atoms : List Ω) (weight : Ω → Rat)
    (response : Ω → Y) (evidence : Ω → Bool) (values : List Y) (unique : values.Nodup)
    (exhaustive : ∀ u ∈ atoms, response u ∈ values) (joint : Y → Rat)
    (identified : ∀ y, joint y = mass atoms weight (fun u => evidence u && decide (response u = y))) :
    (values.map joint).sum = mass atoms weight evidence := by
  rw [funext identified]
  exact sum_masses_of_partition values unique atoms weight response exhaustive evidence

/-- Normalization recovers the path-specific conditional on its support. -/
theorem normalize_reduced_joint (atoms : List Ω) (weight : Ω → Rat)
    (response : Ω → Y) (evidence : Ω → Bool) (values : List Y) (unique : values.Nodup)
    (exhaustive : ∀ u ∈ atoms, response u ∈ values) (joint : Y → Rat)
    (identified : ∀ y, joint y = mass atoms weight (fun u => evidence u && decide (response u = y)))
    (supported : 0 < mass atoms weight evidence) (y : Y) :
    0 < (values.map joint).sum ∧ joint y / (values.map joint).sum =
      mass atoms weight (fun u => evidence u && decide (response u = y)) / mass atoms weight evidence := by
  rw [reduced_joint_sum_eq_evidence atoms weight response evidence values unique exhaustive joint identified,
    identified y]
  exact ⟨supported, rfl⟩

end
end OpenCausalScience.Papers.MalinskyEtAl2019.Normalize
