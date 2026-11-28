module
public import OpenCausalScience.Probability.ConditionalIndependence

/-! Finite unions of error events on finite rational sampling laws. -/

namespace OpenCausalScience.Probability

@[expose] public section

private theorem mass_or_le {Ω : Type} (law : FiniteLaw Ω) (f g : Ω → Bool) :
    law.mass (fun a => f a || g a) ≤ law.mass f + law.mass g := by
  have nonnegative := law.nonnegative
  unfold FiniteLaw.mass FiniteMass.mass
  generalize members : law.atoms = atoms at nonnegative ⊢
  clear members
  induction atoms with
  | nil => simp [Rat.zero_add]
  | cons a rest ih =>
    have head := nonnegative a List.mem_cons_self
    have tail := ih (fun x present => nonnegative x (List.mem_cons_of_mem _ present))
    simp only [List.map_cons, List.sum_cons]
    by_cases hf : f a = true
    · by_cases hg : g a = true
      · simp [hf, hg]
        grind
      · simp [hf, Bool.eq_false_iff.mpr hg]
        grind
    · by_cases hg : g a = true
      · simp [Bool.eq_false_iff.mpr hf, hg]
        grind
      · simpa [Bool.eq_false_iff.mpr hf, Bool.eq_false_iff.mpr hg, Rat.zero_add] using tail

theorem rat_lt_of_le_of_lt {a b c : Rat} (ab : a ≤ b) (bc : b < c) : a < c := by
  apply Classical.byContradiction
  intro notBefore
  exact Rat.not_lt.mpr (Rat.le_trans (Rat.not_lt.mp notBefore) ab) bc

/-- A finite union of error events whose probabilities tend to zero has
vanishing error probability. The sample space may vary with sample size. -/
theorem finite_library_error_vanishes {ι : Type} {Ω : Nat → Type}
    (law : ∀ m, FiniteLaw (Ω m)) (failed : ∀ m, ι → Ω m → Bool) (queries : List ι)
    (each : ∀ q ∈ queries, ∀ ε : Rat, 0 < ε →
      ∃ N, ∀ m, N ≤ m → (law m).mass (failed m q) < ε) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => queries.any fun q => failed m q a) < ε := by
  induction queries with
  | nil =>
    intro ε positive
    refine ⟨0, fun m _ => ?_⟩
    have massZero : (law m).mass (fun _ => false) = 0 := by
      unfold FiniteLaw.mass FiniteMass.mass
      have zeros (xs : List (Ω m)) : (xs.map (fun _ => (0 : Rat))).sum = 0 := by
        induction xs <;> simp_all [Rat.zero_add]
      simpa using zeros (law m).atoms
    simpa only [List.any_nil, massZero] using positive
  | cons q rest ih =>
    intro ε positive
    let δ := ε * (1 / 2 : Rat)
    have δpos : 0 < δ := Rat.mul_pos positive (by decide +kernel)
    have δsum : δ + δ = ε := by
      change ε * (1 / 2) + ε * (1 / 2) = ε
      rw [← Rat.mul_add]
      have halves : (1 / 2 : Rat) + 1 / 2 = 1 := by decide +kernel
      rw [halves, Rat.mul_one]
    obtain ⟨a, head⟩ := each q List.mem_cons_self δ δpos
    obtain ⟨b, tail⟩ := ih (fun v present => each v (List.mem_cons_of_mem _ present)) δ δpos
    refine ⟨max a b, fun m later => ?_⟩
    have hHead := head m (Nat.le_trans (Nat.le_max_left _ _) later)
    have hTail := tail m (Nat.le_trans (Nat.le_max_right _ _) later)
    have both : (law m).mass (failed m q) + (law m).mass (fun x => rest.any fun v => failed m v x) < ε := by
      rw [← δsum]
      exact rat_lt_of_le_of_lt (Rat.le_of_lt (Rat.add_lt_add_right.mpr hHead)) (Rat.add_lt_add_left.mpr hTail)
    simp only [List.any_cons]
    exact rat_lt_of_le_of_lt (mass_or_le (law m) _ _) both

end

end OpenCausalScience.Probability
