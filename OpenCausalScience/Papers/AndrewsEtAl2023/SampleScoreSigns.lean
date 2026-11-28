module
public import OpenCausalScience.Papers.AndrewsEtAl2023.PopulationProjection
public import OpenCausalScience.Discovery.FiniteCIQueries
public import OpenCausalScience.Probability.FiniteErrors

/-! # Finite sampling conditions for grow–shrink scores

The statistical premise is the convergence of each fixed comparison's
error probability. A finite library gives the simultaneous guarantee
needed to apply the population proof to a data-dependent order. -/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.SampleScoreSigns

open OpenCausalScience.Probability OpenCausalScience.Probability.CI
open OpenCausalScience.Discovery.FiniteCIQueries
open GrowShrinkTree PopulationProjection

@[expose] public section

variable {n : Nat}

/-- The conditions and signs for comparing a parent set with one addition. -/
def CorrectSign (J : Relation n) (scores : Fin n → LocalScore n) (q : Comparison n) : Prop :=
  let (child, parent, P) := q
  let canonical := (List.finRange n).filter P
  parent ≠ child → P child = false → P parent = false →
    (J (single child) (single parent) P → scores child (parent :: canonical) < scores child canonical) ∧
    (¬ J (single child) (single parent) P → scores child canonical < scores child (parent :: canonical))

/-- Equal parent sets receive equal scores, irrespective of their list representation. -/
def SetScores (scores : Fin n → LocalScore n) : Prop :=
  ∀ (child : Fin n) (P Q : List (Fin n)), maskOfList P = maskOfList Q → scores child P = scores child Q

theorem locally_consistent_of_signs {J : Relation n} {scores : Fin n → LocalScore n}
    (setScores : SetScores scores) (signs : ∀ q ∈ comparisons n, CorrectSign J scores q) :
    ∀ child, LocallyConsistent J child (scores child) := by
  intro child
  have one (parent : Fin n) (P : List (Fin n)) (different : parent ≠ child)
      (parentOutside : parent ∉ P) (childOutside : child ∉ P) :
      (J (single child) (single parent) (maskOfList P) → scores child (parent :: P) < scores child P) ∧
      (¬ J (single child) (single parent) (maskOfList P) → scores child P < scores child (parent :: P)) := by
    let canonical := (List.finRange n).filter (maskOfList P)
    have before : maskOfList P = maskOfList canonical := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simp [maskOfList, canonical]
    have after : maskOfList (parent :: P) = maskOfList (parent :: canonical) := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simp [maskOfList, canonical]
    rw [setScores child _ _ before, setScores child _ _ after]
    exact signs (child, parent, maskOfList P) (mem_comparisons _ _ _) different
      (by simp [maskOfList, childOutside]) (by simp [maskOfList, parentOutside])
  exact ⟨fun {P Q} same => setScores child P Q same,
    fun {parent P} different parentOutside childOutside => (one parent P different parentOutside childOutside).2,
    fun {parent P} different parentOutside childOutside => (one parent P different parentOutside childOutside).1⟩

private theorem eventual_on_list {ι : Type} (xs : List ι) (P : ι → Nat → Prop)
    (eventually : ∀ i ∈ xs, ∃ N, ∀ m, N ≤ m → P i m) :
    ∃ N, ∀ m, N ≤ m → ∀ i ∈ xs, P i m := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons i tail ih =>
    obtain ⟨a, atHead⟩ := eventually i List.mem_cons_self
    obtain ⟨b, atTail⟩ := ih (fun q h => eventually q (List.mem_cons_of_mem _ h))
    refine ⟨max a b, fun m later q h => ?_⟩
    rcases List.mem_cons.mp h with rfl | member
    · exact atHead m (Nat.le_trans (Nat.le_max_left _ _) later)
    · exact atTail m (Nat.le_trans (Nat.le_max_right _ _) later) q member

/-- Pointwise eventual local signs imply a single threshold for all
legitimate additions, including data-dependent choices of a parent set. -/
theorem eventually_locally_consistent {J : Relation n} (scores : Nat → Fin n → LocalScore n)
    (setScores : ∀ m, SetScores (scores m))
    (each : ∀ q ∈ comparisons n, ∃ N, ∀ m, N ≤ m → CorrectSign J (scores m) q) :
    ∃ N, ∀ m, N ≤ m → ∀ child, LocallyConsistent J child (scores m child) := by
  obtain ⟨N, all⟩ := eventual_on_list (comparisons n) (fun q m => CorrectSign J (scores m) q) each
  exact ⟨N, fun m later => locally_consistent_of_signs (setScores m) (all m later)⟩

noncomputable def comparisonError (J : Relation n) (scores : Fin n → LocalScore n)
    (q : Comparison n) : Bool := by
  classical
  exact decide (¬ CorrectSign J scores q)

noncomputable def signLibraryError (J : Relation n) (scores : Fin n → LocalScore n) : Bool :=
  (comparisons n).any (comparisonError J scores)

theorem locally_consistent_of_no_library_error {J : Relation n} {scores : Fin n → LocalScore n}
    (setScores : SetScores scores) (good : signLibraryError J scores = false) :
    ∀ child, LocallyConsistent J child (scores child) := by
  classical
  apply locally_consistent_of_signs setScores
  intro q present
  apply Classical.byContradiction
  intro fails
  have bad : signLibraryError J scores = true := List.any_eq_true.mpr
    ⟨q, present, by simp [comparisonError, fails]⟩
  simp [good] at bad

/-- Pointwise sign consistency in probability controls the error of any
procedure that succeeds when the finite library of local signs is correct. -/
theorem sample_failure_vanishes_of_fixed_signs {J : Relation n} {Ω : Nat → Type}
    (law : ∀ m, FiniteLaw (Ω m)) (scores : ∀ m, Ω m → Fin n → LocalScore n)
    (failed : ∀ m, Ω m → Bool) (setScores : ∀ m a, SetScores (scores m a))
    (sound : ∀ m a, (∀ child, LocallyConsistent J child (scores m a child)) → failed m a = false)
    (each : ∀ q ∈ comparisons n, ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => comparisonError J (scores m a) q) < ε) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m → (law m).mass (failed m) < ε := by
  intro ε positive
  obtain ⟨N, all⟩ := finite_library_error_vanishes law
    (fun m q a => comparisonError J (scores m a) q) (comparisons n) each ε positive
  refine ⟨N, fun m later => ?_⟩
  apply rat_lt_of_le_of_lt _ (all m later)
  apply FiniteLaw.mass_mono
  intro a _ failure
  cases good : signLibraryError J (scores m a) with
  | true => exact good
  | false =>
    rw [sound m a (locally_consistent_of_no_library_error (setScores m a) good)] at failure
    contradiction

end

end OpenCausalScience.Papers.AndrewsEtAl2023.SampleScoreSigns
