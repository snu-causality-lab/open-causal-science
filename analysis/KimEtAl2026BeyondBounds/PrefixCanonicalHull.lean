import KimEtAl2026BeyondBounds.CanonicalHull
import KimEtAl2026BeyondBounds.PrefixWeights

/-!
# Canonical hull from observed prefixes

In a topological order, the response equations for an observed prefix only
use that prefix and the independent response blocks. Their probability is the
product of the blocks' prefix masses. Each step adds a constraint only in the
new vertex's block. This module models that finite prefix interface and proves
exact hull membership by a bounded linear system, including on zero-mass prefixes.

Kim, Cho and Lee (UAI 2026), Lemma 2 and Appendix B.1.
https://proceedings.mlr.press/v337/kim26b.html
-/

namespace KimEtAl2026BeyondBounds

open scoped BigOperators

variable {C A : Type*} [Fintype C] {Response : C → Type*}
variable [∀ i, Fintype (Response i)] {n : ℕ}

/-- Finite response indicators for observations in a topological order.
`accepts c a t u` tests the equations belonging to component `c` among the
first `t` observed vertices at a specified assignment `a`. -/
structure ObservationPrefixes (Response : C → Type*) (A : Type*) (n : ℕ) where
  owner : ℕ → C
  accepts : (c : C) → A × ℕ → Response c → Bool
  no_constraints : ∀ c a u, accepts c (a, 0) u = true
  nested : ∀ a t, t < n → ∀ u, accepts (owner t) (a, t + 1) u = true →
    accepts (owner t) (a, t) u = true
  other_unchanged : ∀ a t, t < n → ∀ c, c ≠ owner t →
    ∀ u, accepts c (a, t + 1) u = accepts c (a, t) u

/-- The compatibility set, with observational prefix probabilities as input. -/
def prefixCanonicalHull (spec : ObservationPrefixes Response A n) (p : A → ℕ → ℝ) :
    Set (Parameters Response) :=
  {θ | NormalizedBlocks θ ∧ ∀ a t, t ≤ n →
    prefixMass (fun s c => qFactor spec.accepts θ c (a, s)) t = p a t}

/-- The row only belongs to the component owning the newly observed vertex. -/
abbrev PrefixRow (spec : ObservationPrefixes Response A n) (c : C) :=
  {entry : A × Fin n // spec.owner entry.2.val = c}

noncomputable def prefixCoefficient
    (spec : ObservationPrefixes Response A n) (p : A → ℕ → ℝ)
    (c : C) (row : PrefixRow spec c) (u : Response c) : ℝ :=
  let (a, t) := row.val
  p a t.val * indicatorCoefficient spec.accepts c (a, t.val + 1) u -
    p a (t.val + 1) * indicatorCoefficient spec.accepts c (a, t.val) u

omit [Fintype C] in
private theorem prefix_constraint_value
    (spec : ObservationPrefixes Response A n) (p : A → ℕ → ℝ)
    (θ : Parameters Response) (c : C) (row : PrefixRow spec c) :
    blockLinear (prefixCoefficient spec p) θ c row =
      p row.val.1 row.val.2.val * qFactor spec.accepts θ c (row.val.1, row.val.2.val + 1) -
      p row.val.1 (row.val.2.val + 1) * qFactor spec.accepts θ c (row.val.1, row.val.2.val) := by
  simp only [qFactor, blockLinear, prefixCoefficient, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, ← mul_assoc]

omit [Fintype C] in
private theorem nonnegative_prefix_block (spec : ObservationPrefixes Response A n)
    (θ : Parameters Response) (normal : NormalizedBlocks θ) (a : A) (t : ℕ) (c : C) :
    0 ≤ qFactor spec.accepts θ c (a, t) := by
  unfold qFactor blockLinear indicatorCoefficient
  apply Finset.sum_nonneg
  intro u _
  split
  · simpa using (normal.1 c u).1
  · simp

omit [Fintype C] in
private theorem owner_prefix_block_decreases (spec : ObservationPrefixes Response A n)
    (θ : Parameters Response) (normal : NormalizedBlocks θ) (a : A) (t : ℕ)
    (ht : t < n) :
    qFactor spec.accepts θ (spec.owner t) (a, t + 1) ≤
      qFactor spec.accepts θ (spec.owner t) (a, t) := by
  unfold qFactor blockLinear indicatorCoefficient
  apply Finset.sum_le_sum
  intro u _
  by_cases accepted : spec.accepts (spec.owner t) (a, t + 1) u = true
  · simp [accepted, spec.nested a t ht u accepted]
  · rw [ite_eq_right accepted, zero_mul]
    split
    · simpa using (normal.1 (spec.owner t) u).1
    · simp

private theorem all_prefixes_match_iff (spec : ObservationPrefixes Response A n)
    (p : A → ℕ → ℝ) (p0 : ∀ a, p a 0 = 1)
    (nonnegative : ∀ a t, t ≤ n → 0 ≤ p a t)
    (decreases : ∀ a t, t < n → p a (t + 1) ≤ p a t)
    (θ : Parameters Response) (normal : NormalizedBlocks θ) (a : A) :
    (∀ t, t ≤ n → prefixMass (fun s c => qFactor spec.accepts θ c (a, s)) t = p a t) ↔
      ∀ t, t < n →
        p a t * qFactor spec.accepts θ (spec.owner t) (a, t + 1) =
          p a (t + 1) * qFactor spec.accepts θ (spec.owner t) (a, t) := by
  apply prefix_mass_matches_iff n spec.owner (p a)
  · simp [prefixMass, qFactor, blockLinear, indicatorCoefficient, spec.no_constraints, p0, normal.2]
  · exact nonnegative a
  · exact decreases a
  · exact fun t _ c => nonnegative_prefix_block spec θ normal a t c
  · exact owner_prefix_block_decreases spec θ normal a
  · intro t ht c other
    simp [qFactor, blockLinear, indicatorCoefficient, spec.other_unchanged a t ht c other]

/-- The prefix compatibility set equals the finite system of blockwise linear
constraints. The observational law supplies normalized monotone prefix masses. -/
theorem prefix_canonical_hull_eq_linear_constraints
    (spec : ObservationPrefixes Response A n) (p : A → ℕ → ℝ)
    (p0 : ∀ a, p a 0 = 1)
    (nonnegative : ∀ a t, t ≤ n → 0 ≤ p a t)
    (decreases : ∀ a t, t < n → p a (t + 1) ≤ p a t) :
    prefixCanonicalHull spec p = linearConstraintSet (prefixCoefficient spec p) (fun _ _ => 0) := by
  ext θ
  constructor
  · rintro ⟨normal, agrees⟩
    refine ⟨normal, fun c row => ?_⟩
    rcases row with ⟨⟨a, t⟩, rfl⟩
    rw [prefix_constraint_value, sub_eq_zero]
    exact (all_prefixes_match_iff spec p p0 nonnegative decreases θ normal a).1 (agrees a) t.val t.isLt
  · rintro ⟨normal, equations⟩
    refine ⟨normal, fun a => (all_prefixes_match_iff spec p p0 nonnegative decreases θ normal a).2 ?_⟩
    intro t ht
    let row : PrefixRow spec (spec.owner t) := ⟨(a, ⟨t, ht⟩), rfl⟩
    have equation := equations (spec.owner t) row
    rw [prefix_constraint_value, sub_eq_zero] at equation
    exact equation

theorem prefix_canonical_hull_convex_and_bounded
    (spec : ObservationPrefixes Response A n) (p : A → ℕ → ℝ)
    (p0 : ∀ a, p a 0 = 1)
    (nonnegative : ∀ a t, t ≤ n → 0 ≤ p a t)
    (decreases : ∀ a t, t < n → p a (t + 1) ≤ p a t) :
    Convex ℝ (prefixCanonicalHull spec p) ∧
      prefixCanonicalHull spec p ⊆ Set.Icc (0 : Parameters Response) 1 := by
  rw [prefix_canonical_hull_eq_linear_constraints spec p p0 nonnegative decreases]
  exact ⟨linear_constraints_convex _ _, linear_constraints_subset_unit_box _ _⟩

omit [Fintype C] [∀ i, Fintype (Response i)] in
theorem finite_prefix_rows [Finite A] (spec : ObservationPrefixes Response A n) (c : C) :
    Finite (PrefixRow spec c) := inferInstance

end KimEtAl2026BeyondBounds
