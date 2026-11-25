import KimEtAl2026BeyondBounds.PrefixCanonicalHull
import KimEtAl2026BeyondBounds.ReducedCE

/-!
# Canonical compatibility from the structural equations

Kim, Cho and Lee (UAI 2026), Lemma 2 and Appendix B.1.
https://proceedings.mlr.press/v337/kim26b.html

The prefix indicator system is constructed directly from the finite factual
structural equations in a topological order. Matching all observational
prefixes is equivalent to matching all full assignment masses. The resulting
linear system uses these observable prefix probabilities and allows zeros.
-/

namespace KimEtAl2026BeyondBounds.RankedSCM

open scoped BigOperators

universe u v w z

variable {V : Type u} {C : Type v} {Value : V → Type w} {Noise : C → Type z}
variable {G : RankedSCM V C Value Noise} {n : ℕ}

/-- Enumerate the vertices so every parent occurs before its child. -/
structure TopologicalOrder (G : RankedSCM V C Value Noise) (n : ℕ) where
  vertex : Fin n ≃ V
  parentBefore : ∀ {p i}, G.parent p i → (vertex.symm p).val < (vertex.symm i).val

namespace TopologicalOrder

variable (order : TopologicalOrder G n)

def AgreesThrough (target assignment : ∀ i, Value i) (t : ℕ) : Prop :=
  ∀ i, (order.vertex.symm i).val < t → assignment i = target i

/-- The response equations assigned to one block at the specified prefix. -/
def PrefixEquationsHold (c : C) (a : ∀ i, Value i) (t : ℕ) (u : Noise c) : Prop :=
  ∀ i, (order.vertex.symm i).val < t → ∀ h : G.block i = c,
    a i = G.response i (fun p => a p.val) (h.symm ▸ u)

private def ownerAt (default : C) (t : ℕ) : C :=
  if h : t < n then G.block (order.vertex ⟨t, h⟩) else default

private theorem accept_step_backward (a : ∀ i, Value i) (t : ℕ) (c : C) (u : Noise c)
    (h : order.PrefixEquationsHold c a (t + 1) u) : order.PrefixEquationsHold c a t u :=
  fun i hi hc => h i (hi.trans (Nat.lt_succ_self t)) hc

private theorem accept_step_of_other (default : C) (a : ∀ i, Value i) (t : ℕ) (ht : t < n)
    (c : C) (other : c ≠ order.ownerAt default t) (u : Noise c)
    (h : order.PrefixEquationsHold c a t u) : order.PrefixEquationsHold c a (t + 1) u := by
  intro i hi hc
  apply h i _ hc
  by_contra! later
  have hIndex : order.vertex.symm i = ⟨t, ht⟩ := Fin.ext (by
    change (order.vertex.symm i).val = t
    omega)
  have hVertex : i = order.vertex ⟨t, ht⟩ := by
    simpa only [Equiv.apply_symm_apply] using congrArg order.vertex hIndex
  exact other (by simpa [ownerAt, ht, hVertex] using hc.symm)

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The fallback owner is used only for indices outside the enumeration. -/
def prefixSpecification (default : C) : ObservationPrefixes Noise (∀ i, Value i) n where
  owner := order.ownerAt default
  accepts := fun c atAndCount u => decide (order.PrefixEquationsHold c atAndCount.1 atAndCount.2 u)
  no_constraints := by
    intro c a u
    simp [PrefixEquationsHold]
  nested := by
    intro a t _ u accepted
    simp only [decide_eq_true_eq] at accepted ⊢
    exact order.accept_step_backward a t _ u accepted
  other_unchanged := by
    intro a t ht c other u
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact ⟨order.accept_step_backward a t c u, order.accept_step_of_other default a t ht c other u⟩

theorem factual_prefix_iff_accepts (noise : ∀ c, Noise c) (a : ∀ i, Value i) (t : ℕ) :
    order.AgreesThrough a (G.factual noise) t ↔ ∀ c, order.PrefixEquationsHold c a t (noise c) := by
  constructor
  · intro h c i hi hc
    subst c
    calc
      a i = G.factual noise i := (h i hi).symm
      _ = G.response i (fun p => G.factual noise p.val) (noise (G.block i)) :=
        G.factual_at noise i
      _ = G.response i (fun p => a p.val) (noise (G.block i)) := by
        congr 1
        funext p
        exact h p.val ((order.parentBefore p.prop).trans hi)
  · intro h i
    induction i using (measure (fun p : V => (order.vertex.symm p).val)).wf.induction with
    | h i ih =>
      intro hi
      rw [G.factual_at noise i, h (G.block i) i hi rfl]
      congr 1
      funext p
      exact ih p.val (order.parentBefore p.prop) ((order.parentBefore p.prop).trans hi)

variable [Fintype V] [DecidableEq V] [∀ i, Fintype (Value i)]

/-- Marginal mass under the observed law at the specified factual prefix. -/
def observedPrefix (p : ((i : V) → Value i) → ℝ) (a : ∀ i, Value i) (t : ℕ) : ℝ :=
  ∑ b, if order.AgreesThrough a b t then p b else 0

private theorem observed_prefix_zero (p : ((i : V) → Value i) → ℝ) (normalized : ∑ a, p a = 1)
    (a : ∀ i, Value i) : order.observedPrefix p a 0 = 1 := by
  simpa [observedPrefix, AgreesThrough] using normalized

private theorem observed_prefix_nonnegative (p : ((i : V) → Value i) → ℝ)
    (nonnegative : ∀ a, 0 ≤ p a) (a : ∀ i, Value i) (t : ℕ) :
    0 ≤ order.observedPrefix p a t := by
  apply Finset.sum_nonneg
  intro b _
  split <;> simp [nonnegative]

private theorem observed_prefix_decreases (p : ((i : V) → Value i) → ℝ)
    (nonnegative : ∀ a, 0 ≤ p a) (a : ∀ i, Value i) (t : ℕ) :
    order.observedPrefix p a (t + 1) ≤ order.observedPrefix p a t := by
  apply Finset.sum_le_sum
  intro b _
  by_cases h : order.AgreesThrough a b (t + 1)
  · have hsmall : order.AgreesThrough a b t := fun i hi => h i (hi.trans (Nat.lt_succ_self t))
    simp [h, hsmall]
  · by_cases hsmall : order.AgreesThrough a b t <;> simp [h, hsmall, nonnegative]

/-- Marginalizing a full prefix leaves the mass of the one specified assignment. -/
theorem observed_prefix_full (p : ((i : V) → Value i) → ℝ) (a : ∀ i, Value i) :
    order.observedPrefix p a n = p a := by
  have heq (b : ∀ i, Value i) : order.AgreesThrough a b n ↔ b = a := by
    constructor
    · intro h
      funext i
      exact h i (order.vertex.symm i).isLt
    · rintro rfl i _
      rfl
  simp [observedPrefix, heq]

variable [Fintype C] [DecidableEq C] [∀ c, Fintype (Noise c)]

/-- Factor the actual observation-prefix event in the structural model. -/
theorem observational_prefix_factorization (θ : BlockWeights (Noise := Noise)) (default : C)
    (a : ∀ i, Value i) (t : ℕ) :
    order.observedPrefix (G.observationalMass θ) a t =
      prefixMass (fun k c => qFactor (order.prefixSpecification default).accepts θ.weight c (a, k))
        t := by
  unfold observedPrefix
  rw [G.observationalMass_event]
  simp only [order.factual_prefix_iff_accepts]
  rw [sum_product_independent]
  apply Finset.prod_congr rfl
  intro c _
  simp only [localMass, qFactor, blockLinear, indicatorCoefficient, prefixSpecification,
    decide_eq_true_eq]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : order.PrefixEquationsHold c a t u <;> simp [h]

/-- The full observational compatibility set for the finite structural model. -/
def scmCanonicalHull (p : ((i : V) → Value i) → ℝ) : Set (Parameters Noise) :=
  {w | ∃ θ : BlockWeights (Noise := Noise), θ.weight = w ∧ ∀ a, G.observationalMass θ a = p a}

omit [Fintype C] [DecidableEq C] in
private theorem blockWeights_normalized (θ : BlockWeights (Noise := Noise)) :
    NormalizedBlocks θ.weight := by
  refine ⟨fun c u => ⟨θ.nonnegative c u, ?_⟩, θ.normalized⟩
  rw [← θ.normalized c]
  exact Finset.single_le_sum (fun r _ => θ.nonnegative c r) (Finset.mem_univ u)

theorem scm_canonical_hull_eq_prefix (p : ((i : V) → Value i) → ℝ) (default : C) :
    scmCanonicalHull (G := G) p =
      prefixCanonicalHull (order.prefixSpecification default) (order.observedPrefix p) := by
  ext w
  constructor
  · rintro ⟨θ, rfl, h⟩
    refine ⟨blockWeights_normalized θ, fun a t _ => ?_⟩
    rw [← order.observational_prefix_factorization θ default a t, funext h]
  · rintro ⟨hn, h⟩
    let θ : BlockWeights (Noise := Noise) := ⟨w, fun c r => (hn.1 c r).1, hn.2⟩
    refine ⟨θ, rfl, fun a => ?_⟩
    rw [← order.observed_prefix_full (G.observationalMass θ) a,
      order.observational_prefix_factorization θ default a n]
    exact (h a n le_rfl).trans (order.observed_prefix_full p a)

/-- Lemma 2 for the canonical response-table model: exact linear constraints
for the full observational law, including structural zeros. -/
theorem scm_canonical_hull_eq_linear_constraints (p : ((i : V) → Value i) → ℝ)
    (normalized : ∑ a, p a = 1) (nonnegative : ∀ a, 0 ≤ p a) (default : C) :
    scmCanonicalHull (G := G) p =
      linearConstraintSet
        (prefixCoefficient (order.prefixSpecification default) (order.observedPrefix p))
        (fun _ _ => 0) := by
  rw [order.scm_canonical_hull_eq_prefix p default]
  exact prefix_canonical_hull_eq_linear_constraints _ _
    (order.observed_prefix_zero p normalized)
    (fun a t _ => order.observed_prefix_nonnegative p nonnegative a t)
    (fun a t _ => order.observed_prefix_decreases p nonnegative a t)

include order in
theorem scm_canonical_hull_convex_and_bounded (p : ((i : V) → Value i) → ℝ)
    (normalized : ∑ a, p a = 1) (nonnegative : ∀ a, 0 ≤ p a) (default : C) :
    Convex ℝ (scmCanonicalHull (G := G) p) ∧
      scmCanonicalHull (G := G) p ⊆ Set.Icc (0 : Parameters Noise) 1 := by
  rw [order.scm_canonical_hull_eq_linear_constraints p normalized nonnegative default]
  exact ⟨linear_constraints_convex _ _, linear_constraints_subset_unit_box _ _⟩

end

end TopologicalOrder

end KimEtAl2026BeyondBounds.RankedSCM
