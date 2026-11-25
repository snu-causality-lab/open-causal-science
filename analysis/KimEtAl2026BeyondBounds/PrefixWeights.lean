import Mathlib

/-!
# Observed prefix probabilities and response probabilities

For a fixed observation vector in a topological ordering, the probability of a
prefix is the product of the response masses of its C-components. A new observed
vertex adds a constraint in one component. Matching the observational law is
then equivalent to a system of equalities linear in each component's response
weights. The zero-prefix case uses monotonicity and permits structural zeros.

This is an algebraic step in the canonical hull calculation in Kim, Cho and
Lee (UAI 2026), Section 3.2 and Appendix B.1.
Source: https://proceedings.mlr.press/v337/kim26b.html
-/

open scoped BigOperators

namespace KimEtAl2026BeyondBounds

variable {C : Type*} [Fintype C]

/-- The product of the component response masses at a prefix. -/
def prefixMass (q : ℕ → C → ℝ) (t : ℕ) : ℝ :=
  ∏ c, q t c

private theorem prefix_factor [DecidableEq C] (q : ℕ → C → ℝ) (t : ℕ) (owner : C) :
    prefixMass q t = q t owner * ∏ c ∈ Finset.univ.erase owner, q t c := by
  unfold prefixMass
  exact (Finset.mul_prod_erase Finset.univ (q t) (Finset.mem_univ owner)).symm

private theorem prefix_step [DecidableEq C] (q : ℕ → C → ℝ) (owner : C) (t : ℕ)
    (other : ∀ c, c ≠ owner → q (t + 1) c = q t c) :
    prefixMass q (t + 1) = q (t + 1) owner * ∏ c ∈ Finset.univ.erase owner, q t c := by
  rw [prefix_factor q (t + 1) owner]
  congr 1
  exact Finset.prod_congr rfl fun c hc => other c (Finset.ne_of_mem_erase hc)

theorem prefix_mass_nonincreasing (q : ℕ → C → ℝ) (owner : C) (t : ℕ)
    (nonnegative : ∀ c, 0 ≤ q t c)
    (own : q (t + 1) owner ≤ q t owner)
    (other : ∀ c, c ≠ owner → q (t + 1) c = q t c) :
    prefixMass q (t + 1) ≤ prefixMass q t := by
  classical
  rw [prefix_step q owner t other, prefix_factor q t owner]
  exact mul_le_mul_of_nonneg_right own (Finset.prod_nonneg fun c _ => nonnegative c)

/-- One linear cross-multiplied equation per observation step exactly
characterizes equality of all model and target prefix probabilities.

The input specifies one changing component per step, nonnegative component
weights, and monotone factual and target prefix probabilities. A zero target
prefix stays zero in the next step. -/
theorem prefix_mass_matches_iff (n : ℕ) (owner : ℕ → C)
    (p : ℕ → ℝ) (q : ℕ → C → ℝ)
    (initial : prefixMass q 0 = p 0)
    (p_nonneg : ∀ t, t ≤ n → 0 ≤ p t)
    (p_step : ∀ t, t < n → p (t + 1) ≤ p t)
    (q_nonneg : ∀ t, t ≤ n → ∀ c, 0 ≤ q t c)
    (q_own : ∀ t, t < n → q (t + 1) (owner t) ≤ q t (owner t))
    (q_other : ∀ t, t < n → ∀ c, c ≠ owner t → q (t + 1) c = q t c) :
    (∀ t, t ≤ n → prefixMass q t = p t) ↔
      ∀ t, t < n → p t * q (t + 1) (owner t) = p (t + 1) * q t (owner t) := by
  classical
  constructor
  · intro match_all t ht
    rw [← match_all t (Nat.le_of_lt ht), ← match_all (t + 1) (Nat.succ_le_of_lt ht)]
    rw [prefix_step q (owner t) t (q_other t ht), prefix_factor q t (owner t)]
    ring
  · intro step t
    induction t with
    | zero => intro _; exact initial
    | succ t ih =>
        intro hs
        have ht : t < n := Nat.lt_of_succ_le hs
        have hp := ih (Nat.le_of_lt ht)
        by_cases zero : p t = 0
        · have nextZero : p (t + 1) = 0 :=
            le_antisymm (by simpa [zero] using p_step t ht) (p_nonneg (t + 1) hs)
          have nextMassNonneg : 0 ≤ prefixMass q (t + 1) :=
            Finset.prod_nonneg fun c _ => q_nonneg (t + 1) hs c
          have nextMassZero : prefixMass q (t + 1) = 0 :=
            le_antisymm (by
              rw [← zero, ← hp]
              exact prefix_mass_nonincreasing q (owner t) t
                (q_nonneg t (Nat.le_of_lt ht)) (q_own t ht) (q_other t ht)) nextMassNonneg
          exact nextMassZero.trans nextZero.symm
        · let r := ∏ c ∈ Finset.univ.erase (owner t), q t c
          have before : q t (owner t) * r = p t :=
            (prefix_factor q t (owner t)).symm.trans hp
          have after : prefixMass q (t + 1) = q (t + 1) (owner t) * r :=
            prefix_step q (owner t) t (q_other t ht)
          have equation : p t * prefixMass q (t + 1) = p t * p (t + 1) := by
            calc
              p t * prefixMass q (t + 1) =
                  (p t * q (t + 1) (owner t)) * r := by rw [after, mul_assoc]
              _ = (p (t + 1) * q t (owner t)) * r := by rw [step t ht]
              _ = p t * p (t + 1) := by rw [mul_assoc, before, mul_comm]
          exact mul_left_cancel₀ zero equation

end KimEtAl2026BeyondBounds
