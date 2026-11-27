import OpenCausalScienceAnalysis.Decision.SCB2019Projection

/-!
# Forward projection of a structural causal mechanism

Proposition 2 of the September 19, 2026 correction substitutes an eliminated
vertex's equation into its children. The old roots keep their indices, including
roots read by more than two equations. One constant root represents the fork from
the eliminated vertex, including when its equation has no exogenous inputs.

Source: https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Finset Mec

variable {n : ℕ}

/-- Keep all original roots and add one root for the eliminated fork. -/
abbrev ForwardRoots (m : Model n) := m.L ⊕ Unit

/-- The added root takes only one value. -/
def ForwardNoise (m : Model n) : ForwardRoots m → Type
  | .inl l => m.U l
  | .inr _ => Unit

/-- Read the original part of a projected root assignment. -/
def forwardNoise (m : Model n) (u : ∀ l, ForwardNoise m l) (l : m.L) : m.U l :=
  u (.inl l)

private def forwardParents (m : Model n) (w i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => (eliminate m.scm.toMech.diag w).dir j i = true

private theorem mem_forwardParents (m : Model n) (w j i : Fin n) :
    j ∈ forwardParents m w i ↔ j ≠ w ∧ i ≠ w ∧
      (j ∈ m.scm.pa i ∨ (j ∈ m.scm.pa w ∧ w ∈ m.scm.pa i)) := by
  simp [forwardParents, dir_eliminate_iff, Mech.diag_dir]

private theorem not_mem_own_parents (m : Model n) (i : Fin n) : i ∉ m.scm.pa i :=
  fun h => (lt_irrefl _ (m.scm.pa_rank h)).elim

private def forwardScope (m : Model n) (w i : Fin n) : Finset (ForwardRoots m) :=
  if i = w then ∅ else
    ((m.scm.ex i ∪ if w ∈ m.scm.pa i then m.scm.ex w else ∅).map
      ⟨Sum.inl, Sum.inl_injective⟩) ∪
      (if w ∈ m.scm.pa i then {Sum.inr ()} else ∅)

private theorem mem_forwardScope_inl (m : Model n) (w i : Fin n) (l : m.L) :
    Sum.inl l ∈ forwardScope m w i ↔ i ≠ w ∧
      (l ∈ m.scm.ex i ∨ (l ∈ m.scm.ex w ∧ w ∈ m.scm.pa i)) := by
  by_cases hi : i = w
  · simp [forwardScope, hi]
  · by_cases hw : w ∈ m.scm.pa i <;> simp [forwardScope, hi, hw]

private theorem mem_forwardScope_inr (m : Model n) (w i : Fin n) (e : Unit) :
    Sum.inr e ∈ forwardScope m w i ↔ i ≠ w ∧ w ∈ m.scm.pa i := by
  cases e
  by_cases hi : i = w
  · simp [forwardScope, hi]
  · by_cases hw : w ∈ m.scm.pa i <;> simp [forwardScope, hi, hw]

private def forwardEquation (m : Model n) (w i : Fin n) (z : ∀ j, m.X j)
    (u : ∀ l, ForwardNoise m l) : m.X i :=
  if i = w then default else
    m.scm.f i (Function.update z w (m.scm.f w z (forwardNoise m u))) (forwardNoise m u)

private theorem forwardEquation_dep_parents (m : Model n) (w i : Fin n)
    (z z' : ∀ j, m.X j) (u : ∀ l, ForwardNoise m l)
    (same : ∀ j ∈ forwardParents m w i, z j = z' j) :
    forwardEquation m w i z u = forwardEquation m w i z' u := by
  by_cases hi : i = w
  · simp [forwardEquation, hi]
  · simp only [forwardEquation, ite_eq_right hi]
    apply m.scm.f_pa
    intro j hj
    by_cases h : j = w
    · subst j
      simp only [Function.update_self]
      apply m.scm.f_pa
      intro a ha
      have hne : a ≠ w := fun eq => not_mem_own_parents m w (eq ▸ ha)
      exact same a ((mem_forwardParents m w a i).mpr ⟨hne, hi, .inr ⟨ha, hj⟩⟩)
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      exact same j ((mem_forwardParents m w j i).mpr ⟨h, hi, .inl hj⟩)

private theorem forwardEquation_dep_roots (m : Model n) (w i : Fin n)
    (z : ∀ j, m.X j) (u u' : ∀ l, ForwardNoise m l)
    (same : ∀ l ∈ forwardScope m w i, u l = u' l) :
    forwardEquation m w i z u = forwardEquation m w i z u' := by
  by_cases hi : i = w
  · simp [forwardEquation, hi]
  · simp only [forwardEquation, ite_eq_right hi]
    calc
      _ = m.scm.f i (Function.update z w (m.scm.f w z (forwardNoise m u'))) (forwardNoise m u) := by
        apply m.scm.f_pa
        intro j hj
        by_cases h : j = w
        · subst j
          simp only [Function.update_self]
          apply m.scm.f_ex
          intro l hl
          exact same (.inl l) ((mem_forwardScope_inl m w i l).mpr ⟨hi, .inr ⟨hl, hj⟩⟩)
        · simp only [Function.update_of_ne h]
      _ = _ := by
        apply m.scm.f_ex
        intro l hl
        exact same (.inl l) ((mem_forwardScope_inl m w i l).mpr ⟨hi, .inl hl⟩)

/-- Substitute the removed equation and leave its vertex index isolated. -/
def forwardMech (m : Model n) (w : Fin n) :
    Mech n m.X (ForwardRoots m) (ForwardNoise m) where
  pa := forwardParents m w
  ex := forwardScope m w
  rank := m.scm.rank
  pa_rank := by
    intro i j h
    rcases (mem_forwardParents m w j i).mp h with ⟨_, _, direct | ⟨into, out⟩⟩
    · exact m.scm.pa_rank direct
    · exact lt_trans (m.scm.pa_rank into) (m.scm.pa_rank out)
  f := forwardEquation m w
  f_pa := forwardEquation_dep_parents m w
  f_ex := forwardEquation_dep_roots m w

private theorem original_bidirected_iff (m : Model n) (i j : Fin n) :
    m.scm.toMech.diag.bi i j = true ↔
      i ≠ j ∧ ∃ l, l ∈ m.scm.ex i ∧ l ∈ m.scm.ex j := by
  simp [Mech.diag, Finset.Nonempty]

/-- The projected mechanism has exactly the one-vertex latent projection diagram. -/
theorem forwardMech_diag (m : Model n) (w : Fin n) :
    (forwardMech m w).diag = eliminate m.scm.toMech.diag w := by
  rw [ADMG.ext_iff']
  constructor
  · funext j i
    simp [Mech.diag, forwardMech, forwardParents]
  · funext i j
    apply Bool.eq_iff_iff.mpr
    rw [bi_eliminate_iff]
    simp only [Mech.diag_dir]
    change decide (i ≠ j ∧ (forwardScope m w i ∩ forwardScope m w j).Nonempty) = true ↔ _
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨distinct, l, member⟩
      obtain ⟨hi, hj⟩ := mem_inter.mp member
      cases l with
      | inl k =>
        obtain ⟨hiw, directI | ⟨intoI, outI⟩⟩ := (mem_forwardScope_inl m w i k).mp hi
        · obtain ⟨hjw, directJ | ⟨intoJ, outJ⟩⟩ := (mem_forwardScope_inl m w j k).mp hj
          · exact ⟨hiw, hjw, distinct, .inl ((original_bidirected_iff m i j).mpr
              ⟨distinct, k, directI, directJ⟩)⟩
          · exact ⟨hiw, hjw, distinct, .inr (.inl
              ⟨(original_bidirected_iff m i w).mpr ⟨hiw, k, directI, intoJ⟩, outJ⟩)⟩
        · obtain ⟨hjw, directJ | ⟨_, outJ⟩⟩ := (mem_forwardScope_inl m w j k).mp hj
          · exact ⟨hiw, hjw, distinct, .inr (.inr (.inl
              ⟨(original_bidirected_iff m j w).mpr ⟨hjw, k, directJ, intoI⟩, outI⟩))⟩
          · exact ⟨hiw, hjw, distinct, .inr (.inr (.inr ⟨outI, outJ⟩))⟩
      | inr e =>
        obtain ⟨hiw, outI⟩ := (mem_forwardScope_inr m w i e).mp hi
        obtain ⟨hjw, outJ⟩ := (mem_forwardScope_inr m w j e).mp hj
        exact ⟨hiw, hjw, distinct, .inr (.inr (.inr ⟨outI, outJ⟩))⟩
    · rintro ⟨hiw, hjw, distinct, direct | ⟨cross, outJ⟩ | ⟨cross, outI⟩ | ⟨outI, outJ⟩⟩
      · obtain ⟨_, k, hi, hj⟩ := (original_bidirected_iff m i j).mp direct
        exact ⟨distinct, .inl k, mem_inter.mpr
          ⟨(mem_forwardScope_inl m w i k).mpr ⟨hiw, .inl hi⟩,
            (mem_forwardScope_inl m w j k).mpr ⟨hjw, .inl hj⟩⟩⟩
      · obtain ⟨_, k, hi, hk⟩ := (original_bidirected_iff m i w).mp cross
        exact ⟨distinct, .inl k, mem_inter.mpr
          ⟨(mem_forwardScope_inl m w i k).mpr ⟨hiw, .inl hi⟩,
            (mem_forwardScope_inl m w j k).mpr ⟨hjw, .inr ⟨hk, outJ⟩⟩⟩⟩
      · obtain ⟨_, k, hj, hk⟩ := (original_bidirected_iff m j w).mp cross
        exact ⟨distinct, .inl k, mem_inter.mpr
          ⟨(mem_forwardScope_inl m w i k).mpr ⟨hiw, .inr ⟨hk, outI⟩⟩,
            (mem_forwardScope_inl m w j k).mpr ⟨hjw, .inl hj⟩⟩⟩
      · exact ⟨distinct, .inr (), mem_inter.mpr
          ⟨(mem_forwardScope_inr m w i ()).mpr ⟨hiw, outI⟩,
            (mem_forwardScope_inr m w j ()).mpr ⟨hjw, outJ⟩⟩⟩

/-- Every retained response is unchanged under every intervention avoiding the removed vertex. -/
theorem forwardMech_resp (m : Model n) (w : Fin n) {S : Finset (Fin n)} (hw : w ∉ S)
    (x : ∀ i, m.X i) (u : ∀ l, ForwardNoise m l) {y : Fin n} (hy : y ≠ w) :
    (forwardMech m w).resp S x u y = m.scm.toMech.resp S x (forwardNoise m u) y := by
  let base := m.scm.toMech.resp S x (forwardNoise m u)
  let z := Function.update base w default
  have equationW : m.scm.f w z (forwardNoise m u) = base w := by
    calc
      _ = m.scm.f w base (forwardNoise m u) := by
        apply m.scm.f_pa
        intro j hj
        have ne : j ≠ w := fun eq => not_mem_own_parents m w (eq ▸ hj)
        simp only [z, Function.update_of_ne ne]
      _ = _ := (m.scm.toMech.resp_of_not_mem hw).symm
  have substituted : Function.update z w (m.scm.f w z (forwardNoise m u)) = base := by
    funext i
    by_cases hi : i = w
    · subst i
      simp only [Function.update_self, equationW]
    · simp only [Function.update_of_ne hi, z]
  have equilibrium : z = (forwardMech m w).resp S x u := by
    apply (forwardMech m w).eq_resp
    intro i
    by_cases hi : i = w
    · subst i
      simp [z, hw, forwardMech, forwardEquation]
    · by_cases set : i ∈ S
      · simp only [z, Function.update_of_ne hi, ite_eq_left set]
        exact m.scm.toMech.resp_of_mem set
      · simp only [ite_eq_right set]
        change z i = forwardEquation m w i z u
        simp only [forwardEquation, ite_eq_right hi, substituted]
        simp only [z, Function.update_of_ne hi]
        exact m.scm.toMech.resp_of_not_mem set
  rw [← equilibrium]
  simp only [z, Function.update_of_ne hy, base]

end OpenCausalScienceAnalysis.Scb2019
