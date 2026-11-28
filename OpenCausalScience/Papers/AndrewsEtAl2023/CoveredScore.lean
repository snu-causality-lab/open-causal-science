module
public import OpenCausalScience.Papers.AndrewsEtAl2023.DeletionScore
public import OpenCausalScience.Papers.AndrewsEtAl2023.SampleScoreSigns
public import OpenCausalScience.Papers.Chickering1995.Transformation

/-! # Score equivalence from covered reversals -/

namespace OpenCausalScience.Papers.AndrewsEtAl2023

open Probability.CI Chickering1995.CoveredReversal Chickering1995.Transformation
open GrowShrinkTree PopulationProjection DeletionScore SampleScoreSigns

@[expose] public section

variable {n : Nat}

private theorem sum_perm {left right : List Rat} (perm : left.Perm right) : left.sum = right.sum := by
  induction perm with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y rest => simp only [List.sum_cons]; rw [← Rat.add_assoc, Rat.add_comm y x, Rat.add_assoc]
  | trans _ _ first second => exact first.trans second

private abbrev parentList (D : DAG n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun u => D.edge u v)

private theorem parent_mem (D : DAG n) (v u : Fin n) : u ∈ parentList D v ↔ D.edge u v = true := by
  simp [parentList]

private theorem mask_eq_of_membership {P Q : List (Fin n)} (same : ∀ z, z ∈ P ↔ z ∈ Q) :
    maskOfList P = maskOfList Q := by
  funext z
  apply Bool.eq_iff_iff.mpr
  simpa [maskOfList] using same z

/-- Two local score terms balance whenever the two endpoints exchange parent status. -/
def CoveredScoreIdentity (scores : Fin n → LocalScore n) : Prop :=
  ∀ a b P, a ≠ b → a ∉ P → b ∉ P →
    scores a P + scores b (a :: P) = scores a (b :: P) + scores b P

private theorem score_of_reversal {scores : Fin n → LocalScore n} (sets : SetScores scores)
    (localIdentity : CoveredScoreIdentity scores) {G H : DAG n} {a b : Fin n}
    (R : Reversal G H a b) : decomposableScore scores G = decomposableScore scores H := by
  have noLoop (D : DAG n) (v : Fin n) : D.edge v v ≠ true :=
    fun edge => D.no_directed_cycle v (.single edge)
  have distinct : a ≠ b := by rintro rfl; exact noLoop G a R.forward
  have noOpposite (D : DAG n) {x y : Fin n} (edge : D.edge x y = true) : D.edge y x ≠ true :=
    fun opposite => D.no_directed_cycle x (.extend (.single edge) opposite)
  let P := parentList G a
  have leftOutside : a ∉ P := fun h => noLoop G a ((parent_mem ..).mp h)
  have rightOutside : b ∉ P := fun h => noOpposite G R.forward ((parent_mem ..).mp h)
  have oldHead : maskOfList (parentList G b) = maskOfList (a :: P) := by
    apply mask_eq_of_membership
    intro z
    rw [parent_mem, List.mem_cons]
    by_cases ha : z = a
    · subst z; simp [R.forward]
    by_cases hb : z = b
    · subst z; simp [ha, noLoop, rightOutside]
    simpa only [ha, false_or, P, parent_mem] using (R.parents z ha hb).symm
  have newTail : maskOfList (parentList H a) = maskOfList (b :: P) := by
    apply mask_eq_of_membership
    intro z
    rw [parent_mem, List.mem_cons]
    by_cases hb : z = b
    · subst z; simp [R.reverse]
    simpa only [hb, false_or, P, parent_mem] using
      (R.unchanged z a (fun eq => distinct eq.2) (fun eq => hb eq.1)).symm
  have newHead : maskOfList (parentList H b) = maskOfList P := by
    apply mask_eq_of_membership
    intro z
    simp only [P, parent_mem]
    by_cases ha : z = a
    · subst z; simp [noLoop, noOpposite H R.reverse]
    by_cases hb : z = b
    · subst z; simp [noLoop, noOpposite G R.forward]
    exact (R.unchanged z b (fun eq => ha eq.1) (fun eq => hb eq.1)).symm.trans
      (R.parents z ha hb).symm
  let remaining := ((List.finRange n).erase a).erase b
  have first := List.perm_cons_erase (List.mem_finRange a)
  have bMem : b ∈ (List.finRange n).erase a :=
    (List.mem_erase_of_ne distinct.symm).mpr (List.mem_finRange b)
  have second := List.perm_cons_erase bMem
  have perm : (List.finRange n).Perm (a :: b :: remaining) := first.trans (second.cons a)
  have outside := List.nodup_cons.mp (perm.nodup_iff.mp (List.nodup_finRange n))
  have split (D : DAG n) : decomposableScore scores D =
      scores a (parentList D a) + (scores b (parentList D b) +
        (remaining.map (fun z => scores z (parentList D z))).sum) :=
    sum_perm (perm.map fun z => scores z (parentList D z))
  have sameRest : remaining.map (fun z => scores z (parentList G z)) =
      remaining.map (fun z => scores z (parentList H z)) := by
    apply List.map_congr_left
    intro z hz
    apply sets
    apply mask_eq_of_membership
    intro u
    rw [parent_mem, parent_mem]
    apply R.unchanged
    · exact fun eq => (List.nodup_cons.mp outside.2).1 (eq.2 ▸ hz)
    · exact fun eq => outside.1 (List.mem_cons_of_mem _ (eq.2 ▸ hz))
  rw [split G, split H, sameRest, ← Rat.add_assoc, ← Rat.add_assoc,
    sets b _ _ oldHead, sets a _ _ newTail, sets b _ _ newHead]
  exact congrArg (fun pair => pair + _) (localIdentity a b P distinct leftOutside rightOutside)

/-- Balance at every covered reversal suffices for equality throughout each MEC. -/
theorem score_equivalent_of_covered_identity {scores : Fin n → LocalScore n}
    (sets : SetScores scores) (localIdentity : CoveredScoreIdentity scores) : ScoreEquivalent scores := by
  intro G H same
  have seq := reversal_sequence same
  clear same
  induction seq with
  | done edges => unfold decomposableScore; rw [edges]
  | next _ reverse _ ih => exact (score_of_reversal sets localIdentity reverse).trans ih

/-- A local score obtained as the increment of a joint-set potential. -/
def potentialScore (potential : Mask n → Rat) : Fin n → LocalScore n :=
  fun child P => potential (maskOfList (child :: P)) - potential (maskOfList P)

/-- The potential telescopes when either endpoint order is used. -/
theorem potential_score_equivalent (potential : Mask n → Rat) : ScoreEquivalent (potentialScore potential) := by
  have insert (v : Fin n) {P Q : List (Fin n)} (same : maskOfList P = maskOfList Q) :
      maskOfList (v :: P) = maskOfList (v :: Q) := by
    apply mask_eq_of_membership
    intro z
    have h := congrFun same z
    simpa only [maskOfList, decide_eq_true_eq, List.mem_cons] using
      (or_congr Iff.rfl (by simpa [maskOfList] using Bool.eq_iff_iff.mp h) :
        (z = v ∨ z ∈ P) ↔ (z = v ∨ z ∈ Q))
  apply score_equivalent_of_covered_identity
  · intro child P Q same
    unfold potentialScore
    rw [same, insert child same]
  · intro a b P _ _ _
    have comm : maskOfList (b :: a :: P) = maskOfList (a :: b :: P) := by
      apply mask_eq_of_membership
      intro z
      simp only [List.mem_cons]
      exact or_left_comm
    have telescopes (base mid top : Rat) : mid - base + (top - mid) = top - base := by
      rw [Rat.add_comm, Rat.sub_eq_add_neg mid base, ← Rat.add_assoc, Rat.sub_add_cancel,
        ← Rat.sub_eq_add_neg]
    unfold potentialScore
    rw [comm, telescopes, Rat.add_comm, telescopes]

end

end OpenCausalScience.Papers.AndrewsEtAl2023
