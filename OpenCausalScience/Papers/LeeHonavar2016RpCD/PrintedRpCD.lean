module
public import Std

@[expose] public section

namespace RpCD

/-- Supplement Algorithm 1 lines 14 and 20 cannot hold simultaneously. -/
theorem supplement_line20_unreachable (a m ell : Nat)
    (loopRange : a ≤ m - ell + 1) : ¬ (m - ell + 1 < a) :=
  Nat.not_lt_of_ge loopRange

/-- The safe version of R1 applies only after establishing the
non-collider constraint for the specific triple. -/
theorem guarded_r1 {edge : V → V → Prop} {x y z : V} (into : edge x y)
    (adjacent : edge y z ∨ edge z y)
    (noncollider : ¬ (edge x y ∧ edge z y)) : edge y z := by
  rcases adjacent with out | into'
  · exact out
  · exact (noncollider ⟨into, into'⟩).elim

inductive StarVertex | A | B | C | D
  deriving DecidableEq

open StarVertex

def starArrow (x y : StarVertex) : Prop := x ≠ B ∧ y = B

/-- After orienting A -> B <- C, adjacency alone does not justify the
third orientation B -> D. The genuine RCM has D -> B. -/
theorem early_r1_on_star :
    starArrow A B ∧ starArrow C B ∧ ¬ (starArrow A D ∨ starArrow D A) ∧
      starArrow D B ∧ ¬ starArrow B D := by
  unfold starArrow
  decide

end RpCD

end
