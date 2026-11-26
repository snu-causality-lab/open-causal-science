module
public import OpenCausalScience.Papers.ElahiEtAl2024.SplitNetwork

/-! A counterexample to the adjustment condition of Elahi et al. (2024),
Lemma 2, with an empty intervention set. The adjustment variable is an
ancestor of the target only through another treatment. -/

@[expose] public section

namespace OpenCausalScience.Papers.ElahiEtAl2024.DescendantAdjustment

open SplitNetwork
open MixedGraph (Reach)

inductive Vertex
  | x1 | y1 | z | x2 | y2
  deriving DecidableEq

open Vertex

def arrow : Vertex → Vertex → Prop
  | .x1, .y1 | .y1, .z | .z, .x2 | .x2, .y2 => True
  | _, _ => False

def treatment : Vertex → Prop
  | .x1 | .x2 => True
  | _ => False

def target : Vertex → Prop
  | .y1 | .y2 => True
  | _ => False

def adjust (v : Vertex) : Prop := v = z

def observational (_v : Vertex) : Prop := False

def withoutTreatments (a b : Vertex) : Prop :=
  arrow a b ∧ ¬ treatment a ∧ ¬ treatment b

def withoutTreatmentArrows (a b : Vertex) : Prop := arrow a b ∧ ¬ treatment a

theorem target_ancestors_without_treatments (v : Vertex) :
    target v ↔ ∃ y, target y ∧ Reach withoutTreatments v y := by
  constructor
  · intro hv
    exact ⟨v, hv, .refl _⟩
  · rintro ⟨y, hy, path⟩
    cases path with
    | refl => exact hy
    | @extend a _ _ edge =>
        cases a <;> cases y <;> simp [withoutTreatments, arrow, treatment, target] at edge hy

theorem external_parents_of_target (a : Vertex) :
    treatment a ↔ ¬ target a ∧ ∃ b, target b ∧ arrow a b := by
  constructor
  · intro selected
    cases a
    · exact ⟨by simp [target], y1, trivial, trivial⟩
    · contradiction
    · contradiction
    · exact ⟨by simp [target], y2, trivial, trivial⟩
    · contradiction
  · rintro ⟨outside, b, inside, edge⟩
    cases a <;> cases b <;> simp [treatment, target, arrow] at outside inside edge ⊢

theorem adjustment_ancestry :
    Reach arrow z y2 ∧ Reach arrow x1 z :=
  ⟨.extend (.extend (.refl _) (show arrow z x2 from trivial))
    (show arrow x2 y2 from trivial),
   .extend (.extend (.refl _) (show arrow x1 y1 from trivial))
    (show arrow y1 z from trivial)⟩

private theorem no_moral_edge {a b : Vertex}
    (edge : MoralEdge withoutTreatmentArrows observational adjust a b) : False := by
  rcases edge with ⟨left, right, distinct, forward | backward | ⟨c, ac, bc⟩⟩
  · cases a <;> cases b <;>
      simp [remainingArrow, withoutTreatmentArrows, observational, arrow, treatment, adjust]
        at left right forward
  · cases a <;> cases b <;>
      simp [remainingArrow, withoutTreatmentArrows, observational, arrow, treatment, adjust]
        at left right backward
  · cases a <;> cases b <;> cases c <;>
      simp [remainingArrow, withoutTreatmentArrows, observational, arrow, treatment]
        at distinct ac bc

theorem observational_split_cut :
    IsSplitCut withoutTreatmentArrows treatment target observational adjust := by
  apply (split_cut_iff_moral_cut ..).mpr
  intro a b ha hb path
  cases path with
  | refl => cases a <;> simp [treatment, target] at ha hb
  | extend _ edge => exact no_moral_edge edge

def copyCell (parent child : Bool) : Rat :=
  if parent = child then 3 / 4 else 1 / 4

def observedCell (x1 y1 z x2 y2 : Bool) : Rat :=
  (1 / 2) * copyCell x1 y1 * copyCell y1 z * copyCell z x2 * copyCell x2 y2

def interventionCell (setX1 setX2 y1 y2 : Bool) : Rat :=
  copyCell setX1 y1 * copyCell setX2 y2

def sumBinary (cells : Bool → Rat) : Rat := cells false + cells true

theorem positive_law (x1 y1 z x2 y2 : Bool) :
    0 < observedCell x1 y1 z x2 y2 ∧ 0 < interventionCell x1 x2 y1 y2 := by
  cases x1 <;> cases y1 <;> cases z <;> cases x2 <;> cases y2 <;> decide +kernel

theorem observational_law_normalized :
    (sumBinary fun x1 => sumBinary fun y1 => sumBinary fun z =>
      sumBinary fun x2 => sumBinary fun y2 => observedCell x1 y1 z x2 y2) = 1 := by
  decide +kernel

def trueY1 (setX1 setX2 : Bool) : Rat :=
  sumBinary fun y2 => interventionCell setX1 setX2 true y2

def trueY2 (setX1 setX2 : Bool) : Rat :=
  sumBinary fun y1 => interventionCell setX1 setX2 y1 true

theorem both_treatments_are_nonredundant :
    trueY1 true true ≠ trueY1 false true ∧ trueY2 true true ≠ trueY2 true false := by
  decide +kernel

def observedZ (z : Bool) : Rat :=
  sumBinary fun x1 => sumBinary fun y1 => sumBinary fun x2 =>
    sumBinary fun y2 => observedCell x1 y1 z x2 y2

/-- Marginal of the formula in Appendix C.2 after summing out Y₂. -/
def adjustedY1 (x1 x2 : Bool) : Rat :=
  sumBinary fun z =>
    (sumBinary fun y2 => observedCell x1 true z x2 y2) /
      (sumBinary fun y1 => sumBinary fun y2 => observedCell x1 y1 z x2 y2) * observedZ z

theorem adjustment_gives_wrong_response :
    adjustedY1 true true = 7 / 10 ∧ trueY1 true true = 3 / 4 := by
  decide +kernel

end OpenCausalScience.Papers.ElahiEtAl2024.DescendantAdjustment
