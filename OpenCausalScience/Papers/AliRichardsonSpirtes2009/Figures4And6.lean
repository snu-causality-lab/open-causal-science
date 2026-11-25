module
public import OpenCausalScience.Graph.MSeparation

/-! # Figure checks for Markov equivalence of ancestral graphs

The vertices of Ali, Richardson and Spirtes (2009) Figures 4 and 6 are x, q,
b, y, in that order. Figure 4 shows the need to go beyond unshielded
colliders. Figure 6 gives equivalent pairs with different discriminating
paths. Checks enumerate legal singleton queries.
Source: https://www.cmu.edu/dietrich/philosophy/docs/spirtes/AOS626.pdf
-/

namespace OpenCausalScience.AliRichardsonSpirtes2009

@[expose] public section

open MarkedGraph

namespace Figure4

def first : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 0, 1 | 1, 2 | 2, 3 => some (true, true)
  | 1, 3 => some (false, true)
  | _, _ => none

def second : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 1, 2 | 2, 3 => some (true, true)
  | 0, 1 | 1, 3 => some (false, true)
  | _, _ => none

def third : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 1, 2 => some (true, false)
  | 0, 1 | 1, 3 | 2, 3 => some (false, true)
  | _, _ => none

theorem same_adjacencies :
    ∀ x y : Fin 4, first.adjacent x y = second.adjacent x y ∧
      first.adjacent x y = third.adjacent x y := by decide

/-- The configurations are compared on pairwise distinct unshielded triples. -/
theorem same_unshielded_colliders :
    ∀ x b y : Fin 4, x ≠ b → x ≠ y → b ≠ y →
      first.adjacent x b = true → first.adjacent b y = true → first.adjacent x y = false →
      first.collider x b y = second.collider x b y ∧
      first.collider x b y = third.collider x b y := by decide

set_option maxRecDepth 4096 in
theorem first_third_witness :
    first.MSeparated 0 3 (BitVec.ofNat 4 2) ∧
      third.MConnected 0 3 (BitVec.ofNat 4 2) := by
  constructor
  · exact (first.mConnected_false_iff 0 3 _).1 (by decide)
  · exact (third.mConnected_iff 0 3 _).1 (by decide)

theorem first_third_not_equivalent : ¬ first.SameSeparations third := by
  intro equivalent
  exact (equivalent 0 3 (BitVec.ofNat 4 2) (by unfold LegalQuery; decide)).1 first_third_witness.1
    first_third_witness.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem first_second_equivalent : first.SameSeparations second := by
  apply sameSeparations_of_checks
  decide

end Figure4

namespace Figure6

def firstI : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 0, 1 | 1, 2 => some (true, true)
  | 1, 3 | 2, 3 => some (false, true)
  | 0, 2 => some (true, false)
  | _, _ => none

def secondI : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 0, 1 | 0, 2 | 1, 3 | 2, 3 => some (true, false)
  | 1, 2 => some (false, true)
  | _, _ => none

def firstII : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 0, 1 | 0, 2 | 1, 2 | 2, 3 => some (true, true)
  | 1, 3 => some (false, true)
  | _, _ => none

def secondII : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 0, 1 => some (true, false)
  | 0, 2 | 2, 3 => some (true, true)
  | 1, 2 | 1, 3 => some (false, true)
  | _, _ => none

/-- On these fixed four vertices the displayed path discriminates b when
its edges are present, x and y are nonadjacent, and q is both a collider on
the path and a parent of y. -/
def displayedPathDiscriminates (G : MarkedGraph 4) : Bool :=
  G.adjacent 0 1 && G.adjacent 1 2 && G.adjacent 2 3 &&
    !G.adjacent 0 3 && G.collider 0 1 2 && G.directed 1 3

theorem path_differs_in_both_panels :
    displayedPathDiscriminates firstI = true ∧ displayedPathDiscriminates secondI = false ∧
      displayedPathDiscriminates firstII = true ∧ displayedPathDiscriminates secondII = false := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem panel_i_equivalent : firstI.SameSeparations secondI := by
  apply sameSeparations_of_checks
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem panel_ii_equivalent : firstII.SameSeparations secondII := by
  apply sameSeparations_of_checks
  decide

end Figure6

end

end OpenCausalScience.AliRichardsonSpirtes2009
