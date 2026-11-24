module
public import Std

/-! # One intact hedgelet in Figure 3(a)

[R-46](https://causalai.net/r46.pdf), Figure 3(a), Definition 5 and
Corollary 1. Use the figure as one hedge for the observational regime,
with upper vertices `X₁` and `X₂` and one root `R`. Each upper vertex has
one directed and one bidirected edge to `R`. The two upper vertices are
the two singleton hedgelets of this hedge.

The two crossing sources are fair bits. As permitted by the parity rule,
negate the first of the two frontiers in this hedge. There are no shared
sources within the one-vertex bottom. Equations (2)–(3) then give zero in
the first model and the conjunction of the two frontiers and both crossing
bits in the second model, before [R-46e](https://causalai.net/r46e.pdf)'s
independent root flip. Use flip probability `1/4`. All numerators below
have denominator 16.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.IntactHedgelet

@[expose] public section

abbrev Intervention := Bool → Option Bool

def observational : Intervention := fun _ => none

/-- Fix `X₁ = 1` and leave `X₂` as a natural response. -/
def fixFirst : Intervention := fun second => if second then none else some true

def eventNumerator (secondModel : Bool) (fixed : Intervention)
    (event : Bool → Bool → Bool → Bool) : Nat :=
  let bits := [false, true]
  (bits.flatMap fun u₁ => bits.flatMap fun u₂ => bits.map fun flip =>
    let x₁ := (fixed false).getD (!u₁)
    let x₂ := (fixed true).getD u₂
    let rawRoot := secondModel && x₁ && x₂ && u₁ && u₂
    let root := Bool.xor rawRoot flip
    if event x₁ x₂ root then (if flip then 1 else 3) else 0).sum

theorem observational_tables_equal_and_positive :
    ∀ x₁ x₂ root : Bool,
      let cell := fun a b c => a == x₁ && b == x₂ && c == root
      eventNumerator false observational cell = eventNumerator true observational cell ∧
        0 < eventNumerator false observational cell := by decide

/-- The second hedgelet is intact. The root probabilities at this intervention
are `4/16` and `6/16`, although the models agree in the supplied observational
regime for this choice of hedge. -/
theorem intact_second_hedgelet_with_unequal_root_laws :
    fixFirst true = none ∧
      eventNumerator false fixFirst (fun _ _ root => root) = 4 ∧
      eventNumerator true fixFirst (fun _ _ root => root) = 6 := by decide

end

end OpenCausalScience.Papers.LeeEtAl2019.IntactHedgelet
