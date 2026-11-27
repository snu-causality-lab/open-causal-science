module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.AdjacencyWitness
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.ThreeArm

/-! Lee–Honavar (2016), Lemma 1 for an arbitrary same-perspective
unrolled edge. The three-arm witness realizes the dependency and both
unrolled endpoints jointly, with unique terminal words from the base. -/

@[expose] public section

namespace RCDLight.Learning

open RCDPathValidity
open RCDLemma5 (Splice splice_iff)
open RCDThreeArm (Arm LegalArms legal_of_splice skeleton tip terminal_between_tips terminal_word_unique)

variable {K A : Type} {S : Schema K} {m : Model K A}

private theorem unrolled_arrow_ground_dependent (typed : m.typedGroundDependencies S)
    (acyclic : m.acyclic) (paths : ∀ w, m.validPath w ↔ HasTerminal S w)
    {u v : Variable K A} (validV : m.validPath v.1)
    (uType : u.1.getLast? = some (m.itemClass u.2))
    (vType : v.1.getLast? = some (m.itemClass v.2))
    (arrow : m.unrolled u v) {conditions : List (Variable K A)}
    (leftOut : u ∉ conditions) (rightOut : v ∉ conditions) :
    ¬ GroundSeparated m S u v conditions := by
  rcases u with ⟨p, x⟩
  rcases v with ⟨q, y⟩
  obtain ⟨validP, driver, trueD, joined⟩ := arrow
  have validD : HasTerminal S driver := (typed ⟨driver, x, y⟩ trueD).1
  have xNeY : x ≠ y := by
    intro same
    subst x
    exact acyclic y (.single ⟨driver, trueD⟩)
  have splice : Splice q driver p := splice_iff.mpr joined
  cases splice with
  | atPivot before overlap after pivot =>
    let rays : Arm → List K
      | .x => before.reverse
      | .y => overlap.reverse
      | .z => after
    have legal : LegalArms pivot rays S := legal_of_splice before overlap after pivot
      (has_terminal_iff.mp ((paths _).mp validV)).2 (has_terminal_iff.mp validD).2
      (has_terminal_iff.mp ((paths _).mp validP)).2
    let g := skeleton pivot rays legal
    let base : g.Item := .inl (tip rays .x)
    let xEnd : g.Item := .inl (tip rays .z)
    let yEnd : g.Item := .inl (tip rays .y)
    have uTerminal : Terminal g (before ++ pivot :: after) base xEnd := by
      simpa only [rays, List.reverse_reverse] using
        terminal_between_tips pivot rays legal .x .z (by decide)
    have vTerminal : Terminal g (before ++ pivot :: overlap.reverse) base yEnd := by
      simpa only [rays, List.reverse_reverse] using
        terminal_between_tips pivot rays legal .x .y (by decide)
    have dTerminal : Terminal g (overlap ++ pivot :: after) yEnd xEnd := by
      simpa only [rays, List.reverse_reverse] using
        terminal_between_tips pivot rays legal .y .z (by decide)
    obtain ⟨_, xPresent, _, xKind⟩ := terminal_endpoints uTerminal
    obtain ⟨_, yPresent, _, yKind⟩ := terminal_endpoints vTerminal
    let gx : GroundVertex m g :=
      ⟨xEnd, x, Option.some.inj (xKind.symm.trans uType), xPresent⟩
    let gy : GroundVertex m g :=
      ⟨yEnd, y, Option.some.inj (yKind.symm.trans vType), yPresent⟩
    have dEdge : groundArrow m g gx gy := ⟨_, trueD, dTerminal⟩
    exact isolated_ground_edge_is_dependent (g := g) (base := base) (x := gx) (y := gy)
      ⟨rfl, uTerminal⟩ ⟨rfl, vTerminal⟩ (fun same => xNeY (congrArg GroundVertex.attr same))
      (.inr dEdge)
      (fun _ alternative => terminal_word_unique pivot rays legal .x alternative uTerminal)
      (fun _ alternative => terminal_word_unique pivot rays legal .x alternative vTerminal)
      leftOut rightOut

/-- Full adjacency-faithfulness in the paper's unrolled graph. Both
inputs are legal relational variables with their indicated attribute types. -/
theorem unrolled_adjacency_faithfulness_from_ground_oracle
    (typed : m.typedGroundDependencies S) (acyclic : m.acyclic)
    (paths : ∀ w, m.validPath w ↔ HasTerminal S w) (oracle : GroundOracle m S)
    {u v : Variable K A} (validU : m.validPath u.1) (validV : m.validPath v.1)
    (uType : u.1.getLast? = some (m.itemClass u.2))
    (vType : v.1.getLast? = some (m.itemClass v.2))
    (adjacent : m.unrolledAdjacent u v) {conditions : List (Variable K A)}
    (leftOut : u ∉ conditions) (rightOut : v ∉ conditions) :
    m.independent u v conditions = false := by
  have distinct : u ≠ v := by
    intro same
    subst v
    have diagonal : m.unrolled u u := adjacent.elim id id
    exact acyclic u.2 (.single (m.unrolled_has_class_arrow diagonal))
  apply Bool.eq_false_iff.mpr
  intro independent
  have separated := (oracle u v conditions distinct leftOut rightOut).mp independent
  rcases adjacent with arrow | back
  · exact unrolled_arrow_ground_dependent typed acyclic paths validV uType vType
      arrow leftOut rightOut separated
  · exact unrolled_arrow_ground_dependent typed acyclic paths validU vType uType
      back rightOut leftOut separated.symm

end RCDLight.Learning

end
