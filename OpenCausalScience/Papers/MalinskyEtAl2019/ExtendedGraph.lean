module
public import OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeGFormula
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # Deterministic treatment copies in an extended DAG

Malinsky, Shpitser and Richardson (2019), §5. The extended graph
routes a treatment's outgoing arrow through a deterministic copy.
Fixing a copy replaces only the routed input to the child. The
SCM comparison keeps the original exogenous assignment fixed.
Source: https://proceedings.mlr.press/v89/malinsky19b/malinsky19b.pdf#page=7
-/

namespace OpenCausalScience.Papers.MalinskyEtAl2019.ExtendedGraph

open ShpitserTchetgenTchetgen2016
open EdgeGFormula (Assignment EdgeSetting)
open TianPearl2003.AncestralMarginal (Setting)

@[expose] public section

variable {n k : Nat} {Ω Ξ : Type}

abbrev expandedResponse := @TianPearl2003.AncestralMarginal.evaluate

/-- The representation of each original vertex and the parent input
used for each original arrow. An unsplit arrow uses the original
parent directly. -/
structure Routing (original : DAG n) (extended : DAG k) where
  node : Fin n → Fin k
  incoming : Fin n → Fin n → Fin k
  edge_preserved : ∀ {u v}, original.edge u v = true →
    extended.edge (incoming u v) (node v) = true

/-- Replacing an incoming input with the identity copy of a parent
preserves that parent's response whenever the copy is free. -/
theorem free_copy_eq_parent (G : DAG k)
    (mechanism : Ξ → Fin k → Assignment k → Bool) (unit : Ξ) (fixed : Setting k)
    {parent copy : Fin k} (input : G.edge parent copy = true) (free : fixed copy = none)
    (identity : ∀ row, mechanism unit copy row = row parent) :
    expandedResponse G mechanism unit fixed copy = expandedResponse G mechanism unit fixed parent := by
  rw [expandedResponse, TianPearl2003.AncestralMarginal.evaluate, free, identity]
  simp [input]

/-- An actual extended DAG with identity copies and the corresponding
clamps evaluates exactly the same response on each original vertex. -/
theorem edge_response_via_node_copies (original : DAG n) (extended : DAG k)
    (route : Routing original extended)
    (mechanism : Fin n → Ω → Assignment n → Bool) (unit : Fin n → Ω)
    (expandedMechanism : Ξ → Fin k → Assignment k → Bool) (expandedUnit : Ξ)
    (edges : EdgeSetting n) (fixed : Setting k)
    (originalFree : ∀ v, fixed (route.node v) = none)
    (originalEquation : ∀ v row, expandedMechanism expandedUnit (route.node v) row =
      mechanism v (unit v) (fun u => if original.edge u v then row (route.incoming u v) else false))
    (clamps : ∀ u v, original.edge u v = true → fixed (route.incoming u v) = edges u v)
    (copyOrUnsplit : ∀ u v, original.edge u v = true →
      route.incoming u v = route.node u ∨
        (extended.edge (route.node u) (route.incoming u v) = true ∧
          ∀ row, expandedMechanism expandedUnit (route.incoming u v) row = row (route.node u)))
    (v : Fin n) :
    expandedResponse extended expandedMechanism expandedUnit fixed (route.node v) =
      EdgeGFormula.evaluate original mechanism unit edges v := by
  induction bound : original.rank v using Nat.strongRecOn generalizing v with
  | ind rank ih =>
    rw [expandedResponse, TianPearl2003.AncestralMarginal.evaluate, originalFree, originalEquation,
      EdgeGFormula.evaluate_eq_mechanism]
    apply congrArg (mechanism v (unit v))
    funext u
    by_cases arrow : original.edge u v = true
    · have incoming := route.edge_preserved arrow
      simp only [arrow, ↓reduceIte, incoming, dite_true, EdgeGFormula.parents]
      cases setting : edges u v with
      | some value =>
        have setCopy := (clamps u v arrow).trans setting
        rw [TianPearl2003.AncestralMarginal.evaluate, setCopy]
        simp
      | none =>
        have free := (clamps u v arrow).trans setting
        have reduced : expandedResponse extended expandedMechanism expandedUnit fixed (route.incoming u v) =
            expandedResponse extended expandedMechanism expandedUnit fixed (route.node u) := by
          obtain same | copy := copyOrUnsplit u v arrow
          · rw [same]
          · exact free_copy_eq_parent extended expandedMechanism expandedUnit fixed copy.1 free copy.2
        have smaller : original.rank u < rank := bound ▸ original.edge_increases _ _ arrow
        simpa [arrow] using reduced.trans (ih (original.rank u) smaller u rfl)
    · simp [EdgeGFormula.parents, arrow]

end
end OpenCausalScience.Papers.MalinskyEtAl2019.ExtendedGraph
