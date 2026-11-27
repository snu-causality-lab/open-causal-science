module
public import OpenCausalScience.Papers.AnderssonEtAl2001.Flag
public import OpenCausalScience.Papers.Frydenberg1990.MoralSeparation

/-! The p-separation rule for an interior trail vertex in Levitz, Perlman
and Madigan (2001), §3, with the complete Table 2 from their 2003 correction.
The two incident edges are supplied by the trail. -/

namespace OpenCausalScience.Papers.LevitzEtAl2001.Table2

open ChainGraph
open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

def headNoTail (G : ChainGraph n) (u w v : Fin n) : Bool :=
  (G.arrow u w && (G.arrow v w || G.line w v)) ||
    (G.line u w && G.arrow v w)

def directedAncestor (G : ChainGraph n) (conditioning : Vertices n) (w : Fin n) : Bool :=
  (List.finRange n).any fun s => conditioning s && route G.arrow (List.finRange n) w s

def lineActivator (G : ChainGraph n) (conditioning : Vertices n) (u w v : Fin n) : Bool :=
  G.line u w && G.line w v &&
    (List.finRange n).any fun d => G.arrow d w && !conditioning d

def interiorActive (G : ChainGraph n) (conditioning : Vertices n) (u w v : Fin n) : Bool :=
  if headNoTail G u w v then directedAncestor G conditioning w
  else !conditioning w || lineActivator G conditioning u w v

theorem interior_active_iff (G : ChainGraph n) (conditioning : Vertices n) (u w v : Fin n) :
    interiorActive G conditioning u w v = true ↔
      (headNoTail G u w v = true ∧
        ∃ s, conditioning s = true ∧ Reach (fun a b => G.arrow a b = true) w s) ∨
      (headNoTail G u w v = false ∧
        (conditioning w = false ∨ (G.line u w = true ∧ G.line w v = true ∧
          ∃ d, G.arrow d w = true ∧ conditioning d = false))) := by
  cases heads : headNoTail G u w v <;>
    simp [interiorActive, heads, directedAncestor, lineActivator, List.any_eq_true,
      route_iff, and_assoc]

/-- The activator clause is absent in DAGs. The head-no-tail test then
checks an ordinary directed collider and activation uses directed ancestry. -/
theorem dag_interior_active_iff (D : DAG n) (conditioning : Vertices n) (u w v : Fin n) :
    interiorActive (.ofDAG D) conditioning u w v = true ↔
      (D.edge u w = true ∧ D.edge v w = true ∧
        ∃ s, conditioning s = true ∧ Reach (fun a b => D.edge a b = true) w s) ∨
      (¬(D.edge u w = true ∧ D.edge v w = true) ∧ conditioning w = false) := by
  rw [interior_active_iff]
  simp [headNoTail, ChainGraph.ofDAG, Bool.and_eq_false_imp, and_assoc]

open AnderssonEtAl2001.Flag (graph)

theorem flag_separation_comparison :
    (interiorActive graph (fun _ => false) 0 1 2 = false ∧
      interiorActive graph (singleton 1) 0 1 2 = true) ∧
    (Frydenberg1990.MoralSeparation.separated graph ⟨singleton 0, singleton 2, fun _ => false⟩ = false ∧
      Frydenberg1990.MoralSeparation.separated graph ⟨singleton 0, singleton 2, singleton 1⟩ = true) := by
  decide +kernel

end
end OpenCausalScience.Papers.LevitzEtAl2001.Table2
