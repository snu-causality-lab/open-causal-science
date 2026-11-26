module
public import OpenCausalScience.Graph.MixedGraph

/-! The component scopes in Tian (2004) contain the component vertices
and their parents. Two factors communicate through a variable that is
summed out. The vertex presentation below collapses each bidirected
district and attaches each summed variable to the factors it enters.
Source: https://faculty.sites.iastate.edu/jtian/files/inline-files/uai-04.pdf
-/

namespace OpenCausalScience.Papers.Tian2004.FactorGraph

open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

abbrev Vertices (n : Nat) := Fin n → Prop

def Dir (G : MixedGraph n) (u v : Fin n) : Prop := G.edge u false v true = true

def Bidir (G : MixedGraph n) (u v : Fin n) : Prop := G.edge u true v true = true

def Within (live : Vertices n) (R : Fin n → Fin n → Prop) (u v : Fin n) : Prop :=
  live u ∧ live v ∧ R u v

def Free (Y Z : Vertices n) (u : Fin n) : Prop := ¬ Y u ∧ ¬ Z u

/-- At vertex granularity, a factor block traverses district edges and
can cross a directed edge if its parent is summed out. -/
def Bridge (G : MixedGraph n) (live Y Z : Vertices n) (u v : Fin n) : Prop :=
  Within live (fun u v => Bidir G u v ∨ (Free Y Z u ∧ Dir G u v) ∨
    (Free Y Z v ∧ Dir G v u)) u v

/-- A district term directly uses an outcome if it contains that outcome
or has it as a parent. -/
def Touches (G : MixedGraph n) (live Y : Vertices n) (v : Fin n) : Prop :=
  live v ∧ (Y v ∨ ∃ y, Y y ∧ Dir G y v)

/-- A factor block contributes to the conditional outcome when it contains
a district with an outcome in its closed parent scope. -/
def Linked (G : MixedGraph n) (live Y Z : Vertices n) (u : Fin n) : Prop :=
  ∃ v, Reach (Bridge G live Y Z) u v ∧ Touches G live Y v

theorem reach_trans {α : Type} {R : α → α → Prop} {a b c : α} (p : Reach R a b)
    (q : Reach R b c) : Reach R a c := by
  induction q with
  | refl => exact p
  | extend _ edge ih => exact .extend ih edge

theorem reach_map {α : Type} {R S : α → α → Prop} {a b : α}
    (imp : ∀ {u v}, R u v → S u v) (path : Reach R a b) : Reach S a b := by
  induction path with
  | refl => exact .refl _
  | extend _ edge ih => exact .extend ih (imp edge)

theorem reach_symm {α : Type} {R : α → α → Prop} {a b : α}
    (symm : ∀ {u v}, R u v → R v u) (path : Reach R a b) : Reach R b a := by
  induction path with
  | refl => exact .refl _
  | extend _ edge ih => exact reach_trans (.extend (.refl _) (symm edge)) ih

theorem bidir_symm {G : MixedGraph n} {u v : Fin n} (edge : Bidir G u v) : Bidir G v u :=
  (G.symmetric u true v true).symm.trans edge

theorem bridge_symm {G : MixedGraph n} {live Y Z : Vertices n} {u v : Fin n}
    (edge : Bridge G live Y Z u v) : Bridge G live Y Z v u :=
  ⟨edge.2.1, edge.1, edge.2.2.elim (fun b => Or.inl (bidir_symm b))
    (fun tail => Or.inr (Or.symm tail))⟩

theorem linked_of_steps {G : MixedGraph n} {live Y Z : Vertices n} {u v : Fin n}
    (path : Reach (Bridge G live Y Z) u v) (linked : Linked G live Y Z v) : Linked G live Y Z u := by
  obtain ⟨w, rest, hit⟩ := linked
  exact ⟨w, reach_trans path rest, hit⟩

theorem linked_iff_of_steps {G : MixedGraph n} {live Y Z : Vertices n} {u v : Fin n}
    (path : Reach (Bridge G live Y Z) u v) : Linked G live Y Z u ↔ Linked G live Y Z v :=
  ⟨linked_of_steps (reach_symm bridge_symm path), linked_of_steps path⟩

theorem linked_is_live {G : MixedGraph n} {live Y Z : Vertices n} {u : Fin n}
    (linked : Linked G live Y Z u) : live u := by
  obtain ⟨v, route, hit⟩ := linked
  have first {a b} (path : Reach (Bridge G live Y Z) a b) (hb : live b) : live a := by
    induction path with
    | refl => exact hb
    | extend _ edge ih => exact ih edge.1
  exact first route hit.1

/-- The set of vertices in a district under the stated vertex restriction. -/
def district (G : MixedGraph n) (live : Vertices n) (u : Fin n) : Vertices n :=
  fun v => live v ∧ Reach (Within live (Bidir G)) u v

/-- The closed parent scope of the district containing a vertex. -/
def scope (G : MixedGraph n) (live : Vertices n) (u v : Fin n) : Prop :=
  district G live u v ∨ ∃ w, district G live u w ∧ Dir G v w

theorem paths_in_district_are_bridges {G : MixedGraph n} {live Y Z : Vertices n}
    {u v : Fin n} (path : Reach (Within live (Bidir G)) u v) :
    Reach (Bridge G live Y Z) u v :=
  reach_map (fun e => ⟨e.1, e.2.1, Or.inl e.2.2⟩) path

end
end OpenCausalScience.Papers.Tian2004.FactorGraph
