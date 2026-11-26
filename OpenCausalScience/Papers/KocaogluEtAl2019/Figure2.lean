module
public import OpenCausalScience.Papers.KocaogluEtAl2019.Augmentation
public import OpenCausalScience.Graph.DSeparation

/-! Figure 2(a,b) of Kocaoglu et al. (2019), with dashed bidirected
edges represented by explicit latent roots. The observed vertex order is
X, W, Z, Y. The two unused latent names let us give both DAGs the same type. -/

namespace OpenCausalScience.Papers.KocaogluEtAl2019.Figure2

open Augmentation

@[expose] public section

def leftEdges (u v : Fin 8) : Bool :=
  (u, v) ∈ ([(0, 1), (2, 3), (1, 3), (4, 0), (4, 2), (5, 2), (5, 3)] :
      List (Fin 8 × Fin 8))

def left : DAG 8 where
  edge := leftEdges
  rank v := ([2, 3, 1, 4, 0, 0, 0, 0] : List Nat)[v.val]!
  edge_increases := by decide +kernel

def rightEdges (u v : Fin 8) : Bool :=
  (u, v) ∈ ([(2, 0), (0, 3), (2, 3), (0, 1), (6, 0), (6, 3), (7, 1), (7, 3)] :
      List (Fin 8 × Fin 8))

def right : DAG 8 where
  edge := rightEdges
  rank v := ([2, 3, 1, 3, 0, 0, 0, 0] : List Nat)[v.val]!
  edge_increases := by decide +kernel

/-- The target family is the observational regime and an intervention on X.
The drawing suppresses the isolated root from the empty self-comparison. -/
def settings : List (Target 8) := [fun _ => false, (· == 0)]

theorem figured_differences : differences settings = [[], [0]] := by decide +kernel

def leftAug : DAG 9 := addRoots left (fun (_ : Fin 1) v => v == 0)
def rightAug : DAG 9 := addRoots right (fun (_ : Fin 1) v => v == 0)

def subsets : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
    let rest := subsets tail
    rest ++ rest.map (head :: ·)

/-- Complete singleton d-separation answers among visible vertices. -/
def visibleProfile (G : DAG n) (visible : List (Fin n)) : List (Option Bool) :=
  visible.flatMap fun u => visible.flatMap fun v =>
    if u == v then [] else
      (subsets (visible.filter fun a => a != u && a != v)).map (G.dSeparated u v)

/-- The two augmented DAGs agree on all 160 visible d-separation queries.
This is the graphical comparison in Figure 2(c,d) before projection. -/
theorem visible_profiles_equal :
    visibleProfile leftAug [0, 1, 2, 3, 8] = visibleProfile rightAug [0, 1, 2, 3, 8] := by
  decide +kernel

theorem root_outcome_inseparable :
    (subsets ([0, 1, 2] : List (Fin 9))).all
      (fun given => leftAug.dSeparated 8 3 given == some false) = true ∧
    (subsets ([0, 1, 2] : List (Fin 9))).all
      (fun given => rightAug.dSeparated 8 3 given == some false) = true := by decide +kernel

end
end OpenCausalScience.Papers.KocaogluEtAl2019.Figure2
