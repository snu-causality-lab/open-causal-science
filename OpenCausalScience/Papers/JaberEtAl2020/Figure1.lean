module
public import OpenCausalScience.Papers.JaberEtAl2020.PsiAugmentation
public import OpenCausalScience.Papers.KocaogluEtAl2019.Figure2

/-! Figure 1(a–c) and Example 3 in Jaber et al. (2020). The dashed bidirected
edges are represented by distinct latent roots. -/

namespace OpenCausalScience.Papers.JaberEtAl2020.Figure1

open PsiAugmentation
open KocaogluEtAl2019.Figure2 (visibleProfile subsets)

@[expose] public section

/-- Observed vertex order X, Y, Z, W. -/
def d1Edges (u v : Fin 8) : Bool :=
  (u, v) ∈ ([(2, 0), (2, 1), (0, 1), (0, 3), (1, 3), (4, 0), (4, 3)] :
    List (Fin 8 × Fin 8))

def d1 : DAG 8 where
  edge := d1Edges
  rank v := ([2, 3, 1, 4, 0, 0, 0, 0] : List Nat)[v.val]!
  edge_increases := by decide +kernel

def d2Edges (u v : Fin 8) : Bool :=
  (u, v) ∈ ([(0, 1), (2, 1), (4, 0), (4, 2), (5, 2), (5, 3), (6, 0), (6, 3),
      (7, 3), (7, 1)] : List (Fin 8 × Fin 8))

def d2 : DAG 8 where
  edge := d2Edges
  rank v := ([1, 2, 1, 1, 0, 0, 0, 0] : List Nat)[v.val]!
  edge_increases := by decide +kernel

def d3Edges (u v : Fin 8) : Bool :=
  (u, v) ∈ ([(0, 1), (2, 3), (4, 0), (4, 2), (5, 2), (5, 1), (6, 0), (6, 3),
      (7, 3), (7, 1)] : List (Fin 8 × Fin 8))

def d3 : DAG 8 where
  edge := d3Edges
  rank v := ([1, 2, 1, 2, 0, 0, 0, 0] : List Nat)[v.val]!
  edge_increases := by decide +kernel

def i1 (regime : Fin 2) (v : Fin 8) : Option Nat :=
  if regime == 1 && v == 0 then some 1 else none

def i2 (regime : Fin 2) (v : Fin 8) : Option Nat :=
  if (regime == 0 && v == 0) || (regime == 1 && v == 3) then some 1 else none

def augmented1 : DAG 9 := psiAugmented d1 i1
def augmented2 : DAG 9 := psiAugmented d2 i2
def augmented3 : DAG 9 := psiAugmented d3 i1

theorem direct_root_edges_differ :
    augmented1.edge 8 3 = false ∧ augmented2.edge 8 3 = true := by decide +kernel

/-- The first two candidate pairs have different original mechanism maps
and still agree on every graphical query among X, Y, Z, W and F₁. -/
theorem first_two_visible_profiles_equal :
    visibleProfile augmented1 [0, 1, 2, 3, 8] = visibleProfile augmented2 [0, 1, 2, 3, 8] := by
  decide +kernel

theorem third_distinguished_by_w :
    augmented1.dSeparated 8 3 [] = some false ∧
    augmented2.dSeparated 8 3 [] = some false ∧
    augmented3.dSeparated 8 3 [] = some true := by decide +kernel

theorem first_two_root_w_inseparable :
    (subsets ([0, 1, 2] : List (Fin 9))).all
      (fun given => augmented1.dSeparated 8 3 given == some false) = true ∧
    (subsets ([0, 1, 2] : List (Fin 9))).all
      (fun given => augmented2.dSeparated 8 3 given == some false) = true := by decide +kernel

/-- Example 3 uses X, Y, Z and one latent L. Z is targeted in both
experiments but receives different mechanisms. -/
def example3 : DAG 4 where
  edge u v := (u,v) ∈ ([(0,1), (3,1), (3,2)] : List (Fin 4 × Fin 4))
  rank v := ([0, 1, 1, 0] : List Nat)[v.val]!
  edge_increases := by decide +kernel

def example3Regimes (regime : Fin 2) (v : Fin 4) : Option Nat :=
  if v = 2 then some (regime.val + 1)
  else if regime = 0 ∧ v = 0 then some 1 else none

def example3Augmented : DAG 5 := psiAugmented example3 example3Regimes

theorem example3_root_compares_shared_target :
    example3Augmented.edge 4 0 = true ∧ example3Augmented.edge 4 2 = true ∧
    example3Augmented.edge 4 1 = false := by decide +kernel

theorem example3_separations :
    example3.dSeparated 0 2 [] = some true ∧
    example3Augmented.dSeparated 0 2 [4] = some true ∧
    example3Augmented.dSeparated 4 1 [0] = some true := by decide +kernel

end
end OpenCausalScience.Papers.JaberEtAl2020.Figure1
