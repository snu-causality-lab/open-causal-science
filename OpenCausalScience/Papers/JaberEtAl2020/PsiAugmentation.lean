module
public import OpenCausalScience.Papers.KocaogluEtAl2019.Augmentation

/-! # Ψ-Markov augmentation with unknown targets

Definitions 1 and 4 of Jaber et al. (2020). A mechanism label is local to a
variable. `none` denotes its unchanged mechanism. Each pair of regime
positions has its own F-node, even when its difference agrees with another
pair's difference.
-/

namespace OpenCausalScience.Papers.JaberEtAl2020.PsiAugmentation

open OpenCausalScience.Papers.KocaogluEtAl2019.Augmentation

@[expose] public section

abbrev Regime (n : Nat) := Fin n → Option Nat

def changed (left right : Regime n) : Target n :=
  fun v => left v != right v

theorem changed_iff (left right : Regime n) (v : Fin n) :
    changed left right v = true ↔ left v ≠ right v := by
  simp [changed]

def comparisonPairs (r : Nat) : List (Fin r × Fin r) :=
  (List.finRange r).flatMap fun i =>
    ((List.finRange r).filter fun j => decide (i < j)).map (i, ·)

theorem mem_comparisonPairs_iff (i j : Fin r) :
    (i, j) ∈ comparisonPairs r ↔ i < j := by
  simp [comparisonPairs, List.mem_flatMap, List.mem_map]

def psiAugmented (G : DAG n) (regimes : Fin r → Regime n) :
    DAG (n + (comparisonPairs r).length) :=
  addRoots G fun index =>
    let pair := (comparisonPairs r)[index]
    changed (regimes pair.1) (regimes pair.2)

theorem psi_root_edge_iff (G : DAG n) (regimes : Fin r → Regime n)
    (index : Fin (comparisonPairs r).length) (v : Fin n) :
    (psiAugmented G regimes).edge (Fin.natAdd n index)
      (Fin.castAdd (comparisonPairs r).length v) = true ↔
        regimes (comparisonPairs r)[index].1 v ≠ regimes (comparisonPairs r)[index].2 v := by
  simp [psiAugmented, changed_iff]

end
end OpenCausalScience.Papers.JaberEtAl2020.PsiAugmentation
