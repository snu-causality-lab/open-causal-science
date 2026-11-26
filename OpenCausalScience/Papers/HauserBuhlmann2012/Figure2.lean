module
public import OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence

/-! The seven-vertex DAGs and the two regimes from Hauser and Bühlmann
(2012), Figure 2. The source labels 1 through 7 use Fin indices 0 through 6.

https://www.jmlr.org/papers/volume13/hauser12a/hauser12a.pdf#page=7 -/

namespace OpenCausalScience.Papers.HauserBuhlmann2012.Figure2

open OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.VermaPearl1990.Equivalence

@[expose] public section

abbrev v1 : Fin 7 := 0
abbrev v2 : Fin 7 := 1
abbrev v3 : Fin 7 := 2
abbrev v4 : Fin 7 := 3
abbrev v5 : Fin 7 := 4
abbrev v6 : Fin 7 := 5
abbrev v7 : Fin 7 := 6

def edgesD : List (Fin 7 × Fin 7) :=
  [(v2, v1), (v1, v5), (v2, v5), (v2, v3), (v2, v6),
    (v3, v6), (v3, v7), (v3, v4), (v4, v7), (v5, v6)]

def edgesD1 : List (Fin 7 × Fin 7) :=
  [(v1, v2), (v5, v1), (v5, v2), (v2, v3), (v2, v6),
    (v3, v6), (v3, v7), (v3, v4), (v4, v7), (v5, v6)]

def edgesD2 : List (Fin 7 × Fin 7) :=
  [(v2, v1), (v1, v5), (v2, v5), (v3, v2), (v2, v6),
    (v3, v6), (v7, v3), (v4, v3), (v7, v4), (v5, v6)]

def d : DAG 7 where
  edge u v := edgesD.contains (u, v)
  rank v := ([1, 0, 2, 3, 4, 5, 6] : List Nat)[v.val]!
  edge_increases := by decide

def d1 : DAG 7 where
  edge u v := edgesD1.contains (u, v)
  rank v := ([1, 2, 3, 4, 0, 5, 6] : List Nat)[v.val]!
  edge_increases := by decide

def d2 : DAG 7 where
  edge u v := edgesD2.contains (u, v)
  rank v := ([4, 3, 2, 1, 5, 6, 0] : List Nat)[v.val]!
  edge_increases := by decide

def target4 : Target 7 := fun v => v == v4

def regimes : List (Target 7) := [fun _ => false, target4]

theorem regimes_conservative : Conservative regimes :=
  fun _ => ⟨fun _ => false, List.mem_cons_self, rfl⟩

theorem observational_match :
    signaturesMatch d d1 = true ∧ signaturesMatch d d2 = true ∧
      signaturesMatch d1 d2 = true := by
  decide

theorem observational_dConnections :
    SameDConnections d d1 ∧ SameDConnections d d2 ∧ SameDConnections d1 d2 :=
  ⟨signaturesMatch_iff_same_dConnections.mp observational_match.1,
    signaturesMatch_iff_same_dConnections.mp observational_match.2.1,
    signaturesMatch_iff_same_dConnections.mp observational_match.2.2⟩

theorem intervention_match :
    cutSignaturesMatch regimes d d1 = true ∧ cutSignaturesMatch regimes d d2 = false := by
  decide

theorem intervention_distinguishing_edge :
    adjacentTest (cutIncoming d target4) v3 v4 = false ∧
      adjacentTest (cutIncoming d2 target4) v3 v4 = true := by
  decide

theorem figure2_partition :
    (∀ target ∈ regimes, SameDConnections (cutIncoming d target) (cutIncoming d1 target)) ∧
      ¬ (∀ target ∈ regimes, SameDConnections (cutIncoming d target) (cutIncoming d2 target)) :=
  ⟨(cutSignaturesMatch_iff regimes d d1).mp intervention_match.1,
    fun h => Bool.false_ne_true (intervention_match.2.symm.trans
      ((cutSignaturesMatch_iff regimes d d2).mpr h))⟩

end
end OpenCausalScience.Papers.HauserBuhlmann2012.Figure2
