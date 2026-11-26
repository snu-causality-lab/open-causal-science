import MecLean.Common.Graph

/-!
# Ancestors and districts of an induced ADMG

The finite graph operations used in Tian and Pearl's ancestral marginalization and generalized
Q-decomposition, R-290-L, Lemmas 3 and 4.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf
-/

open Finset

namespace Mec

variable {n : ℕ}

namespace ADMG

variable (G : ADMG n)

/-- The c-component of `v ∈ H` in `G[H]`: the vertices joined to `v` by a bidirected path inside
`H`, for `v ∈ H`. -/
def ccOf (H : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := reachSet G.bi (univ \ H) v

/-- `cc_{G[H]}`: the c-components of `G[H]` (Tian and Pearl, R-290-L). -/
def ccomps (H : Finset (Fin n)) : Finset (Finset (Fin n)) := H.image (G.ccOf H)

/-- `C` is an ancestral set in `G[C']` (R-290-L, Lemma 3):
every vertex of `C'` with a directed path inside `C'` to a vertex of `C` lies in `C`. -/
def AncestralIn (C' C : Finset (Fin n)) : Prop :=
  ∀ a ∈ C', ∀ b ∈ C, G.AncAvoid (univ \ C') a b → a ∈ C

instance (C' C : Finset (Fin n)) : Decidable (G.AncestralIn C' C) := by
  unfold AncestralIn; infer_instance

/-- `ord` lists the vertices of `H` once each, in a topological order of `G[H]`. -/
def IsTopoOrder (H : Finset (Fin n)) (ord : List (Fin n)) : Prop :=
  ord.Nodup ∧ (∀ v, v ∈ ord ↔ v ∈ H) ∧
    ∀ a ∈ H, ∀ b ∈ H, G.dir a b = true → ord.idxOf a < ord.idxOf b

instance (H : Finset (Fin n)) (ord : List (Fin n)) : Decidable (G.IsTopoOrder H ord) := by
  unfold IsTopoOrder; infer_instance

end ADMG

namespace QFac

section Graph

variable {G : ADMG n}

theorem ccOf_subset {H : Finset (Fin n)} {v : Fin n} (hv : v ∈ H) : G.ccOf H v ⊆ H := by
  intro x hx
  have hr : Reach G.bi (univ \ H) v x := reach_iff_mem_reachSet.mpr hx
  by_cases hvx : v = x
  · rw [← hvx]
    exact hv
  · have hx' := Reach.last_not_mem hr hvx
    simpa using hx'

theorem mem_ccOf_self (H : Finset (Fin n)) (v : Fin n) : v ∈ G.ccOf H v :=
  reach_iff_mem_reachSet.mp (Reach.refl v)

theorem ccomps_subset {H C : Finset (Fin n)} (hC : C ∈ G.ccomps H) : C ⊆ H := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  exact ccOf_subset hv

theorem ccOf_mem_ccomps {H : Finset (Fin n)} {v : Fin n} (hv : v ∈ H) :
    G.ccOf H v ∈ G.ccomps H :=
  Finset.mem_image_of_mem _ hv

/-- A c-component of `G[H]` contains the bidirected neighbours in `H` of its vertices. -/
theorem mem_ccomp_of_bi {H C : Finset (Fin n)} (hC : C ∈ G.ccomps H) {i j : Fin n}
    (hi : i ∈ C) (hj : j ∈ H) (hij : G.bi i j = true) : j ∈ C := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hC
  exact reach_iff_mem_reachSet.mp
    (Reach.tail (reach_iff_mem_reachSet.mpr hi) hij (by simp [hj]))

private theorem reach_bi_symm (hsym : ∀ i j, G.bi i j = G.bi j i) {H : Finset (Fin n)}
    {v w : Fin n} (hv : v ∈ H) (h : Reach G.bi (univ \ H) v w) :
    w ∈ H ∧ Reach G.bi (univ \ H) w v := by
  induction h with
  | refl => exact ⟨hv, Reach.refl v⟩
  | @tail x y _ hxy ih =>
    obtain ⟨hxH, hxv⟩ := ih
    have hyH : y ∈ H := by simpa using hxy.2
    exact ⟨hyH, Reach.head (by rw [hsym]; exact hxy.1) (by simp [hxH]) hxv⟩

theorem ccOf_eq_of_mem (hsym : ∀ i j, G.bi i j = G.bi j i) {H : Finset (Fin n)} {v w : Fin n}
    (hv : v ∈ H) (hw : w ∈ G.ccOf H v) : G.ccOf H w = G.ccOf H v := by
  have hvw : Reach G.bi (univ \ H) v w := reach_iff_mem_reachSet.mpr hw
  have hwv := (reach_bi_symm hsym hv hvw).2
  ext z
  constructor
  · intro hz
    exact reach_iff_mem_reachSet.mp (Reach.trans hvw (reach_iff_mem_reachSet.mpr hz))
  · intro hz
    exact reach_iff_mem_reachSet.mp (Reach.trans hwv (reach_iff_mem_reachSet.mpr hz))

/-- Two c-components of `G[H]` that share a vertex are equal. -/
theorem ccomps_eq_of_mem (hsym : ∀ i j, G.bi i j = G.bi j i) {H C C' : Finset (Fin n)}
    (hC : C ∈ G.ccomps H) (hC' : C' ∈ G.ccomps H) {i : Fin n} (hi : i ∈ C) (hi' : i ∈ C') :
    C = C' := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hC'
  rw [← ccOf_eq_of_mem hsym hv hi, ← ccOf_eq_of_mem hsym hv' hi']

theorem take_subset_of_topo {H : Finset (Fin n)} {ord : List (Fin n)}
    (hord : G.IsTopoOrder H ord) (k : ℕ) : (ord.take k).toFinset ⊆ H := by
  intro x hx
  exact (hord.2.1 x).mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))

/-- The first `k` vertices of a topological order of `G[H]` form an ancestral set of `G[H]`. -/
theorem take_ancestralIn {H : Finset (Fin n)} {ord : List (Fin n)}
    (hord : G.IsTopoOrder H ord) (k : ℕ) : G.AncestralIn H (ord.take k).toFinset := by
  intro a ha b hb hab
  have hbord : b ∈ ord := List.mem_of_mem_take (List.mem_toFinset.mp hb)
  have hbk : ord.idxOf b < k := (List.mem_take_iff_idxOf_lt hbord).mp (List.mem_toFinset.mp hb)
  have key : ∀ x, G.AncAvoid (univ \ H) a x → x ∈ H ∧ ord.idxOf a ≤ ord.idxOf x := by
    intro x hx
    induction hx with
    | refl => exact ⟨ha, le_rfl⟩
    | @tail y z _ hyz ih =>
      obtain ⟨hyH, hay⟩ := ih
      have hzH : z ∈ H := by simpa using hyz.2
      exact ⟨hzH, le_trans hay (le_of_lt (hord.2.2 y hyH z hzH hyz.1))⟩
  have haord : a ∈ ord := (hord.2.1 a).mpr ha
  rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt haord]
  exact lt_of_le_of_lt (key b hab).2 hbk

theorem take_succ_toFinset {ord : List (Fin n)} {k : ℕ} (hk : k < ord.length) :
    (ord.take (k + 1)).toFinset = insert ord[k] (ord.take k).toFinset := by
  ext x
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, Finset.mem_insert,
    Option.toList_some, List.mem_singleton]
  tauto

end Graph

end QFac

end Mec
