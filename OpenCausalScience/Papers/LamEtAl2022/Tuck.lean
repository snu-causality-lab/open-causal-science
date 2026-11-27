module
public import OpenCausalScience.Papers.Chickering1995.CoveredReversal

/-! Definition 4.1 and 4.2, and the order statement of Lemma B.8, in Lam,
Andrews and Ramsey, UAI 2022. The graph here is the DAG supplied for the
current order. Its statistical construction from the CI oracle is separate. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open OpenCausalScience
open Chickering1995.CoveredReversal

@[expose] public section

/-- The decomposition of an order around two vertices in increasing order. -/
structure OrderSplit (α : Type) where
  pre : List α
  tailVertex : α
  between : List α
  headVertex : α
  suffix : List α

namespace OrderSplit

def original (s : OrderSplit α) : List α :=
  s.pre ++ [s.tailVertex] ++ s.between ++ [s.headVertex] ++ s.suffix

/-- Move the middle ancestors of the head before both endpoints and
place the remaining middle vertices after them, stably within each group. -/
def tuck (s : OrderSplit α) (arrow : Bool) (ancestor : α → Bool) : List α :=
  if arrow then
    s.pre ++ s.between.filter ancestor ++ [s.headVertex, s.tailVertex] ++
      s.between.filter (fun v => !ancestor v) ++ s.suffix
  else s.original


def breakAt [DecidableEq α] (pivot : α) : List α → Option (List α × List α)
  | [] => none
  | a :: rest =>
    if a = pivot then some ([], rest)
    else (breakAt pivot rest).map fun (pre, post) => (a :: pre, post)

private theorem break_at_of_split [DecidableEq α] {pivot : α} {pre post : List α}
    (outside : pivot ∉ pre) : breakAt pivot (pre ++ pivot :: post) = some (pre, post) := by
  induction pre with
  | nil => simp [breakAt]
  | cons a pre ih =>
    have distinct : a ≠ pivot := fun eq => outside (by simp [eq])
    have absent : pivot ∉ pre := fun h => outside (by simp [h])
    simp [breakAt, distinct, ih absent]

private theorem break_at_reconstructs [DecidableEq α] {pivot : α} {xs pre post : List α}
    (h : breakAt pivot xs = some (pre, post)) : xs = pre ++ pivot :: post := by
  induction xs generalizing pre post with
  | nil => simp [breakAt] at h
  | cons a rest ih =>
    by_cases eq : a = pivot
    · subst a
      simp [breakAt] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp only [breakAt, ite_eq_right eq] at h
      cases sub : breakAt pivot rest with
      | none => simp [sub] at h
      | some pair =>
        rcases pair with ⟨left, right⟩
        have restEq := ih sub
        simp [sub] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [restEq]

/-- Locate the ordered endpoints and recover the three surrounding blocks. -/
def fromOrder? [DecidableEq α] (xs : List α) (j k : α) : Option (OrderSplit α) := do
  let (pre, rest) ← breakAt j xs
  let (between, post) ← breakAt k rest
  some ⟨pre, j, between, k, post⟩

theorem from_order_original [DecidableEq α] (s : OrderSplit α)
    (noTailBefore : s.tailVertex ∉ s.pre) (noHeadBetween : s.headVertex ∉ s.between) :
    fromOrder? s.original s.tailVertex s.headVertex = some s := by
  rcases s with ⟨pre, j, between, k, post⟩
  have first := break_at_of_split (post := between ++ k :: post) noTailBefore
  have second := break_at_of_split (post := post) noHeadBetween
  simp [fromOrder?, original, List.append_assoc, first, second]

theorem reconstructs_order [DecidableEq α] {xs : List α} {j k : α} {s : OrderSplit α}
    (split : fromOrder? xs j k = some s) :
    s.original = xs ∧ s.tailVertex = j ∧ s.headVertex = k := by
  unfold fromOrder? at split
  cases first : breakAt j xs with
  | none => simp [first] at split
  | some before =>
    rcases before with ⟨pre, rest⟩
    cases second : breakAt k rest with
    | none => simp [first, second] at split
    | some after =>
      rcases after with ⟨mid, post⟩
      simp [first, second] at split
      subst s
      simp [original, List.append_assoc, break_at_reconstructs first,
        break_at_reconstructs second]

theorem tuck_nonedge (s : OrderSplit α) (ancestor : α → Bool) :
    s.tuck false ancestor = s.original := rfl

private theorem partition_perm (ancestor : α → Bool) (xs : List α) :
    (xs.filter ancestor ++ xs.filter (fun v => !ancestor v)).Perm xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases h : ancestor x with
    | false =>
      simpa [h, List.filter_cons] using
        (List.perm_middle.trans (ih.cons x) :
          (xs.filter ancestor ++ x :: xs.filter (fun v => !ancestor v)).Perm (x :: xs))
    | true =>
      simpa [h, List.filter_cons] using ih.cons x

theorem tuck_perm (s : OrderSplit α) (arrow : Bool) (ancestor : α → Bool) :
    (s.tuck arrow ancestor).Perm s.original := by
  cases arrow with
  | false => exact .refl _
  | true =>
    let before := s.between.filter ancestor
    let after := s.between.filter (fun v => !ancestor v)
    have moveApart :
        (s.tailVertex :: (before ++ after) ++ [s.headVertex]).Perm
          (s.tailVertex :: before ++ s.headVertex :: after) :=
      by simpa [List.append_assoc] using
        ((List.perm_append_singleton s.headVertex after).append_left before).cons s.tailVertex
    have swapOut :
        (s.tailVertex :: before ++ s.headVertex :: after).Perm
          (before ++ s.headVertex :: s.tailVertex :: after) := by
      exact List.perm_middle.symm.trans ((List.Perm.swap _ _ _).append_left before)
    have step := (partition_perm ancestor s.between).append_right [s.headVertex]
    have move := (swapOut.symm.trans moveApart.symm).trans (step.cons s.tailVertex)
    simpa [tuck, original, List.append_assoc, before, after] using
      (move.append_right s.suffix).append_left s.pre

theorem tuck_nodup_iff (s : OrderSplit α) (arrow : Bool) (ancestor : α → Bool) :
    (s.tuck arrow ancestor).Nodup ↔ s.original.Nodup :=
  (s.tuck_perm arrow ancestor).nodup_iff

theorem tuck_of_no_middle_ancestors (s : OrderSplit α) (ancestor : α → Bool)
    (noAnc : ∀ v, v ∈ s.between → ancestor v = false) :
    s.tuck true ancestor = s.pre ++ [s.headVertex, s.tailVertex] ++ s.between ++ s.suffix := by
  have empty : s.between.filter ancestor = [] :=
    List.filter_eq_nil_iff.mpr fun v hv => by simp [noAnc v hv]
  have rest : s.between.filter (fun v => !ancestor v) = s.between :=
    List.filter_eq_self.mpr fun v hv => by simp [noAnc v hv]
  simp [tuck, empty, rest]

end OrderSplit

/-- Parent sets agree outside the two endpoints of the existing arrow. -/
structure Covered (G : DAG n) (j k : Fin n) : Prop where
  arrow : G.edge j k = true
  parents : ∀ u, u ≠ j → u ≠ k → (G.edge u j = true ↔ G.edge u k = true)

/-- There is an arrow and there is no directed path of length at least two
from its tail to its head. In a DAG, a nonempty directed walk cannot repeat
a vertex, and any such longer path has a final arrow. -/
def Singular (G : DAG n) (j k : Fin n) : Prop :=
  G.edge j k = true ∧ ∀ u, G.DirectedWalk j u → G.edge u k ≠ true

inductive Tier
  | covered
  | singular
  | all

def Eligible (tier : Tier) (G : DAG n) (j k : Fin n) : Prop :=
  match tier with
  | .covered => Covered G j k
  | .singular => Singular G j k
  | .all => G.edge j k = true

theorem covered_singular {G : DAG n} {j k : Fin n} (cov : Covered G j k) :
    Eligible .singular G j k := by
  refine ⟨cov.arrow, ?_⟩
  intro u walk last
  have forward := G.rank_lt_of_directedWalk walk
  have lastOrder := G.edge_increases _ _ last
  have uj : u ≠ j := by intro same; subst u; omega
  have uk : u ≠ k := by intro same; subst u; omega
  have back := G.edge_increases _ _ ((cov.parents u uj uk).mpr last)
  omega

theorem singular_all {G : DAG n} {j k : Fin n} (sing : Eligible .singular G j k) :
    Eligible .all G j k := sing.1

/-- Every vertex precedes its children in a complete permutation. -/
def CausalOrder (G : DAG n) (xs : List (Fin n)) : Prop :=
  xs.Pairwise fun a b => G.edge b a = false

theorem covered_parent_in_early_segment {G : DAG n} (s : OrderSplit (Fin n))
    (order : CausalOrder G s.original) (covers : ∀ u, u ∈ s.original)
    (cov : Covered G s.tailVertex s.headVertex) {u : Fin n}
    (edge : G.edge u s.headVertex = true) : u ∈ s.pre ++ [s.tailVertex] := by
  by_cases early : u ∈ s.pre ++ [s.tailVertex]
  · exact early
  have coversU := covers u
  unfold OrderSplit.original at coversU
  have rest : u ∈ s.between ++ [s.headVertex] ++ s.suffix := by
    simpa [List.append_assoc] using
      (List.mem_append.mp (show u ∈ (s.pre ++ [s.tailVertex]) ++
          (s.between ++ [s.headVertex] ++ s.suffix) by
        simpa [List.append_assoc] using coversU)).resolve_left early
  have uj : u ≠ s.tailVertex := fun eq => early (by simp [eq])
  have uk : u ≠ s.headVertex := fun eq =>
    G.no_directed_cycle u (.single (by simpa [← eq] using edge))
  have joined : CausalOrder G
      ((s.pre ++ [s.tailVertex]) ++ (s.between ++ [s.headVertex] ++ s.suffix)) := by
    simpa [CausalOrder, OrderSplit.original, List.append_assoc] using order
  have cross := (List.pairwise_append.mp joined).2.2 s.tailVertex (by simp) u rest
  rw [(cov.parents u uj uk).mpr edge] at cross
  contradiction

theorem covered_ancestor_in_early_segment {G : DAG n} (s : OrderSplit (Fin n))
    (order : CausalOrder G s.original) (covers : ∀ u, u ∈ s.original)
    (cov : Covered G s.tailVertex s.headVertex) {u : Fin n}
    (walk : G.DirectedWalk u s.headVertex) : u ∈ s.pre ++ [s.tailVertex] := by
  let early := s.pre ++ [s.tailVertex]
  let late := s.between ++ [s.headVertex] ++ s.suffix
  have joined : CausalOrder G (early ++ late) := by
    simpa [CausalOrder, OrderSplit.original, early, late, List.append_assoc] using order
  have closed (v w : Fin n) (hs : w ∈ early) (edge : G.edge v w = true) : v ∈ early := by
    have cover : v ∈ early ++ late := by
      simpa [early, late, OrderSplit.original, List.append_assoc] using covers v
    rcases List.mem_append.mp cover with he | hl
    · exact he
    · have wantsFalse := (List.pairwise_append.mp joined).2.2 _ hs _ hl
      rw [edge] at wantsFalse
      contradiction
  have walkClosed {w : Fin n} (hw : w ∈ early) (p : G.DirectedWalk u w) : u ∈ early := by
    induction p with
    | single h => exact closed _ _ hw h
    | extend _ h ih => exact ih (closed _ _ hw h)
  cases walk with
  | single h => exact covered_parent_in_early_segment s order covers cov h
  | extend p h =>
      exact walkClosed (covered_parent_in_early_segment s order covers cov h) p

/-- The ancestor block of a covered tuck is empty, so its only order
change is moving the head immediately before the tail. -/
theorem covered_tuck_order {G : DAG n} (s : OrderSplit (Fin n))
    (order : CausalOrder G s.original) (covers : ∀ u, u ∈ s.original)
    (nodup : s.original.Nodup) (cov : Covered G s.tailVertex s.headVertex)
    (ancestor : Fin n → Bool)
    (ancestorCorrect : ∀ u, ancestor u = true ↔ G.DirectedWalk u s.headVertex) :
    s.tuck (G.edge s.tailVertex s.headVertex) ancestor =
      s.pre ++ [s.headVertex, s.tailVertex] ++ s.between ++ s.suffix := by
  rw [cov.arrow]
  apply s.tuck_of_no_middle_ancestors
  intro v hv
  by_cases notAnc : ancestor v = true
  · have membership := covered_ancestor_in_early_segment s order covers cov
      ((ancestorCorrect v).mp notAnc)
    have divided : ((s.pre ++ [s.tailVertex]) ++
        (s.between ++ [s.headVertex] ++ s.suffix)).Nodup := by
      simpa [OrderSplit.original, List.append_assoc] using nodup
    have different := (List.nodup_append.mp divided).2.2 v membership v (by simp [hv])
    exact (different rfl).elim
  · exact Bool.eq_false_iff.mpr notAnc

/-- Lemma B.8(a). The covered tuck is a causal order of the graph
obtained by reversing the covered arrow. -/
theorem covered_tuck_is_causal_order {G : DAG n} (s : OrderSplit (Fin n))
    (order : CausalOrder G s.original) (covers : ∀ u, u ∈ s.original)
    (nodup : s.original.Nodup) (cov : Covered G s.tailVertex s.headVertex)
    (ancestor : Fin n → Bool)
    (ancestorCorrect : ∀ u, ancestor u = true ↔ G.DirectedWalk u s.headVertex) :
    CausalOrder (Reversal.flip G s.tailVertex s.headVertex cov.arrow cov.parents)
      (s.tuck (G.edge s.tailVertex s.headVertex) ancestor) := by
  let j := s.tailVertex
  let k := s.headVertex
  let mid := s.between
  let post := s.suffix
  let H := Reversal.flip G j k cov.arrow cov.parents
  change CausalOrder H (s.tuck (G.edge j k) ancestor)
  rw [covered_tuck_order s order covers nodup cov ancestor ancestorCorrect]
  have oldOrder : CausalOrder G (s.pre ++ j :: (mid ++ k :: post)) := by
    simpa [OrderSplit.original, j, k, mid, post, List.append_assoc] using order
  have oldNodup : (s.pre ++ j :: (mid ++ k :: post)).Nodup := by
    simpa [OrderSplit.original, j, k, mid, post, List.append_assoc] using nodup
  have newShape : s.pre ++ [s.headVertex, s.tailVertex] ++ s.between ++ s.suffix =
      s.pre ++ k :: j :: (mid ++ post) := by
    simp [j, k, mid, post, List.append_assoc]
  rw [newShape]
  have parentEarlier {v : Fin n} (edge : G.edge v k = true) : v ∈ s.pre ++ [j] :=
    covered_parent_in_early_segment s order covers cov edge
  have same {v u : Fin n} (fwd : ¬ (v = j ∧ u = k)) (rev : ¬ (v = k ∧ u = j))
      (noEdge : G.edge v u = false) : H.edge v u = false := by
    simpa [H, Reversal.flip, Reversal.flippedEdge, fwd, rev] using noEdge
  have oldParts := List.pairwise_append.mp oldOrder
  have oldTail := List.pairwise_cons.mp oldParts.2.1
  have oldBlocks := List.pairwise_append.mp oldTail.2
  have oldHead := List.pairwise_cons.mp oldBlocks.2.1
  have distinct := List.nodup_append.mp oldNodup
  have tailOutside := (List.nodup_cons.mp distinct.2.1).1
  have splitDistinct := List.nodup_append.mp (List.nodup_cons.mp distinct.2.1).2
  have headOutside := (List.nodup_cons.mp splitDistinct.2.1).1
  have headNotMid {v : Fin n} (hv : v ∈ mid) : v ≠ k :=
    splitDistinct.2.2 v hv k (by simp)
  have headNotEarly {v : Fin n} (hv : v ∈ s.pre) : v ≠ k :=
    distinct.2.2 v hv k (by simp)
  have tailNotEarly {v : Fin n} (hv : v ∈ s.pre) : v ≠ j :=
    distinct.2.2 v hv j (by simp)
  have lateNotHead {v : Fin n} (hv : v ∈ mid ++ post) : v ≠ k := by
    rcases List.mem_append.mp hv with hm | hp
    · exact headNotMid hm
    · exact fun eq => headOutside (eq ▸ hp)
  have oldLate {v : Fin n} (hv : v ∈ mid ++ post) : v ∈ mid ++ k :: post := by
    rcases List.mem_append.mp hv with hm | hp
    · exact List.mem_append_left _ hm
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  have lateNotTail {v : Fin n} (hv : v ∈ mid ++ post) : v ≠ j := by
    intro eq
    subst v
    exact tailOutside (oldLate hv)
  have headsDistinct : j ≠ k := fun eq => tailOutside (by simp [eq])
  apply List.pairwise_append.mpr
  refine ⟨oldParts.1.imp_of_mem (fun {u _} hu _ edge => same
    (fun h => headNotEarly hu h.2) (fun h => tailNotEarly hu h.2) edge), ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with eq | hv
      · subst v
        simp [H, Reversal.flip, Reversal.flippedEdge, headsDistinct]
      · apply same (fun h => lateNotTail hv h.1) (fun h => headsDistinct h.2.symm)
        rcases List.mem_append.mp hv with hm | hp
        · apply Bool.eq_false_iff.mpr
          intro last
          rcases List.mem_append.mp (parentEarlier last) with inPre | inTail
          · exact (distinct.2.2 v inPre v (by simp [hm])) rfl
          · exact lateNotTail hv (by simpa using inTail)
        · exact oldHead.1 v hp
    · apply List.pairwise_cons.mpr
      constructor
      · intro v hv
        exact same (fun h => lateNotTail hv h.1) (fun h => lateNotHead hv h.1)
          (oldTail.1 v (oldLate hv))
      · apply List.pairwise_append.mpr
        refine ⟨oldBlocks.1.imp_of_mem (fun {u _} hu _ edge => same
            (fun h => headNotMid hu h.2)
            (fun h => lateNotTail (List.mem_append_left post hu) h.2) edge),
          oldHead.2.imp_of_mem (fun {u _} hu _ edge => same
            (fun h => lateNotHead (List.mem_append_right mid hu) h.2)
            (fun h => lateNotTail (List.mem_append_right mid hu) h.2) edge), ?_⟩
        intro u hu v hv
        exact same (fun h => headNotMid hu h.2)
          (fun h => lateNotTail (List.mem_append_left post hu) h.2)
          (oldBlocks.2.2 u hu v (by simp [hv]))
  · intro u hu v hv
    have oldMembership : v ∈ j :: (mid ++ k :: post) := by
      simpa [or_comm, or_left_comm, or_assoc] using hv
    exact same (fun h => headNotEarly hu h.2) (fun h => tailNotEarly hu h.2)
      (oldParts.2.2 u hu v oldMembership)

end

end OpenCausalScience.Papers.LamEtAl2022
