module
public import OpenCausalScience.Papers.WienobstEtAl2021.PotentialSink

/-! # Partial causal ordering of buckets

Perković (UAI 2020), Definition 3.3, Algorithm 1, Lemma 3.5 and
Supplement Lemmas C.1–C.2. Bucket connectivity is computed in the full
graph before intersecting the buckets with the requested vertex set.
See https://proceedings.mlr.press/v124/perkovic20a.html.
-/

namespace OpenCausalScience.Papers.Perkovic2020.PartialCausalOrder

open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.WienobstEtAl2021.PotentialSink

@[expose] public section

variable {n : Nat}

/-- Connectivity by undirected edges in the full graph. -/
inductive UndirectedWalk (P : PDAG n) : Fin n → Fin n → Prop
  | stay (u) : UndirectedWalk P u u
  | step {u v w} : UndirectedWalk P u v → P.undirected v w → UndirectedWalk P u w

namespace UndirectedWalk

variable {P : PDAG n} {u v w : Fin n}

theorem trans (left : UndirectedWalk P u v) (right : UndirectedWalk P v w) :
    UndirectedWalk P u w := by
  induction right with
  | stay => exact left
  | step _ edge ih => exact .step ih edge

theorem symm (walk : UndirectedWalk P u v) : UndirectedWalk P v u := by
  induction walk with
  | stay => exact .stay _
  | step _ edge ih => exact (UndirectedWalk.step (.stay _) (P.undirected_symm edge)).trans ih

end UndirectedWalk

/-- A finite labelling of the undirected components, including isolated vertices. -/
structure Components (P : PDAG n) where
  label : Fin n → Fin n
  same_iff : ∀ u v, label u = label v ↔ UndirectedWalk P u v

/-- Finite components can always be labelled by their first vertex in
the enumeration. This supplies the component-labelling premise. -/
theorem Components.exists_labels (P : PDAG n) : Nonempty (Components P) := by
  classical
  let connected (u : Fin n) := (List.finRange n).filter (fun v => decide (UndirectedWalk P u v))
  have mem (u v : Fin n) : v ∈ connected u ↔ UndirectedWalk P u v := by
    simp [connected, List.mem_filter]
  have nonempty (u : Fin n) : connected u ≠ [] := by
    intro empty
    have here := (mem u u).mpr (.stay _)
    simp [empty] at here
  let label (u : Fin n) := (connected u).head (nonempty u)
  have path (u : Fin n) : UndirectedWalk P u (label u) :=
    (mem u _).mp (List.head_mem _)
  refine ⟨⟨label, fun u v => ⟨?_, ?_⟩⟩⟩
  · intro same
    exact (same ▸ path u).trans (path v).symm
  · intro walk
    have equal : connected u = connected v := List.filter_congr fun w _ => by
      by_cases fromU : UndirectedWalk P u w
      · simp [fromU, walk.symm.trans fromU]
      · have fromV : ¬ UndirectedWalk P v w := fun h => fromU (walk.trans h)
        simp [fromU, fromV]
    have equalHead := congrArg List.head? equal
    rw [List.head?_eq_some_head (nonempty u), List.head?_eq_some_head (nonempty v)] at equalHead
    exact Option.some.inj equalHead

/-- The two Meek rule implications used for propagation into a bucket. -/
structure R1R2Closed (P : PDAG n) : Prop where
  r1 : ∀ u v w, P.arrow u v → P.undirected v w → u ≠ w →
    ¬ P.adjacent u w → P.arrow v w
  r2 : ∀ u v w, P.arrow u v → P.arrow v w → P.undirected u w → P.arrow u w

/-- The two implications hold at a fixed point of Meek's orientation round. -/
theorem R1R2Closed.of_meek_fixed {P : PDAG n} {G : DAG n} (ext : P.Extends G)
    (fixed : closeRound G P.arrow = P.arrow) : R1R2Closed P := by
  have unresolved {u v : Fin n} (undirected : P.undirected u v) :
      Unoriented G P.arrow u v :=
    ⟨(ext.skeleton _ _).mp undirected.1, undirected.2⟩
  have force {u v : Fin n} (proposal : Proposal G P.arrow u v) : P.arrow u v := by
    have proposed : closeRound G P.arrow u v := .inr proposal
    rw [fixed] at proposed
    exact proposed
  constructor
  · intro u v w uv vw distinct absent
    exact force (.r1 (unresolved vw) uv distinct (fun a => absent ((ext.skeleton u w).mpr a)))
  · intro u v w uv vw uw
    exact force (.r2 (unresolved uw) uv vw)

namespace Components

variable {P : PDAG n} (C : Components P)

/-- An inter-bucket arrow is inherited by every vertex of its target bucket.
The condition on buckets leaves directed edges within a bucket unrestricted. -/
theorem arrow_to_bucket (closed : R1R2Closed P)
    {u v w : Fin n} (arrow : P.arrow u v) (outside : C.label u ≠ C.label v)
    (same : C.label v = C.label w) : P.arrow u w := by
  have propagate {a b : Fin n} (h : P.arrow u a) (edge : P.undirected a b)
      (different : C.label u ≠ C.label b) : P.arrow u b := by
    have distinct : u ≠ b := fun equal => different (congrArg C.label equal)
    have adj : P.adjacent u b := by
      apply Classical.byContradiction
      intro absent
      exact edge.2.1 (closed.r1 u a b h edge distinct absent)
    by_cases forward : P.arrow u b
    · exact forward
    by_cases reverse : P.arrow b u
    · exact (edge.2.2 (closed.r2 b u a reverse h (P.undirected_symm edge))).elim
    · exact (different ((C.same_iff u b).mpr (.step (.stay u) ⟨adj, forward, reverse⟩))).elim
  have follow {x : Fin n} (walk : UndirectedWalk P v x) : P.arrow u x := by
    induction walk with
    | stay => exact arrow
    | @step a b prior edge ih =>
      have sameBucket := (C.same_iff v b).mpr (.step prior edge)
      exact propagate ih edge (fun equal => outside (equal.trans sameBucket.symm))
  exact follow ((C.same_iff v w).mp same)

def quotientArrow (c d : Fin n) : Prop :=
  c ≠ d ∧ ∃ u v, C.label u = c ∧ C.label v = d ∧ P.arrow u v

instance decidableQuotientArrow [DecidableRel P.arrow] :
    DecidableRel C.quotientArrow := fun c d => by
  unfold quotientArrow
  infer_instance

private def ranks (G : DAG n) (c : Fin n) : List Nat :=
  ((List.finRange n).filter fun u => decide (C.label u = c)).map G.rank

private theorem mem_ranks (G : DAG n) {c : Fin n} {r : Nat} :
    r ∈ C.ranks G c ↔ ∃ u, C.label u = c ∧ G.rank u = r := by
  unfold ranks
  simp [List.mem_map, List.mem_filter]

private def bucketRank (G : DAG n) (c : Fin n) : Nat :=
  (C.ranks G c).min?.getD 0

private theorem bucketRank_spec (G : DAG n) (u : Fin n) :
    (∃ w, C.label w = C.label u ∧ G.rank w = C.bucketRank G (C.label u)) ∧
      C.bucketRank G (C.label u) ≤ G.rank u := by
  have mem : G.rank u ∈ C.ranks G (C.label u) := (C.mem_ranks G).mpr ⟨u, rfl, rfl⟩
  cases found : (C.ranks G (C.label u)).min? with
  | none =>
    have empty := List.min?_eq_none_iff.mp found
    simp [empty] at mem
  | some value =>
    obtain ⟨present, lower⟩ := List.min?_eq_some_iff.mp found
    simpa [bucketRank, found] using ⟨(C.mem_ranks G).mp present, lower _ mem⟩

/-- The least extension rank in each bucket increases across each inter-bucket
arrow. This proves acyclicity of the bucket quotient. -/
theorem exists_quotient_rank {G : DAG n} (ext : P.Extends G) (closed : R1R2Closed P) :
    ∃ rank : Fin n → Nat, ∀ c d, C.quotientArrow c d → rank c < rank d := by
  refine ⟨C.bucketRank G, ?_⟩
  rintro c d ⟨different, u, v, rfl, rfl, arrow⟩
  obtain ⟨⟨w, same, attaining⟩, _⟩ := C.bucketRank_spec G v
  have enters := C.arrow_to_bucket closed arrow different same.symm
  have before := G.edge_increases u w (ext.arrows _ _ enters)
  have lower := (C.bucketRank_spec G u).2
  omega

def IsSink (c : Fin n) (remaining : List (Fin n)) : Prop :=
  ∀ d, d ∈ remaining → ¬ C.quotientArrow c d

/-- Supplement Lemma C.1. Any nonempty list of remaining bucket labels
contains one with no outgoing arrow to a remaining bucket. -/
theorem exists_sink {G : DAG n} (ext : P.Extends G) (closed : R1R2Closed P)
    {remaining : List (Fin n)} (nonempty : remaining ≠ []) :
    ∃ c, c ∈ remaining ∧ C.IsSink c remaining := by
  obtain ⟨rank, increasing⟩ := C.exists_quotient_rank ext closed
  cases maximum : (remaining.map rank).max? with
  | none => exact (nonempty (List.map_eq_nil_iff.mp (List.max?_eq_none_iff.mp maximum))).elim
  | some r =>
    obtain ⟨present, upper⟩ := List.max?_eq_some_iff.mp maximum
    obtain ⟨c, hc, rankC⟩ := List.mem_map.mp present
    exact ⟨c, hc, fun d hd arrow =>
      Nat.not_lt_of_ge (rankC ▸ upper (rank d) (List.mem_map.mpr ⟨d, hd, rfl⟩))
        (increasing c d arrow)⟩

def isSink [DecidableRel P.arrow] (c : Fin n) (remaining : List (Fin n)) : Bool :=
  remaining.all (fun d => decide (¬ C.quotientArrow c d))

private theorem isSink_iff [DecidableRel P.arrow] (c : Fin n) (remaining : List (Fin n)) :
    C.isSink c remaining = true ↔ C.IsSink c remaining := by
  simp [isSink, IsSink, List.all_eq_true]

/-- Remove a sink bucket and recurse on the remaining labels, placing the
removed bucket at the end of the causal order. The fuel bounds iterations. -/
def sinkOrder [DecidableRel P.arrow] : Nat → List (Fin n) → Option (List (Fin n))
  | 0, remaining => if remaining.isEmpty then some [] else none
  | fuel + 1, remaining =>
    if remaining.isEmpty then some []
    else do
      let sink ← remaining.find? (fun c => C.isSink c remaining)
      let prior ← sinkOrder fuel (remaining.erase sink)
      pure (prior ++ [sink])

/-- Every pass succeeds within one iteration per remaining label, with all
labels returned and every edge between distinct labels directed forward. -/
theorem sinkOrder_correct [DecidableRel P.arrow] {G : DAG n}
    (ext : P.Extends G) (closed : R1R2Closed P) (fuel : Nat) (remaining : List (Fin n))
    (enough : remaining.length ≤ fuel) :
    ∃ order, C.sinkOrder fuel remaining = some order ∧ order.Perm remaining ∧
      order.Pairwise (fun c d => ¬ C.quotientArrow d c) := by
  induction fuel generalizing remaining with
  | zero =>
    have empty : remaining = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    subst remaining
    exact ⟨[], rfl, .refl _, .nil⟩
  | succ fuel ih =>
    by_cases empty : remaining = []
    · subst remaining
      exact ⟨[], rfl, .refl _, .nil⟩
    have found : ∃ c, remaining.find? (fun c => C.isSink c remaining) = some c := by
      cases selected : remaining.find? (fun c => C.isSink c remaining) with
      | none =>
        obtain ⟨c, hc, sink⟩ := C.exists_sink ext closed empty
        exact (List.find?_eq_none.mp selected c hc ((C.isSink_iff c remaining).mpr sink)).elim
      | some c => exact ⟨c, rfl⟩
    obtain ⟨c, hc⟩ := found
    have present := List.mem_of_find?_eq_some hc
    have sink := (C.isSink_iff c remaining).mp (List.find?_some (p := fun candidate => C.isSink candidate remaining) hc)
    have reduced : (remaining.erase c).length ≤ fuel := by
      rw [List.length_erase_of_mem present]
      omega
    obtain ⟨prior, ran, perm, ordered⟩ := ih (remaining.erase c) reduced
    refine ⟨prior ++ [c], ?_, ?_, ?_⟩
    · simp [sinkOrder, List.isEmpty_eq_false_iff.mpr empty, hc, ran]
    · have atFront : (c :: prior).Perm remaining :=
        (perm.cons c).trans (List.perm_cons_erase present).symm
      exact (List.perm_append_comm (l₁ := prior) (l₂ := [c])).trans atFront
    · refine List.pairwise_append.mpr ⟨ordered, by simp, ?_⟩
      intro a ha b hb arrow
      have same : b = c := by simpa using hb
      exact sink a (List.erase_subset (perm.mem_iff.mp ha)) (same ▸ arrow)

/-- The intersection of a full-graph bucket with the requested vertices. -/
def bucket (selected : Fin n → Bool) (c : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun u => selected u && decide (C.label u = c))

theorem mem_bucket (selected : Fin n → Bool) {c u : Fin n} :
    u ∈ C.bucket selected c ↔ selected u = true ∧ C.label u = c := by
  simp [bucket, List.mem_filter]

private theorem bucket_nonempty (selected : Fin n → Bool) (c : Fin n) :
    !(C.bucket selected c).isEmpty = true ↔ ∃ u, selected u = true ∧ C.label u = c := by
  cases members : C.bucket selected c with
  | nil => simp [members, ← C.mem_bucket selected]
  | cons head tail =>
    refine ⟨fun _ => ⟨head, (C.mem_bucket selected).mp (by simp [members])⟩, fun _ => rfl⟩

/-- Algorithm 1 on the labels of the full undirected components. The result
contains only labels whose intersection with the requested set is nonempty.
Filtering after the sink scan is equivalent to skipping empty intersections
during it, since the scan uses only the full component labels. -/
def pco [DecidableRel P.arrow] (selected : Fin n → Bool) : Option (List (Fin n)) :=
  let all := (List.finRange n).filter fun c => !(C.bucket (fun _ => true) c).isEmpty
  (C.sinkOrder all.length all).map (List.filter fun c => !(C.bucket selected c).isEmpty)

/-- Lemma 3.5. The output lists each bucket of the selected set once and each
edge between different listed buckets points forward in the resulting order. -/
theorem pco_correct [DecidableRel P.arrow] {G : DAG n} (ext : P.Extends G)
    (closed : R1R2Closed P) (selected : Fin n → Bool) :
    ∃ order, C.pco selected = some order ∧
      (∀ c, c ∈ order ↔ ∃ u, selected u = true ∧ C.label u = c) ∧
      order.Pairwise (fun c d => c ≠ d ∧ ∀ u v, C.label u = c → C.label v = d →
        P.adjacent u v → P.arrow u v) := by
  let occupied (c : Fin n) := !(C.bucket (fun _ => true) c).isEmpty
  let keep (c : Fin n) := !(C.bucket selected c).isEmpty
  let all := (List.finRange n).filter occupied
  obtain ⟨order, computed, perm, ordered⟩ := C.sinkOrder_correct
    ext closed all.length all (Nat.le_refl _)
  refine ⟨order.filter keep, ?_, ?_, ?_⟩
  · change Option.map (List.filter keep) (C.sinkOrder all.length all) = _
    rw [computed]
    rfl
  · intro c
    constructor
    · intro member
      exact (C.bucket_nonempty selected c).mp (List.mem_filter.mp member).2
    · intro ⟨u, selectedU, labelU⟩
      exact List.mem_filter.mpr ⟨perm.mem_iff.mpr (List.mem_filter.mpr
        ⟨List.mem_finRange _, (C.bucket_nonempty _ _).mpr ⟨u, rfl, labelU⟩⟩),
        (C.bucket_nonempty selected c).mpr ⟨u, selectedU, labelU⟩⟩
  · have distinct : order.Nodup :=
      perm.nodup_iff.mpr ((List.nodup_finRange n).filter occupied)
    refine ((distinct.filter keep).and (ordered.filter keep)).imp ?_
    intro c d hd
    refine ⟨hd.1, ?_⟩
    intro u v hu hv adj
    by_cases arrow : P.arrow u v
    · exact arrow
    have reverse : ¬ P.arrow v u := fun back =>
      hd.2 ⟨hd.1.symm, v, u, hv, hu, back⟩
    exact (hd.1 (hu.symm.trans (((C.same_iff u v).mpr
      (.step (.stay u) ⟨adj, arrow, reverse⟩)).trans hv))).elim

end Components
namespace Figure4A

abbrev v1 : Fin 4 := 0
abbrev y1 : Fin 4 := 1
abbrev x : Fin 4 := 2
abbrev y2 : Fin 4 := 3

def arrows : List (Fin 4 × Fin 4) := [(y1, x), (y1, y2), (x, y2)]

def openEdges : List (Fin 4 × Fin 4) := [(v1, y1), (v1, x)]

def figure : PDAG 4 where
  adjacent u v := (u, v) ∈ arrows ∨ (v, u) ∈ arrows ∨
    (u, v) ∈ openEdges ∨ (v, u) ∈ openEdges
  arrow u v := (u, v) ∈ arrows
  adjacent_symm := by
    intro u v h
    rcases h with h | h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inr h))
    · exact .inr (.inr (.inl h))
  no_loops := by decide
  arrow_adjacent := Or.inl

instance : DecidableRel figure.arrow := fun _ _ => inferInstanceAs (Decidable (_ ∈ arrows))

instance : DecidableRel figure.adjacent := fun u v =>
  inferInstanceAs (Decidable ((u, v) ∈ arrows ∨ (v, u) ∈ arrows ∨
    (u, v) ∈ openEdges ∨ (v, u) ∈ openEdges))

instance : DecidableRel figure.undirected := fun u v => by
  unfold PDAG.undirected
  infer_instance

def label (u : Fin 4) : Fin 4 := if u = y2 then y2 else v1

def components : Components figure where
  label := label
  same_iff u v := by
    constructor
    · intro same
      have path (w : Fin 4) : UndirectedWalk figure w (label w) := by
        have alternatives : ∀ w : Fin 4, w = v1 ∨ w = y1 ∨ w = x ∨ w = y2 := by decide
        rcases alternatives w with rfl | rfl | rfl | rfl
        · exact .stay v1
        · exact .step (.stay y1) (show figure.undirected y1 v1 by decide)
        · exact .step (.stay x) (show figure.undirected x v1 by decide)
        · exact .stay y2
      exact (same ▸ path u).trans (path v).symm
    · intro path
      have sameEdge : ∀ a b, figure.undirected a b → label a = label b := by decide
      induction path with
      | stay => rfl
      | step _ edge ih => exact ih.trans (sameEdge _ _ edge)

theorem closed : R1R2Closed figure := by
  constructor <;> decide

theorem extendable : ∃ G, figure.Extends G := by
  have order : figure.IsEliminationOrder Fin.val := by
    refine ⟨fun {_ _} equal => Fin.ext equal, ?_⟩
    unfold PDAG.IsPotentialSink
    decide
  exact order.extend

def selected (u : Fin 4) : Bool := u != v1

/-- The full-graph bucket containing the internal arrow `Y₁ → X`
remains one bucket after omitting the middle vertex of `Y₁ – V₁ – X`. -/
theorem internal_arrow : figure.arrow y1 x ∧ components.label y1 = components.label x := by
  decide

theorem pco_figure :
    (components.pco selected).map (List.map (components.bucket selected)) =
      some [[y1, x], [y2]] := by
  decide

end Figure4A

end
end OpenCausalScience.Papers.Perkovic2020.PartialCausalOrder
