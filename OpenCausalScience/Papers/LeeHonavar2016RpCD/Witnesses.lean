module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.Anchors
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.ExactCUT

@[expose] public section

open RelationalPaths
open ExactCUT (Realizes)

namespace RpCD

open ItemClass

structure OneCardinalitySkeleton (V : Type) where
  classOf : V → ItemClass
  edge : V → V → Prop
  symmetric : ∀ {u v}, edge u v → edge v u
  typed : ∀ {u v}, edge u v → classOf v ∈ roleNeighbors (classOf u)
  uniqueNeighbor : ∀ {u v w}, edge u v → edge u w → classOf v = classOf w → v = w

/-- Each generating label appears only once on its path, so items can be
indexed by their class within each path. Values outside that path are unused. -/
structure GeneratingPaths {V : Type} (sk : OneCardinalitySkeleton V) where
  p : ItemClass → V
  q : ItemClass → V
  typedP : ∀ c ∈ pLabels, sk.classOf (p c) = c
  typedQ : ∀ c ∈ qLabels, sk.classOf (q c) = c
  pWalk : Chain sk.edge (p S) (pLabels.tail.map p)
  qWalk : Chain sk.edge (q J) (qLabels.tail.map q)
  sameMiddle : p J = q J

def EndpointsUnshielded {V : Type} {sk : OneCardinalitySkeleton V}
    (w : GeneratingPaths sk) : Prop :=
  ∀ label ∈ shields, ¬ Realizes sk.edge sk.classOf (w.p S) (w.q R) label

theorem actual_endpoints_unshielded (code : List ItemClass) (shield : code ∈ shields) :
    ¬ Realizes (CoreEdge full) Prod.fst start (finish full) code := by
  intro realized
  have startIn : start ∈ vertices full := by decide
  have h := (mem_labels startIn).mpr realized
  have hit : matchingIsShielded full = true :=
    List.any_eq_true.mpr ⟨code, h, List.contains_iff_mem.mpr shield⟩
  exact (shielded_iff_proper full).mp hit rfl

namespace GeneratingPaths

variable {V : Type} {sk : OneCardinalitySkeleton V} (w : GeneratingPaths sk)

theorem sameA_iff_sameS : w.p A = w.q A ↔ w.p S = w.q S := by
  have ep : sk.edge (w.p S) (w.p A) := w.pWalk.1
  have eq : sk.edge (w.q S) (w.q A) := w.qWalk.2.2.2.2.2.2.1
  constructor
  · intro h
    apply sk.uniqueNeighbor (sk.symmetric ep) (h ▸ sk.symmetric eq)
    simp [w.typedP S (by decide), w.typedQ S (by decide)]
  · intro h
    apply sk.uniqueNeighbor ep (h ▸ eq)
    simp [w.typedP A (by decide), w.typedQ A (by decide)]

theorem sameR_iff_sameH : w.p R = w.q R ↔ w.p H = w.q H := by
  have ep : sk.edge (w.p H) (w.p R) := w.pWalk.2.2.1
  have eq : sk.edge (w.q H) (w.q R) := w.qWalk.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · intro h
    apply sk.uniqueNeighbor (sk.symmetric ep) (h ▸ sk.symmetric eq)
    simp [w.typedP H (by decide), w.typedQ H (by decide)]
  · intro h
    apply sk.uniqueNeighbor ep (h ▸ eq)
    simp [w.typedP R (by decide), w.typedQ R (by decide)]

theorem sameT_iff_sameW : w.p T = w.q T ↔ w.p W = w.q W := by
  have ep : sk.edge (w.p W) (w.p T) := w.pWalk.2.2.2.2.1
  have eq : sk.edge (w.q W) (w.q T) := w.qWalk.2.2.2.2.1
  constructor
  · intro h
    apply sk.uniqueNeighbor (sk.symmetric ep) (h ▸ sk.symmetric eq)
    simp [w.typedP W (by decide), w.typedQ W (by decide)]
  · intro h
    apply sk.uniqueNeighbor ep (h ▸ eq)
    simp [w.typedP T (by decide), w.typedQ T (by decide)]

def matching [DecidableEq V] : Blocks :=
  ⟨decide (w.p S = w.q S), decide (w.p H = w.q H),
   decide (w.p W = w.q W), decide (w.p U = w.q U)⟩

theorem match_iff [DecidableEq V] {c : ItemClass} (hp : c ∈ pLabels)
    (hq : c ∈ qLabels) : w.matching.shared c = true ↔ w.p c = w.q c := by
  cases c <;>
    simp [pLabels, qLabels, matching, Blocks.shared, w.sameMiddle,
      w.sameA_iff_sameS, w.sameR_iff_sameH, w.sameT_iff_sameW] at *

def embed (v : Item) : V :=
  if v.2 || !(pLabels.contains v.1) then w.q v.1 else w.p v.1

theorem embed_p {c : ItemClass} (hc : c ∈ pLabels) : w.embed (pItem c) = w.p c := by
  simp [embed, pItem, hc]

theorem embed_q [DecidableEq V] {c : ItemClass} (hc : c ∈ qLabels) :
    w.embed (qItem w.matching c) = w.q c := by
  by_cases hp : c ∈ pLabels
  · have hh := w.match_iff hp hc
    cases hm : w.matching.shared c
    · simp [embed, qItem, hp, hm]
    · simp [embed, qItem, hp, hm, hh.mp hm]
  · simp [embed, qItem, hp]

theorem typed_embed [DecidableEq V] {v : Item} (member : v ∈ vertices w.matching) :
    sk.classOf (w.embed v) = v.1 := by
  simp only [vertices, List.mem_eraseDups, List.mem_append, pItems, qItems, List.mem_map]
    at member
  rcases member with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · rw [w.embed_p hc]
    exact w.typedP c hc
  · rw [w.embed_q hc]
    exact w.typedQ c hc

theorem embed_inj [DecidableEq V] {u v : Item}
    (hu : u ∈ vertices w.matching) (hv : v ∈ vertices w.matching)
    (images : w.embed u = w.embed v) : u = v := by
  have sameClass : u.1 = v.1 := by
    rw [← w.typed_embed hu, ← w.typed_embed hv, images]
  simp only [vertices, List.mem_eraseDups, List.mem_append, pItems, qItems, List.mem_map]
    at hu hv
  rcases hu with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
    rcases hv with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · exact congrArg pItem sameClass
  · change c = d at sameClass
    subst d
    rw [w.embed_p hc, w.embed_q hd] at images
    have eq := (w.match_iff hc hd).mpr images
    simp [qItem, pItem, eq]
  · change c = d at sameClass
    subst d
    rw [w.embed_q hc, w.embed_p hd] at images
    have eq := (w.match_iff hd hc).mpr images.symm
    simp [qItem, pItem, eq]
  · exact congrArg (qItem w.matching) sameClass

private theorem map_incidence [DecidableEq V] {a b : Item}
    (ab : (a, b) ∈ walkEdges w.matching) : sk.edge (w.embed a) (w.embed b) := by
  change (a, b) ∈ (pLabels.map pItem).zip (pLabels.tail.map pItem) ++
    (qLabels.map (qItem w.matching)).zip (qLabels.tail.map (qItem w.matching)) at ab
  simp only [List.mem_append, zip_map, List.mem_map] at ab
  rcases ab with ⟨⟨c, d⟩, h, eq⟩ | ⟨⟨c, d⟩, h, eq⟩
  · obtain ⟨hc, hd⟩ := List.of_mem_zip h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    rw [w.embed_p hc, w.embed_p (List.mem_of_mem_tail hd)]
    apply chain_of_zip w.pWalk
    have h' := (List.mem_map (f := fun (a, b) => (w.p a, w.p b))).mpr ⟨(c, d), h, rfl⟩
    rw [← zip_map] at h'
    exact h'
  · obtain ⟨hc, hd⟩ := List.of_mem_zip h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    rw [w.embed_q hc, w.embed_q (List.mem_of_mem_tail hd)]
    apply chain_of_zip w.qWalk
    have h' := (List.mem_map (f := fun (a, b) => (w.q a, w.q b))).mpr ⟨(c, d), h, rfl⟩
    rw [← zip_map] at h'
    exact h'

theorem map_edge [DecidableEq V] {a b : Item} (ab : CoreEdge w.matching a b) :
    sk.edge (w.embed a) (w.embed b) := by
  rcases (core_edge_iff _ _ _).mp ab with h | h
  · exact w.map_incidence h
  · exact sk.symmetric (w.map_incidence h)

theorem start_in (m : Blocks) : start ∈ vertices m := by
  simp [vertices, pItems, pLabels, start]

theorem middle_in (m : Blocks) : middle ∈ vertices m := by
  simp [vertices, pItems, pLabels, middle]

theorem finish_in (m : Blocks) : finish m ∈ vertices m := by
  simp [vertices, qItems, qLabels, finish]

theorem embed_start : w.embed start = w.p S := w.embed_p (by decide)
theorem embed_middle : w.embed middle = w.p J := w.embed_p (by decide)
theorem embed_finish [DecidableEq V] : w.embed (finish w.matching) = w.q R :=
  w.embed_q (by decide)

theorem explicit_labels_embed [DecidableEq V] {a b : Item} {label : List ItemClass}
    (ha : a ∈ vertices w.matching) (h : label ∈ labels w.matching a b) :
    Realizes sk.edge sk.classOf (w.embed a) (w.embed b) label := by
  obtain ⟨items, path, typed⟩ := (mem_labels ha).mp h
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp path.1
  have inside := chain_mem_vertices ha path.2.2.2
  refine ⟨(a :: tail).map w.embed, path_map w.embed path ?_ (fun _ _ _ _ => w.map_edge), ?_⟩
  · exact fun u hu v hv => w.embed_inj (inside u hu) (inside v hv)
  · rw [← typed, List.map_map]
    exact List.map_congr_left (fun c hc => w.typed_embed (inside c hc))

/-- An unshielded triple with the two specified dependencies must share all blocks. -/
theorem matching_full [DecidableEq V] (unshielded : EndpointsUnshielded w) :
    w.matching = full := by
  by_cases h : w.matching = full
  · exact h
  · have shielded := (shielded_iff_proper _).mpr h
    obtain ⟨label, hLabel, hShield⟩ := List.any_eq_true.mp shielded
    have realized := w.explicit_labels_embed (start_in _) hLabel
    rw [w.embed_start, w.embed_finish] at realized
    exact (unshielded _ (List.contains_iff_mem.mp hShield) realized).elim

theorem closed [DecidableEq V] (h : w.matching = full) :
    ∀ a, a ∈ vertices w.matching → ∀ b, sk.edge (w.embed a) b →
      ∃ next, next ∈ vertices w.matching ∧ CoreEdge w.matching a next ∧ w.embed next = b := by
  intro a ha b ab
  have allowed := sk.typed ab
  rw [w.typed_embed ha] at allowed
  have sat := full_saturates_schema
  rw [← h] at sat
  have covered := List.all_eq_true.mp (List.all_eq_true.mp sat a ha)
    (sk.classOf b) allowed
  obtain ⟨next, adj, hClass⟩ := List.any_eq_true.mp covered
  have inside := (core_edge_vertices _ adj).2
  refine ⟨next, inside, adj, sk.uniqueNeighbor (w.map_edge adj) ab ?_⟩
  rw [w.typed_embed inside]
  exact beq_iff_eq.mp hClass

theorem full_labels_exact [DecidableEq V] (h : w.matching = full) {a b : Item}
    (ha : a ∈ vertices w.matching) (hb : b ∈ vertices w.matching) (label : List ItemClass) :
    Realizes sk.edge sk.classOf (w.embed a) (w.embed b) label ↔
      label ∈ labels w.matching a b := by
  constructor
  · rintro ⟨items, path, labelsEq⟩
    obtain ⟨preimage, image, path', inside⟩ := pullback_path w.embed _ (w.closed h)
      (fun _ hu _ hv => w.embed_inj hu hv) ha hb path
    refine (mem_labels ha).mpr ⟨preimage, path', ?_⟩
    rw [← labelsEq, ← image, List.map_map]
    exact List.map_congr_left (fun c hc => (w.typed_embed (inside c hc)).symm)
  · exact w.explicit_labels_embed ha

/-- For every skeleton supporting this unshielded triple, these finite path
sets are exactly the two Definition 2 middle components. -/
theorem every_witness_has_twelve_middle_paths (unshielded : EndpointsUnshielded w) :
    ∃ left right : List (List ItemClass),
      left.length = 12 ∧ right.length = 12 ∧ left.Nodup ∧ right.Nodup ∧
      (∀ l, Realizes sk.edge sk.classOf (w.p S) (w.p J) l ↔ l ∈ left) ∧
      (∀ l, Realizes sk.edge sk.classOf (w.q R) (w.p J) l ↔ l ∈ right) := by
  classical
  have h := w.matching_full unshielded
  refine ⟨labels full start middle, labels full (finish full) middle,
    full_path_counts.2.2.1, full_path_counts.2.2.2, by decide, by decide, ?_, ?_⟩
  · intro l
    have exactPaths := w.full_labels_exact h (start_in _) (middle_in _) l
    rw [w.embed_start, w.embed_middle, h] at exactPaths
    exact exactPaths
  · intro l
    have exactPaths := w.full_labels_exact h (finish_in _) (middle_in _) l
    rw [w.embed_finish, w.embed_middle, h] at exactPaths
    exact exactPaths

end GeneratingPaths

end RpCD

end
