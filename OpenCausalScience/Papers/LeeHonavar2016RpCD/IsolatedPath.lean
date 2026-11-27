module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.CutComplete

@[expose] public section

open RelationalPaths
open ExactCUT (Realizes)

namespace CutComplete

/-- The consecutive positions of one generating path, as an undirected item graph. -/
def lineEdge (n : Nat) (a b : Fin n) : Prop :=
  b.val = a.val + 1 ∨ a.val = b.val + 1

instance (n : Nat) : DecidableRel (lineEdge n) := by
  intro a b
  unfold lineEdge
  infer_instance

private theorem lineChain (n : Nat) :
    Chain (lineEdge (n+1)) 0 (List.finRange (n+1)).tail := by
  induction n with
  | zero => simp [List.finRange_succ, Chain]
  | succ n ih =>
    rw [List.finRange_succ]
    have rangeHead : List.finRange (n+1) = 0 :: (List.finRange (n+1)).tail := by
      conv => lhs; rw [List.finRange_succ]
      conv => rhs; rw [List.finRange_succ]
      rfl
    rw [List.tail_cons, rangeHead, List.map_cons]
    refine ⟨Or.inl rfl, chain_map Fin.succ ih ?_⟩
    intro a _ b _ adj
    unfold lineEdge at adj ⊢
    simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using adj

theorem linePath (n : Nat) :
    Path (lineEdge (n+1)) 0 (Fin.last n) (List.finRange (n+1)) :=
  ⟨by rw [List.finRange_succ]; rfl,
    by rw [List.finRange_succ_last]; exact List.getLast?_concat,
    List.nodup_finRange _, lineChain n⟩

private theorem chainTail_unique {u z : Fin n} {p q : List (Fin n)}
    (pChain : Chain (lineEdge n) u p) (qChain : Chain (lineEdge n) u q)
    (pLast : (u :: p).getLast? = some z) (qLast : (u :: q).getLast? = some z)
    (pSimple : (u :: p).Nodup) (qSimple : (u :: q).Nodup)
    (pForward : ∀ v ∈ p, v.val + 1 ≠ u.val)
    (qForward : ∀ v ∈ q, v.val + 1 ≠ u.val) : p = q := by
  induction p generalizing u q with
  | nil =>
    have endsHere : u = z := Option.some.inj pLast
    subst z
    cases q with
    | nil => rfl
    | cons next rest =>
      have last : (next :: rest).getLast? = some u := qLast
      obtain ⟨_, form⟩ := List.getLast?_eq_some_iff.mp last
      exact ((List.nodup_cons.mp qSimple).1 (by rw [form]; simp)).elim
  | cons first p ih =>
    cases q with
    | nil =>
      have endsHere : u = z := Option.some.inj qLast
      subst z
      have last : (first :: p).getLast? = some u := pLast
      obtain ⟨_, form⟩ := List.getLast?_eq_some_iff.mp last
      exact ((List.nodup_cons.mp pSimple).1 (by rw [form]; simp)).elim
    | cons next q =>
      have firstStep : first.val = u.val + 1 :=
        pChain.1.resolve_right (fun h => pForward first (by simp) h.symm)
      have nextStep : next.val = u.val + 1 :=
        qChain.1.resolve_right (fun h => qForward next (by simp) h.symm)
      have same : first = next := Fin.ext (firstStep.trans nextStep.symm)
      subst next
      apply congrArg (first :: ·)
      refine ih pChain.2 qChain.2 pLast qLast (List.nodup_cons.mp pSimple).2
        (List.nodup_cons.mp qSimple).2 ?_ ?_
      · intro v mem backward
        have eq : v = u := Fin.ext (by omega)
        exact (List.nodup_cons.mp pSimple).1 (by simp [← eq, mem])
      · intro v mem backward
        have eq : v = u := Fin.ext (by omega)
        exact (List.nodup_cons.mp qSimple).1 (by simp [← eq, mem])

theorem only_line_path {n : Nat} {z : Fin (n+1)} {p q : List (Fin (n+1))}
    (pPath : Path (lineEdge (n+1)) 0 z p) (qPath : Path (lineEdge (n+1)) 0 z q) :
    p = q := by
  obtain ⟨p, rfl⟩ := List.head?_eq_some_iff.mp pPath.1
  obtain ⟨q, rfl⟩ := List.head?_eq_some_iff.mp qPath.1
  apply congrArg (0 :: ·)
  apply chainTail_unique pPath.2.2.2 qPath.2.2.2 pPath.2.1 qPath.2.1 pPath.2.2.1 qPath.2.2.1
  all_goals simp

/-- A path label obeys the local incidence and cardinality restrictions. The two
neighbors of an internal position cannot both be its unique participant of the
same class or both belong to the same relationship class with cardinality one. -/
structure ValidPathLabel (schema : Schema C) (classes : Fin n → C) : Prop where
  typed : ∀ {a b}, b.val = a.val + 1 → TypedIncidence schema (classes a) (classes b)
  localRule : ∀ {a b c}, b.val = a.val + 1 → a.val = c.val + 1 →
    classes b = classes c → ¬ AtMostOne schema (classes a) (classes b)

theorem line_core_legal {schema : Schema C} {classes : Fin n → C}
    (valid : ValidPathLabel schema classes) : CoreLegal schema classes (lineEdge n) := by
  refine ⟨fun adj => adj.symm, ?_, ?_⟩
  · intro a b adj
    rcases adj with forward | backward
    · exact valid.typed forward
    · exact (valid.typed backward).symm
  · intro a b c ab ac classesEqual one
    rcases ab with f | f <;> rcases ac with g | g
    · exact Fin.ext (f.trans g.symm)
    · exact (valid.localRule f g classesEqual one).elim
    · exact (valid.localRule g f classesEqual.symm (classesEqual ▸ one)).elim
    · exact Fin.ext (by omega)

/-- A legal relational path has a realization whose retained endpoints admit
exactly that class-label sequence. Fresh role participants add no competing
simple path between them. -/
theorem isolate_path_label {schema : Schema C} {classes : Fin (n+1) → C}
    (valid : ValidPathLabel schema classes) :
    let classOf := completionClass schema classes (lineEdge (n+1))
    let edge := completionEdge schema classes (lineEdge (n+1))
    SkeletonLegal schema classOf edge ∧
    ∀ label, Realizes edge classOf (.inl 0) (.inl (Fin.last n)) label ↔
      label = (List.finRange (n+1)).map classes := by
  refine ⟨legal_completion (line_core_legal valid), ?_⟩
  intro label
  rw [realization_completion_iff]
  constructor
  · rintro ⟨items, path, classesEqual⟩
    rw [only_line_path path (linePath n)] at classesEqual
    exact classesEqual.symm
  · rintro rfl
    exact ⟨List.finRange _, linePath n, rfl⟩

theorem sameItem_realizes_iff {edge : V → V → Prop} {classOf : V → C} {a : V}
    {label : List C} :
    Realizes edge classOf a a label ↔ label = [classOf a] := by
  constructor
  · rintro ⟨items, path, classes⟩
    obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp path.1
    cases tail with
    | nil => exact classes.symm
    | cons next tail =>
      have last : (next :: tail).getLast? = some a := path.2.1
      obtain ⟨_, form⟩ := List.getLast?_eq_some_iff.mp last
      exact ((List.nodup_cons.mp path.2.2.1).1 (by rw [form]; simp)).elim
  · rintro rfl
    exact ⟨[a], ⟨rfl, rfl, by simp, trivial⟩, rfl⟩

private theorem chain_append_one {edge : V → V → Prop} {a b c : V} {tail : List V}
    (chain : Chain edge a tail) (last : (a :: tail).getLast? = some b) (adj : edge b c) :
    Chain edge a (tail ++ [c]) := by
  induction tail generalizing a with
  | nil =>
    have eq : a = b := Option.some.inj last
    exact ⟨eq.symm ▸ adj, trivial⟩
  | cons next rest ih =>
    exact ⟨chain.1, ih chain.2 last⟩

private theorem path_append_one {edge : V → V → Prop} {a b c : V} {items : List V}
    (path : Path edge a b items) (adj : edge b c) (fresh : c ∉ items) :
    Path edge a c (items ++ [c]) := by
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp path.1
  refine ⟨rfl, List.getLast?_concat, ?_, chain_append_one path.2.2.2 path.2.1 adj⟩
  rw [List.nodup_append]
  exact ⟨path.2.2.1, by simp, fun x mem y hy eq => fresh ((List.mem_singleton.mp hy) ▸ (eq ▸ mem))⟩

theorem reverse_path {edge : V → V → Prop}
    (symmetric : ∀ {a b}, edge a b → edge b a) {a b : V} {items : List V}
    (path : Path edge a b items) :
    Path edge b a items.reverse := by
  induction items generalizing a b with
  | nil => cases path.1
  | cons a' tail ih =>
    have eq : a' = a := Option.some.inj path.1
    subst a'
    cases tail with
    | nil =>
      have eq : a = b := Option.some.inj path.2.1
      subst b
      exact path
    | cons next rest =>
      have suffix : Path edge next b (next :: rest) :=
        ⟨rfl, path.2.1, (List.nodup_cons.mp path.2.2.1).2, path.2.2.2.2⟩
      rw [List.reverse_cons]
      apply path_append_one (ih suffix) (symmetric path.2.2.2.1)
      simpa only [List.mem_reverse] using (List.nodup_cons.mp path.2.2.1).1

theorem realizes_reverse_iff {edge : V → V → Prop} {classOf : V → C}
    (symmetric : ∀ {a b}, edge a b → edge b a) {a b : V} {label : List C} :
    Realizes edge classOf b a label.reverse ↔ Realizes edge classOf a b label := by
  have reverse {u v : V} {labels : List C} (h : Realizes edge classOf u v labels) :
      Realizes edge classOf v u labels.reverse := by
    obtain ⟨items, path, classes⟩ := h
    exact ⟨items.reverse, reverse_path symmetric path, by rw [List.map_reverse, classes]⟩
  exact ⟨fun h => by simpa using reverse h, reverse⟩

end CutComplete

end
