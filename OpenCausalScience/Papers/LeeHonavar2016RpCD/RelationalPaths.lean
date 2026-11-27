module
public import Std

@[expose] public section

namespace RelationalPaths

/-- The edges between successive items, with the starting item supplied separately. -/
def Chain (edge : V → V → Prop) (start : V) : List V → Prop
  | [] => True
  | next :: rest => edge start next ∧ Chain edge next rest

instance instDecidableChain {edge : V → V → Prop} [DecidableRel edge] (start : V) (tail : List V) :
    Decidable (Chain edge start tail) :=
  match tail with
  | [] => isTrue trivial
  | next :: rest =>
    letI : Decidable (Chain edge next rest) := instDecidableChain next rest
    letI : Decidable (edge start next) := ‹DecidableRel edge› start next
    inferInstanceAs (Decidable (edge start next ∧ Chain edge next rest))

def Path (edge : V → V → Prop) (start finish : V) (items : List V) : Prop :=
  items.head? = some start ∧ items.getLast? = some finish ∧ items.Nodup ∧
    Chain edge start items.tail

theorem chain_map (f : V → W) {edge : V → V → Prop} {edge' : W → W → Prop}
    {u : V} {tail : List V} (walk : Chain edge u tail)
    (mapEdge : ∀ a ∈ u :: tail, ∀ b ∈ u :: tail, edge a b → edge' (f a) (f b)) :
    Chain edge' (f u) (tail.map f) := by
  induction tail generalizing u with
  | nil => trivial
  | cons v rest ih =>
    obtain ⟨edgeUV, suffix⟩ := walk
    refine ⟨mapEdge _ (by simp) _ (by simp) edgeUV, ih suffix ?_⟩
    intro a ha b hb ab
    exact mapEdge a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) ab

theorem path_map (f : V → W) {edge : V → V → Prop} {edge' : W → W → Prop}
    {u v : V} {items : List V} (path : Path edge u v items)
    (injective : ∀ a ∈ items, ∀ b ∈ items, f a = f b → a = b)
    (mapEdge : ∀ a ∈ items, ∀ b ∈ items, edge a b → edge' (f a) (f b)) :
    Path edge' (f u) (f v) (items.map f) := by
  obtain ⟨head, last, distinct, walk⟩ := path
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp head
  refine ⟨by simp, by simp only [List.getLast?_map, last, Option.map_some], ?_, ?_⟩
  · have pairwise : (u :: tail).Pairwise (fun a b => f a ≠ f b) :=
      List.Pairwise.imp_of_mem (fun ha hb ne eq => ne (injective _ ha _ hb eq)) distinct
    exact List.Pairwise.map f (fun _ _ ne => ne) pairwise
  · exact chain_map f walk mapEdge

theorem chain_of_zip {edge : V → V → Prop} {start : V} {tail : List V}
    (walk : Chain edge start tail) :
    ∀ a b, (a, b) ∈ (start :: tail).zip tail → edge a b := by
  induction tail generalizing start with
  | nil => simp
  | cons next rest ih =>
    intro a b h
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact walk.1
    · exact ih walk.2 a b h

theorem zip_map (f : V → W) (items tail : List V) :
    (items.map f).zip (tail.map f) =
      (items.zip tail).map (fun (a, b) => (f a, f b)) := by
  induction items generalizing tail with
  | nil => simp
  | cons a rest ih =>
    cases tail <;> simp [ih]

/-- An incidence-closed core contains every item path that starts in it. -/
theorem pullback_chain (f : V → W) {edge : V → V → Prop} {edge' : W → W → Prop}
    (core : V → Prop)
    (closed : ∀ a, core a → ∀ b, edge' (f a) b →
      ∃ next, core next ∧ edge a next ∧ f next = b)
    {u : V} {tail : List W} (inside : core u) (walk : Chain edge' (f u) tail) :
    ∃ preimage, preimage.map f = tail ∧ Chain edge u preimage ∧
      ∀ a ∈ preimage, core a := by
  induction tail generalizing u with
  | nil => exact ⟨[], rfl, trivial, by simp⟩
  | cons b rest ih =>
    obtain ⟨next, nextCore, e, rfl⟩ := closed u inside b walk.1
    obtain ⟨preimage, image, suffix, allInside⟩ := ih nextCore walk.2
    refine ⟨next :: preimage, by simp [image], ⟨e, suffix⟩, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact nextCore
    · exact allInside a ha

theorem pullback_path (f : V → W) {edge : V → V → Prop} {edge' : W → W → Prop}
    (core : V → Prop)
    (closed : ∀ a, core a → ∀ b, edge' (f a) b →
      ∃ next, core next ∧ edge a next ∧ f next = b)
    (injective : ∀ a, core a → ∀ b, core b → f a = f b → a = b)
    {u v : V} {items : List W} (fromCore : core u) (toCore : core v)
    (path : Path edge' (f u) (f v) items) :
    ∃ preimage, preimage.map f = items ∧ Path edge u v preimage ∧
      ∀ a ∈ preimage, core a := by
  obtain ⟨head, last, distinct, walk⟩ := path
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp head
  obtain ⟨preimage, image, walk', allInside⟩ := pullback_chain f core closed fromCore walk
  have image' : (u :: preimage).map f = f u :: tail := by simpa using image
  have allInside' : ∀ a ∈ u :: preimage, core a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact fromCore
    · exact allInside a ha
  refine ⟨u :: preimage, image', ⟨rfl, ?_, ?_, walk'⟩, allInside'⟩
  · rw [← image', List.getLast?_map] at last
    cases h : (u :: preimage).getLast? with
    | none => simp [h] at last
    | some w =>
      have mem : w ∈ u :: preimage := by
        obtain ⟨xs, heq⟩ := List.getLast?_eq_some_iff.mp h
        rw [heq]
        simp
      have eq := injective w (allInside' _ mem) v toCore (by simpa [h] using last)
      simp [eq]
  · rw [← image'] at distinct
    exact (List.pairwise_map.mp distinct).imp (fun ne eq => ne (congrArg f eq))

/-- Add a fresh vertex for each missing role. Each new vertex has one incident edge. -/
def addLeaves (edge : V → V → Prop) (attach : L → V) : V ⊕ L → V ⊕ L → Prop
  | .inl a, .inl b => edge a b
  | .inl a, .inr leaf => attach leaf = a
  | .inr leaf, .inl a => attach leaf = a
  | .inr _, .inr _ => False

theorem retain_core_vertices {edge : W → W → Prop} {core : W → Prop}
    {u v : W} {tail : List W} (walk : Chain edge u tail)
    (distinct : (u :: tail).Nodup) (last : (u :: tail).getLast? = some v)
    (fromCore : core u) (toCore : core v)
    (deadEnd : ∀ a b c, ¬ core b → edge a b → edge b c → a = c) :
    ∀ a ∈ u :: tail, core a := by
  induction tail generalizing u with
  | nil =>
    intro a ha
    simpa using (show a = u from List.mem_singleton.mp ha) ▸ fromCore
  | cons next rest ih =>
    have nextCore : core next := by
      apply Classical.byContradiction
      intro h
      cases rest with
      | nil =>
        have eq : next = v := by simpa using last
        exact h (eq.symm ▸ toCore)
      | cons after more =>
        have eq := deadEnd u next after h walk.1 walk.2.1
        exact (List.nodup_cons.mp distinct).1 (by simp [eq])
    have lastRest : (next :: rest).getLast? = some v := by simpa using last
    intro a mem
    rcases List.mem_cons.mp mem with eq | mem
    · exact eq ▸ fromCore
    · exact ih walk.2 (List.nodup_cons.mp distinct).2 lastRest nextCore a mem

theorem leaf_completion_creates_no_path {edge : V → V → Prop} {attach : L → V}
    {a b : V} {items : List (V ⊕ L)}
    (path : Path (addLeaves edge attach) (.inl a) (.inl b) items) :
    ∃ coreItems : List V, items = coreItems.map Sum.inl ∧ Path edge a b coreItems := by
  obtain ⟨head, last, distinct, walk⟩ := path
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp head
  let project (u : V ⊕ L) : V :=
    match u with
    | .inl x => x
    | .inr l => attach l
  let core (u : V ⊕ L) : Prop := ∃ x, u = Sum.inl x
  have allCore := retain_core_vertices (core := core) walk distinct last
      ⟨a, rfl⟩ ⟨b, rfl⟩ ?_
  · let coreItems := (Sum.inl a :: tail).map project
    have identity (u : V ⊕ L) (hu : u ∈ Sum.inl a :: tail) :
        Sum.inl (project u) = u := by
      obtain ⟨x, rfl⟩ := allCore u hu
      rfl
    refine ⟨coreItems, ?_, path_map project ⟨rfl, last, distinct, walk⟩ ?_ ?_⟩
    · dsimp [coreItems]
      rw [List.map_map]
      have eqMap : (Sum.inl a :: tail).map (Sum.inl ∘ project) =
          (Sum.inl a :: tail).map id :=
        List.map_congr_left (fun u hu => identity u hu)
      simpa using eqMap.symm
    · intro u hu v hv eq
      rw [← identity u hu, ← identity v hv, eq]
    · intro u hu v hv hEdge
      obtain ⟨x, rfl⟩ := allCore u hu
      obtain ⟨y, rfl⟩ := allCore v hv
      exact hEdge
  · intro x y z notCore x_y y_z
    cases y with
    | inl y => exact (notCore ⟨y, rfl⟩).elim
    | inr y =>
      cases x with
      | inr x => exact x_y.elim
      | inl x =>
        cases z with
        | inr z => exact y_z.elim
        | inl z => exact congrArg Sum.inl (Eq.trans (Eq.symm x_y) y_z)

/-- List all simple prefixes from the current item within the vertex budget. -/
def simplePrefixes [DecidableEq V] (neighbors : V → List V) :
    Nat → V → List V → List (List V)
  | 0, _, _ => []
  | fuel + 1, u, seen =>
    if u ∈ seen then [] else
      [u] :: (neighbors u).flatMap fun v =>
        (simplePrefixes neighbors fuel v (u :: seen)).map (u :: ·)

theorem mem_simplePrefixes [DecidableEq V] (neighbors : V → List V)
    (fuel : Nat) (u : V) (seen items : List V) :
    items ∈ simplePrefixes neighbors fuel u seen ↔
      items.head? = some u ∧ items.Nodup ∧ items.length ≤ fuel ∧
      Chain (fun a b => b ∈ neighbors a) u items.tail ∧
      (∀ v ∈ items, v ∉ seen) := by
  induction fuel generalizing u seen items with
  | zero =>
    cases items <;> simp [simplePrefixes]
  | succ fuel ih =>
    by_cases hSeen : u ∈ seen
    · simp only [simplePrefixes, ite_eq_left hSeen, List.not_mem_nil, false_iff]
      rintro ⟨head, _, _, _, unseen⟩
      obtain ⟨xs, rfl⟩ := List.head?_eq_some_iff.mp head
      exact unseen u (by simp) hSeen
    · constructor
      · intro contained
        simp only [simplePrefixes, ite_eq_right hSeen, List.mem_cons, List.mem_flatMap,
          List.mem_map] at contained
        rcases contained with eq | ⟨v, hV, tail, included, rfl⟩
        · subst items
          simp [Chain, hSeen]
        · obtain ⟨head, nd, bound, chain, unseen⟩ := (ih v (u :: seen) tail).mp included
          obtain ⟨xs, rfl⟩ := List.head?_eq_some_iff.mp head
          refine ⟨rfl, List.nodup_cons.mpr ⟨?_, nd⟩, by simpa using bound,
            ⟨hV, chain⟩, ?_⟩
          · intro hu
            exact unseen u hu (by simp)
          · intro w hw
            rcases List.mem_cons.mp hw with eq | hTail
            · exact eq ▸ hSeen
            · exact fun hs => unseen w hTail (by simp [hs])
      · rintro ⟨head, nd, bound, chain, unseen⟩
        obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp head
        cases tail with
        | nil => simp [simplePrefixes, hSeen]
        | cons v xs =>
          simp only [simplePrefixes, ite_eq_right hSeen, List.mem_cons, List.mem_flatMap,
            List.mem_map]
          refine Or.inr ⟨v, chain.1, v :: xs, (ih _ _ _).mpr ?_, rfl⟩
          refine ⟨rfl, (List.nodup_cons.mp nd).2, by simpa using bound, chain.2, ?_⟩
          intro w hw h
          rcases List.mem_cons.mp h with eq | inSeen
          · exact (List.nodup_cons.mp nd).1 (eq ▸ hw)
          · exact unseen w (List.mem_cons_of_mem _ hw) inSeen

def pathLabels [DecidableEq V] [BEq C] (neighbors : V → List V) (classOf : V → C)
    (fuel : Nat) (u v : V) : List (List C) :=
  let paths := (simplePrefixes neighbors fuel u []).filter (fun items =>
    decide (items.getLast? = some v))
  (paths.map (List.map classOf)).eraseDups

theorem mem_pathLabels [DecidableEq V] [BEq C] [LawfulBEq C]
    (neighbors : V → List V) (classOf : V → C) (fuel : Nat) (u v : V)
    (labels : List C) :
    labels ∈ pathLabels neighbors classOf fuel u v ↔
      ∃ items, Path (fun a b => b ∈ neighbors a) u v items ∧
        items.length ≤ fuel ∧ items.map classOf = labels := by
  simp only [pathLabels, List.mem_eraseDups, List.mem_map, List.mem_filter,
    decide_eq_true_eq, mem_simplePrefixes, List.not_mem_nil, not_false_eq_true, implies_true, and_true, Path]
  constructor
  · rintro ⟨items, ⟨⟨head, distinct, bound, chain⟩, last⟩, labelEq⟩
    exact ⟨items, ⟨head, last, distinct, chain⟩, bound, labelEq⟩
  · rintro ⟨items, ⟨head, last, distinct, chain⟩, bound, labelEq⟩
    exact ⟨items, ⟨⟨head, distinct, bound, chain⟩, last⟩, labelEq⟩

end RelationalPaths

end
