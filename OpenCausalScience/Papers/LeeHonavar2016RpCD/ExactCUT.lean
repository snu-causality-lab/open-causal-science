module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RelationalPaths

@[expose] public section

open RelationalPaths

namespace ExactCUT

/-- A finite item path with the specified endpoint and class sequence. -/
def Realizes (edge : V → V → Prop) (classOf : V → C) (a b : V)
    (label : List C) : Prop :=
  ∃ items, Path edge a b items ∧ items.map classOf = label

theorem realization_survives_embedding {core : V → V → Prop}
    {ambient : W → W → Prop} {classOf : W → C} (f : V → W)
    (inj : ∀ a b, f a = f b → a = b)
    (mapEdge : ∀ a b, core a b → ambient (f a) (f b))
    {a b : V} {label : List C} (h : Realizes core (classOf ∘ f) a b label) :
    Realizes ambient classOf (f a) (f b) label := by
  obtain ⟨items, path, code⟩ := h
  exact ⟨items.map f, path_map f path (fun a _ b _ => inj a b)
    (fun a _ b _ => mapEdge a b), by simpa [List.map_map] using code⟩

/-- Complete a retained pair of generating paths with degree-one participants.
Every endpoint path in the result lifts to the original skeleton. -/
theorem completed_core_realizes_only_original_labels {core : V → V → Prop}
    {ambient : W → W → Prop} {classOf : W → C} {attach : L → V}
    (f : V → W) (inj : ∀ a b, f a = f b → a = b)
    (mapEdge : ∀ a b, core a b → ambient (f a) (f b))
    (leafClass : L → C)
    {a b : V} {label : List C}
    (h : Realizes (addLeaves core attach) (Sum.elim (classOf ∘ f) leafClass)
      (.inl a) (.inl b) label) :
    Realizes ambient classOf (f a) (f b) label := by
  obtain ⟨items, path, code⟩ := h
  obtain ⟨source, rfl, hSource⟩ := leaf_completion_creates_no_path path
  apply realization_survives_embedding f inj mapEdge
  exact ⟨source, hSource, by simpa [List.map_map, Function.comp_def] using code⟩

/-- Follow a specified sequence, keeping the visited items of the current branch. -/
def follows [DecidableEq V] [DecidableEq C] (neighbors : V → List V)
    (classOf : V → C) (finish : V) : List C → V → List V → Bool
  | [], current, _ => decide (current = finish)
  | c :: rest, current, seen =>
    (neighbors current).any fun next =>
      decide (classOf next = c) && decide (next ∉ current :: seen) &&
      follows neighbors classOf finish rest next (current :: seen)

theorem follows_spec [DecidableEq V] [DecidableEq C] (neighbors : V → List V)
    (classOf : V → C) (finish : V) (label : List C) (current : V) (seen : List V) :
    follows neighbors classOf finish label current seen = true ↔
      ∃ tail : List V, tail.map classOf = label ∧
        (current :: tail).getLast? = some finish ∧
        (current :: tail).Nodup ∧
        Chain (fun a b => b ∈ neighbors a) current tail ∧
        (∀ v ∈ tail, v ∉ seen) := by
  induction label generalizing current seen with
  | nil =>
    constructor
    · intro h
      have eq : current = finish := by simpa [follows] using h
      exact ⟨[], rfl, by simp [eq], by simp, trivial, by simp⟩
    · rintro ⟨tail, code, last, _, _, _⟩
      have empty : tail = [] := List.map_eq_nil_iff.mp code
      simp [empty, follows] at last ⊢
      exact last
  | cons c rest ih =>
    simp only [follows, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨next, adj, ⟨nextClass, nextNew⟩, suffix, code, last, nodup, walk, unused⟩
      refine ⟨next :: suffix, by simp [code, nextClass], by simpa using last,
        List.nodup_cons.mpr ⟨?_, nodup⟩, ⟨adj, walk⟩, ?_⟩
      · intro same
        rcases List.mem_cons.mp same with eq | h
        · exact nextNew (by simp [eq])
        · exact unused current h (by simp)
      · intro v hv already
        rcases List.mem_cons.mp hv with rfl | hs
        · exact nextNew (List.mem_cons_of_mem _ already)
        · exact unused v hs (List.mem_cons_of_mem _ already)
    · rintro ⟨tail, code, last, nodup, walk, unused⟩
      cases tail with
      | nil => contradiction
      | cons next suffix =>
        have codes := List.cons.inj code
        refine ⟨next, walk.1, ⟨codes.1, ?_⟩, suffix, codes.2,
          by simpa using last, (List.nodup_cons.mp nodup).2, walk.2, ?_⟩
        · intro old
          rcases List.mem_cons.mp old with eq | inSeen
          · exact (List.nodup_cons.mp nodup).1 (by simp [eq])
          · exact unused next (by simp) inSeen
        · intro v hv old
          rcases List.mem_cons.mp old with eq | inSeen
          · exact (List.nodup_cons.mp nodup).1 (List.mem_cons_of_mem _ (eq ▸ hv))
          · exact unused v (List.mem_cons_of_mem _ hv) inSeen

def realizesLabel [DecidableEq V] [DecidableEq C] (neighbors : V → List V)
    (classOf : V → C) (start finish : V) : List C → Bool
  | [] => false
  | c :: rest =>
    decide (classOf start = c) && follows neighbors classOf finish rest start []

theorem realizesLabel_spec [DecidableEq V] [DecidableEq C] (neighbors : V → List V)
    (classOf : V → C) (start finish : V) (label : List C) :
    realizesLabel neighbors classOf start finish label = true ↔
      Realizes (fun a b => b ∈ neighbors a) classOf start finish label := by
  cases label with
  | nil =>
    simp only [realizesLabel, Bool.false_eq_true, false_iff, Realizes]
    rintro ⟨items, path, eq⟩
    have empty : items = [] := List.map_eq_nil_iff.mp eq
    rw [empty] at path
    cases path.1
  | cons c rest =>
    simp only [realizesLabel, Bool.and_eq_true, decide_eq_true_eq, follows_spec, Realizes]
    constructor
    · rintro ⟨head, tail, code, last, nd, chain, _⟩
      exact ⟨start :: tail, ⟨rfl, last, nd, chain⟩, by simp [head, code]⟩
    · rintro ⟨items, path, code⟩
      obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp path.1
      have codes := List.cons.inj code
      exact ⟨codes.1, tail, codes.2, path.2.1, path.2.2.1, path.2.2.2, by simp⟩

/-- For a neighbor test, supply the X-Z dependency labels in the X perspective.
For a middle test, supply the labels of the Y variables in the separator. -/
theorem any_label_spec [DecidableEq V] [DecidableEq C] (neighbors : V → List V)
    (classOf : V → C) (start finish : V) (queries : List (List C)) :
    queries.any (realizesLabel neighbors classOf start finish) = true ↔
      ∃ label ∈ queries, Realizes (fun a b => b ∈ neighbors a) classOf start finish label := by
  simp only [List.any_eq_true, realizesLabel_spec]

end ExactCUT

end
