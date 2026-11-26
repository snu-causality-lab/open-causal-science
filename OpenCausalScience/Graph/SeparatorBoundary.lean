module
public import OpenCausalScience.Graph.MixedSeparationExecutable

/-! # Boundary search for constrained separators

The boundary procedure works on an undirected graph. A blocked vertex can
be reached but cannot be expanded. The procedure starts by blocking all
allowed vertices, retains the required vertices and the left boundary,
then prunes again from the right. The correctness theorem is relative to
the given adjacency. A graph reduction supplies that adjacency when the
original separator problem uses directed or mixed edges.
-/

namespace OpenCausalScience.SeparatorBoundary

open OpenCausalScience.MixedGraph (exploreStack mem_exploreStack_iff)

@[expose] public section

variable {α : Type}

/-- The last vertex may be blocked. Every vertex traversed before it must be open. -/
inductive Reach (edge : α → α → Prop) (source blocked : α → Prop) : α → Prop
  | seed {v} : source v → Reach edge source blocked v
  | step {u v} : Reach edge source blocked u → ¬ blocked u → edge u v →
      Reach edge source blocked v

variable {edge : α → α → Prop} {X Y I Z W : α → Prop}

theorem Reach.map {edge' : α → α → Prop} {X' Z' : α → Prop} {v : α}
    (reach : Reach edge X Z v) (mapSeed : ∀ u, X u → Reach edge' X' Z' u)
    (edgeSub : ∀ u w, edge u w → edge' u w) (blockSub : ∀ u, Z' u → Z u) :
    Reach edge' X' Z' v := by
  induction reach with
  | seed start => exact mapSeed _ start
  | step _ openVertex next ih => exact .step ih (fun h => openVertex (blockSub _ h)) (edgeSub _ _ next)

private theorem Reach.reverse {v : α} (reach : Reach edge X Z v)
    (symmetric : ∀ u w, edge u w → edge w u) (openLast : ¬ Z v) :
    ∃ u, X u ∧ Reach edge (fun w => w = v) Z u := by
  induction reach with
  | seed start => exact ⟨_, start, .seed rfl⟩
  | step before openVertex next ih =>
    obtain ⟨u, start, rev⟩ := ih openVertex
    exact ⟨u, start, rev.map
      (fun w same => same.symm ▸ .step (.seed rfl) openLast (symmetric _ _ next))
      (fun _ _ h => h) (fun _ h => h)⟩

def keepReached (edge : α → α → Prop) (X I Z : α → Prop) (v : α) : Prop :=
  (Z v ∧ Reach edge X Z v) ∨ I v

/-- Removing blockers unreachable from the source preserves the entire
reachable set from that source, including its blocked boundary. -/
theorem reach_keep_reached_iff (required : ∀ v, I v → Z v) (v : α) :
    Reach edge X (keepReached edge X I Z) v ↔ Reach edge X Z v := by
  constructor
  · intro reach
    induction reach with
    | seed hx => exact .seed hx
    | step _ openVertex next ih =>
      exact .step ih (fun blocked => openVertex (.inl ⟨blocked, ih⟩)) next
  · intro reach
    exact reach.map (fun _ h => .seed h) (fun _ _ h => h)
      (fun u h => h.elim And.left (required u))

def Separated (edge : α → α → Prop) (X Y Z : α → Prop) : Prop :=
  ∀ v, Y v → ¬ Reach edge X Z v

private theorem separated_swap (symmetric : ∀ u v, edge u v → edge v u)
    (leftOutside : ∀ v, X v → ¬ Z v) (separated : Separated edge X Y Z) :
    Separated edge Y X Z := by
  intro v hx reach
  have openLast := leftOutside v hx
  obtain ⟨u, hy, rev⟩ := reach.reverse symmetric openLast
  exact separated u hy (rev.map (fun w eq => eq.symm ▸ .seed hx)
    (fun _ _ h => h) (fun _ h => h))

theorem separating_prune {edge : α → α → Prop} {X Y I Z : α → Prop}
    (symmetric : ∀ u v, edge u v → edge v u)
    (required : ∀ v, I v → Z v)
    (leftOutside : ∀ v, X v → ¬ Z v)
    (rightOutside : ∀ v, Y v → ¬ Z v)
    (separated : Separated edge X Y Z) :
    let first := keepReached edge X I Z
    let result := keepReached edge Y I first
    Separated edge X Y result ∧ (∀ v, I v → result v) ∧ (∀ v, result v → Z v) ∧
      ∀ v, result v → ¬ I v → Reach edge X result v ∧ Reach edge Y result v := by
  dsimp only
  let first := keepReached edge X I Z
  let result := keepReached edge Y I first
  have firstSub : ∀ v, first v → Z v := fun v h => h.elim And.left (required v)
  have secondSub : ∀ v, result v → first v := fun _ h => h.elim And.left Or.inr
  have firstSep : Separated edge X Y first := fun v hy route =>
    separated v hy ((reach_keep_reached_iff required v).mp route)
  have firstReverse := separated_swap symmetric (fun v hx h => leftOutside v hx (firstSub v h)) firstSep
  have secondReverse : Separated edge Y X result := fun v hx route =>
    firstReverse v hx ((reach_keep_reached_iff (fun _ h => Or.inr h) v).mp route)
  have secondSep : Separated edge X Y result :=
    separated_swap symmetric (fun v hy h => rightOutside v hy (firstSub v (secondSub v h))) secondReverse
  refine ⟨secondSep, fun _ h => .inr h, fun v h => firstSub v (secondSub v h), ?_⟩
  intro v chosen optional
  obtain ⟨inFirst, fromRight⟩ := chosen.resolve_right optional
  have fromLeft := (inFirst.resolve_right optional).2
  have leftFirst := (reach_keep_reached_iff required v).mpr fromLeft
  exact ⟨leftFirst.map (fun _ h => .seed h) (fun _ _ h => h) secondSub,
    (reach_keep_reached_iff (fun _ h => Or.inr h) v).mpr fromRight⟩

theorem necessary_blocker {v : α}
    (symmetric : ∀ u w, edge u w → edge w u)
    (fromLeft : Reach edge X Z v) (fromRight : Reach edge Y Z v)
    (subset : ∀ x, W x → Z x) (omitted : ¬ W v) :
    ¬ Separated edge X Y W := by
  intro separated
  have left' := fromLeft.map (fun _ h => Reach.seed h) (fun _ _ h => h) subset
  have right' := fromRight.map (fun _ h => Reach.seed h) (fun _ _ h => h) subset
  obtain ⟨y, hy, rev⟩ := right'.reverse symmetric omitted
  exact separated y hy (rev.map (fun w eq => eq.symm ▸ left') (fun _ _ h => h) (fun _ h => h))

def IsSeparator (edge : α → α → Prop) (left right required allowed chosen : α → Prop) :
    Prop :=
  (∀ v, required v → chosen v) ∧ (∀ v, chosen v → allowed v) ∧
    Separated edge left right chosen

def IsMinimalSeparator (edge : α → α → Prop)
    (left right required allowed chosen : α → Prop) : Prop :=
  IsSeparator edge left right required allowed chosen ∧
    ∀ other, IsSeparator edge left right required allowed other →
      (∀ v, other v → chosen v) → ∀ v, chosen v → other v

/-- A valid separator is minimal relative to the required set exactly when
each optional blocker is reached from both sides. -/
theorem is_minimal_separator_iff_boundary {R : α → Prop}
    (symmetric : ∀ u v, edge u v → edge v u)
    (leftOutside : ∀ v, X v → ¬ Z v) (rightOutside : ∀ v, Y v → ¬ Z v)
    (separator : IsSeparator edge X Y I R Z) :
    IsMinimalSeparator edge X Y I R Z ↔
      ∀ v, Z v → ¬ I v → Reach edge X Z v ∧ Reach edge Y Z v := by
  constructor
  · intro minimal
    let pruned := keepReached edge Y I (keepReached edge X I Z)
    obtain ⟨separates, required, within, witnesses⟩ :=
      separating_prune symmetric separator.1 leftOutside rightOutside separator.2.2
    have retained : ∀ v, Z v → pruned v :=
      minimal.2 pruned ⟨required, fun v h => separator.2.1 v (within v h), separates⟩ within
    intro v chosen optional
    obtain ⟨fromLeft, fromRight⟩ := witnesses v (retained v chosen) optional
    exact ⟨fromLeft.map (fun _ h => .seed h) (fun _ _ h => h) retained,
      fromRight.map (fun _ h => .seed h) (fun _ _ h => h) retained⟩
  · intro witnesses
    refine ⟨separator, ?_⟩
    intro other permitted subset v chosen
    by_cases mandatory : I v
    · exact permitted.1 v mandatory
    by_cases retained : other v
    · exact retained
    · obtain ⟨fromLeft, fromRight⟩ := witnesses v chosen mandatory
      exact (necessary_blocker symmetric fromLeft fromRight subset retained permitted.2.2).elim

variable {n : Nat}

def nextVertices (adjacent : Fin n → Fin n → Bool) (blocked : Fin n → Bool)
    (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun w => !blocked v && adjacent v w

private theorem mem_next_vertices_iff (adjacent : Fin n → Fin n → Bool)
    (blocked : Fin n → Bool) (u v : Fin n) :
    v ∈ nextVertices adjacent blocked u ↔ blocked u ≠ true ∧ adjacent u v = true := by
  cases h : blocked u <;> simp [nextVertices, h]

def boundaryVertices (adjacent : Fin n → Fin n → Bool) (source blocked : Fin n → Bool) :
    List (Fin n) :=
  exploreStack (nextVertices adjacent blocked) (List.finRange n) ((List.finRange n).filter source)

theorem mem_boundary_vertices_iff (adjacent : Fin n → Fin n → Bool)
    (source blocked : Fin n → Bool) (v : Fin n) :
    v ∈ boundaryVertices adjacent source blocked ↔
      Reach (fun u w => adjacent u w = true) (fun u => source u = true)
        (fun u => blocked u = true) v := by
  rw [boundaryVertices, mem_exploreStack_iff List.mem_finRange]
  constructor
  · rintro ⟨start, starts, path⟩
    induction path with
    | refl => exact .seed (List.mem_filter.mp starts).2
    | extend _ move ih =>
      obtain ⟨openVertex, edge⟩ := (mem_next_vertices_iff adjacent blocked _ _).mp move
      exact .step ih openVertex edge
  · intro reaches
    induction reaches with
    | seed starts =>
      exact ⟨_, List.mem_filter.mpr ⟨List.mem_finRange _, starts⟩, .refl _⟩
    | step _ openVertex edge ih =>
      obtain ⟨start, starts, path⟩ := ih
      exact ⟨start, starts, .extend path
        ((mem_next_vertices_iff adjacent blocked _ _).mpr ⟨openVertex, edge⟩)⟩

private theorem boundary_hits_iff (adjacent : Fin n → Fin n → Bool)
    (left right blocked : Fin n → Bool) :
    (boundaryVertices adjacent left blocked).any right = true ↔
      ∃ v, right v = true ∧ Reach (fun u w => adjacent u w = true)
        (fun u => left u = true) (fun u => blocked u = true) v := by
  simp [List.any_eq_true, mem_boundary_vertices_iff, and_comm]

def keepBoundary (required chosen : Fin n → Bool)
    (boundary : List (Fin n)) : Fin n → Bool :=
  fun v => (chosen v && boundary.contains v) || required v

private theorem keep_boundary_iff (adjacent : Fin n → Fin n → Bool)
    (source required chosen : Fin n → Bool) (v : Fin n) :
    keepBoundary required chosen (boundaryVertices adjacent source chosen) v = true ↔
      keepReached (fun u w => adjacent u w = true) (fun u => source u = true)
        (fun u => required u = true) (fun u => chosen u = true) v := by
  simp [keepBoundary, keepReached, mem_boundary_vertices_iff]

/-- Two boundary passes on the given adjacency. The allowed set is the
initial blocker set, already restricted to the graph reduction if there is one. -/
def findMinimalSeparator (adjacent : Fin n → Fin n → Bool)
    (left right required allowed : Fin n → Bool) : Option (Fin n → Bool) :=
  let fromLeft := boundaryVertices adjacent left allowed
  if fromLeft.any right then none
  else
    let first := keepBoundary required allowed fromLeft
    some (keepBoundary required first (boundaryVertices adjacent right first))

/-- The option and subset returned by the boundary algorithm are exact.
The search does not depend on a particular order for visiting neighbors. -/
theorem find_minimal_separator_correct (adjacent : Fin n → Fin n → Bool)
    (left right required allowed : Fin n → Bool)
    (symmetric : ∀ u v, adjacent u v = true → adjacent v u = true)
    (requiredAllowed : ∀ v, required v = true → allowed v = true)
    (allowedLeft : ∀ v, allowed v = true → left v ≠ true)
    (allowedRight : ∀ v, allowed v = true → right v ≠ true) :
    let edge := fun u v => adjacent u v = true
    let X := fun v => left v = true
    let Y := fun v => right v = true
    let I := fun v => required v = true
    let R := fun v => allowed v = true
    match findMinimalSeparator adjacent left right required allowed with
    | none => ¬ ∃ Z, IsSeparator edge X Y I R Z
    | some Z => IsMinimalSeparator edge X Y I R (fun v => Z v = true) := by
  classical
  dsimp only
  let edge := fun u v => adjacent u v = true
  let X := fun v => left v = true
  let Y := fun v => right v = true
  let I := fun v => required v = true
  let R := fun v => allowed v = true
  change match findMinimalSeparator adjacent left right required allowed with
    | none => ¬ ∃ Z, IsSeparator edge X Y I R Z
    | some Z => IsMinimalSeparator edge X Y I R (fun v => Z v = true)
  have detection := boundary_hits_iff adjacent left right allowed
  unfold findMinimalSeparator
  dsimp only
  by_cases found : (boundaryVertices adjacent left allowed).any right = true
  · rw [ite_eq_left found]
    rintro ⟨chosen, _, allowedChosen, separates⟩
    obtain ⟨v, hy, reach⟩ := detection.mp found
    exact separates v hy (reach.map (fun _ h => .seed h) (fun _ _ h => h) allowedChosen)
  · rw [ite_eq_right found]
    let first := keepBoundary required allowed (boundaryVertices adjacent left allowed)
    change IsMinimalSeparator edge X Y I R
      (fun v => keepBoundary required first (boundaryVertices adjacent right first) v = true)
    have firstEq : (fun v => first v = true) = keepReached edge X I R :=
      funext fun v => propext (keep_boundary_iff adjacent left required allowed v)
    have secondEq : (fun v => keepBoundary required first
        (boundaryVertices adjacent right first) v = true) =
        keepReached edge Y I (keepReached edge X I R) := by
      exact (funext fun v => propext
        (keep_boundary_iff adjacent right required first v)).trans (by rw [firstEq])
    rw [secondEq]
    have baselineSep : Separated edge X Y R := fun v hy reaches =>
      found (detection.mpr ⟨v, hy, reaches⟩)
    have ⟨separates, keeps, within, witnesses⟩ := separating_prune symmetric requiredAllowed
      (fun v hx hz => allowedLeft v hz hx) (fun v hy hz => allowedRight v hz hy) baselineSep
    exact (is_minimal_separator_iff_boundary symmetric
      (fun v hx hz => allowedLeft v (within v hz) hx)
      (fun v hy hz => allowedRight v (within v hz) hy) ⟨keeps, within, separates⟩).mpr witnesses

/-- The nonminimal variant returns the full initial blocker set on success. -/
def findSeparator (adjacent : Fin n → Fin n → Bool)
    (left right allowed : Fin n → Bool) : Option (Fin n → Bool) :=
  if (boundaryVertices adjacent left allowed).any right then none else some allowed

/-- The first boundary pass decides feasibility before any pruning. -/
theorem find_separator_correct (adjacent : Fin n → Fin n → Bool)
    (left right required allowed : Fin n → Bool)
    (requiredAllowed : ∀ v, required v = true → allowed v = true) :
    let edge := fun u v => adjacent u v = true
    let X := fun v => left v = true
    let Y := fun v => right v = true
    let I := fun v => required v = true
    let R := fun v => allowed v = true
    match findSeparator adjacent left right allowed with
    | none => ¬ ∃ Z, IsSeparator edge X Y I R Z
    | some Z => IsSeparator edge X Y I R (fun v => Z v = true) := by
  have detection := boundary_hits_iff adjacent left right allowed
  unfold findSeparator
  dsimp only
  by_cases found : (boundaryVertices adjacent left allowed).any right = true
  · rw [ite_eq_left found]
    rintro ⟨chosen, _, allowedChosen, separates⟩
    obtain ⟨v, hy, reach⟩ := detection.mp found
    exact separates v hy (reach.map (fun _ h => .seed h) (fun _ _ h => h) allowedChosen)
  · rw [ite_eq_right found]
    exact ⟨requiredAllowed, fun _ h => h, fun v hy reach => found (detection.mpr ⟨v, hy, reach⟩)⟩

end

end OpenCausalScience.SeparatorBoundary
