module
public import OpenCausalScience.Graph.MixedSeparationExecutable

/-! # Collider augmentation of mixed graphs

In an induced mixed graph, the augmented graph connects distinct vertices
that can be joined through collider turns. The search retains the incoming
mark on each arrival and continues when both marks at a turn are heads.

[Richardson and Spirtes (2002), §3.5](https://doi.org/10.1214/aos/1031689015)
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n} {relevant : Fin n → Bool}

/-- The first state stores the outgoing mark, and the last state stores the
incoming mark. Each joining vertex must have two arrowheads. -/
inductive ColliderWalk (G : MixedGraph n) (relevant : Fin n → Bool) :
    Arrival n → Arrival n → Prop where
  | single {source target} : relevant source.1 = true → relevant target.1 = true →
      G.edge source.1 source.2 target.1 target.2 = true → ColliderWalk G relevant source target
  | join {source target : Arrival n} {middle : Fin n} :
      ColliderWalk G relevant source (middle, true) → ColliderWalk G relevant (middle, true) target →
      ColliderWalk G relevant source target

theorem ColliderWalk.reverse {source target : Arrival n}
    (walk : G.ColliderWalk relevant source target) : G.ColliderWalk relevant target source := by
  induction walk with
  | single left right edge => exact .single right left ((G.symmetric _ _ _ _).symm.trans edge)
  | join _ _ forward backward => exact .join backward forward

theorem ColliderWalk.source_relevant {source target : Arrival n}
    (walk : G.ColliderWalk relevant source target) : relevant source.1 = true := by
  induction walk with
  | single left _ _ => exact left
  | join _ _ relevantSource _ => exact relevantSource

theorem ColliderWalk.target_relevant {source target : Arrival n}
    (walk : G.ColliderWalk relevant source target) : relevant target.1 = true :=
  walk.reverse.source_relevant

/-- A successor in the arrival search, after the first edge. -/
def ColliderStep (G : MixedGraph n) (relevant : Fin n → Bool) (source target : Arrival n) : Prop :=
  source.2 = true ∧ relevant target.1 = true ∧ G.edge source.1 true target.1 target.2 = true

private theorem ColliderWalk.extend_reach {source target first : Arrival n}
    (walk : G.ColliderWalk relevant source target) (head : source.2 = true)
    (prior : Reach (G.ColliderStep relevant) first source) :
    Reach (G.ColliderStep relevant) first target := by
  induction walk with
  | single _ visible edge =>
    exact .extend prior ⟨head, visible, by simpa [head] using edge⟩
  | join _ _ towardMiddle fromMiddle => exact fromMiddle rfl (towardMiddle head prior)

theorem ColliderWalk.first_edge {source target : Arrival n}
    (walk : G.ColliderWalk relevant source target) :
    ∃ first, relevant first.1 = true ∧ G.edge source.1 source.2 first.1 first.2 = true ∧
      Reach (G.ColliderStep relevant) first target := by
  induction walk with
  | single _ visible edge => exact ⟨_, visible, edge, .refl _⟩
  | join _ endPath ih _ =>
    obtain ⟨first, visible, edge, reaches⟩ := ih
    exact ⟨first, visible, edge, endPath.extend_reach rfl reaches⟩

theorem ColliderWalk.of_first_edge {source first target : Arrival n}
    (firstEdge : G.ColliderWalk relevant source first)
    (path : Reach (G.ColliderStep relevant) first target) :
    G.ColliderWalk relevant source target := by
  induction path with
  | refl => exact firstEdge
  | @extend before after _ step ih =>
    obtain ⟨hasHead, visible, edge⟩ := step
    obtain ⟨current, mark⟩ := before
    change mark = true at hasHead
    subst mark
    exact .join ih (.single ih.target_relevant visible edge)

private theorem all_arrivals_complete (state : Arrival n) : state ∈ allArrivals n := by
  obtain ⟨u, mark⟩ := state
  cases mark <;> simp [allArrivals, List.mem_map]

/-- Seed the search at a neighbor in the induced graph. -/
def colliderSeeds (G : MixedGraph n) (relevant : Fin n → Bool) (source : Fin n) : List (Arrival n) :=
  (G.seedArrivals (fun v => (v == source) && relevant v)).filter fun s => relevant s.1

theorem mem_colliderSeeds_iff (G : MixedGraph n) (relevant : Fin n → Bool)
    (source : Fin n) (state : Arrival n) :
    state ∈ G.colliderSeeds relevant source ↔
      relevant source = true ∧ relevant state.1 = true ∧
        ∃ mark, G.edge source mark state.1 state.2 = true := by
  rw [colliderSeeds, List.mem_filter, G.mem_seedArrivals_iff]
  constructor
  · rintro ⟨⟨vertex, mark, isSeed, edge⟩, targetIncluded⟩
    obtain ⟨h, included⟩ : (vertex == source) = true ∧ relevant vertex = true := by
      simpa only [Bool.and_eq_true] using isSeed
    have same : vertex = source := by simpa using h
    subst vertex
    exact ⟨included, targetIncluded, mark, edge⟩
  · rintro ⟨included, targetIncluded, mark, edge⟩
    exact ⟨⟨source, mark, by simp [included], edge⟩, targetIncluded⟩

/-- Continue through a vertex only when the arrival and departure marks are heads. -/
def nextColliderArrivals (G : MixedGraph n) (relevant : Fin n → Bool) (state : Arrival n) :
    List (Arrival n) :=
  (allArrivals n).filter fun target =>
    state.2 && (relevant target.1 && G.edge state.1 true target.1 target.2)

theorem mem_nextColliderArrivals_iff (G : MixedGraph n) (relevant : Fin n → Bool)
    (before after : Arrival n) :
    after ∈ G.nextColliderArrivals relevant before ↔ G.ColliderStep relevant before after := by
  simp only [nextColliderArrivals, List.mem_filter, all_arrivals_complete, true_and,
    Bool.and_eq_true, ColliderStep]

def colliderVisited (G : MixedGraph n) (relevant : Fin n → Bool) (source : Fin n) : List (Arrival n) :=
  exploreStack (G.nextColliderArrivals relevant) (allArrivals n) (G.colliderSeeds relevant source)

private theorem map_reach {α : Type} {R S : α → α → Prop} {u v : α}
    (walk : Reach R u v) (transfer : ∀ a b, R a b → S a b) : Reach S u v := by
  induction walk with
  | refl => exact .refl _
  | extend _ step ih => exact .extend ih (transfer _ _ step)

theorem mem_colliderVisited_iff (G : MixedGraph n) (relevant : Fin n → Bool)
    (source : Fin n) (state : Arrival n) :
    state ∈ G.colliderVisited relevant source ↔
      ∃ outgoing, G.ColliderWalk relevant (source, outgoing) state := by
  rw [colliderVisited, mem_exploreStack_iff all_arrivals_complete]
  constructor
  · rintro ⟨first, initial, reached⟩
    obtain ⟨left, right, outgoing, edge⟩ := (G.mem_colliderSeeds_iff relevant source first).mp initial
    exact ⟨outgoing, ColliderWalk.of_first_edge (.single left right edge)
      (map_reach reached fun a b => (G.mem_nextColliderArrivals_iff relevant a b).mp)⟩
  · rintro ⟨outgoing, walk⟩
    obtain ⟨first, right, edge, path⟩ := walk.first_edge
    exact ⟨first, (G.mem_colliderSeeds_iff relevant source first).mpr
      ⟨walk.source_relevant, right, outgoing, edge⟩,
      map_reach path fun a b => (G.mem_nextColliderArrivals_iff relevant a b).mpr⟩

/-- The undirected augmentation inserts both directions whenever the search
from either vertex reaches the other. -/
def colliderAugmented (G : MixedGraph n) (relevant : Fin n → Bool) (source target : Fin n) : Bool :=
  (source != target) &&
    (((G.colliderVisited relevant source).any fun state => state.1 == target) ||
      ((G.colliderVisited relevant target).any fun state => state.1 == source))

private theorem any_colliderVisited_iff (G : MixedGraph n) (relevant : Fin n → Bool)
    (source target : Fin n) :
    ((G.colliderVisited relevant source).any fun state => state.1 == target) = true ↔
      ∃ outgoing incoming, G.ColliderWalk relevant (source, outgoing) (target, incoming) := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨v, incoming⟩, visited, isTarget⟩
    have same : v = target := by simpa using isTarget
    subst v
    obtain ⟨outgoing, walk⟩ := (G.mem_colliderVisited_iff relevant source _).mp visited
    exact ⟨outgoing, incoming, walk⟩
  · rintro ⟨outgoing, incoming, walk⟩
    exact ⟨(target, incoming), (G.mem_colliderVisited_iff relevant source _).mpr
      ⟨outgoing, walk⟩, by simp⟩

theorem collider_augmented_iff (G : MixedGraph n) (relevant : Fin n → Bool)
    (source target : Fin n) :
    G.colliderAugmented relevant source target = true ↔ source ≠ target ∧
      ∃ outgoing incoming, G.ColliderWalk relevant (source, outgoing) (target, incoming) := by
  simp only [colliderAugmented, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true_iff, any_colliderVisited_iff]
  constructor
  · rintro ⟨distinct, forward | ⟨incoming, outgoing, back⟩⟩
    · exact ⟨distinct, forward⟩
    · exact ⟨distinct, outgoing, incoming, back.reverse⟩
  · rintro ⟨distinct, forward⟩
    exact ⟨distinct, .inl forward⟩

theorem collider_augmented_symmetric (G : MixedGraph n) (relevant : Fin n → Bool)
    (source target : Fin n) :
    G.colliderAugmented relevant source target = G.colliderAugmented relevant target source := by
  have different : (source != target) = (target != source) := bne_comm
  simp only [colliderAugmented, different, Bool.or_comm]

end

end OpenCausalScience.MixedGraph
