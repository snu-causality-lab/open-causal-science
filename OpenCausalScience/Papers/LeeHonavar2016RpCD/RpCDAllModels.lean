module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDEquivalence

@[expose] public section

namespace RpCD

open Ground Completion RelationalFiniteSearch
open OpenCausalScience.Papers.VermaPearl1990.Equivalence

variable {A P S : Type} [DecidableEq A] [DecidableEq P]

def Ground.Model.classArrow (M : Model A P) (u v : A) : Prop :=
  ∃ q ∈ M.dependencies, q.source = u ∧ q.target = v

def rankOrder (M : Model A P) (attributes : List A) : List A :=
  attributes.mergeSort fun x y => decide (M.rank y ≤ M.rank x)

omit [DecidableEq P] in
private theorem order_earlier_of_higher_rank (M : Model A P) (attributes : List A)
    {u v : A} (hu : u ∈ attributes) (hv : v ∈ attributes) (direction : M.rank u < M.rank v) :
    (rankOrder M attributes).idxOf v < (rankOrder M attributes).idxOf u := by
  let order := rankOrder M attributes
  have perm : order.Perm attributes := List.mergeSort_perm ..
  have uIndex : order.idxOf u < order.length := List.idxOf_lt_length_iff.mpr (perm.mem_iff.mpr hu)
  have vIndex : order.idxOf v < order.length := List.idxOf_lt_length_iff.mpr (perm.mem_iff.mpr hv)
  have decreasing : order.Pairwise (fun a b => decide (M.rank b ≤ M.rank a) = true) :=
    List.pairwise_mergeSort (le := fun a b => decide (M.rank b ≤ M.rank a)) (fun a b c x y => decide_eq_true (Nat.le_trans
      (of_decide_eq_true y) (of_decide_eq_true x)))
      (by intro a b; simpa using Nat.le_total (M.rank b) (M.rank a)) attributes
  apply Nat.lt_of_not_ge
  intro notEarlier
  rcases Nat.lt_or_eq_of_le notEarlier with earlier | same
  · have opposite := (List.pairwise_iff_getElem.mp decreasing) _ _ uIndex vIndex earlier
    rw [List.getElem_idxOf uIndex, List.getElem_idxOf vIndex] at opposite
    exact Nat.not_le_of_gt direction (of_decide_eq_true opposite)
  · have equal := congrArg (fun i : Nat => order[i]?) same
    rw [List.getElem?_eq_getElem uIndex, List.getElem?_eq_getElem vIndex,
      List.getElem_idxOf uIndex, List.getElem_idxOf vIndex] at equal
    have uv := Option.some.inj equal
    simp [uv] at direction

theorem equivalent_model_represented {B : Schema A P S} {M N : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (initial : List (Dependency A P))
    (containsN : ∀ q ∈ N.dependencies, q ∈ initial)
    (closed : PairClosed (phaseQuery L O) initial) (valid : ∀ q ∈ initial, q.source ≠ q.target)
    (legal : ∀ q ∈ initial, L.valid q) (same : SameRelCI B M N)
    (attributes : List A) (attrLive : ∀ s v, B.attributeOf s v ∈ attributes) :
    let skeleton := learnedSkeleton L O initial
    let order := rankOrder N attributes
    ∀ q, q ∈ (reorient skeleton order).dependencies ↔ q ∈ N.dependencies := by
  let oracleN : Oracle B N := ⟨O.answer, fun q selected => (O.exact q selected).trans (same q selected)⟩
  have recovered := phaseOne_ground_exact L oracleN initial containsN closed valid legal
  intro skeleton order q
  have lives (p : Dependency A P) (mem : p ∈ N.dependencies) :
      p.source ∈ attributes ∧ p.target ∈ attributes := by
    obtain ⟨s, x, z, hit, _⟩ := L.isolate p (legal p (containsN p mem)) (valid p (containsN p mem))
    obtain ⟨target, source⟩ := B.types s p x z hit
    exact ⟨source ▸ attrLive s z, target ▸ attrLive s x⟩
  constructor
  · intro oriented
    obtain ⟨surviving, direction⟩ := List.mem_filter.mp oriented
    rcases ((recovered q).mp surviving).2 with own | reverse
    · exact of_decide_eq_true own
    · have rDep : L.reverse q ∈ N.dependencies := of_decide_eq_true reverse
      obtain ⟨src, dst⟩ := L.endpoints q
      obtain ⟨source, target⟩ := lives (L.reverse q) rDep
      have opposite := order_earlier_of_higher_rank N attributes source target (N.acyclic _ rDep)
      rw [src, dst] at opposite
      exact (Nat.lt_asymm opposite (of_decide_eq_true direction)).elim
  · intro member
    obtain ⟨source, target⟩ := lives q member
    exact List.mem_filter.mpr ⟨(recovered q).mpr ⟨containsN q member, .inl (decide_eq_true member)⟩,
      decide_eq_true (order_earlier_of_higher_rank N attributes source target (N.acyclic q member))⟩

theorem revisedRpCD_allModels_correct {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (initial : List (Dependency A P))
    (initialContains : ∀ q ∈ M.dependencies, q ∈ initial)
    (initialClosed : PairClosed (phaseQuery L O) initial)
    (initialValid : ∀ q ∈ initial, q.source ≠ q.target)
    (initialLegal : ∀ q ∈ initial, L.valid q)
    {cuts : List (OrderedCUT B M)} (coverage : CUTCoverage cuts)
    (attributes : List A) (unique : attributes.Nodup)
    (attrLive : ∀ s v, B.attributeOf s v ∈ attributes) :
    let learned := revisedRpCD L O initial cuts attributes
    (∀ d, d ∈ learned.1 ↔ d ∈ M.dependencies ∨ L.reverse d ∈ M.dependencies) ∧
    (∀ u ∈ attributes, ∀ v ∈ attributes, classAdjacent learned.1 u v = true →
      (learned.2 u v = true ↔ ∀ N : Model A P, (∀ q ∈ N.dependencies, q ∈ initial) →
        SameRelCI B M N → N.classArrow u v)) := by
  let learned := revisedRpCD L O initial cuts attributes
  have learnedCorrect := revisedRpCD_relational_correct L O initial initialContains initialClosed initialValid initialLegal
    coverage attributes unique attrLive
  refine ⟨learnedCorrect.1, fun u hu v hv uv => ?_⟩
  obtain ⟨q, surviving, hit⟩ := List.any_eq_true.mp uv
  obtain ⟨source, target⟩ := Bool.and_eq_true_iff.mp hit
  have dependencyEndpoints : q.source = u ∧ q.target = v := ⟨eq_of_beq source, eq_of_beq target⟩
  rw [learnedCorrect.2 u hu v hv uv]
  constructor
  · intro oriented N containsN same
    let order := rankOrder N attributes
    have perm : order.Perm attributes := List.mergeSort_perm ..
    have reflected : ∀ d, d ∈ (reorient learned.1 order).dependencies ↔ d ∈ N.dependencies :=
      equivalent_model_represented L O initial containsN initialClosed initialValid initialLegal same attributes attrLive
    have ground : ∀ s, OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence.SameDConnections (graph B N s) (graph B (reorient learned.1 order) s) := by
      intro s
      apply same_dConnections_of_edge_eq
      funext x y
      apply Bool.eq_iff_iff.mpr
      change N.dependencies.any _ = true ↔ (reorient learned.1 order).dependencies.any _ = true
      simp only [List.any_eq_true, reflected]
    have comp : SameRelCI B M (reorient learned.1 order) :=
      fun q selected => (same q selected).trans (sameRelCI_of_ground ground q selected)
    have direction := oriented order (perm.nodup_iff.mpr unique) (fun _ => perm.mem_iff) comp
    have chosen : q ∈ (reorient learned.1 order).dependencies :=
      List.mem_filter.mpr ⟨surviving, decide_eq_true (by simpa [dependencyEndpoints.1,
        dependencyEndpoints.2] using direction)⟩
    exact ⟨q, (reflected q).mp chosen, dependencyEndpoints⟩
  · intro forced order _ _ same
    have included (d : Dependency A P) (dep : d ∈ (reorient learned.1 order).dependencies) :
        d ∈ initial :=
      (phaseOne_ground_exact L O initial initialContains initialClosed initialValid initialLegal d).mp
        (List.mem_filter.mp dep).1 |>.1
    obtain ⟨d, dep, src, dst⟩ := forced (reorient learned.1 order) included same
    have direction : order.idxOf d.target < order.idxOf d.source :=
      of_decide_eq_true (List.mem_filter.mp dep).2
    simpa [src, dst] using direction

end RpCD

end
