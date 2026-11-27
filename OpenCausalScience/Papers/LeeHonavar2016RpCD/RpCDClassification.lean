module
public import OpenCausalScience.Discovery.RelationalFiniteSearch
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDCompletion
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDGround

@[expose] public section

namespace RpCD

open Ground
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

structure Triple (A : Type) where
  left : A
  middle : A
  right : A
  deriving DecidableEq

structure Status (A : Type) where
  triple : Triple A
  collider : Bool

variable {A P S : Type}

structure Oracle (B : Schema A P S) (M : Model A P) where
  answer : Dependency A P → List (Dependency A P) → Bool
  exact : ∀ q selected, answer q selected = true ↔ RelCI B M q selected

def Ground.CUT.triple {B : Schema A P S} {M : Model A P} {q : Dependency A P}
    (w : CUT B M q) : Triple A :=
  ⟨B.attributeOf w.skeleton w.base, B.attributeOf w.skeleton w.middle,
    B.attributeOf w.skeleton w.other⟩

private theorem condition_congr {B : Schema A P S} {selected other : List (Dependency A P)}
    (same : ∀ p, p ∈ selected ↔ p ∈ other) {s : S} {base : Fin (B.size s)} :
    condition B s base selected = condition B s base other := by
  funext v
  apply Bool.eq_iff_iff.mpr
  simp only [condition, List.any_eq_true, same]

theorem relCI_congr {B : Schema A P S} {M : Model A P} {q : Dependency A P}
    {selected other : List (Dependency A P)} (same : ∀ p, p ∈ selected ↔ p ∈ other) :
    RelCI B M q selected ↔ RelCI B M q other := by
  unfold RelCI
  simp only [condition_congr same]

structure OrderedCUT (B : Schema A P S) (M : Model A P) where
  query : Dependency A P
  witness : CUT B M query

/-- Search all subsets of the surviving relational adjacencies in this
perspective. Membership of the middle is checked in the CUT's own skeleton. -/
def classify {B : Schema A P S} {M : Model A P} (O : Oracle B M)
    (neighbors : A → List (Dependency A P)) (c : OrderedCUT B M) : Option (Status A) :=
  let w := c.witness
  ((RelationalFiniteSearch.conditioningLists (neighbors c.query.target)).find?
    (O.answer c.query)).map fun selected =>
      ⟨w.triple, !(condition B w.skeleton w.base selected w.middle)⟩

theorem classify_sound {B : Schema A P S} {M : Model A P} (O : Oracle B M)
    (neighbors : A → List (Dependency A P)) (c : OrderedCUT B M)
    (sound : ∀ p ∈ neighbors c.query.target, ∀ z,
      B.realizes c.witness.skeleton p c.witness.base z = true →
      Adjacent (Ground.graph B M c.witness.skeleton) c.witness.base z)
    {result : Status A} (classified : classify O neighbors c = some result) :
    result.triple = c.witness.triple ∧
      (result.collider = true ↔
        HeadToHead (Ground.graph B M c.witness.skeleton)
          c.witness.base c.witness.middle c.witness.other) := by
  unfold classify at classified
  cases found :
      (RelationalFiniteSearch.conditioningLists (neighbors c.query.target)).find?
        (O.answer c.query) with
  | none => simp [found] at classified
  | some selected =>
    simp [found] at classified
    subst result
    refine ⟨rfl, ?_⟩
    have sub := RelationalFiniteSearch.mem_conditioningLists.mp (List.mem_of_find?_eq_some found)
    have ci := (O.exact _ _).mp (List.find?_some found)
    simpa only [Bool.not_eq_true'] using
      cut_collider_by_neighbors B M c.witness (fun p mem => sound p (sub.subset mem)) ci

theorem classify_exists [DecidableEq A] [DecidableEq P]
    {B : Schema A P S} {M : Model A P} (O : Oracle B M)
    (neighbors : A → List (Dependency A P)) (c : OrderedCUT B M)
    (includeParents : ∀ p ∈ parents M c.query.target, p ∈ neighbors c.query.target)
    (different : ∀ s x z, B.realizes s c.query x z = true → x ≠ z)
    (rankOrder : M.rank c.query.source ≤ M.rank c.query.target) :
    ∃ result, classify O neighbors c = some result := by
  let pa := parents M c.query.target
  let selected := (neighbors c.query.target).filter (· ∈ pa)
  have equiv (p : Dependency A P) : p ∈ selected ↔ p ∈ pa := by
    simp only [selected, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun present => ⟨includeParents p present, present⟩⟩
  have ci := (relCI_congr (B := B) (M := M) (q := c.query) equiv).mpr
    (parents_separate_of_distinct B M different rankOrder)
  have listed := RelationalFiniteSearch.mem_conditioningLists.mpr
    (List.filter_sublist (l := neighbors c.query.target) (p := fun p => decide (p ∈ pa)))
  cases found :
      (RelationalFiniteSearch.conditioningLists (neighbors c.query.target)).find?
        (O.answer c.query) with
  | none =>
    exact ((List.find?_eq_none.mp found) selected listed ((O.exact _ _).mpr ci)).elim
  | some xs =>
    exact ⟨⟨c.witness.triple, !(condition B c.witness.skeleton c.witness.base xs c.witness.middle)⟩,
      by simp [classify, found]⟩

/-- The successful direction may use a different admissible CUT witness. -/
theorem classify_one_of_two [DecidableEq A] [DecidableEq P]
    {B : Schema A P S} {M : Model A P} (O : Oracle B M)
    (neighbors : A → List (Dependency A P)) (f r : OrderedCUT B M)
    (source : f.query.source = r.query.target) (target : f.query.target = r.query.source)
    (includeParents : ∀ x p, p ∈ parents M x → p ∈ neighbors x)
    (fDistinct : ∀ s x z, B.realizes s f.query x z = true → x ≠ z)
    (rDistinct : ∀ s x z, B.realizes s r.query x z = true → x ≠ z) :
    (∃ result, classify O neighbors f = some result) ∨
      (∃ result, classify O neighbors r = some result) := by
  rcases Nat.le_total (M.rank f.query.source) (M.rank f.query.target) with forward | backward
  · exact .inl (classify_exists O neighbors f (includeParents _) fDistinct forward)
  · exact .inr (classify_exists O neighbors r (includeParents _) rDistinct (by simpa [source, target] using backward))

namespace Completion

variable [DecidableEq A]

/-- Collect definite colliders and forbidden colliders before completing the
class graph. A triple with equal endpoint classes is allowed. -/
def classifyConstraints (adj : A → A → Bool) (results : List (Status A)) : Constraints A where
  adjacent := adj
  fixed := fun x y => results.any fun c =>
    c.collider && (c.triple.middle == y) && ((c.triple.left == x) || (c.triple.right == x))
  noncollider := fun x y z => results.any fun c =>
    !c.collider && (c.triple.left == x) && (c.triple.middle == y) && (c.triple.right == z)

def Matches (adj : A → A → Bool) (order : List A) (c : Status A) : Prop :=
  let C : Constraints A := ⟨adj, fun _ _ => false, fun _ _ _ => false⟩
  c.collider = true ↔ arrow C order c.triple.left c.triple.middle ∧
    arrow C order c.triple.right c.triple.middle

theorem classifyConstraints_valid (adj : A → A → Bool) (results : List (Status A))
    (symm : ∀ x y, adj x y = adj y x) (noLoops : ∀ x, adj x x = false)
    (incident : ∀ c ∈ results, adj c.triple.left c.triple.middle = true ∧
      adj c.triple.right c.triple.middle = true) :
    ValidInput (classifyConstraints adj results) where
  symmetric := symm
  loopless := noLoops
  fixed_adjacent x y hit := by
    obtain ⟨c, member, found⟩ := List.any_eq_true.mp hit
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at found
    obtain ⟨⟨_, middle⟩, left | right⟩ := found
    · simpa [classifyConstraints, middle, left] using (incident c member).1
    · simpa [classifyConstraints, middle, right] using (incident c member).2

theorem classified_extensions_iff (adj : A → A → Bool)
    (results : List (Status A)) (live order : List A)
    (covered : ∀ c ∈ results, c.triple.left ∈ live ∧ c.triple.middle ∈ live ∧ c.triple.right ∈ live) :
    Consistent (classifyConstraints adj results) live order ↔
      order.Nodup ∧ (∀ v, v ∈ order ↔ v ∈ live) ∧ ∀ c ∈ results, Matches adj order c := by
  constructor
  · intro h
    refine ⟨h.nodup, h.members, fun c member => ?_⟩
    obtain ⟨left, middle, right⟩ := covered c member
    unfold Matches
    constructor
    · intro yes
      have fixedLeft : (classifyConstraints adj results).fixed c.triple.left c.triple.middle = true :=
        List.any_eq_true.mpr ⟨c, member, by simp [yes]⟩
      have fixedRight : (classifyConstraints adj results).fixed c.triple.right c.triple.middle = true :=
        List.any_eq_true.mpr ⟨c, member, by simp [yes]⟩
      exact ⟨h.fixed _ left _ middle fixedLeft, h.fixed _ right _ middle fixedRight⟩
    · intro both
      by_cases yes : c.collider = true
      · exact yes
      have no : c.collider = false := Bool.eq_false_iff.mpr yes
      have reject :
          (classifyConstraints adj results).noncollider c.triple.left c.triple.middle c.triple.right = true :=
        List.any_eq_true.mpr ⟨c, member, by simp [no]⟩
      exact (h.noncollider _ left _ middle _ right reject both).elim
  · rintro ⟨nodup, members, agrees⟩
    refine ⟨nodup, members, ?_, ?_⟩
    · intro x _ y _ fixed
      obtain ⟨c, member, hit⟩ := List.any_eq_true.mp fixed
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hit
      obtain ⟨⟨yes, middle⟩, left | right⟩ := hit
      · simpa only [arrow, classifyConstraints, left, middle] using ((agrees c member).mp yes).1
      · simpa only [arrow, classifyConstraints, right, middle] using ((agrees c member).mp yes).2
    · intro x _ y _ z _ no collider
      obtain ⟨c, member, hit⟩ := List.any_eq_true.mp no
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hit
      obtain ⟨⟨⟨notCollider, left⟩, middle⟩, right⟩ := hit
      have yes := (agrees c member).mpr (by simpa only [arrow, classifyConstraints, left, middle, right] using collider)
      simp [notCollider] at yes

end Completion
end RpCD

end
