module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.ClassClosure

/-! Isolated typed line witnesses for the canonical queries in Lee–Honavar
(2016), Lemma 1. Bridge burning excludes any alternative conditioning word
from the two ground endpoints. -/

@[expose] public section

namespace RCDPathValidity

open RCDLemma5

variable {K : Type} {S : Schema K}

abbrev Slot (w : List K) := Fin w.length
abbrev Item (w : List K) := Slot w ⊕ (Slot w × K)

def orient {n : Nat} (backward : Bool) (i : Fin n) : Fin n :=
  if backward then i.rev else i

private theorem orient_orient {n : Nat} (backward : Bool) (i : Fin n) :
    orient backward (orient backward i) = i := by
  cases backward <;> simp [orient, Fin.rev_rev]

def readWord (backward : Bool) (w : List K) : List K :=
  if backward then w.reverse else w

private theorem read_length (backward : Bool) (w : List K) :
    (readWord backward w).length = w.length := by
  cases backward <;> simp [readWord]

def orientedCore {w : List K} (backward : Bool) (i : Slot w) : Item w :=
  .inl (orient backward i)

def distance {w : List K} (backward : Bool) : Item w → Nat
  | .inl i => (orient backward i).val
  | .inr (i, _) => (orient backward i).val + 1

private theorem distance_core {w : List K} (backward : Bool) (i : Slot w) :
    distance backward (orientedCore backward i) = i.val := by
  simp [distance, orientedCore, orient_orient]

private theorem orient_neighbors {w : List K} (backward : Bool) {i j : Slot w}
    (next : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    (orient backward i).val + 1 = (orient backward j).val ∨
      (orient backward j).val + 1 = (orient backward i).val := by
  cases backward
  · exact next
  · have iBound := i.isLt
    have jBound := j.isLt
    simp only [orient, ite_true, Fin.val_rev]
    omega

private theorem next_oriented_core {w : List K} (h : Local S.adj S.retrace w)
    (backward : Bool) {i j : Slot w} (step : i.val + 1 = j.val) :
    (lineSkeleton S w h).edge (orientedCore backward i) (orientedCore backward j) :=
  orient_neighbors backward (.inl step)

private theorem line_edge_bound {w : List K} (h : Local S.adj S.retrace w)
    (backward : Bool) {u v : Item w} (edge : (lineSkeleton S w h).edge u v) :
    distance backward v ≤ distance backward u + 1 := by
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      have choices := orient_neighbors backward (show i.val + 1 = j.val ∨ j.val + 1 = i.val from edge)
      simp only [distance]
      omega
    | inr p =>
      obtain ⟨j, e⟩ := p
      have same : i = j := edge.1
      subst j
      exact Nat.le_refl _
  | inr p =>
    obtain ⟨i, e⟩ := p
    cases v with
    | inl j =>
      have same : j = i := edge.1
      subst j
      simp only [distance]
      omega
    | inr p => exact False.elim edge

private theorem kind_of_core {w : List K} (h : Local S.adj S.retrace w)
    (backward : Bool) (i : Slot w) :
    (lineSkeleton S w h).kind (orientedCore backward i) =
      (readWord backward w)[i.val]'(by rw [read_length]; exact i.isLt) := by
  cases backward
  · rfl
  · change w[(i.rev).val] = w.reverse[i.val]
    rw [List.getElem_reverse]
    have eq : i.rev.val = w.length - 1 - i.val := by
      rw [Fin.val_rev]
      omega
    have same : i.rev = (⟨w.length - 1 - i.val, by have := i.isLt; omega⟩ : Slot w) :=
      Fin.ext eq
    exact congrArg (fun j : Slot w => w[j.val]) same

private theorem line_trail_forward {w : List K} (h : Local S.adj S.retrace w)
    (backward : Bool) {suffix : List K}
    (i : Slot w) (remaining : suffix = (readWord backward w).drop (i.val + 1)) :
    ∃ trail : List (Item w),
      Chain (lineSkeleton S w h).edge (orientedCore backward i) trail ∧
      Chain (fun u v => distance backward v = distance backward u + 1)
        (orientedCore backward i) trail ∧
      trail.map (lineSkeleton S w h).kind = suffix ∧
      (orientedCore backward i :: trail).getLast? =
        some (orientedCore backward ⟨w.length - 1, by have := i.isLt; omega⟩) := by
  induction suffix generalizing i with
  | nil =>
    have exactPos : i.val = w.length - 1 := by
      have size := congrArg List.length remaining
      simp only [List.length_nil, List.length_drop, read_length] at size
      have bound := i.isLt
      omega
    have pos : i = (⟨w.length - 1, by omega⟩ : Slot w) := Fin.ext exactPos
    exact ⟨[], trivial, trivial, rfl, by simp [pos]⟩
  | cons k ks ih =>
    have hasNext : i.val + 1 < w.length := by
      have size := congrArg List.length remaining
      simp only [List.length_cons, List.length_drop, read_length] at size
      omega
    let j : Slot w := ⟨i.val + 1, hasNext⟩
    have jWord : j.val < (readWord backward w).length := by rw [read_length]; exact j.isLt
    rw [List.drop_eq_getElem_cons jWord] at remaining
    obtain ⟨first, tail⟩ := List.cons.inj remaining
    obtain ⟨trail, adjacent, rises, kinds, last⟩ := ih j tail
    refine ⟨orientedCore backward j :: trail, ⟨next_oriented_core h backward rfl, adjacent⟩,
      ⟨by simp only [distance_core]; rfl, rises⟩, ?_, by simpa using last⟩
    exact congr (congrArg List.cons ((kind_of_core h backward j).trans first.symm)) kinds

private theorem exact_core_word {w : List K} (h : Local S.adj S.retrace w)
    (backward : Bool) {i : Slot w} {trail : List (Item w)}
    (adjacent : Chain (lineSkeleton S w h).edge (orientedCore backward i) trail)
    (last : (orientedCore backward i :: trail).getLast? =
      some (orientedCore backward ⟨w.length - 1, by have := i.isLt; omega⟩))
    (loopless : (orientedCore backward i :: trail).Nodup)
    (noBehind : ∀ j : Slot w, j.val + 1 = i.val → orientedCore backward j ∉ trail) :
    trail.map (lineSkeleton S w h).kind = (readWord backward w).drop (i.val + 1) := by
  induction trail generalizing i with
  | nil =>
    have eq : orientedCore backward i =
        orientedCore backward ⟨w.length - 1, by have := i.isLt; omega⟩ := by simpa using last
    have pos : i.val = w.length - 1 := by
      simpa only [distance_core] using congrArg (distance backward) eq
    rw [List.drop_of_length_le]
    · rfl
    · simp only [read_length]; omega
  | cons first trail ih =>
    cases first with
    | inr leaf =>
      obtain ⟨j,k⟩ := leaf
      cases trail with
      | nil => simp [orientedCore] at last
      | cons next tail =>
        have edgeA : orient backward i = j := adjacent.1.1
        have edgeB : next = Sum.inl j := by
          cases next with
          | inl l => exact congrArg Sum.inl adjacent.2.1.1
          | inr leaf => exact False.elim adjacent.2.1
        have blocked := (List.nodup_cons.mp loopless).1
        exfalso
        apply blocked
        simp [orientedCore, edgeA, edgeB]
    | inl original =>
      let j := orient backward original
      have firstEq : orientedCore backward j = Sum.inl original :=
        congrArg Sum.inl (orient_orient backward original)
      rw [← firstEq] at adjacent last loopless noBehind ⊢
      have step : i.val + 1 = j.val := by
        have originalStep : (orient backward i).val + 1 = (orient backward j).val ∨
            (orient backward j).val + 1 = (orient backward i).val := adjacent.1
        have choice := orient_neighbors backward originalStep
        simp only [orient_orient] at choice
        exact choice.resolve_right (fun prior => noBehind j prior (by simp))
      have priorAbsent (p : Slot w) (behind : p.val + 1 = j.val) :
          orientedCore backward p ∉ trail := by
        have same : p = i := Fin.ext (by omega)
        intro appeared
        exact (List.nodup_cons.mp loopless).1
          (List.mem_cons_of_mem _ (same ▸ appeared))
      have nextWord := ih adjacent.2 (by simpa using last)
        (List.nodup_cons.mp loopless).2 priorAbsent
      have jWord : j.val < (readWord backward w).length := by rw [read_length]; exact j.isLt
      rw [step, List.drop_eq_getElem_cons jWord]
      exact congr (congrArg List.cons (kind_of_core h backward j)) nextWord

theorem oriented_terminal_word {w : List K} (h : Local S.adj S.retrace w)
    (nonempty : w ≠ []) (backward : Bool) {word : List K}
    (reaches : Terminal (lineSkeleton S w h) word
      (orientedCore backward ⟨0, List.length_pos_iff.mpr nonempty⟩)
      (orientedCore backward ⟨w.length - 1, by have := List.length_pos_iff.mpr nonempty; omega⟩)) :
    word = readWord backward w := by
  obtain ⟨trail, adjacent, spelling, last, loopless⟩ := trace_of_terminal reaches
  let i : Slot w := ⟨0, List.length_pos_iff.mpr nonempty⟩
  have path := exact_core_word h backward adjacent last loopless (by
    intro j prior
    change j.val + 1 = 0 at prior
    omega)
  change (orientedCore backward i :: trail).map (lineSkeleton S w h).kind = word at spelling
  rw [← spelling]
  have head : i.val < (readWord backward w).length := by rw [read_length]; exact i.isLt
  have decomp := List.drop_eq_getElem_cons head
  change (readWord backward w).drop 0 = _ at decomp
  rw [List.drop_zero] at decomp
  exact (congr (congrArg List.cons (kind_of_core h backward i)) path).trans decomp.symm

theorem reaches_oriented_endpoints {w : List K} (h : Local S.adj S.retrace w)
    (nonempty : w ≠ []) (backward : Bool) :
    Terminal (lineSkeleton S w h) (readWord backward w)
      (orientedCore backward ⟨0, List.length_pos_iff.mpr nonempty⟩)
      (orientedCore backward ⟨w.length - 1, by have := List.length_pos_iff.mpr nonempty; omega⟩) := by
  let i : Slot w := ⟨0, List.length_pos_iff.mpr nonempty⟩
  obtain ⟨trail, adjacent, rises, kinds, last⟩ :=
    line_trail_forward h backward i (suffix := (readWord backward w).drop 1) rfl
  have terminal := terminal_of_ranked_chain (g := lineSkeleton S w h)
    (distance backward) (line_edge_bound h backward)
    (show (lineSkeleton S w h).present (orientedCore backward i) from trivial)
    adjacent rises last
  have head : i.val < (readWord backward w).length := by rw [read_length]; exact i.isLt
  have spelling : (orientedCore backward i :: trail).map (lineSkeleton S w h).kind =
      readWord backward w := by
    have decomp := List.drop_eq_getElem_cons head
    change (readWord backward w).drop 0 = _ at decomp
    rw [List.drop_zero] at decomp
    exact (congr (congrArg List.cons (kind_of_core h backward i)) kinds).trans decomp.symm
  exact spelling ▸ terminal

structure IsolatedLine (S : Schema K) (w : List K) where
  skeleton : Skeleton S
  start : skeleton.Item
  finish : skeleton.Item
  startsPresent : skeleton.present start
  finishPresent : skeleton.present finish
  startKind : w.head? = some (skeleton.kind start)
  finishKind : w.getLast? = some (skeleton.kind finish)
  forward : Terminal skeleton w start finish
  backward : Terminal skeleton w.reverse finish start
  uniqueForward : ∀ other, Terminal skeleton other start finish → other = w
  uniqueBackward : ∀ other, Terminal skeleton other finish start → other = w.reverse

/-- The whole-history terminal semantics reaches the opposite endpoint in
both traversals, and only the specified class word can reach it. -/
def isolatedLine {w : List K} (nonempty : w ≠ []) (h : Local S.adj S.retrace w) :
    IsolatedLine S w := by
  let start : Slot w := ⟨0, List.length_pos_iff.mpr nonempty⟩
  let finish : Slot w := ⟨w.length - 1, by have := start.isLt; omega⟩
  have backwardsStart : orientedCore true start = Sum.inl finish := by
    apply congrArg Sum.inl
    apply Fin.ext
    rfl
  have backwardsFinish : orientedCore true finish = Sum.inl start := by
    apply congrArg Sum.inl
    apply Fin.ext
    change (finish.rev).val = 0
    have bound := start.isLt
    simp only [Fin.val_rev, finish]
    omega
  refine ⟨lineSkeleton S w h, .inl start, .inl finish, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem start.isLt]
    rfl
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem finish.isLt]
    rfl
  · exact reaches_oriented_endpoints h nonempty false
  · have reaches := reaches_oriented_endpoints h nonempty true
    change Terminal (lineSkeleton S w h) w.reverse (orientedCore true start)
      (orientedCore true finish) at reaches
    rwa [backwardsStart, backwardsFinish] at reaches
  · exact fun _ reaches => oriented_terminal_word h nonempty false reaches
  · intro word reaches
    rw [← backwardsStart, ← backwardsFinish] at reaches
    exact oriented_terminal_word h nonempty true reaches

end RCDPathValidity

namespace RCDLight.Learning

open RCDPathValidity RelationalFiniteSearch
open OpenCausalScience.ActiveSimplePath (ActiveSuffix Adjacent DConnected)

variable {K A : Type} {S : Schema K} {m : Model K A}

/-- A true dependency is a legal path from its effect's item class to
its cause's class, as in the relational model definition. -/
def Model.typedGroundDependencies (m : Model K A) (S : Schema K) : Prop :=
  ∀ d, m.trueDependency d = true → HasTerminal S d.path ∧
    d.path.head? = some (m.itemClass d.effect) ∧
    d.path.getLast? = some (m.itemClass d.cause)

/-- An edge witnessed at two endpoint instances survives every conditioning
set excluding the respective relational variables, when each endpoint is
reached by only its own word. -/
theorem isolated_ground_edge_is_dependent {g : Skeleton S} {base : g.Item}
    {u v : Variable K A} {x y : GroundVertex m g}
    (xTerm : instantiates g base u x) (yTerm : instantiates g base v y)
    (different : x ≠ y) (edge : Adjacent (groundArrow m g) y x)
    (uniqueLeft : ∀ other, Terminal g other base x.item → other = u.1)
    (uniqueRight : ∀ other, Terminal g other base y.item → other = v.1)
    {conditions : List (Variable K A)} (leftOut : u ∉ conditions) (rightOut : v ∉ conditions) :
    ¬ GroundSeparated m S u v conditions := by
  intro separated
  have leftWitness : ¬ conditionedAt g base conditions x := by
    rintro ⟨other, member, type, term⟩
    have same : other = u := Prod.ext (uniqueLeft _ term) (type.symm.trans xTerm.1)
    exact leftOut (same ▸ member)
  have rightWitness : ¬ conditionedAt g base conditions y := by
    rintro ⟨other, member, type, term⟩
    have same : other = v := Prod.ext (uniqueRight _ term) (type.symm.trans yTerm.1)
    exact rightOut (same ▸ member)
  have connecting : DConnected (groundArrow m g) (conditionedAt g base conditions) y x :=
    ⟨x, [], .last edge, by simp [Ne.symm different]⟩
  exact (separated g base x y xTerm yTerm leftWitness rightWitness).2 connecting

private theorem self_terminal {g : Skeleton S} {item : g.Item} {k : K}
    (present : g.present item) (kind : g.kind item = k) :
    Terminal g [k] item item :=
  ⟨k, [], rfl, present, kind, rfl⟩

private theorem ground_dependency_dependence (typed : m.typedGroundDependencies S)
    (acyclic : m.acyclic) {d : Dependency K A} (trueD : m.trueDependency d = true) :
    (∀ {conditions : List (Variable K A)},
      d.source ∉ conditions → canonical m.itemClass d.effect ∉ conditions →
      ¬ GroundSeparated m S d.source (canonical m.itemClass d.effect) conditions) ∧
    (∀ {conditions : List (Variable K A)},
      d.reverse.source ∉ conditions → canonical m.itemClass d.reverse.effect ∉ conditions →
      ¬ GroundSeparated m S d.reverse.source
        (canonical m.itemClass d.reverse.effect) conditions) := by
  obtain ⟨validPath, effectKind, causeKind⟩ := typed d trueD
  obtain ⟨nonempty, localWord⟩ := has_terminal_iff.mp validPath
  let line := isolatedLine nonempty localWord
  let g := line.skeleton
  let x : GroundVertex m g :=
    ⟨line.finish, d.cause, Option.some.inj (line.finishKind.symm.trans causeKind),
      line.finishPresent⟩
  let y : GroundVertex m g :=
    ⟨line.start, d.effect, Option.some.inj (line.startKind.symm.trans effectKind),
      line.startsPresent⟩
  have xy : groundArrow m g x y := ⟨d.path, by cases d; exact trueD, line.forward⟩
  have different : x ≠ y := by
    intro endpoints
    have same : d.cause = d.effect := congrArg GroundVertex.attr endpoints
    have diagonal : m.classArrow d.effect d.effect := ⟨d.path, by cases d; simp_all⟩
    exact acyclic _ (.single diagonal)
  constructor
  · intro conditions leftOut rightOut
    apply isolated_ground_edge_is_dependent (g := g) (x := x) (y := y)
      (base := line.start) ⟨rfl, line.forward⟩
      ⟨rfl, self_terminal line.startsPresent y.typed⟩ different (.inr xy)
      line.uniqueForward ?_ leftOut rightOut
    intro other atStart
    exact (noncanonical_excludes_base atStart).trans (congrArg (fun k => [k]) y.typed)
  · intro conditions leftOut rightOut
    apply isolated_ground_edge_is_dependent (g := g) (x := y) (y := x)
      (base := line.finish) ⟨rfl, line.backward⟩
      ⟨rfl, self_terminal line.finishPresent x.typed⟩ different.symm (.inl xy)
      line.uniqueBackward ?_ leftOut rightOut
    intro other atFinish
    exact (noncanonical_excludes_base atFinish).trans (congrArg (fun k => [k]) x.typed)

/-- Lemma 1 for both canonical queries used by RCD-Light Phase I. The
witness is a legal finite line with completed relationship tuples. -/
theorem canonical_adjacency_faithfulness_from_ground_oracle
    (typed : m.typedGroundDependencies S) (acyclic : m.acyclic)
    (oracle : GroundOracle m S) : AdjacencyFaithful m := by
  intro d pair conditions leftOut rightOut
  have different : d.source ≠ canonical m.itemClass d.effect := by
    intro same
    have sameClass : d.cause = d.effect := congrArg Prod.snd same
    have loop : m.classArrow d.effect d.effect := by
      rcases pair with forward | backward
      · exact ⟨d.path, by cases d; simp_all⟩
      · exact ⟨d.path.reverse, by cases d; simp_all [Model.query, Dependency.reverse]⟩
    exact acyclic _ (.single loop)
  apply Bool.eq_false_iff.mpr
  intro answered
  have separated :=
    (oracle d.source (canonical m.itemClass d.effect) conditions different leftOut rightOut).mp
      answered
  rcases pair with direct | opposite
  · exact (ground_dependency_dependence typed acyclic direct).1 leftOut rightOut separated
  · have actual : m.trueDependency d.reverse = true := opposite
    obtain ⟨_, backward⟩ := ground_dependency_dependence typed acyclic actual
    exact backward (conditions := conditions)
      (by simpa only [Dependency.reverse_reverse] using leftOut)
      (by simpa only [Dependency.reverse_reverse] using rightOut)
      (by simpa only [Dependency.reverse_reverse] using separated)

theorem learner_to_closure_with_ground_adjacency [DecidableEq K] [DecidableEq A]
    (initial : List (Dependency K A)) (background : ClassFacts A)
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (typed : m.typedGroundDependencies S) (oracle : GroundOracle m S)
    (backgroundSound : background.sound m) (orientationFaithful : OrientationFaithful m) :
    let out := learnToClosure m initial background
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      (∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d) ∧
      classRound (candidateAdjacent (adjacencyPhase m initial)) out.2 = out.2 :=
  learner_to_closure_sound initial background acyclic reverseClosed exhaustive proper oracle
    (canonical_adjacency_faithfulness_from_ground_oracle typed acyclic oracle)
    backgroundSound orientationFaithful (symmetric_oracle_from_ground oracle)

end RCDLight.Learning

end
