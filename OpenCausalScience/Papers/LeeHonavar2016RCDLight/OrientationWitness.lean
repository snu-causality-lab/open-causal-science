module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.ThreeArm
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.BoundedCandidates
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.GroundTriple

/-! Lee and Honavar, AAAI 2016, Lemma 2 for the canonical-flank representatives of RCD-Light. -/

@[expose] public section

namespace RCDPathValidity

open RCDThreeArm
open RCDLemma5 (Local Splice)

variable {K : Type} {S : Schema K}

structure SpliceRealization (S : Schema K) (centerWord dependency flank : List K) where
  skeleton : Skeleton S
  left : skeleton.Item
  middle : skeleton.Item
  right : skeleton.Item
  left_middle : Terminal skeleton centerWord left middle
  middle_left : Terminal skeleton centerWord.reverse middle left
  middle_right : Terminal skeleton dependency middle right
  right_middle : Terminal skeleton dependency.reverse right middle
  left_right : Terminal skeleton flank left right
  unique_word : ∀ {u p q}, Terminal skeleton p left u → Terminal skeleton q left u → p = q

/-- A valid pivot splice is realized by one legal skeleton for all of its traversals. -/
theorem realize_splice {q d r : List K} (splice : Splice q d r)
    (qValid : Local S.adj S.retrace q) (dValid : Local S.adj S.retrace d)
    (rValid : Local S.adj S.retrace r) : Nonempty (SpliceRealization S q d r) := by
  cases splice with
  | atPivot before overlap after v =>
    let rays : Arm → List K := fun | .x => before.reverse | .y => overlap.reverse | .z => after
    have legal : LegalArms v rays S := legal_of_splice before overlap after v qValid dValid rValid
    let g := RCDThreeArm.skeleton v rays legal
    have xy := terminal_between_tips v rays legal .x .y (by decide)
    have yx := terminal_between_tips v rays legal .y .x (by decide)
    have yz := terminal_between_tips v rays legal .y .z (by decide)
    have zy := terminal_between_tips v rays legal .z .y (by decide)
    have xz := terminal_between_tips v rays legal .x .z (by decide)
    refine ⟨⟨g, .inl (tip rays .x), .inl (tip rays .y), .inl (tip rays .z), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [rays, List.reverse_reverse] using xy
    · simpa only [rays, List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append] using yx
    · simpa only [rays, List.reverse_reverse] using yz
    · simpa only [rays, List.reverse_append, List.reverse_cons, List.append_assoc,
        List.singleton_append] using zy
    · simpa only [rays, List.reverse_reverse] using xz
    · exact terminal_word_unique v rays legal .x

/-- Terminal classes and presence at the two ends of a bridge-burning traversal. -/
theorem terminal_ends {g : Skeleton S} {w : List K} {b f : g.Item}
    (h : Terminal g w b f) :
    w.head? = some (g.kind b) ∧ w.getLast? = some (g.kind f) ∧ g.present b ∧ g.present f := by
  obtain ⟨tr, chain, labels, lastItem, distinct⟩ := trace_of_terminal h
  have basePresent : g.present b := by
    obtain ⟨_,_,_,present,_,_⟩ := h
    exact present
  refine ⟨?_, ?_, basePresent, ?_⟩
  · rw [← labels]
    rfl
  · rw [← labels, List.getLast?_map, lastItem]
    rfl
  · clear h labels distinct
    induction tr generalizing b with
    | nil =>
      have eq : b = f := Option.some.inj lastItem
      exact eq ▸ basePresent
    | cons next tr ih =>
      exact ih chain.2 (by simpa using lastItem) (g.endpoints_present chain.1).2

end RCDPathValidity

namespace RCDLight.Learning

open RCDPathValidity
open RCDLemma5 (Local Splice splice_iff splice_canonicality splice_triangle local_reverse)
open OpenCausalScience.ActiveSimplePath (Adjacent)

variable {K A : Type} {S : Schema K} {m : Model K A}

private theorem canonical_arm_dependency {t : Triple K A} (rep : Representative m t) :
    m.trueDependency ⟨t.middle.1.reverse, t.leftAttribute, t.middle.2⟩ = true ∨
      m.trueDependency ⟨t.middle.1, t.middle.2, t.leftAttribute⟩ = true := by
  rcases rep.leftArm with forward | backward
  · obtain ⟨_,d,dep,join⟩ := forward
    have exactWord := splice_canonicality (splice_iff.mpr join) rfl
    exact .inl (exactWord ▸ dep)
  · obtain ⟨_,d,dep,i,pivot,joined⟩ := backward
    have one : i = 1 := by
      have lower := pivot.1
      have upper : i ≤ 1 := by simpa [Triple.left, canonical] using pivot.2.1
      omega
    have eq : d = t.middle.1 := by simpa [joinAt, one, Triple.left, canonical] using joined
    exact .inr (eq ▸ dep)

private theorem right_arm_dependency {t : Triple K A} (rep : Representative m t) :
    ∃ d, Splice t.middle.1 d t.right.1 ∧
      (m.trueDependency ⟨d,t.right.2,t.middle.2⟩ = true ∨
        m.trueDependency ⟨d.reverse,t.middle.2,t.right.2⟩ = true) := by
  rcases rep.rightArm with forward | backward
  · obtain ⟨_,d,dep,join⟩ := forward
    exact ⟨d.reverse, splice_triangle (splice_iff.mpr join), .inr (by simpa using dep)⟩
  · obtain ⟨_,d,dep,join⟩ := backward
    exact ⟨d, splice_iff.mpr join, .inl dep⟩

private theorem ground_has_class_arrow {g : Skeleton S} {x y : GroundVertex m g}
    (arrow : groundArrow m g x y) : m.classArrow x.attr y.attr := by
  obtain ⟨p,d,_⟩ := arrow
  exact ⟨p,d⟩

private theorem ground_and_unrolled_agree {g : Skeleton S}
    {x y : GroundVertex m g} {p q : Variable K A}
    (xAttr : x.attr = p.2) (yAttr : y.attr = q.2) (acyclic : m.acyclic)
    (groundAdj : Adjacent (groundArrow m g) x y) (liftedAdj : m.unrolledAdjacent p q) :
    groundArrow m g x y ↔ m.unrolled p q := by
  constructor
  · intro forward
    rcases liftedAdj with yes | backward
    · exact yes
    · have right := m.unrolled_has_class_arrow backward
      have left : m.classArrow p.2 q.2 := by simpa only [xAttr,yAttr] using ground_has_class_arrow forward
      exact (acyclic p.2 (.extend (.single left) right)).elim
  · intro forward
    rcases groundAdj with yes | backward
    · exact yes
    · have left := m.unrolled_has_class_arrow forward
      have right : m.classArrow q.2 p.2 := by simpa only [xAttr,yAttr] using ground_has_class_arrow backward
      exact (acyclic p.2 (.extend (.single left) right)).elim

private theorem ground_adjacency_attributes_distinct {g : Skeleton S} {p q : GroundVertex m g}
    (acyclic : m.acyclic) (adj : Adjacent (groundArrow m g) p q) : p ≠ q := by
  intro eq
  subst q
  have loop := adj.elim ground_has_class_arrow ground_has_class_arrow
  exact acyclic p.attr (.single loop)

/-- The two orientation-faithfulness tests hold for every canonical-flank
representative, with no restriction on the other variables in the separator. -/
theorem representative_orientation_faithfulness (typed : m.typedGroundDependencies S)
    (pathSemantics : ∀ p, m.validPath p → HasTerminal S p)
    (acyclic : m.acyclic) (oracle : GroundOracle m S) : OrientationFaithful m := by
  intro t rep conditions leftOut rightOut active
  have leftDep := canonical_arm_dependency rep
  obtain ⟨d, splice, rightDep⟩ := right_arm_dependency rep
  have qValid := (has_terminal_iff.mp (pathSemantics _ rep.middleValid)).2
  have rValid := (has_terminal_iff.mp (pathSemantics _ rep.rightValid)).2
  have dValid : Local S.adj S.retrace d := by
    rcases rightDep with direct | reverse
    · exact (has_terminal_iff.mp (typed _ direct).1).2
    · have rev := (has_terminal_iff.mp (typed _ reverse).1).2
      simpa only [List.reverse_reverse] using local_reverse S.symm rev
  obtain ⟨realization⟩ := realize_splice splice qValid dValid rValid
  let g := realization.skeleton
  have baseKind : g.kind realization.left = m.itemClass t.leftAttribute :=
    Option.some.inj ((terminal_ends realization.left_right).1.symm.trans rep.rightBase)
  have qEnd : t.middle.1.getLast? = some (m.itemClass t.middle.2) := by
    rcases leftDep with intoMiddle | outOfMiddle
    · simpa only [List.head?_reverse] using (typed _ intoMiddle).2.1
    · exact (typed _ outOfMiddle).2.2
  have dEnd : d.getLast? = some (m.itemClass t.right.2) := by
    rcases rightDep with intoMiddle | outOfMiddle
    · exact (typed _ intoMiddle).2.2
    · simpa only [List.head?_reverse] using (typed _ outOfMiddle).2.1
  have middleKind : g.kind realization.middle = m.itemClass t.middle.2 :=
    Option.some.inj ((terminal_ends realization.left_middle).2.1.symm.trans qEnd)
  have rightKind : g.kind realization.right = m.itemClass t.right.2 :=
    Option.some.inj ((terminal_ends realization.middle_right).2.1.symm.trans dEnd)
  let x : GroundVertex m g := ⟨realization.left, t.leftAttribute, baseKind,
    (terminal_ends realization.left_middle).2.2.1⟩
  let y : GroundVertex m g := ⟨realization.middle, t.middle.2, middleKind,
    (terminal_ends realization.left_middle).2.2.2⟩
  let z : GroundVertex m g := ⟨realization.right, t.right.2, rightKind,
    (terminal_ends realization.left_right).2.2.2⟩
  have self : Terminal g (t.left m).1 realization.left realization.left :=
    ⟨m.itemClass t.leftAttribute, [], rfl, x.present, baseKind, rfl⟩
  have tLeft : instantiates g realization.left (t.left m) x := ⟨rfl, self⟩
  have tMiddle : instantiates g realization.left t.middle y := ⟨rfl, realization.left_middle⟩
  have tRight : instantiates g realization.left t.right z := ⟨rfl, realization.left_right⟩
  have xy : Adjacent (groundArrow m g) x y := by
    rcases leftDep with intoMiddle | outOfMiddle
    · exact .inl ⟨t.middle.1.reverse,intoMiddle,realization.middle_left⟩
    · exact .inr ⟨t.middle.1,outOfMiddle,realization.left_middle⟩
  have zy : Adjacent (groundArrow m g) z y := by
    rcases rightDep with intoMiddle | outOfMiddle
    · exact .inl ⟨d,intoMiddle,realization.middle_right⟩
    · exact .inr ⟨d.reverse,outOfMiddle,realization.right_middle⟩
  have sameCollider : t.collider m ↔ groundArrow m g x y ∧ groundArrow m g z y := by
    have left := ground_and_unrolled_agree (m := m) (x := x) (y := y) rfl rfl acyclic xy rep.leftArm
    have right := ground_and_unrolled_agree (m := m) (x := z) (y := y) rfl rfl acyclic zy rep.rightArm.symm
    exact ⟨fun h => ⟨left.mpr h.1, right.mpr h.2⟩,
      fun h => ⟨left.mp h.1, right.mp h.2⟩⟩
  have xz : x ≠ z := by
    intro same
    have sameItem : realization.left = realization.right := congrArg GroundVertex.item same
    have sameAttr : t.leftAttribute = t.right.2 := congrArg GroundVertex.attr same
    have sameWord : (t.left m).1 = t.right.1 := by
      apply realization.unique_word self
      exact sameItem.symm ▸ realization.left_right
    exact rep.leftRightDistinct (Prod.ext sameWord sameAttr)
  have dependent := isolated_ground_triple_is_dependent tLeft tMiddle tRight
    (ground_adjacency_attributes_distinct acyclic xy)
    (fun eq => ground_adjacency_attributes_distinct acyclic zy eq.symm) xz xy zy sameCollider
    (fun _ other => realization.unique_word other self)
    (fun _ other => realization.unique_word other realization.left_middle)
    (fun _ other => realization.unique_word other realization.left_right)
    leftOut rightOut active
  exact Bool.eq_false_iff.mpr fun independent => dependent
    ((oracle (t.left m) t.right conditions rep.leftRightDistinct leftOut rightOut).mp independent)

/-- The finite RCD-Light learner recovers the undirected dependencies and makes only
sound arrow decisions with an exact relational d-separation oracle. -/
theorem bounded_learner_sound_from_ground_oracle [DecidableEq K] [DecidableEq A]
    (S : Schema K) [DecidableRel S.role] [DecidableRel S.many] (m : Model K A)
    {classes : List K} {attributes : List A} (maximumHops : Nat) (background : ClassFacts A)
    (coversClasses : ∀ c, c ∈ classes) (coversAttributes : ∀ a, a ∈ attributes)
    (pathSemantics : ∀ p, m.validPath p ↔ HasTerminal S p)
    (typed : m.typedGroundDependencies S) (acyclic : m.acyclic)
    (hopBound : ∀ d, m.trueDependency d = true → d.path.length ≤ maximumHops + 1)
    (oracle : GroundOracle m S) (backgroundSound : background.sound m) :
    let initial := boundedDependencies S m.itemClass classes attributes maximumHops
    let out := learnBounded S m classes attributes maximumHops background
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      (∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔
        RelationalFiniteSearch.pairPresent m.query m.trueDependency d) ∧
      classRound (candidateAdjacent (adjacencyPhase m initial)) out.2 = out.2 :=
  bounded_learner_sound S m maximumHops background coversClasses coversAttributes pathSemantics typed
    acyclic hopBound oracle backgroundSound
    (representative_orientation_faithfulness typed (fun p => (pathSemantics p).mp) acyclic oracle)

end RCDLight.Learning

end
