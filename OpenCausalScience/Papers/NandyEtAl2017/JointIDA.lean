module
public import OpenCausalScience.Papers.MaathuisEtAl2009.LocalIDA

/-! # Nandy, Maathuis and Richardson (2017), joint-IDA

The parent-set support in Algorithm 5.1 comes from independently choosing
collider-free orientations of the undirected chain components. All targets
in the same component must use the same orientation. Theorem 5.1 also
compares multiplicities, which are separate from the set result here.
https://arxiv.org/pdf/1407.2451#page=18
-/

namespace OpenCausalScience.Papers.NandyEtAl2017.JointIDA

open OpenCausalScience.Papers.AnderssonEtAl1997.Characterization
open OpenCausalScience.Papers.AnderssonEtAl1997.Condensation
open OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph
open OpenCausalScience.Papers.MaathuisEtAl2009.LocalIDA
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.VermaPearl1990.Equivalence

@[expose] public section

variable {n k : Nat}

structure ComponentOrientation (G : DAG n) (c : Nat) where
  dag : DAG n
  skeleton : ∀ u v, Adjacent dag u v ↔ (essentialComponents G).adjacency c u v
  noColliders : ∀ u v w, ¬ UnshieldedCollider dag u v w

private noncomputable def restrict (G H : DAG n) (c : Nat) : DAG n where
  edge u v := if label G u = c ∧ label G v = c then H.edge u v else false
  rank := H.rank
  edge_increases u v edge := by
    by_cases within : label G u = c ∧ label G v = c
    · exact H.edge_increases u v (by simpa [within] using edge)
    · simp [within] at edge

private noncomputable def orientationOfExtension {G H : DAG n} (same : SameDConnections G H)
    (c : Nat) : ComponentOrientation G c := by
  have skeleton := sameSkeleton_of_sameDConnections same
  have restrictedSkeleton (u v : Fin n) :
      Adjacent (restrict G H c) u v ↔ (essentialComponents G).adjacency c u v := by
    change Adjacent (restrict G H c) u v ↔ Adjacent G u v ∧ label G u = c ∧ label G v = c
    by_cases within : label G u = c ∧ label G v = c
    · simpa [Adjacent, restrict, within.1, within.2] using (skeleton u v).symm
    · have reverse : ¬ (label G v = c ∧ label G u = c) := fun h => within h.symm
      simp [Adjacent, restrict, within, reverse]
  refine ⟨restrict G H c, restrictedSkeleton, ?_⟩
  intro u v w collider
  obtain ⟨_, hu, hv⟩ := (restrictedSkeleton u v).mp (.inl collider.2.2.1)
  obtain ⟨_, hw, _⟩ := (restrictedSkeleton w v).mp (.inl collider.2.2.2)
  have new : UnshieldedCollider H u v w := by
    refine ⟨collider.1, ?_, ?_, ?_⟩
    · exact fun adj => collider.2.1 ((restrictedSkeleton u w).mpr
        ⟨(skeleton u w).mpr adj, hu, hw⟩)
    · have within : label G u = c ∧ label G v = c := ⟨hu, hv⟩
      simpa only [restrict, ite_eq_left within] using collider.2.2.1
    · have within : label G w = c ∧ label G v = c := ⟨hw, hv⟩
      simpa only [restrict, ite_eq_left within] using collider.2.2.2
  have original := (sameUnshieldedColliders_of_sameDConnections same u v w).mpr new
  have before := (essentialComponents G).fixed_increases u v (collider_arrows_compelled original).1
  exact Nat.ne_of_lt before (hu.trans hv.symm)

private noncomputable def assemble (G : DAG n) (choice : ∀ c, ComponentOrientation G c) : DAG n := by
  let edge (u v : Fin n) :=
    if label G u = label G v then (choice (label G v)).dag.edge u v else G.edge u v
  let localRank (u : Fin n) := (choice (label G u)).dag.rank u
  let isolated : DAG n := ⟨fun _ _ => false, localRank, by simp⟩
  let span := isolated.rankBound
  let rank (u : Fin n) := span * label G u + localRank u
  refine ⟨edge, rank, ?_⟩
  intro u v present
  by_cases within : label G u = label G v
  · have localEdge : (choice (label G v)).dag.edge u v = true := by
      simpa [edge, within] using present
    have ordered := (choice (label G v)).dag.edge_increases _ _ localEdge
    change span * label G u + (choice (label G u)).dag.rank u <
      span * label G v + (choice (label G v)).dag.rank v
    rw [within]
    exact Nat.add_lt_add_left ordered _
  · have oldEdge : G.edge u v = true := by simpa [edge, within] using present
    have reflective : SameDConnections G G := fun _ _ _ => Iff.rfl
    have base := extension_iff_same_d_connections.mpr reflective
    have before := (essentialComponents G).fixed_increases u v
      ((essentialComponents G).fixed_of_edge_between base oldEdge within)
    change label G u < label G v at before
    have mul := Nat.mul_le_mul_left span before
    rw [Nat.mul_succ] at mul
    have bound : localRank u < span := isolated.rank_lt_bound u
    change span * label G u + localRank u < span * label G v + localRank v
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left bound _)
      (Nat.le_trans mul (Nat.le_add_right _ _))

private theorem assembled_edge (G : DAG n) (choice : ∀ c, ComponentOrientation G c)
    (u v : Fin n) :
    (assemble G choice).edge u v =
      if label G u = label G v then (choice (label G v)).dag.edge u v else G.edge u v := rfl

private theorem assembled_skeleton (G : DAG n) (choice : ∀ c, ComponentOrientation G c)
    (u v : Fin n) : Adjacent G u v ↔ Adjacent (assemble G choice) u v := by
  by_cases within : label G u = label G v
  · have shape := (choice (label G v)).skeleton u v
    change Adjacent (choice (label G v)).dag u v ↔
      Adjacent G u v ∧ label G u = label G v ∧ label G v = label G v at shape
    unfold Adjacent
    rw [assembled_edge, assembled_edge, ite_eq_left within, ite_eq_left within.symm, within]
    exact (show Adjacent (choice (label G v)).dag u v ↔ Adjacent G u v by
      simpa [within] using shape).symm
  · have reverse : label G v ≠ label G u := fun h => within h.symm
    simp [Adjacent, assembled_edge, within, reverse]

private theorem assembled_parent {G : DAG n} (choice : ∀ c, ComponentOrientation G c)
    (u v : Fin n) : (assemble G choice).edge u v = true ↔
      Compelled G u v ∨ (choice (label G v)).dag.edge u v = true := by
  rw [assembled_edge]
  by_cases within : label G u = label G v
  · rw [ite_eq_left within]
    refine ⟨Or.inr, fun h => h.resolve_left ?_⟩
    exact fun fixed => Nat.ne_of_lt ((essentialComponents G).fixed_increases u v fixed) within
  · rw [ite_eq_right within]
    have reflective : SameDConnections G G := fun _ _ _ => Iff.rfl
    have base := extension_iff_same_d_connections.mpr reflective
    refine ⟨fun h => .inl ((essentialComponents G).fixed_of_edge_between base h within), ?_⟩
    rintro (fixed | localEdge)
    · exact compelled_in_base fixed
    · exact (within (((choice (label G v)).skeleton u v).mp (.inl localEdge)).2.1).elim

private theorem assembled_equivalent (G : DAG n) (choice : ∀ c, ComponentOrientation G c) :
    SameDConnections G (assemble G choice) := by
  apply same_dConnections_iff_same_signature.mpr
  refine ⟨assembled_skeleton G choice, ?_⟩
  intro u v w
  constructor
  · intro collider
    obtain ⟨left, right⟩ := collider_arrows_compelled collider
    exact ⟨collider.1, fun a => collider.2.1 ((assembled_skeleton G choice u w).mpr a),
      (assembled_parent choice u v).mpr (.inl left), (assembled_parent choice w v).mpr (.inl right)⟩
  · intro collider
    have missing : ¬ Adjacent G u w := fun a => collider.2.1 ((assembled_skeleton G choice u w).mp a)
    obtain left | left := (assembled_parent choice u v).mp collider.2.2.1
    · obtain right | right := (assembled_parent choice w v).mp collider.2.2.2
      · exact ⟨collider.1, missing, compelled_in_base left, compelled_in_base right⟩
      · have within := (((choice (label G v)).skeleton w v).mp (.inl right)).2.1
        have inherited := (essentialComponents G).inherits_parents u v w left within.symm
        exact (missing (.inl (compelled_in_base inherited))).elim
    · have withinU := (((choice (label G v)).skeleton u v).mp (.inl left)).2.1
      obtain right | right := (assembled_parent choice w v).mp collider.2.2.2
      · have inherited := (essentialComponents G).inherits_parents w v u right withinU.symm
        exact (missing (.inr (compelled_in_base inherited))).elim
      · have noLocalAdjacent : ¬ Adjacent (choice (label G v)).dag u w := fun adjacent =>
          missing (((choice (label G v)).skeleton u w).mp adjacent).1
        exact ((choice (label G v)).noColliders u v w
          ⟨collider.1, noLocalAdjacent, left, right⟩).elim

/-- Theorem 5.1, support: targets in one component obtain their parent
sets from one local DAG, and orientations of different components can be
combined with the original compelled parents. -/
theorem joint_parent_support_iff_componentwise (G : DAG n)
    (target : Fin k → Fin n) (parents : Fin k → Fin n → Prop) :
    (∃ H : DAG n, SameDConnections G H ∧ ∀ i, HasParents H (target i) (parents i)) ↔
    ∀ c, ∃ localDag : ComponentOrientation G c,
      ∀ i, label G (target i) = c → ∀ u,
        parents i u ↔ Compelled G u (target i) ∨ localDag.dag.edge u (target i) = true := by
  constructor
  · rintro ⟨H, same, actual⟩ c
    refine ⟨orientationOfExtension same c, ?_⟩
    intro i active u
    have extension := extension_iff_same_d_connections.mpr same
    by_cases within : label G u = c
    · have localEdge : (orientationOfExtension same c).dag.edge u (target i) = H.edge u (target i) := by
        simp [orientationOfExtension, restrict, within, active]
      rw [localEdge, ← actual i u]
      exact ⟨Or.inr, fun h => h.elim (fun fixed => fixed H same) id⟩
    · have localEdge : (orientationOfExtension same c).dag.edge u (target i) = false := by
        simp [orientationOfExtension, restrict, within]
      rw [localEdge, ← actual i u]
      simp only [Bool.false_eq_true, or_false]
      refine ⟨fun edge => (essentialComponents G).fixed_of_edge_between extension edge ?_,
        fun fixed => fixed H same⟩
      exact fun sameLabel => within (sameLabel.trans active)
  · intro perComponent
    let choice (c) := Classical.choose (perComponent c)
    refine ⟨assemble G choice, assembled_equivalent G choice, ?_⟩
    intro i u
    exact (assembled_parent choice u (target i)).trans
      (Classical.choose_spec (perComponent (label G (target i))) i rfl u).symm

namespace Figure2

def one : Fin 3 := 0
def two : Fin 3 := 1
def three : Fin 3 := 2

def figureEdge (intoThreeFromOne intoThreeFromTwo : Bool) (u v : Fin 3) : Bool :=
  (u == one && v == three && intoThreeFromOne) ||
  (u == three && v == one && !intoThreeFromOne) ||
  (u == two && v == three && intoThreeFromTwo) ||
  (u == three && v == two && !intoThreeFromTwo)

def figureRank (intoThreeFromOne intoThreeFromTwo : Bool) (v : Fin 3) : Nat :=
  if v == one then (if intoThreeFromOne then 0 else 2)
  else if v == two then (if intoThreeFromTwo then 0 else 2)
  else 1

def figure (intoThreeFromOne intoThreeFromTwo : Bool) : DAG 3 where
  edge := figureEdge intoThreeFromOne intoThreeFromTwo
  rank := figureRank intoThreeFromOne intoThreeFromTwo
  edge_increases := by cases intoThreeFromOne <;> cases intoThreeFromTwo <;> decide

def fork : DAG 3 := figure false false

def representatives : List (DAG 3) :=
  [figure true false, figure false true, fork, figure true true].filter (signaturesMatch fork)

def parentList (G : DAG 3) (v : Fin 3) : List (Fin 3) :=
  (List.finRange 3).filter (fun u => G.edge u v)

/-- Example 3 has three joint tuples. Projecting onto vertex 1 counts
the parent set `{3}` twice and the empty parent set once. -/
theorem figure2_parent_tuples :
    representatives.map (fun G => (parentList G one, parentList G two)) =
      [([], [three]), ([three], []), ([three], [three])] ∧
    representatives.map (fun G => parentList G one) = [[], [three], [three]] := by decide

theorem each_target_can_have_no_parents :
    (∃ G, SameDConnections fork G ∧ HasParents G one (fun _ => False)) ∧
    (∃ G, SameDConnections fork G ∧ HasParents G two (fun _ => False)) := by
  exact ⟨⟨figure true false, signaturesMatch_iff_same_dConnections.mp (by decide), by
    unfold HasParents
    decide⟩, ⟨figure false true, signaturesMatch_iff_same_dConnections.mp (by decide), by
    unfold HasParents
    decide⟩⟩

theorem no_joint_empty_parents :
    ¬ ∃ G, SameDConnections fork G ∧ HasParents G one (fun _ => False) ∧
      HasParents G two (fun _ => False) := by
  rintro ⟨G, same, noOneParents, noTwoParents⟩
  have skeleton := sameSkeleton_of_sameDConnections same
  have first : G.edge one three = true :=
    ((skeleton one three).mp (Or.inr (by decide))).resolve_right (noOneParents three).mp
  have second : G.edge two three = true :=
    ((skeleton two three).mp (Or.inr (by decide))).resolve_right (noTwoParents three).mp
  have absentInFork : ¬ Adjacent fork one two := by unfold Adjacent; decide
  have missing : ¬ Adjacent G one two := fun adjacent =>
    absentInFork ((skeleton one two).mpr adjacent)
  have collider : UnshieldedCollider G one three two := ⟨by decide, missing, first, second⟩
  have oldCollider := (sameUnshieldedColliders_of_sameDConnections same one three two).mpr collider
  have absentArrow : fork.edge one three ≠ true := by decide
  exact absentArrow oldCollider.2.2.1

end Figure2

end
end OpenCausalScience.Papers.NandyEtAl2017.JointIDA
