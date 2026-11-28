module
public import OpenCausalScience.Discovery.OrderBoundary
public import OpenCausalScience.Papers.LauritzenEtAl1990.MoralFactorization
public import OpenCausalScience.Papers.RaskuttiUhler2018.Minimality

/-! # Ordered-local and global Markov properties for a DAG

On the ancestral set of a query, moral separation splits the
unconditioned vertices into two sides. Process the relevant variables
in topological order. Each child-parent family has its unconditioned
vertices on one side, so contraction and weak union maintain the
separation statement throughout the induction.
-/

namespace OpenCausalScience.Discovery

open Probability.CI
open OpenCausalScience.Moralization
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
open OpenCausalScience.Papers.LauritzenEtAl1990.MoralFactorization

@[expose] public section

variable {n : Nat}

private theorem union_disjoint {A B C : Mask n} (ac : Disjoint A C) (bc : Disjoint B C) :
    Disjoint (union A B) C := by
  intro v h
  exact (Bool.or_eq_true_iff.mp h).elim (ac v) (bc v)

private theorem subset_union {A B C : Mask n} (ac : Subset A C) (bc : Subset B C) :
    Subset (union A B) C := by
  intro v h
  exact (Bool.or_eq_true_iff.mp h).elim (ac v) (bc v)

private theorem subset_of_disjoint_diff {A B C : Mask n} (ab : Subset A B) (ac : Disjoint A C) :
    Subset A (diff B C) := by
  intro v h
  simp [diff, ab v h, ac v h]

private theorem single_disjoint {x : Fin n} {A : Mask n} (outside : A x = false) :
    Disjoint (single x) A := by
  intro v present
  have same : v = x := by simpa [single] using present
  simpa [same] using outside

private theorem union_comm (A B : Mask n) : union A B = union B A := by
  funext v
  exact Bool.or_comm _ _

/-- Restrict ordered local Markovness to a selected joint block of
predecessors. Additional conditioned predecessors can be included when
they already contain all parents. -/
theorem OrderedLocalMarkov.restrict {G : DAG n} {J : Relation n} {order : Fin n → Nat}
    (semigraphoid : Semigraphoid J) (localMarkov : OrderedLocalMarkov G order J)
    {v : Fin n} {Y B : Mask n} (yEarlier : Subset Y (predecessors order v))
    (bEarlier : Subset B (predecessors order v)) (disj : Disjoint Y B)
    (parents : Subset (fun u => G.edge u v) B) : J (single v) Y B := by
  let U := predecessors order v
  let P : Mask n := fun u => G.edge u v
  have pEarlier : Subset P U := parents.trans bEarlier
  have xOff : Disjoint (single v) U := single_disjoint (by simp [U, predecessors])
  have yOff : Disjoint Y P := disj.restrict_right parents
  have ySub := subset_of_disjoint_diff yEarlier yOff
  have bSub : Subset (diff B P) (diff U P) :=
    subset_of_disjoint_diff ((subset_diff_left B P).trans bEarlier) (disjoint_diff_right B P)
  have jBlocks : Disjoint3 (single v) (diff U P) P :=
    ⟨xOff.restrict_right (subset_diff_left U P), xOff.restrict_right pEarlier, disjoint_diff_right U P⟩
  have narrowed := semigraphoid.decompose_subset jBlocks (subset_union ySub bSub) (localMarkov v)
  have wBlocks : Disjoint4 (single v) Y (diff B P) P :=
    ⟨⟨xOff.restrict_right yEarlier, xOff.restrict_right ((subset_diff_left B P).trans bEarlier),
      disj.restrict_right (subset_diff_left B P)⟩, xOff.restrict_right pEarlier, yOff,
      disjoint_diff_right B P⟩
  have enlarged := semigraphoid.weak_union wBlocks narrowed
  rwa [union_eq_of_subset_diff (show Subset P B from parents)] at enlarged

private def before (order : Fin n → Nat) (k : Nat) (A : Mask n) : Mask n :=
  fun v => A v && decide (order v < k)

private theorem before_subset (order : Fin n → Nat) (k : Nat) (A : Mask n) :
    Subset (before order k A) A := fun _ h => (Bool.and_eq_true_iff.mp h).1

private theorem before_as_predecessors {order : Fin n → Nat} {k : Nat} {v : Fin n}
    (hv : order v = k) (A : Mask n) : Subset (before order k A) (predecessors order v) := by
  intro u h
  simpa [predecessors, hv] using (Bool.and_eq_true_iff.mp h).2

private theorem before_succ_absent {order : Fin n → Nat} {k : Nat}
    (A : Mask n) (absent : ∀ v, order v = k → A v = false) :
    before order (k + 1) A = before order k A := by
  funext v
  by_cases eq : order v = k
  · simp [before, absent v eq]
  · have lt : order v < k + 1 ↔ order v < k := by omega
    simp [before, lt]

private theorem before_succ_insert {order : Fin n → Nat} {k : Nat} {v : Fin n}
    (hv : order v = k) (inj : ∀ u w, order u = order w → u = w)
    (A : Mask n) (present : A v = true) :
    before order (k + 1) A = union (before order k A) (single v) := by
  funext u
  by_cases same : u = v
  · simp [before, union, single, same, hv, present]
  · have ne : order u ≠ k := fun h => same (inj _ _ (h.trans hv.symm))
    have lt : order u < k + 1 ↔ order u < k := by omega
    simp [before, union, single, same, lt]

private theorem before_succ {order : Fin n → Nat} {k : Nat} {v : Fin n}
    (hv : order v = k) (inj : ∀ u w, order u = order w → u = w)
    (A : Mask n) (absent : A v = false) :
    before order (k + 1) A = before order k A :=
  before_succ_absent A (fun u h => by simpa [inj _ _ (h.trans hv.symm)] using absent)

private theorem before_has_parents {G : DAG n} {v : Fin n} {A B : Mask n} {k : Nat}
    (topo : ∀ u w, G.edge u w = true → G.rank u < G.rank w)
    (hv : G.rank v = k) (parents : Subset (fun u => G.edge u v) (union A B)) :
    Subset (fun u => G.edge u v) (union (before G.rank k A) (before G.rank k B)) := by
  intro u arrow
  have earlier : G.rank u < k := by simpa [hv] using topo _ _ arrow
  rcases Bool.or_eq_true_iff.mp (parents u arrow) with left | right
  · simp [union, before, earlier, left]
  · simp [union, before, earlier, right]

private theorem before_right_empty {order : Fin n → Nat} (A : Mask n) :
    before order 0 A = empty := by
  funext u
  simp [before, empty]

private theorem before_covers (order : Fin n → Nat) (A : Mask n)
    (k : Nat) (bound : ∀ v, order v < k) : before order k A = A := by
  funext v
  simp [before, bound v]

private theorem exists_rank_bound (order : Fin n → Nat) : ∃ k, ∀ v, order v < k := by
  let values := (List.finRange n).map order
  have upper : ∀ x ∈ values, x ≤ values.sum := by
    intro x mem
    clear_value values
    induction values with
    | nil => cases mem
    | cons a rest ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp mem with rfl | there
      · omega
      · have := ih there
        omega
  refine ⟨values.sum + 1, fun v => ?_⟩
  have := upper (order v) (List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩)
  omega

private theorem adjoin_to_left {G : DAG n} {J : Relation n}
    (g : Semigraphoid J) (localMarkov : OrderedLocalMarkov G G.rank J)
    {A B C : Mask n} (disj : Disjoint3 A B C)
    (parentsOf : ∀ v, union A (union B C) v = true →
      (A v = false ∧ Subset (fun u => G.edge u v) (union C B)) ∨
      (B v = false ∧ Subset (fun u => G.edge u v) (union C A)))
    (injective : ∀ u v, G.rank u = G.rank v → u = v)
    (k : Nat) :
    J (before G.rank k A) (before G.rank k B) (before G.rank k C) := by
  induction k with
  | zero =>
    simp only [before_right_empty]
    exact g.empty_right _ _
  | succ k ih =>
    by_cases existsVertex : ∃ v, G.rank v = k
    · obtain ⟨v, rank⟩ := existsVertex
      let a := before G.rank k A
      let b := before G.rank k B
      let c := before G.rank k C
      let x := single v
      change J a b c at ih
      have aEarlier := before_as_predecessors rank A
      have bEarlier := before_as_predecessors rank B
      have cEarlier := before_as_predecessors rank C
      have ab : Disjoint a b :=
        (disj.1.restrict_left (before_subset _ _ _)).restrict_right (before_subset _ _ _)
      have ac : Disjoint a c :=
        (disj.2.1.restrict_left (before_subset _ _ _)).restrict_right (before_subset _ _ _)
      have bc : Disjoint b c :=
        (disj.2.2.restrict_left (before_subset _ _ _)).restrict_right (before_subset _ _ _)
      have xa : Disjoint x a := single_disjoint (by simp [a, before, rank])
      have xb : Disjoint x b := single_disjoint (by simp [b, before, rank])
      have xc : Disjoint x c := single_disjoint (by simp [c, before, rank])
      have rotateLeft (parents : Subset (fun u => G.edge u v) (union C A)) :
          J b (union a x) c := by
        have ci : J x b (union c a) :=
          localMarkov.restrict g bEarlier (subset_union cEarlier aEarlier)
            (union_disjoint bc.symm ab).symm (before_has_parents G.edge_increases rank parents)
        exact g.contraction ⟨⟨ab.symm, xb.symm, xa.symm⟩, bc, ac, xc⟩
          (g.symmetry ih) (g.symmetry ci)
      have rotateRight (parents : Subset (fun u => G.edge u v) (union C B)) :
          J a (union b x) c := by
        have ci : J x a (union c b) :=
          localMarkov.restrict g aEarlier (subset_union cEarlier bEarlier)
            (union_disjoint ac.symm ab.symm).symm (before_has_parents G.edge_increases rank parents)
        exact g.contraction ⟨⟨ab, xa.symm, xb.symm⟩, ac, bc, xc⟩ ih (g.symmetry ci)
      by_cases vUsed : union A (union B C) v = true
      · rcases parentsOf v vUsed with ⟨notA, parents⟩ | ⟨notB, parents⟩
        · rw [before_succ rank injective A notA]
          cases vb : B v with
          | true =>
            rw [before_succ_insert rank injective B vb, before_succ rank injective C (disj.2.2 v vb)]
            exact rotateRight parents
          | false =>
            have vc : C v = true := by simpa [union, notA, vb] using vUsed
            rw [before_succ rank injective B vb, before_succ_insert rank injective C vc]
            exact g.weak_union ⟨⟨ab, xa.symm, xb.symm⟩, ac, bc, xc⟩ (rotateRight parents)
        · rw [before_succ rank injective B notB]
          cases va : A v with
          | true =>
            rw [before_succ_insert rank injective A va, before_succ rank injective C (disj.2.1 v va)]
            exact g.symmetry (rotateLeft parents)
          | false =>
            have vc : C v = true := by simpa [union, va, notB] using vUsed
            rw [before_succ rank injective A va, before_succ_insert rank injective C vc]
            exact g.symmetry (g.weak_union ⟨⟨ab.symm, xb.symm, xa.symm⟩, bc, ac, xc⟩
              (rotateLeft parents))
      · have absent : A v = false ∧ B v = false ∧ C v = false := by
          simpa [union] using Bool.eq_false_iff.mpr vUsed
        rw [before_succ rank injective A absent.1, before_succ rank injective B absent.2.1,
          before_succ rank injective C absent.2.2]
        exact ih
    · have none : ∀ v, G.rank v ≠ k := fun v h => existsVertex ⟨v, h⟩
      rw [before_succ_absent A (fun v h => (none v h).elim),
        before_succ_absent B (fun v h => (none v h).elim),
        before_succ_absent C (fun v h => (none v h).elim)]
      exact ih

/-- Ordered-local Markovness entails every graphical separation for a
semigraphoid relation, including joint variable sets at both endpoints. -/
theorem OrderedLocalMarkov.global_independence {G : DAG n} {J : Relation n}
    (g : Semigraphoid J) (localMarkov : OrderedLocalMarkov G G.rank J)
    (distinctRank : ∀ u v, G.rank u = G.rank v → u = v)
    (Q : Query G) (leftOutside : Disjoint Q.left Q.condition.member)
    (rightOutside : Disjoint Q.right Q.condition.member) (separated : ¬ Q.DConnection) :
    J Q.left Q.right Q.condition.member := by
  classical
  let Z : Mask n := Q.condition.member
  let L : Mask n := fun v => (decide (Q.relevant v) && !Z v) && leftSide Q v
  let R : Mask n := fun v => (decide (Q.relevant v) && !Z v) && !leftSide Q v
  have noWalk := (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside).mp separated
  have lr : Disjoint L R := by
    intro v member
    have side : leftSide Q v = true := (Bool.and_eq_true_iff.mp member).2
    simp [R, side]
  have lz : Disjoint L Z := by
    intro v member
    simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp member).1).2
  have rz : Disjoint R Z := by
    intro v member
    simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp member).1).2
  have lSub : Subset Q.left L := by
    intro v hv
    have rel := (Q.relevant_iff v).mpr ⟨v, .inl hv, .inl rfl⟩
    have side := (left_side_iff Q v).mpr ⟨v, hv, .nil _⟩
    simp [L, rel, Z, leftOutside v hv, side]
  have rSub : Subset Q.right R := by
    intro v hv
    have rel := (Q.relevant_iff v).mpr ⟨v, .inr (.inl hv), .inl rfl⟩
    have side : leftSide Q v = false := by
      apply Bool.eq_false_iff.mpr
      rintro onLeft
      obtain ⟨w, source, walk⟩ := (left_side_iff Q v).mp onLeft
      exact noWalk ⟨w, v, source, hv, walk⟩
    simp [R, rel, Z, rightOutside v hv, side]
  have parentPart : ∀ v, union L (union R Z) v = true →
      (L v = false ∧ Subset (fun u => G.edge u v) (union Z R)) ∨
      (R v = false ∧ Subset (fun u => G.edge u v) (union Z L)) := by
    intro v present
    have rel : Q.relevant v := by
      rcases Bool.or_eq_true_iff.mp present with l | r
      · exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp l).1).1
      · rcases Bool.or_eq_true_iff.mp r with r | z
        · exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp r).1).1
        · exact (Q.relevant_iff v).mpr ⟨v, .inr (.inr z), .inl rfl⟩
    cases own : owner Q v
    · refine .inl ⟨?_, ?_⟩
      · cases inside : Z v
        · have side := (family_has_one_side Q v v rel (.inl rfl) inside).trans own
          simp [L, side]
        · simp [L, inside]
      · intro u hp
        cases inside : Z u
        · have side := (family_has_one_side Q v u rel (.inr hp) inside).trans own
          simp [union, R, inside, side, parent_is_relevant hp rel]
        · simp [union, inside]
    · refine .inr ⟨?_, ?_⟩
      · cases inside : Z v
        · have side := (family_has_one_side Q v v rel (.inl rfl) inside).trans own
          simp [R, side]
        · simp [R, inside]
      · intro u hp
        cases inside : Z u
        · have side := (family_has_one_side Q v u rel (.inr hp) inside).trans own
          simp [union, L, inside, side, parent_is_relevant hp rel]
        · simp [union, inside]
  obtain ⟨k, bound⟩ := exists_rank_bound G.rank
  have collect := adjoin_to_left g localMarkov ⟨lr, lz, rz⟩ parentPart distinctRank k
  rw [before_covers _ L _ bound, before_covers _ R _ bound, before_covers _ Z _ bound] at collect
  have narrowRight := g.decompose_subset ⟨lr, lz, rz⟩ rSub collect
  have narrowLeft := g.decompose_subset ⟨(lr.restrict_right rSub).symm, rz.restrict_left rSub, lz⟩
    lSub (g.symmetry narrowRight)
  exact g.symmetry narrowLeft

/-- The Markov implication for the ordered graph, using the paper's
graphoid assumptions and an oracle matching the singleton queries. -/
theorem induced_order_is_markov {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (order : Fin n → Nat)
    (distinctRank : ∀ u v, order u = order v → u = v) :
    Papers.RaskuttiUhler2018.IsMarkov (orderDAG order independent) independent := by
  intro x y Z distinct xOutside yOutside separated
  let Q : Query (orderDAG order independent) :=
    ⟨single x, single y, Conditioning.ofPredicate _ Z⟩
  have lDisj : Disjoint Q.left Q.condition.member := single_disjoint xOutside
  have rDisj : Disjoint Q.right Q.condition.member := single_disjoint yOutside
  have noD := (Q.dagMoralSeparated_eq_true_iff lDisj rDisj).mp separated
  apply (agrees x y Z distinct xOutside yOutside).mpr
  exact (order_dag_ordered_local g agrees order).global_independence g.toSemigraphoid
    distinctRank Q lDisj rDisj noD

/-- Theorem 3.5 of Lam et al. and the graph-level form of Lemma 2.1
of Raskutti and Uhler. The order graph is an I-map and no proper
edge-subgraph is an I-map for the same oracle. -/
theorem induced_order_sgs_minimal {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (order : Fin n → Nat)
    (distinctRank : ∀ u v, order u = order v → u = v) :
    Papers.RaskuttiUhler2018.IsMarkov (orderDAG order independent) independent ∧
      ∀ H : DAG n, (∀ u v, H.edge u v = true → (orderDAG order independent).edge u v = true) →
        Papers.RaskuttiUhler2018.IsMarkov H independent →
        H.edge = (orderDAG order independent).edge :=
  ⟨induced_order_is_markov g agrees order distinctRank, fun _ sub markov =>
    Papers.RaskuttiUhler2018.markov_subgraph_edges_eq order distinctRank sub markov⟩

end

end OpenCausalScience.Discovery
