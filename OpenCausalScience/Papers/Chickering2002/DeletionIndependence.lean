module
public import OpenCausalScience.Papers.Chickering2002.IndependenceMap
public import OpenCausalScience.Discovery.OrderedMarkov

/-! The parent-set CI test for a backward deletion from an I-map. -/

namespace OpenCausalScience.Papers.Chickering2002

open Discovery Probability.CI RaskuttiUhler2018 Moralization
open VermaPearl1990.DAGEquivalence VermaPearl1990.Equivalence
open KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat} {J : Relation n} {independent : CIOracle n}

private theorem no_self_arrow (G : DAG n) (x : Fin n) : G.edge x x = false :=
  Bool.eq_false_iff.mpr fun e => G.no_directed_cycle x (.single e)

private theorem single_disjoint {x : Fin n} {A : Mask n} (out : A x = false) :
    Disjoint (single x) A := by
  intro v hv
  have eq : v = x := beq_iff_eq.mp hv
  subst v
  exact out

theorem ordered_local_of_markov {G : DAG n} (g : Graphoid J) (agrees : MatchesOracle J independent)
    (order : Fin n → Nat) (unique : ∀ u v, order u = order v → u = v)
    (topo : ∀ u v, G.edge u v = true → order u < order v) (markov : IsMarkov G independent) :
    OrderedLocalMarkov G order J := by
  intro v
  let U := predecessors order v
  let P := fun w => G.edge w v
  have vOutside : U v = false := by simp [U, predecessors]
  have subset : Subset P U := fun w hw => decide_eq_true (topo w v hw)
  have parents : diff U (diff U P) = P := by
    funext w
    cases h : P w
    · simp [diff, h]
    · simp [diff, h, subset w h]
  have localCI : J (single v) (diff U P) (diff U (diff U P)) := by
    apply joint_of_singleton_exclusions g (single_disjoint vOutside) (subset_diff_left U P)
    intro w mem
    obtain ⟨pred, absent⟩ := Bool.and_eq_true_iff.mp mem
    have earlier : order w < order v := of_decide_eq_true pred
    have distinct : v ≠ w := by
      intro equal
      subst w
      exact (Nat.lt_irrefl _) earlier
    have missing : G.edge w v = false := by simpa [P] using absent
    have condEq : diff U (single w) = predecessorsExcept order w v := by
      rfl
    have sep : graphOracle G v w (diff U (single w)) = true := by
      rw [condEq, graphOracle_predecessors_eq_not_edge order unique topo earlier, missing]
      rfl
    have wOut : diff U (single w) w = false := by simp [diff, single]
    have vOut : diff U (single w) v = false := by simp [diff, vOutside]
    exact (agrees v w _ distinct vOut wOut).mp (markov v w _ distinct vOut wOut sep)
  simpa only [parents] using localCI

theorem markov_of_ordered_local {G : DAG n} (g : Semigraphoid J) (agrees : MatchesOracle J independent)
    (order : Fin n → Nat) (unique : ∀ u v, order u = order v → u = v)
    (topo : ∀ u v, G.edge u v = true → order u < order v) (ordered : OrderedLocalMarkov G order J) :
    IsMarkov G independent := by
  let H : DAG n := ⟨G.edge, order, topo⟩
  have same : SameDConnections G H := same_dConnections_of_edge_eq rfl
  intro x y c distinct hx hy sep
  let Q : Query H := ⟨single x, single y, Conditioning.ofPredicate H c⟩
  have noConnection : ¬ Q.DConnection := by
    rintro ⟨u, v, hu, hv, connection⟩
    have equalU : u = x := beq_iff_eq.mp hu
    have equalV : v = y := beq_iff_eq.mp hv
    subst u
    subst v
    exact (graphOracle_eq_true_iff G x y c hx hy).mp sep ((same c x y).mpr connection)
  exact (agrees x y c distinct hx hy).mpr
    (OrderedLocalMarkov.global_independence g (G := H) ordered unique Q
      (single_disjoint hx) (single_disjoint hy) noConnection)

theorem deletion_markov_iff_parent_independence {G : DAG n} {u v : Fin n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (markov : IsMarkov G independent)
    (edge : G.edge u v = true) :
    IsMarkov (G.deleteArrow u v) independent ↔
      J (single v) (single u) (fun w => (G.deleteArrow u v).edge w v) := by
  let H := G.deleteArrow u v
  let P : Mask n := fun w => H.edge w v
  have noU : P u = false := by simp [P, H, DAG.deleteArrow]
  have noV : P v = false := no_self_arrow H v
  have distinct : v ≠ u := by
    intro same
    subst v
    exact G.no_directed_cycle _ (.single edge)
  constructor
  · intro remains
    have separated : graphOracle H v u P = true := by
      apply (graphOracle_eq_true_iff H v u P noV noU).mpr
      apply parents_dSeparate distinct (Bool.eq_false_iff.mp noU)
      intro walk
      have a := H.rank_lt_of_directedWalk walk
      have b := G.edge_increases _ _ edge
      change G.rank v < G.rank u at a
      exact Nat.lt_asymm a b
    exact (agrees v u P distinct noV noU).mp (remains _ _ _ distinct noV noU separated)
  · intro test
    let order := (topologicalOrder G).idxOf
    have unique := idxOf_injective (topological_order_perm G)
    have topo := topological_order_increases G
    have first := ordered_local_of_markov g agrees order unique topo markov
    have topoH (a b : Fin n) (e : H.edge a b = true) : order a < order b :=
      topo a b ((Bool.and_eq_true_iff.mp e).1)
    apply markov_of_ordered_local g.toSemigraphoid agrees order unique topoH
    intro z
    by_cases atTarget : z = v
    · subst z
      let U := predecessors order v
      let old := fun w => G.edge w v
      let rest := diff U old
      have pre : U u = true := decide_eq_true (topo u v edge)
      have out : U v = false := by simp [U, predecessors]
      have oldEq : old = union P (single u) := by
        funext w
        by_cases same : w = u
        · subst w
          simp [old, union, single, edge]
        · have different : (w == u) = false := Bool.eq_false_iff.mpr (fun h => same (beq_iff_eq.mp h))
          simp [old, union, single, P, H, DAG.deleteArrow, different]
      have restEq : diff U P = union (single u) rest := by
        funext w
        by_cases same : w = u
        · subst w
          simp [diff, union, single, pre, noU]
        · have different : (w == u) = false := Bool.eq_false_iff.mpr (fun h => same (beq_iff_eq.mp h))
          simp [diff, union, single, rest, old, P, H, DAG.deleteArrow, different]
      have notRest : rest v = false := by simp [rest, diff, out]
      have uNotRest : rest u = false := by simp [rest, diff, old, edge]
      have restNotP : Disjoint rest P := by
        intro w mem
        have notOld : old w = false := by simpa using (Bool.and_eq_true_iff.mp mem).2
        rw [oldEq] at notOld
        exact (Bool.or_eq_false_iff.mp notOld).1
      change J (single v) (diff U P) P
      rw [restEq]
      apply g.contraction ⟨⟨single_disjoint (by simp [single, distinct]), single_disjoint notRest,
        single_disjoint uNotRest⟩, single_disjoint noV, single_disjoint noU, restNotP⟩ test
      have before := first v
      change J (single v) rest old at before
      rwa [oldEq] at before
    · have same : (fun w => H.edge w z) = (fun w => G.edge w z) := by
        funext w
        simp [H, DAG.deleteArrow, atTarget]
      rw [same]
      exact first z

end

end OpenCausalScience.Papers.Chickering2002
