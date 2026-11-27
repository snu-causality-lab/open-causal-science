module
public import OpenCausalScience.Graph.ChainMarkov

/-! # LWF ancestral moral separation

Frydenberg (1990), chain-graph global Markov property. Restrict to
ancestral chain components, drop directions and marry the parents of
each component.
-/

namespace OpenCausalScience.Papers.Frydenberg1990.MoralSeparation

open ChainGraph
open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

def relevant (G : ChainGraph n) (query : CIStatement n) (u : Fin n) : Bool :=
  (List.finRange n).any fun v =>
    (query.left v || query.right v || query.given v) &&
      route G.advance (List.finRange n) u v

def adjacent (G : ChainGraph n) (u v : Fin n) : Bool :=
  G.line u v || G.arrow u v || G.arrow v u

def coParents (G : ChainGraph n) (query : CIStatement n) (u v : Fin n) : Bool :=
  (List.finRange n).any fun a =>
    relevant G query a && G.arrow u a &&
      (List.finRange n).any fun b =>
        relevant G query b && G.arrow v b && G.component a b

def retained (G : ChainGraph n) (query : CIStatement n) (u : Fin n) : Bool :=
  relevant G query u && !query.given u

def moralEdge (G : ChainGraph n) (query : CIStatement n) (u v : Fin n) : Bool :=
  retained G query u && retained G query v && u != v &&
    (adjacent G u v || coParents G query u v)

def Connected (G : ChainGraph n) (query : CIStatement n) : Prop :=
  ∃ u v, query.left u = true ∧ query.right v = true ∧
    Reach (fun a b => moralEdge G query a b = true) u v

def separated (G : ChainGraph n) (query : CIStatement n) : Bool :=
  !(List.finRange n).any fun u => query.left u &&
    (List.finRange n).any fun v =>
      query.right v && route (moralEdge G query) (List.finRange n) u v

theorem separated_eq_true_iff (G : ChainGraph n) (query : CIStatement n) :
    separated G query = true ↔ ¬ Connected G query := by
  simp only [separated, Connected, Bool.not_eq_true', Bool.eq_false_iff]
  apply not_congr
  simp [List.any_eq_true, route_iff]

private theorem relevant_of_seed (G : ChainGraph n) (query : CIStatement n) {v : Fin n}
    (seed : (query.left v || query.right v || query.given v) = true) :
    relevant G query v = true := by
  exact List.any_eq_true.mpr ⟨v, List.mem_finRange v,
    Bool.and_eq_true_iff.mpr ⟨seed, (route_iff G.advance v v).mpr (.refl v)⟩⟩

theorem adjacent_never_separated (G : ChainGraph n) {u v : Fin n} (distinct : u ≠ v)
    (edge : adjacent G u v = true) (given : Vertices n)
    (uOpen : given u = false) (vOpen : given v = false) :
    separated G ⟨singleton u, singleton v, given⟩ = false := by
  let query : CIStatement n := ⟨singleton u, singleton v, given⟩
  have uSeed : query.left u = true := by simp [query, ChainGraph.singleton]
  have vSeed : query.right v = true := by simp [query, ChainGraph.singleton]
  have uRetained : retained G query u = true := Bool.and_eq_true_iff.mpr
    ⟨relevant_of_seed G query (by simp [uSeed]), by simp [query, uOpen]⟩
  have vRetained : retained G query v = true := Bool.and_eq_true_iff.mpr
    ⟨relevant_of_seed G query (by simp [vSeed]), by simp [query, vOpen]⟩
  have linked : moralEdge G query u v = true := by
    simp [moralEdge, uRetained, vRetained, distinct, edge]
  apply Bool.eq_false_iff.mpr
  intro blocked
  exact ((separated_eq_true_iff G query).mp blocked)
    ⟨u, v, uSeed, vSeed, .extend (.refl _) linked⟩

def rankBound (G : ChainGraph n) (u v : Fin n) : Nat := max (G.rank u) (G.rank v)

def rankConditioning (G : ChainGraph n) (u v : Fin n) : Vertices n :=
  fun w => w != u && w != v && decide (G.rank w ≤ rankBound G u v)

theorem nonadjacent_rank_separator (G : ChainGraph n) {u v : Fin n} (distinct : u ≠ v)
    (absent : adjacent G u v = false) :
    separated G ⟨singleton u, singleton v, rankConditioning G u v⟩ = true := by
  let query : CIStatement n := ⟨singleton u, singleton v, rankConditioning G u v⟩
  have relevantBound {w : Fin n} (rel : relevant G query w = true) :
      G.rank w ≤ rankBound G u v := by
    obtain ⟨seed, _, checked⟩ := List.any_eq_true.mp rel
    obtain ⟨inSeed, reaches⟩ := Bool.and_eq_true_iff.mp checked
    apply Nat.le_trans (G.rank_le_of_advance ((route_iff _ _ _).mp reaches))
    rcases Bool.or_eq_true_iff.mp inSeed with endpoint | conditioned
    · rcases Bool.or_eq_true_iff.mp endpoint with left | right
      · obtain rfl : seed = u := beq_iff_eq.mp left
        exact Nat.le_max_left _ _
      · obtain rfl : seed = v := beq_iff_eq.mp right
        exact Nat.le_max_right _ _
    · exact of_decide_eq_true (Bool.and_eq_true_iff.mp conditioned).2
  have noCofamily : coParents G query u v = false := by
    apply Bool.eq_false_iff.mpr
    intro pairParents
    obtain ⟨a, _, foundA⟩ := List.any_eq_true.mp pairParents
    obtain ⟨both, foundB⟩ := Bool.and_eq_true_iff.mp foundA
    obtain ⟨relevantA, arrowA⟩ := Bool.and_eq_true_iff.mp both
    obtain ⟨b, _, foundB⟩ := List.any_eq_true.mp foundB
    obtain ⟨requirementsB, same⟩ := Bool.and_eq_true_iff.mp foundB
    have arrowB := (Bool.and_eq_true_iff.mp requirementsB).2
    have level := G.component_rank same
    have aboveU := G.arrow_increases _ _ arrowA
    have aboveV := G.arrow_increases _ _ arrowB
    have bounded := relevantBound relevantA
    unfold rankBound at bounded
    omega
  have noStep (w : Fin n) : ¬ moralEdge G query u w = true := by
    intro hop
    unfold moralEdge at hop
    obtain ⟨both, connected⟩ := Bool.and_eq_true_iff.mp hop
    obtain ⟨retainedPair, neq⟩ := Bool.and_eq_true_iff.mp both
    have kept := (Bool.and_eq_true_iff.mp retainedPair).2
    have neU : w ≠ u := Ne.symm (bne_iff_ne.mp neq)
    have bound := relevantBound (Bool.and_eq_true_iff.mp kept).1
    by_cases neV : w = v
    · subst w
      simp [absent, noCofamily] at connected
    · have forbidden : query.given w = true := by
        simp [query, rankConditioning, neU, neV, bound]
      simp [retained, forbidden] at kept
  apply (separated_eq_true_iff G query).mpr
  rintro ⟨source, target, fromU, toV, route⟩
  have sourceEq : source = u := beq_iff_eq.mp fromU
  have targetEq : target = v := beq_iff_eq.mp toV
  subst source
  subst target
  have onlyU : ∀ w, Reach (fun a b => moralEdge G query a b = true) u w → w = u := by
    intro w reaches
    induction reaches with
    | refl => rfl
    | extend prior hop ih =>
      rw [ih] at hop
      exact (noStep _ hop).elim
  exact distinct (onlyU v route).symm

/-- The LWF separation model determines its skeleton. The proof gives an
explicit distinguisher whenever two chain graphs disagree on adjacency. -/
theorem equal_separations_same_skeleton (G H : ChainGraph n)
    (same : ∀ query, separated G query = separated H query) :
    ∀ u v, u ≠ v → adjacent G u v = adjacent H u v := by
  intro u v distinct
  cases ge : adjacent G u v <;> cases he : adjacent H u v
  · rfl
  · have gTrue := nonadjacent_rank_separator G distinct ge
    have hFalse := adjacent_never_separated H distinct he (rankConditioning G u v)
      (by simp [rankConditioning]) (by simp [rankConditioning])
    rw [same] at gTrue
    rw [hFalse] at gTrue
    contradiction
  · have hTrue := nonadjacent_rank_separator H distinct he
    have gFalse := adjacent_never_separated G distinct ge (rankConditioning H u v)
      (by simp [rankConditioning]) (by simp [rankConditioning])
    rw [same, hTrue] at gFalse
    contradiction
  · rfl

end
end OpenCausalScience.Papers.Frydenberg1990.MoralSeparation
