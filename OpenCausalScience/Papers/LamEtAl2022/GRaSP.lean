module
public import OpenCausalScience.Discovery.OrderDAG
public import OpenCausalScience.Papers.LamEtAl2022.EdgeCount
public import OpenCausalScience.Papers.LamEtAl2022.Search
public import OpenCausalScience.Papers.LamEtAl2022.Tuck

/-! # Oracle GRaSP on a finite vertex order -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

def eligible (tier : Tier) (G : DAG n) (j k : Fin n) : Bool :=
  G.edge j k && match tier with
    | .covered => (List.finRange n).all fun u => u == j || u == k || (G.edge u j == G.edge u k)
    | .singular => (List.finRange n).all fun u => !(hasDirectedWalk G j u && G.edge u k)
    | .all => true

theorem eligible_eq_true_iff (tier : Tier) (G : DAG n) (j k : Fin n) :
    eligible tier G j k = true ↔ Eligible tier G j k := by
  cases tier with
  | covered =>
    simp only [eligible, Bool.and_eq_true_iff, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true_iff, beq_iff_eq, Eligible]
    constructor
    · rintro ⟨arrow, tests⟩
      refine ⟨arrow, ?_⟩
      intro u uj uk
      exact Bool.eq_iff_iff.mp ((tests u).resolve_left (fun h => h.elim uj uk))
    · intro cov
      refine ⟨cov.arrow, ?_⟩
      intro u
      by_cases uj : u = j
      · exact .inl (.inl uj)
      by_cases uk : u = k
      · exact .inl (.inr uk)
      exact .inr (Bool.eq_iff_iff.mpr (cov.parents u uj uk))
  | singular =>
    simp only [eligible, Eligible, Singular, Bool.and_eq_true_iff, List.all_eq_true, List.mem_finRange,
      true_implies, Bool.not_eq_true', Bool.eq_false_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro test u path arrow
      exact test u (Bool.and_eq_true_iff.mpr ⟨(hasDirectedWalk_iff _ _ _).mpr path, arrow⟩)
    · intro singular u both
      obtain ⟨path, arrow⟩ := Bool.and_eq_true_iff.mp both
      exact singular u ((hasDirectedWalk_iff _ _ _).mp path) arrow
  | all => simp [eligible, Eligible]

def graph (independent : CIOracle n) (order : List (Fin n)) : DAG n :=
  orderDAG order.idxOf independent

def move (tier : Tier) (G : DAG n) (order : List (Fin n)) (j k : Fin n) :
    Option (List (Fin n)) :=
  if eligible tier G j k then
    (OrderSplit.fromOrder? order j k).map fun s => s.tuck true (fun u => hasDirectedWalk G u k)
  else none

def moves (independent : CIOracle n) (tier : Tier) (order : List (Fin n)) : List (List (Fin n)) :=
  (vertexPairs n).filterMap fun (j, k) => move tier (graph independent order) order j k

theorem moves_perm {independent : CIOracle n} {tier : Tier} {start target : List (Fin n)}
    (candidate : target ∈ moves independent tier start) : target.Perm start := by
  obtain ⟨⟨j, k⟩, _, result⟩ := List.mem_filterMap.mp candidate
  change move tier (graph independent start) start j k = some target at result
  unfold move at result
  split at result
  · cases splitResult : OrderSplit.fromOrder? start j k with
    | none => simp [splitResult] at result
    | some s =>
      simp [splitResult] at result
      subst target
      simpa [(OrderSplit.reconstructs_order splitResult).1] using
        s.tuck_perm true (fun u => hasDirectedWalk (graph independent start) u k)
  · simp at result

def graphKey (independent : CIOracle n) (order : List (Fin n)) : List (Fin n × Fin n) :=
  (vertexPairs n).filter fun (u, v) => (graph independent order).edge u v

def improve (independent : CIOracle n) (tier : Tier) (depth : Nat) (start : List (Fin n)) :
    List (Fin n) :=
  Search.descend (moves independent tier) (fun order => (graphKey independent order).length)
    (graphKey independent) depth start

/-- Algorithm 2 initializes each tier with the order returned by its preceding tier. -/
def search (independent : CIOracle n) (depth : Nat) (tier : Tier) (start : List (Fin n)) :
    List (Fin n) :=
  let covered := improve independent .covered depth start
  match tier with
  | .covered => covered
  | .singular => improve independent .singular depth covered
  | .all => improve independent .all depth (improve independent .singular depth covered)

theorem search_perm_and_terminal (independent : CIOracle n) (depth : Nat) (tier : Tier)
    (start : List (Fin n)) :
    let result := search independent depth tier start
    result.Perm start ∧
      Search.firstImprovement (moves independent tier) (fun order => (graphKey independent order).length)
        (graphKey independent) depth [graphKey independent result] result = none := by
  have perm (t : Tier) (order : List (Fin n)) : (improve independent t depth order).Perm order :=
    Search.descend_perm _ _ _ _ _ (fun member => moves_perm member)
  have terminal (t : Tier) (order : List (Fin n)) :=
    (Search.descend_spec (moves independent t) (fun order => (graphKey independent order).length)
      (graphKey independent) depth order).2
  cases tier with
  | covered => exact ⟨perm .covered start, terminal .covered start⟩
  | singular =>
    exact ⟨(perm .singular _).trans (perm .covered start), terminal .singular _⟩
  | all =>
    exact ⟨(perm .all _).trans ((perm .singular _).trans (perm .covered start)), terminal .all _⟩

end

end OpenCausalScience.Papers.LamEtAl2022
