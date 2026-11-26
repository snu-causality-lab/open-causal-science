module
public import OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence

/-! Kocaoglu, Dimakis and Vishwanath (2017), the finite graph version
of Theorem 1. Perfect interventions are represented by their cut DAGs.

https://proceedings.mlr.press/v70/kocaoglu17a/kocaoglu17a.pdf -/

namespace OpenCausalScience.Papers.KocaogluEtAl2017.SeparatingDesign

open OpenCausalScience.Papers.Chickering1995.CoveredReversal
open OpenCausalScience.Papers.Chickering1995.Transformation
open OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.VermaPearl1990.Equivalence

@[expose] public section

variable {n : Nat}

/-- The design separates every edge of the given skeleton. Only the
adjacencies of `base` are used. -/
def SeparatesSkeleton (base : DAG n) (targets : List (Target n)) : Prop :=
  ∀ u v, Adjacent base u v → ∃ target ∈ targets, target u ≠ target v

/-- The supplied perfect-intervention signatures distinguish every
pair of DAG orientations of a fixed labelled skeleton. The observational
signature is available as well. -/
def IdentifiesEveryOrientation (base : DAG n) (targets : List (Target n)) : Prop :=
  ∀ G H, SameSkeleton base G → SameSkeleton base H → SameDConnections G H →
    (∀ target ∈ targets, SameDConnections (cutIncoming G target) (cutIncoming H target)) →
    G.edge = H.edge

private theorem identifies_of_separates {base : DAG n} {targets : List (Target n)}
    (separates : SeparatesSkeleton base targets) : IdentifiesEveryOrientation base targets := by
  intro G H skG skH _ same
  have shared : SameSkeleton G H := fun u v => (skG u v).symm.trans (skH u v)
  funext u v
  apply Bool.eq_iff_iff.mpr
  by_cases edge : Adjacent base u v
  · obtain ⟨target, member, separated⟩ := separates u v edge
    have cuts := sameSkeleton_of_sameDConnections (same target member)
    exact ((cut_skeleton_iff_crossing_directions target shared).mp cuts) u v separated
  · exact iff_of_false (fun h => edge ((skG u v).mpr (.inl h)))
      (fun h => edge ((skH u v).mpr (.inl h)))

private def firstPairRank (a b v : Fin n) : Nat :=
  if v = a then 0 else if v = b then 1 else v.val + 2

private theorem first_pair_rank_eq_implies_eq {a b x y : Fin n} (distinct : a ≠ b)
    (equal : firstPairRank a b x = firstPairRank a b y) : x = y := by
  by_cases xa : x = a
  · subst x
    by_cases ya : y = a
    · exact ya.symm
    · by_cases yb : y = b
      · simp [firstPairRank, distinct.symm, yb] at equal
      · simp [firstPairRank, ya, yb] at equal
  · by_cases xb : x = b
    · subst x
      by_cases ya : y = a
      · simp [firstPairRank, distinct.symm, ya] at equal
      · by_cases yb : y = b
        · exact yb.symm
        · simp [firstPairRank, distinct.symm, ya, yb] at equal
    · by_cases ya : y = a
      · simp [firstPairRank, xa, xb, ya] at equal
      · by_cases yb : y = b
        · simp [firstPairRank, distinct.symm, xa, xb, yb] at equal
        · apply Fin.ext
          simpa [firstPairRank, xa, xb, ya, yb] using equal

private def withFirstPair (base : DAG n) (a b : Fin n) : DAG n where
  edge u v := adjacentTest base u v && decide (firstPairRank a b u < firstPairRank a b v)
  rank := firstPairRank a b
  edge_increases _ _ edge := of_decide_eq_true (Bool.and_eq_true_iff.mp edge).2

private theorem first_pair_edge_iff {base : DAG n} {a b x y : Fin n} :
    (withFirstPair base a b).edge x y = true ↔
      Adjacent base x y ∧ firstPairRank a b x < firstPairRank a b y := by
  change (adjacentTest base x y && decide (_ < _)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, adjacentTest, Bool.or_eq_true]
  rfl

private theorem first_pair_same_skeleton (base : DAG n) {a b : Fin n} (distinct : a ≠ b) :
    SameSkeleton base (withFirstPair base a b) := by
  intro x y
  constructor
  · intro adj
    have different : x ≠ y := by
      intro equal
      subst y
      exact base.no_directed_cycle x (.single (adj.elim id id))
    have rankNe : firstPairRank a b x ≠ firstPairRank a b y :=
      fun equal => different (first_pair_rank_eq_implies_eq distinct equal)
    rcases Nat.lt_or_gt_of_ne rankNe with smaller | greater
    · exact .inl (first_pair_edge_iff.mpr ⟨adj, smaller⟩)
    · exact .inr (first_pair_edge_iff.mpr ⟨Or.symm adj, greater⟩)
  · intro adj
    exact adj.elim (fun e => (first_pair_edge_iff.mp e).1)
      (fun e => Or.symm (first_pair_edge_iff.mp e).1)

private theorem first_pair_is_covered (base : DAG n) {a b : Fin n} (distinct : a ≠ b) :
    ∀ x, x ≠ a → x ≠ b →
      ((withFirstPair base a b).edge x a = true ↔ (withFirstPair base a b).edge x b = true) := by
  intro x xa xb
  simp [first_pair_edge_iff, firstPairRank, distinct.symm, xa, xb]

private theorem crossing_directions_of_unseparated_reversal {G H : DAG n} {a b : Fin n}
    (R : Reversal G H a b) (target : Target n) (same : target a = target b) :
    SameCrossingDirections target G H :=
  fun _ _ separated => R.unchanged _ _
    (by rintro ⟨rfl, rfl⟩; exact separated same)
    (by rintro ⟨rfl, rfl⟩; exact separated same.symm)

/-- If an edge is never separated, orienting its endpoints first
makes its reversal observationally and interventionally indistinguishable. -/
theorem unseparated_edge_has_indistinguishable_orientations
    {base : DAG n} {targets : List (Target n)} {a b : Fin n}
    (edge : Adjacent base a b) (unseparated : ∀ t ∈ targets, t a = t b) :
    ∃ G H : DAG n, SameSkeleton base G ∧ SameSkeleton base H ∧ SameDConnections G H ∧
      (∀ t ∈ targets, SameDConnections (cutIncoming G t) (cutIncoming H t)) ∧
      G.edge a b = true ∧ H.edge b a = true := by
  have distinct : a ≠ b := by
    intro equal
    subst b
    exact base.no_directed_cycle a (.single (edge.elim id id))
  let G := withFirstPair base a b
  have forward : G.edge a b = true := first_pair_edge_iff.mpr
    ⟨edge, by simp [firstPairRank, distinct.symm]⟩
  have parents := first_pair_is_covered base distinct
  let H := Reversal.flip G a b forward parents
  have R : Reversal G H a b := Reversal.flip_is_covered_reversal G a b forward parents
  have obs : SameDConnections G H := sameDConnections_of_reversal R
  have signature := same_dConnections_iff_same_signature.mp obs
  have sk := first_pair_same_skeleton base distinct
  refine ⟨G, H, sk, fun x y => (sk x y).trans (signature.1 x y), obs, ?_, forward, R.reverse⟩
  intro t member
  exact same_dConnections_after_cut t signature
    ((cut_skeleton_iff_crossing_directions t signature.1).mpr
      (crossing_directions_of_unseparated_reversal R t (unseparated t member)))

/-- A fixed intervention design identifies all DAG orientations of a
skeleton exactly when it separates each edge of that skeleton. -/
theorem identifies_every_orientation_iff_separates_skeleton
    (base : DAG n) (targets : List (Target n)) :
    IdentifiesEveryOrientation base targets ↔ SeparatesSkeleton base targets := by
  refine ⟨?_, identifies_of_separates⟩
  intro identifies a b edge
  classical
  by_cases existsTarget : ∃ target ∈ targets, target a ≠ target b
  · exact existsTarget
  · exfalso
    have same : ∀ t ∈ targets, t a = t b := by
      intro t member
      by_cases equal : t a = t b
      · exact equal
      · exact (existsTarget ⟨t, member, equal⟩).elim
    obtain ⟨G, H, skG, skH, obs, regimes, forward, backward⟩ :=
      unseparated_edge_has_indistinguishable_orientations edge same
    have arrows := identifies G H skG skH obs regimes
    exact G.no_directed_cycle a (.extend (.single forward) (arrows.symm ▸ backward))

/-- Boolean edge-separation test for a fixed design. -/
def separatesCheck (base : DAG n) (targets : List (Target n)) : Bool :=
  (List.finRange n).all fun u => (List.finRange n).all fun v =>
    !adjacentTest base u v || targets.any (fun target => target u != target v)

theorem separatesCheck_iff (base : DAG n) (targets : List (Target n)) :
    separatesCheck base targets = true ↔ SeparatesSkeleton base targets := by
  simp only [separatesCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, bne_iff_ne, SeparatesSkeleton]
  constructor
  · intro h u v adj
    have actual : adjacentTest base u v = true := Bool.or_eq_true_iff.mpr adj
    exact (h u v).resolve_left (fun absent => Bool.false_ne_true (absent.symm.trans actual))
  · intro h u v
    cases found : adjacentTest base u v
    · exact .inl rfl
    · exact .inr (h u v (Bool.or_eq_true_iff.mp found))

end
end OpenCausalScience.Papers.KocaogluEtAl2017.SeparatingDesign
