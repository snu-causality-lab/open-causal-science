module
public import OpenCausalScience.Papers.VermaPearl1990.Equivalence

/-! The graphical criteria of Hauser and Bühlmann (2012), Theorem 10
(ii)–(iv), for perfect interventions. The model equality in (i) is a
probabilistic statement beyond the scope of this module.

https://www.jmlr.org/papers/volume13/hauser12a/hauser12a.pdf -/

namespace OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence

open OpenCausalScience.Papers.Chickering1995.CoveredReversal
open OpenCausalScience.Papers.Chickering1995.Transformation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.VermaPearl1990.Equivalence

@[expose] public section

variable {n : Nat}

abbrev Target (n : Nat) := Fin n → Bool

/-- A perfect intervention deletes precisely the arrows into its target. -/
def cutIncoming (G : DAG n) (target : Target n) : DAG n where
  edge u v := G.edge u v && !target v
  rank := G.rank
  edge_increases u v h := G.edge_increases u v (Bool.and_eq_true_iff.mp h).1

theorem cut_edge_iff {G : DAG n} {target : Target n} {u v : Fin n} :
    (cutIncoming G target).edge u v = true ↔ G.edge u v = true ∧ target v = false := by
  cases ht : target v <;> simp [cutIncoming, ht]

/-- Every vertex is untargeted in at least one of the regimes. -/
def Conservative (targets : List (Target n)) : Prop :=
  ∀ v, ∃ target ∈ targets, target v = false

def SameSkeleton (G H : DAG n) : Prop :=
  ∀ u v, Adjacent G u v ↔ Adjacent H u v

/-- A target that separates two endpoints exposes the arrow's direction. -/
def SameCrossingDirections (target : Target n) (G H : DAG n) : Prop :=
  ∀ u v, target u ≠ target v → (G.edge u v = true ↔ H.edge u v = true)

private theorem opposite_absent {G : DAG n} {u v : Fin n} (h : G.edge u v = true) :
    G.edge v u ≠ true :=
  fun opposite => G.no_directed_cycle u (.extend (.single h) opposite)

private theorem kept_direction_of_cut_skeleton {G H : DAG n} {target : Target n}
    (sameCut : SameSkeleton (cutIncoming G target) (cutIncoming H target))
    {u v : Fin n} (targeted : target u = true) (untargeted : target v = false)
    (edge : G.edge u v = true) : H.edge u v = true := by
  rcases (sameCut u v).mp (.inl (cut_edge_iff.mpr ⟨edge, untargeted⟩)) with kept | removed
  · exact (cut_edge_iff.mp kept).1
  · exact (Bool.false_ne_true ((cut_edge_iff.mp removed).2.symm.trans targeted)).elim

/-- Given the observational skeleton, the cut skeleton records exactly
the directions across the boundary of the target. This includes Lemma 47. -/
theorem cut_skeleton_iff_crossing_directions {G H : DAG n} (target : Target n)
    (same : SameSkeleton G H) :
    SameSkeleton (cutIncoming G target) (cutIncoming H target) ↔
      SameCrossingDirections target G H := by
  constructor
  · intro sameCut u v distinct
    have forward {D E : DAG n} (sk : SameSkeleton D E)
        (cut : SameSkeleton (cutIncoming D target) (cutIncoming E target))
        (edge : D.edge u v = true) : E.edge u v = true := by
      cases hu : target u <;> cases hv : target v
      · exact (distinct (hu.trans hv.symm)).elim
      · rcases (sk u v).mp (.inl edge) with sameArrow | reversed
        · exact sameArrow
        · have opposite := kept_direction_of_cut_skeleton
            (fun x y => (cut x y).symm) hv hu reversed
          exact (opposite_absent edge opposite).elim
      · exact kept_direction_of_cut_skeleton cut hu hv edge
      · exact (distinct (hu.trans hv.symm)).elim
    exact ⟨forward same sameCut,
      forward (fun x y => (same x y).symm) (fun x y => (sameCut x y).symm)⟩
  · intro crossing u v
    have transfer {D E : DAG n} (sk : SameSkeleton D E)
        (dir : SameCrossingDirections target D E) {u v : Fin n}
        (arrow : (cutIncoming D target).edge u v = true) :
        Adjacent (cutIncoming E target) u v := by
      obtain ⟨edge, untargeted⟩ := cut_edge_iff.mp arrow
      cases source : target u
      · rcases (sk u v).mp (.inl edge) with keep | rev
        · exact .inl (cut_edge_iff.mpr ⟨keep, untargeted⟩)
        · exact .inr (cut_edge_iff.mpr ⟨rev, source⟩)
      · exact .inl (cut_edge_iff.mpr
          ⟨(dir u v (by simp [source, untargeted])).mp edge, untargeted⟩)
    constructor
    · intro adj
      exact adj.elim (transfer same crossing) (fun arrow => Or.symm (transfer same crossing arrow))
    · intro adj
      have sk : SameSkeleton H G := fun x y => (same x y).symm
      have dir : SameCrossingDirections target H G := fun x y h => (crossing x y h).symm
      exact adj.elim (transfer sk dir) (fun arrow => Or.symm (transfer sk dir arrow))

private theorem same_dConnections_after_cut_of_reversal {G H : DAG n}
    {u v : Fin n} (target : Target n) (R : Reversal G H u v)
    (sameTarget : target u = target v) :
    SameDConnections (cutIncoming G target) (cutIncoming H target) := by
  cases hu : target u
  · have hv : target v = false := sameTarget.symm.trans hu
    apply sameDConnections_of_reversal (a := u) (b := v)
    exact {
      forward := cut_edge_iff.mpr ⟨R.forward, hv⟩
      reverse := cut_edge_iff.mpr ⟨R.reverse, hu⟩
      unchanged := fun x y first second =>
        cut_edge_iff.trans ((and_congr (R.unchanged x y first second) Iff.rfl).trans cut_edge_iff.symm)
      parents := fun x first second => by
        simpa only [cut_edge_iff, hu, hv, and_true] using R.parents x first second }
  · have hv : target v = true := sameTarget.symm.trans hu
    apply same_dConnections_of_edge_eq
    funext x y
    apply Bool.eq_iff_iff.mpr
    rw [cut_edge_iff, cut_edge_iff]
    by_cases first : x = u ∧ y = v
    · obtain ⟨rfl, rfl⟩ := first
      simp [hv]
    · by_cases second : x = v ∧ y = u
      · obtain ⟨rfl, rfl⟩ := second
        simp [hu]
      · exact and_congr (R.unchanged x y first second) Iff.rfl

private theorem same_dConnections_after_cut_of_sequence {G H : DAG n}
    (target : Target n) (sequence : ReversalSequence H G)
    (crossing : SameCrossingDirections target G H) :
    SameDConnections (cutIncoming G target) (cutIncoming H target) := by
  induction sequence with
  | done equal =>
    apply same_dConnections_of_edge_eq
    funext x y
    simp only [cutIncoming, equal]
  | @next D E u v differing R _ ih =>
    have same : target u = target v := by
      by_cases equal : target u = target v
      · exact equal
      · exact (opposite_absent differing.2 ((crossing u v equal).mp differing.1)).elim
    have transferred : SameCrossingDirections target E H := by
      intro x y separated
      have first : ¬ (x = u ∧ y = v) := by
        rintro ⟨rfl, rfl⟩
        exact separated same
      have second : ¬ (x = v ∧ y = u) := by
        rintro ⟨rfl, rfl⟩
        exact separated same.symm
      exact (R.unchanged x y first second).symm.trans (crossing x y separated)
    have oneStep := same_dConnections_after_cut_of_reversal target R same
    exact fun fixed x y => (oneStep fixed x y).trans (ih transferred fixed x y)

/-- The graphical implication from Theorem 10(iv) to the per-regime
d-separations. It holds even for a non-conservative target collection. -/
theorem same_dConnections_after_cut {G H : DAG n} (target : Target n)
    (observational : SameSignature G H)
    (sameCut : SameSkeleton (cutIncoming G target) (cutIncoming H target)) :
    SameDConnections (cutIncoming G target) (cutIncoming H target) :=
  same_dConnections_after_cut_of_sequence target
    (reversal_sequence_of_same_signature observational)
    ((cut_skeleton_iff_crossing_directions target observational.1).mp sameCut)

private theorem observational_skeleton_of_cut_signatures {G H : DAG n}
    {targets : List (Target n)} (conservative : Conservative targets)
    (signatures : ∀ target ∈ targets, SameSignature (cutIncoming G target) (cutIncoming H target)) :
    SameSkeleton G H := by
  have transfer {D E : DAG n}
      (same : ∀ target ∈ targets, SameSkeleton (cutIncoming D target) (cutIncoming E target))
      {u v : Fin n} (edge : D.edge u v = true) : Adjacent E u v := by
    obtain ⟨target, member, retained⟩ := conservative v
    rcases (same target member u v).mp (.inl (cut_edge_iff.mpr ⟨edge, retained⟩))
      with forward | backward
    · exact .inl (cut_edge_iff.mp forward).1
    · exact .inr (cut_edge_iff.mp backward).1
  intro u v
  constructor
  · intro adj
    have same := fun target member => (signatures target member).1
    exact adj.elim (transfer same) (fun arrow => Or.symm (transfer same arrow))
  · intro adj
    have same : ∀ target ∈ targets, SameSkeleton (cutIncoming H target) (cutIncoming G target) :=
      fun target member x y => ((signatures target member).1 x y).symm
    exact adj.elim (transfer same) (fun arrow => Or.symm (transfer same arrow))

private theorem observational_signature_of_cut_signatures {G H : DAG n}
    {targets : List (Target n)} (conservative : Conservative targets)
    (signatures : ∀ target ∈ targets, SameSignature (cutIncoming G target) (cutIncoming H target)) :
    SameSignature G H := by
  have skeleton := observational_skeleton_of_cut_signatures conservative signatures
  have transfer {D E : DAG n} (sk : SameSkeleton D E)
      (same : ∀ target ∈ targets, ∀ x m y,
        UnshieldedCollider (cutIncoming D target) x m y →
          UnshieldedCollider (cutIncoming E target) x m y)
      {x m y : Fin n} (collider : UnshieldedCollider D x m y) :
      UnshieldedCollider E x m y := by
    obtain ⟨target, member, retained⟩ := conservative m
    obtain ⟨ne, absent, left, right⟩ := collider
    have cutAbsent : ¬ Adjacent (cutIncoming D target) x y :=
      fun adj => absent (adj.elim (fun edge => .inl (cut_edge_iff.mp edge).1)
        (fun edge => .inr (cut_edge_iff.mp edge).1))
    obtain ⟨_, _, newLeft, newRight⟩ :=
      same target member x m y ⟨ne, cutAbsent, cut_edge_iff.mpr ⟨left, retained⟩,
        cut_edge_iff.mpr ⟨right, retained⟩⟩
    exact ⟨ne, fun adj => absent ((sk x y).mpr adj), (cut_edge_iff.mp newLeft).1,
      (cut_edge_iff.mp newRight).1⟩
  exact ⟨skeleton, fun _ _ _ => ⟨
    transfer skeleton (fun target member x m y => ((signatures target member).2 x m y).mp),
    transfer (fun x y => (skeleton x y).symm)
      (fun target member x m y => ((signatures target member).2 x m y).mpr)⟩⟩

/-- The graph part of Theorem 10(ii) and (iii). -/
theorem cut_dConnections_iff_cut_signatures (targets : List (Target n)) (G H : DAG n) :
    (∀ target ∈ targets, SameDConnections (cutIncoming G target) (cutIncoming H target)) ↔
      (∀ target ∈ targets, SameSignature (cutIncoming G target) (cutIncoming H target)) := by
  exact ⟨fun h t member => same_dConnections_iff_same_signature.mp (h t member),
    fun h t member => same_dConnections_iff_same_signature.mpr (h t member)⟩

/-- Theorem 10(iii) and (iv) are equivalent for conservative targets. -/
theorem cut_signatures_iff_observational_and_cut_skeletons {G H : DAG n}
    {targets : List (Target n)} (conservative : Conservative targets) :
    (∀ target ∈ targets, SameSignature (cutIncoming G target) (cutIncoming H target)) ↔
      SameSignature G H ∧
        (∀ target ∈ targets, SameSkeleton (cutIncoming G target) (cutIncoming H target)) := by
  constructor
  · intro signatures
    exact ⟨observational_signature_of_cut_signatures conservative signatures,
      fun t member => (signatures t member).1⟩
  · intro h t member
    exact same_dConnections_iff_same_signature.mp (same_dConnections_after_cut t h.1 (h.2 t member))

/-- Executable signature comparison for all specified targets. -/
def cutSignaturesMatch (targets : List (Target n)) (G H : DAG n) : Bool :=
  targets.all fun target => signaturesMatch (cutIncoming G target) (cutIncoming H target)

theorem cutSignaturesMatch_iff (targets : List (Target n)) (G H : DAG n) :
    cutSignaturesMatch targets G H = true ↔
      ∀ target ∈ targets, SameDConnections (cutIncoming G target) (cutIncoming H target) :=
  ⟨fun h t member => signaturesMatch_iff_same_dConnections.mp (List.all_eq_true.mp h t member),
    fun h => List.all_eq_true.mpr fun t member => signaturesMatch_iff_same_dConnections.mpr (h t member)⟩

end
end OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence
