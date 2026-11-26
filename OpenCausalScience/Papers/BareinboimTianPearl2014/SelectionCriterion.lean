module
public import OpenCausalScience.Graph.MixedSeparation
public import OpenCausalScience.Graph.MoralizationExecutable

/-! # Graphical selection criteria

Bareinboim, Tian and Pearl (2014). Theorem 1 tests separation of the
outcomes from the selection node given the query conditioning set.
Theorem 3 uses the admissible common ancestors to test whether any
allowed external adjustment stratum satisfies Theorem 2.

Source: https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf
-/

namespace OpenCausalScience.Papers.BareinboimTianPearl2014.SelectionCriterion

open OpenCausalScience.Moralization
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness (Conditioning)

@[expose] public section

variable {n : Nat} {G : DAG n}

def passes (H : MixedGraph n) (outcome selection conditioning : Fin n → Bool) : Bool :=
  H.mSeparated outcome selection conditioning

/-- The mixed-graph search used by the public CGA wrapper tests exactly
the absence of an active path from the outcome to selection. -/
theorem passes_iff_no_active_path (H : MixedGraph n) (outcome selection conditioning : Fin n → Bool)
    (outside : ∀ v, outcome v = true → conditioning v = false)
    (distinct : ∀ v, outcome v = true → selection v = false) :
    passes H outcome selection conditioning = true ↔ ¬ H.PathConnected outcome selection conditioning :=
  H.m_separated_iff_no_path outcome selection conditioning outside distinct

def dagQuery (G : DAG n) (outcome selection conditioning : Fin n → Bool) : Query G :=
  ⟨outcome, selection, Conditioning.ofPredicate G conditioning⟩

def add (required other : Fin n → Bool) : Fin n → Bool :=
  fun v => required v || other v

/-- Take the common measured variables in the ancestor region and
remove the endpoints and required conditioning variables. -/
def candidate (G : DAG n) (outcome selection fixed common : Fin n → Bool) : Fin n → Bool :=
  fun v => common v && ((dagQuery G outcome selection fixed).relevantBool v &&
    (!outcome v && (!selection v && !fixed v)))

def validAdditional (outcome selection fixed common extra : Fin n → Bool) : Prop :=
  ∀ v, extra v = true →
    common v = true ∧ outcome v = false ∧ selection v = false ∧ fixed v = false

private theorem candidate_valid (G : DAG n) (outcome selection fixed common : Fin n → Bool) :
    validAdditional outcome selection fixed common (candidate G outcome selection fixed common) := by
  intro v included
  simp only [candidate, Bool.and_eq_true, Bool.not_eq_true'] at included
  exact ⟨included.1, included.2.2⟩

private theorem ancestor_trans {a b c : Fin n} (first : Ancestor G a b) (second : Ancestor G b c) :
    Ancestor G a c := by
  rcases second with rfl | suffix
  · exact first
  rcases first with rfl | beginning
  · exact .inr suffix
  apply Or.inr
  induction suffix with
  | single arrow => exact .extend beginning arrow
  | extend _ arrow ih => exact .extend ih arrow

private theorem baseline_subset {outcome selection fixed extra : Fin n → Bool} {v : Fin n}
    (baseline : (dagQuery G outcome selection fixed).relevant v) :
    (dagQuery G outcome selection (add fixed extra)).relevant v := by
  apply (Query.relevant_iff _ _).mpr
  obtain ⟨w, seeds, path⟩ := (Query.relevant_iff _ _).mp baseline
  change outcome w = true ∨ selection w = true ∨ fixed w = true at seeds
  refine ⟨w, ?_, path⟩
  change outcome w = true ∨ selection w = true ∨ add fixed extra w = true
  exact seeds.imp id (Or.imp id (fun fixed => Bool.or_eq_true_iff.mpr (.inl fixed)))

private theorem candidate_subset {outcome selection fixed common : Fin n → Bool} {v : Fin n}
    (relevant : (dagQuery G outcome selection
      (add fixed (candidate G outcome selection fixed common))).relevant v) :
    (dagQuery G outcome selection fixed).relevant v := by
  apply (Query.relevant_iff _ _).mpr
  obtain ⟨w, seeds, path⟩ := (Query.relevant_iff _ _).mp relevant
  change outcome w = true ∨ selection w = true ∨ add fixed _ w = true at seeds
  rcases seeds with y | s | either
  · exact ⟨w, .inl y, path⟩
  · exact ⟨w, .inr (.inl s), path⟩
  · rcases Bool.or_eq_true_iff.mp either with base | extra
    · exact ⟨w, .inr (.inr base), path⟩
    simp only [candidate, Bool.and_eq_true] at extra
    have baseline : (dagQuery G outcome selection fixed).relevant w :=
      (Query.relevantBool_iff _ _).mp extra.2.1
    obtain ⟨u, seeds, next⟩ := (Query.relevant_iff _ _).mp baseline
    exact ⟨u, seeds, ancestor_trans path next⟩

private theorem add_outside {outcome selection fixed common extra : Fin n → Bool}
    (legal : validAdditional outcome selection fixed common extra)
    (outcomeOutside : ∀ v, outcome v = true → fixed v = false)
    (selectionOutside : ∀ v, selection v = true → fixed v = false) :
    (∀ v, outcome v = true → add fixed extra v = false) ∧
      (∀ v, selection v = true → add fixed extra v = false) := by
  constructor
  · intro v hy
    refine Bool.or_eq_false_iff.mpr ⟨outcomeOutside v hy, Bool.eq_false_iff.mpr ?_⟩
    intro present
    have h := (legal v present).2.1
    rw [hy] at h
    contradiction
  · intro v hs
    refine Bool.or_eq_false_iff.mpr ⟨selectionOutside v hs, Bool.eq_false_iff.mpr ?_⟩
    intro present
    have h := (legal v present).2.2.1
    rw [hs] at h
    contradiction

private theorem canonical_walk_to_other {outcome selection fixed common extra : Fin n → Bool}
    (legal : validAdditional outcome selection fixed common extra)
    {v w : Fin n}
    (walk : (dagQuery G outcome selection (add fixed (candidate G outcome selection fixed common))).MoralWalk v w) :
    (dagQuery G outcome selection (add fixed extra)).MoralWalk v w := by
  have remain {u : Fin n} : (dagQuery G outcome selection
      (add fixed (candidate G outcome selection fixed common))).relevant u →
      (dagQuery G outcome selection (add fixed extra)).relevant u :=
    fun ancestor => baseline_subset (candidate_subset ancestor)
  have outside {u : Fin n}
      (relevant : (dagQuery G outcome selection
        (add fixed (candidate G outcome selection fixed common))).relevant u)
      (unblocked : add fixed (candidate G outcome selection fixed common) u = false) :
      add fixed extra u = false := by
    obtain ⟨givenOut, canonicalOut⟩ := Bool.or_eq_false_iff.mp unblocked
    refine Bool.or_eq_false_iff.mpr ⟨givenOut, Bool.eq_false_iff.mpr ?_⟩
    intro here
    obtain ⟨co, out, sel, base⟩ := legal u here
    have can : candidate G outcome selection fixed common u = true := by
      have rel := (Query.relevantBool_iff _ _).mpr (candidate_subset relevant)
      simp [candidate, co, out, sel, base, rel]
    exact Bool.false_ne_true (canonicalOut.symm.trans can)
  induction walk with
  | nil u => exact .nil u
  | cons edge _ ih =>
    apply Query.MoralWalk.cons _ ih
    refine ⟨remain edge.sourceRelevant, remain edge.targetRelevant,
      outside edge.sourceRelevant edge.sourceOutside, outside edge.targetRelevant edge.targetOutside,
      edge.distinct, ?_⟩
    rcases edge.connection with arrow | arrow | ⟨child, inGraph, e₁, e₂⟩
    · exact .inl arrow
    · exact .inr (.inl arrow)
    · exact .inr (.inr ⟨child, remain inGraph, e₁, e₂⟩)

/-- Theorem 3. The search for intersecting measured covariates that
can separate selection reduces to a single test in a finite DAG. -/
theorem exists_external_separator_iff (G : DAG n)
    (outcome selection fixed common : Fin n → Bool)
    (outcomeOutside : ∀ v, outcome v = true → fixed v = false)
    (selectionOutside : ∀ v, selection v = true → fixed v = false) :
    (∃ extra, validAdditional outcome selection fixed common extra ∧
      ¬ (dagQuery G outcome selection (add fixed extra)).DConnection) ↔
      (dagQuery G outcome selection (add fixed (candidate G outcome selection fixed common))).dagMoralSeparated = true := by
  have valid := candidate_valid G outcome selection fixed common
  have ⟨left, right⟩ := add_outside valid outcomeOutside selectionOutside
  rw [Query.dagMoralSeparated_eq_true_iff _ left right]
  constructor
  · rintro ⟨other, legal, separated⟩
    apply (Query.dSeparation_iff_no_moralConnection _ left right).mpr
    rintro ⟨s, y, src, tgt, walk⟩
    have ⟨otherLeft, otherRight⟩ := add_outside legal outcomeOutside selectionOutside
    exact (Query.dSeparation_iff_no_moralConnection _ otherLeft otherRight).mp separated
      ⟨s, y, src, tgt, canonical_walk_to_other legal walk⟩
  · intro separated
    exact ⟨_, valid, separated⟩

end
end OpenCausalScience.Papers.BareinboimTianPearl2014.SelectionCriterion
