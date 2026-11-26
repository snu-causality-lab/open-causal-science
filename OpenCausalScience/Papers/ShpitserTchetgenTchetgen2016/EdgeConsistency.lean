module
public import OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.PathReduction

/-! # Inducing edge settings from path assignments

Shpitser and Tchetgen Tchetgen (2016), §5.3. The intervened prefix of a
relevant path supplies a constant. The coverage and value agreement
conditions imply the recursive edge/path compatibility of Lemma 5.7.
Source: https://arxiv.org/pdf/1411.2127#page=26
-/

namespace OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeConsistency

open EdgeGFormula PathReduction

@[expose] public section

variable {n : Nat} {Ω : Type}

abbrev Assignments (n : Nat) := List (List (Fin n) × Bool)

/-- The assigned prefix, if one is encountered in this context. -/
def prefixSetting (paths : Assignments n) : PathSetting n :=
  fun route => (paths.find? fun entry => entry.1.isPrefixOf route).map Prod.snd

/-- Assign an edge the value of its first listed path. Agreement of
all paths with that edge makes this independent of the listed order. -/
def inducedEdges (paths : Assignments n) : EdgeSetting n :=
  fun u v => (paths.find? fun entry => entry.1.take 2 == [u, v]).map Prod.snd

/-- Suffixes whose proper internal paths have not cut off the
substitution. A preceding edge may be the beginning of a clamp. -/
inductive RelevantSuffix (G : DAG n) (paths : Assignments n) (outcome : Fin n) :
    Fin n → List (Fin n) → Prop
  | outcome : RelevantSuffix G paths outcome outcome []
  | prepend {u v : Fin n} {later : List (Fin n)} :
      G.edge u v = true → prefixSetting paths (u :: v :: later) = none →
      RelevantSuffix G paths outcome v later → RelevantSuffix G paths outcome u (v :: later)

/-- For a proper list of nonempty directed paths, coverage expresses
that a relevant route starting at a treated edge must meet an assigned
prefix. Agreement requires equal values along paths with the same
first edge. The length hypothesis restricts assignments to paths with
at least one edge. -/
structure Consistent (G : DAG n) (paths : Assignments n) (outcome : Fin n) : Prop where
  has_edge : ∀ entry ∈ paths, 2 ≤ entry.1.length
  agrees : ∀ left ∈ paths, ∀ right ∈ paths, left.1.take 2 = right.1.take 2 → left.2 = right.2
  covers : ∀ u v later, RelevantSuffix G paths outcome v later → G.edge u v = true →
    inducedEdges paths u v ≠ none → prefixSetting paths (u :: v :: later) ≠ none

private theorem prefix_starts_with_edge {paths : Assignments n} {u v : Fin n}
    {later : List (Fin n)} {entry : List (Fin n) × Bool} (len : 2 ≤ entry.1.length)
    (find : (paths.find? fun pair => pair.1.isPrefixOf (u :: v :: later)) = some entry) :
    entry.1.take 2 = [u, v] := by
  have isPrefix : entry.1.isPrefixOf (u :: v :: later) = true :=
    List.find?_some (p := fun pair => pair.1.isPrefixOf (u :: v :: later)) (a := entry) find
  have init := List.isPrefixOf_iff_prefix.mp isPrefix
  rw [List.prefix_iff_eq_take] at init
  have taken := congrArg (List.take 2) init
  rw [List.take_take, Nat.min_eq_left len] at taken
  exact taken

private theorem preceding_settings_eq {G : DAG n} {paths : Assignments n} {outcome u v : Fin n}
    {later : List (Fin n)} (consistent : Consistent G paths outcome)
    (relevant : RelevantSuffix G paths outcome v later) (edge : G.edge u v = true) :
    prefixSetting paths (u :: v :: later) = inducedEdges paths u v := by
  cases p : paths.find? (fun pair => pair.1.isPrefixOf (u :: v :: later)) with
  | none =>
    have empty : prefixSetting paths (u :: v :: later) = none := by simp [prefixSetting, p]
    cases e : paths.find? (fun pair => pair.1.take 2 == [u, v]) with
    | none => simp [empty, inducedEdges, e]
    | some entry =>
      have nonempty : inducedEdges paths u v ≠ none := by simp [inducedEdges, e]
      exact ((consistent.covers u v later relevant edge nonempty) empty).elim
  | some entry =>
    have listed := List.mem_of_find?_eq_some p
    have begins := prefix_starts_with_edge (consistent.has_edge entry listed) p
    cases e : paths.find? (fun pair => pair.1.take 2 == [u, v]) with
    | none =>
      exact (List.find?_eq_none.mp e entry listed (by simp [begins])).elim
    | some edgeEntry =>
      have chosen := List.mem_of_find?_eq_some e
      have edgeTest : (edgeEntry.1.take 2 == [u, v]) = true :=
        List.find?_some (p := fun pair => pair.1.take 2 == [u, v]) (a := edgeEntry) e
      have edgeBegins : edgeEntry.1.take 2 = [u, v] := beq_iff_eq.mp edgeTest
      have same := consistent.agrees entry listed edgeEntry chosen (begins.trans edgeBegins.symm)
      simp [prefixSetting, inducedEdges, p, e, same]

private theorem live_suffix_relevant_of_consistent {G : DAG n} {paths : Assignments n}
    {outcome v : Fin n} {later : List (Fin n)} (consistent : Consistent G paths outcome)
    (live : LiveSuffix G (inducedEdges paths) outcome v later) : RelevantSuffix G paths outcome v later := by
  induction live with
  | outcome => exact .outcome
  | prepend edge unset _ ih =>
    exact .prepend edge ((preceding_settings_eq consistent ih edge).trans unset) ih

theorem compatible_of_consistent {G : DAG n} {paths : Assignments n} {outcome : Fin n}
    (consistent : Consistent G paths outcome) :
    Compatible G (prefixSetting paths) (inducedEdges paths) outcome :=
  fun _ _ _ live edge => preceding_settings_eq consistent (live_suffix_relevant_of_consistent consistent live) edge

/-- A listed-path intervention obeying the common-first-edge coverage
and value conditions is equal to its induced edge intervention. -/
theorem path_response_eq_induced_edges (G : DAG n)
    (mechanism : Fin n → Ω → Assignment n → Bool) (unit : Fin n → Ω)
    (paths : Assignments n) (outcome : Fin n) (consistent : Consistent G paths outcome) :
    pathResponse G mechanism unit (prefixSetting paths) outcome [] =
      evaluate G mechanism unit (inducedEdges paths) outcome :=
  path_response_eq_edge_response G mechanism unit _ _ outcome (compatible_of_consistent consistent)

end
end OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeConsistency
