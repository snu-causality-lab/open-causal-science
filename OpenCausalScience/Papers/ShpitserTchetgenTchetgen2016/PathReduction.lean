module
public import OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeGFormula

/-! # Recursive substitution along paths

Shpitser and Tchetgen Tchetgen (2016), Lemma 5.7. The hypothesis
states compatibility with the induced edge intervention directly
on each unblocked directed suffix into the queried outcome.
Source: https://arxiv.org/pdf/1411.2127#page=26
-/

namespace OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.PathReduction

open EdgeGFormula

@[expose] public section

variable {n : Nat} {Ω : Type}

abbrev PathSetting (n : Nat) := List (Fin n) → Option Bool

/-- A suffix lists the later vertices towards the queried outcome.
An assignment to `u :: v :: suffix` replaces `u` only in that context. -/
def pathResponse (G : DAG n) (mechanism : Fin n → Ω → Assignment n → Bool)
    (unit : Fin n → Ω) (paths : PathSetting n) (v : Fin n) (suffix : List (Fin n)) : Bool :=
  mechanism v (unit v) (fun u =>
    if _parent : G.edge u v = true then
      match paths (u :: v :: suffix) with
      | some assigned => assigned
      | none => pathResponse G mechanism unit paths u (v :: suffix)
    else false)
termination_by G.rank v
decreasing_by exact G.edge_increases _ _ _parent

/-- Suffixes traversed by edge substitution, starting at the outcome
and stopping upstream recursion at a clamped arrow. -/
inductive LiveSuffix (G : DAG n) (edges : EdgeSetting n) (outcome : Fin n) :
    Fin n → List (Fin n) → Prop
  | outcome : LiveSuffix G edges outcome outcome []
  | prepend {u v : Fin n} {later : List (Fin n)} :
      G.edge u v = true → edges u v = none → LiveSuffix G edges outcome v later →
      LiveSuffix G edges outcome u (v :: later)

/-- At every live suffix, the setting on each preceding arrow agrees
with its setting in the induced edge intervention. -/
def Compatible (G : DAG n) (paths : PathSetting n) (edges : EdgeSetting n)
    (outcome : Fin n) : Prop :=
  ∀ u v suffix, LiveSuffix G edges outcome v suffix → G.edge u v = true →
    paths (u :: v :: suffix) = edges u v

theorem path_response_eq_edge_of_compatible (G : DAG n)
    (mechanism : Fin n → Ω → Assignment n → Bool) (unit : Fin n → Ω)
    (paths : PathSetting n) (edges : EdgeSetting n) (outcome : Fin n)
    (compatible : Compatible G paths edges outcome) (v : Fin n) (suffix : List (Fin n))
    (live : LiveSuffix G edges outcome v suffix) :
    pathResponse G mechanism unit paths v suffix = evaluate G mechanism unit edges v := by
  induction bound : G.rank v using Nat.strongRecOn generalizing v suffix with
  | ind rank ih =>
    rw [pathResponse, evaluate]
    apply congrArg (mechanism v (unit v))
    funext u
    by_cases parent : G.edge u v = true
    · have same := compatible u v suffix live parent
      cases assigned : edges u v with
      | none =>
        have smaller : G.rank u < rank := by rw [← bound]; exact G.edge_increases _ _ parent
        simpa [parent, same, assigned] using
          ih (G.rank u) smaller u (v :: suffix) (.prepend parent assigned live) rfl
      | some b => simp [parent, same, assigned]
    · simp [parent]

/-- Compatible substitution preserves the entire queried response on
one unit, with the same exogenous values on both sides. -/
theorem path_response_eq_edge_response (G : DAG n)
    (mechanism : Fin n → Ω → Assignment n → Bool) (unit : Fin n → Ω)
    (paths : PathSetting n) (edges : EdgeSetting n) (outcome : Fin n)
    (compatible : Compatible G paths edges outcome) :
    pathResponse G mechanism unit paths outcome [] = evaluate G mechanism unit edges outcome :=
  path_response_eq_edge_of_compatible G mechanism unit paths edges outcome compatible
    outcome [] .outcome

end
end OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.PathReduction
