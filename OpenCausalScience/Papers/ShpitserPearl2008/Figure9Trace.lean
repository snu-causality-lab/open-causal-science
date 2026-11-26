module
public import OpenCausalScience.Papers.ShpitserPearl2008.Figure9
public import OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence
public import OpenCausalScience.Graph.MixedSeparationExecutable

/-! # Graph trace for Figures 9–12

The observed copies of Figure 9(b) are quotiented in the order in
Figure 11. Taking the directed ancestors of the query gives Figure 9(c).
For Figure 12, the outgoing-edge tests exchange D and Z but retain the
factual X. Figure 9(d) gives the ensuing two-component ID* call.
https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=17
-/

namespace OpenCausalScience.Papers.ShpitserPearl2008.Figure9Trace

open ParallelWorlds (Copy)
open Figure9
open CounterfactualDecision (FactorAtom baseAction)
open TianPearl2003.IdentifyRecurrence (district)

@[expose] public section

abbrev CopyVertex := Copy World 5

def copies : List CopyVertex :=
  [.setX, .factual, .setD].flatMap fun world => (List.finRange 5).map fun v => (world, v)

def keptCopies (step : Nat) : List CopyVertex :=
  copies.filter fun vertex => representatives step vertex == vertex.1

/-- Follow the selected representative's incoming edges. Intervention
copies are present as constants and have no incoming edges. -/
def parents (step : Nat) (child : CopyVertex) : List CopyVertex :=
  let world := representatives step child
  if (settings false false world child.2).isSome then []
  else ((List.finRange 5).filter fun u => graph.edge u child.2).map fun u =>
    (representatives step (world, u), u)

def seed : List CopyVertex := [(.setX, y), (.factual, x), (.factual, z), (.factual, d)]

def ancestors (step : Nat) (query : List CopyVertex) : List CopyVertex :=
  (List.range 5).foldl (fun stack _ => (stack ++ stack.flatMap (parents step)).eraseDups) query

theorem figure11_stage_sizes :
    (keptCopies 0).length = 15 ∧ (keptCopies 1).length = 13 ∧
      (keptCopies 2).length = 10 ∧ (keptCopies 3).length = 9 := by decide +kernel

theorem figure9c_parent_lists :
    (ancestors 3 seed).map (fun vertex => (vertex, parents 3 vertex)) =
      [((.setX, y), [(.setX, w), (.factual, z)]),
       ((.factual, x), []), ((.factual, z), [(.factual, d)]),
       ((.factual, d), []), ((.setX, w), [(.setX, x)]), ((.setX, x), [])] := by decide +kernel

/-- Index order in Figure 9(c): x̄, Wₓ, D, Z, X, Yₓ. -/
def figure9cVertex (v : Fin 6) : CopyVertex :=
  match v.val with
  | 0 => (.setX, x)
  | 1 => (.setX, w)
  | 2 => (.factual, d)
  | 3 => (.factual, z)
  | 4 => (.factual, x)
  | _ => (.setX, y)

/-- Shared treatment/outcome U creates the single bidirected edge that
remains after the other worlds are merged and pruned. -/
def cMarks (intervened : Option (Fin 6)) (u : Fin 6) (atU : Bool) (v : Fin 6) (atV : Bool) : Bool :=
  match atU, atV with
  | false, false => false
  | false, true => intervened != some u && (parents 3 (figure9cVertex v)).contains (figure9cVertex u)
  | true, false => intervened != some v && (parents 3 (figure9cVertex u)).contains (figure9cVertex v)
  | true, true => (u == 4 && v == 5) || (u == 5 && v == 4)

def figure9c (intervened : Option (Fin 6)) : MixedGraph 6 where
  edge := cMarks intervened
  symmetric := by
    intro u a v b
    cases a <;> cases b <;> simp [cMarks, Bool.and_comm, Bool.or_comm]
  loop_free := by
    intro u a b
    have base : (parents 3 (figure9cVertex u)).contains (figure9cVertex u) = false :=
      (show ∀ v, (parents 3 (figure9cVertex v)).contains (figure9cVertex v) = false from by decide +kernel) u
    cases a <;> cases b <;> simp only [cMarks]
    · rw [base, Bool.and_false]
    · rw [base, Bool.and_false]
    · exact (show ∀ v : Fin 6, (v == 4 && v == 5 || v == 5 && v == 4) = false from
        by decide +kernel) u
  no_arrow_of_undirected := by simp [cMarks]

/-- Index order in Figure 9(d): x̄, Wₓ,z, z̄, X, Yₓ,z. -/
def dMarks (u : Fin 5) (atU : Bool) (v : Fin 5) (atV : Bool) : Bool :=
  let arrow (a b : Fin 5) := (a == 0 && b == 1) || (a == 1 && b == 4) || (a == 2 && b == 4)
  match atU, atV with
  | false, false => false
  | false, true => arrow u v
  | true, false => arrow v u
  | true, true => (u == 3 && v == 4) || (u == 4 && v == 3)

def figure9d : MixedGraph 5 where
  edge := dMarks
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by simp [dMarks]

private theorem no_walk_of_closed {n : Nat} (G : MixedGraph n)
    (first last : Fin n) (region : Fin n → Bool) (inside : region first = true)
    (outside : region last = false)
    (closed : ∀ u a v b, region u = true → G.edge u a v b = true → region v = true) :
    ¬ G.WalkConnected (· == first) (· == last) (fun _ => false) := by
  rintro ⟨start, finish, ⟨u, mark, firstEq, edge⟩, route, lastEq⟩
  have seedInside := closed u mark start.1 start.2 ((beq_iff_eq.mp firstEq).symm ▸ inside) edge
  have finishInside : region finish.1 = true := by
    clear lastEq
    induction route with
    | refl => exact seedInside
    | extend _ next ih =>
      obtain ⟨mark, edge, _⟩ := next
      exact closed _ mark _ _ ih edge
  have impossible := (beq_iff_eq.mp lastEq) ▸ finishInside
  rw [outside] at impossible
  contradiction

/-- D and Z can be exchanged on Figure 9(c). X retains its bidirected
path even when its outgoing edges are removed for the exchange test. -/
theorem idc_exchange_checks :
    (figure9c (some 2)).mSeparated (· == 2) (· == 5) (fun _ => false) = true ∧
    (figure9c (some 3)).mSeparated (· == 3) (· == 5) (fun _ => false) = true ∧
    (figure9c (some 4)).mSeparated (· == 4) (· == 5) (fun _ => false) = false ∧
    figure9d.mSeparated (· == 3) (· == 4) (fun _ => false) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ((figure9c (some 2)).m_separated_iff_no_walk _ _ _).mpr
    exact no_walk_of_closed _ 2 5 (· == 2) rfl rfl (by decide +kernel)
  · apply ((figure9c (some 3)).m_separated_iff_no_walk _ _ _).mpr
    exact no_walk_of_closed _ 3 5 (fun v => v == 2 || v == 3) rfl rfl (by decide +kernel)
  · apply Bool.eq_false_iff.mpr
    intro separated
    exact ((figure9c (some 4)).m_separated_iff_no_walk _ _ _).mp separated
      ⟨(5, true), (5, true), ⟨4, true, rfl, rfl⟩, .refl _, rfl⟩
  · apply Bool.eq_false_iff.mpr
    intro separated
    exact (figure9d.m_separated_iff_no_walk _ _ _).mp separated
      ⟨(4, true), (4, true), ⟨3, true, rfl, rfl⟩, .refl _, rfl⟩

/-- Line 6 of ID* splits the random nodes in Figure 9(d) into
{Wₓ,z} and {factual X, Yₓ,z}. The fixed x̄ and z̄ are excluded. -/
theorem id_star_split :
    district figure9d [1, 3, 4] 1 = [1] ∧
    district figure9d [1, 3, 4] 3 = [3, 4] ∧
    district figure9d [1, 3, 4] 4 = [3, 4] := by decide +kernel

/-- The two successful line 9 calls use only the W/Z settings for the
{X,Y} factor, and only the X setting for the W factor. -/
theorem id_star_worked_base_cases : ∀ xSet zObs wObs xObs yObs,
    let pairFactor : List (FactorAtom 5) := [⟨x, xObs, fun _ => none⟩,
      ⟨y, yObs, fun v => if v = z then some zObs else if v = w then some wObs else none⟩]
    let singleFactor : List (FactorAtom 5) := [⟨w, wObs, fun v => if v = x then some xSet else none⟩]
    (baseAction pairFactor).map (fun action => (List.finRange 5).map action) =
        some [none, none, some wObs, some zObs, none] ∧
      (baseAction singleFactor).map (fun action => (List.finRange 5).map action) =
        some [none, some xSet, none, none, none] := by decide +kernel

end
end OpenCausalScience.Papers.ShpitserPearl2008.Figure9Trace
