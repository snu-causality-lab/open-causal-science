module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyCorrectness
public import OpenCausalScience.Papers.TianPearl2003.IdentifyReachability

/-! # Selected-only RC

Bareinboim and Tian (AAAI 2015), Figure 4. The selected kernel is
indexed by the current graph's vertices other than the fixed
selection event. Division removes a district from the kernel's
random set and leaves its vertices available as fixed arguments.

Source: https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=6
-/

namespace OpenCausalScience.Papers.BareinboimTian2015.RC

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyCorrectness
open TianPearl2003.IdentifyReachability

@[expose] public section

variable {n : Nat}

/-- Partition by the bidirected districts in the induced current graph. -/
def districts (G : MixedGraph n) (current : Vertices n) : List (Vertices n) :=
  (current.map (district G current)).eraseDups

def eligible (G : MixedGraph n) (selection : Fin n) (current : Vertices n) :
    List (Vertices n) :=
  let selectedAncestors := ancestors G current [selection]
  (districts G current).filter (fun d => d.all (!selectedAncestors.contains ·))

def retainedAfter (current : Vertices n) (components : List (Vertices n)) : Vertices n :=
  current.filter fun vertex => !components.any (·.contains vertex)

theorem peel_shrinks_iff (G : MixedGraph n) (selection : Fin n) (current : Vertices n) :
    (retainedAfter current (eligible G selection current)).length < current.length ↔
      eligible G selection current ≠ [] := by
  constructor
  · intro smaller empty
    simp [retainedAfter, empty] at smaller
  · intro nonempty
    have someDistrict : ∃ component, component ∈ eligible G selection current := by
      cases eq : eligible G selection current with
      | nil => exact False.elim (nonempty eq)
      | cons head tail => exact ⟨head, List.mem_cons_self⟩
    obtain ⟨component, member⟩ := someDistrict
    obtain ⟨root, inside, equal⟩ := List.mem_map.mp
      (List.mem_eraseDups.mp (List.mem_filter.mp member).1)
    have inDistrict : root ∈ component := equal ▸
      (mem_district_iff G current root root).mpr (.seed inside (by simp))
    have discarded :
        (eligible G selection current).any (fun d => d.contains root) = true :=
      List.any_eq_true.mpr ⟨component, member, List.contains_iff_mem.mpr inDistrict⟩
    have subset : (retainedAfter current (eligible G selection current)).Sublist current :=
      List.filter_sublist
    apply Nat.lt_of_le_of_ne subset.length_le
    intro equalLengths
    have keep := List.filter_eq_self.mp (subset.eq_of_length equalLengths) root inside
    change (!(eligible G selection current).any (fun d => d.contains root)) = true at keep
    rw [discarded] at keep
    contradiction

inductive Plan (n : Nat) where
  | restrict (current retained : Vertices n) (next : Plan n)
  | peel (current : Vertices n) (removed : List (Vertices n)) (retained : Vertices n)
      (next : Plan n)
  | identify (current component : Vertices n) (ordinary : List (Instruction n))
  | blocked (current : Vertices n)
  deriving DecidableEq

/-- The Figure 4 branch decisions, including the call to Identify.
The target is a connected district with the supplied root. The
current list includes the selection vertex. -/
def plan (G : MixedGraph n) (selection root : Fin n) (target current : Vertices n) :
    Plan n :=
  let relevant := ancestors G current (target ++ [selection])
  if _prunes : relevant.length < current.length then
    .restrict current relevant (plan G selection root target relevant)
  else
    let clean := eligible G selection current
    match clean.find? (fun d => target.all d.contains) with
    | some component => .identify current component (identifyPlan G target root component)
    | none =>
      let retained := retainedAfter current clean
      if _peels : retained.length < current.length then
        .peel current clean retained (plan G selection root target retained)
      else .blocked current
termination_by current.length

/-- The strict-decrease checks implement the two tests in Figure 4:
restriction has stabilized and no removable component exists. -/
theorem plan_blocks_here_iff (G : MixedGraph n) (selection root : Fin n)
    (target current : Vertices n) :
    plan G selection root target current = .blocked current ↔
      ancestors G current (target ++ [selection]) = current ∧ eligible G selection current = [] := by
  rw [plan]
  by_cases prunes : (ancestors G current (target ++ [selection])).length < current.length
  · have different : ancestors G current (target ++ [selection]) ≠ current := by
      intro same
      rw [same] at prunes
      omega
    simp [prunes, different]
  · have same := ancestors_eq_current_of_no_decrease G current (target ++ [selection]) prunes
    simp only [same, Nat.lt_irrefl, dite_false, true_and]
    change
      ((match (eligible G selection current).find? (fun d => target.all d.contains) with
         | some d => Plan.identify current d (identifyPlan G target root d)
         | none =>
           if (retainedAfter current (eligible G selection current)).length < current.length then
             .peel current (eligible G selection current)
               (retainedAfter current (eligible G selection current))
               (plan G selection root target (retainedAfter current (eligible G selection current)))
           else .blocked current) = .blocked current) ↔ _
    by_cases empty : eligible G selection current = []
    · simp [empty, retainedAfter]
    · have smaller := (peel_shrinks_iff G selection current).mpr empty
      cases found : (eligible G selection current).find? (fun d => target.all d.contains) <;>
        simp [empty, smaller]

variable {G : MixedGraph n} {K : Type}

/-- The two kinds of kernels and the three selected-kernel operations.
The local laws are Figure 4's ancestral marginal, selected prefix
extraction, and division by the extracted ordinary factors. -/
structure Operations (G : MixedGraph n) (selection : Fin n) (K : Type) where
  ordinary : KernelOperations G K
  selected : Vertices n → K
  marginalize : Vertices n → Vertices n → K → K
  extract : Vertices n → Vertices n → K → K
  divide : Vertices n → List (Vertices n) → List K → K → K
  marginalize_ancestors : ∀ current target,
    marginalize current (ancestors G current (target ++ [selection])) (selected current) =
      selected (ancestors G current (target ++ [selection]))
  extract_eligible : ∀ current d, d ∈ eligible G selection current →
    extract current d (selected current) = ordinary.kernel d
  divide_eligible : ∀ current,
    let clean := eligible G selection current
    divide current clean (clean.map ordinary.kernel) (selected current) =
      selected (retainedAfter current clean)

def execute {selection : Fin n} (ops : Operations G selection K) : Plan n → K → Option K
  | .restrict current retained next, input => execute ops next (ops.marginalize current retained input)
  | .peel current clean _ next, input =>
    execute ops next (ops.divide current clean (clean.map (fun d => ops.extract current d input)) input)
  | .identify current component ordinary, input =>
    run ops.ordinary ordinary (ops.extract current component input)
  | .blocked _, _ => none

/-- A successful RC traversal returns the requested population
kernel when its local kernel identities hold. -/
theorem successful_execution_returns_kernel {selection : Fin n} (ops : Operations G selection K)
    (root : Fin n) (target current : Vertices n) {result : K}
    (success : execute ops (plan G selection root target current) (ops.selected current) =
      some result) :
    result = ops.ordinary.kernel target := by
  induction size : current.length using Nat.strongRecOn generalizing current with
  | ind count ih =>
    rw [plan] at success
    split at success
    next prunes =>
      simp only [execute, ops.marginalize_ancestors] at success
      exact ih _ (by omega) _ success rfl
    next =>
      dsimp only at success
      cases found : (eligible G selection current).find? (fun d => target.all d.contains) with
      | some d =>
        rw [found] at success
        have member : d ∈ eligible G selection current := List.mem_of_find?_eq_some found
        simp only [execute, ops.extract_eligible current d member] at success
        exact successful_plan_returns_target ops.ordinary target root d result success
      | none =>
        rw [found] at success
        dsimp only at success
        split at success
        next peels =>
          have same :
              (eligible G selection current).map (fun d => ops.extract current d (ops.selected current)) =
                (eligible G selection current).map ops.ordinary.kernel :=
            List.map_congr_left (fun d member => ops.extract_eligible current d member)
          simp only [execute, same, ops.divide_eligible] at success
          exact ih _ (by omega) _ success rfl
        next =>
          simp [execute] at success

end
end OpenCausalScience.Papers.BareinboimTian2015.RC
