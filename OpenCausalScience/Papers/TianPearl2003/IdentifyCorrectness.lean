module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence

/-! # Sound execution of the Identify plan

Tian and Pearl (2003), R-290-L, Figure 7. Interpret the plan with
kernel operations. When ancestral marginalization and c-factor
extraction satisfy their kernel laws, evaluating a successful plan
returns the kernel on the requested set. The ancestor fixed point
has no returned kernel. This proof makes no claim of nonidentifiability
for that branch.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26
-/

namespace OpenCausalScience.Papers.TianPearl2003.IdentifyCorrectness

open IdentifyRecurrence

@[expose] public section

variable {n : Nat} {K : Type} {G : MixedGraph n}

/-- The kernel operations of Figure 7 with their two local semantic
laws. The kernel representation and its cell domains are abstract. -/
structure KernelOperations (G : MixedGraph n) (K : Type) where
  kernel : Vertices n → K
  marginalize : Vertices n → Vertices n → K → K
  extract : Vertices n → Vertices n → K → K
  extensional : ∀ left right,
    (∀ v, v ∈ left ↔ v ∈ right) → kernel left = kernel right
  marginalize_ancestors : ∀ current target,
    marginalize current (ancestors G current target) (kernel current) =
      kernel (ancestors G current target)
  extract_district : ∀ current root,
    extract current (district G current root) (kernel current) = kernel (district G current root)

def run (ops : KernelOperations G K) : List (Instruction n) → K → Option K
  | [], input => some input
  | .marginalize current retained :: remaining, input =>
    run ops remaining (ops.marginalize current retained input)
  | .extractFactor current retained :: remaining, input =>
    run ops remaining (ops.extract current retained input)
  | .ancestorFixedPoint _ :: _, _ => none

private theorem same_vertices_membership (left right : Vertices n)
    (same : sameVertices left right = true) : ∀ v, v ∈ left ↔ v ∈ right := by
  obtain ⟨toRight, toLeft⟩ := Bool.and_eq_true_iff.mp same
  intro v
  exact ⟨fun member => List.contains_iff_mem.mp (List.all_eq_true.mp toRight v member),
    fun member => List.contains_iff_mem.mp (List.all_eq_true.mp toLeft v member)⟩

theorem successful_plan_returns_target (ops : KernelOperations G K) (target : Vertices n)
    (root : Fin n) (current : Vertices n) (value : K)
    (successful : run ops (identifyPlan G target root current) (ops.kernel current) = some value) :
    value = ops.kernel target := by
  induction length : current.length using Nat.strongRecOn generalizing current with
  | ind count ih =>
    let retained := ancestors G current target
    rw [identifyPlan] at successful
    change run ops (if sameVertices retained target then [.marginalize current retained]
      else if retained.length < current.length then
        .marginalize current retained :: .extractFactor retained (district G retained root) ::
          identifyPlan G target root (district G retained root)
      else [.ancestorFixedPoint current]) (ops.kernel current) = some value at successful
    cases same : sameVertices retained target
    · by_cases smaller : retained.length < current.length
      · have shrinks : (district G retained root).length < current.length :=
          recursive_set_smaller G current target root smaller
        have decreases : (district G retained root).length < count := by omega
        simp only [same, Bool.false_eq_true, ite_eq_right (not_false), ite_eq_left smaller, run]
          at successful
        change run ops (identifyPlan G target root (district G retained root))
          (ops.extract retained (district G retained root)
            (ops.marginalize current retained (ops.kernel current))) = some value at successful
        rw [show ops.marginalize current retained (ops.kernel current) = ops.kernel retained
          from ops.marginalize_ancestors current target, ops.extract_district] at successful
        exact ih (district G retained root).length decreases (district G retained root) successful rfl
      · simp [same, smaller, run] at successful
    · have equal : ops.kernel retained = ops.kernel target :=
        ops.extensional retained target (same_vertices_membership retained target same)
      simp only [same, ite_eq_left (show True from trivial), run] at successful
      change some (ops.marginalize current retained (ops.kernel current)) = some value at successful
      have result := Option.some.inj successful
      exact result.symm.trans ((ops.marginalize_ancestors current target).trans equal)

end

end OpenCausalScience.Papers.TianPearl2003.IdentifyCorrectness
