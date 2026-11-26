module
public import OpenCausalScience.Papers.Tian2004.IntrinsicIdentify
public import OpenCausalScience.Papers.TianPearl2003.IdentifyCorrectness

/-! # Selecting a source for a counterfactual factor

Correa, Lee and Bareinboim (2021), Algorithm 1, lines 5–11.
The counterfactual factor and its consistent value assignments have
already been formed. The free vertices of a supplied experiment
exclude its intervention set. The source must retain every target
vertex and admit the Identify plan starting in the relevant district.

Source: https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=8
-/

namespace OpenCausalScience.Papers.CorreaLeeBareinboim2021.SourceKernels

open Tian2004.IntrinsicIdentify
open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyCorrectness

@[expose] public section

variable {n : Nat} {K : Type}

def completes : List (Instruction n) → Bool
  | [] => true
  | .marginalize _ _ :: rest | .extractFactor _ _ :: rest => completes rest
  | .ancestorFixedPoint _ :: _ => false

theorem completes_iff (plan : List (Instruction n)) :
    completes plan = true ↔ PlanSucceeds plan := by
  induction plan with
  | nil => simp [completes, PlanSucceeds]
  | cons command rest ih => cases command <;> simp [completes, PlanSucceeds, ih]

/-- A source consists of the free or randomized vertices of an input
experimental regime. The observational source has all vertices free. -/
def admits (G : MixedGraph n) (target : Vertices n) (root : Fin n)
    (source : Vertices n) : Bool :=
  target.all source.contains &&
    completes (identifyPlan G target root (district G source root))

def findSource (G : MixedGraph n) (target : Vertices n) (root : Fin n)
    (sources : List (Vertices n)) : Option (Vertices n) :=
  sources.find? (admits G target root)

theorem admits_iff {G : MixedGraph n} {target source : Vertices n} {root : Fin n}
    (rank : Fin n → Nat) (ranked : ∀ a b, G.edge a false b true = true → rank a < rank b)
    (rootIn : root ∈ target) (connected : Shpitser2023.FixedPointObstruction.DistrictConnected G target) :
    admits G target root source = true ↔ target ⊆ source ∧ SetReachable G source target := by
  simp only [admits, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, completes_iff]
  constructor
  · rintro ⟨present, succeeds⟩
    exact ⟨present, (component_identify_succeeds_iff_intrinsic rank ranked present rootIn connected).mp succeeds⟩
  · rintro ⟨present, reachable⟩
    exact ⟨present, (component_identify_succeeds_iff_intrinsic rank ranked present rootIn connected).mpr reachable⟩

theorem find_source_iff {G : MixedGraph n} {target : Vertices n} {root : Fin n}
    (sources : List (Vertices n))
    (rank : Fin n → Nat) (ranked : ∀ a b, G.edge a false b true = true → rank a < rank b)
    (rootIn : root ∈ target) (connected : Shpitser2023.FixedPointObstruction.DistrictConnected G target) :
    (findSource G target root sources).isSome = true ↔
      ∃ source ∈ sources, target ⊆ source ∧ SetReachable G source target := by
  simp only [findSource, List.find?_isSome, admits_iff rank ranked rootIn connected]

theorem run_is_some_iff {G : MixedGraph n} (ops : KernelOperations G K)
    (plan : List (Instruction n)) (initial : K) :
    (run ops plan initial).isSome = true ↔ PlanSucceeds plan := by
  induction plan generalizing initial with
  | nil => simp [run, PlanSucceeds]
  | cons command _ ih => cases command <;> simp [run, PlanSucceeds, ih]

/-- A successful source lookup can execute the stream of kernel
operations. The source district kernel has to be available, and the
two operations must obey Tian and Pearl's local kernel laws. -/
theorem selected_source_returns_kernel {G : MixedGraph n} (ops : KernelOperations G K)
    {target source : Vertices n} {root : Fin n} (sources : List (Vertices n))
    (found : findSource G target root sources = some source) :
    run ops (identifyPlan G target root (district G source root)) (ops.kernel (district G source root)) =
      some (ops.kernel target) := by
  have good := List.find?_some found
  have succeeds := completes_iff _ |>.mp (Bool.and_eq_true_iff.mp good).2
  have result := (run_is_some_iff ops _ (ops.kernel (district G source root))).mpr succeeds
  generalize hRun : run ops (identifyPlan G target root (district G source root))
    (ops.kernel (district G source root)) = returned at result ⊢
  cases returned with
  | none => contradiction
  | some value =>
    rw [successful_plan_returns_target ops target root _ value hRun]

end

end OpenCausalScience.Papers.CorreaLeeBareinboim2021.SourceKernels
