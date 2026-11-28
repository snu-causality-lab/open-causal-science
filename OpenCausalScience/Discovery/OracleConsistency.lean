module
public import OpenCausalScience.Discovery.FiniteCIQueries
public import OpenCausalScience.Discovery.OrderDAG
public import OpenCausalScience.Probability.FiniteErrors

/-! # Pointwise CI errors and finite-oracle search -/

namespace OpenCausalScience.Discovery

open Probability FiniteCIQueries

@[expose] public section

variable {n : Nat}

def oracleError (observed exact : CIOracle n) (q : Comparison n) : Bool :=
  observed q.1 q.2.1 q.2.2 != exact q.1 q.2.1 q.2.2

theorem oracle_eq_of_no_errors {observed exact : CIOracle n}
    (noError : (comparisons n).any (oracleError observed exact) = false) : observed = exact := by
  funext x y conditioned
  by_cases same : observed x y conditioned = exact x y conditioned
  · exact same
  · have failure : (comparisons n).any (oracleError observed exact) = true :=
      List.any_eq_true.mpr ⟨(x, y, conditioned), mem_comparisons x y conditioned,
        by simp [oracleError, same]⟩
    exact (Bool.false_ne_true (noError.symm.trans failure)).elim

/-- Pointwise agreement in probability on a fixed finite vertex set
transfers to the output of every deterministic oracle algorithm. -/
theorem sample_oracle_error_vanishes {α : Type} {Ω : Nat → Type}
    (law : ∀ m, FiniteLaw (Ω m)) (observed : ∀ m, Ω m → CIOracle n) (exact : CIOracle n)
    (algorithm : CIOracle n → α) (correct : α → Prop) (population : correct (algorithm exact))
    (each : ∀ q ∈ comparisons n, ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => oracleError (observed m a) exact q) < ε) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => @decide (¬ correct (algorithm (observed m a))) (Classical.propDecidable _)) < ε := by
  classical
  intro ε positive
  obtain ⟨N, all⟩ := finite_library_error_vanishes law
    (fun m q a => oracleError (observed m a) exact q) (comparisons n) each ε positive
  refine ⟨N, fun m later => rat_lt_of_le_of_lt ?_ (all m later)⟩
  apply FiniteLaw.mass_mono
  intro a _ failed
  change (comparisons n).any (oracleError (observed m a) exact) = true
  cases status : (comparisons n).any (oracleError (observed m a) exact) with
  | true => rfl
  | false =>
    have same := oracle_eq_of_no_errors status
    have worked : correct (algorithm (observed m a)) := by
      rw [same]
      exact population
    exact ((@of_decide_eq_true _ (Classical.propDecidable _) failed) worked).elim

end

end OpenCausalScience.Discovery
