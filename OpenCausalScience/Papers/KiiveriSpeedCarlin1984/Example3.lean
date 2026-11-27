module
public import OpenCausalScience.Probability.FiniteSummation

/-! # Recursive and undirected Markov constraints in Example 3

The printed covariance and concentration matrices are indexed in the
paper's reverse order 4, 3, 2, 1. The algebra distinguishes the
conditioning sets {1} and {1,4}.
Source: https://doi.org/10.1017/S1446788700027312, p. 41.
-/

namespace OpenCausalScience.Papers.KiiveriSpeedCarlin1984.Example3

open Probability.FiniteSummation

@[expose] public section

def covariance (i j : Fin 4) : Rat :=
  (#[#[4, -2, -2, 1], #[-2, 2, 1, -1], #[-2, 1, 2, -1], #[1, -1, -1, 1]] :
    Array (Array Rat))[i.val]![j.val]!

def concentration (i j : Fin 4) : Rat :=
  (#[#[1, 1, 1, 1], #[1, 2, 1, 2], #[1, 1, 2, 2], #[1, 2, 2, 4]] :
    Array (Array Rat))[i.val]![j.val]!

/-- Coefficients of four independent unit-variance noises. -/
def noiseCoefficients (i j : Fin 4) : Rat :=
  (#[#[1, -1, -1, 1], #[0, 1, 0, -1], #[0, 0, 1, -1], #[0, 0, 0, 1]] :
    Array (Array Rat))[i.val]![j.val]!

theorem covariance_from_noise :
    ∀ i j, covariance i j =
      sumOver (List.finRange 4) (fun k => noiseCoefficients i k * noiseCoefficients j k) := by
  decide +kernel

theorem inverse_calculates :
    ∀ i j, sumOver (List.finRange 4) (fun k => covariance i k * concentration k j) =
      (if i = j then 1 else 0) := by
  decide +kernel

theorem conditional_constraints :
    covariance 2 1 - covariance 2 3 * covariance 3 1 / covariance 3 3 = 0 ∧
      concentration 2 1 = 1 := by
  decide +kernel

end
end OpenCausalScience.Papers.KiiveriSpeedCarlin1984.Example3
