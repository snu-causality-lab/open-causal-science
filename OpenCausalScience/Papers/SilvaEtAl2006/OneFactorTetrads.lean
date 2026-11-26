module
public import Std

/-! The one-factor covariance case used by Silva et al. (2006), Section 3.
In the covariance expansion below, the factor is uncorrelated with the
measurement errors, and distinct measurement errors are uncorrelated. -/

@[expose] public section

namespace OpenCausalScience.Papers.SilvaEtAl2006.OneFactorTetrads

variable {V : Type}

def covariance (loading : V → Rat) (factorVariance : Rat)
    (errorCovariance : V → V → Rat) (i j : V) : Rat :=
  loading i * loading j * factorVariance + errorCovariance i j

theorem cross_tetrad_eq_zero (loading : V → Rat) (factorVariance : Rat)
    (errorCovariance : V → V → Rat) (i j k l : V)
    (ik : errorCovariance i k = 0) (il : errorCovariance i l = 0)
    (jk : errorCovariance j k = 0) (jl : errorCovariance j l = 0) :
    let σ := covariance loading factorVariance errorCovariance
    σ i k * σ j l - σ i l * σ j k = 0 := by
  simp only [covariance, ik, il, jk, jl, Rat.add_zero]
  grind

theorem all_three_tetrads_vanish (loading : V → Rat) (factorVariance : Rat)
    (errorCovariance : V → V → Rat) (a b c d : V)
    (offDiagonal : ∀ i j, i ≠ j → errorCovariance i j = 0)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    let σ := covariance loading factorVariance errorCovariance
    σ a b * σ c d = σ a c * σ b d ∧
    σ a b * σ c d = σ a d * σ b c ∧
    σ a c * σ b d = σ a d * σ b c := by
  simp only [covariance, offDiagonal _ _ ab, offDiagonal _ _ ac, offDiagonal _ _ ad,
    offDiagonal _ _ bc, offDiagonal _ _ bd, offDiagonal _ _ cd, Rat.add_zero]
  grind

end OpenCausalScience.Papers.SilvaEtAl2006.OneFactorTetrads
