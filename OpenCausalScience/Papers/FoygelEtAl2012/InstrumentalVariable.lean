module
public import Std

/-! Foygel, Draisma and Drton (2012), Example 1 and Figure 1.
The covariance equations are for the centered linear model. -/

@[expose] public section

namespace OpenCausalScience.Papers.FoygelEtAl2012.InstrumentalVariable

/-- Covariance with the instrument is linear in the other argument. -/
structure InstrumentMoment (Ω : Type) where
  cov : (Ω → Rat) → Rat
  add : ∀ x y, cov (fun u => x u + y u) = cov x + cov y
  scale : ∀ (a : Rat) x, cov (fun u => a * x u) = a * cov x

theorem coefficient_from_instrument {Ω : Type} (moment : InstrumentMoment Ω)
    (x y error : Ω → Rat) (coefficient : Rat)
    (equation : y = fun u => coefficient * x u + error u)
    (uncorrelated : moment.cov error = 0)
    (relevant : moment.cov x ≠ 0) :
    moment.cov y / moment.cov x = coefficient := by
  rw [equation, moment.add, moment.scale, uncorrelated, Rat.add_zero, Rat.mul_div_cancel relevant]

theorem example1_coefficients {Ω : Type} (moment : InstrumentMoment Ω)
    (z x y ex ey : Ω → Rat) (a b : Rat)
    (first : x = fun u => a * z u + ex u)
    (second : y = fun u => b * x u + ey u)
    (exOrthogonal : moment.cov ex = 0)
    (eyOrthogonal : moment.cov ey = 0)
    (instrumentVariance : moment.cov z ≠ 0)
    (relevant : moment.cov x ≠ 0) :
    moment.cov x / moment.cov z = a ∧ moment.cov y / moment.cov x = b :=
  ⟨coefficient_from_instrument moment z x ex a first exOrthogonal instrumentVariance,
   coefficient_from_instrument moment x y ey b second eyOrthogonal relevant⟩

end OpenCausalScience.Papers.FoygelEtAl2012.InstrumentalVariable
