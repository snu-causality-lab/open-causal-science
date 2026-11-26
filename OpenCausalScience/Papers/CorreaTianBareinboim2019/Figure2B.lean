module
public import OpenCausalScience.Papers.CorreaTianBareinboim2019.HybridDistrict
public import OpenCausalScience.Papers.CorreaLeeBareinboim2021.Figure6

/-! # Figure 2(b), the ratio beyond covariate adjustment

Correa, Tian and Bareinboim (AAAI 2019), equation (23). The two
independent latent blocks behind W1 also enter X and Y, respectively.
At fixed W2, those blocks separate in the mass of (X,Y), but
conditioning on their common child W1 can couple them. Summing
the selected conditional cells over the population margin of W1
before taking the ratio recovers the causal response.

Source: https://causalai.net/r38.pdf#page=7
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2019.Figure2B

open TianPearl2003.AncestralMarginal (mass sum_masses_of_partition)
open CorreaLeeBareinboim2021.Figure6 (productAtoms productWeight product_event_mass)
open PopulationMargin (divide_mul_of_cross)

@[expose] public section

variable {Ω Ξ W₁ W₂ : Type} [DecidableEq W₁]

/-- Private noises can be included in either independent block. The
W2 and selection mechanisms are integrated into their conditional
probabilities at the fixed W2 value. -/
structure Model (Ω Ξ W₁ W₂ : Type) where
  xAtoms : List Ω
  yAtoms : List Ξ
  xWeight : Ω → Rat
  yWeight : Ξ → Rat
  yNormalized : mass yAtoms yWeight (fun _ => true) = 1
  w₁ : Ω × Ξ → W₁
  w₂Mass : W₁ → W₂ → Rat
  selectionMass : W₂ → Rat
  x : W₂ → Ω → Bool
  y : Bool → Ξ → Bool

def Model.unitMass (m : Model Ω Ξ W₁ W₂) : (Ω × Ξ → Bool) → Rat :=
  mass (productAtoms m.xAtoms m.yAtoms) (productWeight m.xWeight m.yWeight)

def Model.populationW₁ (m : Model Ω Ξ W₁ W₂) (a : W₁) : Rat :=
  m.unitMass (fun u => decide (m.w₁ u = a))

def Model.selectedCell (m : Model Ω Ξ W₁ W₂) (a : W₁) (b : W₂)
    (event : Ω × Ξ → Bool) : Rat :=
  m.unitMass (fun u => event u && decide (m.w₁ u = a)) *
    (m.w₂Mass a b * m.selectionMass b)

def Model.integrate (m : Model Ω Ξ W₁ W₂) (values : List W₁) (b : W₂)
    (event : Ω × Ξ → Bool) : Rat :=
  (values.map fun a => (m.selectedCell a b event / m.selectedCell a b (fun _ => true)) *
    m.populationW₁ a).sum

private theorem Model.integrate_eq_unit_mass (m : Model Ω Ξ W₁ W₂) (values : List W₁)
    (nodup : values.Nodup) (exhaustive : ∀ u ∈ productAtoms m.xAtoms m.yAtoms, m.w₁ u ∈ values)
    (b : W₂) (supported : ∀ a ∈ values, m.selectedCell a b (fun _ => true) ≠ 0)
    (event : Ω × Ξ → Bool) :
    m.integrate values b event = m.unitMass event := by
  unfold Model.unitMass
  rw [← sum_masses_of_partition values nodup (productAtoms m.xAtoms m.yAtoms)
    (productWeight m.xWeight m.yWeight) m.w₁ exhaustive event]
  unfold Model.integrate
  congr 1
  apply List.map_congr_left
  intro a present
  apply divide_mul_of_cross (supported a present)
  simp only [Model.selectedCell, Model.populationW₁, Bool.true_and, Model.unitMass]
  rw [Rat.mul_assoc, Rat.mul_comm (m.w₂Mass a b * m.selectionMass b)]

/-- The two sums in the paper's ratio are taken before conditioning on
X. The formula is valid on supported rows and a nonzero final denominator. -/
theorem ratio_eq_interventional_response (m : Model Ω Ξ W₁ W₂)
    (values : List W₁) (nodup : values.Nodup)
    (exhaustive : ∀ u ∈ productAtoms m.xAtoms m.yAtoms, m.w₁ u ∈ values)
    (b : W₂) (x y : Bool)
    (supported : ∀ a ∈ values, m.selectedCell a b (fun _ => true) ≠ 0)
    (hasTreatment : mass m.xAtoms m.xWeight (fun u => m.x b u == x) ≠ 0) :
    m.integrate values b (fun u => (m.x b u.1 == x) && (m.y x u.2 == y)) /
      m.integrate values b (fun u => m.x b u.1 == x) =
      mass m.yAtoms m.yWeight (fun u => m.y x u == y) := by
  rw [m.integrate_eq_unit_mass values nodup exhaustive b supported,
    m.integrate_eq_unit_mass values nodup exhaustive b supported]
  have joint : m.unitMass (fun u => (m.x b u.1 == x) && (m.y x u.2 == y)) =
      mass m.xAtoms m.xWeight (fun u => m.x b u == x) *
        mass m.yAtoms m.yWeight (fun u => m.y x u == y) :=
    product_event_mass m.xAtoms m.yAtoms m.xWeight m.yWeight
      (fun u => m.x b u == x) (fun u => m.y x u == y)
  have denominator : m.unitMass (fun u => m.x b u.1 == x) =
      mass m.xAtoms m.xWeight (fun u => m.x b u == x) := by
    simpa only [Model.unitMass, Bool.and_true, m.yNormalized, Rat.mul_one] using
      (product_event_mass m.xAtoms m.yAtoms m.xWeight m.yWeight
        (fun u => m.x b u == x) (fun _ => true))
  rw [joint, denominator]
  apply HybridDistrict.ratio_eq_of_cross
    ⟨mass m.xAtoms m.xWeight (fun u => m.x b u == x) *
        mass m.yAtoms m.yWeight (fun u => m.y x u == y),
      mass m.xAtoms m.xWeight (fun u => m.x b u == x)⟩
  · exact hasTreatment
  · exact Rat.mul_comm _ _

end
end OpenCausalScience.Papers.CorreaTianBareinboim2019.Figure2B
