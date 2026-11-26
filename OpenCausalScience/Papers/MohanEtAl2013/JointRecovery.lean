module
public import OpenCausalScience.Papers.BareinboimTian2015.KernelIdentities
public import OpenCausalScience.Papers.BareinboimTianPearl2014.SelectionCriterion

/-! Mohan, Pearl and Tian (2013), Theorem 2 and Equations (6)–(8).
A response indicator is zero in the paper when the variable is observed.
The formulas here use event masses for that value. -/

namespace OpenCausalScience.Papers.MohanEtAl2013.JointRecovery

open OpenCausalScience.Moralization
open BareinboimTian2015.KernelIdentities (selected_marginal_eq_scale)
open BareinboimTianPearl2014.SelectionCriterion (dagQuery)

@[expose] public section

variable {n : Nat}

/-- A response indicator with no children in the substantive/indicator
graph is separated from other nonparents by its substantive parents. -/
theorem sink_indicator_parent_separation (G : DAG n) (indicator : Fin n)
    (other : Fin n → Bool)
    (sink : ∀ v, G.edge indicator v = false)
    (otherNonparent : ∀ v, other v = true → G.edge v indicator = false)
    (distinct : other indicator = false) :
    ¬ (dagQuery G (· == indicator) other (fun v => G.edge v indicator)).DConnection := by
  let query := dagQuery G (· == indicator) other (fun v => G.edge v indicator)
  have leftOutside : ∀ v, query.left v = true → query.condition.member v = false := by
    intro v h
    change (v == indicator) = true at h
    have same := beq_iff_eq.mp h
    subst v
    exact sink indicator
  have rightOutside : ∀ v, query.right v = true → query.condition.member v = false :=
    otherNonparent
  apply (query.dSeparation_iff_no_moralConnection leftOutside rightOutside).mpr
  rintro ⟨x, y, hx, hy, w⟩
  change (x == indicator) = true at hx
  have same := beq_iff_eq.mp hx
  subst x
  cases w with
  | nil => exact Bool.false_ne_true (distinct.symm.trans hy)
  | cons edge _ =>
    rcases edge.connection with outgoing | incoming | ⟨child, _, parentArrow, _⟩
    · exact Bool.false_ne_true ((sink _).symm.trans outgoing)
    · exact Bool.false_ne_true (edge.targetOutside.symm.trans incoming)
    · exact Bool.false_ne_true ((sink child).symm.trans parentArrow)

variable {Ω I : Type}

/-- Observable conditional response probability on an observed parent stratum. -/
def responseRatio (fiber : List Ω) (mass responds : Ω → Rat) : Rat :=
  (fiber.map (fun cell => responds cell * mass cell)).sum / (fiber.map mass).sum

/-- Equation (8): summing over the rest of the observed parent stratum
preserves its response probability if each row has that same rate. -/
theorem response_ratio_eq (fiber : List Ω) (mass responds : Ω → Rat) (rate : Rat)
    (invariant : ∀ cell ∈ fiber, responds cell = rate)
    (supported : (fiber.map mass).sum ≠ 0) :
    responseRatio fiber mass responds = rate := by
  rw [responseRatio, selected_marginal_eq_scale fiber mass responds rate invariant]
  exact Rat.mul_div_cancel supported

private theorem response_product_nonzero (values : List Rat)
    (supported : ∀ p ∈ values, p ≠ 0) : values.prod ≠ 0 := by
  induction values with
  | nil => decide
  | cons p ps ih =>
    have hp := supported p List.mem_cons_self
    have hps := ih (fun x hx => supported x (List.mem_cons_of_mem _ hx))
    simp only [List.prod_cons]
    intro h
    have canceled := Rat.mul_div_cancel (a := p) hps
    simp [h, Rat.div_def, Rat.zero_mul] at canceled
    exact hp canceled.symm

/-- Equation (6), using the complete-case factorization of Equation (7).
Each input stratum contains the substantive parent assignments, restricted
to the observation of every partially observed parent. -/
theorem joint_cell_from_observed_responses (indicators : List I)
    (target complete : Rat) (rate : I → Rat) (parentStratum : I → List Ω)
    (mass responds : I → Ω → Rat)
    (completeFactorization : complete = target * (indicators.map rate).prod)
    (rateInvariant : ∀ i ∈ indicators, ∀ cell ∈ parentStratum i, responds i cell = rate i)
    (stratumSupported : ∀ i ∈ indicators, ((parentStratum i).map (mass i)).sum ≠ 0)
    (ratesSupported : ∀ i ∈ indicators, rate i ≠ 0) :
    complete / (indicators.map fun i => responseRatio (parentStratum i) (mass i) (responds i)).prod =
      target := by
  have observedEq : (indicators.map fun i => responseRatio (parentStratum i) (mass i) (responds i)) =
      indicators.map rate := by
    apply List.map_congr_left
    intro i hi
    exact response_ratio_eq _ _ _ _ (rateInvariant i hi) (stratumSupported i hi)
  have positiveProduct : (indicators.map rate).prod ≠ 0 := by
    apply response_product_nonzero
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact ratesSupported i hi
  rw [observedEq, completeFactorization, Rat.mul_div_cancel positiveProduct]

end
end OpenCausalScience.Papers.MohanEtAl2013.JointRecovery
