module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyReachability
public import OpenCausalScience.Papers.BareinboimTian2015.RC

/-! # Selected-kernel identities for RC

Bareinboim and Tian (AAAI 2015), Lemma 3 and Theorem 3.
Selection ancestry can be placed first in a topological rank. A
selection multiplier that is constant across a retained prefix fiber
can be pulled outside its finite sum, then canceled between consecutive
prefix marginals. Division by recovered ordinary district factors
preserves the selection multiplier on the remaining kernel.

Sources:
https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=5
https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=6
-/

namespace OpenCausalScience.Papers.BareinboimTian2015.KernelIdentities

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyReachability

@[expose] public section

variable {n : Nat}

/-- A topological rank with every ancestor of selection before any
nonancestor, for a bound larger than all the original ranks. -/
def selectionFirstRank (G : MixedGraph n) (selection : Fin n) (current : Vertices n)
    (height : Nat) (rank : Fin n → Nat) (v : Fin n) : Nat :=
  if (ancestors G current [selection]).contains v then rank v else height + rank v

theorem selection_first_preserves_arrows (G : MixedGraph n) (selection : Fin n)
    (current : Vertices n) (height : Nat) (rank : Fin n → Nat)
    (bounded : ∀ v, rank v < height)
    (ranked : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {u v : Fin n} (inside : u ∈ current) (edge : G.edge u false v true = true) :
    selectionFirstRank G selection current height rank u <
      selectionFirstRank G selection current height rank v := by
  let selected := ancestors G current [selection]
  have closed (before : v ∈ selected) : u ∈ selected :=
    (mem_ancestors_iff G current [selection] u).mpr
      (.step ((mem_ancestors_iff G current [selection] v).mp before) inside edge)
  have ranks := ranked u v edge
  have bound := bounded u
  change (if selected.contains u then rank u else height + rank u) <
    (if selected.contains v then rank v else height + rank v)
  cases upstream : selected.contains u <;> cases downstream : selected.contains v
  · change height + rank u < height + rank v
    omega
  · have member : selected.contains u = true :=
      List.contains_iff_mem.mpr (closed (List.contains_iff_mem.mp downstream))
    rw [upstream] at member
    contradiction
  · change rank u < height + rank v
    omega
  · exact ranks

theorem ancestor_before_eligible_vertex (G : MixedGraph n) (selection : Fin n)
    (current : Vertices n) (height : Nat) (rank : Fin n → Nat)
    (bounded : ∀ v, rank v < height) {d : Vertices n}
    (eligible : d ∈ RC.eligible G selection current)
    {a v : Fin n} (antecedent : a ∈ ancestors G current [selection]) (inDistrict : v ∈ d) :
    selectionFirstRank G selection current height rank a <
      selectionFirstRank G selection current height rank v := by
  have notAncestor : (ancestors G current [selection]).contains v = false := by
    have none := List.all_eq_true.mp (List.mem_filter.mp eligible).2 v inDistrict
    simpa using none
  unfold selectionFirstRank
  simp only [List.contains_iff_mem.mpr antecedent, notAncestor, ite_true, Bool.false_eq_true, ite_false]
  have bound := bounded a
  omega

variable {A : Type}

/-- Selected and population marginals for a finite list of full cells
have the same multiplier when the selection-parent values are fixed
throughout the list. -/
theorem selected_marginal_eq_scale (fiber : List A) (kernel multiplier : A → Rat) (factor : Rat)
    (constant : ∀ cell ∈ fiber, multiplier cell = factor) :
    (fiber.map (fun cell => multiplier cell * kernel cell)).sum =
      factor * (fiber.map kernel).sum := by
  induction fiber with
  | nil => simp [Rat.mul_zero]
  | cons cell rest ih =>
    have first := constant cell List.mem_cons_self
    have remaining := ih (fun v member => constant v (List.mem_cons_of_mem _ member))
    simp [first, remaining, Rat.mul_add]

private theorem cancel_common_scale (factor numerator denominator : Rat) (nonzero : factor ≠ 0) :
    (factor * numerator) / (factor * denominator) = numerator / denominator := by
  rw [Rat.mul_comm factor numerator, Rat.mul_comm factor denominator,
    Rat.div_def (numerator * factor), Rat.inv_mul_rev, Rat.div_def, Rat.mul_assoc,
    ← Rat.mul_assoc factor, Rat.mul_inv_cancel _ nonzero, Rat.one_mul]

/-- Lemma 3, equation (20). The two adjacent prefix fibers have the
same selection-parent assignment and hence the same scale. The
corresponding population ratio is defined by the denominator premise. -/
theorem selected_prefix_ratio_eq_population (after before : List A)
    (kernel multiplier : A → Rat) (factor : Rat)
    (constant : ∀ cell ∈ after ++ before, multiplier cell = factor)
    (scaleSupported : factor ≠ 0) (_denominatorSupported : (before.map kernel).sum ≠ 0) :
    (after.map (fun cell => multiplier cell * kernel cell)).sum /
        (before.map (fun cell => multiplier cell * kernel cell)).sum =
      (after.map kernel).sum / (before.map kernel).sum := by
  rw [selected_marginal_eq_scale after kernel multiplier factor
        (fun v member => constant v (List.mem_append.mpr (.inl member))),
      selected_marginal_eq_scale before kernel multiplier factor
        (fun v member => constant v (List.mem_append.mpr (.inr member)))]
  exact cancel_common_scale _ _ _ scaleSupported

/-- The selected prefix ratios give the same district factor once each
retained prefix pair fixes the selection parents and is supported. -/
theorem selected_district_product_eq_population (prefixes : List (List A × List A))
    (kernel multiplier : A → Rat)
    (supported : ∀ pair ∈ prefixes, ∃ factor ≠ 0,
      (∀ cell ∈ pair.1 ++ pair.2, multiplier cell = factor) ∧ (pair.2.map kernel).sum ≠ 0) :
    (prefixes.map (fun pair =>
      (pair.1.map (fun v => multiplier v * kernel v)).sum /
      (pair.2.map (fun v => multiplier v * kernel v)).sum)).prod =
    (prefixes.map (fun pair =>
      (pair.1.map kernel).sum / (pair.2.map kernel).sum)).prod := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro pair member
  obtain ⟨factor, nonzero, constant, denominator⟩ := supported pair member
  exact selected_prefix_ratio_eq_population pair.1 pair.2 kernel multiplier factor
    constant nonzero denominator

/-- Theorem 3, equations (25)–(26), at each fixed argument assignment. -/
theorem divide_recovered_factors (weighted remaining : Rat)
    (recovered : List Rat) (multiplier : Rat)
    (factorization : weighted = multiplier * remaining * recovered.prod)
    (supported : recovered.prod ≠ 0) :
    weighted / recovered.prod = multiplier * remaining := by
  rw [factorization, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ supported, Rat.mul_one]

/-- An already parameter-invariant recovered formula can integrate
its fixed nuisance arguments against any normalized available law. -/
theorem average_fixed_arguments (rows : List A) (weight value : A → Rat) (target : Rat)
    (invariant : ∀ row ∈ rows, value row = target) (normalized : (rows.map weight).sum = 1) :
    (rows.map (fun row => weight row * value row)).sum = target := by
  have same : (rows.map (fun row => weight row * value row)) =
      (rows.map (fun row => value row * weight row)) :=
    List.map_congr_left (fun row _ => Rat.mul_comm _ _)
  rw [same, selected_marginal_eq_scale rows weight value target invariant, normalized, Rat.mul_one]

end
end OpenCausalScience.Papers.BareinboimTian2015.KernelIdentities
