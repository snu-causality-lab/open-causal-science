module
public import Mathlib.Analysis.Calculus.MeanValue
public import OpenCausalScience.Papers.KimEtAl2026.BlockMaps

/-! # Global block maps from zero derivatives on connected supports

In Appendix B of the [corrected version](https://www.sanghacklee.me/ai-corrected/CRL_internal_auxiliaries_AI_corrected_2026-10-15.pdf),
the argument after App. Assumption 7 uses the connected open block supports in
Assumption 1. Vary one non-matching input block while fixing the others. The
slice is a copy of that block support, so vanishing derivative everywhere on it
implies constancy. Finitely many such replacements establish fiber constancy.
A bijection of the whole supports then gives a bijection of each matched pair.
Continuous Jacobian blocks with a unique pointwise matching also yield a
constant matching across the support. The pointwise derivative identities and
matching are premises supplied by Appendix B’s earlier argument.
-/

namespace OpenCausalScience.Papers.KimEtAl2026.ConnectedBlockMaps

open BlockMaps

@[expose] public section

variable {ι κ : Type*} {E : ι → Type*} {F : κ → Type*}

/-- The Cartesian product of the block supports. -/
abbrev Support (U : ∀ i, Set (E i)) := ∀ i, ↥(U i)

/-- Restrict the ambient map to the specified input and output supports. -/
def restrict {U : ∀ i, Set (E i)} {V : ∀ k, Set (F k)}
    (r : (∀ i, E i) → ∀ k, F k)
    (maps : ∀ (x : Support U) k, r (fun i => (x i).val) k ∈ V k) :
    Support U → Support V :=
  fun x k => ⟨r (fun i => (x i).val) k, maps x k⟩

/-- The `k`-th output on the slice in which only input block `j` varies. -/
def slice [DecidableEq ι] {U : ∀ i, Set (E i)}
    (r : (∀ i, E i) → ∀ k, F k) (x : Support U) (k : κ) (j : ι) : E j → F k :=
  fun z => r (replace (fun i => (x i).val) j z) k

private theorem replace_val [DecidableEq ι] {U : ∀ i, Set (E i)}
    (x : Support U) (j : ι) (v : U j) :
    (fun i => (replace x j v i).val) = replace (fun i => (x i).val) j v.val := by
  funext i
  by_cases same : j = i
  · subst i
    rw [replace_same, replace_same]
  · rw [replace_ne _ _ same, replace_ne _ _ same]

private theorem replace_self [DecidableEq ι] (x : ∀ i, E i) (j : ι) :
    replace x j (x j) = x := by
  funext i
  by_cases same : j = i
  · subst i
    exact replace_same x j (x j)
  · exact replace_ne x (x j) same

private theorem replace_twice [DecidableEq ι] (x : ∀ i, E i) (j : ι) (v w : E j) :
    replace (replace x j v) j w = replace x j w := by
  funext i
  by_cases same : j = i
  · subst i
    rw [replace_same, replace_same]
  · simp only [replace_ne _ _ same]

private theorem product_nonempty [∀ i, TopologicalSpace (E i)] {U : ∀ i, Set (E i)}
    (connectedU : ∀ j, IsConnected (U j)) : Nonempty (Support U) :=
  nonempty_product_iff.mpr fun j =>
    let ⟨z, hz⟩ := (connectedU j).nonempty
    ⟨⟨z, hz⟩⟩

variable
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ k, NormedAddCommGroup (F k)] [∀ k, NormedSpace ℝ (F k)]

/-- Zero off-block derivatives on the entire product of connected open supports
imply global constancy on the fibers of the matched block projection. -/
theorem fiberConstant_of_zero_off_block_deriv [DecidableEq ι]
    {U : ∀ i, Set (E i)} {V : ∀ k, Set (F k)}
    {r : (∀ i, E i) → ∀ k, F k} {σ : κ → ι}
    (maps : ∀ (x : Support U) k, r (fun i => (x i).val) k ∈ V k)
    (blocks : List ι) (complete : ∀ j, j ∈ blocks)
    (openU : ∀ j, IsOpen (U j)) (connectedU : ∀ j, IsConnected (U j))
    (zeroDeriv : ∀ (x : Support U) k j, σ k ≠ j → ∀ z ∈ U j,
      HasFDerivAt (𝕜 := ℝ) (slice r x k j) 0 z) : FiberConstant (restrict r maps) σ := by
  apply (fiberConstant_iff_single_block_invariant blocks complete).mpr
  intro k x j v different
  apply Subtype.ext
  change r (fun i => (replace x j v i).val) k = r (fun i => (x i).val) k
  rw [replace_val x j v]
  have h : slice r x k j v.val = slice r x k j (x j).val :=
    (openU j).is_const_of_fderiv_eq_zero (connectedU j).isPreconnected
      (fun z hz => (zeroDeriv x k j different z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (zeroDeriv x k j different z hz).fderiv) v.property (x j).property
  simpa only [slice, replace_self] using h

/-- The matched component maps are unique bijections of the block supports
under the derivative assumptions and a bijective map of the whole supports. -/
theorem exists_matched_block_maps_of_zero_off_block_deriv [DecidableEq ι]
    {U : ∀ i, Set (E i)} {V : ∀ k, Set (F k)}
    {r : (∀ i, E i) → ∀ k, F k} {σ : κ → ι}
    (maps : ∀ (x : Support U) k, r (fun i => (x i).val) k ∈ V k)
    (blocks : List ι) (complete : ∀ j, j ∈ blocks)
    (openU : ∀ j, IsOpen (U j)) (connectedU : ∀ j, IsConnected (U j))
    (zeroDeriv : ∀ (x : Support U) k j, σ k ≠ j → ∀ z ∈ U j,
      HasFDerivAt (𝕜 := ℝ) (slice r x k j) 0 z)
    (σinj : Function.Injective σ) (bijective : Function.Bijective (restrict r maps)) :
    ∃ φ : ∀ k, U (σ k) → V k,
      (∀ k, Function.Bijective (φ k)) ∧
      (∀ x k, restrict r maps x k = φ k (x (σ k))) ∧
      ∀ ψ : (∀ k, U (σ k) → V k), (∀ x k, restrict r maps x k = ψ k (x (σ k))) →
        ∀ k a, ψ k a = φ k a := by
  have fiber := fiberConstant_of_zero_off_block_deriv maps blocks complete openU connectedU
    zeroDeriv
  obtain ⟨φ, inj, surj, factors, unique⟩ := exists_matched_block_maps fiber σinj
    bijective.injective bijective.surjective (product_nonempty connectedU)
  exact ⟨φ, fun k => ⟨inj k, surj k⟩, factors, unique⟩

/-- Continuous Jacobian blocks with a unique nonzero block for each output
have the same matching at every point of the connected product support. -/
theorem exists_global_block_matching {U : ∀ i, Set (E i)}
    (connectedU : ∀ j, IsConnected (U j))
    (D : ∀ k j, Support U → (E j →L[ℝ] F k))
    (continuousD : ∀ k j, Continuous (D k j))
    (pointwiseMatching : ∀ x, ∃ σ : κ → ι, Function.Injective σ ∧
      ∀ k j, D k j x ≠ 0 ↔ σ k = j) :
    ∃ σ : κ → ι, Function.Injective σ ∧ ∀ x k j, D k j x ≠ 0 ↔ σ k = j := by
  classical
  let : ∀ j, PreconnectedSpace ↥(U j) :=
    fun j => Subtype.preconnectedSpace (connectedU j).isPreconnected
  choose matchAt matchInj nonzero using pointwiseMatching
  have locallyConstant (k : κ) : IsLocallyConstant (fun x => matchAt x k) := by
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro j
    have fiber : (fun x => matchAt x k) ⁻¹' {j} =
        (D k j) ⁻¹' ({0} : Set (E j →L[ℝ] F k))ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
      exact (nonzero x k j).symm
    rw [fiber]
    exact isClosed_singleton.isOpen_compl.preimage (continuousD k j)
  obtain ⟨x₀⟩ := product_nonempty connectedU
  refine ⟨matchAt x₀, matchInj x₀, fun x k j => ?_⟩
  rw [nonzero x k j, (locallyConstant k).apply_eq_of_preconnectedSpace x x₀]

/-- A bijection with continuous, pointwise matched Jacobian blocks globally
factors into unique bijections between the corresponding block supports. -/
theorem exists_matched_block_maps_of_continuous_block_derivatives [DecidableEq ι]
    {U : ∀ i, Set (E i)} {V : ∀ k, Set (F k)}
    {r : (∀ i, E i) → ∀ k, F k}
    (maps : ∀ (x : Support U) k, r (fun i => (x i).val) k ∈ V k)
    (blocks : List ι) (complete : ∀ j, j ∈ blocks)
    (openU : ∀ j, IsOpen (U j)) (connectedU : ∀ j, IsConnected (U j))
    (D : ∀ k j, Support U → (E j →L[ℝ] F k))
    (derivative : ∀ x k j, HasFDerivAt (𝕜 := ℝ) (slice r x k j) (D k j x) (x j).val)
    (continuousD : ∀ k j, Continuous (D k j))
    (pointwiseMatching : ∀ x, ∃ σ : κ → ι, Function.Injective σ ∧
      ∀ k j, D k j x ≠ 0 ↔ σ k = j)
    (bijective : Function.Bijective (restrict r maps)) :
    ∃ σ : κ → ι, Function.Injective σ ∧ (∀ x k j, D k j x ≠ 0 ↔ σ k = j) ∧
      ∃ φ : ∀ k, U (σ k) → V k,
      (∀ k, Function.Bijective (φ k)) ∧
      (∀ x k, restrict r maps x k = φ k (x (σ k))) ∧
      ∀ ψ : (∀ k, U (σ k) → V k), (∀ x k, restrict r maps x k = ψ k (x (σ k))) →
        ∀ k a, ψ k a = φ k a := by
  obtain ⟨σ, σinj, nonzero⟩ := exists_global_block_matching connectedU D continuousD pointwiseMatching
  have zeroDeriv (x : Support U) (k : κ) (j : ι) (different : σ k ≠ j)
      (z : E j) (hz : z ∈ U j) : HasFDerivAt (𝕜 := ℝ) (slice r x k j) 0 z := by
    let y := replace x j ⟨z, hz⟩
    have hvalue : (y j).val = z := by simp only [y, replace_same]
    have sameSlice : slice r y k j = slice r x k j := by
      funext w
      unfold slice
      rw [show (fun i => (y i).val) = replace (fun i => (x i).val) j z from
        replace_val x j ⟨z, hz⟩, replace_twice]
    have hzero : D k j y = 0 := by
      by_contra hn
      exact different ((nonzero y k j).mp hn)
    simpa only [hvalue, sameSlice, hzero] using derivative y k j
  exact ⟨σ, σinj, nonzero, exists_matched_block_maps_of_zero_off_block_deriv maps blocks complete
    openU connectedU zeroDeriv σinj bijective⟩

end
end OpenCausalScience.Papers.KimEtAl2026.ConnectedBlockMaps
