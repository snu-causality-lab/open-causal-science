module
public import Std

/-! # Global block maps on product supports

[Kim et al., corrected version](https://www.sanghacklee.me/ai-corrected/CRL_internal_auxiliaries_AI_corrected_2026-10-15.pdf),
Appendix B, the paragraph after App. Assumption 7 and the support row of the
change table, for Propositions 1–2 of the
[proceedings version](https://proceedings.mlr.press/v337/kim26e.html). The
correction requires the true and learned target supports to be Cartesian
products of connected open block supports. It then argues that zero
cross-block derivatives make each matched output block depend only on its
input block, and that bijectivity of the full map between the product supports
makes each block map globally invertible.

This module proves the set-theoretic part of that argument. A support is a
dependent product `∀ i, α i`, where `α i` is the support of block `i` (for
example a subtype of `ℝ^{mᵢ}`). The map `f` is the global map between the
supports, either the learned-to-true map `r` or its inverse. The block
assignment `σ` says which input block each output block reads.

* `FiberConstant f σ`: output block `k` of `f` is constant on every fiber of
  the projection to input block `σ k`. Premise.
* Global bijectivity of `f`. Premise, supplied in the paper by App.
  Assumption 2.
* Injectivity of `σ`, or a two-sided inverse `τ` for the converse. Premise,
  supplied in the paper by the block matching of App. Assumption 6 together
  with the claim that the block assignment is the same at every support point.
* A point of the input product. Premise. `empty_product_counterexample`
  shows the conclusion fails without it.

From these, `blockMap` builds the component maps on the slice through a base
point. `apply_eq_blockMap` gives the exact factorization,
`blockMap_injective` and `blockMap_surjective` derive the two halves of
block bijectivity from the corresponding global halves, `blockMap_unique`
shows the block maps are determined by `f`, and the inverse factors through the
inverse block maps (`matched_block_correspondence`).
`bijective_fiberConstant_iff_blockProduct` characterizes the global maps as
the products of bijective block maps along a block permutation.

`fiberConstant_iff_single_block_invariant` reduces fiber constancy over a
finite block index to invariance under replacing one non-matched block at a
time. That invariance is the analytic input that is still not formalized here:
on each slice obtained by fixing all blocks except one non-matched block `j`,
the map has zero derivative along block `j` (from the rank argument and App.
Assumption 6 at every support point), and the slice is a copy of the connected
open block support of `j`, so the map is constant along it. Differentiability,
the zero off-block Jacobian on the whole support, the point independence of the
block assignment, and the mean value step on connected open sets are not proved
in this module.
-/

namespace OpenCausalScience.Papers.KimEtAl2026.BlockMaps

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

variable {ι : Type u₁} {κ : Type u₂} {α : ι → Type u₃} {β : κ → Type u₄}

/-- Replace input block `i` of a point of the product support by `v`. -/
def replace [DecidableEq ι] (x : ∀ i, α i) (i : ι) (v : α i) (j : ι) : α j :=
  if h : i = j then cast (congrArg α h) v else x j

theorem replace_same [DecidableEq ι] (x : ∀ i, α i) (i : ι) (v : α i) :
    replace x i v i = v := by
  unfold replace
  split
  next => exact cast_eq _ _
  next h => exact absurd rfl h

theorem replace_ne [DecidableEq ι] (x : ∀ i, α i) {i j : ι} (v : α i) (hij : i ≠ j) :
    replace x i v j = x j := by
  unfold replace
  split
  next h => exact absurd h hij
  next => rfl

/-- Output block `k` of `f` depends only on input block `σ k`: it takes one
value on each fiber of the projection to that block. -/
def FiberConstant (f : (∀ i, α i) → ∀ k, β k) (σ : κ → ι) : Prop :=
  ∀ k (x y : ∀ i, α i), x (σ k) = y (σ k) → f x k = f y k

/-- The matched block map of output block `k`, read on the slice through the
base point `x₀` in which only input block `σ k` varies. -/
def blockMap [DecidableEq ι] (f : (∀ i, α i) → ∀ k, β k) (σ : κ → ι) (x₀ : ∀ i, α i)
    (k : κ) (a : α (σ k)) : β k :=
  f (replace x₀ (σ k) a) k

/-- The map whose output block `k` applies `φ k` to input block `σ k`. -/
def blockProduct (σ : κ → ι) (φ : ∀ k, α (σ k) → β k) (x : ∀ i, α i) (k : κ) : β k :=
  φ k (x (σ k))

/-- Exact factorization of a fiber-constant map through its block maps. -/
theorem apply_eq_blockMap [DecidableEq ι] {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι}
    (fiber : FiberConstant f σ) (x₀ x : ∀ i, α i) (k : κ) :
    f x k = blockMap f σ x₀ k (x (σ k)) :=
  fiber k x (replace x₀ (σ k) (x (σ k))) (replace_same x₀ (σ k) (x (σ k))).symm

theorem eq_blockProduct [DecidableEq ι] {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι}
    (fiber : FiberConstant f σ) (x₀ : ∀ i, α i) :
    f = blockProduct σ (blockMap f σ x₀) := by
  funext x k
  exact apply_eq_blockMap fiber x₀ x k

/-- On a nonempty product, any family of block maps through which `f` factors
is the family of slice maps. -/
theorem blockMap_unique [DecidableEq ι] {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι}
    {ψ : ∀ k, α (σ k) → β k} (factors : ∀ x k, f x k = ψ k (x (σ k)))
    (x₀ : ∀ i, α i) (k : κ) (a : α (σ k)) :
    blockMap f σ x₀ k a = ψ k a := by
  unfold blockMap
  rw [factors, replace_same]

/-- The slice maps do not depend on the base point. -/
theorem blockMap_base_independent [DecidableEq ι] {f : (∀ i, α i) → ∀ k, β k}
    {σ : κ → ι} (fiber : FiberConstant f σ) (x₀ x₁ : ∀ i, α i) (k : κ) (a : α (σ k)) :
    blockMap f σ x₀ k a = blockMap f σ x₁ k a :=
  blockMap_unique (fun x l => apply_eq_blockMap fiber x₁ x l) x₀ k a

/-- Global injectivity and an injective block assignment give injective block
maps. Varying input block `σ k` on the slice leaves every other output block
fixed, because no other output block reads `σ k`. -/
theorem blockMap_injective [DecidableEq ι] {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι}
    (fiber : FiberConstant f σ) (σinj : Function.Injective σ) (finj : Function.Injective f)
    (x₀ : ∀ i, α i) (k : κ) : Function.Injective (blockMap f σ x₀ k) := by
  intro a b same
  have outputs : f (replace x₀ (σ k) a) = f (replace x₀ (σ k) b) := by
    funext l
    by_cases hl : l = k
    · subst hl
      exact same
    · apply fiber l
      have distinct : σ k ≠ σ l := fun e => hl (σinj e).symm
      rw [replace_ne x₀ a distinct, replace_ne x₀ b distinct]
  have coordinate := congrFun (finj outputs) (σ k)
  rwa [replace_same, replace_same] at coordinate

/-- Global surjectivity gives surjective block maps. -/
theorem blockMap_surjective [DecidableEq ι] {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι}
    (fiber : FiberConstant f σ) (fsurj : ∀ y, ∃ x, f x = y) (x₀ : ∀ i, α i) (k : κ)
    (b : β k) : ∃ a, blockMap f σ x₀ k a = b := by
  classical
  obtain ⟨x, hx⟩ := fsurj (replace (f x₀) k b)
  refine ⟨x (σ k), ?_⟩
  rw [← apply_eq_blockMap fiber x₀ x k, hx, replace_same]

theorem nonempty_product_iff : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨x⟩ i => ⟨x i⟩, fun h => ⟨fun i => Classical.choice (h i)⟩⟩

/-- The global block-map step: a bijection between a nonempty product support
and a product support whose output blocks are fiber constant along an
injective block assignment factors exactly through unique bijective block
maps. Block injectivity and surjectivity are derived, not assumed. -/
theorem exists_matched_block_maps {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι}
    (fiber : FiberConstant f σ) (σinj : Function.Injective σ)
    (finj : Function.Injective f) (fsurj : ∀ y, ∃ x, f x = y)
    (nonempty : Nonempty (∀ i, α i)) :
    ∃ φ : (∀ k, α (σ k) → β k),
      (∀ k, Function.Injective (φ k)) ∧ (∀ k b, ∃ a, φ k a = b) ∧
      (∀ x k, f x k = φ k (x (σ k))) ∧
      ∀ ψ : (∀ k, α (σ k) → β k), (∀ x k, f x k = ψ k (x (σ k))) →
        ∀ k a, ψ k a = φ k a := by
  classical
  obtain ⟨x₀⟩ := nonempty
  exact ⟨blockMap f σ x₀, fun k => blockMap_injective fiber σinj finj x₀ k,
    fun k b => blockMap_surjective fiber fsurj x₀ k b,
    fun x k => apply_eq_blockMap fiber x₀ x k,
    fun _ factors k a => (blockMap_unique factors x₀ k a).symm⟩

/-! ### Inverse block maps -/

/-- The inverse block map of output block `k`, read on the slice of the output
product through `y₀` in which only block `k` varies. -/
def inverseBlockMap [DecidableEq κ] (g : (∀ k, β k) → ∀ i, α i) (σ : κ → ι)
    (y₀ : ∀ k, β k) (k : κ) (b : β k) : α (σ k) :=
  g (replace y₀ k b) (σ k)

/-- Input block `σ k` of the inverse depends only on output block `k`. -/
theorem inverse_apply_eq_inverseBlockMap [DecidableEq ι] [DecidableEq κ]
    {f : (∀ i, α i) → ∀ k, β k} {g : (∀ k, β k) → ∀ i, α i} {σ : κ → ι}
    (fiber : FiberConstant f σ) (σinj : Function.Injective σ)
    (left : ∀ x, g (f x) = x) (right : ∀ y, f (g y) = y) (x₀ : ∀ i, α i)
    (y₀ y : ∀ k, β k) (k : κ) :
    g y (σ k) = inverseBlockMap g σ y₀ k (y k) := by
  have finj : Function.Injective f := fun a b h =>
    (left a).symm.trans ((congrArg g h).trans (left b))
  apply blockMap_injective fiber σinj finj x₀ k
  unfold inverseBlockMap
  rw [← apply_eq_blockMap fiber x₀ (g y) k,
    ← apply_eq_blockMap fiber x₀ (g (replace y₀ k (y k))) k, right, right, replace_same]

theorem blockMap_inverseBlockMap [DecidableEq ι] [DecidableEq κ]
    {f : (∀ i, α i) → ∀ k, β k} {g : (∀ k, β k) → ∀ i, α i} {σ : κ → ι}
    (fiber : FiberConstant f σ) (right : ∀ y, f (g y) = y) (x₀ : ∀ i, α i)
    (y₀ : ∀ k, β k) (k : κ) (b : β k) :
    blockMap f σ x₀ k (inverseBlockMap g σ y₀ k b) = b := by
  unfold inverseBlockMap
  rw [← apply_eq_blockMap fiber x₀ (g (replace y₀ k b)) k, right, replace_same]

theorem inverseBlockMap_blockMap [DecidableEq ι] [DecidableEq κ]
    {f : (∀ i, α i) → ∀ k, β k} {g : (∀ k, β k) → ∀ i, α i} {σ : κ → ι}
    (fiber : FiberConstant f σ) (σinj : Function.Injective σ)
    (left : ∀ x, g (f x) = x) (right : ∀ y, f (g y) = y) (x₀ : ∀ i, α i)
    (y₀ : ∀ k, β k) (k : κ) (a : α (σ k)) :
    inverseBlockMap g σ y₀ k (blockMap f σ x₀ k a) = a := by
  have h := inverse_apply_eq_inverseBlockMap fiber σinj left right x₀ y₀
    (f (replace x₀ (σ k) a)) k
  rw [left, replace_same] at h
  exact h.symm

/-- Exact correspondence between a global bijection `f` with inverse `g`,
whose output blocks are fiber constant along an injective block assignment,
and its matched block bijections. The output base point is the image of the
input base point, so only the input product has to be nonempty. When `σ` is
surjective the second clause determines every input block of `g y`. -/
theorem matched_block_correspondence [DecidableEq ι] [DecidableEq κ]
    {f : (∀ i, α i) → ∀ k, β k} {g : (∀ k, β k) → ∀ i, α i} {σ : κ → ι}
    (fiber : FiberConstant f σ) (σinj : Function.Injective σ)
    (left : ∀ x, g (f x) = x) (right : ∀ y, f (g y) = y) (x₀ : ∀ i, α i) :
    (∀ x k, f x k = blockMap f σ x₀ k (x (σ k))) ∧
    (∀ y k, g y (σ k) = inverseBlockMap g σ (f x₀) k (y k)) ∧
    (∀ k a, inverseBlockMap g σ (f x₀) k (blockMap f σ x₀ k a) = a) ∧
    (∀ k b, blockMap f σ x₀ k (inverseBlockMap g σ (f x₀) k b) = b) :=
  ⟨fun x k => apply_eq_blockMap fiber x₀ x k,
    fun y k => inverse_apply_eq_inverseBlockMap fiber σinj left right x₀ (f x₀) y k,
    fun k a => inverseBlockMap_blockMap fiber σinj left right x₀ (f x₀) k a,
    fun k b => blockMap_inverseBlockMap fiber right x₀ (f x₀) k b⟩

/-! ### Products of block maps -/

theorem blockProduct_fiberConstant (σ : κ → ι) (φ : ∀ k, α (σ k) → β k) :
    FiberConstant (blockProduct σ φ) σ :=
  fun k _ _ same => congrArg (φ k) same

/-- Injective block maps along a surjective block assignment give an injective
product map. -/
theorem blockProduct_injective {σ : κ → ι} {φ : ∀ k, α (σ k) → β k}
    (φinj : ∀ k, Function.Injective (φ k)) (σsurj : ∀ i, ∃ k, σ k = i) :
    Function.Injective (blockProduct σ φ) := by
  intro x y same
  funext i
  obtain ⟨k, rfl⟩ := σsurj i
  exact φinj k (congrFun same k)

theorem cast_section_eq (σ : κ → ι) (c : ∀ k, α (σ k)) {k k' : κ} (e : k' = k)
    (h : α (σ k') = α (σ k)) : cast h (c k') = c k := by
  subst e
  exact cast_eq _ _

/-- Surjective block maps along a block permutation `σ` with inverse `τ` give
a surjective product map. -/
theorem blockProduct_surjective (σ : κ → ι) (τ : ι → κ) (σ_τ : ∀ i, σ (τ i) = i)
    (τ_σ : ∀ k, τ (σ k) = k) {φ : ∀ k, α (σ k) → β k}
    (φsurj : ∀ k b, ∃ a, φ k a = b) : ∀ y, ∃ x, blockProduct σ φ x = y := by
  intro y
  obtain ⟨c, hc⟩ : ∃ c : (∀ k, α (σ k)), ∀ k, φ k (c k) = y k :=
    ⟨fun k => Classical.choose (φsurj k (y k)),
      fun k => Classical.choose_spec (φsurj k (y k))⟩
  refine ⟨fun i => cast (congrArg α (σ_τ i)) (c (τ i)), ?_⟩
  funext k
  show φ k (cast (congrArg α (σ_τ (σ k))) (c (τ (σ k)))) = y k
  rw [cast_section_eq σ c (τ_σ k)]
  exact hc k

/-- On a nonempty product support and for a block permutation, the global
bijections with fiber-constant output blocks are exactly the products of
bijective block maps. -/
theorem bijective_fiberConstant_iff_blockProduct (σ : κ → ι) (τ : ι → κ)
    (σ_τ : ∀ i, σ (τ i) = i) (τ_σ : ∀ k, τ (σ k) = k)
    (nonempty : Nonempty (∀ i, α i)) (f : (∀ i, α i) → ∀ k, β k) :
    (Function.Injective f ∧ (∀ y, ∃ x, f x = y) ∧ FiberConstant f σ) ↔
      ∃ φ : (∀ k, α (σ k) → β k), (∀ k, Function.Injective (φ k)) ∧
        (∀ k b, ∃ a, φ k a = b) ∧ f = blockProduct σ φ := by
  classical
  constructor
  · rintro ⟨finj, fsurj, fiber⟩
    obtain ⟨x₀⟩ := nonempty
    have σinj : Function.Injective σ := fun a b h =>
      (τ_σ a).symm.trans ((congrArg τ h).trans (τ_σ b))
    exact ⟨blockMap f σ x₀, fun k => blockMap_injective fiber σinj finj x₀ k,
      fun k b => blockMap_surjective fiber fsurj x₀ k b, eq_blockProduct fiber x₀⟩
  · rintro ⟨φ, φinj, φsurj, rfl⟩
    exact ⟨blockProduct_injective φinj (fun i => ⟨τ i, σ_τ i⟩),
      blockProduct_surjective σ τ σ_τ τ_σ φsurj, blockProduct_fiberConstant σ φ⟩

/-! ### Finite coordinate replacement -/

/-- Replacing one input block other than `i₀` leaves `F` unchanged. -/
def SingleBlockInvariant [DecidableEq ι] {γ : Sort u₅} (F : (∀ i, α i) → γ) (i₀ : ι) :
    Prop :=
  ∀ (x : ∀ i, α i) (j : ι) (v : α j), i₀ ≠ j → F (replace x j v) = F x

/-- Points that agree at `i₀` and outside the listed blocks have the same
value. The proof replaces the listed blocks one at a time. -/
theorem eq_of_agree_outside [DecidableEq ι] {γ : Sort u₅} {F : (∀ i, α i) → γ} {i₀ : ι}
    (invariant : SingleBlockInvariant F i₀) (s : List ι) :
    ∀ x y : (∀ i, α i), (∀ j, j ∉ s → x j = y j) → x i₀ = y i₀ → F x = F y := by
  induction s with
  | nil =>
    intro x y outside _
    have same : x = y := funext fun j => outside j (by simp)
    rw [same]
  | cons j rest ih =>
    intro x y outside matched
    have outsideRest : ∀ l, l ∉ rest → l ≠ j → x l = y l := fun l hl hlj =>
      outside l (fun h => (List.mem_cons.mp h).elim hlj hl)
    by_cases hj : i₀ = j
    · refine ih x y ?_ matched
      intro l hl
      by_cases hlj : l = j
      · subst hlj
        subst hj
        exact matched
      · exact outsideRest l hl hlj
    · rw [← invariant x j (y j) hj]
      refine ih (replace x j (y j)) y ?_ ?_
      · intro l hl
        by_cases hlj : j = l
        · subst hlj
          exact replace_same _ _ _
        · rw [replace_ne x (y j) hlj]
          exact outsideRest l hl (fun e => hlj e.symm)
      · have distinct : j ≠ i₀ := fun e => hj e.symm
        rw [replace_ne x (y j) distinct]
        exact matched

/-- With finitely many blocks, single-block invariance gives constancy on the
whole fiber over block `i₀`. -/
theorem eq_of_eq_at_block [DecidableEq ι] {γ : Sort u₅} {F : (∀ i, α i) → γ} {i₀ : ι}
    (blocks : List ι) (complete : ∀ i, i ∈ blocks) (invariant : SingleBlockInvariant F i₀)
    (x y : ∀ i, α i) (matched : x i₀ = y i₀) : F x = F y :=
  eq_of_agree_outside invariant blocks x y (fun j hj => absurd (complete j) hj) matched

/-- Over a finite block index, fiber constancy is equivalent to invariance of
each output block under replacement of any single non-matched input block. -/
theorem fiberConstant_iff_single_block_invariant [DecidableEq ι]
    {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι} (blocks : List ι) (complete : ∀ i, i ∈ blocks) :
    FiberConstant f σ ↔ ∀ k, SingleBlockInvariant (fun x => f x k) (σ k) := by
  constructor
  · intro fiber k x j v distinct
    have outside : j ≠ σ k := fun e => distinct e.symm
    exact fiber k (replace x j v) x (replace_ne x v outside)
  · intro invariant k x y matched
    exact eq_of_eq_at_block blocks complete (invariant k) x y matched

/-- The global block-map step with single-block invariance as the remaining
analytic input. -/
theorem exists_matched_block_maps_of_single_block_invariant [DecidableEq ι]
    {f : (∀ i, α i) → ∀ k, β k} {σ : κ → ι} (blocks : List ι) (complete : ∀ i, i ∈ blocks)
    (invariant : ∀ k, SingleBlockInvariant (fun x => f x k) (σ k))
    (σinj : Function.Injective σ) (finj : Function.Injective f)
    (fsurj : ∀ y, ∃ x, f x = y) (nonempty : Nonempty (∀ i, α i)) :
    ∃ φ : (∀ k, α (σ k) → β k),
      (∀ k, Function.Injective (φ k)) ∧ (∀ k b, ∃ a, φ k a = b) ∧
      (∀ x k, f x k = φ k (x (σ k))) ∧
      ∀ ψ : (∀ k, α (σ k) → β k), (∀ x k, f x k = ψ k (x (σ k))) →
        ∀ k a, ψ k a = φ k a :=
  exists_matched_block_maps
    ((fiberConstant_iff_single_block_invariant blocks complete).mpr invariant)
    σinj finj fsurj nonempty

/-! ### Empty supports -/

/-- Input blocks of the empty-support example. Block `false` is empty. -/
def emptyInputBlock : Bool → Type
  | false => Empty
  | true => Bool

/-- Output blocks of the empty-support example. Block `false` is empty and
block `true` is a point. -/
def emptyOutputBlock : Bool → Type
  | false => Empty
  | true => Unit

theorem emptyOutputBlock_true_subsingleton (u v : emptyOutputBlock true) : u = v := by
  change Unit at u
  change Unit at v
  cases u
  cases v
  rfl

/-- Without a point of the input product the hypotheses hold vacuously but
the conclusion fails. Both products are empty, so the empty map is a
bijection with fiber-constant output blocks along the identity assignment.
The matched block map of block `true` goes from a two-point block to a
one-point block and cannot be injective. -/
theorem empty_product_counterexample :
    (∀ _ : (∀ i, emptyInputBlock i), False) ∧
    ∃ f : (∀ i, emptyInputBlock i) → ∀ k, emptyOutputBlock k,
      Function.Injective f ∧ (∀ y, ∃ x, f x = y) ∧ FiberConstant f id ∧
      ∀ φ : (∀ k, emptyInputBlock (id k) → emptyOutputBlock k),
        ¬ Function.Injective (φ true) := by
  refine ⟨fun x => Empty.elim (x false), fun x => Empty.elim (x false), ?_, ?_, ?_, ?_⟩
  · intro x _ _
    exact Empty.elim (x false)
  · intro y
    exact Empty.elim (y false)
  · intro _ x _ _
    exact Empty.elim (x false)
  · intro φ injective
    have collision : φ true true = φ true false := emptyOutputBlock_true_subsingleton _ _
    have impossible : (true : Bool) = false := injective collision
    exact Bool.noConfusion impossible

end

end OpenCausalScience.Papers.KimEtAl2026.BlockMaps
