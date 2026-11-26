module
public import Std

/-! # Recovering a c-factor from ordered prefix masses

Tian and Pearl, On the Identification of Causal Effects, R-290-L,
Lemma 4(ii), Equations (71)–(72). Prefix masses are products of the
current block factors. At each step only the block containing the
new variable changes. The proof recovers a selected block by taking
just the ratios of consecutive prefix masses at that block's steps.
The graphical derivation of these prefix premises is separate.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=22
-/

namespace OpenCausalScience.Papers.TianPearl2003.QDecomposition

@[expose] public section

variable {ι : Type} [DecidableEq ι]

def jointMass (blocks : List ι) (weights : ι → Rat) : Rat :=
  (blocks.map weights).prod

private def otherMass (blocks : List ι) (block : ι) (weights : ι → Rat) : Rat :=
  jointMass blocks fun k => if k = block then 1 else weights k

private theorem factor_out (blocks : List ι) (block : ι) (weights : ι → Rat)
    (unique : blocks.Nodup) (present : block ∈ blocks) :
    jointMass blocks weights = weights block * otherMass blocks block weights := by
  induction blocks with
  | nil => simp at present
  | cons k rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases head : k = block
    · subst k
      have same : (rest.map fun k => if k = block then (1 : Rat) else weights k) =
          rest.map weights := by
        apply List.map_congr_left
        intro j mem
        have different : j ≠ block := fun equal => absent (equal ▸ mem)
        simp [different]
      simp [jointMass, otherMass, same, Rat.one_mul]
    · have tailPresent : block ∈ rest :=
        (List.mem_cons.mp present).resolve_left (fun equal => head equal.symm)
      have factor := ih tailUnique tailPresent
      simp only [jointMass, otherMass, List.map_cons, List.prod_cons, ite_eq_right head] at factor ⊢
      rw [factor]
      rw [← Rat.mul_assoc, Rat.mul_comm (weights k), Rat.mul_assoc]

theorem prefix_ratio_eq_block_ratio (blocks : List ι) (owner : ι) (before after : ι → Rat)
    (unique : blocks.Nodup) (present : owner ∈ blocks)
    (unchanged : ∀ k, k ≠ owner → after k = before k)
    (supported : jointMass blocks before ≠ 0) :
    jointMass blocks after / jointMass blocks before = after owner / before owner := by
  have otherSame : otherMass blocks owner after = otherMass blocks owner before := by
    unfold otherMass jointMass
    apply congrArg List.prod
    apply List.map_congr_left
    intro k _
    by_cases same : k = owner <;> simp [same, unchanged]
  rw [factor_out blocks owner after unique present, factor_out blocks owner before unique present,
    otherSame]
  have otherNonzero : otherMass blocks owner before ≠ 0 := by
    intro zero
    apply supported
    rw [factor_out blocks owner before unique present, zero, Rat.mul_zero]
  rw [Rat.div_def (after owner * otherMass blocks owner before), Rat.inv_mul_rev,
    Rat.div_def, Rat.mul_assoc, ← Rat.mul_assoc (otherMass blocks owner before),
    Rat.mul_inv_cancel _ otherNonzero, Rat.one_mul]

/-- An ordered prefix extension adds one vertex from the named block and
records the resulting partial block factors at the fixed cell. -/
abbrev Prefix (ι : Type) := ι × (ι → Rat)

inductive PrefixChanges (blocks : List ι) : (ι → Rat) → List (Prefix ι) → Prop
  | nil (before) : PrefixChanges blocks before []
  | cons {before after : ι → Rat} {owner : ι} {remaining : List (Prefix ι)}
      (present : owner ∈ blocks)
      (unchanged : ∀ k, k ≠ owner → after k = before k)
      (supported : jointMass blocks before ≠ 0)
      (later : PrefixChanges blocks after remaining) :
      PrefixChanges blocks before ((owner, after) :: remaining)

def finalFactors (before : ι → Rat) : List (Prefix ι) → ι → Rat
  | [] => before
  | (_, after) :: remaining => finalFactors after remaining

/-- Equation (71), expressed through the joint marginal at each prefix. -/
def recoveredFactor (blocks : List ι) (selected : ι) (before : ι → Rat) :
    List (Prefix ι) → Rat
  | [] => 1
  | (owner, after) :: remaining =>
    (if owner = selected then jointMass blocks after / jointMass blocks before else 1) *
      recoveredFactor blocks selected after remaining

theorem scaled_recovered_factor (blocks : List ι) (unique : blocks.Nodup) (selected : ι)
    {before : ι → Rat} {prefixes : List (Prefix ι)}
    (changes : PrefixChanges blocks before prefixes) :
    before selected * recoveredFactor blocks selected before prefixes =
      finalFactors before prefixes selected := by
  induction changes with
  | nil before => simp [recoveredFactor, finalFactors, Rat.mul_one]
  | @cons before after owner remaining present unchanged supported later ih =>
    by_cases same : owner = selected
    · subst owner
      have nonzero : before selected ≠ 0 := by
        intro zero
        apply supported
        rw [factor_out blocks selected before unique present, zero, Rat.zero_mul]
      simp [recoveredFactor, finalFactors]
      rw [prefix_ratio_eq_block_ratio blocks selected before after unique present unchanged supported,
        ← Rat.mul_assoc, Rat.mul_comm (before selected) (after selected / before selected),
        Rat.div_mul_cancel nonzero, ih]
    · have stayed := unchanged selected (fun equal => same equal.symm)
      simp only [recoveredFactor, finalFactors, ite_eq_right same, Rat.one_mul]
      rw [← stayed, ih]

theorem recovered_factor_eq_final (blocks : List ι) (unique : blocks.Nodup) (selected : ι)
    {before : ι → Rat} {prefixes : List (Prefix ι)}
    (initial : before selected = 1) (changes : PrefixChanges blocks before prefixes) :
    recoveredFactor blocks selected before prefixes = finalFactors before prefixes selected := by
  have recovered := scaled_recovered_factor blocks unique selected changes
  rwa [initial, Rat.one_mul] at recovered

end

end OpenCausalScience.Papers.TianPearl2003.QDecomposition
