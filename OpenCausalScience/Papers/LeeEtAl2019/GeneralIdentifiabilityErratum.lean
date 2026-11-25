module
public import Std

/-! # General Identifiability with Arbitrary Surrogate Experiments (Lee et al.)

Source: the July 2022 erratum [R-46e](https://causalai.net/r46e.pdf),
equations (A.1) and (A.2) and the following frontier and bottom-noise
prescriptions.

The first results check the Boolean aggregation and the frontier-parity rule.
The bottom-noise results check the independent bit flips on finite tables of
integer weights, with a common positive denominator for probability tables.
The incidence counts used by the parity argument and the construction of
models agreeing on the available interventions are separate graph and model
claims.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.GeneralIdentifiabilityErratum

@[expose] public section

def xorAll : List Bool → Bool
  | [] => false
  | b :: bits => Bool.xor b (xorAll bits)

theorem xor_all_append (xs ys : List Bool) :
    xorAll (xs ++ ys) = Bool.xor (xorAll xs) (xorAll ys) := by
  induction xs with
  | nil => simpa only [List.nil_append, xorAll] using (Bool.false_xor (xorAll ys)).symm
  | cons x xs ih =>
    simp only [List.cons_append, xorAll, ih]
    exact (Bool.xor_assoc _ _ _).symm

theorem xor_all_eq_of_perm {xs ys : List Bool} (perm : xs.Perm ys) :
    xorAll xs = xorAll ys := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp only [xorAll, ih]
  | swap a b tail =>
    simp only [xorAll]
    exact Bool.xor_left_comm b a (xorAll tail)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem xor_all_flatten (groups : List (List Bool)) :
    xorAll (groups.map xorAll) = xorAll groups.flatten := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
    simp only [List.map_cons, xorAll, List.flatten_cons, xor_all_append, ih]

structure XorInputGroup where
  parents : List Bool
  confounders : List Bool

def groupBit (input : XorInputGroup) : Bool :=
  Bool.xor (xorAll input.parents) (xorAll input.confounders)

private theorem xor_interchange (a b c d : Bool) :
    Bool.xor (Bool.xor a b) (Bool.xor c d) = Bool.xor (Bool.xor a c) (Bool.xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Equation (A.1) distributes over parent and confounder occurrences. -/
theorem xor_groups_aggregate (inputs : List XorInputGroup) :
    xorAll (inputs.map groupBit) =
      Bool.xor (xorAll (inputs.flatMap XorInputGroup.parents))
        (xorAll (inputs.flatMap XorInputGroup.confounders)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
    simp only [List.map_cons, List.flatMap_cons, xorAll, xor_all_append, ih, groupBit]
    exact xor_interchange _ _ _ _

/-- Equation (A.2) can group occurrences into hedge-level parent bits and
confounder bits when flattening each grouping keeps the original occurrences. -/
theorem xor_groups_eq_regrouped_xor (inputs : List XorInputGroup)
    (parentGroups confounderGroups : List (List Bool))
    (parents : (inputs.flatMap XorInputGroup.parents).Perm parentGroups.flatten)
    (confounders : (inputs.flatMap XorInputGroup.confounders).Perm confounderGroups.flatten) :
    xorAll (inputs.map groupBit) =
      Bool.xor (xorAll (parentGroups.map xorAll)) (xorAll (confounderGroups.map xorAll)) := by
  rw [xor_groups_aggregate, xor_all_flatten, xor_all_flatten,
    xor_all_eq_of_perm parents, xor_all_eq_of_perm confounders]

private theorem paired_xor_is_false (bits : List Bool) :
    xorAll (bits.flatMap fun b => [b, b]) = false := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.flatMap_cons, xor_all_append, ih]
    cases b <;> rfl

/-- Cancellation given the two incidences of each
internal confounder and the single incidences of crossing confounders are given. -/
theorem xor_eq_crossings_of_paired_internal (total crossing internal : List Bool)
    (incidences : total.Perm (crossing ++ internal.flatMap fun b => [b, b])) :
    xorAll total = xorAll crossing := by
  rw [xor_all_eq_of_perm incidences, xor_all_append, paired_xor_is_false]
  exact Bool.xor_false _

def countParity : Nat → Bool
  | 0 => false
  | n + 1 => !countParity n

theorem count_parity_eq (n : Nat) : countParity n = (n % 2 == 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countParity, ih]
    by_cases h : n % 2 = 1
    · have next : n.succ % 2 ≠ 1 := by omega
      simp [h, next]
    · have next : n.succ % 2 = 1 := by omega
      simp [h, next]

theorem xor_all_replicate_true (n : Nat) : xorAll (List.replicate n true) = countParity n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, xorAll, countParity, ih, Bool.true_xor]

private theorem xor_all_flip_at (front back : List Bool) (bit : Bool) :
    xorAll (front ++ (!bit) :: back) = !(xorAll (front ++ bit :: back)) := by
  simp only [xor_all_append, xorAll, Bool.not_xor, Bool.xor_not]

private theorem false_mem_of_xor_all_ne_parity (bits : List Bool)
    (h : xorAll bits ≠ countParity bits.length) : false ∈ bits := by
  induction bits with
  | nil => exact False.elim (h rfl)
  | cons b bits ih =>
    cases b with
    | false => simp
    | true =>
      apply List.mem_cons_of_mem true
      apply ih
      intro tail
      apply h
      simp only [xorAll, List.length_cons, countParity, tail]
      cases countParity bits.length <;> rfl

/-- `front`, `bit`, and `back` record the arbitrary selected frontier and
its neighbors in the ordered list of frontier bits. -/
def correctedFrontiers (crossingCount : Nat) (front : List Bool) (bit : Bool)
    (back : List Bool) : List Bool :=
  if countParity crossingCount = countParity (front ++ bit :: back).length
  then front ++ (!bit) :: back
  else front ++ bit :: back

/-- In the all-one crossing case, Lemma 2 supplies the pre-negation parity.
The rule in R-46e forces a zero at some frontier whenever that parity holds. -/
theorem corrected_frontiers_contain_false (crossingCount : Nat) (front : List Bool)
    (bit : Bool) (back : List Bool)
    (before : xorAll (front ++ bit :: back) = countParity crossingCount) :
    false ∈ correctedFrontiers crossingCount front bit back := by
  unfold correctedFrontiers
  split
  next same =>
    apply false_mem_of_xor_all_ne_parity
    rw [xor_all_flip_at, before, same]
    simp [List.length_append]
  next different =>
    apply false_mem_of_xor_all_ne_parity
    rw [before]
    exact different

abbrev WeightTable (α : Type) := (α → Bool) → Nat

/-- Replace a bottom-bit assignment by the assignment that flips one bit. -/
def flipAt {α : Type} [DecidableEq α] (i : α) (assignment : α → Bool) : α → Bool :=
  fun j => if j = i then !(assignment j) else assignment j

private theorem flip_at_involutive {α : Type} [DecidableEq α] (i : α)
    (assignment : α → Bool) : flipAt i (flipAt i assignment) = assignment := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

/-- One independent XOR noise bit with probability `flip / (keep + flip)`.
The transformed integer weights use the corresponding multiplied denominator. -/
def noiseAt {α : Type} [DecidableEq α] (keep flip : Nat) (i : α)
    (law : WeightTable α) : WeightTable α :=
  fun out => keep * law out + flip * law (flipAt i out)

private theorem weighted_sum_strict (keep flip a b c d : Nat)
    (bias : flip < keep) (totals : a + b = c + d) (greater : c < a) :
    keep * c + flip * d < keep * a + flip * b := by
  let δ := a - c
  have δpos : 0 < δ := by dsimp [δ]; omega
  have a_eq : a = c + δ := by dsimp [δ]; omega
  have d_eq : d = b + δ := by dsimp [δ]; omega
  have scaled := Nat.mul_lt_mul_of_pos_right bias δpos
  rw [a_eq, d_eq, Nat.mul_add, Nat.mul_add]
  omega

private theorem eq_of_weighted_pair_eq (keep flip a b c d : Nat)
    (bias : flip < keep)
    (first : keep * a + flip * b = keep * c + flip * d)
    (second : keep * b + flip * a = keep * d + flip * c) : a = c := by
  have sum_identity (u v : Nat) :
      keep * u + flip * v + (keep * v + flip * u) = (keep + flip) * (u + v) := by
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  have multiplied :
      (keep * a + flip * b) + (keep * b + flip * a) =
        (keep * c + flip * d) + (keep * d + flip * c) := by
    rw [first, second]
  rw [sum_identity, sum_identity] at multiplied
  have totals : a + b = c + d := by
    by_cases h : a + b < c + d
    · have strict := Nat.mul_lt_mul_of_pos_left h (by omega : 0 < keep + flip)
      omega
    · by_cases h' : c + d < a + b
      · have strict := Nat.mul_lt_mul_of_pos_left h' (by omega : 0 < keep + flip)
        omega
      · omega
  by_cases h : a < c
  · have strict := weighted_sum_strict keep flip c d a b bias totals.symm h
    omega
  · by_cases h' : c < a
    · have strict := weighted_sum_strict keep flip a b c d bias totals h'
      omega
    · omega

theorem noise_at_injective {α : Type} [DecidableEq α] (keep flip : Nat) (i : α)
    (biased : keep ≠ flip) : Function.Injective (noiseAt keep flip i) := by
  intro p q equal
  funext out
  have first := congrFun equal out
  have second := congrFun equal (flipAt i out)
  simp only [noiseAt, flip_at_involutive] at first second
  by_cases bias : flip < keep
  · exact eq_of_weighted_pair_eq keep flip _ _ _ _ bias first second
  · have reverseBias : keep < flip := by omega
    refine eq_of_weighted_pair_eq flip keep (p out) (p (flipAt i out))
      (q out) (q (flipAt i out)) reverseBias ?_ ?_
    · simpa only [Nat.add_comm] using second
    · simpa only [Nat.add_comm] using first

/-- Apply independent copies of the same noise channel at each listed bit. -/
def noiseAll {α : Type} [DecidableEq α] (keep flip : Nat) : List α → WeightTable α → WeightTable α
  | [], law => law
  | i :: is, law => noiseAt keep flip i (noiseAll keep flip is law)

/-- Independent biased flipping preserves any disagreement of finite weight
tables in a shared representation. -/
theorem noise_all_injective {α : Type} [DecidableEq α] (keep flip : Nat)
    (biased : keep ≠ flip) (coordinates : List α) : Function.Injective (noiseAll keep flip coordinates) := by
  induction coordinates with
  | nil => exact fun _ _ h => h
  | cons i is ih =>
    exact fun _ _ h => ih (noise_at_injective keep flip i biased h)

/-- With both flip and keep having positive weight, a positive input cell
gives positive mass to every output that differs only at the listed bits. -/
theorem noise_all_pos {α : Type} [DecidableEq α] (keep flip : Nat)
    (keep_pos : 0 < keep) (flip_pos : 0 < flip) (coordinates : List α)
    (law : WeightTable α) (raw out : α → Bool) (raw_pos : 0 < law raw)
    (same_outside : ∀ i ∉ coordinates, raw i = out i) :
    0 < noiseAll keep flip coordinates law out := by
  induction coordinates generalizing out with
  | nil =>
    have same : raw = out := funext (fun i => same_outside i (by simp))
    simpa only [noiseAll, ← same] using raw_pos
  | cons i is ih =>
    simp only [noiseAll, noiseAt]
    by_cases same : raw i = out i
    · have rest : ∀ j ∉ is, raw j = out j := by
        intro j notMem
        by_cases atI : j = i
        · simpa only [atI] using same
        · exact same_outside j (by simp [atI, notMem])
      exact Nat.lt_of_lt_of_le (Nat.mul_pos keep_pos (ih out rest)) (Nat.le_add_right _ _)
    · have flipped : raw i = !(out i) := by
        revert same
        generalize raw i = a
        generalize out i = b
        cases a <;> cases b <;> decide
      have rest : ∀ j ∉ is, raw j = flipAt i out j := by
        intro j notMem
        by_cases atI : j = i
        · simpa [flipAt, atI] using flipped
        · simpa [flipAt, atI] using same_outside j (by simp [atI, notMem])
      exact Nat.lt_of_lt_of_le (Nat.mul_pos flip_pos (ih (flipAt i out) rest)) (Nat.le_add_left _ _)

end

end OpenCausalScience.Papers.LeeEtAl2019.GeneralIdentifiabilityErratum
