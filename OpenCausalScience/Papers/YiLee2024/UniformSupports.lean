module
public import OpenCausalScience.Papers.YiLee2024.FixedEdgeSparsity

/-! # Uniform fixed-size supports in Filter, Rank, and Prune

[Yi and Lee's correction](https://www.sanghacklee.me/ai-corrected/FRP_AI_corrected_2026-09-19.pdf),
Appendix G. For a fixed ordered pair, put the two edges between its vertices
first, followed by the disjoint pairs of edges into each other vertex,
then the unrestricted slots. The zero-pattern event uses the stated generic
noncancellation premise. The support sampling here is before eigenvalue
rejection.
-/

namespace OpenCausalScience.Papers.YiLee2024.UniformSupports

@[expose] public section

open FixedEdgeSparsity

/-- Each slot records whether the corresponding directed edge is selected. -/
def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).map (false :: ·) ++ (allMasks n).map (true :: ·)

def maskSize (mask : List Bool) : Nat := mask.count true

def fixedMasks (slots edges : Nat) : List (List Bool) :=
  (allMasks slots).filter fun m => maskSize m == edges

theorem mem_all_masks (slots : Nat) (mask : List Bool) :
    mask ∈ allMasks slots ↔ mask.length = slots := by
  induction slots generalizing mask with
  | zero => cases mask <;> simp [allMasks]
  | succ slots ih =>
    cases mask with
    | nil => simp [allMasks]
    | cons bit tail => cases bit <;> simp [allMasks, ih]

private theorem nodup_prefix (head : List Bool) {xs : List (List Bool)} (d : xs.Nodup) :
    (xs.map (head ++ ·)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  apply List.Pairwise.imp _ d
  intro a b ne same
  exact ne (List.append_cancel_left same)

/-- Different prefixes describe disjoint support choices. -/
private theorem nodup_append_prefix {a b : List Bool} {xs ys : List (List Bool)}
    (hxs : xs.Nodup) (hys : ys.Nodup) (different : a ≠ b) (sameLength : a.length = b.length) :
    ((xs.map (a ++ ·)) ++ (ys.map (b ++ ·))).Nodup := by
  rw [List.Nodup, List.pairwise_append]
  refine ⟨nodup_prefix a hxs, nodup_prefix b hys, ?_⟩
  intro x hx y hy equal
  obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
  apply different
  have heads :=  congrArg (List.take a.length) equal
  simpa [sameLength] using heads

theorem all_masks_nodup (slots : Nat) : (allMasks slots).Nodup := by
  induction slots with
  | zero => simp [allMasks]
  | succ slots ih =>
    simpa only [allMasks, List.singleton_append] using
      nodup_append_prefix (a := [false]) (b := [true]) ih ih (by decide) rfl

theorem mem_fixed_masks (slots edges : Nat) (mask : List Bool) :
    mask ∈ fixedMasks slots edges ↔ mask.length = slots ∧ maskSize mask = edges := by
  simp [fixedMasks, mem_all_masks]

@[simp] private theorem mask_size_false_cons (mask : List Bool) :
    maskSize (false :: mask) = maskSize mask := by simp [maskSize]

@[simp] private theorem mask_size_true_cons (mask : List Bool) :
    maskSize (true :: mask) = maskSize mask + 1 := by simp [maskSize]

@[simp] private theorem plus_one_beq_zero (a : Nat) : (a + 1 == 0) = false := by
  simp

@[simp] private theorem plus_one_beq_plus_one (a b : Nat) :
    (a + 1 == b + 1) = (a == b) := by
  by_cases h : a = b <;> simp [h]

private theorem zero_mask_count (slots : Nat) :
    (allMasks slots).countP (fun m => maskSize m == 0) = 1 := by
  induction slots with
  | zero => rfl
  | succ slots ih => simp [allMasks, Function.comp_def, ih]

theorem fixed_masks_count (slots edges : Nat) :
    (fixedMasks slots edges).length = choose slots edges := by
  unfold fixedMasks
  rw [← List.countP_eq_length_filter]
  induction slots generalizing edges with
  | zero => cases edges <;> simp [allMasks, maskSize, choose]
  | succ slots ih =>
    cases edges with
    | zero => simp only [choose, zero_mask_count]
    | succ edges =>
      simp [allMasks, Function.comp_def, ih, choose]

/-- The paired slots carry at most one edge per pair. -/
def allowedPairs : Nat → List Bool → Prop
  | 0, _ => True
  | n + 1, a :: b :: tail => (a = false ∨ b = false) ∧ allowedPairs n tail
  | _ + 1, _ => False

/-- Enumerate the uniquely labeled supports of the paired and free slots.
Each pair is either empty, left only, or right only. -/
def pairedMasks (free : Nat) : Nat → List (List Bool)
  | 0 => allMasks free
  | n + 1 =>
    let tail := pairedMasks free n
    tail.map (false :: false :: ·) ++ tail.map (true :: false :: ·) ++
      tail.map (false :: true :: ·)

theorem mem_paired_masks (pairs free : Nat) (mask : List Bool) :
    mask ∈ pairedMasks free pairs ↔ mask.length = pairs * 2 + free ∧ allowedPairs pairs mask := by
  induction pairs generalizing mask with
  | zero => simp [pairedMasks, allowedPairs, mem_all_masks]
  | succ pairs ih =>
    rcases mask with _ | ⟨a, _ | ⟨b, tail⟩⟩
    · simp [pairedMasks, allowedPairs]
    · simp [pairedMasks, allowedPairs]
    · cases a <;> cases b <;>
        simp [pairedMasks, allowedPairs, ih, Nat.succ_mul] <;> omega

theorem paired_masks_nodup (pairs free : Nat) : (pairedMasks free pairs).Nodup := by
  induction pairs with
  | zero => exact all_masks_nodup free
  | succ pairs ih =>
    simp only [pairedMasks]
    rw [List.Nodup, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact nodup_append_prefix (a := [false, false]) (b := [true, false]) ih ih (by decide) rfl
    · exact nodup_prefix [false, true] ih
    · intro x hx y hy equal
      obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨x', _, rfl⟩ := List.mem_map.mp h
        simp at equal
      · obtain ⟨x', _, rfl⟩ := List.mem_map.mp h
        simp at equal

private theorem count_zero_paired_masks (pairs free : Nat) :
    (pairedMasks free pairs).countP (fun m => maskSize m == 0) = 1 := by
  induction pairs with
  | zero => exact zero_mask_count free
  | succ pairs ih =>
    simp [pairedMasks, Function.comp_def, ih]

theorem paired_masks_count (pairs free edges : Nat) :
    (pairedMasks free pairs).countP (fun m => maskSize m == edges) =
      supportCount pairs free edges := by
  induction pairs generalizing edges with
  | zero =>
    rw [supportCount, ← fixed_masks_count free edges]
    simp [pairedMasks, fixedMasks, List.countP_eq_length_filter]
  | succ pairs ih =>
    cases edges with
    | zero => simp only [supportCount, count_zero_paired_masks]
    | succ edges =>
      simp [pairedMasks, Function.comp_def, ih, supportCount, Nat.two_mul]

/-- Full masks for the fixed pair put its two excluded edges first. -/
def zeroMasks (pairs free edges : Nat) : List (List Bool) :=
  ((pairedMasks free pairs).filter fun m => maskSize m == edges).map (false :: false :: ·)

theorem zero_masks_nodup (pairs free edges : Nat) : (zeroMasks pairs free edges).Nodup :=
  nodup_prefix [false, false] (List.Sublist.nodup List.filter_sublist (paired_masks_nodup pairs free))

theorem mem_zero_masks (pairs free edges : Nat) (mask : List Bool) :
    mask ∈ zeroMasks pairs free edges ↔
      ∃ tail, mask = false :: false :: tail ∧ tail.length = pairs * 2 + free ∧
        allowedPairs pairs tail ∧ maskSize tail = edges := by
  constructor
  · intro mem
    obtain ⟨tail, filtered, rfl⟩ := List.mem_map.mp mem
    obtain ⟨paired, size⟩ := List.mem_filter.mp filtered
    obtain ⟨length, allowed⟩ := (mem_paired_masks pairs free tail).mp paired
    exact ⟨tail, rfl, length, allowed, beq_iff_eq.mp size⟩
  · rintro ⟨tail, rfl, length, allowed, size⟩
    exact List.mem_map.mpr ⟨tail, List.mem_filter.mpr
      ⟨(mem_paired_masks pairs free tail).mpr ⟨length, allowed⟩, beq_iff_eq.mpr size⟩, rfl⟩

/-- Exact count of supports in the fixed-pair zero-pattern event, using
the closed-form coefficients from the companion module. -/
theorem zero_masks_count (pairs free edges : Nat) :
    (zeroMasks pairs free edges).length =
      convolve (fun r => choose pairs r * 2 ^ r) (choose free) edges := by
  unfold zeroMasks
  rw [List.length_map, ← List.countP_eq_length_filter, paired_masks_count, support_count_eq]

private theorem zero_masks_subset (pairs free edges : Nat) :
    zeroMasks pairs free edges ⊆ fixedMasks (2 + pairs * 2 + free) edges := by
  intro mask mem
  obtain ⟨tail, rfl, size, _, count⟩ := (mem_zero_masks pairs free edges mask).mp mem
  apply (mem_fixed_masks _ _ _).mpr
  simp [count, size, Nat.add_comm, Nat.add_left_comm] <;> omega

private theorem favorable_count (pairs free edges : Nat) :
    (fixedMasks (2 + pairs * 2 + free) edges).countP (zeroMasks pairs free edges).contains =
      supportCount pairs free edges := by
  let all := fixedMasks (2 + pairs * 2 + free) edges
  let zeros := zeroMasks pairs free edges
  have unique : all.Nodup := List.Sublist.nodup List.filter_sublist (all_masks_nodup _)
  have perm : (all.filter zeros.contains).Perm zeros := by
    apply (List.perm_ext_iff_of_nodup
      (List.Sublist.nodup List.filter_sublist unique) (zero_masks_nodup _ _ _)).mpr
    intro mask
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨And.right, fun h => ⟨zero_masks_subset _ _ _ h, h⟩⟩
  rw [List.countP_eq_length_filter, perm.length_eq]
  unfold zeros zeroMasks
  rw [List.length_map, ← List.countP_eq_length_filter, paired_masks_count]

/-- The averaging denominator is positive for every feasible edge count. -/
theorem fixed_masks_nonempty (slots edges : Nat) (feasible : edges ≤ slots) :
    ∃ mask, mask ∈ fixedMasks slots edges := by
  refine ⟨List.replicate edges true ++ List.replicate (slots - edges) false, ?_⟩
  apply (mem_fixed_masks _ _ _).mpr
  simp [maskSize, List.count_append, List.count_replicate] <;> omega

/-- Under the uniform size-constrained sampler, this is the exact event
probability for one ordered pair in its slot labeling. A uniform average
uses a feasible edge count. -/
theorem uniform_zero_probability (pairs free edges : Nat) :
    let all := fixedMasks (2 + pairs * 2 + free) edges
    ((all.countP (zeroMasks pairs free edges).contains : Nat) : Rat) / all.length =
      (supportCount pairs free edges : Nat) / (choose (2 + pairs * 2 + free) edges : Nat) := by
  simp only [favorable_count, fixed_masks_count]

private theorem sum_constant {α : Type} (xs : List α) (c : Nat) :
    (xs.map fun _ => c).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem sum_counts_transpose {α β : Type} (xs : List α) (ys : List β) (test : α → β → Bool) :
    (xs.map fun x => ys.countP (test x)).sum = (ys.map fun y => xs.countP (fun x => test x y)).sum := by
  have sumAdd (l : List β) (f h : β → Nat) :
      (l.map fun x => f x + h x).sum = (l.map f).sum + (l.map h).sum := by
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega
  have countAsSum (p : β → Bool) :
      ys.countP p = (ys.map fun y => if p y then 1 else 0).sum := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [List.countP_cons, ih, Nat.add_comm]
  induction xs with
  | nil => simp [sum_constant]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, sumAdd, ← countAsSum, ← ih]
    omega

private theorem slots_split (q : Nat) :
    (q + 2) * (q + 1) = 2 + q * 2 + (q + 1) * q := by
  simp [Nat.add_mul, Nat.mul_add]
  omega

/-- Summing the zero indicators over all ordered pairs gives the corrected
Appendix G expectation, for any relabelings of the uniform support
sampler to the per-pair slot order. The predicates count precision zeros
under the paper's noncancellation premise. -/
theorem uniform_zero_expectation {Pair : Type} (q edges : Nat) (orderedPairs : List Pair)
    (numberOfPairs : orderedPairs.length = (q + 2) * (q + 1))
    (relabel : Pair → List Bool → List Bool)
    (preserves : ∀ pair ∈ orderedPairs,
      let all := fixedMasks ((q + 2) * (q + 1)) edges
      (all.map (relabel pair)).Perm all) :
    let all := fixedMasks ((q + 2) * (q + 1)) edges
    let zeros := zeroMasks q ((q + 1) * q) edges
    (((all.map fun m => orderedPairs.countP (fun p => zeros.contains (relabel p m))).sum : Nat) : Rat) /
      all.length = expectedZeros q edges := by
  dsimp only
  rw [sum_counts_transpose]
  have sameCounts : (orderedPairs.map fun p =>
      (fixedMasks ((q + 2) * (q + 1)) edges).countP
        (fun m => (zeroMasks q ((q + 1) * q) edges).contains (relabel p m))) =
      orderedPairs.map (fun _ => supportCount q ((q + 1) * q) edges) := by
    apply List.map_congr_left
    intro pair mem
    have perm := (preserves pair mem).countP_eq (zeroMasks q ((q + 1) * q) edges).contains
    simpa only [List.countP_map, Function.comp_def, slots_split q, favorable_count] using perm
  rw [sameCounts]
  simp [expectedZeros, fixed_masks_count, sum_constant, numberOfPairs]

end
end OpenCausalScience.Papers.YiLee2024.UniformSupports
