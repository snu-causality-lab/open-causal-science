module
public import Std

/-! # Parity of independent private flips

[Lee and Bareinboim, corrected R-58](https://www.sanghacklee.me/ai-corrected/R58_AI_corrected_2026-10-25.pdf),
Appendices B–C, Examples 1–2, Lemma 7 equation (5), and Figure 13.
The two integer weights represent an independent Bernoulli law when
normalized by their positive sum. The parity identities do not presume
that the lifted hedge realizes the stated independent noise sets.
-/

namespace OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.HedgeNoise

@[expose] public section

@[ext] structure BitWeights where
  zero : Int
  one : Int

def total (weights : BitWeights) : Int := weights.zero + weights.one

def imbalance (weights : BitWeights) : Int := weights.zero - weights.one

def xorWeights (a b : BitWeights) : BitWeights :=
  ⟨a.zero * b.zero + a.one * b.one, a.zero * b.one + a.one * b.zero⟩

theorem total_xor_weights (a b : BitWeights) : total (xorWeights a b) = total a * total b := by
  simp only [total, xorWeights, Int.add_mul, Int.mul_add]
  omega

theorem imbalance_xor_weights (a b : BitWeights) :
    imbalance (xorWeights a b) = imbalance a * imbalance b := by
  simp only [imbalance, xorWeights, Int.sub_mul, Int.mul_sub]
  omega

private theorem eq_of_total_and_imbalance {a b : BitWeights}
    (ht : total a = total b) (hi : imbalance a = imbalance b) : a = b := by
  simp only [total] at ht
  simp only [imbalance] at hi
  ext <;> omega

private theorem xorWeights_assoc (a b c : BitWeights) :
    xorWeights (xorWeights a b) c = xorWeights a (xorWeights b c) := by
  apply eq_of_total_and_imbalance
  · simp only [total_xor_weights, Int.mul_assoc]
  · simp only [imbalance_xor_weights, Int.mul_assoc]

def parityWeights : List BitWeights → BitWeights
  | [] => ⟨1, 0⟩
  | head :: tail => xorWeights head (parityWeights tail)

/-- A single private flip with the normalized weights of the dropped
parity gives exactly the same normalized XOR law on the kept channel. -/
theorem compensating_flip_preserves_parity (kept dropped : List BitWeights) :
    parityWeights (kept ++ dropped) = xorWeights (parityWeights kept) (parityWeights dropped) := by
  induction kept with
  | nil => simp [parityWeights, xorWeights]
  | cons head tail ih => simp [parityWeights, ih, xorWeights_assoc]

/-- Numerators and denominators in `1 - 2δ = ∏ (1 - 2εᵢ)`, with the
normalized signed imbalance of a Bernoulli bit interpreted as `1 - 2ε`. -/
theorem compensation_products (noises : List BitWeights) :
    imbalance (parityWeights noises) = (noises.map imbalance).prod ∧
    total (parityWeights noises) = (noises.map total).prod := by
  induction noises with
  | nil => decide
  | cons head tail ih => simp [parityWeights, imbalance_xor_weights, total_xor_weights, ih.1, ih.2]

/-- Strict support and bias toward zero are preserved when composing two
private flips with `0 < ε, δ < 1/2`. -/
theorem positive_biased_xor (a b : BitWeights)
    (ha : 0 < a.one) (hb : 0 < b.one)
    (ba : a.one < a.zero) (bb : b.one < b.zero) :
    0 < (xorWeights a b).one ∧ (xorWeights a b).one < (xorWeights a b).zero := by
  constructor
  · exact Int.add_pos (Int.mul_pos (by omega) hb) (Int.mul_pos ha (by omega))
  · have h : 0 < imbalance (xorWeights a b) := by
      rw [imbalance_xor_weights]
      exact Int.mul_pos (by simpa [imbalance] using ba) (by simpa [imbalance] using bb)
    simpa [imbalance] using h

/-- A fair input forces an unbiased parity, while an input biased toward
zero stays biased toward zero after an independent flip biased toward zero.
This checks the two parity cases used after the intervention in Lemma 7. -/
theorem root_parity_after_transfer (fair biased transfer : BitWeights)
    (hf : imbalance fair = 0) (hb : 0 < imbalance biased) (ht : 0 < imbalance transfer) :
    imbalance (xorWeights fair transfer) = 0 ∧ 0 < imbalance (xorWeights biased transfer) := by
  rw [imbalance_xor_weights, imbalance_xor_weights, hf, Int.zero_mul]
  exact ⟨rfl, Int.mul_pos hb ht⟩

/-- Figure 13 at `ε = 1/10`: the six dropped flips have `δ = 368928/1000000`
and the additional seventh flip yields `P(Y = 0) = 6048576/10000000`. -/
theorem figure13_six_compensating_flips :
    (parityWeights (List.replicate 6 ⟨9, 1⟩)).one = 368928 ∧
    total (parityWeights (List.replicate 6 ⟨9, 1⟩)) = 1000000 ∧
    (parityWeights (List.replicate 7 ⟨9, 1⟩)).zero = 6048576 ∧
    total (parityWeights (List.replicate 7 ⟨9, 1⟩)) = 10000000 := by
  decide

end

end OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.HedgeNoise
