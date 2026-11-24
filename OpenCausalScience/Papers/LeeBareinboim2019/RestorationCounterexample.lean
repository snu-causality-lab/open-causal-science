module
public import Std

/-!
# Lee and Bareinboim (2019), the limits of model restoration

Consider the original graph with `A ↔ W → B`, `A ↔ C`, and `B ↔ C`.
Eliminating the non-manipulable node `W` gives the bidirected triangle.
The projected graph admits a model with three outputs equal to the same
fair bit. The original graph has only pairwise shared sources. The sources
on `A ↔ W`, and any private noise of `W`, can be put into one block `AB`.
The other two blocks carry the sources for `A ↔ C` and `B ↔ C`. Private
noise of a retained vertex may be included in a block incident to it.

For independent finite sources the joint support is the product of their
supports. The theorems take the three block types to be those supports,
so agreement almost surely is agreement at every input in the product.
This is an instance of the obstruction of Evans (2016), Example 6.6, in
the setting of the published Proposition 3. The corrected proposition
requires restoration only of a chosen POMIS witness.

Sources:
* https://doi.org/10.1609/aaai.v33i01.33014164
* https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
* https://arxiv.org/abs/1408.1809
-/

namespace OpenCausalScience.Papers.LeeBareinboim2019.RestorationCounterexample

@[expose] public section

variable {AB AC BC : Type} {Output : Type}

/-- Each retained equation receives the two independent source blocks
incident to it. Any common output on their product support is constant. -/
theorem agreement_is_constant (a : AB → AC → Output) (b : AB → BC → Output)
    (c : AC → BC → Output) (ab₀ : AB) (ac₀ : AC) (bc₀ : BC)
    (agree : ∀ ab ac bc, a ab ac = b ab bc ∧ b ab bc = c ac bc)
    (ab : AB) (ac : AC) : a ab ac = a ab₀ ac₀ := by
  calc
    a ab ac = b ab bc₀ := (agree ab ac bc₀).1
    _ = c ac₀ bc₀ := (agree ab ac₀ bc₀).2
    _ = b ab₀ bc₀ := (agree ab₀ ac₀ bc₀).2.symm
    _ = a ab₀ ac₀ := (agree ab₀ ac₀ bc₀).1.symm

/-- There is no restoration of a law placing positive mass on both `000`
and `111` and zero mass on all other outcomes. -/
theorem no_common_fair_bit (a : AB → AC → Bool) (b : AB → BC → Bool)
    (c : AC → BC → Bool) (bc₀ : BC) :
    ¬ ((∀ ab ac bc, a ab ac = b ab bc ∧ b ab bc = c ac bc) ∧
      (∃ ab ac, a ab ac = false) ∧ (∃ ab ac, a ab ac = true)) := by
  rintro ⟨agree, ⟨ab₀, ac₀, zero⟩, ⟨ab, ac, one⟩⟩
  have same := agreement_is_constant a b c ab₀ ac₀ bc₀ agree ab ac
  rw [zero, one] at same
  contradiction

def sharedBitModel (u : Bool) : Bool × Bool × Bool := (u, u, u)

theorem projected_common_fair_bit :
    [false, true].map sharedBitModel = [(false, false, false), (true, true, true)] := rfl

end
end OpenCausalScience.Papers.LeeBareinboim2019.RestorationCounterexample
