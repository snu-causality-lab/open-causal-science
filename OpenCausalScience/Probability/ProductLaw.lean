module
public import OpenCausalScience.Probability.ConditionalIndependence
public import OpenCausalScience.Probability.FiniteSummation

/-! # Factorized finite laws

A split density on the Cartesian product of two finite state spaces
gives independence of all observables read from the respective sides.
The statement includes unnormalized and zero-mass slices.
-/

namespace OpenCausalScience.Probability.FiniteLaw

open FiniteSummation

@[expose] public section

variable {A B C D : Type}

def productLaw (left : FiniteLaw A) (right : FiniteLaw B) : FiniteLaw (A × B) where
  atoms := left.atoms.flatMap fun a => right.atoms.map fun b => (a, b)
  weight := fun (a, b) => left.weight a * right.weight b
  nonnegative := by
    rintro ⟨a, b⟩ here
    obtain ⟨x, hx, rest⟩ := List.mem_flatMap.mp here
    obtain ⟨y, hy, eq⟩ := List.mem_map.mp rest
    cases eq
    exact Rat.mul_nonneg (left.nonnegative _ hx) (right.nonnegative _ hy)

theorem product_mass (left : FiniteLaw A) (right : FiniteLaw B) (p : A → Bool) (q : B → Bool) :
    (productLaw left right).mass (fun ab => p ab.1 && q ab.2) =
      left.mass p * right.mass q := by
  change sumOver (left.atoms.flatMap fun a => right.atoms.map fun b => (a, b))
    (fun ab => if p ab.1 && q ab.2 then left.weight ab.1 * right.weight ab.2 else 0) =
      sumOver left.atoms (fun a => if p a then left.weight a else 0) *
        sumOver right.atoms (fun b => if q b then right.weight b else 0)
  rw [sum_flatMap, ← sum_product]
  apply sum_congr
  intro a _
  rw [sum_map]
  apply sum_congr
  intro b _
  cases p a <;> cases q b <;> simp [Rat.zero_mul, Rat.mul_zero]

theorem product_independent (left : FiniteLaw A) (right : FiniteLaw B)
    (f : A → C) (g : B → D) :
    (productLaw left right).IndependentAt (f ∘ Prod.fst) (g ∘ Prod.snd) (fun _ => true) := by
  intro testF testG
  let p a := testF (f a)
  let q b := testG (g b)
  have first := product_mass left right p (fun _ => true)
  have second := product_mass left right (fun _ => true) q
  simp only [Bool.and_true, Bool.true_and] at first second
  change (productLaw left right).mass (fun ab => p ab.1 && q ab.2) *
      (productLaw left right).mass (fun _ => true) =
    (productLaw left right).mass (fun ab => p ab.1) *
      (productLaw left right).mass (fun ab => q ab.2)
  rw [product_mass, first, second]
  have entire := product_mass left right (fun _ => true) (fun _ => true)
  simp only [Bool.true_and] at entire
  rw [entire]
  grind

end
end OpenCausalScience.Probability.FiniteLaw
