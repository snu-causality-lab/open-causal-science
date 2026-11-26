module
public import Std

/-! # Finite event mass

A list of atoms and rational weights determines the mass of a Boolean event.
The partition identity works for signed weights as well as probability laws.
-/

namespace OpenCausalScience.Probability.FiniteMass

@[expose] public section

variable {Ω : Type}

/-- Sum the weights of the atoms in the event. The list determines multiplicity. -/
def mass (atoms : List Ω) (weight : Ω → Rat) (event : Ω → Bool) : Rat :=
  (atoms.map fun unit => if event unit then weight unit else 0).sum

theorem mass_univ (atoms : List Ω) (weight : Ω → Rat) :
    mass atoms weight (fun _ => true) = (atoms.map weight).sum := by
  simp [mass]

/-- Events that agree on every listed atom of nonzero weight have equal mass. -/
theorem mass_congr_on_support (atoms : List Ω) (weight : Ω → Rat) {event other : Ω → Bool}
    (agree : ∀ atom ∈ atoms, weight atom ≠ 0 → event atom = other atom) :
    mass atoms weight event = mass atoms weight other := by
  unfold mass
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom member
  by_cases zero : weight atom = 0
  · simp [zero]
  · rw [agree atom member zero]

private theorem sum_add {A : Type} (states : List A) (p q : A → Rat) :
    (states.map fun a => p a + q a).sum = (states.map p).sum + (states.map q).sum := by
  induction states with
  | nil => simp [Rat.zero_add]
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, Rat.add_assoc]
    rw [← Rat.add_assoc (q a), Rat.add_comm (q a), Rat.add_assoc]

private theorem sum_indicator {A : Type} [DecidableEq A] (states : List A)
    (picked : A) (c : Rat) (unique : states.Nodup) :
    (states.map fun a => if picked = a then c else 0).sum = if picked ∈ states then c else 0 := by
  induction states with
  | nil => simp
  | cons a rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases same : picked = a
    · subst picked
      simp [ih tailUnique, absent, Rat.add_zero]
    · simp [same, List.mem_cons, ih tailUnique, Rat.zero_add]

/-- The masses of the cells of a finite partition sum to the event mass. -/
theorem sum_masses_of_partition {A : Type} [DecidableEq A] (states : List A)
    (unique : states.Nodup) (atoms : List Ω) (weight : Ω → Rat)
    (cell : Ω → A) (exhaustive : ∀ unit ∈ atoms, cell unit ∈ states) (event : Ω → Bool) :
    (states.map fun a => mass atoms weight (fun unit => event unit && decide (cell unit = a))).sum =
      mass atoms weight event := by
  induction atoms with
  | nil =>
    have zero (xs : List A) : (xs.map fun _ => (0 : Rat)).sum = 0 := by
      induction xs with
      | nil => rfl
      | cons a rest ih => simp [ih, Rat.zero_add]
    exact zero states
  | cons unit tail ih =>
    have inside := exhaustive unit List.mem_cons_self
    have tailInside : ∀ sample ∈ tail, cell sample ∈ states :=
      fun sample member => exhaustive sample (List.mem_cons_of_mem _ member)
    simp only [mass, List.map_cons, List.sum_cons] at ih ⊢
    rw [sum_add, ih tailInside]
    by_cases holds : event unit = true
    · simp [holds, sum_indicator states (cell unit) (weight unit) unique, inside]
    · have fails : event unit = false := Bool.eq_false_iff.mpr holds
      have zero := sum_indicator states (cell unit) 0 unique
      have every : (states.map fun _ => (0 : Rat)) =
          states.map (fun a => if cell unit = a then (0 : Rat) else 0) := by
        simp
      simp [fails, every, zero, inside]

end

end OpenCausalScience.Probability.FiniteMass
