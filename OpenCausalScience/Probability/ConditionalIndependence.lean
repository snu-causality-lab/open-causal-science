module
public import OpenCausalScience.Probability.FiniteMass

/-! # Conditional independence for finite rational laws

The cross-product definition includes zero-mass conditioning cells. On
supported cells it equals the usual condition stated using ratios.
Dawid (1979), Lemmas 4.1–4.3, motivates the rules below.
-/

namespace OpenCausalScience.Probability

@[expose] public section

structure FiniteLaw (Ω : Type) where
  atoms : List Ω
  weight : Ω → Rat
  nonnegative : ∀ a ∈ atoms, 0 ≤ weight a

namespace FiniteLaw

variable {Ω A B C D : Type}

def mass (law : FiniteLaw Ω) (event : Ω → Bool) : Rat :=
  FiniteMass.mass law.atoms law.weight event

def andEvent (a b : Ω → Bool) : Ω → Bool := fun u => a u && b u

local infixr:60 " ∩ₑ " => andEvent

theorem and_event_comm (a b : Ω → Bool) : a ∩ₑ b = b ∩ₑ a := by
  funext u
  exact Bool.and_comm (a u) (b u)

theorem and_event_assoc (a b c : Ω → Bool) : (a ∩ₑ b) ∩ₑ c = a ∩ₑ b ∩ₑ c := by
  funext u
  exact Bool.and_assoc (a u) (b u) (c u)

theorem and_event_left_comm (a b c : Ω → Bool) : a ∩ₑ b ∩ₑ c = b ∩ₑ a ∩ₑ c := by
  rw [← and_event_assoc, and_event_comm a b, and_event_assoc]

def valueEvent [DecidableEq A] (observable : Ω → A) (value : A) : Ω → Bool :=
  fun a => decide (observable a = value)

def IndependentAt (law : FiniteLaw Ω) (left : Ω → A) (right : Ω → B)
    (event : Ω → Bool) : Prop :=
  ∀ (f : A → Bool) (g : B → Bool),
    law.mass (event ∩ₑ (f ∘ left) ∩ₑ (g ∘ right)) * law.mass event =
      law.mass (event ∩ₑ (f ∘ left)) * law.mass (event ∩ₑ (g ∘ right))

def IndependentGiven [DecidableEq C] (law : FiniteLaw Ω)
    (left : Ω → A) (right : Ω → B) (condition : Ω → C) : Prop :=
  ∀ c, law.IndependentAt left right (valueEvent condition c)

theorem mass_nonnegative (law : FiniteLaw Ω) (event : Ω → Bool) : 0 ≤ law.mass event := by
  have nonnegative := law.nonnegative
  unfold mass FiniteMass.mass
  generalize ha : law.atoms = atoms at nonnegative ⊢
  clear ha
  induction atoms with
  | nil => exact Rat.le_refl
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    apply Rat.add_nonneg
    · split
      · exact nonnegative a List.mem_cons_self
      · exact Rat.le_refl
    · exact ih (fun a ha => nonnegative a (List.mem_cons_of_mem _ ha))

theorem mass_mono (law : FiniteLaw Ω) {sub event : Ω → Bool}
    (h : ∀ a ∈ law.atoms, sub a = true → event a = true) : law.mass sub ≤ law.mass event := by
  unfold mass FiniteMass.mass
  generalize ha : law.atoms = atoms at h ⊢
  have weights (a) (ha' : a ∈ atoms) : 0 ≤ law.weight a :=
    law.nonnegative a (ha ▸ ha')
  clear ha
  induction atoms with
  | nil => exact Rat.le_refl
  | cons a rest ih =>
    have restH := ih
      (fun a ha' => h a (List.mem_cons_of_mem _ ha'))
      (fun a ha' => weights a (List.mem_cons_of_mem _ ha'))
    have hWeight := weights a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    cases hs : sub a
    · cases he : event a
      · simpa only [Bool.false_eq_true, ↓reduceIte, Rat.zero_add] using restH
      · simp only [Bool.false_eq_true, ↓reduceIte, Rat.zero_add]
        grind
    · have he := h a List.mem_cons_self hs
      simp only [he, ↓reduceIte]
      grind

theorem submass_eq_zero (law : FiniteLaw Ω) {sub event : Ω → Bool}
    (h : ∀ a ∈ law.atoms, sub a = true → event a = true) (zero : law.mass event = 0) :
    law.mass sub = 0 := by
  apply Rat.le_antisymm _ (law.mass_nonnegative sub)
  rw [← zero]
  exact law.mass_mono h

theorem mass_sum_value (law : FiniteLaw Ω) [DecidableEq B] (y : Ω → B)
    (states : List B) (unique : states.Nodup) (exhaustive : ∀ a ∈ law.atoms, y a ∈ states)
    (event : Ω → Bool) :
    (states.map fun b => law.mass (event ∩ₑ valueEvent y b)).sum = law.mass event :=
  FiniteMass.sum_masses_of_partition states unique law.atoms law.weight y exhaustive event

theorem IndependentAt.symm {law : FiniteLaw Ω} {x : Ω → A} {y : Ω → B}
    {event : Ω → Bool} (h : law.IndependentAt x y event) : law.IndependentAt y x event := by
  intro g f
  rw [and_event_comm (g ∘ y) (f ∘ x), Rat.mul_comm (law.mass (event ∩ₑ (g ∘ y)))]
  exact h f g

theorem IndependentGiven.symm [DecidableEq C] {law : FiniteLaw Ω} {x : Ω → A}
    {y : Ω → B} {z : Ω → C} (h : law.IndependentGiven x y z) :
    law.IndependentGiven y x z := fun c => (h c).symm

theorem IndependentAt.map_right {law : FiniteLaw Ω} {x : Ω → A} {y : Ω → B}
    {event : Ω → Bool} (h : law.IndependentAt x y event) (g : B → D) :
    law.IndependentAt x (g ∘ y) event :=
  fun f' g' => h f' (g' ∘ g)

theorem IndependentGiven.map_right [DecidableEq C] {law : FiniteLaw Ω} {x : Ω → A}
    {y : Ω → B} {z : Ω → C} (h : law.IndependentGiven x y z) (g : B → D) :
    law.IndependentGiven x (g ∘ y) z := fun c => (h c).map_right g

theorem IndependentGiven.map_left [DecidableEq C] {law : FiniteLaw Ω} {x : Ω → A}
    {y : Ω → B} {z : Ω → C} (h : law.IndependentGiven x y z) (f : A → D) :
    law.IndependentGiven (f ∘ x) y z := (h.symm.map_right f).symm

theorem independent_given_pair_condition_left_iff [DecidableEq C] {law : FiniteLaw Ω}
    {x : Ω → A} {y : Ω → B} {z : Ω → C} :
    law.IndependentGiven (fun u => (x u, z u)) y z ↔ law.IndependentGiven x y z := by
  constructor
  · intro h
    exact h.map_left Prod.fst
  · intro h c f g
    have agreement :
        valueEvent z c ∩ₑ (f ∘ fun u => (x u, z u)) =
          valueEvent z c ∩ₑ ((fun a => f (a, c)) ∘ x) := by
      funext u
      by_cases eq : z u = c <;> simp [andEvent, valueEvent, eq]
    rw [← and_event_assoc, agreement, and_event_assoc]
    exact h c (fun a => f (a, c)) g

theorem mass_and_eq_zero (law : FiniteLaw Ω) {a : Ω → Bool}
    (b : Ω → Bool) (zero : law.mass a = 0) : law.mass (a ∩ₑ b) = 0 :=
  law.submass_eq_zero (fun _ _ h => (Bool.and_eq_true_iff.1 h).1) zero

theorem independent_at_zero (law : FiniteLaw Ω) {e : Ω → Bool} (zero : law.mass e = 0)
    (x : Ω → A) (y : Ω → B) : law.IndependentAt x y e := by
  intro f g
  rw [law.mass_and_eq_zero (f ∘ x) zero, zero, Rat.mul_zero, Rat.zero_mul]

theorem IndependentAt.condition_right {law : FiniteLaw Ω} {x : Ω → A} {y : Ω → B}
    {event : Ω → Bool} (h : law.IndependentAt x y event) (test : B → Bool) :
    law.IndependentAt x y (event ∩ₑ (test ∘ y)) := by
  by_cases baseZero : law.mass event = 0
  · exact law.independent_at_zero (law.mass_and_eq_zero _ baseZero) x y
  intro f g
  have hTest := h f test
  have hBoth := h f (fun y' => test y' && g y')
  change law.mass (event ∩ₑ (f ∘ x) ∩ₑ (test ∘ y) ∩ₑ (g ∘ y)) * law.mass event =
      law.mass (event ∩ₑ (f ∘ x)) * law.mass (event ∩ₑ (test ∘ y) ∩ₑ (g ∘ y)) at hBoth
  rw [and_event_comm (f ∘ x) (test ∘ y), ← and_event_assoc event] at hTest
  rw [and_event_left_comm (f ∘ x) (test ∘ y)] at hBoth
  simp only [← and_event_assoc event (test ∘ y)] at hBoth
  have hScaled :
      (law.mass ((event ∩ₑ (test ∘ y)) ∩ₑ (f ∘ x) ∩ₑ (g ∘ y)) *
          law.mass (event ∩ₑ (test ∘ y))) * law.mass event =
        (law.mass ((event ∩ₑ (test ∘ y)) ∩ₑ (f ∘ x)) *
          law.mass ((event ∩ₑ (test ∘ y)) ∩ₑ (g ∘ y))) * law.mass event := by
    grind
  exact (by simpa only [Rat.mul_div_cancel baseZero] using congrArg (· / law.mass event) hScaled)

theorem value_event_pair [DecidableEq A] [DecidableEq B] (x : Ω → A) (y : Ω → B)
    (a : A) (b : B) :
    valueEvent (fun u => (x u, y u)) (a, b) = valueEvent x a ∩ₑ valueEvent y b := by
  funext u
  by_cases hx : x u = a <;> by_cases hy : y u = b <;> simp [valueEvent, andEvent, hx, hy]

theorem IndependentGiven.weak_union [DecidableEq C] [DecidableEq D] {law : FiniteLaw Ω}
    {x : Ω → A} {y : Ω → B} {z : Ω → C}
    (h : law.IndependentGiven x y z) (g : B → D) :
    law.IndependentGiven x y (fun u => (z u, g (y u))) := by
  rintro ⟨c, d⟩
  rw [value_event_pair]
  exact (h c).condition_right (fun b => decide (g b = d))


def distinctValues [DecidableEq A] : List A → List A
  | [] => []
  | a :: rest =>
    let values := distinctValues rest
    if a ∈ values then values else a :: values

theorem mem_distinctValues [DecidableEq A] (a : A) (as : List A) :
    a ∈ distinctValues as ↔ a ∈ as := by
  induction as with
  | nil => rfl
  | cons b rest ih =>
    by_cases present : b ∈ distinctValues rest
    · have old := ih.mp
      simp only [distinctValues, present, ite_eq_left, List.mem_cons]
      constructor
      · exact fun h => Or.inr (old h)
      · rintro (rfl | tail)
        · exact present
        · exact ih.mpr tail
    · simp [distinctValues, present, ih]

theorem nodup_distinctValues [DecidableEq A] (as : List A) :
    (distinctValues as).Nodup := by
  induction as with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    by_cases present : a ∈ distinctValues rest
    · simpa [distinctValues, present] using ih
    · simp [distinctValues, present, ih]

private theorem sum_multiply_right {T : Type} (xs : List T) (f : T → Rat) (r : Rat) :
    (xs.map f).sum * r = (xs.map fun x => f x * r).sum := by
  induction xs with
  | nil => exact Rat.zero_mul r
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, Rat.add_mul, ih]

private theorem sum_multiply_left {T : Type} (xs : List T) (f : T → Rat) (r : Rat) :
    r * (xs.map f).sum = (xs.map fun x => r * f x).sum := by
  induction xs with
  | nil => exact Rat.mul_zero r
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, Rat.mul_add, ih]

theorem event_value_sum [DecidableEq B] (law : FiniteLaw Ω) (y : Ω → B)
    (event : Ω → Bool) :
    ((distinctValues (law.atoms.map y)).map
      fun b => law.mass (event ∩ₑ valueEvent y b)).sum = law.mass event := by
  apply law.mass_sum_value y _ (nodup_distinctValues _)
  intro a ha
  exact (mem_distinctValues _ _).mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem and_event_rotate (a b c : Ω → Bool) : (a ∩ₑ b) ∩ₑ c = (a ∩ₑ c) ∩ₑ b := by
  rw [and_event_assoc a b, and_event_comm b c, ← and_event_assoc a c]

theorem IndependentAt.contraction [DecidableEq B] {law : FiniteLaw Ω}
    {x : Ω → A} {y : Ω → B} {w : Ω → D} {event : Ω → Bool}
    (h : law.IndependentAt x y event)
    (hLocal : ∀ b, law.IndependentAt x w (event ∩ₑ valueEvent y b)) :
    law.IndependentAt x (fun a => (y a, w a)) event := by
  intro f g
  let left := f ∘ x
  let right := g ∘ (fun a => (y a, w a))
  let total := event ∩ₑ left ∩ₑ right
  let marginal := event ∩ₑ right
  let states := distinctValues (law.atoms.map y)
  have current (b : B) :
      law.mass (total ∩ₑ valueEvent y b) * law.mass event =
        law.mass (event ∩ₑ left) * law.mass (marginal ∩ₑ valueEvent y b) := by
    let value := valueEvent y b
    let cell := event ∩ₑ value
    have joints : total ∩ₑ value = cell ∩ₑ left ∩ₑ ((fun c => g (b, c)) ∘ w) := by
      funext a
      by_cases hb : y a = b
      · simp [total, cell, value, right, valueEvent, andEvent, hb]
      · simp [total, cell, value, valueEvent, andEvent, hb]
    have targets : marginal ∩ₑ value = cell ∩ₑ ((fun c => g (b, c)) ∘ w) := by
      funext a
      by_cases hb : y a = b
      · simp [marginal, cell, value, right, valueEvent, andEvent, hb]
      · simp [marginal, cell, value, valueEvent, andEvent, hb]
    rw [joints, targets]
    by_cases zero : law.mass cell = 0
    · rw [law.mass_and_eq_zero (left ∩ₑ ((fun c => g (b, c)) ∘ w)) zero,
        law.mass_and_eq_zero (((fun c => g (b, c)) ∘ w)) zero,
        Rat.zero_mul, Rat.mul_zero]
    · have ht := h f (fun b' => decide (b' = b))
      change law.mass (event ∩ₑ left ∩ₑ value) * law.mass event =
        law.mass (event ∩ₑ left) * law.mass cell at ht
      rw [and_event_comm left value, ← and_event_assoc event] at ht
      change law.mass (cell ∩ₑ left) * law.mass event =
        law.mass (event ∩ₑ left) * law.mass cell at ht
      have hl := hLocal b f (fun c => g (b, c))
      change law.mass (cell ∩ₑ left ∩ₑ ((fun c => g (b, c)) ∘ w)) * law.mass cell =
        law.mass (cell ∩ₑ left) * law.mass (cell ∩ₑ ((fun c => g (b, c)) ∘ w)) at hl
      have hScaled :
          (law.mass (cell ∩ₑ left ∩ₑ ((fun c => g (b, c)) ∘ w)) * law.mass event) *
            law.mass cell =
          (law.mass (event ∩ₑ left) * law.mass (cell ∩ₑ ((fun c => g (b, c)) ∘ w))) *
            law.mass cell := by
        grind
      simpa only [Rat.mul_div_cancel zero] using congrArg (· / law.mass cell) hScaled
  change law.mass total * law.mass event = law.mass (event ∩ₑ left) * law.mass marginal
  calc
    _ = (states.map fun b => law.mass (total ∩ₑ valueEvent y b) * law.mass event).sum := by
      rw [← law.event_value_sum y total, sum_multiply_right]
    _ = (states.map fun b =>
        law.mass (event ∩ₑ left) * law.mass (marginal ∩ₑ valueEvent y b)).sum := by
      exact congrArg List.sum (List.map_congr_left (fun b _ => current b))
    _ = _ := by rw [← sum_multiply_left, law.event_value_sum y marginal]

theorem IndependentGiven.contraction [DecidableEq B] [DecidableEq C]
    {law : FiniteLaw Ω} {x : Ω → A} {y : Ω → B} {w : Ω → D} {z : Ω → C}
    (h : law.IndependentGiven x y z)
    (hLocal : law.IndependentGiven x w (fun u => (z u, y u))) :
    law.IndependentGiven x (fun u => (y u, w u)) z := by
  intro c
  apply (h c).contraction
  intro b
  have h' := hLocal (c, b)
  rw [value_event_pair] at h'
  exact h'


theorem scaled_masses_of_values [DecidableEq B] (law : FiniteLaw Ω) (y : Ω → B)
    (p q : Ω → Bool) (r t : Rat)
    (each : ∀ b, law.mass (p ∩ₑ valueEvent y b) * r = t * law.mass (q ∩ₑ valueEvent y b)) :
    law.mass p * r = t * law.mass q := by
  rw [← law.event_value_sum y p, ← law.event_value_sum y q,
    sum_multiply_right, sum_multiply_left]
  exact congrArg List.sum (List.map_congr_left (fun b _ => each b))

theorem scaled_masses_of_value_test [DecidableEq B] (law : FiniteLaw Ω) (y : Ω → B)
    (p q : Ω → Bool) (r t : Rat)
    (each : ∀ b, law.mass (p ∩ₑ valueEvent y b) * r = t * law.mass (q ∩ₑ valueEvent y b))
    (g : B → Bool) : law.mass (p ∩ₑ (g ∘ y)) * r = t * law.mass (q ∩ₑ (g ∘ y)) := by
  apply law.scaled_masses_of_values y
  intro b
  have replaceTest (base : Ω → Bool) :
      (base ∩ₑ (g ∘ y)) ∩ₑ valueEvent y b =
        fun u => (base ∩ₑ valueEvent y b) u && g b := by
    funext u
    by_cases h : y u = b <;> simp [andEvent, valueEvent, h]
  rw [replaceTest p, replaceTest q]
  cases hg : g b
  · have same :
        (fun (u : Ω) => ((p ∩ₑ valueEvent y b) u && false)) =
          fun u => ((q ∩ₑ valueEvent y b) u && false) := by
      funext u
      simp
    have zero : law.mass (fun (u : Ω) => ((q ∩ₑ valueEvent y b) u && false)) = 0 :=
      law.submass_eq_zero (event := fun _ => false)
        (by intro u _ hu; simp at hu) (by
          unfold mass FiniteMass.mass
          induction law.atoms <;> simp_all [Rat.zero_add])
    rw [same, zero, Rat.zero_mul, Rat.mul_zero]
  · simpa using each b

theorem independent_at_iff_point_right [DecidableEq B] (law : FiniteLaw Ω)
    (x : Ω → A) (y : Ω → B) (event : Ω → Bool) :
    law.IndependentAt x y event ↔
      ∀ (f : A → Bool) b,
        law.mass ((event ∩ₑ (f ∘ x)) ∩ₑ valueEvent y b) * law.mass event =
          law.mass (event ∩ₑ (f ∘ x)) * law.mass (event ∩ₑ valueEvent y b) := by
  constructor
  · intro h f b
    rw [and_event_assoc]
    exact h f (fun v => decide (v = b))
  · intro h f g
    rw [← and_event_assoc]
    exact law.scaled_masses_of_value_test y _ _ _ _ (h f) g

theorem IndependentAt.intersection [DecidableEq B] [DecidableEq D] {law : FiniteLaw Ω}
    {x : Ω → A} {y : Ω → B} {w : Ω → D} {event : Ω → Bool}
    (hXY : ∀ d, law.IndependentAt x y (event ∩ₑ valueEvent w d))
    (hXW : ∀ b, law.IndependentAt x w (event ∩ₑ valueEvent y b))
    (supported : ∀ b d, law.mass (event ∩ₑ valueEvent y b ∩ₑ valueEvent w d) ≠ 0) :
    law.IndependentAt x (fun u => (y u, w u)) event := by
  by_cases empty : law.atoms = []
  · apply law.independent_at_zero
    simp [mass, FiniteMass.mass, empty]
  let d := w (law.atoms.head empty)
  have dSupport : law.mass (event ∩ₑ valueEvent w d) ≠ 0 := by
    intro zero
    apply supported (y (law.atoms.head empty)) d
    rw [and_event_comm (valueEvent y (y (law.atoms.head empty))), ← and_event_assoc event]
    exact law.mass_and_eq_zero _ zero
  apply IndependentAt.contraction _ hXW
  apply (independent_at_iff_point_right law x y event).mpr
  intro f b
  let l := f ∘ x
  let lhs := event ∩ₑ l
  let row := valueEvent y b
  let col := valueEvent w d
  have each (b' : B) :
      law.mass (lhs ∩ₑ valueEvent y b') * law.mass (event ∩ₑ col) =
        law.mass ((event ∩ₑ col) ∩ₑ l) * law.mass (event ∩ₑ valueEvent y b') := by
    let row' := valueEvent y b'
    let cell := event ∩ₑ row' ∩ₑ col
    have h₁ := hXY d f (fun v => decide (v = b'))
    have h₂ := hXW b' f (fun v => decide (v = d))
    change law.mass ((event ∩ₑ col) ∩ₑ l ∩ₑ row') * law.mass (event ∩ₑ col) =
      law.mass ((event ∩ₑ col) ∩ₑ l) * law.mass ((event ∩ₑ col) ∩ₑ row') at h₁
    change law.mass ((event ∩ₑ row') ∩ₑ l ∩ₑ col) * law.mass (event ∩ₑ row') =
      law.mass ((event ∩ₑ row') ∩ₑ l) * law.mass ((event ∩ₑ row') ∩ₑ col) at h₂
    let joint := cell ∩ₑ l
    have joint₁ : (event ∩ₑ col) ∩ₑ l ∩ₑ row' = joint := by
      funext u
      simp [joint, cell, andEvent, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    have joint₂ : (event ∩ₑ row') ∩ₑ l ∩ₑ col = joint := by
      funext u
      simp [joint, cell, andEvent, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    have cell₁ : (event ∩ₑ col) ∩ₑ row' = cell := by
      rw [and_event_assoc, and_event_comm col row']
    have cell₂ : (event ∩ₑ row') ∩ₑ col = cell := and_event_assoc _ _ _
    have rowLeft : (event ∩ₑ row') ∩ₑ l = lhs ∩ₑ row' := and_event_rotate _ _ _
    rw [joint₁, cell₁] at h₁
    rw [joint₂, rowLeft, cell₂] at h₂
    change law.mass (lhs ∩ₑ row') * law.mass (event ∩ₑ col) =
      law.mass ((event ∩ₑ col) ∩ₑ l) * law.mass (event ∩ₑ row')
    have hs :
        (law.mass (lhs ∩ₑ row') * law.mass (event ∩ₑ col)) * law.mass cell =
          (law.mass ((event ∩ₑ col) ∩ₑ l) * law.mass (event ∩ₑ row')) * law.mass cell := by
      grind
    have hn : law.mass cell ≠ 0 := supported b' d
    simpa only [Rat.mul_div_cancel hn] using congrArg (· / law.mass cell) hs
  have total := law.scaled_masses_of_values y lhs event _ _ each
  have hb := each b
  change law.mass (lhs ∩ₑ row) * law.mass event = law.mass lhs * law.mass (event ∩ₑ row)
  have hs :
      (law.mass (lhs ∩ₑ row) * law.mass event) * law.mass (event ∩ₑ col) =
        (law.mass lhs * law.mass (event ∩ₑ row)) * law.mass (event ∩ₑ col) := by
    grind
  have hn : law.mass (event ∩ₑ col) ≠ 0 := dSupport
  simpa only [Rat.mul_div_cancel hn] using congrArg (· / law.mass (event ∩ₑ col)) hs

theorem IndependentGiven.intersection [DecidableEq B] [DecidableEq C] [DecidableEq D]
    {law : FiniteLaw Ω} {x : Ω → A} {y : Ω → B} {w : Ω → D} {z : Ω → C}
    (hXY : law.IndependentGiven x y (fun u => (z u, w u)))
    (hXW : law.IndependentGiven x w (fun u => (z u, y u)))
    (supported : ∀ c, law.mass (valueEvent z c) ≠ 0 → ∀ b d,
      law.mass (valueEvent z c ∩ₑ valueEvent y b ∩ₑ valueEvent w d) ≠ 0) :
    law.IndependentGiven x (fun u => (y u, w u)) z := by
  intro c
  by_cases zero : law.mass (valueEvent z c) = 0
  · exact law.independent_at_zero zero _ _
  apply IndependentAt.intersection _ _ (supported c zero)
  · intro d
    have h := hXY (c, d)
    rwa [value_event_pair] at h
  · intro b
    have h := hXW (c, b)
    rwa [value_event_pair] at h

end FiniteLaw

end

end OpenCausalScience.Probability
