module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Probability.FiniteMass

/-! # Ancestral marginalization of intervention kernels

Tian and Pearl (2003), R-290-L, Lemma 3, Equation (69). The equations of a
finite binary structural model read only their graph parents. A set is
ancestral in the current free graph when every parent outside that set
is already fixed. Keeping the same exogenous law, additionally fixing
the other free variables preserves the retained response on each unit.
Summing the cells of the original kernel then gives the new kernel.
Latent roots can be included among the vertices retained on both sides,
and marginalized by using an event that reads only the retained
observed variables.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=21
-/

namespace OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

@[expose] public section

variable {n : Nat} {G : DAG n} {Ω : Type}

abbrev Setting (n : Nat) := Fin n → Option Bool

/-- Inputs at indices with no parent arrow are always false. -/
def evaluate (G : DAG n) (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (unit : Ω)
    (fixed : Setting n) (v : Fin n) : Bool :=
  match fixed v with
  | some x => x
  | none => mechanism unit v (fun u =>
    if _parent : G.edge u v = true then evaluate G mechanism unit fixed u else false)
termination_by G.rank v
decreasing_by exact G.edge_increases _ _ _parent

def addClamps (keep : Fin n → Bool) (values : Fin n → Bool) (fixed : Setting n) : Setting n :=
  fun v => if keep v then fixed v else
    match fixed v with
    | some x => some x
    | none => some (values v)

def ancestralAmongFree (G : DAG n) (keep : Fin n → Bool) (fixed : Setting n) : Prop :=
  ∀ u v, G.edge u v = true → keep v = true → keep u = true ∨ fixed u ≠ none

theorem retained_evaluation_unchanged (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (unit : Ω)
    (keep values : Fin n → Bool) (fixed : Setting n)
    (ancestral : ancestralAmongFree G keep fixed) (v : Fin n) (retained : keep v = true) :
    evaluate G mechanism unit fixed v = evaluate G mechanism unit (addClamps keep values fixed) v := by
  induction bound : G.rank v using Nat.strongRecOn generalizing v with
  | ind rank ih =>
    rw [evaluate, evaluate]
    have unchanged : addClamps keep values fixed v = fixed v := by simp [addClamps, retained]
    rw [unchanged]
    cases fixed v with
    | some _ => rfl
    | none =>
      apply congrArg (mechanism unit v)
      funext u
      by_cases parent : G.edge u v = true
      · rw [dite_eq_left parent, dite_eq_left parent]
        obtain kept | clamped := ancestral u v parent retained
        · have smaller := G.edge_increases _ _ parent
          exact ih (G.rank u) (by omega) u kept rfl
        · rw [evaluate, evaluate]
          have same : addClamps keep values fixed u = fixed u := by
            cases value : fixed u with
            | none => contradiction
            | some _ => simp [addClamps, value]
          rw [same]
          cases value : fixed u with
          | none => exact (clamped value).elim
          | some _ => rfl
      · rw [dite_eq_right parent, dite_eq_right parent]

def mass (atoms : List Ω) (weight : Ω → Rat) (event : Ω → Bool) : Rat :=
  OpenCausalScience.Probability.FiniteMass.mass atoms weight event

def readsOnly (event : (Fin n → Bool) → Bool) (keep : Fin n → Bool) : Prop :=
  ∀ first second, (∀ v, keep v = true → first v = second v) → event first = event second

theorem retained_mass_unchanged (G : DAG n) (mechanism : Ω → Fin n → (Fin n → Bool) → Bool)
    (atoms : List Ω) (weight : Ω → Rat) (keep values : Fin n → Bool) (fixed : Setting n)
    (ancestral : ancestralAmongFree G keep fixed) (event : (Fin n → Bool) → Bool)
    (reads : readsOnly event keep) :
    mass atoms weight (fun unit => event (evaluate G mechanism unit fixed)) =
      mass atoms weight (fun unit => event (evaluate G mechanism unit (addClamps keep values fixed))) := by
  apply congrArg (mass atoms weight)
  funext unit
  exact reads _ _ (retained_evaluation_unchanged G mechanism unit keep values fixed ancestral)

theorem sum_masses_of_partition {A : Type} [DecidableEq A] (states : List A)
    (unique : states.Nodup) (atoms : List Ω) (weight : Ω → Rat)
    (cell : Ω → A) (exhaustive : ∀ unit ∈ atoms, cell unit ∈ states) (event : Ω → Bool) :
    (states.map fun a => mass atoms weight (fun unit => event unit && decide (cell unit = a))).sum =
      mass atoms weight event :=
  OpenCausalScience.Probability.FiniteMass.sum_masses_of_partition
    states unique atoms weight cell exhaustive event

/-- The sum of the old kernel cells on the removed coordinates equals
the retained event mass in the kernel with the extra clamps. -/
theorem ancestral_marginal_equals_kernel {A : Type} [DecidableEq A] (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (atoms : List Ω) (weight : Ω → Rat)
    (keep values : Fin n → Bool) (fixed : Setting n)
    (ancestral : ancestralAmongFree G keep fixed) (event : (Fin n → Bool) → Bool)
    (reads : readsOnly event keep) (removedCell : (Fin n → Bool) → A) (cells : List A)
    (unique : cells.Nodup)
    (exhaustive : ∀ unit ∈ atoms, removedCell (evaluate G mechanism unit fixed) ∈ cells) :
    (cells.map fun a => mass atoms weight (fun unit =>
      event (evaluate G mechanism unit fixed) &&
        decide (removedCell (evaluate G mechanism unit fixed) = a))).sum =
      mass atoms weight (fun unit => event (evaluate G mechanism unit (addClamps keep values fixed))) := by
  rw [sum_masses_of_partition cells unique atoms weight _ exhaustive]
  exact retained_mass_unchanged G mechanism atoms weight keep values fixed ancestral event reads

end

end OpenCausalScience.Papers.TianPearl2003.AncestralMarginal
