module
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # Parallel worlds and node merging

Shpitser and Pearl, JMLR 9 (2008), Lemmas 24–25 and Figure 10.
Worlds share the same exogenous assignment. For copies of the same
binary variable, equal inputs to the shared mechanism give equal
responses. Redirecting an input to another world copy with the same
response on the evidence preserves every query probability there.
https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=19
-/

namespace OpenCausalScience.Papers.ShpitserPearl2008.ParallelWorlds

open TianPearl2003.AncestralMarginal (Setting evaluate mass)

@[expose] public section

variable {n : Nat} {W Ω : Type}

/-- Copies have an intervention world and the index of their original variable. -/
abbrev Copy (W : Type) (n : Nat) := W × Fin n

abbrev Mechanism (Ω : Type) (n : Nat) := Ω → Fin n → (Fin n → Bool) → Bool

abbrev Representatives (W : Type) (n : Nat) := Copy W n → W

/-- Every world uses the same exogenous unit and the original equations. -/
def response (G : DAG n) (mechanism : Mechanism Ω n) (settings : W → Setting n)
    (unit : Ω) (copy : Copy W n) : Bool :=
  evaluate G mechanism unit (settings copy.1) copy.2

/-- Lemma 24 for same-variable copies. Exogenous inputs already match
because both equations read the same unit. Endogenous inputs may match
because they share a representative or take the same value on the evidence. -/
theorem response_eq_of_matching_parents (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (unit : Ω) {v : Fin n} {first second : W}
    (freeFirst : settings first v = none) (freeSecond : settings second v = none)
    (agree : ∀ u, G.edge u v = true →
      response G mechanism settings unit (first, u) = response G mechanism settings unit (second, u)) :
    response G mechanism settings unit (first, v) = response G mechanism settings unit (second, v) := by
  unfold response
  rw [evaluate, evaluate]
  simp only [freeFirst, freeSecond]
  apply congrArg (mechanism unit v)
  funext u
  by_cases arrow : G.edge u v = true
  · simp only [dite_eq_left arrow]
    exact agree u arrow
  · simp [arrow]

/-- Evaluate with the representative's equation and original parent
world. Each parent input is itself read through the representative map. -/
def mergedResponse (G : DAG n) (mechanism : Mechanism Ω n) (settings : W → Setting n)
    (representative : Representatives W n) (unit : Ω) (copy : Copy W n) : Bool :=
  let chosen := representative copy
  match settings chosen copy.2 with
  | some value => value
  | none => mechanism unit copy.2 (fun u =>
    if _parent : G.edge u copy.2 = true then
      mergedResponse G mechanism settings representative unit (chosen, u)
    else false)
termination_by G.rank copy.2
decreasing_by exact G.edge_increases _ _ _parent

/-- Lemma 25 at the response level. Redirecting all parent inputs through
valid representatives preserves the evaluated values on each supported unit. -/
theorem merged_response_eq (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (representative : Representatives W n) (unit : Ω)
    (valid : ∀ c, response G mechanism settings unit (representative c, c.2) =
      response G mechanism settings unit c) (copy : Copy W n) :
    mergedResponse G mechanism settings representative unit copy =
      response G mechanism settings unit copy := by
  induction height : G.rank copy.2 using Nat.strongRecOn generalizing copy with
  | ind rank ih =>
    rw [← valid copy, mergedResponse, response, evaluate]
    dsimp only
    cases setting : settings (representative copy) copy.2 with
    | some value => rfl
    | none =>
      apply congrArg (mechanism unit copy.2)
      funext u
      by_cases arrow : G.edge u copy.2 = true
      · simp only [dite_eq_left arrow]
        exact ih (G.rank u) (height ▸ G.edge_increases _ _ arrow) (representative copy, u) rfl
      · simp [arrow]

structure Atom (W : Type) (n : Nat) where
  copy : Copy W n
  value : Bool

/-- A query is a conjunction of binary outcome assignments. -/
def holds (value : Copy W n → Bool) (query : List (Atom W n)) : Bool :=
  query.all (fun atom => value atom.copy == atom.value)

/-- Rename the occurrence to the copy retained by `make-cg`. -/
def rename (representative : Representatives W n) (query : List (Atom W n)) :
    List (Atom W n) :=
  query.map fun atom => ⟨(representative atom.copy, atom.copy.2), atom.value⟩

theorem holds_congr {first second : Copy W n → Bool} {query : List (Atom W n)}
    (agree : ∀ atom ∈ query, first atom.copy = second atom.copy) :
    holds first query = holds second query := by
  induction query with
  | nil => rfl
  | cons atom query ih =>
    simp only [holds, List.all_cons]
    rw [agree atom List.mem_cons_self]
    exact congrArg _ (ih (fun entry member => agree entry (List.mem_cons_of_mem _ member)))

/-- Renaming the query and updating the mechanisms' read locations preserves
joint mass with the evidence. The evidence guard need only guarantee equality
on its own event, as with the observed value in Figures 9 and 11. -/
theorem merge_preserves_mass (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (representative : Representatives W n)
    (units : List Ω) (weight : Ω → Rat) (evidence : Ω → Bool)
    (valid : ∀ unit, evidence unit = true → ∀ c,
      response G mechanism settings unit (representative c, c.2) =
      response G mechanism settings unit c)
    (query : List (Atom W n)) :
    mass units weight (fun unit => evidence unit && holds (response G mechanism settings unit) query) =
      mass units weight (fun unit => evidence unit &&
        holds (mergedResponse G mechanism settings representative unit) (rename representative query)) := by
  apply congrArg (mass units weight)
  funext unit
  cases observed : evidence unit with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    change holds (response G mechanism settings unit) query = holds _ (rename representative query)
    unfold rename
    simp only [holds, List.all_map]
    change holds (response G mechanism settings unit) query =
      holds (fun c => mergedResponse G mechanism settings representative unit (representative c, c.2)) query
    apply holds_congr
    intro atom _
    rw [merged_response_eq G mechanism settings representative unit (valid unit observed)]
    exact (valid unit observed atom.copy).symm

/-- Asking equivalent copies to attain different values makes a conjunction empty. -/
theorem incompatible_merged_assignments {value : Copy W n → Bool} {left right : Copy W n}
    {a b : Bool} (same : value left = value right) (distinct : a ≠ b) :
    holds value [⟨left, a⟩, ⟨right, b⟩] = false := by
  cases checked : holds value [⟨left, a⟩, ⟨right, b⟩] with
  | false => rfl
  | true =>
    simp only [holds, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq] at checked
    exact (distinct (checked.1.symm.trans (same.trans checked.2))).elim

end
end OpenCausalScience.Papers.ShpitserPearl2008.ParallelWorlds
