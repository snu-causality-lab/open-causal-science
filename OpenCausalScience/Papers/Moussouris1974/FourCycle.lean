module
public import OpenCausalScience.Papers.Grimmett1973.CliqueFactorization

/-! # Moussouris's four-cycle support example

The eight configurations of Figure 3(a) are also listed in Geiger,
Meek and Sturmfels (2006), Example 7, equation (4.12).
-/

namespace OpenCausalScience.Papers.Moussouris1974

open Grimmett1973

@[expose] public section

abbrev State := Assignment (fun _ : Fin 4 => Bool)

def state (a b c d : Bool) : State :=
  fun v => if v = 0 then a else if v = 1 then b else if v = 2 then c else d

def support : List (Bool × Bool × Bool × Bool) :=
  [(false, false, false, false), (true, false, false, false),
   (true, true, false, false), (true, true, true, false), (true, true, true, true),
   (false, true, true, true), (false, false, true, true), (false, false, false, true)]

def onSupport (x : State) : Bool := support.contains (x 0, x 1, x 2, x 3)

def probability (x : State) : Rat := if onSupport x then 1 / 8 else 0

def edge (u v : Fin 4) : Prop := (u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val

instance (u v : Fin 4) : Decidable (edge u v) := by
  unfold edge
  infer_instance

def missing : State := state false false true false

private theorem vertex_cases (v : Fin 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  omega

private theorem state_coordinates (x : State) : state (x 0) (x 1) (x 2) (x 3) = x := by
  funext v
  rcases vertex_cases v with rfl | rfl | rfl | rfl <;> rfl

def assignments : List (Bool × Bool × Bool × Bool) :=
  [false, true].flatMap fun a =>
    [false, true].flatMap fun b =>
      [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d)

theorem probability_nonnegative (x : State) : 0 ≤ probability x := by
  unfold probability
  split <;> decide +kernel

theorem probability_normalized :
    assignments.Nodup ∧ (∀ a, a ∈ assignments) ∧
      (assignments.map fun (a, b, c, d) => probability (state a b c d)).sum = 1 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  rintro ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private theorem nonedges (u v : Fin 4) (different : u ≠ v) (absent : ¬ edge u v) :
    (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) := by
  rcases vertex_cases u with rfl | rfl | rfl | rfl <;>
    rcases vertex_cases v with rfl | rfl | rfl | rfl <;>
    revert different absent <;> decide +kernel

private theorem rectangle_02 : Rectangle probability 0 2 := by
  have checked : ∀ (a b c d s s' t t' : Bool),
      probability (pairChanges (state a b c d) 0 2 s t) *
        probability (pairChanges (state a b c d) 0 2 s' t') =
      probability (pairChanges (state a b c d) 0 2 s t') *
        probability (pairChanges (state a b c d) 0 2 s' t) := by decide +kernel
  intro x
  rw [← state_coordinates x]
  exact checked _ _ _ _

private theorem rectangle_13 : Rectangle probability 1 3 := by
  have checked : ∀ (a b c d s s' t t' : Bool),
      probability (pairChanges (state a b c d) 1 3 s t) *
        probability (pairChanges (state a b c d) 1 3 s' t') =
      probability (pairChanges (state a b c d) 1 3 s t') *
        probability (pairChanges (state a b c d) 1 3 s' t) := by decide +kernel
  intro x
  rw [← state_coordinates x]
  exact checked _ _ _ _

private theorem reverse_rectangle {u v : Fin 4} (different : u ≠ v)
    (forward : Rectangle probability u v) : Rectangle probability v u := by
  intro x b b' a a'
  simp only [pairChanges, setAt_commute x different.symm]
  have h := forward x a a' b b'
  simp only [pairChanges] at h
  rw [Rat.mul_comm (probability (setAt (setAt x u a) v b'))] at h
  exact h

theorem pairwise_markov : PairwiseMarkov edge probability := by
  intro u v different absent
  rcases nonedges u v different absent with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rectangle_02
  · exact reverse_rectangle (by decide) rectangle_02
  · exact rectangle_13
  · exact reverse_rectangle (by decide) rectangle_13

theorem absent_configuration : probability missing = 0 := by decide +kernel

private theorem witness_mask (m0 m1 m2 m3 : Bool)
    (first : m0 = true → m2 = false) (second : m1 = true → m3 = false) :
    ∃ a b c d : Bool, onSupport (state a b c d) = true ∧
      (m0 = true → a = false) ∧ (m1 = true → b = false) ∧
      (m2 = true → c = true) ∧ (m3 = true → d = false) := by
  revert m0 m1 m2 m3 first second
  decide +kernel

theorem every_clique_projection_is_realized (scope : List (Fin 4))
    (clique : IsClique edge scope) :
    ∃ x : State, probability x ≠ 0 ∧ ∀ v ∈ scope, missing v = x v := by
  let mask (v : Fin 4) : Bool := decide (v ∈ scope)
  have excludes_opposite {u v : Fin 4} (different : u ≠ v) (absent : ¬ edge u v)
      (present : mask u = true) : mask v = false := by
    apply decide_eq_false
    exact fun hv => absent (clique u (of_decide_eq_true present) v hv different)
  obtain ⟨a, b, c, d, supported, at0, at1, at2, at3⟩ :=
    witness_mask (mask 0) (mask 1) (mask 2) (mask 3)
      (excludes_opposite (by decide) (by decide +kernel))
      (excludes_opposite (by decide) (by decide +kernel))
  refine ⟨state a b c d, ?_, ?_⟩
  · rw [probability, supported]
    change (1 / 8 : Rat) ≠ 0
    decide +kernel
  · intro v member
    have in_mask : mask v = true := decide_eq_true member
    rcases vertex_cases v with rfl | rfl | rfl | rfl
    · exact (at0 in_mask).symm
    · exact (at1 in_mask).symm
    · exact (at2 in_mask).symm
    · exact (at3 in_mask).symm

theorem does_not_factor : ¬ CliqueFactorization edge probability := by
  intro factorized
  exact factored_nonzero_of_locally_realized factorized missing
    every_clique_projection_is_realized absent_configuration

theorem pairwise_markov_not_clique_factorization :
    PairwiseMarkov edge probability ∧ ¬ CliqueFactorization edge probability :=
  ⟨pairwise_markov, does_not_factor⟩

end

end OpenCausalScience.Papers.Moussouris1974
