module
public import OpenCausalScience.Probability.ConditionalIndependence

/-! # Support and composition in finite conditional independence

The general semigraphoid rules are in the shared probability module.
The examples below mark the distinct limits of intersection without
rectangular support and composition even with full support.
-/

namespace OpenCausalScience.Papers.Dawid1979

open Probability
open FiniteLaw

@[expose] public section

def unconditioned {Ω : Type} : Ω → Bool := fun _ => true

def boolTest (one zero : Bool) : Bool → Bool := fun b => if b then one else zero

theorem bool_test_cases (f : Bool → Bool) : boolTest (f true) (f false) = f := by
  funext b
  cases b <;> rfl

def diagonal : FiniteLaw Bool where
  atoms := [false, true]
  weight := fun _ => 1 / 2
  nonnegative := by decide +kernel

theorem intersection_can_fail_without_support :
    diagonal.IndependentGiven id id id ∧
    ¬ diagonal.IndependentAt id (fun b => (b, b)) unconditioned := by
  constructor
  · intro b f g
    rw [← bool_test_cases f, ← bool_test_cases g]
    cases b <;> cases f true <;> cases f false <;> cases g true <;> cases g false <;> decide +kernel
  · intro h
    have witness := h id Prod.fst
    revert witness
    decide +kernel

def binaryTriples : List (Bool × Bool × Bool) :=
  [false, true].flatMap fun x =>
    [false, true].flatMap fun y => [false, true].map fun z => (x, y, z)

def xorLaw : FiniteLaw (Bool × Bool × Bool) where
  atoms := binaryTriples
  weight := fun ⟨x, y, z⟩ => if (x ^^ y) = z then 3 / 16 else 1 / 16
  nonnegative := by
    rintro ⟨x, y, z⟩ _
    cases x <;> cases y <;> cases z <;> decide +kernel

def xCoord (a : Bool × Bool × Bool) : Bool := a.1
def yCoord (a : Bool × Bool × Bool) : Bool := a.2.1
def zCoord (a : Bool × Bool × Bool) : Bool := a.2.2

theorem composition_can_fail_at_full_support :
    (∀ a, 0 < xorLaw.weight a) ∧
    xorLaw.mass unconditioned = 1 ∧
    xorLaw.IndependentAt zCoord xCoord unconditioned ∧
    xorLaw.IndependentAt zCoord yCoord unconditioned ∧
    ¬ xorLaw.IndependentAt zCoord (fun a => (xCoord a, yCoord a)) unconditioned := by
  refine ⟨?_, by decide +kernel, ?_, ?_, ?_⟩
  · rintro ⟨x, y, z⟩
    cases x <;> cases y <;> cases z <;> decide +kernel
  · intro f g
    rw [← bool_test_cases f, ← bool_test_cases g]
    cases f true <;> cases f false <;> cases g true <;> cases g false <;> decide +kernel
  · intro f g
    rw [← bool_test_cases f, ← bool_test_cases g]
    cases f true <;> cases f false <;> cases g true <;> cases g false <;> decide +kernel
  · intro h
    have witness := h id (fun b => b.1 && b.2)
    revert witness
    decide +kernel

end

end OpenCausalScience.Papers.Dawid1979
