module
public import OpenCausalScience.Probability.Graphoid

/-! The finite library of singleton conditional-independence queries. -/

namespace OpenCausalScience.Discovery.FiniteCIQueries

open OpenCausalScience.Probability.CI

@[expose] public section

variable {n : Nat}

def variableMasks : (n : Nat) → List (Mask n)
  | 0 => [empty]
  | n + 1 => (variableMasks n).map (fun tail => Fin.cases (motive := fun _ => Bool) false tail) ++
      (variableMasks n).map (fun tail => Fin.cases (motive := fun _ => Bool) true tail)

theorem mem_variable_masks (P : Mask n) : P ∈ variableMasks n := by
  induction n with
  | zero =>
    have eq : P = empty := by funext v; exact Fin.elim0 v
    simp [variableMasks, eq]
  | succ n ih =>
    let tail : Mask n := fun v => P v.succ
    have eq : Fin.cases (P 0) tail = P := by
      funext v
      induction v using Fin.cases <;> rfl
    have present : tail ∈ variableMasks n := ih tail
    simp only [variableMasks, List.mem_append, List.mem_map]
    cases first : P 0 with
    | false => exact .inl ⟨tail, present, first ▸ eq⟩
    | true => exact .inr ⟨tail, present, first ▸ eq⟩

abbrev Comparison (n : Nat) := Fin n × Fin n × Mask n

def comparisons (n : Nat) : List (Comparison n) :=
  (List.finRange n).flatMap fun child => (List.finRange n).flatMap fun parent =>
    (variableMasks n).map (child, parent, ·)

theorem mem_comparisons (child parent : Fin n) (P : Mask n) :
    (child, parent, P) ∈ comparisons n :=
  List.mem_flatMap.mpr ⟨child, List.mem_finRange _, List.mem_flatMap.mpr
    ⟨parent, List.mem_finRange _, List.mem_map.mpr ⟨P, mem_variable_masks _, rfl⟩⟩⟩

end

end OpenCausalScience.Discovery.FiniteCIQueries
