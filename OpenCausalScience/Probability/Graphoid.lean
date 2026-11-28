module
public import Std

/-! # Conditional independence on finite variable sets -/

namespace OpenCausalScience.Probability.CI

@[expose] public section

variable {n : Nat}

abbrev Mask (n : Nat) := Fin n → Bool

abbrev Relation (n : Nat) := Mask n → Mask n → Mask n → Prop

def empty : Mask n := fun _ => false

def single (x : Fin n) : Mask n := fun v => v == x

def union (A B : Mask n) : Mask n := fun v => A v || B v

def inter (A B : Mask n) : Mask n := fun v => A v && B v

def diff (A B : Mask n) : Mask n := fun v => A v && !B v

def Subset (A B : Mask n) : Prop := ∀ v, A v = true → B v = true

def Disjoint (A B : Mask n) : Prop := ∀ v, A v = true → B v = false

def Disjoint3 (A B C : Mask n) : Prop := Disjoint A B ∧ Disjoint A C ∧ Disjoint B C

def Disjoint4 (A B C D : Mask n) : Prop :=
  Disjoint3 A B C ∧ Disjoint A D ∧ Disjoint B D ∧ Disjoint C D

structure Semigraphoid (J : Relation n) : Prop where
  empty_right (X Z : Mask n) : J X empty Z
  symmetry {X Y Z : Mask n} : J X Y Z → J Y X Z
  decomposition {X Y W Z : Mask n} : Disjoint4 X Y W Z → J X (union Y W) Z → J X Y Z
  weak_union {X Y W Z : Mask n} : Disjoint4 X Y W Z → J X (union Y W) Z → J X Y (union Z W)
  contraction {X Y W Z : Mask n} : Disjoint4 X Y W Z →
    J X Y Z → J X W (union Z Y) → J X (union Y W) Z

structure Graphoid (J : Relation n) : Prop extends Semigraphoid J where
  intersection {X Y W Z : Mask n} : Disjoint4 X Y W Z →
    J X Y (union Z W) → J X W (union Z Y) → J X (union Y W) Z

theorem subset_refl (A : Mask n) : Subset A A := fun _ h => h

theorem Subset.trans {A B C : Mask n} (ab : Subset A B) (bc : Subset B C) :
    Subset A C := fun v hv => bc v (ab v hv)

theorem Disjoint.symm {A B : Mask n} (h : Disjoint A B) : Disjoint B A := by
  intro v hv
  exact Bool.eq_false_iff.mpr fun ha => Bool.false_ne_true ((h v ha).symm.trans hv)

theorem Disjoint.restrict_left {A B C : Mask n} (h : Disjoint A B) (sub : Subset C A) :
    Disjoint C B := fun v hv => h v (sub v hv)

theorem Disjoint.restrict_right {A B C : Mask n} (h : Disjoint A B) (sub : Subset C B) :
    Disjoint A C := (h.symm.restrict_left sub).symm

theorem subset_union_left (A B : Mask n) : Subset A (union A B) := by
  intro v hv
  simp [union, hv]

theorem subset_union_right (A B : Mask n) : Subset B (union A B) := by
  intro v hv
  simp [union, hv]

theorem subset_diff_left (A B : Mask n) : Subset (diff A B) A := by
  intro v hv
  exact (Bool.and_eq_true_iff.mp hv).1

theorem disjoint_diff_right (A B : Mask n) : Disjoint (diff A B) B := by
  intro v hv
  simpa using (Bool.and_eq_true_iff.mp hv).2

theorem union_eq_of_subset_diff {A B : Mask n} (sub : Subset A B) :
    union A (diff B A) = B := by
  funext v
  cases ha : A v with
  | false => simp [union, diff, ha]
  | true => simp [union, ha, sub v ha]

theorem Semigraphoid.decompose_subset {J : Relation n} (g : Semigraphoid J)
    {X Y Z B : Mask n} (disj : Disjoint3 X Y Z) (sub : Subset B Y) (ci : J X Y Z) :
    J X B Z := by
  have subsetR := subset_diff_left Y B
  have h : Disjoint4 X B (diff Y B) Z :=
    ⟨⟨disj.1.restrict_right sub, disj.1.restrict_right subsetR, (disjoint_diff_right Y B).symm⟩,
      disj.2.1, disj.2.2.restrict_left sub, disj.2.2.restrict_left subsetR⟩
  apply g.decomposition h
  rwa [union_eq_of_subset_diff sub]

end

end OpenCausalScience.Probability.CI
