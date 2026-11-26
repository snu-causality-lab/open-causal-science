module
public import Std

/-! # Product of c-factors

Tian and Pearl (2003), R-290-L, Equations (55) and (70). At a fixed
observed cell and intervention assignment, the observed equations
split into factors by c-component. Each factor uses only its own
exogenous block. The result below sums the product over actual joint
root assignments, and proves that this equals the product of the
individually marginalized block factors.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=22
-/

namespace OpenCausalScience.Papers.TianPearl2003.DistrictProduct

@[expose] public section

variable {Ω : Type}

/-- The independent finite root block supplying one component's
likelihood at the specified observed cell. A deterministic SCM uses a
zero-or-one likelihood. -/
structure RootBlock (Ω : Type) where
  atoms : List Ω
  weight : Ω → Rat
  cellLikelihood : Ω → Rat
  nonnegative : ∀ atom ∈ atoms, 0 ≤ weight atom
  normalized : (atoms.map weight).sum = 1

def RootBlock.contribution (block : RootBlock Ω) (atom : Ω) : Rat :=
  block.weight atom * block.cellLikelihood atom

def RootBlock.factor (block : RootBlock Ω) : Rat :=
  (block.atoms.map block.contribution).sum

/-- The Cartesian product of the lists of exogenous atoms. -/
def assignments : List (RootBlock Ω) → List (List Ω)
  | [] => [[]]
  | head :: tail => head.atoms.flatMap fun atom =>
    (assignments tail).map (atom :: ·)

/-- The product-law weight times the likelihood of the observed cell. -/
def weightedLikelihood : List (RootBlock Ω) → List Ω → Rat
  | [], [] => 1
  | head :: tail, atom :: rest => head.contribution atom * weightedLikelihood tail rest
  | _, _ => 0

def jointMass (blocks : List (RootBlock Ω)) : Rat :=
  ((assignments blocks).map (weightedLikelihood blocks)).sum

private theorem sum_times {A : Type} (values : List A) (f : A → Rat) (c : Rat) :
    (values.map fun a => c * f a).sum = c * (values.map f).sum := by
  induction values with
  | nil => simp [Rat.mul_zero]
  | cons a rest ih => simp [ih, Rat.mul_add]

private theorem sum_times_right {A : Type} (values : List A) (f : A → Rat) (c : Rat) :
    (values.map fun a => f a * c).sum = (values.map f).sum * c := by
  induction values with
  | nil => simp [Rat.zero_mul]
  | cons a rest ih => simp [ih, Rat.add_mul]

private theorem sum_flat_map {A B : Type} (as : List A) (values : A → List B) (f : B → Rat) :
    ((as.flatMap values).map f).sum = (as.map fun a => ((values a).map f).sum).sum := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp [ih]

theorem joint_mass_eq_product_factors (blocks : List (RootBlock Ω)) :
    jointMass blocks = (blocks.map RootBlock.factor).prod := by
  induction blocks with
  | nil => simp [jointMass, weightedLikelihood, assignments, Rat.add_zero]
  | cons head tail ih =>
    unfold jointMass at ih ⊢
    rw [assignments, sum_flat_map]
    simp only [List.map_map, List.map_cons, List.prod_cons]
    have inner (atom : Ω) :
        (List.map (weightedLikelihood (head :: tail) ∘ (atom :: ·)) (assignments tail)).sum =
          head.contribution atom * ((assignments tail).map (weightedLikelihood tail)).sum :=
      sum_times (assignments tail) _ _
    rw [List.map_congr_left (fun atom _ => inner atom), sum_times_right, ih]
    rfl

end

end OpenCausalScience.Papers.TianPearl2003.DistrictProduct
