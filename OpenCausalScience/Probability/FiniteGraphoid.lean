module
public import OpenCausalScience.Probability.ConditionalIndependence
public import OpenCausalScience.Probability.Graphoid

/-! # The independence relation of finite rational distributions -/

namespace OpenCausalScience.Probability.FiniteLaw

open CI

@[expose] public section

variable {n : Nat} {A : Type}

abbrev Block (S : Mask n) (A : Type) := {v : Fin n // S v = true} → A

def project (S : Mask n) (ω : Fin n → A) : Block S A := fun v => ω v.val

def restrictBlock {S T : Mask n} (sub : Subset S T) (value : Block T A) : Block S A :=
  fun v => value ⟨v.val, sub v.val v.property⟩

def mergeBlocks {S T : Mask n} (s : Block S A) (t : Block T A) : Block (union S T) A :=
  fun v =>
    if left : S v.val = true then s ⟨v.val, left⟩
    else t ⟨v.val, (Bool.or_eq_true_iff.mp v.property).resolve_left left⟩

private theorem restrict_project {S T : Mask n} (sub : Subset S T) (ω : Fin n → A) :
    restrictBlock sub (project T ω) = project S ω := rfl

private theorem merge_restrictions {S T : Mask n} (value : Block (union S T) A) :
    mergeBlocks (restrictBlock (subset_union_left S T) value)
      (restrictBlock (subset_union_right S T) value) = value := by
  funext v
  unfold mergeBlocks
  split <;> rfl

private theorem merge_projects (S T : Mask n) (ω : Fin n → A) :
    mergeBlocks (project S ω) (project T ω) = project (union S T) ω := by
  simpa only [restrict_project] using merge_restrictions (project (union S T) ω)

private theorem restrict_merge_left {S T : Mask n} (s : Block S A) (t : Block T A) :
    restrictBlock (subset_union_left S T) (mergeBlocks s t) = s := by
  funext v
  simp [restrictBlock, mergeBlocks, v.property]

private theorem restrict_merge_right {S T : Mask n} (disj : Disjoint S T)
    (s : Block S A) (t : Block T A) :
    restrictBlock (subset_union_right S T) (mergeBlocks s t) = t := by
  funext v
  simp [restrictBlock, mergeBlocks, disj.symm v.val v.property]

/-- Conditional independence of the coordinates selected by three masks. -/
noncomputable def setIndependence (law : FiniteLaw (Fin n → A)) : CI.Relation n := by
  classical
  exact fun X Y Z => law.IndependentGiven (project X) (project Y) (project Z)

/-- Singleton blocks have the same conditional independence as their
individual coordinate observables. -/
theorem set_singletons_iff (law : FiniteLaw (Fin n → A)) (x y : Fin n) (Z : Mask n) :
    open Classical in
    law.setIndependence (single x) (single y) Z ↔
      law.IndependentGiven (fun ω => ω x) (fun ω => ω y) (project Z) := by
  classical
  change law.IndependentGiven (project (single x)) (project (single y)) (project Z) ↔ _
  constructor
  · intro ci
    exact (ci.map_left fun b => b ⟨x, by simp [single]⟩).map_right
      (fun b => b ⟨y, by simp [single]⟩)
  · intro ci
    let packX : A → Block (single x) A := fun value _ => value
    let packY : A → Block (single y) A := fun value _ => value
    have eqX : packX ∘ (fun (ω : Fin n → A) => ω x) = project (single x) := by
      funext ω v
      have same : v.val = x := by simpa [single] using v.property
      simp [packX, project, same]
    have eqY : packY ∘ (fun (ω : Fin n → A) => ω y) = project (single y) := by
      funext ω v
      have same : v.val = y := by simpa [single] using v.property
      simp [packY, project, same]
    rw [← eqX, ← eqY]
    exact (ci.map_left packX).map_right packY

/-- The product identities on individual cells characterize finite
conditional independence inside an event. -/
theorem independent_at_iff_cell_masses {Ω X Y : Type} [DecidableEq X] [DecidableEq Y]
    (law : FiniteLaw Ω) (x : Ω → X) (y : Ω → Y) (event : Ω → Bool) :
    law.IndependentAt x y event ↔
      ∀ a b, law.mass (andEvent (andEvent event (valueEvent x a)) (valueEvent y b)) *
          law.mass event =
        law.mass (andEvent event (valueEvent x a)) * law.mass (andEvent event (valueEvent y b)) := by
  constructor
  · intro ci a b
    rw [and_event_assoc]
    exact ci (fun t => decide (t = a)) (fun t => decide (t = b))
  · intro cells
    apply (independent_at_iff_point_right law x y event).mpr
    intro f b
    let row := valueEvent y b
    rw [and_event_rotate event (f ∘ x) row, Rat.mul_comm (law.mass (andEvent event (f ∘ x)))]
    apply law.scaled_masses_of_value_test x (andEvent event row) event _ _
    intro a
    rw [and_event_rotate event row (valueEvent x a),
      Rat.mul_comm (law.mass (andEvent event row))]
    exact cells a b

/-- Coordinates of an assignment agree with a supplied stratum on its mask. -/
def stratum [DecidableEq A] (Z : Mask n) (assignment ω : Fin n → A) : Bool :=
  (List.finRange n).all fun v => decide (Z v = true → ω v = assignment v)

theorem stratum_eq_value_event [DecidableEq A] (Z : Mask n) (assignment : Fin n → A) :
    open Classical in
    stratum Z assignment = valueEvent (project Z) (project Z assignment) := by
  classical
  funext ω
  apply Bool.eq_iff_iff.mpr
  simp only [stratum, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq, valueEvent]
  constructor
  · intro equal
    funext v
    exact equal v.val v.property
  · intro equal v present
    exact congrFun equal ⟨v, present⟩

/-- An executable criterion for singleton CI with an arbitrary mask of
conditioning coordinates. The cell equations use ordinary coordinates
and Boolean events on assignments. -/
theorem set_singletons_iff_cell_masses [DecidableEq A] (law : FiniteLaw (Fin n → A))
    (x y : Fin n) (Z : Mask n) (default : A) :
    law.setIndependence (single x) (single y) Z ↔
      ∀ (assignment : Fin n → A) (a b : A),
        law.mass (andEvent (andEvent (stratum Z assignment) (valueEvent (· x) a))
            (valueEvent (· y) b)) * law.mass (stratum Z assignment) =
          law.mass (andEvent (stratum Z assignment) (valueEvent (· x) a)) *
            law.mass (andEvent (stratum Z assignment) (valueEvent (· y) b)) := by
  rw [set_singletons_iff]
  change (∀ z, law.IndependentAt (· x) (· y) (open Classical in valueEvent (project Z) z)) ↔ _
  constructor
  · intro ci assignment a b
    rw [stratum_eq_value_event]
    exact (independent_at_iff_cell_masses _ _ _ _).mp (ci (project Z assignment)) a b
  · intro cells z
    let assignment : Fin n → A := fun v => if h : Z v = true then z ⟨v, h⟩ else default
    have eq : project Z assignment = z := by
      funext v
      simp [project, assignment, v.property]
    have tests := cells assignment
    rw [stratum_eq_value_event, eq] at tests
    exact (independent_at_iff_cell_masses _ _ _ _).mpr tests

private theorem given_pair_of_union {D E : Type} (law : FiniteLaw (Fin n → A))
    (x : (Fin n → A) → D) (y : (Fin n → A) → E) (S T : Mask n) (disj : Disjoint S T) :
    open Classical in
    law.IndependentGiven x y (project (union S T)) ↔
      law.IndependentGiven x y (fun ω => (project S ω, project T ω)) := by
  classical
  have eventEq (s : Block S A) (t : Block T A) :
      valueEvent (project (union S T)) (mergeBlocks s t) =
        valueEvent (fun ω => (project S ω, project T ω)) (s, t) := by
    funext ω
    apply Bool.eq_iff_iff.mpr
    simp only [valueEvent, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have hS := congrArg (restrictBlock (subset_union_left S T)) h
        simpa only [restrict_project, restrict_merge_left] using hS
      · have hT := congrArg (restrictBlock (subset_union_right S T)) h
        simpa only [restrict_project, restrict_merge_right disj] using hT
    · rintro ⟨hS, hT⟩
      rw [← hS, ← hT, merge_projects]
  constructor
  · intro h c
    rcases c with ⟨s, t⟩
    change law.IndependentAt x y (valueEvent (fun ω => (project S ω, project T ω)) (s, t))
    rw [← eventEq]
    exact h _
  · intro h c
    have new := h (restrictBlock (subset_union_left S T) c, restrictBlock (subset_union_right S T) c)
    change law.IndependentAt x y (valueEvent _ _) at new
    rw [← eventEq, merge_restrictions] at new
    exact new

private theorem given_pair_on_right {D : Type} (law : FiniteLaw (Fin n → A))
    (x : (Fin n → A) → D) (S T Z : Mask n) :
    open Classical in
    law.IndependentGiven x (project (union S T)) (project Z) ↔
      law.IndependentGiven x (fun ω => (project S ω, project T ω)) (project Z) := by
  classical
  constructor
  · intro h
    exact h.map_right fun c => (restrictBlock (subset_union_left S T) c,
      restrictBlock (subset_union_right S T) c)
  · intro h
    have mapped := h.map_right fun p => mergeBlocks p.1 p.2
    simpa only [Function.comp_def, merge_projects] using mapped

private theorem zero_event_mass {Ω : Type} (law : FiniteLaw Ω) :
    law.mass (fun _ => false) = 0 := by
  unfold mass FiniteMass.mass
  induction law.atoms with
  | nil => rfl
  | cons a rest ih => simpa [Rat.zero_add] using ih

private theorem empty_right_ci (law : FiniteLaw (Fin n → A)) (X Z : Mask n) :
    law.setIndependence X empty Z := by
  classical
  intro z f g
  let c : Block (empty : Mask n) A := fun v => (Bool.false_ne_true v.property).elim
  have test : (g ∘ project empty) = fun _ => g c := by
    funext ω
    have constant : project empty ω = c := by
      funext v
      exact (Bool.false_ne_true v.property).elim
    exact congrArg g constant
  rw [test]
  cases v : g c
  · have andFalse (e : (Fin n → A) → Bool) : andEvent e (fun _ => false) = fun _ => false := by
      funext ω
      exact Bool.and_false (e ω)
    simp only [andFalse, zero_event_mass, Rat.zero_mul, Rat.mul_zero]
  · have andTrue (e : (Fin n → A) → Bool) : andEvent e (fun _ => true) = e := by
      funext ω
      exact Bool.and_true (e ω)
    simp only [andTrue]

/-- The finite law's set-valued CI obeys the semigraphoid rules at any support. -/
theorem set_independence_semigraphoid (law : FiniteLaw (Fin n → A)) :
    Semigraphoid law.setIndependence := by
  classical
  constructor
  · exact empty_right_ci law
  · intro X Y Z h
    exact IndependentGiven.symm h
  · intro X Y W Z _ h
    have split := (given_pair_on_right law (project X) Y W Z).mp h
    exact split.map_right Prod.fst
  · intro X Y W Z disj h
    have split := (given_pair_on_right law (project X) Y W Z).mp h
    have shifted := (split.weak_union Prod.snd).map_right Prod.fst
    exact (given_pair_of_union law (project X) (project Y) Z W disj.2.2.2.symm).mpr shifted
  · intro X Y W Z disj first second
    have split := (given_pair_of_union law (project X) (project W) Z Y disj.2.2.1.symm).mp second
    exact (given_pair_on_right law (project X) Y W Z).mpr (IndependentGiven.contraction first split)

private theorem mass_pos_of_atom {Ω : Type} (law : FiniteLaw Ω) (event : Ω → Bool)
    (a : Ω) (present : a ∈ law.atoms) (support : 0 < law.weight a) (holds : event a = true) :
    0 < law.mass event := by
  have nonnegative := law.nonnegative
  unfold mass FiniteMass.mass
  generalize eq : law.atoms = atoms at nonnegative present ⊢
  clear eq
  induction atoms with
  | nil => cases present
  | cons b rest ih =>
    have headNonnegative : 0 ≤ (if event b then law.weight b else 0) := by
      split
      · exact nonnegative b List.mem_cons_self
      · exact Rat.le_refl
    have tailNonnegative : 0 ≤ (rest.map fun ω => if event ω then law.weight ω else 0).sum := by
      let lawRest := FiniteLaw.mk rest law.weight (fun ω h => nonnegative ω (List.mem_cons_of_mem _ h))
      simpa [lawRest, mass, FiniteMass.mass] using lawRest.mass_nonnegative event
    rcases List.mem_cons.mp present with rfl | h
    · simp only [List.map_cons, List.sum_cons, holds, ↓reduceIte]
      have added : law.weight a + 0 ≤ law.weight a +
          (rest.map fun ω => if event ω then law.weight ω else 0).sum :=
        Rat.add_le_add_left.mpr tailNonnegative
      rw [Rat.add_zero] at added
      exact Rat.not_le.mp (fun h => Rat.not_le.mpr support (Rat.le_trans added h))
    · have pos := ih (fun ω hv => nonnegative ω (List.mem_cons_of_mem _ hv)) h
      simp only [List.map_cons, List.sum_cons]
      let tail := (rest.map fun ω => if event ω then law.weight ω else 0).sum
      have added : 0 + tail ≤ (if event b then law.weight b else 0) + tail :=
        Rat.add_le_add_right.mpr headNonnegative
      rw [Rat.zero_add] at added
      exact Rat.not_le.mp (fun h => Rat.not_le.mpr pos (Rat.le_trans added h))

/-- Strictly positive mass at every full assignment gives the
intersection rule for disjoint masks. -/
theorem set_independence_graphoid (law : FiniteLaw (Fin n → A)) (default : A)
    (fullSupport : ∀ ω, ω ∈ law.atoms ∧ 0 < law.weight ω) :
    Graphoid law.setIndependence := by
  classical
  refine ⟨set_independence_semigraphoid law, ?_⟩
  intro X Y W Z disj first second
  have firstPair := (given_pair_of_union law (project X) (project Y) Z W disj.2.2.2.symm).mp first
  have secondPair := (given_pair_of_union law (project X) (project W) Z Y disj.2.2.1.symm).mp second
  apply (given_pair_on_right law (project X) Y W Z).mpr
  apply firstPair.intersection secondPair
  intro z _ y w
  let ω : Fin n → A := fun v =>
    if hz : Z v = true then z ⟨v, hz⟩
    else if hy : Y v = true then y ⟨v, hy⟩
    else if hw : W v = true then w ⟨v, hw⟩
    else default
  have zEq : project Z ω = z := by
    funext v
    simp [project, ω, v.property]
  have yEq : project Y ω = y := by
    funext v
    simp [project, ω, disj.2.2.1 v.val v.property, v.property]
  have wEq : project W ω = w := by
    funext v
    simp [project, ω, disj.2.2.2 v.val v.property, disj.1.2.2.symm v.val v.property,
      v.property]
  apply Rat.ne_of_gt
  apply mass_pos_of_atom law _ ω (fullSupport ω).1 (fullSupport ω).2
  simp [andEvent, valueEvent, zEq, yEq, wEq]

end

end OpenCausalScience.Probability.FiniteLaw
