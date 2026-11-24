module
public import Std

/-!
# Kwon et al. (2025), aggregate reward and static border mixtures

Section 7 and Appendix H of the 2026-10-25 correction replace the temporal
restriction with a static border family for the aggregate reward. The model
below uses finite rational probability laws. The expected value comparison
uses the same law throughout, and supports may include the empty cut.

Sources:
* https://openreview.net/forum?id=F4LhOqhxkk
* https://www.sanghacklee.me/ai-corrected/NS_SCB_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.KwonEtAl2025.AggregateReward

@[expose] public section

def weightedSum {α : Type} (atoms : List α) (weight value : α → Rat) : Rat :=
  (atoms.map fun atom => weight atom * value atom).sum

private theorem sum_add {α : Type} (atoms : List α) (f g : α → Rat) :
    (atoms.map fun x => f x + g x).sum = (atoms.map f).sum + (atoms.map g).sum := by
  induction atoms with
  | nil => simp [Rat.add_zero]
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ac_rfl

private theorem sum_mul {α : Type} (atoms : List α) (f : α → Rat) (c : Rat) :
    (atoms.map fun x => f x * c).sum = (atoms.map f).sum * c := by
  induction atoms with
  | nil => simp
  | cons x xs ih => simp [ih, Rat.add_mul]

private theorem sum_le {α : Type} (atoms : List α) (f g : α → Rat)
    (bound : ∀ x ∈ atoms, f x ≤ g x) : (atoms.map f).sum ≤ (atoms.map g).sum := by
  induction atoms with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Rat.le_trans (Rat.add_le_add_right.mpr (bound x (by simp)))
      (Rat.add_le_add_left.mpr (ih (fun y hy => bound y (by simp [hy]))))

private theorem sum_zero {α : Type} (atoms : List α) :
    (atoms.map fun _ => (0 : Rat)).sum = 0 := by
  induction atoms <;> simp [Rat.zero_add, *]

private theorem sum_nonneg {α : Type} (atoms : List α) (f : α → Rat)
    (nonneg : ∀ x ∈ atoms, 0 ≤ f x) : 0 ≤ (atoms.map f).sum := by
  rw [← sum_zero atoms]
  exact sum_le atoms (fun _ => 0) f nonneg

private theorem sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Rat) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp [sum_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_add, ih]

private theorem sum_indicator {α : Type} [DecidableEq α] (values : List α)
    (unique : values.Nodup) (a : α) (value : α → Rat) :
    (values.map fun b => if a = b then value b else 0).sum =
      if a ∈ values then value a else 0 := by
  induction values with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    by_cases same : a = b
    · subst b
      simp [ih tail, absent, Rat.add_zero]
    · simp [ih tail, same, Rat.zero_add]

/-- The probability of a fixed natural border assignment under `do(s)`. -/
def borderMass {Outside Assignment : Type} [DecidableEq Assignment]
    (outside : List Outside) (weight : Outside → Rat) (natural : Outside → Assignment)
    (b : Assignment) : Rat :=
  (outside.map fun u => if natural u = b then weight u else 0).sum

private theorem border_mass_nonneg {Outside Assignment : Type} [DecidableEq Assignment]
    (outside : List Outside) (weight : Outside → Rat) (natural : Outside → Assignment)
    (positive : ∀ u ∈ outside, 0 ≤ weight u) (b : Assignment) :
    0 ≤ borderMass outside weight natural b := by
  apply sum_nonneg
  intro u hu
  split
  · exact positive u hu
  · exact Rat.le_refl

private theorem group_by_border {Outside Assignment : Type} [DecidableEq Assignment]
    (outside : List Outside) (weight : Outside → Rat) (natural : Outside → Assignment)
    (assignments : List Assignment) (unique : assignments.Nodup)
    (covers : ∀ u ∈ outside, natural u ∈ assignments) (value : Assignment → Rat) :
    weightedSum outside weight (fun u => value (natural u)) =
      weightedSum assignments (borderMass outside weight natural) value := by
  unfold weightedSum
  have factors (b : Assignment) :
      borderMass outside weight natural b * value b =
        (outside.map fun u => if natural u = b then weight u * value b else 0).sum := by
    unfold borderMass
    rw [← sum_mul]
    congr 1
    apply List.map_congr_left
    intro u _
    split <;> simp_all
  calc
    _ = (outside.map fun u =>
        (assignments.map fun b => if natural u = b then weight u * value b else 0).sum).sum := by
      congr 1
      apply List.map_congr_left
      intro u hu
      simp [sum_indicator assignments unique, covers u hu]
    _ = (assignments.map fun b =>
        (outside.map fun u => if natural u = b then weight u * value b else 0).sum).sum :=
      sum_swap outside assignments _
    _ = _ := by simp only [← factors]

/-- The weights are the distribution of the natural border under `do(s)`,
including zero-mass assignments. They form a probability law. -/
theorem border_mass_normalized {Outside Assignment : Type} [DecidableEq Assignment]
    (outside : List Outside) (weight : Outside → Rat) (natural : Outside → Assignment)
    (assignments : List Assignment) (unique : assignments.Nodup)
    (covers : ∀ u ∈ outside, natural u ∈ assignments)
    (positive : ∀ u ∈ outside, 0 ≤ weight u) (normalized : (outside.map weight).sum = 1) :
    (∀ b ∈ assignments, 0 ≤ borderMass outside weight natural b) ∧
      (assignments.map (borderMass outside weight natural)).sum = 1 := by
  refine ⟨fun b _ => border_mass_nonneg outside weight natural positive b, ?_⟩
  simpa [weightedSum] using
    (group_by_border outside weight natural assignments unique covers (fun _ => 1)).symm.trans
      (by simpa [weightedSum] using normalized)

/-- A finite nonnegative probability average is bounded by every common
upper bound for the values. -/
theorem weighted_sum_le {α : Type} (atoms : List α) (weight value : α → Rat) (upper : Rat)
    (positive : ∀ x ∈ atoms, 0 ≤ weight x) (normalized : (atoms.map weight).sum = 1)
    (bound : ∀ x ∈ atoms, value x ≤ upper) : weightedSum atoms weight value ≤ upper := by
  have comparison := sum_le atoms (fun x => weight x * value x) (fun x => weight x * upper)
    (fun x hx => Rat.mul_le_mul_of_nonneg_left (bound x hx) (positive x hx))
  rwa [sum_mul, normalized, Rat.one_mul] at comparison

abbrev Plan (V State : Type) := V → Option State

/-- A ranked SCM on an expanded DAG. `uses` records each direct use of a
source, so the same source may occur in more than two equations. -/
structure SCM (V Source State Noise : Type) where
  rank : V → Nat
  parent : V → V → Prop
  uses : Source → V → Prop
  parent_lower : ∀ {p v}, parent p v → rank p < rank v
  law : V → (V → State) → (Source → Noise) → State
  evaluate : Plan V State → (Source → Noise) → V → State
  solve : ∀ plan noise v,
    evaluate plan noise v = (plan v).getD (law v (evaluate plan noise) noise)
  respects_inputs : ∀ v left right noise other,
    (∀ p, parent p v → left p = right p) →
    (∀ u, uses u v → noise u = other u) →
    law v left noise = law v right other

variable {V Source State Noise : Type}

private theorem evaluate_agrees (model : SCM V Source State Noise)
    (plan otherPlan : Plan V State) (noise otherNoise : Source → Noise)
    (region boundary : V → Prop)
    (settings : ∀ v, region v → plan v = otherPlan v)
    (parents : ∀ v, region v → plan v = none → ∀ p, model.parent p v → region p ∨ boundary p)
    (sources : ∀ v, region v → plan v = none → ∀ u, model.uses u v → noise u = otherNoise u)
    (boundaryValues : ∀ v, boundary v → model.evaluate plan noise v = model.evaluate otherPlan otherNoise v)
    (v : V) (inside : region v) : model.evaluate plan noise v = model.evaluate otherPlan otherNoise v := by
  induction h : model.rank v using Nat.strongRecOn generalizing v with
  | ind n ih =>
    rw [model.solve plan, model.solve otherPlan, ← settings v inside]
    cases cut : plan v with
    | some value => rfl
    | none =>
      apply model.respects_inputs
      · intro p hp
        rcases parents v inside cut p hp with localParent | externalParent
        · exact ih (model.rank p) (h ▸ model.parent_lower hp) p localParent rfl
        · exact boundaryValues p externalParent
      · exact sources v inside cut

/-- Ancestors in the graph after cutting into the intervention targets. -/
inductive Ancestor (model : SCM V Source State Noise) (plan : Plan V State) (reward : V) : V → Prop where
  | reward : Ancestor model plan reward reward
  | parent {p v} : Ancestor model plan reward v → model.parent p v → plan v = none →
      Ancestor model plan reward p

/-- The least descendant-and-bidirected closure of the reward in the cut
ancestral graph. A shared source gives the bidirected step in the expanded graph. -/
inductive Territory (model : SCM V Source State Noise) (plan : Plan V State) (reward : V) : V → Prop where
  | reward : Territory model plan reward reward
  | child {v next} : Territory model plan reward v → Ancestor model plan reward next →
      model.parent v next → plan next = none → Territory model plan reward next
  | shared {v next u} : Territory model plan reward v → Ancestor model plan reward next →
      model.uses u v → model.uses u next → plan next = none → Territory model plan reward next

def Border (model : SCM V Source State Noise) (plan : Plan V State) (reward v : V) : Prop :=
  ¬ Territory model plan reward v ∧ ∃ t, Territory model plan reward t ∧ model.parent v t

abbrev BorderAssignment (model : SCM V Source State Noise) (plan : Plan V State) (reward : V) :=
  {v // Border model plan reward v} → State

private theorem territory_ancestor {model : SCM V Source State Noise} {plan reward v}
    (inside : Territory model plan reward v) : Ancestor model plan reward v := by
  cases inside with
  | reward => exact .reward
  | child _ ancestor _ _ => exact ancestor
  | shared _ ancestor _ _ _ => exact ancestor

private theorem territory_free {model : SCM V Source State Noise} {plan reward v}
    (rewardFree : plan reward = none) (inside : Territory model plan reward v) : plan v = none := by
  cases inside with
  | reward => exact rewardFree
  | child _ _ _ free => exact free
  | shared _ _ _ _ free => exact free

def insideSource (model : SCM V Source State Noise) (plan : Plan V State)
    (reward : V) (u : Source) : Prop :=
  ∃ v, Territory model plan reward v ∧ model.uses u v

/-- Combine the assignments of the independent root sets. Each root keeps
one value shared by all equations using it. -/
noncomputable def combineNoise (model : SCM V Source State Noise) (plan : Plan V State)
    (reward : V) (inside outside : Source → Noise) (u : Source) : Noise := by
  classical
  exact if insideSource model plan reward u then inside u else outside u

noncomputable def naturalBorder (model : SCM V Source State Noise) (plan : Plan V State) (reward : V)
    (insideBase outside : Source → Noise) (v : {v // Border model plan reward v}) : State :=
  model.evaluate plan (combineNoise model plan reward insideBase outside) v.val

/-- The fixed plan intervening on precisely the full border. -/
noncomputable def borderPlan (model : SCM V Source State Noise) (plan : Plan V State)
    (reward : V) (assignment : BorderAssignment model plan reward) (v : V) : Option State := by
  classical
  exact if h : Border model plan reward v then some (assignment ⟨v, h⟩) else none

/-- Given `do(s)`, the natural border depends only on the exterior roots.
This follows from closure in the graph with incoming edges cut at `s`. -/
theorem natural_border_independent_of_inside (model : SCM V Source State Noise)
    (plan : Plan V State) (reward : V) (rewardFree : plan reward = none)
    (inside otherInside outside : Source → Noise) :
    naturalBorder model plan reward inside outside = naturalBorder model plan reward otherInside outside := by
  funext v
  let region := fun w => Ancestor model plan reward w ∧ ¬ Territory model plan reward w
  have onBorder : region v.val := by
    obtain ⟨outsideTerritory, t, insideTerritory, edge⟩ := v.property
    exact ⟨.parent (territory_ancestor insideTerritory) edge (territory_free rewardFree insideTerritory),
      outsideTerritory⟩
  apply evaluate_agrees model plan plan _ _ region (fun _ => False) (fun _ _ => rfl) _ _ _ _ onBorder
  · intro w hw free p hp
    exact Or.inl ⟨.parent hw.1 hp free, fun h => hw.2 (.child h hw.1 hp free)⟩
  · intro w hw free u hu
    have disjoint : ¬ insideSource model plan reward u := by
      rintro ⟨t, ht, use⟩
      exact hw.2 (.shared ht hw.1 use hu free)
    simp [combineNoise, disjoint]
  · exact fun _ h => h.elim

private theorem territory_with_boundary (model : SCM V Source State Noise)
    (plan : Plan V State) (reward : V) (first second : Plan V State)
    (firstFree : ∀ v, Territory model plan reward v → first v = none)
    (secondFree : ∀ v, Territory model plan reward v → second v = none)
    (inside outside otherOutside : Source → Noise)
    (same : ∀ v, Border model plan reward v →
      model.evaluate first (combineNoise model plan reward inside outside) v =
        model.evaluate second (combineNoise model plan reward inside otherOutside) v) :
    model.evaluate first (combineNoise model plan reward inside outside) reward =
      model.evaluate second (combineNoise model plan reward inside otherOutside) reward := by
  classical
  apply evaluate_agrees model first second _ _ (Territory model plan reward) (Border model plan reward)
    (fun v hv => (firstFree v hv).trans (secondFree v hv).symm) _ _ same reward .reward
  · intro v hv _ p hp
    by_cases h : Territory model plan reward p
    · exact Or.inl h
    · exact Or.inr ⟨h, v, hv, hp⟩
  · intro v hv _ u hu
    have used : insideSource model plan reward u := ⟨v, hv, hu⟩
    simp [combineNoise, used]

/-- Fixing the full natural border gives the same reward at each interior
source assignment. This also deletes the other intervention targets. -/
theorem reward_under_natural_border (model : SCM V Source State Noise)
    (plan : Plan V State) (reward : V) (rewardFree : plan reward = none)
    (inside insideBase outside outsideBase : Source → Noise) :
    model.evaluate plan (combineNoise model plan reward inside outside) reward =
      model.evaluate (borderPlan model plan reward (naturalBorder model plan reward insideBase outside))
        (combineNoise model plan reward inside outsideBase) reward := by
  refine territory_with_boundary model plan reward plan _ (fun _ => territory_free rewardFree)
    ?_ inside outside outsideBase ?_
  · intro v hv
    have notBorder : ¬ Border model plan reward v := fun h => h.1 hv
    simp [borderPlan, notBorder]
  · intro v hv
    have same := congrFun
      (natural_border_independent_of_inside model plan reward rewardFree inside insideBase outside) ⟨v, hv⟩
    rw [model.solve (borderPlan model plan reward _)]
    simpa [borderPlan, hv, naturalBorder] using same

private theorem reward_border_independent_of_outside (model : SCM V Source State Noise)
    (plan : Plan V State) (reward : V) (assignment : BorderAssignment model plan reward)
    (inside outside otherOutside : Source → Noise) :
    model.evaluate (borderPlan model plan reward assignment) (combineNoise model plan reward inside outside) reward =
      model.evaluate (borderPlan model plan reward assignment) (combineNoise model plan reward inside otherOutside) reward := by
  have free (v : V) (hv : Territory model plan reward v) : borderPlan model plan reward assignment v = none := by
    have notBorder : ¬ Border model plan reward v := fun h => h.1 hv
    simp [borderPlan, notBorder]
  apply territory_with_boundary model plan reward _ _ free free
  intro v hv
  rw [model.solve _ _ v, model.solve _ _ v]
  simp [borderPlan, hv]

/-- Finite laws with exact probabilities. Each atom occurrence contributes
its mass to the sum. -/
structure FiniteLaw (α : Type) where
  atoms : List α
  mass : α → Rat
  nonnegative : ∀ u ∈ atoms, 0 ≤ mass u
  normalized : (atoms.map mass).sum = 1

def FiniteLaw.mean {α : Type} (law : FiniteLaw α) (value : α → Rat) : Rat :=
  weightedSum law.atoms law.mass value

private theorem mean_constant {α : Type} (law : FiniteLaw α) (value : Rat) :
    law.mean (fun _ => value) = value := by
  rw [FiniteLaw.mean, weightedSum, sum_mul, law.normalized, Rat.one_mul]

private theorem mean_congr {α : Type} (law : FiniteLaw α) {f g : α → Rat}
    (same : ∀ u ∈ law.atoms, f u = g u) : law.mean f = law.mean g := by
  unfold FiniteLaw.mean weightedSum
  exact congrArg List.sum (List.map_congr_left (fun u hu => congrArg (law.mass u * ·) (same u hu)))

def interventionMean (model : SCM V Source State Noise) (joint : FiniteLaw (Source → Noise))
    (reward : V) (rewardValue : State → Rat) (plan : Plan V State) : Rat :=
  joint.mean fun noise => rewardValue (model.evaluate plan noise reward)

/-- Independence of the root groups used inside and outside this territory.
It concerns the joint exogenous law and a fixed partition of the roots. -/
def SourcesFactor (model : SCM V Source State Noise) (plan : Plan V State) (reward : V)
    (joint inside outside : FiniteLaw (Source → Noise)) : Prop :=
  ∀ f : (Source → Noise) → Rat,
    joint.mean f = outside.mean fun u => inside.mean fun v => f (combineNoise model plan reward v u)

/-- Appendix H, Lemma H.1 for finite rational laws. We sum over full border
assignments. Those inconsistent with the fixed values on `S ∩ B` have zero
weight, because the natural border under `do(s)` already fixes them. -/
theorem static_border_mixture (model : SCM V Source State Noise)
    (joint inside outside : FiniteLaw (Source → Noise)) (plan : Plan V State) (reward : V)
    (rewardValue : State → Rat) (rewardFree : plan reward = none)
    (factor : SourcesFactor model plan reward joint inside outside)
    (insideBase outsideBase : Source → Noise) [DecidableEq (BorderAssignment model plan reward)]
    (assignments : List (BorderAssignment model plan reward)) (unique : assignments.Nodup)
    (covers : ∀ u ∈ outside.atoms, naturalBorder model plan reward insideBase u ∈ assignments) :
    let mass := borderMass outside.atoms outside.mass (naturalBorder model plan reward insideBase)
    (∀ b ∈ assignments, 0 ≤ mass b) ∧ (assignments.map mass).sum = 1 ∧
      interventionMean model joint reward rewardValue plan =
        weightedSum assignments mass (fun b =>
          interventionMean model joint reward rewardValue (borderPlan model plan reward b)) := by
  let natural := naturalBorder model plan reward insideBase
  let mass := borderMass outside.atoms outside.mass natural
  let mean := fun b => interventionMean model joint reward rewardValue (borderPlan model plan reward b)
  let localMean := fun b => inside.mean fun i => rewardValue
    (model.evaluate (borderPlan model plan reward b) (combineNoise model plan reward i outsideBase) reward)
  refine ⟨(border_mass_normalized _ _ _ _ unique covers outside.nonnegative outside.normalized).1,
    (border_mass_normalized _ _ _ _ unique covers outside.nonnegative outside.normalized).2, ?_⟩
  have fixed (b : BorderAssignment model plan reward) : mean b = localMean b := by
    unfold mean interventionMean
    rw [factor]
    calc
      _ = outside.mean (fun _ => localMean b) := by
        apply mean_congr
        intro u _
        apply mean_congr
        intro i _
        exact congrArg rewardValue (reward_border_independent_of_outside model plan reward b i u outsideBase)
      _ = _ := mean_constant outside _
  calc
    _ = outside.mean (fun u => inside.mean fun i =>
          rewardValue (model.evaluate plan (combineNoise model plan reward i u) reward)) := factor _
    _ = outside.mean (fun u => localMean (natural u)) := by
      apply mean_congr
      intro u _
      apply mean_congr
      intro i _
      exact congrArg rewardValue (reward_under_natural_border model plan reward rewardFree i insideBase u outsideBase)
    _ = outside.mean (fun u => mean (natural u)) :=
      mean_congr outside (fun u _ => (fixed (natural u)).symm)
    _ = weightedSum assignments mass mean := group_by_border _ _ _ _ unique covers _

/-- Common coordinates in `S ∩ B` retain the values fixed by `s`. -/
theorem natural_border_keeps_fixed_coordinate (model : SCM V Source State Noise)
    (plan : Plan V State) (reward : V) (inside outside : Source → Noise)
    (v : {v // Border model plan reward v}) (value : State) (fixed : plan v.val = some value) :
    naturalBorder model plan reward inside outside v = value := by
  simp [naturalBorder, model.solve plan, fixed]

private theorem ancestor_of_cuts {model : SCM V Source State Noise} {first second : Plan V State}
    {reward v : V} (uncut : ∀ x, first x = none → second x = none)
    (h : Ancestor model first reward v) : Ancestor model second reward v := by
  induction h with
  | reward => exact .reward
  | parent _ edge free ih => exact .parent ih edge (uncut _ free)

private theorem territory_of_cuts {model : SCM V Source State Noise} {first second : Plan V State}
    {reward v : V} (uncut : ∀ x, first x = none → second x = none)
    (h : Territory model first reward v) : Territory model second reward v := by
  induction h with
  | reward => exact .reward
  | child _ ancestor edge free ih => exact .child ih (ancestor_of_cuts uncut ancestor) edge (uncut _ free)
  | shared _ ancestor sourceNext sourceOld free ih =>
    exact .shared ih (ancestor_of_cuts uncut ancestor) sourceNext sourceOld (uncut _ free)

/-- Algorithm 1 needs one representative per target set. The border is
independent of the values assigned to the cut. -/
theorem border_eq_of_same_targets (model : SCM V Source State Noise) (reward : V)
    (first second : Plan V State) (same : ∀ v, first v = none ↔ second v = none) :
    Border model first reward = Border model second reward := by
  have territorySame (v : V) : Territory model first reward v ↔ Territory model second reward v :=
    ⟨territory_of_cuts (fun x => (same x).mp), territory_of_cuts (fun x => (same x).mpr)⟩
  funext v
  exact propext (by simp only [Border, territorySame])

private theorem border_plan_of_cuts (model : SCM V Source State Noise) (reward : V)
    (first second : Plan V State) (same : ∀ v, first v = none ↔ second v = none)
    (assignment : BorderAssignment model first reward) :
    ∃ transferred : BorderAssignment model second reward,
      borderPlan model first reward assignment = borderPlan model second reward transferred := by
  classical
  have eq := border_eq_of_same_targets model reward first second same
  let transferred : BorderAssignment model second reward := fun v => assignment ⟨v.val, eq.symm ▸ v.property⟩
  refine ⟨transferred, ?_⟩
  funext v
  have sameHere : Border model first reward v ↔ Border model second reward v := by rw [eq]
  by_cases member : Border model first reward v
  · simp [borderPlan, member, sameHere.mp member, transferred]
  · have absent : ¬ Border model second reward v := fun h => member (sameHere.mpr h)
    simp [borderPlan, member, absent]

/-- The plans from one iteration for each allowed target support, keeping
all full-domain assignments to its border. Repeated plans may be removed. -/
noncomputable def staticCandidates (model : SCM V Source State Noise) (reward : V)
    (supports : List (Plan V State)) (assignments : ∀ s, List (BorderAssignment model s reward)) :
    List (Plan V State) := supports.flatMap fun s => (assignments s).map (borderPlan model s reward)

private theorem finite_argmax {α : Type} (xs : List α) (value : α → Rat) (nonempty : xs ≠ []) :
    ∃ x ∈ xs, ∀ y ∈ xs, value y ≤ value x := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases tail : xs = []
    · subst xs
      exact ⟨x, by simp, fun y hy => by simpa using (List.mem_singleton.mp hy) ▸ (Rat.le_refl : value x ≤ value x)⟩
    · obtain ⟨best, member, greatest⟩ := ih tail
      rcases Rat.le_total (a := value x) (b := value best) with headLE | tailLE
      · refine ⟨best, by simp [member], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact headLE
        · exact greatest y hy
      · refine ⟨x, by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Rat.le_refl
        · exact Rat.le_trans (greatest y hy) tailLE

/-- Every border setting induces a legal plan on the projected model,
whose only endogenous vertices are the allowed actions and the reward. -/
theorem static_candidates_legal (model : SCM V Source State Noise) (reward : V)
    (allowed : V → State → Prop) (full supports : List (Plan V State))
    (assignments : ∀ s, List (BorderAssignment model s reward))
    (planDomain : ∀ s, s ∈ full ↔ ∀ v a, s v = some a → v ≠ reward ∧ allowed v a)
    (assignmentDomain : ∀ s b, b ∈ assignments s ↔ ∀ v, allowed v.val (b v))
    (candidate : Plan V State) (member : candidate ∈ staticCandidates model reward supports assignments) :
    candidate ∈ full := by
  classical
  obtain ⟨s, _, h⟩ := List.mem_flatMap.mp member
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
  apply (planDomain _).mpr
  intro v a set
  by_cases inBorder : Border model s reward v
  · have equal : b ⟨v, inBorder⟩ = a := by simpa [borderPlan, inBorder] using set
    refine ⟨fun h => inBorder.1 (h ▸ Territory.reward), ?_⟩
    rw [← equal]
    exact (assignmentDomain s b).mp hb ⟨v, inBorder⟩
  · simp [borderPlan, inBorder] at set

/-- Section 7, Theorem 7.1 for finite rational source laws. Every feasible
plan is dominated by an Algorithm 1 candidate. A common maximizer exists
for the full and candidate lists, and the objective can be taken in the
original model if forward projection preserves its value for each plan. -/
theorem fixed_plan_optimal_value_coverage (model : SCM V Source State Noise)
    (joint : FiniteLaw (Source → Noise)) (reward : V) (rewardValue : State → Rat)
    (allowed : V → State → Prop) (full supports : List (Plan V State))
    (assignments : ∀ s, List (BorderAssignment model s reward))
    (planDomain : ∀ s, s ∈ full ↔ ∀ v a, s v = some a → v ≠ reward ∧ allowed v a)
    (assignmentDomain : ∀ s b, b ∈ assignments s ↔ ∀ v, allowed v.val (b v))
    (unique : ∀ s, (assignments s).Nodup)
    (supportCoverage : ∀ s ∈ full, ∃ representative ∈ supports,
      ∀ v, s v = none ↔ representative v = none)
    (statesLegal : ∀ s ∈ full, ∀ noise v, v ≠ reward → allowed v (model.evaluate s noise v))
    (independent : ∀ s ∈ full, ∃ inside outside, SourcesFactor model s reward joint inside outside)
    (noiseBase : Source → Noise) (originalValue : Plan V State → Rat)
    (projection : ∀ s ∈ full, originalValue s = interventionMean model joint reward rewardValue s) :
    (∀ s ∈ full, ∃ candidate ∈ staticCandidates model reward supports assignments,
      originalValue s ≤ originalValue candidate) ∧
    ∃ best ∈ staticCandidates model reward supports assignments, best ∈ full ∧
      (∀ other ∈ staticCandidates model reward supports assignments, originalValue other ≤ originalValue best) ∧
      ∀ s ∈ full, originalValue s ≤ originalValue best := by
  classical
  let candidates := staticCandidates model reward supports assignments
  have legal : ∀ c ∈ candidates, c ∈ full :=
    static_candidates_legal model reward allowed full supports assignments planDomain assignmentDomain
  have dominate (s : Plan V State) (feasible : s ∈ full) :
      ∃ candidate ∈ candidates, originalValue s ≤ originalValue candidate := by
    obtain ⟨inside, outside, factor⟩ := independent s feasible
    have rewardFree : s reward = none := by
      cases cut : s reward with
      | none => rfl
      | some a => exact ((planDomain s).mp feasible reward a cut).1.elim rfl
    have covers (u : Source → Noise) (_ : u ∈ outside.atoms) :
        naturalBorder model s reward noiseBase u ∈ assignments s := by
      apply (assignmentDomain s _).mpr
      intro v
      apply statesLegal s feasible _ v.val
      intro equal
      exact v.property.1 (equal.symm ▸ (Territory.reward : Territory model s reward reward))
    obtain ⟨nonneg, norm, mixture⟩ := static_border_mixture model joint inside outside s reward
      rewardValue rewardFree factor noiseBase noiseBase (assignments s) (unique s) covers
    let projectedMean := interventionMean model joint reward rewardValue
    have assignmentNonempty : assignments s ≠ [] := by
      intro empty
      simp [empty] at norm
    obtain ⟨b, selected, greatest⟩ := finite_argmax (assignments s)
      (fun b => projectedMean (borderPlan model s reward b)) assignmentNonempty
    have bounded : projectedMean s ≤ projectedMean (borderPlan model s reward b) := by
      dsimp only [projectedMean]
      rw [mixture]
      exact weighted_sum_le _ _ _ _ nonneg norm greatest
    obtain ⟨representative, listed, targets⟩ := supportCoverage s feasible
    obtain ⟨transferred, equal⟩ := border_plan_of_cuts model reward s representative targets b
    let candidate := borderPlan model representative reward transferred
    have transferredLegal : transferred ∈ assignments representative := by
      apply (assignmentDomain representative transferred).mpr
      intro v
      have eq := border_eq_of_same_targets model reward s representative targets
      have inBorder : Border model s reward v.val := eq.symm ▸ v.property
      have assignmentsEqual : b ⟨v.val, inBorder⟩ = transferred v := by
        have atV := congrFun equal v.val
        simpa [borderPlan, inBorder, v.property] using atV
      rw [← assignmentsEqual]
      exact (assignmentDomain s b).mp selected ⟨v.val, inBorder⟩
    have included : candidate ∈ candidates := List.mem_flatMap.mpr
      ⟨representative, listed, List.mem_map.mpr ⟨transferred, transferredLegal, rfl⟩⟩
    refine ⟨candidate, included, ?_⟩
    rw [projection s feasible, projection candidate (legal candidate included)]
    dsimp only [candidate]
    rwa [← equal]
  have fullNonempty : full ≠ [] := by
    have member : (fun _ => none) ∈ full := by
      apply (planDomain _).mpr
      intro _ _ h
      contradiction
    intro empty
    simp [empty] at member
  obtain ⟨allBest, feasible, greatest⟩ := finite_argmax full originalValue fullNonempty
  obtain ⟨best, included, superior⟩ := dominate allBest feasible
  refine ⟨dominate, best, included, legal best included, ?_, ?_⟩
  · exact fun c hc => Rat.le_trans (greatest c (legal c hc)) superior
  · exact fun s hs => Rat.le_trans (greatest s hs) superior

/-- A directed parent edge in the latent projection follows a directed
route through removed intermediate vertices. -/
inductive ProjectedParent (model : SCM V Source State Noise) (retain : V → Prop) : V → V → Prop where
  | direct {p v} : model.parent p v → ProjectedParent model retain p v
  | through {p q v} : model.parent p q → ¬ retain q → ProjectedParent model retain q v →
      ProjectedParent model retain p v

/-- The projected structural equation retains a root input if directly
used or transmitted entirely through removed endogenous vertices. -/
inductive ProjectedUse (model : SCM V Source State Noise) (retain : V → Prop) : Source → V → Prop where
  | direct {u v} : model.uses u v → ProjectedUse model retain u v
  | through {u q v} : model.uses u q → ¬ retain q → ProjectedParent model retain q v →
      ProjectedUse model retain u v

theorem projected_parent_lower {model : SCM V Source State Noise} {retain : V → Prop}
    {p v : V} (edge : ProjectedParent model retain p v) : model.rank p < model.rank v := by
  induction edge with
  | direct edge => exact model.parent_lower edge
  | through edge _ _ ih => exact Nat.lt_trans (model.parent_lower edge) ih

def extendPlan (retain : V → Prop) [DecidablePred retain] (plan : Plan {v // retain v} State) : Plan V State :=
  fun v => if h : retain v then plan ⟨v, h⟩ else none

/-- Evaluate a removed variable by unfolding its parents to bounded depth,
using supplied values as soon as a retained variable is reached. The bound
in a projected equation is its rank, which exceeds each parent's rank. -/
def substitute (model : SCM V Source State Noise) (retain : V → Prop) [DecidablePred retain]
    (values : {v // retain v} → State) (noise : Source → Noise) (fallback : V → State) : Nat → V → State
  | 0 => fallback
  | n + 1 => fun v =>
    if h : retain v then values ⟨v, h⟩ else model.law v (substitute model retain values noise fallback n) noise

private theorem substitute_agrees (model : SCM V Source State Noise) (retain : V → Prop)
    [DecidablePred retain] (left right : {v // retain v} → State) (noise other : Source → Noise)
    (fallback : V → State) (v : V)
    (inputs : ∀ p : {w // retain w}, ProjectedParent model retain p.val v → left p = right p)
    (sources : ∀ u, ProjectedUse model retain u v → noise u = other u)
    (depth : Nat) (p : V) (route : ProjectedParent model retain p v) :
    substitute model retain left noise fallback depth p = substitute model retain right other fallback depth p := by
  induction depth generalizing p with
  | zero => rfl
  | succ n ih =>
    by_cases kept : retain p
    · simpa [substitute, kept] using inputs ⟨p, kept⟩ route
    · simp only [substitute, dite_eq_right kept]
      apply model.respects_inputs
      · intro q edge
        exact ih q (.through edge kept route)
      · intro u used
        exact sources u (.through used kept route)

private theorem substitute_extends_evaluation (model : SCM V Source State Noise) (retain : V → Prop)
    [DecidablePred retain] (plan : Plan {v // retain v} State) (noise : Source → Noise) (fallback : V → State)
    (depth : Nat) (p : V) (deep : model.rank p < depth) :
    substitute model retain (fun v => model.evaluate (extendPlan retain plan) noise v.val) noise fallback depth p =
      model.evaluate (extendPlan retain plan) noise p := by
  induction depth generalizing p with
  | zero => omega
  | succ n ih =>
    by_cases kept : retain p
    · simp [substitute, kept]
    · simp only [substitute, dite_eq_right kept]
      rw [model.solve (extendPlan retain plan) noise p]
      simp only [extendPlan, dite_eq_right kept, Option.getD_none]
      apply model.respects_inputs
      · intro q edge
        exact ih q (Nat.lt_of_lt_of_le (model.parent_lower edge) (Nat.le_of_lt_succ deep))
      · intro _ _
        rfl

/-- Build the projected SCM by substituting removed equations, retaining
the original roots, including instance-wise sharing. -/
def project (model : SCM V Source State Noise) (retain : V → Prop) [DecidablePred retain]
    (fallback : V → State) : SCM {v // retain v} Source State Noise where
  rank := fun v => model.rank v.val
  parent := fun p v => ProjectedParent model retain p.val v.val
  uses := fun u v => ProjectedUse model retain u v.val
  parent_lower := projected_parent_lower
  law := fun v values noise => model.law v.val
    (substitute model retain values noise fallback (model.rank v.val)) noise
  evaluate := fun plan noise v => model.evaluate (extendPlan retain plan) noise v.val
  solve := by
    intro plan noise v
    rw [model.solve (extendPlan retain plan) noise v.val]
    have onRetained : extendPlan retain plan v.val = plan v := by
      simp [extendPlan, v.property]
    rw [onRetained]
    congr 1
    apply model.respects_inputs
    · intro p edge
      exact (substitute_extends_evaluation model retain plan noise fallback (model.rank v.val) p
        (model.parent_lower edge)).symm
    · intro _ _
      rfl
  respects_inputs := by
    intro v left right noise other inputs sources
    apply model.respects_inputs
    · intro p edge
      exact substitute_agrees model retain left right noise other fallback v.val inputs sources
        (model.rank v.val) p (.direct edge)
    · intro u used
      exact sources u (.direct used)

/-- Appendix H forward preservation and Appendix J.1, Proposition J.1.
Given the same root assignment, every retained outcome is preserved under
every plan on retained vertices. The projected equations are obtained by
substitution as checked by the `solve` field of `project`. -/
theorem project_preserves_intervention (model : SCM V Source State Noise) (retain : V → Prop)
    [DecidablePred retain] (fallback : V → State) (plan : Plan {v // retain v} State)
    (noise : Source → Noise) (v : {v // retain v}) :
    (project model retain fallback).evaluate plan noise v = model.evaluate (extendPlan retain plan) noise v.val :=
  rfl

/-- Embed the original vertices as `some v` and give the new aggregate
sink the vertex `none`. Its parents are the listed time-specific rewards. -/
inductive AggregateParent (parent : V → V → Prop) (rewards : List V) : Option V → Option V → Prop where
  | original {u v} : parent u v → AggregateParent parent rewards (some u) (some v)
  | reward {v} : v ∈ rewards → AggregateParent parent rewards (some v) none

def originalState (fallback : State) : State ⊕ Rat → State
  | .inl value => value
  | .inr _ => fallback

def aggregateState : State ⊕ Rat → Rat
  | .inl _ => 0
  | .inr value => value

def originalPlan (fallback : V → State) (plan : Plan (Option V) (State ⊕ Rat)) : Plan V State :=
  fun v => (plan (some v)).map (originalState (fallback v))

def sumRewards (rewards : List V) (value : State → Rat) (states : V → State) : Rat :=
  (rewards.map fun v => value (states v)).sum

def evaluateAggregate (model : SCM V Source State Noise) (fallback : V → State)
    (rewards : List V) (value : State → Rat) (plan : Plan (Option V) (State ⊕ Rat))
    (noise : Source → Noise) (vertex : Option V) : State ⊕ Rat :=
  (plan vertex).getD (match vertex with
    | some v => Sum.inl (model.evaluate (originalPlan fallback plan) noise v)
    | none => Sum.inr (sumRewards rewards value (model.evaluate (originalPlan fallback plan) noise)))

theorem original_state_of_aggregate_evaluation (model : SCM V Source State Noise)
    (fallback : V → State) (rewards : List V) (value : State → Rat)
    (plan : Plan (Option V) (State ⊕ Rat)) (noise : Source → Noise) (v : V) :
    originalState (fallback v) (evaluateAggregate model fallback rewards value plan noise (some v)) =
      model.evaluate (originalPlan fallback plan) noise v := by
  cases cut : plan (some v) with
  | none => simp [evaluateAggregate, originalState, cut]
  | some a => simp [evaluateAggregate, model.solve (originalPlan fallback plan) noise v, originalPlan, cut]

/-- Augment the original ranked model with the exact sum of the rewards.
The full `SCM` interface also handles arbitrary hypothetical settings of
the enlarged state type. Legal fixed plans set only original states on
action vertices and leave the aggregate sink and every original reward free. -/
def augment (model : SCM V Source State Noise) (fallback : V → State)
    (rewards : List V) (value : State → Rat) (sinkRank : Nat) (bounded : ∀ v, model.rank v < sinkRank) :
    SCM (Option V) Source (State ⊕ Rat) Noise where
  rank := fun v => v.elim sinkRank model.rank
  parent := AggregateParent model.parent rewards
  uses := fun u v => v.elim False (model.uses u)
  parent_lower := by
    intro p v h
    cases h with
    | original edge => exact model.parent_lower edge
    | reward _ => exact bounded _
  law := fun v states noise =>
    let originals := fun w => originalState (fallback w) (states (some w))
    match v with
    | some w => .inl (model.law w originals noise)
    | none => .inr (sumRewards rewards value originals)
  evaluate := evaluateAggregate model fallback rewards value
  solve := by
    intro plan noise v
    have originals :
        (fun w => originalState (fallback w) (evaluateAggregate model fallback rewards value plan noise (some w))) =
          model.evaluate (originalPlan fallback plan) noise :=
      funext (original_state_of_aggregate_evaluation model fallback rewards value plan noise)
    cases v with
    | none =>
      change (plan none).getD (Sum.inr (sumRewards rewards value (model.evaluate (originalPlan fallback plan) noise))) =
        (plan none).getD (Sum.inr (sumRewards rewards value (fun w =>
          originalState (fallback w) (evaluateAggregate model fallback rewards value plan noise (some w)))))
      rw [originals]
    | some v =>
      change (plan (some v)).getD (Sum.inl (model.evaluate (originalPlan fallback plan) noise v)) =
        (plan (some v)).getD (Sum.inl (model.law v (fun w =>
          originalState (fallback w) (evaluateAggregate model fallback rewards value plan noise (some w))) noise))
      rw [originals]
      cases cut : plan (some v) with
      | some a => rfl
      | none =>
        have law := model.solve (originalPlan fallback plan) noise v
        have uncut : originalPlan fallback plan v = none := by simp [originalPlan, cut]
        rw [uncut] at law
        exact congrArg Sum.inl law
  respects_inputs := by
    intro v left right noise other inputs sources
    cases v with
    | none =>
      change Sum.inr (sumRewards rewards value (fun w => originalState (fallback w) (left (some w)))) =
        Sum.inr (sumRewards rewards value (fun w => originalState (fallback w) (right (some w))))
      apply congrArg Sum.inr
      unfold sumRewards
      apply congrArg List.sum
      apply List.map_congr_left
      intro w hw
      dsimp only
      rw [inputs (some w) (.reward hw)]
    | some v =>
      change Sum.inl (model.law v (fun w => originalState (fallback w) (left (some w))) noise) =
        Sum.inl (model.law v (fun w => originalState (fallback w) (right (some w))) other)
      apply congrArg Sum.inl
      apply model.respects_inputs
      · intro p hp
        rw [inputs (some p) (.original hp)]
      · exact sources

/-- For retained interventions, evaluating the projected aggregate sink
gives the sum of the original time-specific outcomes at the same root
assignment. The projection and aggregate both use the original root law. -/
theorem projected_aggregate_value (model : SCM V Source State Noise) (fallback : V → State)
    (rewards : List V) (value : State → Rat) (sinkRank : Nat) (bounded : ∀ v, model.rank v < sinkRank)
    (retain : Option V → Prop) [DecidablePred retain] (keepsSink : retain none)
    (projectFallback : Option V → State ⊕ Rat) (plan : Plan {v // retain v} (State ⊕ Rat))
    (sinkFree : plan ⟨none, keepsSink⟩ = none) (noise : Source → Noise) :
    aggregateState ((project (augment model fallback rewards value sinkRank bounded) retain projectFallback).evaluate
      plan noise ⟨none, keepsSink⟩) =
      sumRewards rewards value (model.evaluate (originalPlan fallback (extendPlan retain plan)) noise) := by
  rw [project_preserves_intervention]
  simp [augment, evaluateAggregate, extendPlan, keepsSink, sinkFree, aggregateState]

/-- The expected sum follows pointwise under the same finite joint law.
This discharges the projection premise of the coverage theorem for the
projected aggregate construction. -/
theorem projected_aggregate_mean (model : SCM V Source State Noise) (fallback : V → State)
    (rewards : List V) (value : State → Rat) (sinkRank : Nat) (bounded : ∀ v, model.rank v < sinkRank)
    (retain : Option V → Prop) [DecidablePred retain] (keepsSink : retain none)
    (projectFallback : Option V → State ⊕ Rat) (plan : Plan {v // retain v} (State ⊕ Rat))
    (sinkFree : plan ⟨none, keepsSink⟩ = none) (joint : FiniteLaw (Source → Noise)) :
    interventionMean (project (augment model fallback rewards value sinkRank bounded) retain projectFallback)
      joint ⟨none, keepsSink⟩ aggregateState plan =
      joint.mean (fun noise => sumRewards rewards value
        (model.evaluate (originalPlan fallback (extendPlan retain plan)) noise)) := by
  apply mean_congr
  intro noise _
  exact projected_aggregate_value model fallback rewards value sinkRank bounded retain keepsSink
    projectFallback plan sinkFree noise

/-- The finite rational version of Theorem 7.1 for the constructed static
projection. The graph supplies one cut representative per allowed support.
The candidate list attains the original cumulative objective's maximum. -/
theorem aggregate_optimal_value_coverage (model : SCM V Source State Noise) (fallback : V → State)
    (rewards : List V) (value : State → Rat) (sinkRank : Nat) (bounded : ∀ v, model.rank v < sinkRank)
    (retain : Option V → Prop) [DecidablePred retain] (keepsSink : retain none)
    (projectFallback : Option V → State ⊕ Rat) (joint : FiniteLaw (Source → Noise))
    (noiseBase : Source → Noise) :
    let projected := project (augment model fallback rewards value sinkRank bounded) retain projectFallback
    let sink : {v // retain v} := ⟨none, keepsSink⟩
    ∀ (allowed : {v // retain v} → State ⊕ Rat → Prop)
      (full supports : List (Plan {v // retain v} (State ⊕ Rat)))
      (assignments : ∀ s, List (BorderAssignment projected s sink)),
      (∀ s, s ∈ full ↔ ∀ v a, s v = some a → v ≠ sink ∧ allowed v a) →
      (∀ s b, b ∈ assignments s ↔ ∀ v, allowed v.val (b v)) →
      (∀ s, (assignments s).Nodup) →
      (∀ s ∈ full, ∃ representative ∈ supports, ∀ v, s v = none ↔ representative v = none) →
      (∀ s ∈ full, ∀ noise v, v ≠ sink → allowed v (projected.evaluate s noise v)) →
      (∀ s ∈ full, ∃ inside outside, SourcesFactor projected s sink joint inside outside) →
      let candidates := staticCandidates projected sink supports assignments
      let originalValue := fun s => joint.mean fun noise =>
        sumRewards rewards value (model.evaluate (originalPlan fallback (extendPlan retain s)) noise)
      (∀ s ∈ full, ∃ candidate ∈ candidates, originalValue s ≤ originalValue candidate) ∧
      ∃ best ∈ candidates, best ∈ full ∧
        (∀ candidate ∈ candidates, originalValue candidate ≤ originalValue best) ∧
        ∀ s ∈ full, originalValue s ≤ originalValue best := by
  dsimp only
  intro allowed full supports assignments planDomain assignmentDomain unique supportCoverage statesLegal independent
  refine fixed_plan_optimal_value_coverage _ joint _ aggregateState allowed full supports assignments
    planDomain assignmentDomain unique supportCoverage statesLegal independent noiseBase _ ?_
  intro s member
  have sinkFree : s ⟨none, keepsSink⟩ = none := by
    cases hs : s ⟨none, keepsSink⟩ with
    | none => rfl
    | some b => exact ((planDomain s).mp member _ b hs).1.elim rfl
  exact (projected_aggregate_mean model fallback rewards value sinkRank bounded retain keepsSink
    projectFallback s sinkFree joint).symm

end
end OpenCausalScience.Papers.KwonEtAl2025.AggregateReward
