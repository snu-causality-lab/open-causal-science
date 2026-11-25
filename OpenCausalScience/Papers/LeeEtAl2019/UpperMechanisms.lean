module
public import OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse

/-! # Upper structural equations in the July 2022 g-identifiability erratum

Equation (A.2) of [R-46e](https://causalai.net/r46e.pdf) evaluates one Boolean
coordinate per upper vertex within each indexed hedge. A vertex's directed
successor either stays in the upper forest or enters the common bottom. An
internal confounder joins two upper vertices, while a crossing confounder has
one upper and one bottom endpoint. One chosen frontier is negated when the
crossing and frontier counts agree modulo two.

For a supplied regime, a fixed root or one hedge with every upper equation
untouched suffices for agreement of the bottom laws. The result states this
as an explicit premise for the finite model.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.UpperMechanisms

@[expose] public section

open GeneralIdentifiabilityErratum CorrectedConverse

structure UpperHedge (tops internal crossings roots : Nat) where
  child : Fin tops → Option (Fin tops)
  frontierRoot : Fin tops → Fin roots
  internalEdges : Bottom tops internal
  crossingTop : Fin crossings → Fin tops
  crossingRoot : Fin crossings → Fin roots
  selected : Fin tops
  selected_is_frontier : child selected = none

variable {tops internal crossings roots : Nat}

def UpperHedge.frontiers (g : UpperHedge tops internal crossings roots) : List (Fin tops) :=
  (List.finRange tops).filter fun v => (g.child v).isNone

def UpperHedge.negated (g : UpperHedge tops internal crossings roots) (v : Fin tops) : Bool :=
  decide (v = g.selected) && (countParity crossings == countParity g.frontiers.length)

structure UpperWorld (tops internal crossings : Nat) where
  values : Fin tops → Bool
  internalBits : BitVec internal
  crossingBits : Fin crossings → Bool

def UpperHedge.parentParity (g : UpperHedge tops internal crossings roots)
    (values : Fin tops → Bool) (v : Fin tops) : Bool :=
  xorAll ((List.finRange tops).map fun p => decide (g.child p = some v) && values p)

def UpperHedge.crossingParity (g : UpperHedge tops internal crossings roots)
    (bits : Fin crossings → Bool) (v : Fin tops) : Bool :=
  xorAll ((List.finRange crossings).map fun e => decide (v = g.crossingTop e) && bits e)

def UpperHedge.rhs (g : UpperHedge tops internal crossings roots)
    (world : UpperWorld tops internal crossings) (v : Fin tops) : Bool :=
  Bool.xor (g.parentParity world.values v)
    (Bool.xor (bottomParity g.internalEdges world.internalBits v)
      (g.crossingParity world.crossingBits v))

/-- Under an intervention the imposed coordinate replaces its whole equation. -/
def UpperHedge.Satisfies (g : UpperHedge tops internal crossings roots)
    (fixed : Fin tops → Option Bool) (world : UpperWorld tops internal crossings) : Prop :=
  ∀ v, world.values v = (fixed v).getD (Bool.xor (g.rhs world v) (g.negated v))

def UpperHedge.rootInputs (g : UpperHedge tops internal crossings roots)
    (world : UpperWorld tops internal crossings) : GateInputs roots where
  frontiers r := (g.frontiers.filter fun t => g.frontierRoot t == r).map world.values
  crossing r := ((List.finRange crossings).filter fun e => g.crossingRoot e == r).map
    world.crossingBits

private theorem xor_map_xor {α : Type} (xs : List α) (f h : α → Bool) :
    xorAll (xs.map fun x => Bool.xor (f x) (h x)) =
      Bool.xor (xorAll (xs.map f)) (xorAll (xs.map h)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, xorAll, ih, Bool.xor_assoc]
    exact congrArg (Bool.xor (f x)) (Bool.xor_left_comm _ _ _)

private theorem xor_const_false {α : Type} (xs : List α) :
    xorAll (xs.map fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, xorAll, Bool.false_xor, ih]

private theorem xor_transpose {α β : Type} (xs : List α) (ys : List β) (f : α → β → Bool) :
    xorAll (xs.map fun x => xorAll (ys.map (f x))) =
      xorAll (ys.map fun y => xorAll (xs.map fun x => f x y)) := by
  induction xs with
  | nil => simpa only [List.map_nil, xorAll] using (xor_const_false ys).symm
  | cons x xs ih => simp only [List.map_cons, xorAll, ih, xor_map_xor]

private theorem xor_one {α : Type} [DecidableEq α] (xs : List α) (a : α)
    (unique : xs.Nodup) (value : Bool) :
    xorAll (xs.map fun x => decide (x = a) && value) = (decide (a ∈ xs) && value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨notMem, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases equal : x = a
    · subst x
      simp [xorAll, ih tailUnique, notMem]
    · simp [xorAll, ih tailUnique, equal, Ne.symm equal]

private theorem xor_filter {α : Type} (xs : List α) (p f : α → Bool) :
    xorAll (xs.map fun x => p x && f x) = xorAll ((xs.filter p).map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [xorAll, h, ih]

private theorem xor_partition {α : Type} (xs : List α) (p f : α → Bool) :
    xorAll (xs.map f) = Bool.xor (xorAll ((xs.filter p).map f))
      (xorAll ((xs.filter fun x => !p x).map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [xorAll, h, ih, Bool.xor_left_comm]

private theorem xor_parent_parity (g : UpperHedge tops internal crossings roots)
    (values : Fin tops → Bool) :
    xorAll ((List.finRange tops).map (g.parentParity values)) =
      xorAll (((List.finRange tops).filter fun v => !(g.child v).isNone).map values) := by
  unfold UpperHedge.parentParity
  rw [xor_transpose, ← xor_filter]
  apply congrArg xorAll
  apply List.map_congr_left
  intro p _
  cases g.child p with
  | none => simp [xor_const_false]
  | some c =>
    simp only [Option.some.injEq, Option.isNone_some, Bool.not_false, Bool.true_and]
    simpa only [List.mem_finRange, decide_true, Bool.true_and, eq_comm] using
      xor_one (List.finRange tops) c (List.nodup_finRange _) (values p)

private theorem xor_internal_parity (g : UpperHedge tops internal crossings roots)
    (bits : BitVec internal) :
    xorAll ((List.finRange tops).map (bottomParity g.internalEdges bits)) = false := by
  unfold bottomParity
  rw [xor_transpose]
  apply (congrArg xorAll (List.map_congr_left (g := fun _ => false) ?_)).trans
    (xor_const_false _)
  intro e _
  simp only [incident, Bool.and_xor_distrib_right, xor_map_xor]
  rw [xor_one _ _ (List.nodup_finRange _), xor_one _ _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

private theorem xor_crossing_parity (g : UpperHedge tops internal crossings roots)
    (bits : Fin crossings → Bool) :
    xorAll ((List.finRange tops).map (g.crossingParity bits)) =
      xorAll ((List.finRange crossings).map bits) := by
  unfold UpperHedge.crossingParity
  rw [xor_transpose]
  apply congrArg xorAll
  apply List.map_congr_left
  intro e _
  simpa only [List.mem_finRange, decide_true, Bool.true_and] using
    xor_one (List.finRange tops) (g.crossingTop e) (List.nodup_finRange _) (bits e)

/-- Summing the untouched upper equations cancels each
nonfrontier value and both incidences of every internal UC. The remaining
terms are the corrected frontier parity and the crossing parity. -/
theorem intact_frontier_parity (g : UpperHedge tops internal crossings roots)
    (world : UpperWorld tops internal crossings) (law : g.Satisfies (fun _ => none) world) :
    xorAll (g.frontiers.map world.values) =
      Bool.xor (xorAll ((List.finRange crossings).map world.crossingBits))
        (countParity crossings == countParity g.frontiers.length) := by
  let other := ((List.finRange tops).filter fun v => !(g.child v).isNone).map world.values
  have split : xorAll ((List.finRange tops).map world.values) =
      Bool.xor (xorAll (g.frontiers.map world.values)) (xorAll other) :=
    xor_partition _ _ _
  have equations : (List.finRange tops).map world.values =
      (List.finRange tops).map (fun v => Bool.xor (g.rhs world v) (g.negated v)) :=
    List.map_congr_left fun v _ => law v
  have correction : xorAll ((List.finRange tops).map g.negated) =
      (countParity crossings == countParity g.frontiers.length) := by
    change xorAll ((List.finRange tops).map (fun v =>
      decide (v = g.selected) && (countParity crossings == countParity g.frontiers.length))) = _
    simpa only [List.mem_finRange, decide_true, Bool.true_and] using
      xor_one (List.finRange tops) g.selected (List.nodup_finRange _)
        (countParity crossings == countParity g.frontiers.length)
  rw [equations, xor_map_xor, correction] at split
  change Bool.xor (xorAll ((List.finRange tops).map fun v =>
    Bool.xor (g.parentParity world.values v)
      (Bool.xor (bottomParity g.internalEdges world.internalBits v)
        (g.crossingParity world.crossingBits v)))) _ = _ at split
  simp only [xor_map_xor, xor_parent_parity, xor_internal_parity,
    xor_crossing_parity, Bool.false_xor] at split
  have cancel (remaining crossing negation frontier : Bool)
      (h : Bool.xor (Bool.xor remaining crossing) negation = Bool.xor frontier remaining) :
      frontier = Bool.xor crossing negation := by
    cases remaining <;> cases crossing <;> cases negation <;> cases frontier <;> simp_all
  exact cancel (xorAll other) _ _ _ split

private theorem xor_true_of_all (xs : List Bool) (all : xs.all id = true) :
    xorAll xs = countParity xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, id_eq, Bool.and_eq_true] at all
    simp only [xorAll, all.1, Bool.true_xor, List.length_cons, countParity, ih all.2]

/-- All root inputs from this hedge could be enabled only if every crossing
and every frontier were one. Their parity with the R-46e negation rules it out. -/
theorem intact_hedge_disables_root (g : UpperHedge tops internal crossings roots)
    (world : UpperWorld tops internal crossings) (law : g.Satisfies (fun _ => none) world) :
    ∃ r, (g.rootInputs world).enabled r = false := by
  classical
  by_cases disabled : ∃ r, (g.rootInputs world).enabled r = false
  · exact disabled
  exfalso
  have all (r : Fin roots) : (g.rootInputs world).enabled r = true := by
    cases h : (g.rootInputs world).enabled r with
    | false => exact False.elim (disabled ⟨r, h⟩)
    | true => rfl
  have frontiers : (g.frontiers.map world.values).all id = true := by
    apply List.all_eq_true.mpr
    intro b mem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp mem
    have atRoot := (Bool.and_eq_true_iff.mp (all (g.frontierRoot t))).1
    apply List.all_eq_true.mp atRoot
    exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨ht, by simp⟩, rfl⟩
  have crossingsTrue : ((List.finRange crossings).map world.crossingBits).all id = true := by
    apply List.all_eq_true.mpr
    intro b mem
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp mem
    have atRoot := (Bool.and_eq_true_iff.mp (all (g.crossingRoot e))).2
    apply List.all_eq_true.mp atRoot
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp⟩, rfl⟩
  have parity := intact_frontier_parity g world law
  rw [xor_true_of_all _ frontiers, xor_true_of_all _ crossingsTrue,
    List.length_map, List.length_map, List.length_finRange] at parity
  have impossible (f c : Bool) : f ≠ Bool.xor c (c == f) := by
    cases f <;> cases c <;> decide
  exact impossible _ _ parity

def mergeRootInputs (inputs : List (GateInputs roots)) : GateInputs roots where
  frontiers r := inputs.flatMap fun inputs => inputs.frontiers r
  crossing r := inputs.flatMap fun inputs => inputs.crossing r

theorem merged_enabled_iff (inputs : List (GateInputs roots)) (r : Fin roots) :
    (mergeRootInputs inputs).enabled r = true ↔ ∀ input ∈ inputs, input.enabled r = true := by
  induction inputs with
  | nil => simp [mergeRootInputs, GateInputs.enabled]
  | cons x xs ih =>
    simp only [mergeRootInputs, GateInputs.enabled, List.flatMap_cons, List.all_append,
      Bool.and_eq_true, List.forall_mem_cons] at ih ⊢
    rw [← ih]
    grind

/-- For each available experiment, a root intervention or one untouched
hedge suffices. Each hedge is evaluated according to the
structural equations of its own coordinates in the upper world. -/
theorem supplied_agreement_from_untouched_hedge {Context : Type}
    {bottomEdges : Nat} (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (connected : ∀ r, Walk bottom r distinguished) (fixed : Fin roots → Option Bool)
    (inputs : Context → List (GateInputs roots)) (contexts : List Context) (keep flip : Nat)
    (offered : (∃ r, fixed r ≠ none) ∨
      ∃ (n e c : Nat) (g : UpperHedge n e c roots) (world : Context → UpperWorld n e c),
        (∀ ctx ∈ contexts, g.Satisfies (fun _ => none) (world ctx)) ∧
        (∀ ctx ∈ contexts, g.rootInputs (world ctx) ∈ inputs ctx)) :
    noisyRootMixture bottom distinguished false fixed
        (fun ctx => (mergeRootInputs (inputs ctx)).enabled) contexts keep flip =
      noisyRootMixture bottom distinguished true fixed
        (fun ctx => (mergeRootInputs (inputs ctx)).enabled) contexts keep flip := by
  apply supplied_slice_agreement bottom distinguished connected
  intro ctx mem
  rcases offered with ⟨r, intervened⟩ | ⟨_, _, _, g, world, law, contained⟩
  · exact ⟨r, Or.inl intervened⟩
  obtain ⟨r, off⟩ := intact_hedge_disables_root g (world ctx) (law ctx mem)
  refine ⟨r, Or.inr ?_⟩
  cases h : (mergeRootInputs (inputs ctx)).enabled r with
  | false => rfl
  | true =>
    have on := (merged_enabled_iff _ _).mp h _ (contained ctx mem)
    simp [off] at on

/-- Evaluate the upper equations from the earlier vertices in a topological
ranking of this directed forest. -/
def UpperHedge.evaluate (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) (internalBits : BitVec internal)
    (crossingBits : Fin crossings → Bool) (v : Fin tops) : Bool :=
  (fixed v).getD (Bool.xor (Bool.xor
    (xorAll ((List.finRange tops).map fun p => if _h : g.child p = some v then
      g.evaluate rank ranks fixed internalBits crossingBits p else false))
    (Bool.xor (bottomParity g.internalEdges internalBits v) (g.crossingParity crossingBits v)))
    (g.negated v))
termination_by rank v
decreasing_by exact ranks _ _ _h

theorem evaluated_world_satisfies (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) (internalBits : BitVec internal)
    (crossingBits : Fin crossings → Bool) :
    g.Satisfies fixed ⟨g.evaluate rank ranks fixed internalBits crossingBits,
      internalBits, crossingBits⟩ := by
  intro v
  change g.evaluate rank ranks fixed internalBits crossingBits v = _
  rw [UpperHedge.evaluate]
  simp only [dite_eq_ite]
  have parents : ((List.finRange tops).map fun p => if g.child p = some v then
        g.evaluate rank ranks fixed internalBits crossingBits p else false) =
      ((List.finRange tops).map fun p => decide (g.child p = some v) &&
        g.evaluate rank ranks fixed internalBits crossingBits p) := by
    apply List.map_congr_left
    intro p _
    by_cases h : g.child p = some v <;> simp [h]
  rw [parents]
  rfl

end

end OpenCausalScience.Papers.LeeEtAl2019.UpperMechanisms
