module
public import OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse

/-! # The upper forest of a hedge in the g-identifiability converse

R-46, Definitions 5–6 and §3.1, and R-46e, equations (A.1)–(A.2).
One hedge has one Boolean coordinate per upper vertex. The unique directed
successor of each upper vertex either stays in the upper forest or enters
the common bottom. Each internal UC is incident to two upper vertices.
Each crossing UC has one upper and one bottom endpoint.

For a supplied experiment avoiding the bottom, Definition 6 supplies an
entire hedge disjoint from the intervened vertices. The parity argument
below uses that entire hedge.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.UpperHedgelets

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

/-- R-46 Lemma 2. Summing the untouched upper equations cancels each
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
hedge of Definition 6 suffices. Each hedge is evaluated according to the
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

private theorem parent_parity_xor (g : UpperHedge tops internal crossings roots)
    (a b : Fin tops → Bool) (v : Fin tops) :
    g.parentParity (fun p => Bool.xor (a p) (b p)) v =
      Bool.xor (g.parentParity a v) (g.parentParity b v) := by
  simp only [UpperHedge.parentParity, Bool.and_xor_distrib_left, xor_map_xor]

private theorem parent_parity_single (g : UpperHedge tops internal crossings roots)
    (p v : Fin tops) :
    g.parentParity (fun q => decide (q = p)) v = decide (g.child p = some v) := by
  unfold UpperHedge.parentParity
  rw [show (List.finRange tops).map (fun q => decide (g.child q = some v) && decide (q = p)) =
        (List.finRange tops).map (fun q => decide (q = p) && decide (g.child p = some v)) by
    apply List.map_congr_left
    intro q _
    by_cases h : q = p <;> simp [h]]
  rw [xor_one _ _ (List.nodup_finRange _)]
  simp

/-- A directed path within the upper forest from a vertex to the first
intervened vertex. The length may be zero. -/
inductive ReachesIntervention (g : UpperHedge tops internal crossings roots)
    (fixed : Fin tops → Option Bool) : Fin tops → Prop
  | fixed {v} : fixed v ≠ none → ReachesIntervention g fixed v
  | next {p q} : fixed p = none → g.child p = some q → ReachesIntervention g fixed q →
      ReachesIntervention g fixed p

/-- The part of a directed descendant path in Definition 5 which stays above
the bottom. -/
inductive DirectedPath (g : UpperHedge tops internal crossings roots) : Fin tops → Fin tops → Prop
  | refl (v) : DirectedPath g v v
  | next {p q v} : g.child p = some q → DirectedPath g q v → DirectedPath g p v

theorem reaches_intervention_of_descendant (g : UpperHedge tops internal crossings roots)
    (fixed : Fin tops → Option Bool) {p v : Fin tops} (path : DirectedPath g p v)
    (intervened : fixed v ≠ none) : ReachesIntervention g fixed p := by
  induction path with
  | refl _ => exact .fixed intervened
  | @next p q _ edge _ ih =>
    by_cases free : fixed p = none
    · exact .next free edge (ih intervened)
    · exact .fixed free

/-- A unit change at the start of this path propagates only as far as the
first replaced equation, without changing any frontier or fixed value. -/
theorem directed_path_mask (g : UpperHedge tops internal crossings roots)
    (fixed : Fin tops → Option Bool) {p : Fin tops} (path : ReachesIntervention g fixed p) :
    ∃ mask : Fin tops → Bool,
      (∀ v, fixed v ≠ none → mask v = false) ∧
      (∀ v, g.child v = none → mask v = false) ∧
      (∀ v, fixed v = none → mask v = Bool.xor (g.parentParity mask v) (decide (v = p))) := by
  induction path with
  | @fixed p hp =>
    refine ⟨fun _ => false, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    intro v hv
    have ne : v ≠ p := fun eq => hp (eq ▸ hv)
    simp [UpperHedge.parentParity, xor_const_false, ne]
  | @next p q free edge _ ih =>
    obtain ⟨mask, maskFixed, maskFrontier, propagate⟩ := ih
    refine ⟨fun v => Bool.xor (decide (v = p)) (mask v), ?_, ?_, ?_⟩
    · intro v hv
      have ne : v ≠ p := fun eq => hv (eq ▸ free)
      simp [ne, maskFixed v hv]
    · intro v hv
      have ne : v ≠ p := by
        intro eq
        subst v
        simp [edge] at hv
      simp [ne, maskFrontier v hv]
    · intro v hv
      change Bool.xor (decide (v = p)) (mask v) = _
      rw [parent_parity_xor, parent_parity_single, edge, propagate v hv]
      simp [eq_comm, Bool.xor_comm]

private theorem internal_parity_xor (g : Bottom tops internal) (a b : BitVec internal)
    (v : Fin tops) :
    bottomParity g (a ^^^ b) v = Bool.xor (bottomParity g a v) (bottomParity g b v) := by
  simp only [bottomParity, BitVec.getLsbD_xor, Bool.and_xor_distrib_left, xor_map_xor]

/-- The switch used in R-46 Lemma 5. Flip the internal UCs along a walk
from a free frontier to a vertex whose directed response is cut by the
intervention. The resulting world flips just that frontier among the
frontiers, and preserves all crossing bits. -/
theorem flip_frontier_along_walk (g : UpperHedge tops internal crossings roots)
    (fixed : Fin tops → Option Bool) (world : UpperWorld tops internal crossings)
    (law : g.Satisfies fixed world) {frontier pivot : Fin tops}
    (isFrontier : g.child frontier = none) (isFree : fixed frontier = none)
    (walk : Walk g.internalEdges frontier pivot) (cut : ReachesIntervention g fixed pivot) :
    ∃ newWorld : UpperWorld tops internal crossings, g.Satisfies fixed newWorld ∧
      newWorld.crossingBits = world.crossingBits ∧
      ∀ v, g.child v = none →
        newWorld.values v = Bool.xor (world.values v) (decide (v = frontier)) := by
  obtain ⟨edgeMask, edgeParity⟩ := walk_mask g.internalEdges walk
  obtain ⟨pathMask, fixedPath, frontierPath, pathParity⟩ := directed_path_mask g fixed cut
  let valueMask : Fin tops → Bool := fun v => Bool.xor (decide (v = frontier)) (pathMask v)
  let newWorld : UpperWorld tops internal crossings :=
    ⟨fun v => Bool.xor (world.values v) (valueMask v), world.internalBits ^^^ edgeMask,
      world.crossingBits⟩
  refine ⟨newWorld, ?_, rfl, ?_⟩
  · intro v
    cases hv : fixed v with
    | some prescribed =>
      have notFrontier : v ≠ frontier := by
        intro eq
        subst v
        simp [isFree] at hv
      have old := law v
      simp only [hv, Option.getD_some] at old ⊢
      simp [newWorld, valueMask, old, notFrontier, fixedPath v (by simp [hv])]
    | none =>
      have maskBalance : valueMask v =
          Bool.xor (g.parentParity valueMask v) (bottomParity g.internalEdges edgeMask v) := by
        unfold valueMask
        rw [parent_parity_xor, parent_parity_single, isFrontier, edgeParity, pathParity v hv]
        simp only [reduceCtorEq, decide_false, Bool.false_xor]
        exact Bool.xor_left_comm _ _ _
      have old := law v
      simp only [hv, Option.getD_none] at old ⊢
      change Bool.xor (world.values v) (valueMask v) = _
      rw [old, maskBalance]
      simp only [UpperHedge.rhs, newWorld, parent_parity_xor, internal_parity_xor]
      simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  · intro v vFrontier
    simp [newWorld, valueMask, frontierPath v vFrontier, Bool.xor_comm]

/-- If each frontier's upper bidirected component contains a vertex whose
directed path meets the target intervention, setting all intervened
coordinates to one admits an exogenous world with all root inputs enabled.
The crossing bits are one in the initial and every modified world. -/
theorem target_upper_world (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) (fixesOne : ∀ v, fixed v ≠ some false)
    (hits : ∀ f, g.child f = none → fixed f = none →
      ∃ p, Walk g.internalEdges f p ∧ ReachesIntervention g fixed p) :
    ∃ world : UpperWorld tops internal crossings, g.Satisfies fixed world ∧
      ∀ r, (g.rootInputs world).enabled r = true := by
  let initial : UpperWorld tops internal crossings :=
    ⟨g.evaluate rank ranks fixed 0 (fun _ => true), 0, fun _ => true⟩
  have repair (remaining : List (Fin tops)) (contained : ∀ f ∈ remaining, g.child f = none)
      (old : UpperWorld tops internal crossings) (law : g.Satisfies fixed old) :
      ∃ world : UpperWorld tops internal crossings, g.Satisfies fixed world ∧
        world.crossingBits = old.crossingBits ∧
        (∀ f ∈ remaining, world.values f = true) ∧
        (∀ f, g.child f = none → old.values f = true → world.values f = true) := by
    induction remaining generalizing old with
    | nil => exact ⟨old, law, rfl, by simp, fun _ _ h => h⟩
    | cons f rest ih =>
      have hf := contained f List.mem_cons_self
      have tail := fun v mem => contained v (List.mem_cons_of_mem f mem)
      cases h : old.values f with
      | true =>
        obtain ⟨world, worldLaw, crossing, done, preserved⟩ := ih tail old law
        refine ⟨world, worldLaw, crossing, ?_, preserved⟩
        simp only [List.forall_mem_cons]
        exact ⟨preserved f hf h, done⟩
      | false =>
        have free : fixed f = none := by
          rw [law f] at h
          cases value : fixed f with
          | none => rfl
          | some b => cases b <;> simp_all
        obtain ⟨p, walk, cut⟩ := hits f hf free
        obtain ⟨next, nextLaw, nextCrossing, flipped⟩ :=
          flip_frontier_along_walk g fixed old law hf free walk cut
        have on : next.values f = true := by simp [flipped f hf, h]
        obtain ⟨world, worldLaw, crossing, done, preserved⟩ := ih tail next nextLaw
        refine ⟨world, worldLaw, crossing.trans nextCrossing, ?_, ?_⟩
        · simp only [List.forall_mem_cons]
          exact ⟨preserved f hf on, done⟩
        · intro t ht wasTrue
          have ne : t ≠ f := by
            intro eq
            subst t
            simp [h] at wasTrue
          exact preserved t ht (by simp [flipped t ht, wasTrue, ne])
  obtain ⟨world, law, crossing, on, _⟩ := repair g.frontiers
    (fun f mem => Option.isNone_iff_eq_none.mp (List.mem_filter.mp mem).2) initial
    (evaluated_world_satisfies g rank ranks fixed 0 (fun _ => true))
  refine ⟨world, law, ?_⟩
  intro r
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro b mem
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp mem
    exact on f (List.mem_filter.mp hf).1
  · simp [UpperHedge.rootInputs, crossing, initial]

/-- One coordinate of the upper model, including its target intervention.
The descendant-hit hypothesis expresses that the top bidirected component
of each frontier, together with its directed descendants above the roots,
intersects the intervention. -/
structure TargetHedge (roots : Nat) where
  tops : Nat
  internal : Nat
  crossings : Nat
  graph : UpperHedge tops internal crossings roots
  rank : Fin tops → Nat
  ordered : ∀ p v, graph.child p = some v → rank p < rank v
  fixed : Fin tops → Option Bool
  fixesOne : ∀ v, fixed v ≠ some false
  hits : ∀ f, graph.child f = none →
    ∃ p v, Walk graph.internalEdges f p ∧ DirectedPath graph p v ∧ fixed v ≠ none

abbrev TargetHedge.World (hedge : TargetHedge roots) :=
  UpperWorld hedge.tops hedge.internal hedge.crossings

theorem target_world_from_hedgelet_hits (hedge : TargetHedge roots) :
    ∃ world : hedge.World, hedge.graph.Satisfies hedge.fixed world ∧
      ∀ r, (hedge.graph.rootInputs world).enabled r = true := by
  apply target_upper_world hedge.graph hedge.rank hedge.ordered hedge.fixed hedge.fixesOne
  intro f frontier _
  obtain ⟨p, v, walk, path, fixed⟩ := hedge.hits f frontier
  exact ⟨p, walk, reaches_intervention_of_descendant hedge.graph hedge.fixed path fixed⟩

/-- When all hedge coordinates have independent upper worlds, the target
root laws differ. The context list is an enumeration of those joint worlds;
in particular it contains every admissible combination of independent bits. -/
theorem target_laws_differ_from_hedgelet_hits {Hedge : Type} {bottomEdges : Nat}
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (connected : ∀ r, Walk bottom r distinguished) (hedges : Hedge → TargetHedge roots)
    (indices : List Hedge) (contexts : List ((i : Hedge) → (hedges i).World))
    (enumerates : ∀ world, (∀ i, (hedges i).graph.Satisfies (hedges i).fixed (world i)) →
      world ∈ contexts) (keep flip : Nat) (biased : keep ≠ flip) :
    let enabled := fun (world : (i : Hedge) → (hedges i).World) =>
      (mergeRootInputs (indices.map fun i => (hedges i).graph.rootInputs (world i))).enabled
    noisyRootMixture bottom distinguished false (fun _ => none) enabled contexts keep flip ≠
      noisyRootMixture bottom distinguished true (fun _ => none) enabled contexts keep flip := by
  classical
  let witnesses := fun i => target_world_from_hedgelet_hits (hedges i)
  let world := fun i => Classical.choose (witnesses i)
  have laws := fun i => (Classical.choose_spec (witnesses i)).1
  have enabled := fun i => (Classical.choose_spec (witnesses i)).2
  dsimp only
  apply target_laws_differ bottom distinguished connected _ contexts keep flip biased world
    (enumerates world laws)
  intro r
  apply (merged_enabled_iff _ r).mpr
  intro input mem
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
  exact enabled i r

end

end OpenCausalScience.Papers.LeeEtAl2019.UpperHedgelets
