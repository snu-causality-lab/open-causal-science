module
public import OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse
public import OpenCausalScience.Papers.LeeEtAl2019.UpperMechanisms

/-! # Upper support of the supplied distributions in the g-identifiability converse

[R-46e](https://causalai.net/r46e.pdf) (July 2022) makes positivity explicit in
Definition 4: the supplied distributions `P(V \ Z | do(z))` must be positive.
`CorrectedConverse.supplied_slice_positive` gives positive mass to every root
assignment agreeing with the root intervention once the slice of retained upper
worlds at the observed upper bits is nonempty. For one hedge, this module
constructs a world in that slice for every upper assignment agreeing with the
intervention and passes it to the bottom lemma.

Each hedge coordinate is evaluated using R-46e Equation (A.2). Prescribed
upper bits leave a residual that the confounder parity must equal at each
vertex with a free equation. Flipping the internal bits along a bidirected
walk to a crossing endpoint and then flipping that crossing bit changes
the confounder parity at the starting vertex alone. The XOR of these
corrections attains every residual.

The reachability premise is that each upper vertex has a bidirected walk
to the top endpoint of a crossing confounder. A topological ranking makes
the upper bits functions of the confounder bits. Thus `upperWorlds` contains
every world satisfying the equations. `joint_slice_positive` treats a family
of independently indexed coordinates given a complete world enumeration.
`JointSCM` supplies that enumeration.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.UpperSupport

@[expose] public section

open GeneralIdentifiabilityErratum CorrectedConverse UpperMechanisms

variable {tops internal crossings roots : Nat}

private theorem xor_all_map_xor {α : Type} (xs : List α) (f h : α → Bool) :
    xorAll (xs.map fun x => Bool.xor (f x) (h x)) =
      Bool.xor (xorAll (xs.map f)) (xorAll (xs.map h)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, xorAll, ih, Bool.xor_assoc]
    exact congrArg (Bool.xor (f x)) (Bool.xor_left_comm _ _ _)

private theorem xor_all_map_false {α : Type} (xs : List α) :
    xorAll (xs.map fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, xorAll, Bool.false_xor, ih]

private theorem xor_all_one_hot {α : Type} [DecidableEq α] (xs : List α) (a : α)
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

private theorem bottom_parity_xor_bits (g : Bottom tops internal) (a b : BitVec internal)
    (v : Fin tops) :
    bottomParity g (a ^^^ b) v = Bool.xor (bottomParity g a v) (bottomParity g b v) := by
  simp only [bottomParity, BitVec.getLsbD_xor, Bool.and_xor_distrib_left, xor_all_map_xor]

private theorem bottom_parity_zero_bits (g : Bottom tops internal) (v : Fin tops) :
    bottomParity g 0 v = false := by
  simp [bottomParity, xor_all_map_false]

private theorem crossing_parity_xor_bits (g : UpperHedge tops internal crossings roots)
    (a b : Fin crossings → Bool) (v : Fin tops) :
    g.crossingParity (fun e => Bool.xor (a e) (b e)) v =
      Bool.xor (g.crossingParity a v) (g.crossingParity b v) := by
  simp only [UpperHedge.crossingParity, Bool.and_xor_distrib_left, xor_all_map_xor]

private theorem crossing_parity_false_bits (g : UpperHedge tops internal crossings roots)
    (v : Fin tops) : g.crossingParity (fun _ => false) v = false := by
  simp [UpperHedge.crossingParity, xor_all_map_false]

private theorem crossing_parity_indicator (g : UpperHedge tops internal crossings roots)
    (e : Fin crossings) (v : Fin tops) :
    g.crossingParity (fun f => decide (f = e)) v = decide (v = g.crossingTop e) := by
  unfold UpperHedge.crossingParity
  rw [show (List.finRange crossings).map
        (fun f => decide (v = g.crossingTop f) && decide (f = e)) =
      (List.finRange crossings).map (fun f => decide (f = e) && decide (v = g.crossingTop e)) by
    apply List.map_congr_left
    intro f _
    by_cases h : f = e <;> simp [h]]
  rw [xor_all_one_hot _ _ (List.nodup_finRange _)]
  simp

private theorem xor_swap_middle (a b c d : Bool) :
    Bool.xor (Bool.xor a b) (Bool.xor c d) = Bool.xor (Bool.xor a c) (Bool.xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem xor_cancel_last (a b : Bool) : Bool.xor (Bool.xor a b) b = a := by
  cases a <;> cases b <;> rfl

private theorem xor_residual_cancel (value parents negation : Bool) :
    value = Bool.xor (Bool.xor parents (Bool.xor value (Bool.xor parents negation)))
      negation := by
  cases value <;> cases parents <;> cases negation <;> rfl

/-- The singleton correction. Flip the internal UCs along a bidirected walk from
`v` to the top endpoint of a crossing UC, then flip that crossing UC. The UC
parity changes at `v` alone. -/
theorem singleton_parity_correction (g : UpperHedge tops internal crossings roots)
    {v : Fin tops} {e : Fin crossings} (walk : Walk g.internalEdges v (g.crossingTop e)) :
    ∃ (internalBits : BitVec internal) (crossingBits : Fin crossings → Bool), ∀ w,
      Bool.xor (bottomParity g.internalEdges internalBits w) (g.crossingParity crossingBits w) =
        decide (w = v) := by
  obtain ⟨mask, maskSpec⟩ := walk_mask g.internalEdges walk
  refine ⟨mask, fun f => decide (f = e), fun w => ?_⟩
  rw [maskSpec, crossing_parity_indicator]
  exact xor_cancel_last _ _

/-- If each bidirected component of the upper forest contains the top endpoint
of a crossing UC, every assignment of residual bits is a UC parity. The XOR of
the singleton corrections at the vertices with residual one attains it. -/
theorem residual_parity_correction (g : UpperHedge tops internal crossings roots)
    (reach : ∀ v, ∃ e, Walk g.internalEdges v (g.crossingTop e)) (residual : Fin tops → Bool) :
    ∃ (internalBits : BitVec internal) (crossingBits : Fin crossings → Bool), ∀ v,
      Bool.xor (bottomParity g.internalEdges internalBits v) (g.crossingParity crossingBits v) =
        residual v := by
  have listed (vs : List (Fin tops)) (unique : vs.Nodup) :
      ∃ (internalBits : BitVec internal) (crossingBits : Fin crossings → Bool), ∀ v,
        Bool.xor (bottomParity g.internalEdges internalBits v) (g.crossingParity crossingBits v) =
          (decide (v ∈ vs) && residual v) := by
    induction vs with
    | nil =>
      refine ⟨0, fun _ => false, fun v => ?_⟩
      rw [bottom_parity_zero_bits, crossing_parity_false_bits]
      simp
    | cons w ws ih =>
      obtain ⟨notMem, tailUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨internalBits, crossingBits, spec⟩ := ih tailUnique
      cases hw : residual w with
      | false =>
        refine ⟨internalBits, crossingBits, fun v => (spec v).trans ?_⟩
        by_cases same : v = w
        · subst v
          simp [hw]
        · simp [same]
      | true =>
        obtain ⟨e, walk⟩ := reach w
        obtain ⟨maskBits, maskCrossing, maskSpec⟩ := singleton_parity_correction g walk
        refine ⟨internalBits ^^^ maskBits,
          fun f => Bool.xor (crossingBits f) (maskCrossing f), fun v => ?_⟩
        rw [bottom_parity_xor_bits, crossing_parity_xor_bits, xor_swap_middle, spec v,
          maskSpec v]
        by_cases same : v = w
        · subst v
          simp [notMem, hw]
        · simp [same]
  obtain ⟨internalBits, crossingBits, spec⟩ := listed (List.finRange tops) (List.nodup_finRange _)
  exact ⟨internalBits, crossingBits, fun v => (spec v).trans (by simp)⟩

/-- The UC parity that an untouched upper equation needs for prescribed upper
bits: the prescribed bit cancelled against the parent parity and the R-46e
frontier negation. -/
def upperResidual (g : UpperHedge tops internal crossings roots) (values : Fin tops → Bool)
    (v : Fin tops) : Bool :=
  Bool.xor (values v) (Bool.xor (g.parentParity values v) (g.negated v))

/-- Every assignment of upper bits agreeing with the intervention is the upper
part of a world satisfying the hedge equations. -/
theorem prescribed_upper_world (g : UpperHedge tops internal crossings roots)
    (reach : ∀ v, ∃ e, Walk g.internalEdges v (g.crossingTop e))
    (fixed : Fin tops → Option Bool) (observed : Fin tops → Bool)
    (consistent : ∀ v value, fixed v = some value → observed v = value) :
    ∃ world : UpperWorld tops internal crossings, g.Satisfies fixed world ∧
      world.values = observed := by
  obtain ⟨internalBits, crossingBits, spec⟩ :=
    residual_parity_correction g reach (upperResidual g observed)
  refine ⟨⟨observed, internalBits, crossingBits⟩, ?_, rfl⟩
  intro v
  cases hv : fixed v with
  | some value => exact consistent v value hv
  | none =>
    show observed v = Bool.xor (Bool.xor (g.parentParity observed v)
      (Bool.xor (bottomParity g.internalEdges internalBits v) (g.crossingParity crossingBits v)))
      (g.negated v)
    rw [spec v]
    exact xor_residual_cancel (observed v) (g.parentParity observed v) (g.negated v)

/-- The upper bits are functions of the upper UCs. Two worlds with the same UCs
that satisfy the same equations have the same upper bits, by induction along a
topological ranking of the upper forest. -/
theorem values_eq_of_satisfies (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) (internalBits : BitVec internal)
    (crossingBits : Fin crossings → Bool) {first second : Fin tops → Bool}
    (firstLaw : g.Satisfies fixed ⟨first, internalBits, crossingBits⟩)
    (secondLaw : g.Satisfies fixed ⟨second, internalBits, crossingBits⟩) :
    first = second := by
  have bounded (n : Nat) : ∀ v, rank v < n → first v = second v := by
    induction n with
    | zero =>
      intro _ below
      omega
    | succ n ih =>
      intro v below
      have parents : g.parentParity first v = g.parentParity second v := by
        unfold UpperHedge.parentParity
        apply congrArg xorAll
        apply List.map_congr_left
        intro p _
        by_cases edge : g.child p = some v
        · rw [ih p (by have := ranks p v edge; omega)]
        · simp [edge]
      have firstEq : first v = (fixed v).getD (Bool.xor (Bool.xor (g.parentParity first v)
          (Bool.xor (bottomParity g.internalEdges internalBits v)
            (g.crossingParity crossingBits v))) (g.negated v)) := firstLaw v
      have secondEq : second v = (fixed v).getD (Bool.xor (Bool.xor (g.parentParity second v)
          (Bool.xor (bottomParity g.internalEdges internalBits v)
            (g.crossingParity crossingBits v))) (g.negated v)) := secondLaw v
      rw [firstEq, secondEq, parents]
  funext v
  exact bounded (rank v + 1) v (by omega)

/-- Every world satisfying the equations is the evaluated world of its own UCs. -/
theorem values_eq_evaluate_of_satisfies (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) (world : UpperWorld tops internal crossings)
    (law : g.Satisfies fixed world) :
    world.values = g.evaluate rank ranks fixed world.internalBits world.crossingBits := by
  obtain ⟨values, internalBits, crossingBits⟩ := world
  exact values_eq_of_satisfies g rank ranks fixed internalBits crossingBits law
    (evaluated_world_satisfies g rank ranks fixed internalBits crossingBits)

/-- Evaluating the upper equations at suitable UCs gives any prescribed upper
bits agreeing with the intervention. -/
theorem evaluate_attains_prescribed (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (reach : ∀ v, ∃ e, Walk g.internalEdges v (g.crossingTop e))
    (fixed : Fin tops → Option Bool) (observed : Fin tops → Bool)
    (consistent : ∀ v value, fixed v = some value → observed v = value) :
    ∃ (internalBits : BitVec internal) (crossingBits : Fin crossings → Bool),
      g.evaluate rank ranks fixed internalBits crossingBits = observed := by
  obtain ⟨world, law, same⟩ := prescribed_upper_world g reach fixed observed consistent
  exact ⟨world.internalBits, world.crossingBits,
    (values_eq_evaluate_of_satisfies g rank ranks fixed world law).symm.trans same⟩

/-- Every assignment of `n` crossing-UC bits. -/
def crossingAssignments : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => i.elim0]
  | n + 1 => (crossingAssignments n).flatMap fun rest =>
      [false, true].map fun first => (fun i => Fin.cases first rest i : Fin (n + 1) → Bool)

theorem mem_crossing_assignments {n : Nat} (bits : Fin n → Bool) :
    bits ∈ crossingAssignments n := by
  induction n with
  | zero => exact List.mem_singleton.mpr (funext fun i => i.elim0)
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨fun i => bits i.succ, ih _, ?_⟩
    apply List.mem_map.mpr
    refine ⟨bits 0, by cases bits 0 <;> decide, ?_⟩
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i
    · simp
    · simp

/-- All upper UC assignments of one hedge, each with the upper bits evaluated
along a topological ranking under the intervention. -/
def upperWorlds (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) : List (UpperWorld tops internal crossings) :=
  (List.finRange (2 ^ internal)).flatMap fun u => (crossingAssignments crossings).map fun bits =>
    ⟨g.evaluate rank ranks fixed (BitVec.ofFin u) bits, BitVec.ofFin u, bits⟩

theorem mem_upper_worlds_of_satisfies (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) {world : UpperWorld tops internal crossings}
    (law : g.Satisfies fixed world) : world ∈ upperWorlds g rank ranks fixed := by
  obtain ⟨values, internalBits, crossingBits⟩ := world
  have evaluated : values = g.evaluate rank ranks fixed internalBits crossingBits :=
    values_eq_evaluate_of_satisfies g rank ranks fixed _ law
  apply List.mem_flatMap.mpr
  refine ⟨internalBits.toFin, List.mem_finRange _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨crossingBits, mem_crossing_assignments _, ?_⟩
  rw [BitVec.ofFin_toFin, ← evaluated]

theorem satisfies_of_mem_upper_worlds (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) {world : UpperWorld tops internal crossings}
    (mem : world ∈ upperWorlds g rank ranks fixed) : g.Satisfies fixed world := by
  obtain ⟨u, _, inner⟩ := List.mem_flatMap.mp mem
  obtain ⟨bits, _, rfl⟩ := List.mem_map.mp inner
  exact evaluated_world_satisfies g rank ranks fixed (BitVec.ofFin u) bits

/-- The retained upper worlds whose upper bits are the observed ones. With the
root law of each retained world, this is the slice of the joint upper and
bottom law at the observed upper bits. -/
def upperSlice (contexts : List (UpperWorld tops internal crossings))
    (observed : Fin tops → Bool) : List (UpperWorld tops internal crossings) :=
  contexts.filter fun world => (List.finRange tops).all fun v => world.values v == observed v

theorem prescribed_world_mem_upper_slice (g : UpperHedge tops internal crossings roots)
    (reach : ∀ v, ∃ e, Walk g.internalEdges v (g.crossingTop e))
    (fixed : Fin tops → Option Bool) (contexts : List (UpperWorld tops internal crossings))
    (enumerates : ∀ world, g.Satisfies fixed world → world ∈ contexts)
    (observed : Fin tops → Bool)
    (consistent : ∀ v value, fixed v = some value → observed v = value) :
    ∃ world ∈ upperSlice contexts observed, g.Satisfies fixed world ∧
      world.values = observed := by
  obtain ⟨world, law, same⟩ := prescribed_upper_world g reach fixed observed consistent
  refine ⟨world, List.mem_filter.mpr ⟨enumerates world law, ?_⟩, law, same⟩
  apply List.all_eq_true.mpr
  intro v _
  simp [same]

/-- The upper part of R-46e positivity for one hedge. If the retained upper
worlds include every world satisfying the hedge equations under the
intervention, then the slice at any upper bits agreeing with the intervention
gives positive mass, in either model, to every root assignment agreeing with the
root intervention. -/
theorem upper_slice_positive {bottomEdges : Nat} (g : UpperHedge tops internal crossings roots)
    (reach : ∀ v, ∃ e, Walk g.internalEdges v (g.crossingTop e))
    (fixed : Fin tops → Option Bool) (contexts : List (UpperWorld tops internal crossings))
    (enumerates : ∀ world, g.Satisfies fixed world → world ∈ contexts)
    (observed : Fin tops → Bool)
    (consistent : ∀ v value, fixed v = some value → observed v = value)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool)
    (enabled : UpperWorld tops internal crossings → Fin roots → Bool)
    (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip)
    (out : Fin roots → Bool)
    (outConsistent : ∀ r value, rootFixed r = some value → out r = value) :
    0 < noisyRootMixture bottom distinguished secondModel rootFixed enabled
      (upperSlice contexts observed) keep flip out := by
  obtain ⟨world, mem, _⟩ :=
    prescribed_world_mem_upper_slice g reach fixed contexts enumerates observed consistent
  exact supplied_slice_positive bottom distinguished secondModel rootFixed enabled _ keep flip
    keepPositive flipPositive world mem out outConsistent

/-- The same positivity for the list of all upper UC assignments with evaluated
upper bits, which needs no enumeration hypothesis. -/
theorem evaluated_upper_slice_positive {bottomEdges : Nat}
    (g : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ranks : ∀ p v, g.child p = some v → rank p < rank v)
    (reach : ∀ v, ∃ e, Walk g.internalEdges v (g.crossingTop e))
    (fixed : Fin tops → Option Bool) (observed : Fin tops → Bool)
    (consistent : ∀ v value, fixed v = some value → observed v = value)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool)
    (enabled : UpperWorld tops internal crossings → Fin roots → Bool)
    (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip)
    (out : Fin roots → Bool)
    (outConsistent : ∀ r value, rootFixed r = some value → out r = value) :
    0 < noisyRootMixture bottom distinguished secondModel rootFixed enabled
      (upperSlice (upperWorlds g rank ranks fixed) observed) keep flip out :=
  upper_slice_positive g reach fixed _
    (fun _ law => mem_upper_worlds_of_satisfies g rank ranks fixed law) observed consistent
    bottom distinguished secondModel rootFixed enabled keep flip keepPositive flipPositive out
    outConsistent

/-- One hedge with its own upper coordinates and the component condition. In
the indexed model each top variable and confounder carries a bit for each hedge containing it,
so different hedges do not share these coordinates. -/
structure SupportHedge (roots : Nat) where
  tops : Nat
  internal : Nat
  crossings : Nat
  graph : UpperHedge tops internal crossings roots
  reach : ∀ v, ∃ e, Walk graph.internalEdges v (graph.crossingTop e)

abbrev SupportHedge.World (hedge : SupportHedge roots) :=
  UpperWorld hedge.tops hedge.internal hedge.crossings

/-- The retained joint upper worlds whose bits are the observed ones at every
listed hedge. -/
def jointSlice {Hedge : Type} (hedges : Hedge → SupportHedge roots) (indices : List Hedge)
    (contexts : List ((i : Hedge) → (hedges i).World))
    (observed : (i : Hedge) → Fin (hedges i).tops → Bool) :
    List ((i : Hedge) → (hedges i).World) :=
  contexts.filter fun world => indices.all fun i =>
    (List.finRange (hedges i).tops).all fun v => (world i).values v == observed i v

theorem prescribed_joint_world {Hedge : Type} (hedges : Hedge → SupportHedge roots)
    (fixed : (i : Hedge) → Fin (hedges i).tops → Option Bool)
    (observed : (i : Hedge) → Fin (hedges i).tops → Bool)
    (consistent : ∀ i v value, fixed i v = some value → observed i v = value) :
    ∃ world : (i : Hedge) → (hedges i).World,
      ∀ i, (hedges i).graph.Satisfies (fixed i) (world i) ∧ (world i).values = observed i :=
  ⟨fun i => Classical.choose (prescribed_upper_world (hedges i).graph (hedges i).reach
      (fixed i) (observed i) (consistent i)),
    fun i => Classical.choose_spec (prescribed_upper_world (hedges i).graph (hedges i).reach
      (fixed i) (observed i) (consistent i))⟩

/-- Positivity of the joint slice for hedges with independent coordinates, when
the retained joint worlds include every family of worlds satisfying the hedge
equations under the intervention. -/
theorem joint_slice_positive {Hedge : Type} {bottomEdges : Nat}
    (hedges : Hedge → SupportHedge roots)
    (fixed : (i : Hedge) → Fin (hedges i).tops → Option Bool)
    (contexts : List ((i : Hedge) → (hedges i).World))
    (enumerates : ∀ world : (i : Hedge) → (hedges i).World,
      (∀ i, (hedges i).graph.Satisfies (fixed i) (world i)) → world ∈ contexts)
    (indices : List Hedge) (observed : (i : Hedge) → Fin (hedges i).tops → Bool)
    (consistent : ∀ i v value, fixed i v = some value → observed i v = value)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool)
    (enabled : ((i : Hedge) → (hedges i).World) → Fin roots → Bool)
    (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip)
    (out : Fin roots → Bool)
    (outConsistent : ∀ r value, rootFixed r = some value → out r = value) :
    0 < noisyRootMixture bottom distinguished secondModel rootFixed enabled
      (jointSlice hedges indices contexts observed) keep flip out := by
  obtain ⟨world, spec⟩ := prescribed_joint_world hedges fixed observed consistent
  refine supplied_slice_positive bottom distinguished secondModel rootFixed enabled _ keep flip
    keepPositive flipPositive world ?_ out outConsistent
  refine List.mem_filter.mpr ⟨enumerates world fun i => (spec i).1, ?_⟩
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro v _
  simp [(spec i).2]

end

end OpenCausalScience.Papers.LeeEtAl2019.UpperSupport
