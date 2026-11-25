module
public import OpenCausalScience.Papers.LeeEtAl2019.UpperSupport

/-! # Joint world weights for the corrected g-identifiability converse

The July 2022 [R-46e](https://causalai.net/r46e.pdf) gives the upper
structural equation (A.2) and the updated bottom equations (2) and (3).
Each choice of the independent upper confounder bits is enumerated once.
Summing bottom weights over worlds at specified upper bits gives the joint
weights; summing over all upper worlds gives the root marginal weights.
The target check uses a compatible solution of (A.2) enabling every root.
The graph embedding and the transport of root disagreement to the target
outcome are separate from these finite calculations.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.JointSCM

@[expose] public section

open GeneralIdentifiabilityErratum CorrectedConverse UpperMechanisms UpperSupport

variable {roots count : Nat}

/-- Cartesian product for finite dependent lists. -/
def tupleProduct : {n : Nat} → (α : Fin n → Type) →
    ((i : Fin n) → List (α i)) → List ((i : Fin n) → α i)
  | 0, _, _ => [fun i => i.elim0]
  | n + 1, α, choices => (choices 0).flatMap fun head =>
      (tupleProduct (fun i : Fin n => α i.succ) (fun i => choices i.succ)).map
        fun tail => Fin.cases head tail

private theorem mem_tuples {n : Nat} (α : Fin n → Type)
    (choices : (i : Fin n) → List (α i)) (tuple : (i : Fin n) → α i) :
    tuple ∈ tupleProduct α choices ↔ ∀ i, tuple i ∈ choices i := by
  induction n with
  | zero =>
    constructor
    · intro _ i
      exact i.elim0
    · intro _
      exact List.mem_singleton.mpr (funext fun i => i.elim0)
  | succ n ih =>
    change tuple ∈ (choices 0).flatMap _ ↔ _
    constructor
    · intro mem i
      obtain ⟨head, hm, m⟩ := List.mem_flatMap.mp mem
      obtain ⟨tail, tm, rfl⟩ := List.mem_map.mp m
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hm
      · simpa using (ih _ _ _).mp tm i
    · intro each
      apply List.mem_flatMap.mpr
      refine ⟨tuple 0, each 0, List.mem_map.mpr ⟨fun i => tuple i.succ, ?_, ?_⟩⟩
      · exact (ih _ _ _).mpr fun i => each i.succ
      · funext i
        exact Fin.cases (by simp) (fun i => by simp) i

private theorem nodup_map_of_left_inverse {α β : Type} (f : α → β) (g : β → α)
    (inverse : ∀ x, g (f x) = x) {xs : List α} (unique : xs.Nodup) :
    (xs.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact unique.imp fun diff same => diff (by simpa only [inverse] using congrArg g same)

private theorem nodup_flat_map_of_key {α β : Type} (f : α → List β) (key : β → α)
    {xs : List α} (unique : xs.Nodup)
    (blockUnique : ∀ a ∈ xs, (f a).Nodup)
    (identifies : ∀ a ∈ xs, ∀ b ∈ f a, key b = a) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    refine ⟨blockUnique a List.mem_cons_self, ih tailUnique
      (fun p hp => blockUnique p (List.mem_cons_of_mem _ hp))
      (fun p hp => identifies p (List.mem_cons_of_mem _ hp)), ?_⟩
    intro b hb b' hb' same
    obtain ⟨p, hp, mem⟩ := List.mem_flatMap.mp hb'
    apply absent
    have left := identifies a List.mem_cons_self b hb
    have right := identifies p (List.mem_cons_of_mem _ hp) b' mem
    have equal : a = p := left.symm.trans ((congrArg key same).trans right)
    exact equal ▸ hp

private theorem nodup_tuples {n : Nat} (α : Fin n → Type)
    (choices : (i : Fin n) → List (α i)) (unique : ∀ i, (choices i).Nodup) :
    (tupleProduct α choices).Nodup := by
  induction n with
  | zero => simp [tupleProduct]
  | succ n ih =>
    change ((choices 0).flatMap _).Nodup
    apply nodup_flat_map_of_key _ (fun tuple : (i : Fin (n + 1)) → α i => tuple 0) (unique 0)
    · intro head _
      apply nodup_map_of_left_inverse _ (fun tuple (i : Fin n) => tuple i.succ)
      · intro tail
        funext i
        simp
      · exact ih _ _ fun i => unique i.succ
    · intro head _ tuple mem
      obtain ⟨tail, _, rfl⟩ := List.mem_map.mp mem
      simp

private theorem length_flat_map_of_constant {α β : Type} (f : α → List β)
    (xs : List α) (k : Nat) (size : ∀ a ∈ xs, (f a).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.length_append, size a List.mem_cons_self,
      ih (fun a ha => size a (List.mem_cons_of_mem _ ha)), List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem length_tuples {n : Nat} (α : Fin n → Type)
    (choices : (i : Fin n) → List (α i)) :
    (tupleProduct α choices).length = ((List.finRange n).map fun i => (choices i).length).prod := by
  induction n with
  | zero => simp [tupleProduct]
  | succ n ih =>
    rw [tupleProduct, List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    rw [length_flat_map_of_constant _ _ _ (fun _ _ => List.length_map _)]
    rw [ih]
    rfl

private theorem nodup_crossing_assignments (crossings : Nat) :
    (crossingAssignments crossings).Nodup := by
  induction crossings with
  | zero => simp [crossingAssignments]
  | succ n ih =>
    rw [crossingAssignments]
    apply nodup_flat_map_of_key _ (fun bits i => bits i.succ) ih
    · intro tail _
      apply nodup_map_of_left_inverse _ (fun bits => bits 0)
      · intro first
        simp
      · decide
    · intro tail _ bits mem
      obtain ⟨first, _, rfl⟩ := List.mem_map.mp mem
      funext i
      simp

private theorem length_crossing_assignments (crossings : Nat) :
    (crossingAssignments crossings).length = 2 ^ crossings := by
  induction crossings with
  | zero => rfl
  | succ n ih =>
    rw [crossingAssignments, length_flat_map_of_constant _ _ 2 (by simp), ih, Nat.pow_succ]

private theorem nodup_upper_worlds {tops internal crossings : Nat}
    (graph : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ordered : ∀ p v, graph.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) :
    (upperWorlds graph rank ordered fixed).Nodup := by
  rw [upperWorlds]
  apply nodup_flat_map_of_key _ (fun world => world.internalBits.toFin) (List.nodup_finRange _)
  · intro u _
    apply nodup_map_of_left_inverse _ (fun world => world.crossingBits)
    · intro bits
      rfl
    · exact nodup_crossing_assignments _
  · intro u _ world mem
    obtain ⟨bits, _, rfl⟩ := List.mem_map.mp mem
    rfl

private theorem length_upper_worlds {tops internal crossings : Nat}
    (graph : UpperHedge tops internal crossings roots)
    (rank : Fin tops → Nat) (ordered : ∀ p v, graph.child p = some v → rank p < rank v)
    (fixed : Fin tops → Option Bool) :
    (upperWorlds graph rank ordered fixed).length = 2 ^ (internal + crossings) := by
  rw [upperWorlds, length_flat_map_of_constant _ _ _ (fun _ _ => List.length_map _),
    List.length_finRange, length_crossing_assignments, Nat.pow_add]

variable (hedges : Fin count → SupportHedge roots)

abbrev World := (i : Fin count) → (hedges i).World

abbrev Intervention := (i : Fin count) → Fin (hedges i).tops → Option Bool

abbrev UpperAssignment := (i : Fin count) → Fin (hedges i).tops → Bool

structure Rankings where
  rank : (i : Fin count) → Fin (hedges i).tops → Nat
  ordered : ∀ i p v, (hedges i).graph.child p = some v → rank i p < rank i v

/-- Evaluated joint worlds from all choices of the independent upper UC bits. -/
def worlds (ranking : Rankings hedges) (fixed : Intervention hedges) : List (World hedges) :=
  tupleProduct (fun i => (hedges i).World) fun i =>
    upperWorlds (hedges i).graph (ranking.rank i) (ranking.ordered i) (fixed i)

theorem mem_worlds_iff (ranking : Rankings hedges) (fixed : Intervention hedges)
    (world : World hedges) :
    world ∈ worlds hedges ranking fixed ↔
      ∀ i, (hedges i).graph.Satisfies (fixed i) (world i) := by
  rw [worlds, mem_tuples]
  constructor
  · intro mem i
    exact satisfies_of_mem_upper_worlds _ _ _ _ (mem i)
  · intro law i
    exact mem_upper_worlds_of_satisfies _ _ _ _ (law i)

theorem worlds_nodup (ranking : Rankings hedges) (fixed : Intervention hedges) :
    (worlds hedges ranking fixed).Nodup := by
  unfold worlds
  exact nodup_tuples _ _ fun i => nodup_upper_worlds _ _ _ _

def upperBitCount : Nat :=
  ((List.finRange count).map fun i => (hedges i).internal + (hedges i).crossings).sum

private theorem prod_two_pow (sizes : List Nat) :
    (sizes.map (2 ^ ·)).prod = 2 ^ sizes.sum := by
  induction sizes with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons, List.prod_cons, ih, List.sum_cons, Nat.pow_add]

theorem worlds_length (ranking : Rankings hedges) (fixed : Intervention hedges) :
    (worlds hedges ranking fixed).length = 2 ^ upperBitCount hedges := by
  rw [worlds, length_tuples, upperBitCount, ← prod_two_pow, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact length_upper_worlds _ _ _ _

/-- The root inputs consist of the frontier and crossing coordinates of every hedge. -/
def rootInputs (world : World hedges) : List (GateInputs roots) :=
  (List.finRange count).map fun i => (hedges i).graph.rootInputs (world i)

def enabled (world : World hedges) : Fin roots → Bool :=
  (mergeRootInputs (rootInputs hedges world)).enabled

variable {bottomEdges : Nat}

/-- The joint weights for the observed upper assignment and the root output.
Upper UC worlds and bottom UC worlds each have unit weight; positive integers
`keep` and `flip` are the private noise weights at every free root. The
intervened bits are retained as coordinates fixed to their imposed values. -/
def jointWeight (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool) (keep flip : Nat)
    (observed : UpperAssignment hedges) : WeightTable (Fin roots) :=
  noisyRootMixture bottom distinguished secondModel rootFixed (enabled hedges)
    (jointSlice hedges (List.finRange count) (worlds hedges ranking fixed) observed) keep flip

/-- The weights of the root marginal, summing over all upper worlds. -/
def rootWeight (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool) (keep flip : Nat) : WeightTable (Fin roots) :=
  noisyRootMixture bottom distinguished secondModel rootFixed (enabled hedges)
    (worlds hedges ranking fixed) keep flip

/-- A root intervention or one whole untouched hedge suffices for a
supplied experiment. Every upper slice agrees under this explicit premise. -/
theorem supplied_weights_equal (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (connected : ∀ r, Walk bottom r distinguished)
    (rootFixed : Fin roots → Option Bool) (keep flip : Nat)
    (offered : (∃ r, rootFixed r ≠ none) ∨ (∃ i, ∀ v, fixed i v = none)) :
    jointWeight hedges ranking fixed bottom distinguished false rootFixed keep flip =
      jointWeight hedges ranking fixed bottom distinguished true rootFixed keep flip := by
  funext observed
  apply supplied_agreement_from_untouched_hedge bottom distinguished connected rootFixed
    (rootInputs hedges)
  rcases offered with root | ⟨i, untouched⟩
  · exact Or.inl root
  · refine Or.inr ⟨_, _, _, (hedges i).graph, fun (w : World hedges) => w i, ?_, ?_⟩
    · intro world mem
      have law := (mem_worlds_iff hedges ranking fixed world).1 (List.mem_filter.mp mem).1 i
      rw [show fixed i = fun _ => none from funext untouched] at law
      exact law
    · intro world _
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- R-46e Definition 4 positivity holds at every upper and root assignment
consistent with the supplied intervention, for the evaluated joint worlds. -/
theorem supplied_weight_positive (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool)
    (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip)
    (observed : UpperAssignment hedges)
    (consistent : ∀ i v value, fixed i v = some value → observed i v = value)
    (out : Fin roots → Bool)
    (outConsistent : ∀ r value, rootFixed r = some value → out r = value) :
    0 < jointWeight hedges ranking fixed bottom distinguished secondModel rootFixed keep flip
      observed out :=
  joint_slice_positive hedges fixed _ (fun w => (mem_worlds_iff hedges ranking fixed w).2)
    _ observed consistent bottom distinguished secondModel rootFixed (enabled hedges) keep flip
    keepPositive flipPositive out outConsistent

/-- A compatible solution of (A.2), including the frontier toggle and the
target assignment, at which all root indicators are enabled. -/
def HasEnabledWorld (fixed : Intervention hedges) : Prop :=
  ∃ w : World hedges, (∀ i, (hedges i).graph.Satisfies (fixed i) (w i)) ∧
    ∀ r, enabled hedges w r = true

/-- Exhaustive finite check of the target equations and root indicators. -/
def targetHasEnabledWorld (ranking : Rankings hedges) (fixed : Intervention hedges) : Bool :=
  (worlds hedges ranking fixed).any fun w => (List.finRange roots).all (enabled hedges w)

theorem targetHasEnabledWorld_eq_true (ranking : Rankings hedges) (fixed : Intervention hedges) :
    targetHasEnabledWorld hedges ranking fixed = true ↔ HasEnabledWorld hedges fixed := by
  simp only [targetHasEnabledWorld, List.any_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, mem_worlds_iff, HasEnabledWorld]

theorem exists_world_all_enabled (ranking : Rankings hedges) (fixed : Intervention hedges)
    (target : HasEnabledWorld hedges fixed) :
    ∃ w ∈ worlds hedges ranking fixed, ∀ r, enabled hedges w r = true := by
  obtain ⟨w, equations, on⟩ := target
  exact ⟨w, (mem_worlds_iff hedges ranking fixed w).2 equations, on⟩

/-- Root marginals differ when the target admits an all-enabled world and
no root is fixed. The private root noise can have any common biased weights. -/
theorem target_root_weights_differ (ranking : Rankings hedges) (fixed : Intervention hedges)
    (target : HasEnabledWorld hedges fixed)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (connected : ∀ r, Walk bottom r distinguished) (keep flip : Nat) (biased : keep ≠ flip) :
    rootWeight hedges ranking fixed bottom distinguished false (fun _ => none) keep flip ≠
      rootWeight hedges ranking fixed bottom distinguished true (fun _ => none) keep flip := by
  obtain ⟨w, mem, on⟩ := exists_world_all_enabled hedges ranking fixed target
  exact target_laws_differ bottom distinguished connected (enabled hedges) _ keep flip biased w mem on

private theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_map_mul {α : Type} (xs : List α) (f : α → Nat) (k : Nat) :
    (xs.map fun x => k * f x).sum = k * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem sum_map_constant {α : Type} (xs : List α) (k : Nat) :
    (xs.map fun _ => k).sum = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.add_mul, Nat.add_comm]

private theorem sum_map_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp [sum_map_constant]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, sum_map_add, ih]

private theorem sum_map_delta {α : Type} [DecidableEq α] (xs : List α)
    (unique : xs.Nodup) (x : α) (gain : Nat) :
    (xs.map fun y => if x = y then gain else 0).sum = if x ∈ xs then gain else 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    by_cases h : x = y
    · subst y
      simp [ih tail, absent]
    · simp [ih tail, h]

private theorem weighted_count {α β : Type} [DecidableEq β] (xs : List α) (ys : List β)
    (value : α → β) (score : β → Nat) (unique : ys.Nodup)
    (covers : ∀ x ∈ xs, value x ∈ ys) :
    (ys.map fun y => score y * xs.countP (fun x => decide (value x = y))).sum =
      (xs.map fun x => score (value x)).sum := by
  induction xs with
  | nil => simp [sum_map_constant]
  | cons x xs ih =>
    simp only [List.countP_cons, decide_eq_true_eq, Nat.mul_add, sum_map_add, List.map_cons,
      List.sum_cons, ih (fun x hx => covers x (List.mem_cons_of_mem _ hx))]
    rw [show (ys.map fun y => score y * (if value x = y then 1 else 0)) =
        (ys.map fun y => if value x = y then score (value x) else 0) from by
      apply List.map_congr_left
      intro y _
      by_cases same : value x = y <;> simp [same]]
    rw [sum_map_delta _ unique]
    simp only [covers x List.mem_cons_self, ↓reduceIte, Nat.add_comm]

private theorem sum_perm {xs ys : List Nat} (perm : xs.Perm ys) : xs.sum = ys.sum := by
  induction perm with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap a b xs => simp [Nat.add_left_comm]
  | trans _ _ first second => exact first.trans second

private theorem flip_at_twice (i : Fin roots) (out : Fin roots → Bool) :
    flipAt i (flipAt i out) = out := by
  funext j
  by_cases same : j = i <;> simp [flipAt, same]

private theorem flip_assignments_perm (i : Fin roots) :
    ((crossingAssignments roots).map (flipAt i)).Perm (crossingAssignments roots) := by
  have unique := nodup_crossing_assignments roots
  apply (List.perm_ext_iff_of_nodup
    (nodup_map_of_left_inverse _ _ (flip_at_twice i) unique) unique).2
  intro out
  constructor
  · intro _
    exact mem_crossing_assignments _
  · intro _
    exact List.mem_map.mpr ⟨flipAt i out, mem_crossing_assignments _, flip_at_twice i out⟩

private theorem sum_map_flip (i : Fin roots) (weight : (Fin roots → Bool) → Nat) :
    ((crossingAssignments roots).map fun out => weight (flipAt i out)).sum =
      ((crossingAssignments roots).map weight).sum :=
  by simpa only [List.map_map, Function.comp_def] using
    sum_perm ((flip_assignments_perm i).map weight)

private def weightedRootSum (score : (Fin roots → Bool) → Nat)
    (law : WeightTable (Fin roots)) : Nat :=
  ((crossingAssignments roots).map fun out => score out * law out).sum

private theorem all_roots_beq (first second : Fin roots → Bool) :
    ((List.finRange roots).all fun v => first v == second v) = true ↔ first = second := by
  simp only [List.all_eq_true, beq_iff_eq, List.mem_finRange, true_implies]
  exact funext_iff.symm

private theorem weighted_raw_root_law (bottom : Bottom roots bottomEdges)
    (distinguished : Fin roots) (secondModel : Bool) (fixed : Fin roots → Option Bool)
    (on : Fin roots → Bool) (score : (Fin roots → Bool) → Nat) :
    weightedRootSum score (rawRootLaw bottom distinguished secondModel fixed on) =
      ((List.finRange (2 ^ bottomEdges)).map fun u =>
        score (rootOutcome bottom distinguished secondModel fixed on (BitVec.ofFin u))).sum := by
  classical
  unfold weightedRootSum rawRootLaw
  rw [show ((crossingAssignments roots).map fun out => score out *
        (List.finRange (2 ^ bottomEdges)).countP (fun u => (List.finRange roots).all
          fun v => rootOutcome bottom distinguished secondModel fixed on (BitVec.ofFin u) v ==
            out v)) =
      (crossingAssignments roots).map (fun out => score out *
        (List.finRange (2 ^ bottomEdges)).countP
          (fun u => decide (rootOutcome bottom distinguished secondModel fixed on
            (BitVec.ofFin u) = out))) from by
    apply List.map_congr_left
    intro out _
    congr 1
    apply List.countP_congr
    intro u _
    rw [all_roots_beq, decide_eq_true_eq]]
  exact weighted_count _ _ _ _ (nodup_crossing_assignments roots)
    (fun _ _ => mem_crossing_assignments _)

private theorem weighted_raw_root_mixture {Context : Type} (bottom : Bottom roots bottomEdges)
    (distinguished : Fin roots) (secondModel : Bool) (fixed : Fin roots → Option Bool)
    (on : Context → Fin roots → Bool) (contexts : List Context)
    (score : (Fin roots → Bool) → Nat) :
    weightedRootSum score (rawRootMixture bottom distinguished secondModel fixed on contexts) =
      (contexts.map fun ctx =>
        weightedRootSum score (rawRootLaw bottom distinguished secondModel fixed (on ctx))).sum := by
  unfold weightedRootSum rawRootMixture
  rw [show ((crossingAssignments roots).map fun out => score out *
        (contexts.map fun ctx => rawRootLaw bottom distinguished secondModel fixed (on ctx) out).sum)
      = ((crossingAssignments roots).map fun out =>
        (contexts.map fun ctx => score out *
          rawRootLaw bottom distinguished secondModel fixed (on ctx) out).sum) from by
    apply List.map_congr_left
    intro out _
    exact (sum_map_mul _ _ _).symm]
  exact sum_map_swap _ _ _

private theorem weighted_noise_at (law : WeightTable (Fin roots))
    (score : (Fin roots → Bool) → Nat) (i : Fin roots) (keep flip : Nat) :
    weightedRootSum score (noiseAt keep flip i law) =
      keep * weightedRootSum score law + flip * weightedRootSum (fun out => score (flipAt i out)) law := by
  have second := sum_map_flip i (fun out => score (flipAt i out) * law out)
  simp only [flip_at_twice] at second
  simp only [weightedRootSum, noiseAt, Nat.mul_add, sum_map_add]
  rw [show ((crossingAssignments roots).map fun out => score out * (keep * law out)) =
      (crossingAssignments roots).map (fun out => keep * (score out * law out)) from by
    apply List.map_congr_left
    intro _ _
    exact Nat.mul_left_comm _ _ _]
  rw [show ((crossingAssignments roots).map fun out => score out * (flip * law (flipAt i out))) =
      (crossingAssignments roots).map (fun out => flip * (score out * law (flipAt i out))) from by
    apply List.map_congr_left
    intro _ _
    exact Nat.mul_left_comm _ _ _]
  rw [sum_map_mul, sum_map_mul, second]

/-- Sum the root law over every binary assignment, including zero-weight
assignments inconsistent with the root intervention. -/
def totalRootWeight (law : WeightTable (Fin roots)) : Nat :=
  ((crossingAssignments roots).map law).sum

private theorem weighted_root_sum_one (law : WeightTable (Fin roots)) :
    weightedRootSum (fun _ => 1) law = totalRootWeight law := by
  simp [weightedRootSum, totalRootWeight]

private theorem total_noise_all (law : WeightTable (Fin roots)) (keep flip : Nat)
    (coordinates : List (Fin roots)) :
    totalRootWeight (noiseAll keep flip coordinates law) =
      (keep + flip) ^ coordinates.length * totalRootWeight law := by
  induction coordinates with
  | nil => simp [noiseAll]
  | cons i is ih =>
    rw [noiseAll, ← weighted_root_sum_one, weighted_noise_at,
      weighted_root_sum_one, ← Nat.add_mul, ih]
    simp only [List.length_cons, Nat.pow_succ]
    ac_rfl

/-- Common denominator for the joint and marginal root weights. There are
`2^(upperBitCount + bottomEdges)` uniform UC assignments. Each free root
responds to one independent noise draw of total weight `keep + flip`. -/
def massDenominator (bottomEdges : Nat) (rootFixed : Fin roots → Option Bool) (keep flip : Nat) :
    Nat :=
  2 ^ (upperBitCount hedges + bottomEdges) * (keep + flip) ^ (freeRoots rootFixed).length

theorem root_weight_total (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool) (keep flip : Nat) :
    totalRootWeight (rootWeight hedges ranking fixed bottom distinguished secondModel
      rootFixed keep flip) = massDenominator hedges bottomEdges rootFixed keep flip := by
  rw [rootWeight, noisyRootMixture, total_noise_all, ← weighted_root_sum_one,
    weighted_raw_root_mixture]
  have each (w : World hedges) :
      weightedRootSum (fun _ => 1)
        (rawRootLaw bottom distinguished secondModel rootFixed (enabled hedges w)) =
        2 ^ bottomEdges := by
    rw [weighted_raw_root_law, sum_map_constant, List.length_finRange, Nat.mul_one]
  simp only [each, sum_map_constant, worlds_length, massDenominator, Nat.pow_add]
  ac_rfl

/-- All upper observations, including cells with zero mass under an intervention. -/
def upperAssignments : List (UpperAssignment hedges) :=
  tupleProduct (fun i => Fin (hedges i).tops → Bool) fun i =>
    crossingAssignments (hedges i).tops

private theorem upper_assignments_complete (obs : UpperAssignment hedges) :
    obs ∈ upperAssignments hedges :=
  (mem_tuples _ _ _).2 fun _ => mem_crossing_assignments _

private theorem upper_assignments_nodup : (upperAssignments hedges).Nodup :=
  nodup_tuples _ _ fun _ => nodup_crossing_assignments _

private theorem sum_map_filter {α : Type} (xs : List α) (p : α → Bool) (f : α → Nat) :
    ((xs.filter p).map f).sum = (xs.map fun x => if p x then f x else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [h, ih]

private theorem upper_test_iff (world : World hedges) (obs : UpperAssignment hedges) :
    ((List.finRange count).all fun i =>
      (List.finRange (hedges i).tops).all fun v => (world i).values v == obs i v) = true ↔
      (fun i => (world i).values) = obs := by
  simp only [List.all_eq_true, beq_iff_eq, List.mem_finRange, true_implies, funext_iff]

private theorem sum_of_slices (contexts : List (World hedges)) (weight : World hedges → Nat) :
    ((upperAssignments hedges).map fun obs =>
      ((jointSlice hedges (List.finRange count) contexts obs).map weight).sum).sum =
      (contexts.map weight).sum := by
  classical
  rw [show ((upperAssignments hedges).map fun obs =>
        ((jointSlice hedges (List.finRange count) contexts obs).map weight).sum) =
      (upperAssignments hedges).map (fun obs =>
        (contexts.map fun w => if (fun i => (w i).values) = obs then weight w else 0).sum) from by
    apply List.map_congr_left
    intro obs _
    rw [jointSlice, sum_map_filter]
    apply congrArg List.sum
    apply List.map_congr_left
    intro w _
    simp only [upper_test_iff]]
  rw [sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  rw [sum_map_delta _ (upper_assignments_nodup hedges)]
  simp only [upper_assignments_complete hedges, ↓reduceIte]

private theorem noise_all_sum {α : Type} (xs : List α) (law : α → WeightTable (Fin roots))
    (coordinates : List (Fin roots)) (keep flip : Nat) (out : Fin roots → Bool) :
    (xs.map fun x => noiseAll keep flip coordinates (law x) out).sum =
      noiseAll keep flip coordinates (fun r => (xs.map fun x => law x r).sum) out := by
  induction coordinates generalizing out with
  | nil => rfl
  | cons i is ih =>
    simp only [noiseAll, noiseAt, sum_map_add, sum_map_mul, ih]

/-- Summing the joint weights over all upper observations gives the root marginal. -/
theorem joint_weight_marginalize (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool) (keep flip : Nat) (out : Fin roots → Bool) :
    ((upperAssignments hedges).map fun obs => jointWeight hedges ranking fixed bottom distinguished
      secondModel rootFixed keep flip obs out).sum =
      rootWeight hedges ranking fixed bottom distinguished secondModel rootFixed keep flip out := by
  simp only [jointWeight, rootWeight, noisyRootMixture, noise_all_sum]
  apply congrFun (congrArg (noiseAll keep flip (freeRoots rootFixed)) _)
  funext r
  exact sum_of_slices hedges (worlds hedges ranking fixed) fun w =>
    rawRootLaw bottom distinguished secondModel rootFixed (enabled hedges w) r

theorem joint_weight_total (ranking : Rankings hedges) (fixed : Intervention hedges)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots) (secondModel : Bool)
    (rootFixed : Fin roots → Option Bool) (keep flip : Nat) :
    ((upperAssignments hedges).map fun obs => totalRootWeight (jointWeight hedges ranking fixed
      bottom distinguished secondModel rootFixed keep flip obs)).sum =
      massDenominator hedges bottomEdges rootFixed keep flip := by
  rw [← root_weight_total hedges ranking fixed bottom distinguished secondModel rootFixed keep flip]
  unfold totalRootWeight
  rw [sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro out _
  exact joint_weight_marginalize hedges ranking fixed bottom distinguished secondModel rootFixed
    keep flip out

/-- Parity of all bottom bits. -/
def rootParity (out : Fin roots → Bool) : Bool :=
  xorAll ((List.finRange roots).map out)

private theorem xor_map_xor {α : Type} (xs : List α) (a b : α → Bool) :
    xorAll (xs.map fun x => Bool.xor (a x) (b x)) =
      Bool.xor (xorAll (xs.map a)) (xorAll (xs.map b)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, xorAll, ih, Bool.xor_assoc]
    exact congrArg (Bool.xor (a x)) (Bool.xor_left_comm _ _ _)

private theorem xor_map_zero {α : Type} (xs : List α) :
    xorAll (xs.map fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, xorAll, ih, Bool.false_xor]

private theorem xor_map_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Bool) :
    xorAll (xs.map fun x => xorAll (ys.map (f x))) =
      xorAll (ys.map fun y => xorAll (xs.map fun x => f x y)) := by
  induction xs with
  | nil => simpa only [List.map_nil, xorAll] using (xor_map_zero ys).symm
  | cons x xs ih => simp only [List.map_cons, xorAll, ih, xor_map_xor]

private theorem xor_map_one_hot {α : Type} [DecidableEq α] (xs : List α)
    (unique : xs.Nodup) (x : α) (bit : Bool) :
    xorAll (xs.map fun y => decide (y = x) && bit) = (decide (x ∈ xs) && bit) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    by_cases same : y = x
    · subst y
      simp [xorAll, ih tail, absent]
    · simp [xorAll, ih tail, same, Ne.symm same]

private theorem bottom_parity_even (bottom : Bottom roots bottomEdges) (bits : BitVec bottomEdges) :
    rootParity (bottomParity bottom bits) = false := by
  unfold rootParity bottomParity
  rw [xor_map_swap]
  apply (congrArg xorAll (List.map_congr_left (g := fun _ => false) ?_)).trans (xor_map_zero _)
  intro e _
  simp only [incident, Bool.and_xor_distrib_right, xor_map_xor]
  rw [xor_map_one_hot _ (List.nodup_finRange _), xor_map_one_hot _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

theorem root_parity_all_enabled (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (secondModel : Bool) (bits : BitVec bottomEdges) :
    rootParity (rootOutcome bottom distinguished secondModel (fun _ => none) (fun _ => true)
      bits) = secondModel := by
  change xorAll ((List.finRange roots).map fun r =>
    Bool.xor (bottomParity bottom bits r) (secondModel && decide (r = distinguished))) = secondModel
  have even := bottom_parity_even bottom bits
  unfold rootParity at even
  cases secondModel
  · simpa only [Bool.false_and, Bool.xor_false] using even
  · simp only [Bool.true_and, xor_map_xor, even, Bool.false_xor]
    simpa using xor_map_one_hot _ (List.nodup_finRange roots) distinguished true

private theorem root_parity_flip (i : Fin roots) (out : Fin roots → Bool) :
    rootParity (flipAt i out) = !(rootParity out) := by
  unfold rootParity
  rw [show (List.finRange roots).map (flipAt i out) =
      (List.finRange roots).map (fun v => Bool.xor (out v) (decide (v = i))) from by
    apply List.map_congr_left
    intro r _
    by_cases same : r = i <;> simp [flipAt, same]]
  rw [xor_map_xor]
  have toggled := xor_map_one_hot (List.finRange roots) (List.nodup_finRange _) i true
  simp only [Bool.and_true, List.mem_finRange, decide_true] at toggled
  simp only [toggled, Bool.xor_true]

/-- The weights on even and odd root parity. `Unit` indexes the single output
bit so that this table can use the same private-noise operation. -/
def parityWeights (law : WeightTable (Fin roots)) : WeightTable Unit :=
  fun out =>
    ((crossingAssignments roots).map fun root => (if rootParity root = out () then 1 else 0) *
      law root).sum

private theorem parity_weights_noise_at (law : WeightTable (Fin roots)) (i : Fin roots)
    (keep flip : Nat) :
    parityWeights (noiseAt keep flip i law) = noiseAt keep flip () (parityWeights law) := by
  funext out
  show weightedRootSum (fun root => if rootParity root = out () then 1 else 0)
      (noiseAt keep flip i law) =
    keep * weightedRootSum (fun root => if rootParity root = out () then 1 else 0) law +
    flip * weightedRootSum (fun root => if rootParity root = flipAt () out () then 1 else 0) law
  rw [weighted_noise_at]
  congr 2
  apply congrArg (fun score => weightedRootSum score law)
  funext root
  simp only [root_parity_flip, flipAt, ↓reduceIte]
  cases rootParity root <;> cases out () <;> rfl

theorem parity_weights_noise_all (law : WeightTable (Fin roots)) (coordinates : List (Fin roots))
    (keep flip : Nat) :
    parityWeights (noiseAll keep flip coordinates law) =
      noiseAll keep flip (coordinates.map fun _ => ()) (parityWeights law) := by
  induction coordinates with
  | nil => rfl
  | cons i is ih =>
    simp only [noiseAll, parity_weights_noise_at, ih, List.map_cons]

private theorem all_enabled_even_weight (bottom : Bottom roots bottomEdges)
    (distinguished : Fin roots) (secondModel : Bool) :
    parityWeights (rawRootLaw bottom distinguished secondModel (fun _ => none) (fun _ => true))
        (fun _ => false) = if secondModel then 0 else 2 ^ bottomEdges := by
  change weightedRootSum (fun out => if rootParity out = false then 1 else 0) _ = _
  rw [weighted_raw_root_law]
  cases secondModel <;>
    simp [root_parity_all_enabled, sum_map_constant, List.length_finRange]

private theorem raw_even_weights_differ {Context : Type} (bottom : Bottom roots bottomEdges)
    (distinguished : Fin roots) (connected : ∀ r, Walk bottom r distinguished)
    (on : Context → Fin roots → Bool) (contexts : List Context)
    (w : Context) (mem : w ∈ contexts) (allEnabled : ∀ r, on w r = true) :
    parityWeights (rawRootMixture bottom distinguished true (fun _ => none) on contexts)
        (fun _ => false) <
      parityWeights (rawRootMixture bottom distinguished false (fun _ => none) on contexts)
        (fun _ => false) := by
  classical
  let even ctx secondModel := parityWeights
    (rawRootLaw bottom distinguished secondModel (fun _ => none) (on ctx)) (fun _ => false)
  let gain ctx := if ∀ r, on ctx r = true then 2 ^ bottomEdges else 0
  have exactGain (ctx : Context) : even ctx true + gain ctx = even ctx false := by
    by_cases all : ∀ r, on ctx r = true
    · simp [even, gain, all, show on ctx = fun _ => true from funext all, all_enabled_even_weight]
    · obtain ⟨r, off⟩ := Classical.not_forall.mp all
      have off' : on ctx r = false := by cases h : on ctx r <;> simp_all
      rw [show even ctx true = even ctx false from by
        unfold even
        rw [raw_root_laws_equal bottom distinguished r (connected r) _ _ (Or.inr off')]]
      simp [gain, all]
  have positive : 0 < (contexts.map gain).sum := by
    apply List.sum_pos_iff_exists_pos_nat.mpr
    exact ⟨gain w, List.mem_map.mpr ⟨w, mem, rfl⟩, by simpa [gain, allEnabled] using Nat.two_pow_pos bottomEdges⟩
  have gainSum := congrArg List.sum (List.map_congr_left (l := contexts)
    (fun ctx _ => exactGain ctx))
  rw [sum_map_add] at gainSum
  change weightedRootSum (fun out => if rootParity out = false then 1 else 0) _ <
    weightedRootSum (fun out => if rootParity out = false then 1 else 0) _
  rw [weighted_raw_root_mixture, weighted_raw_root_mixture]
  change (contexts.map fun ctx => even ctx true).sum < (contexts.map fun ctx => even ctx false).sum
  omega

/-- The two target laws differ on root parity itself after biased private
noise. -/
theorem target_root_parity_weights_differ (ranking : Rankings hedges) (fixed : Intervention hedges)
    (target : HasEnabledWorld hedges fixed)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (connected : ∀ r, Walk bottom r distinguished) (keep flip : Nat) (biased : keep ≠ flip) :
    parityWeights (rootWeight hedges ranking fixed bottom distinguished false
        (fun _ => none) keep flip) ≠
      parityWeights (rootWeight hedges ranking fixed bottom distinguished true
        (fun _ => none) keep flip) := by
  obtain ⟨w, mem, on⟩ := exists_world_all_enabled hedges ranking fixed target
  have difference := raw_even_weights_differ bottom distinguished connected (enabled hedges)
    (worlds hedges ranking fixed) w mem on
  intro eq
  simp only [rootWeight, noisyRootMixture, parity_weights_noise_all] at eq
  have rawEq := noise_all_injective keep flip biased _ eq
  exact Nat.ne_of_lt difference (congrFun rawEq (fun _ => false)).symm

theorem parity_weights_total (law : WeightTable (Fin roots)) :
    parityWeights law (fun _ => false) + parityWeights law (fun _ => true) =
      totalRootWeight law := by
  unfold parityWeights totalRootWeight
  rw [← sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro out _
  cases rootParity out <;> simp

/-- Odd root parity has a different weight in the two models with the same
denominator. -/
theorem target_odd_weight_differs (ranking : Rankings hedges) (fixed : Intervention hedges)
    (target : HasEnabledWorld hedges fixed)
    (bottom : Bottom roots bottomEdges) (distinguished : Fin roots)
    (connected : ∀ r, Walk bottom r distinguished) (keep flip : Nat) (biased : keep ≠ flip) :
    parityWeights (rootWeight hedges ranking fixed bottom distinguished false
        (fun _ => none) keep flip) (fun _ => true) ≠
      parityWeights (rootWeight hedges ranking fixed bottom distinguished true
        (fun _ => none) keep flip) (fun _ => true) := by
  let law := fun model => rootWeight hedges ranking fixed bottom distinguished model
    (fun _ => none) keep flip
  intro odd
  apply target_root_parity_weights_differ hedges ranking fixed target bottom distinguished
    connected keep flip biased
  have equal : totalRootWeight (law false) = totalRootWeight (law true) :=
    (root_weight_total hedges ranking fixed bottom distinguished false _ keep flip).trans
      (root_weight_total hedges ranking fixed bottom distinguished true _ keep flip).symm
  have even : parityWeights (law false) (fun _ => false) =
      parityWeights (law true) (fun _ => false) := by
    have one := parity_weights_total (law false)
    have two := parity_weights_total (law true)
    change parityWeights (law false) (fun _ => true) =
      parityWeights (law true) (fun _ => true) at odd
    omega
  show parityWeights (law false) = parityWeights (law true)
  funext out
  have reindex : (fun _ : Unit => out ()) = out := funext fun _ => rfl
  rw [← reindex]
  cases out () <;> assumption

end

end OpenCausalScience.Papers.LeeEtAl2019.JointSCM
