module
public import OpenCausalScience.Papers.LeeEtAl2019.GeneralIdentifiabilityErratum

/-! # Positive bottom witnesses in the g-identifiability converse

The binary bottom construction of [R-46](https://causalai.net/r46.pdf) §3.1,
Lemmas 4–7, using the root perturbation of [R-46e](https://causalai.net/r46e.pdf).
A bidirected edge has one independent fair bit. An upper assignment determines
which root equations are enabled. An intervention replaces the affected root
equation and suppresses its private noise. Laws below are integer weights with
a common denominator in each regime.

For the non-degenerate case the upper construction must supply, for each
available experiment, a disabled or intervened root for every upper assignment
and support for every free upper value. The target must permit an all-enabled
upper assignment. Those properties of arbitrary hedgelets are separate from
the bottom witness construction.
-/

namespace OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse

@[expose] public section

open GeneralIdentifiabilityErratum

/-- One source per bidirected edge, indexed separately from the vertices. -/
structure Bottom (vertices edges : Nat) where
  left : Fin edges → Fin vertices
  right : Fin edges → Fin vertices

variable {vertices edges : Nat}

def incident (g : Bottom vertices edges) (e : Fin edges) (v : Fin vertices) : Bool :=
  Bool.xor (decide (v = g.left e)) (decide (v = g.right e))

def bottomParity (g : Bottom vertices edges) (bits : BitVec edges)
    (v : Fin vertices) : Bool :=
  xorAll ((List.finRange edges).map fun e => incident g e v && bits.getLsbD e.val)

private theorem xor_map_xor {α : Type} (xs : List α) (f h : α → Bool) :
    xorAll (xs.map fun x => Bool.xor (f x) (h x)) =
      Bool.xor (xorAll (xs.map f)) (xorAll (xs.map h)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, xorAll, ih]
    simp only [Bool.xor_assoc]
    exact congrArg (Bool.xor (f x)) (Bool.xor_left_comm _ _ _)

private theorem xor_const_false {α : Type} (xs : List α) :
    xorAll (xs.map fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, xorAll, Bool.false_xor, ih]

private theorem xor_map_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Bool) :
    xorAll (xs.map fun x => xorAll (ys.map (f x))) =
      xorAll (ys.map fun y => xorAll (xs.map fun x => f x y)) := by
  induction xs with
  | nil => simpa only [List.map_nil, xorAll] using (xor_const_false ys).symm
  | cons x xs ih =>
    simp only [List.map_cons, xorAll, ih, xor_map_xor]

private theorem xor_one_hot {α : Type} [DecidableEq α] (xs : List α) (a : α)
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

private theorem xor_all_vertices (g : Bottom vertices edges) (bits : BitVec edges) :
    xorAll ((List.finRange vertices).map (bottomParity g bits)) = false := by
  unfold bottomParity
  rw [xor_map_swap]
  apply (congrArg xorAll (List.map_congr_left (g := fun _ => false) ?_)).trans
    (xor_const_false _)
  intro e _
  simp only [incident, Bool.and_xor_distrib_right, xor_map_xor]
  rw [xor_one_hot _ _ (List.nodup_finRange _), xor_one_hot _ _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

private theorem bottom_parity_xor (g : Bottom vertices edges) (bits mask : BitVec edges)
    (v : Fin vertices) :
    bottomParity g (bits ^^^ mask) v =
      Bool.xor (bottomParity g bits v) (bottomParity g mask v) := by
  simp only [bottomParity, BitVec.getLsbD_xor, Bool.and_xor_distrib_left, xor_map_xor]

private theorem bottom_parity_one (g : Bottom vertices edges) (e : Fin edges)
    (v : Fin vertices) : bottomParity g (BitVec.twoPow edges e.val) v = incident g e v := by
  have bits (f : Fin edges) : (BitVec.twoPow edges e.val).getLsbD f.val = decide (f = e) := by
    simp only [BitVec.getLsbD_twoPow, e.isLt, decide_true, Bool.true_and, Fin.val_inj, eq_comm]
  unfold bottomParity
  rw [show (List.finRange edges).map
      (fun f => incident g f v && (BitVec.twoPow edges e.val).getLsbD f.val) =
      (List.finRange edges).map (fun f => decide (f = e) && incident g e v) by
    apply List.map_congr_left
    intro f _
    rw [bits]
    by_cases h : f = e <;> simp [h]]
  rw [xor_one_hot _ _ (List.nodup_finRange _)]
  simp

/-- A bidirected walk, including length zero when the distinguished root is
itself disabled or intervened. Edges can be traversed in either direction. -/
inductive Walk (g : Bottom vertices edges) : Fin vertices → Fin vertices → Prop
  | refl (v) : Walk g v v
  | forward (e) {v} : Walk g (g.right e) v → Walk g (g.left e) v
  | backward (e) {v} : Walk g (g.left e) v → Walk g (g.right e) v

/-- Flipping the edge bits along a walk changes the parity at its endpoints
only. Traversing an edge twice cancels its two flips. -/
theorem walk_mask (g : Bottom vertices edges) {start stop : Fin vertices}
    (walk : Walk g start stop) :
    ∃ mask : BitVec edges, ∀ v, bottomParity g mask v =
      Bool.xor (decide (v = start)) (decide (v = stop)) := by
  induction walk with
  | refl v =>
    refine ⟨0, fun w => ?_⟩
    simp [bottomParity, xor_const_false]
  | forward e _ ih =>
    obtain ⟨mask, maskSpec⟩ := ih
    refine ⟨BitVec.twoPow edges e.val ^^^ mask, fun w => ?_⟩
    rw [bottom_parity_xor, bottom_parity_one, maskSpec, incident]
    simp
  | backward e _ ih =>
    obtain ⟨mask, maskSpec⟩ := ih
    refine ⟨BitVec.twoPow edges e.val ^^^ mask, fun w => ?_⟩
    rw [bottom_parity_xor, bottom_parity_one, maskSpec, incident, Bool.xor_comm
      (decide (w = g.left e)) (decide (w = g.right e))]
    simp

private def flipWorld (mask : BitVec edges) (u : Fin (2 ^ edges)) : Fin (2 ^ edges) :=
  (BitVec.ofFin u ^^^ mask).toFin

private theorem flip_world_twice (mask : BitVec edges) (u : Fin (2 ^ edges)) :
    flipWorld mask (flipWorld mask u) = u := by
  simp only [flipWorld, BitVec.ofFin_toFin, BitVec.xor_assoc, BitVec.xor_self,
    BitVec.xor_zero, BitVec.toFin_ofFin]

private theorem uniform_worlds_perm (mask : BitVec edges) :
    ((List.finRange (2 ^ edges)).map (flipWorld mask)).Perm (List.finRange (2 ^ edges)) := by
  have nodup := List.nodup_finRange (2 ^ edges)
  have mapped : ((List.finRange (2 ^ edges)).map (flipWorld mask)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp (R := fun a b : Fin (2 ^ edges) => a ≠ b) ?_ nodup
    intro a b ne eq
    exact ne ((flip_world_twice mask a).symm.trans
      ((congrArg (flipWorld mask) eq).trans (flip_world_twice mask b)))
  apply (List.perm_ext_iff_of_nodup mapped nodup).2
  intro u
  constructor
  · intro _
    exact List.mem_finRange u
  · intro _
    exact List.mem_map.mpr ⟨flipWorld mask u, List.mem_finRange _, flip_world_twice mask u⟩

/-- The pair differs at one root. Its parity is complemented in the second
model only when its own equation is in effect and enabled. -/
def rootOutcome (g : Bottom vertices edges) (distinguished : Fin vertices) (secondModel : Bool)
    (fixed : Fin vertices → Option Bool) (enabled : Fin vertices → Bool)
    (bits : BitVec edges) (v : Fin vertices) : Bool :=
  match fixed v with
  | some value => value
  | none => enabled v && Bool.xor (bottomParity g bits v)
      (secondModel && decide (v = distinguished))

def rawRootLaw (g : Bottom vertices edges) (distinguished : Fin vertices) (secondModel : Bool)
    (fixed : Fin vertices → Option Bool) (enabled : Fin vertices → Bool) :
    WeightTable (Fin vertices) :=
  fun out => (List.finRange (2 ^ edges)).countP fun u =>
    (List.finRange vertices).all fun v =>
      rootOutcome g distinguished secondModel fixed enabled (BitVec.ofFin u) v == out v

/-- R-46 Lemma 4 and Corollary 1 at fixed upper inputs. One disabled or
intervened root can absorb the distinguished-root flip. -/
theorem raw_root_laws_equal (g : Bottom vertices edges) (distinguished hidden : Fin vertices)
    (path : Walk g hidden distinguished)
    (fixed : Fin vertices → Option Bool) (enabled : Fin vertices → Bool)
    (hiddenEq : fixed hidden ≠ none ∨ enabled hidden = false) :
    rawRootLaw g distinguished false fixed enabled =
      rawRootLaw g distinguished true fixed enabled := by
  obtain ⟨mask, maskSpec⟩ := walk_mask g path
  have agreement (u : Fin (2 ^ edges)) (v : Fin vertices) :
      rootOutcome g distinguished true fixed enabled (BitVec.ofFin (flipWorld mask u)) v =
        rootOutcome g distinguished false fixed enabled (BitVec.ofFin u) v := by
    unfold rootOutcome
    cases hv : fixed v with
    | some val => rfl
    | none =>
      simp only [flipWorld, BitVec.ofFin_toFin, bottom_parity_xor, maskSpec, Bool.true_and,
        Bool.false_and, Bool.xor_false]
      by_cases same : v = hidden
      · subst v
        rcases hiddenEq with no | disabled
        · exact False.elim (no hv)
        · simp [disabled]
      · simp [same]
  funext out
  unfold rawRootLaw
  have perm := (uniform_worlds_perm mask).countP_eq
    (fun u => (List.finRange vertices).all fun v =>
      rootOutcome g distinguished true fixed enabled (BitVec.ofFin u) v == out v)
  simpa only [List.countP_map, Function.comp_def, agreement] using perm

/-- The noise acts at non-intervened roots only, as required by replacement
of the entire structural equation under an intervention. -/
def freeRoots (fixed : Fin vertices → Option Bool) : List (Fin vertices) :=
  (List.finRange vertices).filter fun v => (fixed v).isNone

def noisyRootLaw (g : Bottom vertices edges) (distinguished : Fin vertices) (secondModel : Bool)
    (fixed : Fin vertices → Option Bool) (enabled : Fin vertices → Bool) (keep flip : Nat) :
    WeightTable (Fin vertices) :=
  noiseAll keep flip (freeRoots fixed) (rawRootLaw g distinguished secondModel fixed enabled)

/-- Every output of the un-intervened roots has positive probability after
private noise, for either model and every upper configuration. -/
theorem noisy_root_law_positive (g : Bottom vertices edges) (distinguished : Fin vertices)
    (secondModel : Bool) (fixed : Fin vertices → Option Bool) (enabled : Fin vertices → Bool)
    (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip)
    (out : Fin vertices → Bool)
    (consistent : ∀ v value, fixed v = some value → out v = value) :
    0 < noisyRootLaw g distinguished secondModel fixed enabled keep flip out := by
  let raw := rootOutcome g distinguished secondModel fixed enabled 0
  apply noise_all_pos keep flip keepPositive flipPositive (freeRoots fixed) _ raw
  · apply List.countP_pos_iff.mpr
    refine ⟨(0 : BitVec edges).toFin, List.mem_finRange _, ?_⟩
    apply List.all_eq_true.mpr
    intro v _
    apply beq_iff_eq.mpr
    rw [BitVec.ofFin_toFin]
  · intro v absent
    cases h : fixed v with
    | none => exact False.elim (absent (by simp [freeRoots, h]))
    | some value => simpa [raw, rootOutcome, h] using (consistent _ _ h).symm

private theorem xor_second_model_all_enabled (g : Bottom vertices edges)
    (distinguished : Fin vertices) (bits : BitVec edges) :
    xorAll ((List.finRange vertices).map
      (rootOutcome g distinguished true (fun _ => none) (fun _ => true) bits)) = true := by
  change xorAll ((List.finRange vertices).map fun v =>
    Bool.xor (bottomParity g bits v) (decide (v = distinguished))) = true
  simp only [xor_map_xor, xor_all_vertices, Bool.false_xor]
  simpa only [Bool.and_true, List.mem_finRange, decide_true, Bool.true_and] using
    xor_one_hot (List.finRange vertices) distinguished (List.nodup_finRange _) true

/-- When all roots are enabled without root intervention, the all-zero output
has positive raw weight in the first model and zero raw weight in the second.
This is the parity separation underlying Lemmas 5 and 7. -/
theorem all_enabled_zero_weights (g : Bottom vertices edges) (distinguished : Fin vertices) :
    0 < rawRootLaw g distinguished false (fun _ => none) (fun _ => true) (fun _ => false) ∧
    rawRootLaw g distinguished true (fun _ => none) (fun _ => true) (fun _ => false) = 0 := by
  constructor
  · apply List.countP_pos_iff.mpr
    refine ⟨(0 : BitVec edges).toFin, List.mem_finRange _, ?_⟩
    simp [rootOutcome, bottomParity, xor_const_false]
  · apply List.countP_eq_zero.mpr
    intro u _ allZero
    have outputZero : ∀ v, rootOutcome g distinguished true (fun _ => none) (fun _ => true)
        (BitVec.ofFin u) v = false := by
      intro v
      simpa only [beq_iff_eq] using List.all_eq_true.mp allZero v (List.mem_finRange v)
    have mapZero := List.map_congr_left (l := List.finRange vertices)
      (fun v _ => outputZero v)
    have parity := xor_second_model_all_enabled g distinguished (BitVec.ofFin u)
    rw [mapZero, xor_const_false] at parity
    contradiction

/-- The upper assignment list represents independent upper exogenous worlds.
Filtering it by a given observed upper output gives the corresponding slice
of the joint upper and bottom law, retaining its absolute weight. -/
def rawRootMixture {Context : Type} (g : Bottom vertices edges) (distinguished : Fin vertices)
    (secondModel : Bool) (fixed : Fin vertices → Option Bool) (enabled : Context → Fin vertices → Bool)
    (contexts : List Context) : WeightTable (Fin vertices) :=
  fun out => (contexts.map fun ctx => rawRootLaw g distinguished secondModel fixed (enabled ctx) out).sum

def noisyRootMixture {Context : Type} (g : Bottom vertices edges) (distinguished : Fin vertices)
    (secondModel : Bool) (fixed : Fin vertices → Option Bool) (enabled : Context → Fin vertices → Bool)
    (contexts : List Context) (keep flip : Nat) : WeightTable (Fin vertices) :=
  noiseAll keep flip (freeRoots fixed) (rawRootMixture g distinguished secondModel fixed enabled contexts)

/-- If every retained upper world disables or intervenes on some root, the
two models agree on this slice of the joint law, including private noise. -/
theorem supplied_slice_agreement {Context : Type} (g : Bottom vertices edges)
    (distinguished : Fin vertices) (connected : ∀ v, Walk g v distinguished)
    (fixed : Fin vertices → Option Bool) (enabled : Context → Fin vertices → Bool)
    (contexts : List Context) (keep flip : Nat)
    (blocked : ∀ ctx ∈ contexts, ∃ v, fixed v ≠ none ∨ enabled ctx v = false) :
    noisyRootMixture g distinguished false fixed enabled contexts keep flip =
      noisyRootMixture g distinguished true fixed enabled contexts keep flip := by
  have raw : rawRootMixture g distinguished false fixed enabled contexts =
      rawRootMixture g distinguished true fixed enabled contexts := by
    funext out
    unfold rawRootMixture
    apply congrArg List.sum
    apply List.map_congr_left
    intro ctx mem
    obtain ⟨v, hidden⟩ := blocked ctx mem
    exact congrFun (raw_root_laws_equal g distinguished v (connected v) fixed (enabled ctx) hidden) out
  simp only [noisyRootMixture, raw]

private theorem sum_map_positive {α : Type} (xs : List α) (f : α → Nat) {x : α}
    (mem : x ∈ xs) (positive : 0 < f x) : 0 < (xs.map f).sum := by
  exact List.sum_pos_iff_exists_pos_nat.mpr ⟨f x, List.mem_map.mpr ⟨x, mem, rfl⟩, positive⟩

private theorem sum_map_strict {α : Type} (xs : List α) (f g : α → Nat) {x : α}
    (le : ∀ y ∈ xs, f y ≤ g y) (mem : x ∈ xs) (strict : f x < g x) :
    (xs.map f).sum < (xs.map g).sum := by
  have sumLe {ys : List α} (h : ∀ y ∈ ys, f y ≤ g y) :
      (ys.map f).sum ≤ (ys.map g).sum := by
    induction ys with
    | nil => exact Nat.le_refl _
    | cons y ys ih =>
      exact Nat.add_le_add (h y (by simp)) (ih fun w hw => h w (List.mem_cons_of_mem y hw))
  induction xs with
  | nil => simp at mem
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    have tail : ∀ w ∈ ys, f w ≤ g w := fun w hw => le w (List.mem_cons_of_mem y hw)
    rcases List.mem_cons.mp mem with same | later
    · exact Nat.add_lt_add_of_lt_of_le (same ▸ strict) (sumLe tail)
    · exact Nat.add_lt_add_of_le_of_lt (le y (by simp)) (ih tail later)

/-- Every nonempty upper slice has positive mass at every compatible bottom
assignment in both perturbed models. An empty slice is exactly the separate
upper-support issue. -/
theorem supplied_slice_positive {Context : Type} (g : Bottom vertices edges)
    (distinguished : Fin vertices) (secondModel : Bool)
    (fixed : Fin vertices → Option Bool) (enabled : Context → Fin vertices → Bool)
    (contexts : List Context) (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip)
    (ctx : Context) (mem : ctx ∈ contexts) (out : Fin vertices → Bool)
    (consistent : ∀ v value, fixed v = some value → out v = value) :
    0 < noisyRootMixture g distinguished secondModel fixed enabled contexts keep flip out := by
  let raw := rootOutcome g distinguished secondModel fixed (enabled ctx) 0
  apply noise_all_pos keep flip keepPositive flipPositive (freeRoots fixed) _ raw
  · apply sum_map_positive contexts _ mem
    apply List.countP_pos_iff.mpr
    refine ⟨(0 : BitVec edges).toFin, List.mem_finRange _, ?_⟩
    apply List.all_eq_true.mpr
    intro v _
    apply beq_iff_eq.mpr
    rw [BitVec.ofFin_toFin]
  · intro v absent
    cases h : fixed v with
    | none => exact False.elim (absent (by simp [freeRoots, h]))
    | some value => simpa [raw, rootOutcome, h] using (consistent _ _ h).symm

/-- With no root intervention and at least one all-enabled target world,
the raw all-zero weights differ. A common biased channel then leaves the
target tables distinguishable. -/
theorem target_laws_differ {Context : Type} (g : Bottom vertices edges)
    (distinguished : Fin vertices) (connected : ∀ v, Walk g v distinguished)
    (enabled : Context → Fin vertices → Bool) (contexts : List Context) (keep flip : Nat)
    (biased : keep ≠ flip) (ctx : Context) (mem : ctx ∈ contexts)
    (allEnabled : ∀ v, enabled ctx v = true) :
    noisyRootMixture g distinguished false (fun _ => none) enabled contexts keep flip ≠
      noisyRootMixture g distinguished true (fun _ => none) enabled contexts keep flip := by
  have allEnabledWeights := all_enabled_zero_weights g distinguished
  have compare (w : Context) :
      rawRootLaw g distinguished true (fun _ => none) (enabled w) (fun _ => false) ≤
        rawRootLaw g distinguished false (fun _ => none) (enabled w) (fun _ => false) := by
    classical
    by_cases all : ∀ v, enabled w v = true
    · have gate : enabled w = fun _ => true := funext all
      simp only [gate, allEnabledWeights.2, Nat.zero_le]
    · obtain ⟨v, hidden⟩ := Classical.not_forall.mp all
      have off : enabled w v = false := by cases h : enabled w v <;> simp_all
      exact Nat.le_of_eq (congrFun
        (raw_root_laws_equal g distinguished v (connected v) _ _ (Or.inr off)) _).symm
  have strict :
      rawRootMixture g distinguished true (fun _ => none) enabled contexts (fun _ => false) <
        rawRootMixture g distinguished false (fun _ => none) enabled contexts (fun _ => false) := by
    apply sum_map_strict contexts _ _ (fun w _ => compare w) mem
    have gate : enabled ctx = fun _ => true := funext allEnabled
    simpa only [gate, allEnabledWeights.2] using allEnabledWeights.1
  intro eq
  have rawEq := noise_all_injective keep flip biased _ eq
  exact Nat.ne_of_lt strict (congrFun rawEq (fun _ => false)).symm

/-- The positive witnesses for the degenerate thicket, R-46 Lemmas 6–7
with R-46e noise. The models agree for every nonempty root intervention and
every imposed value. Every configuration of the remaining roots has positive
mass. Their observational laws differ. The upper world has one value and
enables every root, so the result needs only the connected bottom graph. -/
theorem degenerate_thicket_witness (g : Bottom vertices edges)
    (distinguished : Fin vertices) (connected : ∀ v, Walk g v distinguished)
    (keep flip : Nat) (keepPositive : 0 < keep) (flipPositive : 0 < flip) (biased : keep ≠ flip) :
    (∀ fixed : Fin vertices → Option Bool, (∃ v, fixed v ≠ none) →
      noisyRootLaw g distinguished false fixed (fun _ => true) keep flip =
        noisyRootLaw g distinguished true fixed (fun _ => true) keep flip ∧
      ∀ (secondModel : Bool) (out : Fin vertices → Bool),
        (∀ v value, fixed v = some value → out v = value) →
        0 < noisyRootLaw g distinguished secondModel fixed (fun _ => true) keep flip out) ∧
    noisyRootLaw g distinguished false (fun _ => none) (fun _ => true) keep flip ≠
      noisyRootLaw g distinguished true (fun _ => none) (fun _ => true) keep flip := by
  constructor
  · intro fixed nonempty
    obtain ⟨v, intervened⟩ := nonempty
    constructor
    · unfold noisyRootLaw
      rw [raw_root_laws_equal g distinguished v (connected v) fixed _ (Or.inl intervened)]
    · intro secondModel out consistent
      exact noisy_root_law_positive g distinguished secondModel fixed _ keep flip
        keepPositive flipPositive out consistent
  · have difference := target_laws_differ g distinguished connected (Context := Unit)
      (fun _ _ => true) [()] keep flip biased () (List.mem_singleton.mpr rfl) (fun _ => rfl)
    exact difference

/-- Inputs to the indicators in R-46 (2)–(3). In the complemented-vector
notation, the zero tests require that every input bit be one. -/
structure GateInputs (vertices : Nat) where
  frontiers : Fin vertices → List Bool
  crossing : Fin vertices → List Bool

def GateInputs.enabled (inputs : GateInputs vertices) (v : Fin vertices) : Bool :=
  (inputs.frontiers v).all id && (inputs.crossing v).all id

/-- Data of an intact hedge at one upper exogenous assignment. The parity
is the conclusion of R-46 Lemma 2 before the negation. The two coverage
conditions connect the hedge's bits to the tested root inputs. -/
structure IntactHedgeBits (inputs : GateInputs vertices) where
  crossing : List Bool
  before : List Bool
  selected : Bool
  after : List Bool
  parity : xorAll (before ++ selected :: after) = xorAll crossing
  crossingTested : ∀ b ∈ crossing, ∃ v, b ∈ inputs.crossing v
  frontierTested : ∀ b ∈ correctedFrontiers crossing.length before selected after,
    ∃ v, b ∈ inputs.frontiers v

private theorem false_all_if_false_mem (xs : List Bool) (mem : false ∈ xs) :
    xs.all id = false := by
  cases h : xs.all id with
  | false => rfl
  | true => exact Bool.noConfusion (List.all_eq_true.mp h false mem)

/-- The R-46e crossing and frontier prescription disables at least one root
when the intact hedge's pre-negation parity and root input coverage hold. -/
theorem root_disabled_by_intact_hedge {inputs : GateInputs vertices}
    (hedge : IntactHedgeBits inputs) : ∃ v, inputs.enabled v = false := by
  by_cases crossingZero : false ∈ hedge.crossing
  · obtain ⟨v, h⟩ := hedge.crossingTested false crossingZero
    refine ⟨v, ?_⟩
    simp only [GateInputs.enabled, false_all_if_false_mem _ h, Bool.and_false]
  · have allTrue (xs : List Bool) (noZero : false ∉ xs) :
        xorAll xs = countParity xs.length := by
      induction xs with
      | nil => rfl
      | cons bit xs ih =>
        cases bit with
        | false => exact False.elim (noZero List.mem_cons_self)
        | true =>
          have tail : false ∉ xs := fun h => noZero (List.mem_cons_of_mem true h)
          simp only [xorAll, countParity, List.length_cons, Bool.true_xor, ih tail]
    have before : xorAll (hedge.before ++ hedge.selected :: hedge.after) =
        countParity hedge.crossing.length := hedge.parity.trans (allTrue _ crossingZero)
    obtain ⟨v, h⟩ := hedge.frontierTested false
      (corrected_frontiers_contain_false _ _ _ _ before)
    refine ⟨v, ?_⟩
    simp only [GateInputs.enabled, false_all_if_false_mem _ h, Bool.false_and]

/-- When a supplied regime avoids the roots, an intact hedge with the
required parity and input coverage suffices for agreement at that upper
world. If the regime intervenes on a root, no hedge is needed there. -/
theorem supplied_slice_agreement_from_hedges {Context : Type} (g : Bottom vertices edges)
    (distinguished : Fin vertices) (connected : ∀ v, Walk g v distinguished)
    (fixed : Fin vertices → Option Bool) (inputs : Context → GateInputs vertices)
    (contexts : List Context) (keep flip : Nat)
    (supplied : ∀ ctx ∈ contexts, (∃ v, fixed v ≠ none) ∨ Nonempty (IntactHedgeBits (inputs ctx))) :
    noisyRootMixture g distinguished false fixed (fun ctx => (inputs ctx).enabled) contexts
      keep flip =
    noisyRootMixture g distinguished true fixed (fun ctx => (inputs ctx).enabled) contexts
      keep flip := by
  apply supplied_slice_agreement g distinguished connected
  intro ctx mem
  rcases supplied ctx mem with ⟨v, fixedValue⟩ | intact
  · exact ⟨v, Or.inl fixedValue⟩
  · obtain ⟨hedge⟩ := intact
    obtain ⟨v, disabled⟩ := root_disabled_by_intact_hedge hedge
    exact ⟨v, Or.inr disabled⟩

end

end OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse
