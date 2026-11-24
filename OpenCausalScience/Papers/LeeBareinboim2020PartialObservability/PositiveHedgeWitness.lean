module
public import OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.HedgeNoise
public import OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse

/-! # Positive projected hedge distributions

Corrected R-58, Appendix B, Lemma 7. A primitive coin or private noise
has an XOR effect on the projected coordinates. The mask gives the
coordinates reached, after directed propagation, by that primitive bit.
Finite tables use integer weights with a common normalizing denominator.
-/

namespace OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.PositiveHedgeWitness

@[expose] public section

open HedgeNoise
open OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse (Bottom Walk)

abbrev JointWeights (coordinates : Nat) := BitVec coordinates → Int

structure Channel (coordinates : Nat) where
  effect : BitVec coordinates
  weights : BitWeights

variable {coordinates : Nat}

def Channel.apply (ch : Channel coordinates) (law : JointWeights coordinates) :
    JointWeights coordinates := fun out =>
  ch.weights.zero * law out + ch.weights.one * law (out ^^^ ch.effect)

def point (location : BitVec coordinates) : JointWeights coordinates :=
  fun out => if out = location then 1 else 0

def run (channels : List (Channel coordinates)) (location : BitVec coordinates) :
    JointWeights coordinates :=
  channels.foldr Channel.apply (point location)

def Channel.Fair (ch : Channel coordinates) : Prop := ch.weights.zero = ch.weights.one

def Channel.Positive (ch : Channel coordinates) : Prop :=
  0 < ch.weights.zero ∧ 0 < ch.weights.one

def Invariant (law : JointWeights coordinates) (mask : BitVec coordinates) : Prop :=
  ∀ out, law (out ^^^ mask) = law out

private theorem applying_preserves_invariance (ch : Channel coordinates)
    (law : JointWeights coordinates) (mask : BitVec coordinates) (invariant : Invariant law mask) :
    Invariant (ch.apply law) mask := by
  intro out
  unfold Channel.apply
  rw [invariant out, BitVec.xor_assoc, BitVec.xor_comm mask ch.effect, ← BitVec.xor_assoc, invariant]

private theorem fair_channel_invariance (ch : Channel coordinates) (law : JointWeights coordinates)
    (fair : ch.Fair) : Invariant (ch.apply law) ch.effect := by
  intro out
  simp only [Channel.apply, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [show ch.weights.zero = ch.weights.one from fair, Int.add_comm]

theorem run_invariant_of_fair_mem (channels : List (Channel coordinates))
    (location : BitVec coordinates) (ch : Channel coordinates) (mem : ch ∈ channels)
    (fair : ch.Fair) : Invariant (run channels location) ch.effect := by
  induction channels with
  | nil => simp at mem
  | cons curr rest ih =>
    change Invariant (curr.apply (run rest location)) ch.effect
    rcases List.mem_cons.mp mem with same | later
    · subst curr
      exact fair_channel_invariance ch _ fair
    · exact applying_preserves_invariance curr _ _ (ih later)

/-- Masks produced by flipping any collection of the fair primitive coins. -/
inductive Generated (channels : List (Channel coordinates)) : BitVec coordinates → Prop
  | zero : Generated channels 0
  | coin (ch : Channel coordinates) : ch ∈ channels → ch.Fair → Generated channels ch.effect
  | xor {a b} : Generated channels a → Generated channels b → Generated channels (a ^^^ b)

theorem run_invariant_of_generated (channels : List (Channel coordinates))
    (location : BitVec coordinates) {mask : BitVec coordinates} (generated : Generated channels mask) :
    Invariant (run channels location) mask := by
  induction generated with
  | zero => intro out; simp
  | coin ch mem fair => exact run_invariant_of_fair_mem channels location ch mem fair
  | xor _ _ ia ib => intro out; rw [← BitVec.xor_assoc, ib, ia]

/-- XOR of the selected root coordinates, viewed as a linear Boolean map. -/
structure Parity (coordinates : Nat) where
  value : BitVec coordinates → Bool
  zero : value 0 = false
  xor : ∀ a b, value (a ^^^ b) = Bool.xor (value a) (value b)

def ConstantOnParity (parity : Parity coordinates) (law : JointWeights coordinates) : Prop :=
  ∀ a b, parity.value a = parity.value b → law a = law b

/-- Every output pair of the same root parity is related by flipping fair
coins when those coins generate the kernel of the root parity. -/
theorem constant_on_parity_of_fair_masks (channels : List (Channel coordinates))
    (location : BitVec coordinates) (parity : Parity coordinates)
    (covers : ∀ mask, parity.value mask = false → Generated channels mask) :
    ConstantOnParity parity (run channels location) := by
  intro a b same
  have even : parity.value (a ^^^ b) = false := by rw [parity.xor, same, Bool.xor_self]
  have invariant := run_invariant_of_generated channels location (covers _ even) a
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using invariant.symm

def cellTotal (law : JointWeights coordinates) : Int :=
  ((List.finRange (2 ^ coordinates)).map fun u => law (BitVec.ofFin u)).sum

def parityCell (parity : Parity coordinates) (event : Bool) (law : JointWeights coordinates) : Int :=
  cellTotal fun out => if parity.value out = event then law out else 0

def parityLaw (parity : Parity coordinates) (law : JointWeights coordinates) : BitWeights :=
  ⟨parityCell parity false law, parityCell parity true law⟩

private theorem map_finRange_xor_perm (mask : BitVec coordinates) :
    ((List.finRange (2 ^ coordinates)).map fun u => (BitVec.ofFin u ^^^ mask).toFin).Perm
      (List.finRange (2 ^ coordinates)) := by
  let flip := fun u : Fin (2 ^ coordinates) => (BitVec.ofFin u ^^^ mask).toFin
  have involutive (u : Fin (2 ^ coordinates)) : flip (flip u) = u := by
    simp only [flip, BitVec.ofFin_toFin, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, BitVec.toFin_ofFin]
  apply List.perm_ext_iff_of_nodup ?_ (List.nodup_finRange _) |>.mpr
  · intro u
    constructor
    · intro _
      exact List.mem_finRange u
    · intro _
      exact List.mem_map.mpr ⟨flip u, List.mem_finRange _, involutive u⟩
  · unfold List.Nodup
    rw [List.pairwise_map]
    exact List.Pairwise.imp (R := fun a b : Fin (2 ^ coordinates) => a ≠ b)
      (fun {a b} ne eq => ne ((involutive a).symm.trans ((congrArg flip eq).trans (involutive b))))
      (List.nodup_finRange _)

private theorem sum_int_of_perm {xs ys : List Int} (perm : xs.Perm ys) : xs.sum = ys.sum := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem cell_total_shift (mask : BitVec coordinates) (law : JointWeights coordinates) :
    cellTotal (fun out => law (out ^^^ mask)) = cellTotal law := by
  have perm := (map_finRange_xor_perm mask).map fun u => law (BitVec.ofFin u)
  simpa only [cellTotal, List.map_map, Function.comp_def, BitVec.ofFin_toFin] using sum_int_of_perm perm

private theorem cell_total_linear (a b : Int) (p q : JointWeights coordinates) :
    cellTotal (fun out => a * p out + b * q out) = a * cellTotal p + b * cellTotal q := by
  unfold cellTotal
  generalize List.finRange (2 ^ coordinates) = xs
  induction xs with
  | nil => simp
  | cons u xs ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]; omega

theorem parity_cell_apply (parity : Parity coordinates) (event : Bool)
    (ch : Channel coordinates) (law : JointWeights coordinates) :
    parityCell parity event (ch.apply law) =
      ch.weights.zero * parityCell parity event law +
        ch.weights.one * parityCell parity (Bool.xor event (parity.value ch.effect)) law := by
  have eq : (fun out => if parity.value out = event then ch.apply law out else 0) =
      fun out => ch.weights.zero * (if parity.value out = event then law out else 0) +
        ch.weights.one * (if parity.value (out ^^^ ch.effect) =
          Bool.xor event (parity.value ch.effect) then law (out ^^^ ch.effect) else 0) := by
    funext out
    rw [parity.xor]
    by_cases same : parity.value out = event <;> simp [Channel.apply, same]
  unfold parityCell
  rw [eq, cell_total_linear]
  have shift := cell_total_shift ch.effect (fun out =>
    if parity.value out = Bool.xor event (parity.value ch.effect) then law out else 0)
  congr 1
  exact congrArg (Int.mul ch.weights.one) shift

theorem parity_law_apply (parity : Parity coordinates) (ch : Channel coordinates)
    (law : JointWeights coordinates) :
    parityLaw parity (ch.apply law) =
      xorWeights (if parity.value ch.effect then ch.weights else ⟨total ch.weights, 0⟩)
        (parityLaw parity law) := by
  ext <;> cases h : parity.value ch.effect <;>
    simp [parityLaw, xorWeights, parity_cell_apply, h, total, Int.add_mul]

private theorem parity_cell_eq_count_mul (parity : Parity coordinates) (law : JointWeights coordinates)
    (constant : ConstantOnParity parity law) (out : BitVec coordinates) :
    parityCell parity (parity.value out) law =
      cellTotal (fun w => if parity.value w = parity.value out then 1 else 0) * law out := by
  unfold parityCell cellTotal
  generalize List.finRange (2 ^ coordinates) = xs
  induction xs with
  | nil => simp
  | cons u xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Int.add_mul]
    by_cases h : parity.value (BitVec.ofFin u) = parity.value out
    · simp [h, constant _ _ h]
    · simp [h]

private theorem cell_count_positive (parity : Parity coordinates) (out : BitVec coordinates) :
    0 < cellTotal (fun w => if parity.value w = parity.value out then 1 else 0) := by
  have member : out.toFin ∈ List.finRange (2 ^ coordinates) := List.mem_finRange _
  unfold cellTotal
  generalize List.finRange (2 ^ coordinates) = xs at member ⊢
  have nonnegative (ys : List (Fin (2 ^ coordinates))) : 0 ≤
      (ys.map fun u => if parity.value (BitVec.ofFin u) = parity.value out then 1 else (0 : Int)).sum := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      split <;> omega
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp member with h | tail
    · subst y
      simpa using Int.add_pos_of_pos_of_nonneg (by decide : (0 : Int) < 1) (nonnegative ys)
    · have positive := ih tail
      simp only at positive ⊢
      split <;> omega

/-- The two parity weights completely determine a joint law constant on
the parity classes. No appeal to an unformalized Fourier inversion. -/
theorem joint_eq_of_parity_law (parity : Parity coordinates) (a b : JointWeights coordinates)
    (aConstant : ConstantOnParity parity a) (bConstant : ConstantOnParity parity b)
    (equal : parityLaw parity a = parityLaw parity b) : a = b := by
  funext out
  have sameCell : parityCell parity (parity.value out) a = parityCell parity (parity.value out) b := by
    cases h : parity.value out
    · exact congrArg BitWeights.zero equal
    · exact congrArg BitWeights.one equal
  rw [parity_cell_eq_count_mul parity a aConstant, parity_cell_eq_count_mul parity b bConstant]
    at sameCell
  exact Int.eq_of_mul_eq_mul_left (Int.ne_of_gt (cell_count_positive parity out)) sameCell

def Parity.project (parity : Parity coordinates) (ch : Channel coordinates) : BitWeights :=
  if parity.value ch.effect then ch.weights else ⟨total ch.weights, 0⟩

private theorem weighted_singleton (xs : List (Fin (2 ^ coordinates))) (unique : xs.Nodup)
    (target : Fin (2 ^ coordinates)) (value : Int) :
    (xs.map fun x => if x = target then value else 0).sum =
      if target ∈ xs then value else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨notMem, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases equal : x = target
    · subst x
      simp [ih tailUnique, notMem]
    · simp [ih tailUnique, equal, Ne.symm equal]

theorem parity_law_run_at_zero (parity : Parity coordinates) (channels : List (Channel coordinates)) :
    parityLaw parity (run channels 0) = parityWeights (channels.map parity.project) := by
  induction channels with
  | nil =>
    have mass (e : Bool) : parityCell parity e (point 0) = if e = false then 1 else 0 := by
      let target := (0 : BitVec coordinates).toFin
      have cell (x : Fin (2 ^ coordinates)) :
          (if parity.value (BitVec.ofFin x) = e then point 0 (BitVec.ofFin x) else 0) =
            if x = target then (if e = false then 1 else 0) else 0 := by
        by_cases h : x = target
        · subst x
          rw [show BitVec.ofFin target = (0 : BitVec coordinates) from BitVec.ofFin_toFin _]
          rw [parity.zero]
          cases e <;> simp [point]
        · have nonzero : BitVec.ofFin x ≠ (0 : BitVec coordinates) := by
            intro eq
            exact h (congrArg BitVec.toFin eq)
          simp only [h, nonzero, point, ite_false, ite_self]
      unfold parityCell cellTotal
      rw [List.map_congr_left (fun x _ => cell x), weighted_singleton _ (List.nodup_finRange _)]
      simp
    ext
    · exact mass false
    · exact mass true
  | cons ch tail ih =>
    simp only [run, List.foldr_cons] at ih ⊢
    rw [parity_law_apply, ih]
    rfl

private theorem run_nonnegative (channels : List (Channel coordinates))
    (location : BitVec coordinates) (weights : ∀ ch ∈ channels, ch.Positive) (out : BitVec coordinates) :
    0 ≤ run channels location out := by
  induction channels generalizing out with
  | nil => simp [run, point]; split <;> omega
  | cons ch tail ih =>
    have pos := weights ch List.mem_cons_self
    have rest : ∀ c ∈ tail, Channel.Positive c := fun c mem => weights c (List.mem_cons_of_mem ch mem)
    exact Int.add_nonneg (Int.mul_nonneg (Int.le_of_lt pos.1) (ih rest out))
      (Int.mul_nonneg (Int.le_of_lt pos.2) (ih rest (out ^^^ ch.effect)))

/-- A mask obtainable by a choice of values for the primitive bits. -/
inductive Emits : List (Channel coordinates) → BitVec coordinates → Prop
  | zero : Emits [] 0
  | skip (ch) {chs mask} : Emits chs mask → Emits (ch :: chs) mask
  | flip (ch) {chs mask} : Emits chs mask → Emits (ch :: chs) (mask ^^^ ch.effect)

/-- Every assignment emitted by positive independent private bits has
strictly positive joint weight. -/
theorem run_positive_of_emits {channels : List (Channel coordinates)}
    {mask : BitVec coordinates} (emitted : Emits channels mask)
    (weights : ∀ ch ∈ channels, ch.Positive) : 0 < run channels 0 mask := by
  induction emitted with
  | zero => simp [run, point]
  | @skip ch tail mask _ ih =>
    have pos := weights ch List.mem_cons_self
    have rest : ∀ c ∈ tail, Channel.Positive c := fun c mem => weights c (List.mem_cons_of_mem ch mem)
    change 0 < ch.weights.zero * run tail 0 mask + ch.weights.one * run tail 0 (mask ^^^ ch.effect)
    exact Int.add_pos_of_pos_of_nonneg (Int.mul_pos pos.1 (ih rest))
      (Int.mul_nonneg (Int.le_of_lt pos.2) (run_nonnegative tail 0 rest _))
  | @flip ch tail mask _ ih =>
    have pos := weights ch List.mem_cons_self
    have rest : ∀ c ∈ tail, Channel.Positive c := fun c mem => weights c (List.mem_cons_of_mem ch mem)
    change 0 < ch.weights.zero * run tail 0 (mask ^^^ ch.effect) +
      ch.weights.one * run tail 0 ((mask ^^^ ch.effect) ^^^ ch.effect)
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact Int.add_pos_of_nonneg_of_pos
      (Int.mul_nonneg (Int.le_of_lt pos.1) (run_nonnegative tail 0 rest _))
      (Int.mul_pos pos.2 (ih rest))

/-- The projected observational distributions coincide and have full
support. `shared` contains the projected weights of the fair coins and
retained noises. `dropped` contains the projected noise weights replaced
by a single independent compensated flip in the second model. -/
theorem equal_positive_observational_laws (parity : Parity coordinates)
    (first second : List (Channel coordinates)) (shared dropped : List BitWeights)
    (firstProjection : first.map parity.project = shared ++ dropped)
    (secondProjection : second.map parity.project = shared ++ [parityWeights dropped])
    (firstFair : ∀ mask, parity.value mask = false → Generated first mask)
    (secondFair : ∀ mask, parity.value mask = false → Generated second mask)
    (weights : ∀ ch ∈ first, ch.Positive) (support : ∀ out, Emits first out) :
    run first 0 = run second 0 ∧ ∀ out, 0 < run first 0 out ∧ 0 < run second 0 out := by
  have compensation : parityWeights (shared ++ dropped) =
      parityWeights (shared ++ [parityWeights dropped]) := by
    rw [compensating_flip_preserves_parity, compensating_flip_preserves_parity]
    simp [parityWeights, xorWeights]
  have equal : run first 0 = run second 0 := by
    apply joint_eq_of_parity_law parity
    · exact constant_on_parity_of_fair_masks first _ parity firstFair
    · exact constant_on_parity_of_fair_masks second _ parity secondFair
    · rw [parity_law_run_at_zero, parity_law_run_at_zero, firstProjection, secondProjection]
      exact compensation
  exact ⟨equal, fun out => ⟨run_positive_of_emits (support out) weights,
    equal ▸ run_positive_of_emits (support out) weights⟩⟩

private theorem prod_int_positive (xs : List Int) (h : ∀ x ∈ xs, 0 < x) : 0 < xs.prod := by
  induction xs with
  | nil => decide
  | cons x xs ih => exact Int.mul_pos (h x List.mem_cons_self) (ih fun y mem =>
      h y (List.mem_cons_of_mem x mem))

private theorem prod_int_eq_zero_of_mem_zero (xs : List Int) (h : (0 : Int) ∈ xs) : xs.prod = 0 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with same | later
    · subst x
      simp
    · simp [ih later]

/-- A primitive fair coin reaching an odd number of target roots forces
model one to be fair. If every projected input of model two has positive
imbalance, its target stays biased after independent biased transfer. -/
theorem target_parities_differ_after_transfer (parity : Parity coordinates)
    (first second : List (Channel coordinates)) (coin : Channel coordinates)
    (present : coin ∈ first) (fair : coin.Fair) (crossesCut : parity.value coin.effect = true)
    (secondBias : ∀ ch ∈ second, 0 < imbalance (parity.project ch))
    (transfer : BitWeights) (transferBias : 0 < imbalance transfer) :
    xorWeights (parityLaw parity (run first 0)) transfer ≠
      xorWeights (parityLaw parity (run second 0)) transfer := by
  have firstZero : imbalance (parityLaw parity (run first 0)) = 0 := by
    rw [parity_law_run_at_zero, (compensation_products _).1]
    apply prod_int_eq_zero_of_mem_zero
    refine List.mem_map.mpr ⟨parity.project coin, List.mem_map.mpr ⟨coin, present, rfl⟩, ?_⟩
    simp [Parity.project, crossesCut, imbalance, show coin.weights.zero = coin.weights.one from fair]
  have secondPositive : 0 < imbalance (parityLaw parity (run second 0)) := by
    rw [parity_law_run_at_zero, (compensation_products _).1]
    apply prod_int_positive
    intro w mem
    obtain ⟨projected, projectedMem, rfl⟩ := List.mem_map.mp mem
    obtain ⟨ch, chMem, rfl⟩ := List.mem_map.mp projectedMem
    exact secondBias ch chMem
  have ⟨zero, positive⟩ := root_parity_after_transfer _ _ transfer firstZero secondPositive transferBias
  intro same
  rw [same] at zero
  exact Int.ne_of_gt positive zero

def atom (v : Fin coordinates) : BitVec coordinates := BitVec.twoPow coordinates v.val

/-- A connected bidirected path across an intervention's active-ancestor
cut contains an edge with one endpoint on each side of the cut. -/
theorem walk_crosses_cut {edges : Nat} (g : Bottom coordinates edges) (inside : Fin coordinates → Bool)
    {start stop : Fin coordinates} (walk : Walk g start stop) (different : inside start ≠ inside stop) :
    ∃ e, inside (g.left e) ≠ inside (g.right e) := by
  induction walk with
  | refl _ => exact False.elim (different rfl)
  | forward e _ ih =>
    by_cases same : inside (g.left e) = inside (g.right e)
    · exact ih fun tail => different (same.trans tail)
    · exact ⟨e, same⟩
  | backward e _ ih =>
    by_cases same : inside (g.left e) = inside (g.right e)
    · exact ih fun tail => different (same.symm.trans tail)
    · exact ⟨e, same⟩

/-- Fair edge coins with opposite endpoints on the active-ancestor cut
give the separating target parity. The incidence equation describes which
endpoint influences remain after directed propagation and intervention. -/
theorem target_difference_from_intervention_cut {edges : Nat} (parity : Parity coordinates)
    (first second : List (Channel coordinates)) (graph : Bottom coordinates edges)
    (coin : Fin edges → Channel coordinates) (inside : Fin coordinates → Bool)
    (present : ∀ e, coin e ∈ first) (fair : ∀ e, (coin e).Fair)
    (incidence : ∀ e, parity.value (coin e).effect =
      Bool.xor (inside (graph.left e)) (inside (graph.right e)))
    {start stop : Fin coordinates} (walk : Walk graph start stop) (different : inside start ≠ inside stop)
    (secondBias : ∀ ch ∈ second, 0 < imbalance (parity.project ch))
    (transfer : BitWeights) (transferBias : 0 < imbalance transfer) :
    xorWeights (parityLaw parity (run first 0)) transfer ≠
      xorWeights (parityLaw parity (run second 0)) transfer := by
  obtain ⟨e, opposite⟩ := walk_crosses_cut graph inside walk different
  apply target_parities_differ_after_transfer parity first second (coin e) (present e) (fair e)
    _ secondBias transfer transferBias
  rw [incidence]
  have xor_of_ne (a b : Bool) (ne : a ≠ b) : Bool.xor a b = true := by
    cases a <;> cases b <;> simp_all
  exact xor_of_ne _ _ opposite

/-- Along a bidirected walk, simultaneously flipping its fair coins
cancels every interior incidence. `transport` propagates an exogenous
incidence mask through the directed graph. -/
private theorem walk_generates_endpoint_effect {edges : Nat} (g : Bottom coordinates edges)
    (channels : List (Channel coordinates)) (transport : BitVec coordinates → BitVec coordinates)
    (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b))
    (footprint : Fin coordinates → BitVec coordinates)
    (readEdge : ∀ e, Generated channels (transport (footprint (g.left e) ^^^ footprint (g.right e))))
    {a b : Fin coordinates} (walk : Walk g a b) :
    Generated channels (transport (footprint a ^^^ footprint b)) := by
  induction walk with
  | refl v =>
    rw [BitVec.xor_self]
    change Generated channels (transport 0)
    rw [zero]
    exact .zero
  | @forward e v _ ih =>
    have path := Generated.xor (readEdge e) ih
    rw [← linear, BitVec.xor_assoc, ← BitVec.xor_assoc (footprint (g.right e)), BitVec.xor_self,
      BitVec.zero_xor] at path
    exact path
  | @backward e v _ ih =>
    have edge := readEdge e
    rw [BitVec.xor_comm] at edge
    have path := Generated.xor edge ih
    rw [← linear, BitVec.xor_assoc, ← BitVec.xor_assoc (footprint (g.left e)), BitVec.xor_self,
      BitVec.zero_xor] at path
    exact path

theorem walk_generates_endpoint_pair {edges : Nat} (g : Bottom coordinates edges)
    (channels : List (Channel coordinates)) (transport : BitVec coordinates → BitVec coordinates)
    (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b))
    (readEdge : ∀ e, Generated channels (transport (atom (g.left e) ^^^ atom (g.right e))))
    {a b : Fin coordinates} (walk : Walk g a b) :
    Generated channels (transport (atom a ^^^ atom b)) :=
  walk_generates_endpoint_effect g channels transport zero linear atom readEdge walk

private theorem atom_bit (v j : Fin coordinates) :
    (atom v).getLsbD j.val = decide (v = j) := by
  simp only [atom, BitVec.getLsbD_twoPow, v.isLt, decide_true, Bool.true_and, Fin.val_inj]

def evenAtom (parity : Parity coordinates) (pivot v : Fin coordinates) : BitVec coordinates :=
  if parity.value (atom v) then atom v ^^^ atom pivot else atom v

private theorem even_atom_parity (parity : Parity coordinates) (pivot v : Fin coordinates)
    (odd : parity.value (atom pivot) = true) : parity.value (evenAtom parity pivot v) = false := by
  unfold evenAtom
  cases h : parity.value (atom v) <;> simp [h, parity.xor, odd]

private theorem even_atom_bit (parity : Parity coordinates) (pivot v j : Fin coordinates)
    (away : j ≠ pivot) : (evenAtom parity pivot v).getLsbD j.val = decide (v = j) := by
  unfold evenAtom
  split
  · rw [BitVec.getLsbD_xor, atom_bit, atom_bit, decide_eq_false (Ne.symm away), Bool.xor_false]
  · exact atom_bit v j

/-- These masks are a spanning set of the even subspace. They are endpoint
pairs when both atoms have odd parity, and singleton masks at coordinates
that have no path into the parity being measured. -/
private theorem parity_kernel_spanned_of_atoms (parity : Parity coordinates)
    (spanned : BitVec coordinates → Prop) (zero : spanned 0)
    (closed : ∀ a b, spanned a → spanned b → spanned (a ^^^ b)) (pivot : Fin coordinates)
    (odd : parity.value (atom pivot) = true)
    (atoms : ∀ v, spanned (evenAtom parity pivot v)) :
    ∀ mask, parity.value mask = false → spanned mask := by
  have within (xs : List (Fin coordinates)) (mask : BitVec coordinates)
      (supported : ∀ j, j ≠ pivot → mask.getLsbD j.val = true → j ∈ xs)
      (even : parity.value mask = false) : spanned mask := by
    induction xs generalizing mask with
    | nil =>
      have onlyPivot : mask = if mask.getLsbD pivot.val then atom pivot else 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        let j : Fin coordinates := ⟨k, hk⟩
        change mask.getLsbD j.val = _
        by_cases same : j = pivot
        · have sameIndex : k = pivot.val := congrArg Fin.val same
          change mask.getLsbD k = _
          rw [sameIndex]
          split
          next h => rw [h, atom_bit pivot pivot]; simp
          next h =>
            change _ = (0#coordinates).getLsbD _
            rw [BitVec.getLsbD_zero]
            exact Bool.eq_false_iff.mpr h
        · have off : mask.getLsbD j.val = false := by
            cases h : mask.getLsbD j.val
            · rfl
            · exact False.elim (List.not_mem_nil (supported j same h))
          rw [off]
          split
          · change false = (atom pivot).getLsbD j.val
            rw [atom_bit pivot j, decide_eq_false (Ne.symm same)]
          · change false = (0#coordinates).getLsbD _
            rw [BitVec.getLsbD_zero]
      by_cases active : mask.getLsbD pivot.val = true
      · have single : mask = atom pivot := by rwa [ite_eq_left active] at onlyPivot
        rw [single, odd] at even
        contradiction
      · have off : mask = 0 := by rwa [ite_eq_right active] at onlyPivot
        rw [off]
        exact zero
    | cons v xs ih =>
      if use : v ≠ pivot ∧ mask.getLsbD v.val = true then
        have tail : spanned (mask ^^^ evenAtom parity pivot v) := by
          apply ih
          · intro j away active
            rw [BitVec.getLsbD_xor, even_atom_bit parity pivot v j away] at active
            by_cases same : v = j
            · subst j
              rw [use.2, show decide (v = v) = true by simp, Bool.xor_self] at active
              contradiction
            · have was : mask.getLsbD j.val = true := by
                rwa [decide_eq_false same, Bool.xor_false] at active
              exact (List.mem_cons.mp (supported j away was)).resolve_left (Ne.symm same)
          · rw [parity.xor, even, even_atom_parity parity pivot v odd, Bool.false_xor]
        have restored := closed _ _ tail (atoms v)
        rwa [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at restored
      else
        exact ih mask (fun j away active =>
          (List.mem_cons.mp (supported j away active)).resolve_left (fun same => by
            subst j
            exact use ⟨away, active⟩)) even
  intro mask even
  exact within (List.finRange coordinates) mask (fun j _ _ => List.mem_finRange j) even

theorem parity_kernel_generated_of_atoms (parity : Parity coordinates)
    (channels : List (Channel coordinates)) (pivot : Fin coordinates)
    (odd : parity.value (atom pivot) = true)
    (atoms : ∀ v, Generated channels (evenAtom parity pivot v)) :
    ∀ mask, parity.value mask = false → Generated channels mask :=
  parity_kernel_spanned_of_atoms parity (Generated channels) .zero (fun _ _ => .xor) pivot odd atoms

private theorem transported_atoms_cover (channels : List (Channel coordinates))
    (parity : Parity coordinates) (pivot : Fin coordinates)
    (transport : BitVec coordinates → BitVec coordinates) (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b))
    (surjective : ∀ out, ∃ mask, transport mask = out)
    (odd : parity.value (transport (atom pivot)) = true)
    (atoms : ∀ v, Generated channels (transport
      (if parity.value (transport (atom v)) then atom v ^^^ atom pivot else atom v))) :
    ∀ out, parity.value out = false → Generated channels out := by
  let pullback : Parity coordinates :=
    ⟨fun mask => parity.value (transport mask), by rw [zero, parity.zero],
      fun a b => (congrArg parity.value (linear a b)).trans (parity.xor _ _)⟩
  have zeroGenerated : Generated channels (transport 0) := by rw [zero]; exact .zero
  have close (a b : BitVec coordinates) (ha : Generated channels (transport a))
      (hb : Generated channels (transport b)) : Generated channels (transport (a ^^^ b)) := by
    rw [linear]
    exact .xor ha hb
  have span := parity_kernel_spanned_of_atoms pullback (fun m => Generated channels (transport m))
    zeroGenerated close pivot odd atoms
  intro out even
  obtain ⟨mask, rfl⟩ := surjective out
  exact span mask even

/-- Model one's fair mask spanning argument. Complete bidirected
connectivity generates all endpoint pairs. An invertible directed
transport maps these pairs onto the root-parity kernel when every
vertex's innovation reaches exactly one root in the parity. -/
theorem connected_transported_fair_masks_cover {edges : Nat} (g : Bottom coordinates edges)
    (channels : List (Channel coordinates)) (parity : Parity coordinates) (pivot : Fin coordinates)
    (transport : BitVec coordinates → BitVec coordinates) (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b))
    (surjective : ∀ out, ∃ mask, transport mask = out)
    (readEdge : ∀ e, Generated channels (transport (atom (g.left e) ^^^ atom (g.right e))))
    (connected : ∀ v, Walk g v pivot) (oneRoot : ∀ v, parity.value (transport (atom v)) = true) :
    ∀ out, parity.value out = false → Generated channels out := by
  apply transported_atoms_cover channels parity pivot transport zero linear surjective (oneRoot pivot)
  intro v
  rw [ite_eq_left (oneRoot v)]
  exact walk_generates_endpoint_pair g channels transport zero linear readEdge (connected v)

def upperFootprint (inBottom : Fin coordinates → Bool) (v : Fin coordinates) : BitVec coordinates :=
  if inBottom v then 0 else atom v

/-- Model two retains both endpoint reads within the bottom and only the
upper endpoint read on a crossing. A walk from an upper vertex to the
bottom then generates a singleton at that vertex. Together with the bottom
walks these singleton masks span the full root-parity kernel. -/
theorem trimmed_transported_fair_masks_cover {fullEdges bottomEdges : Nat}
    (full : Bottom coordinates fullEdges) (bottom : Bottom coordinates bottomEdges)
    (channels : List (Channel coordinates)) (parity : Parity coordinates) (pivot : Fin coordinates)
    (inBottom : Fin coordinates → Bool) (pivotInBottom : inBottom pivot = true)
    (transport : BitVec coordinates → BitVec coordinates) (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b))
    (surjective : ∀ out, ∃ mask, transport mask = out)
    (bottomRead : ∀ e, Generated channels (transport (atom (bottom.left e) ^^^ atom (bottom.right e))))
    (upperRead : ∀ e, inBottom (full.left e) = false ∨ inBottom (full.right e) = false →
      Generated channels (transport
        (upperFootprint inBottom (full.left e) ^^^ upperFootprint inBottom (full.right e))))
    (fullConnected : ∀ v, Walk full v pivot)
    (bottomConnected : ∀ v, inBottom v = true → Walk bottom v pivot)
    (reachesRoot : ∀ v, parity.value (transport (atom v)) = inBottom v) :
    ∀ out, parity.value out = false → Generated channels out := by
  apply transported_atoms_cover channels parity pivot transport zero linear surjective
    ((reachesRoot pivot).trans pivotInBottom)
  intro v
  rw [reachesRoot]
  split
  next h =>
    exact walk_generates_endpoint_pair bottom channels transport zero linear bottomRead (bottomConnected v h)
  next h =>
    have upper : inBottom v = false := Bool.eq_false_iff.mpr h
    have allRead (e : Fin fullEdges) : Generated channels (transport
        (upperFootprint inBottom (full.left e) ^^^ upperFootprint inBottom (full.right e))) := by
      by_cases read : inBottom (full.left e) = false ∨ inBottom (full.right e) = false
      · exact upperRead e read
      · have left : inBottom (full.left e) = true := by
          cases he : inBottom (full.left e) with
          | false => exact False.elim (read (Or.inl he))
          | true => rfl
        have right : inBottom (full.right e) = true := by
          cases he : inBottom (full.right e) with
          | false => exact False.elim (read (Or.inr he))
          | true => rfl
        have eq : upperFootprint inBottom (full.left e) ^^^ upperFootprint inBottom (full.right e) = 0 := by
          rw [show upperFootprint inBottom (full.left e) = 0 from ite_eq_left left,
            show upperFootprint inBottom (full.right e) = 0 from ite_eq_left right]
          simp
        rw [eq, zero]
        exact .zero
    have path := walk_generates_endpoint_effect full channels transport zero linear
      (upperFootprint inBottom) allRead (fullConnected v)
    rw [show upperFootprint inBottom v = atom v from ite_eq_right (by simp [upper]),
      show upperFootprint inBottom pivot = 0 from ite_eq_left pivotInBottom] at path
    simpa using path

end

end OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.PositiveHedgeWitness
