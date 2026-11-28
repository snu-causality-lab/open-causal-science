module
public import OpenCausalScience.Discovery.OrderedMarkov
public import OpenCausalScience.Probability.FiniteGraphoid
public import OpenCausalScience.Papers.RaskuttiUhler2018.Figure1Distribution

/-! # Figure 1 as a finite probability law

The integer cell checks identify the actual singleton independences of
a positive normalized law on the four Boolean variables.
-/

namespace OpenCausalScience.Papers.RaskuttiUhler2018.Figure1

open Probability Probability.CI Probability.FiniteLaw Discovery

@[expose] public section

abbrev Assignment := Fin 4 → Bool

def readBits (w : BitVec 4) : Assignment := fun v => w.getLsbD v.val

def writeBits (ω : Assignment) : BitVec 4 :=
  (BitVec.ofBoolListLE ((List.finRange 4).map ω)).cast (by simp)

theorem read_write_bits (ω : Assignment) : readBits (writeBits ω) = ω := by
  funext v
  change (BitVec.cast _ (BitVec.ofBoolListLE _)).getLsbD v.val = ω v
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have bound : v.val < ((List.finRange 4).map ω).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some,
    List.getElem_map, List.getElem_finRange]
  congr 1

theorem write_read_bits (w : BitVec 4) : writeBits (readBits w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact congrFun (read_write_bits (readBits w)) ⟨i, hi⟩

private theorem worlds_exhaustive (w : BitVec 4) : w ∈ worlds := by
  exact List.mem_map.mpr ⟨w.toFin, List.mem_finRange _, BitVec.ofFin_toFin w⟩

def scale : Rat := (1 : Rat) / 256

private theorem numerator_pos (w : BitVec 4) : 0 < cellNumerator w := by
  have pos := distribution_positive_normalized.2 w.toFin
  rwa [BitVec.ofFin_toFin] at pos

def law : FiniteLaw Assignment where
  atoms := worlds.map readBits
  weight := fun ω => (cellNumerator (writeBits ω) : Rat) * scale
  nonnegative := by
    intro ω _
    exact Rat.le_of_lt (Rat.mul_pos (Rat.natCast_pos.mpr (numerator_pos _)) (by decide +kernel))

theorem law_full_support : ∀ ω : Assignment, ω ∈ law.atoms ∧ 0 < law.weight ω := by
  intro ω
  exact ⟨List.mem_map.mpr ⟨writeBits ω, worlds_exhaustive _, read_write_bits ω⟩,
    Rat.mul_pos (Rat.natCast_pos.mpr (numerator_pos _)) (by decide +kernel)⟩

private theorem mass_eq_numerator (event : Assignment → Bool) :
    law.mass event = (eventNumerator (event ∘ readBits) : Rat) * scale := by
  unfold FiniteLaw.mass FiniteMass.mass eventNumerator
  simp only [law, List.map_map, Function.comp_def]
  induction worlds with
  | nil => simp [Rat.zero_mul]
  | cons w rest ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Rat.natCast_add, Rat.add_mul, ih]
    by_cases h : event (readBits w) = true <;> simp [h, write_read_bits, Rat.zero_mul]

theorem law_normalized : law.mass (fun _ => true) = 1 := by
  rw [mass_eq_numerator]
  change ↑(eventNumerator (fun _ => true)) * scale = 1
  rw [distribution_positive_normalized.1]
  decide +kernel

private theorem eq_of_scaled_products (a b c d : Nat) :
    (↑a * scale) * (↑b * scale) = (↑c * scale) * (↑d * scale) ↔ a * b = c * d := by
  have reorder (x y : Nat) :
      (↑x * scale) * (↑y * scale) = (↑(x * y) : Rat) * (scale * scale) := by
    rw [← Rat.mul_assoc, Rat.mul_assoc (↑x), Rat.mul_comm scale (↑y),
      ← Rat.mul_assoc (↑x), Rat.mul_assoc, Rat.natCast_mul]
  rw [reorder, reorder]
  constructor
  · intro equal
    have nonzero : scale * scale ≠ 0 := by decide +kernel
    have cancel := congrArg (fun r => r / (scale * scale)) equal
    simp only [Rat.mul_div_cancel nonzero] at cancel
    exact Rat.natCast_inj.mp cancel
  · intro equal
    rw [equal]

private theorem stratum_bits (Z : Mask 4) (assignment : Assignment) (w : BitVec 4) :
    stratum Z assignment (readBits w) =
      ((w &&& writeBits Z) == (writeBits assignment &&& writeBits Z)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [stratum, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro agrees
    apply BitVec.eq_of_getLsbD_eq
    intro i bound
    have zBit := congrFun (read_write_bits Z) ⟨i, bound⟩
    have aBit := congrFun (read_write_bits assignment) ⟨i, bound⟩
    change (writeBits Z).getLsbD i = Z ⟨i, bound⟩ at zBit
    change (writeBits assignment).getLsbD i = assignment ⟨i, bound⟩ at aBit
    rw [BitVec.getLsbD_and, BitVec.getLsbD_and, zBit, aBit]
    cases inZ : Z ⟨i, bound⟩ with
    | false => simp
    | true => simpa [readBits] using agrees ⟨i, bound⟩ inZ
  · intro equal i present
    have eqBit := congrArg (fun b : BitVec 4 => b.getLsbD i.val) equal
    have zBit := congrFun (read_write_bits Z) i
    have aBit := congrFun (read_write_bits assignment) i
    change (writeBits Z).getLsbD i.val = Z i at zBit
    change (writeBits assignment).getLsbD i.val = assignment i at aBit
    rw [BitVec.getLsbD_and, BitVec.getLsbD_and, zBit, aBit, present] at eqBit
    simpa [readBits] using eqBit

private theorem point_bits (x : Fin 4) (a : Bool) (w : BitVec 4) :
    valueEvent (fun ω : Assignment => ω x) a (readBits w) = (w.getLsbD x.val == a) := by
  apply Bool.eq_iff_iff.mpr
  simp [valueEvent, readBits]

private theorem mass_cell_equiv (x y : Fin 4) (Z : Mask 4) (assignment : Assignment) (a b : Bool) :
    (let e := stratum Z assignment
     let l := valueEvent (fun ω : Assignment => ω x) a
     let r := valueEvent (fun ω : Assignment => ω y) b
     law.mass (andEvent (andEvent e l) r) * law.mass e =
       law.mass (andEvent e l) * law.mass (andEvent e r)) ↔
    (let e := fun w : BitVec 4 => (w &&& writeBits Z) == (writeBits assignment &&& writeBits Z)
     let l := fun w : BitVec 4 => w.getLsbD x.val == a
     let r := fun w : BitVec 4 => w.getLsbD y.val == b
     eventNumerator (fun w => e w && l w && r w) * eventNumerator e =
       eventNumerator (fun w => e w && l w) * eventNumerator (fun w => e w && r w)) := by
  dsimp only
  simp only [mass_eq_numerator, Function.comp_def, andEvent, stratum_bits, point_bits]
  apply eq_of_scaled_products

private theorem numerator_test_iff_law_ci (x y : Fin 4) (Z : Mask 4) (distinct : x ≠ y)
    (xOutside : Z x = false) (yOutside : Z y = false) :
    independentInLaw x y (writeBits Z) = true ↔ law.setIndependence (single x) (single y) Z := by
  rw [set_singletons_iff_cell_masses law x y Z false]
  unfold independentInLaw
  rw [List.all_eq_true]
  constructor
  · intro tests assignment a b
    let ω : Assignment := fun v => if v = x then a else if v = y then b else assignment v
    have maskSame : writeBits ω &&& writeBits Z = writeBits assignment &&& writeBits Z := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let j : Fin 4 := ⟨i, hi⟩
      have h1 := congrFun (read_write_bits ω) j
      have h2 := congrFun (read_write_bits assignment) j
      have h3 := congrFun (read_write_bits Z) j
      change (writeBits ω).getLsbD i = ω j at h1
      change (writeBits assignment).getLsbD i = assignment j at h2
      change (writeBits Z).getLsbD i = Z j at h3
      simp only [BitVec.getLsbD_and, h1, h2, h3]
      by_cases jx : j = x
      · simp [jx, xOutside]
      by_cases jy : j = y
      · simp [jy, yOutside]
      simp [ω, jx, jy]
    have sameX : (writeBits ω).getLsbD x.val = a := by
      simpa [readBits, ω] using congrFun (read_write_bits ω) x
    have sameY : (writeBits ω).getLsbD y.val = b := by
      simpa [readBits, ω, distinct.symm] using congrFun (read_write_bits ω) y
    have tested := tests (writeBits ω) (worlds_exhaustive _)
    apply (mass_cell_equiv x y Z assignment a b).mpr
    simpa only [maskSame, sameX, sameY, beq_iff_eq] using tested
  · intro ci w _
    have tested := (mass_cell_equiv x y Z (readBits w) (readBits w x) (readBits w y)).mp
      (ci (readBits w) (readBits w x) (readBits w y))
    simpa only [write_read_bits, readBits, beq_iff_eq] using tested

/-- The exact four-variable distribution realizes the Figure 1 oracle as
a graphoid relation on all disjoint variable sets. -/
theorem law_matches_figure_oracle : MatchesOracle law.setIndependence independent := by
  intro x y Z distinct xOutside yOutside
  have xBit := congrFun (read_write_bits Z) x
  have yBit := congrFun (read_write_bits Z) y
  have agrees := distribution_realizes_figure_oracle x y (writeBits Z).toFin distinct
    (by simpa only [BitVec.ofFin_toFin, readBits] using xBit.trans xOutside)
    (by simpa only [BitVec.ofFin_toFin, readBits] using yBit.trans yOutside)
  simp only [BitVec.ofFin_toFin] at agrees
  rw [show (fun z : Fin 4 => (writeBits Z).getLsbD z.val) = Z from read_write_bits Z] at agrees
  rw [← agrees]
  exact numerator_test_iff_law_ci x y Z distinct xOutside yOutside

theorem figure_order_is_markov (order : Fin 4 → Nat)
    (distinctRank : ∀ u v, order u = order v → u = v) :
    IsMarkov (orderDAG order independent) independent :=
  induced_order_is_markov (law.set_independence_graphoid false law_full_support)
    law_matches_figure_oracle order distinctRank

end

end OpenCausalScience.Papers.RaskuttiUhler2018.Figure1
