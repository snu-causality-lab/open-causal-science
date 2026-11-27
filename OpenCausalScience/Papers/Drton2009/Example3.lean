module
public import OpenCausalScience.Papers.AnderssonEtAl2001.Flag

/-! # Four distinct models for one chain graph

Drton (2009), Fig. 3 and Example 3. Vertex indices 0, 1, 2, 3 represent
the published labels 1, 2, 3, 4. The four positive laws are explicit
examples realizing one block-recursive interpretation each.
-/

namespace OpenCausalScience.Papers.Drton2009.Example3

open ChainGraph
open AnderssonEtAl2001.Flag (agreementWeight)
open Probability.FiniteMass (mass)

@[expose] public section

def graph : ChainGraph 4 where
  line := fun u v =>
    (u == 2 && (v == 1 || v == 3)) || (v == 2 && (u == 1 || u == 3))
  arrow := fun u v => u == 0 && v == 2
  rank := fun v => if v == 0 then 0 else 1
  line_symm := by decide
  line_irrefl := by decide
  line_level := by decide
  arrow_increases := by decide

def readings : List MarkovType := [.I, .II, .III, .IV]

/-- A fair variable 1 and a copy-scattering law through variable 3 in
type I. Type II hides the effect of variable 1 by reversing the polarity
of the fair bit 3. Type III uses two dependent conditional tables whose
mixtures at the different levels of variable 1 are product tables.
Type IV uses three independent bits and observes their noisy parity. -/
def law (kind : MarkovType) (cell : BitVec 4) : Rat :=
  let a := ofMask cell 0
  let c := ofMask cell 1
  let b := ofMask cell 2
  let d := ofMask cell 3
  match kind with
  | .I => agreementWeight (a == b) * agreementWeight (b == c) *
      agreementWeight (b == d) / 128
  | .II => agreementWeight ((a ^^ b) == c) * agreementWeight ((a ^^ b) == d) / 64
  | .III => agreementWeight (a == b) *
      (if c != d then 15 else if c == b then 33 else 1) / 512
  | .IV => agreementWeight (b == (a ^^ c ^^ d)) / 32

theorem laws_positive_normalized (kind : MarkovType) :
    (∀ k : Fin 16, 0 < law kind (BitVec.ofFin k)) ∧
      mass (allMasks 4) (law kind) (fun _ => true) = 1 := by
  cases kind <;> decide +kernel

def modelMembership (kind : MarkovType) : List Bool :=
  readings.map fun candidate => graph.check candidate (CIStatement.binaryCheck (law kind))

theorem type_i_membership : modelMembership .I = [true, false, false, false] := by
  decide +kernel

theorem type_ii_membership : modelMembership .II = [false, true, false, false] := by
  decide +kernel

theorem type_iii_membership : modelMembership .III = [false, false, true, false] := by
  decide +kernel

theorem type_iv_membership : modelMembership .IV = [false, false, false, true] := by
  decide +kernel

end
end OpenCausalScience.Papers.Drton2009.Example3
