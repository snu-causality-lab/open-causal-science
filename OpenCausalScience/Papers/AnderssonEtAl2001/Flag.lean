module
public import OpenCausalScience.Graph.ChainMarkov

/-! # Two Markov readings of the same flag

The three-vertex flag in Andersson, Madigan and Perlman (1996), p. 46,
also part of the LWF–AMP comparison in their 2001 journal article.
Both laws below are newly constructed finite witnesses with full support.
-/

namespace OpenCausalScience.Papers.AnderssonEtAl2001.Flag

open ChainGraph
open Probability.FiniteMass (mass)

@[expose] public section

def graph : ChainGraph 3 where
  line := fun u v => (u == 1 && v == 2) || (u == 2 && v == 1)
  arrow := fun u v => u == 0 && v == 1
  rank := fun v => if v == 0 then 0 else 1
  line_symm := by decide
  line_irrefl := by decide
  line_level := by decide
  arrow_increases := by decide

def agreementWeight (agrees : Bool) : Rat := if agrees then 3 else 1

/-- Independent noisy copies along A → B → C realize the LWF independence. -/
def lwfLaw (x : BitVec 3) : Rat :=
  agreementWeight (ofMask x 0 == ofMask x 1) *
    agreementWeight (ofMask x 1 == ofMask x 2) / 32

/-- A and C are independent bits, and B is their noisy parity. -/
def ampLaw (x : BitVec 3) : Rat :=
  agreementWeight (ofMask x 1 == (ofMask x 0 ^^ ofMask x 2)) / 16

theorem lwf_law_positive_normalized :
    (∀ k : Fin 8, 0 < lwfLaw (BitVec.ofFin k)) ∧ mass (allMasks 3) lwfLaw (fun _ => true) = 1 := by
  decide +kernel

theorem amp_law_positive_normalized :
    (∀ k : Fin 8, 0 < ampLaw (BitVec.ofFin k)) ∧ mass (allMasks 3) ampLaw (fun _ => true) = 1 := by
  decide +kernel

theorem lwf_holds_amp_fails :
    graph.check .I (CIStatement.binaryCheck lwfLaw) = true ∧
      graph.check .II (CIStatement.binaryCheck lwfLaw) = false := by
  decide +kernel

theorem amp_holds_lwf_fails :
    graph.check .II (CIStatement.binaryCheck ampLaw) = true ∧
      graph.check .I (CIStatement.binaryCheck ampLaw) = false := by
  decide +kernel

end
end OpenCausalScience.Papers.AnderssonEtAl2001.Flag
