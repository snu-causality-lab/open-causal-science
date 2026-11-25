import MecLean.CtfScb.Border
import MecLean.CtfScb.WitnessAux

set_option linter.unusedSectionVars false

/-!
# `thm: ctf-pomis`, "if": a witness SCM

If `IB(𝓗_{𝐗_{∗∗}}, Y) = ∅`, one model conforming to `𝒢` makes the best assignment of `F` strictly
better than every assignment of every non-equivalent specification.

The witness adapts `ScbMec.LB2018` using reserved values for selected inputs:

* every vertex takes values in `Option (Roots n → ZMod K) ⊕ Fin n`: a coordinate tuple, the
  invalid value `none`, or the reserved value `inr w` designated for the input of `f_w`; natural
  outputs are never reserved;
* outside `T = An(Y)_{𝒢_F}` a vertex records its own roots; inside `T` it checks every selected
  input `(p, v)` of `relevant G y F` against `inr v` and every unselected input for being a tuple
  (by `mem_of_dir_into_diagH` these come from `T`), returns `none` on a failure, and otherwise adds
  the coordinates of its unselected parents to the record of its own roots;
* the reward is one when every coordinate `l` of `y` lies in `{0, cnt_F(l)}`, so the designated
  assignment has mean one;
* a competitor that selects an edge of `𝓗_F` meets the live/non-live split of
  `ScbMec.LB18.exists_split` and has mean at most `1/2` (`LB18.E_le_half`); a non-equivalent
  competitor that selects no such edge omits a selected input of `relevant G y F`, whose receiver
  becomes `none`, and `none` reaches `y`.

`Border.lean` supplies the graph facts this needs (`muct_eq_diagH_of_ctfIB`,
`mem_of_dir_into_diagH`, `relevant_relevant`, `ctfIB_relevant`).
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

/-- **`thm: ctf-pomis`, "if"**: a specification whose
regime graph `𝓗_{𝐗_{∗∗}}` has an empty interventional border is a ctf-POMIS. -/
theorem ctfPomis_if {G : ADMG n} (hG : G.WF) {y : Fin n} {F : EdgeSet n}
    (h : ctfIB G y F = ∅) : CtfPOMIS G y F := by
  have hT : DiagMUCT (G.cutE F) y ∅ (diagH (G.cutE F) y ∅) := by
    rw [← muct_eq_diagH_of_ctfIB h]
    exact Alg.diagMUCT_muct (Finset.notMem_empty y)
  exact CtfWit.ctfPomis_of_muct hG hT

end Mec.CtfScb
