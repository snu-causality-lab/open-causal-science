module
public import OpenCausalScience.Graph.MSeparation

/-! # Richardson and Spirtes (2002), Figure 9

The four vertices are alpha, beta, gamma, delta. Figure 9(a) lacks the
gamma–delta edge but connects that pair under all four legal conditioning
sets. Figure 9(b) adds gamma ↔ delta without changing the separation
relation. The authors' errata provide no amendment to this figure.

Source: https://www.cmu.edu/dietrich/philosophy/docs/spirtes/annals2002.pdf#page=18
Errata: https://sites.stat.washington.edu/tsr/website/documents/2002/annals-2002-errata.txt
-/

namespace OpenCausalScience.RichardsonSpirtes2002.Figure9

@[expose] public section

open MarkedGraph

def graph : MarkedGraph 4 := ofAscending fun u v =>
  match u.val, v.val with
  | 0, 1 | 0, 3 | 1, 2 => some (true, true)
  | 0, 2 | 1, 3 => some (false, true)
  | _, _ => none

def extension : MarkedGraph 4 := ofAscending fun u v =>
  if u = 2 ∧ v = 3 then some (true, true) else graph.marks u v

theorem missing_edge : graph.adjacent 2 3 = false := by decide

set_option maxRecDepth 4096 in
theorem gamma_delta_connected (cond : BitVec 4)
    (gammaExcluded : conditioned cond 2 = false)
    (deltaExcluded : conditioned cond 3 = false) : graph.MConnected 2 3 cond := by
  apply (graph.mConnected_iff 2 3 cond).1
  have all : ∀ i : Fin 16, conditioned (@BitVec.ofFin 4 i) 2 = false →
      conditioned (@BitVec.ofFin 4 i) 3 = false →
      graph.mConnected 2 3 (@BitVec.ofFin 4 i) = true := by decide
  exact all cond.toFin gammaExcluded deltaExcluded

theorem graph_has_no_maximality_witness : ¬ graph.HasSeparators := by
  intro maximal
  obtain ⟨cond, legal, separated⟩ := maximal 2 3 (by decide) missing_edge
  exact separated (gamma_delta_connected cond legal.2.1 legal.2.2)

theorem extension_is_complete :
    ∀ x y : Fin 4, x ≠ y → extension.adjacent x y = true := by decide

theorem extension_has_separators : extension.HasSeparators := by
  intro x y ne missing
  rw [extension_is_complete x y ne] at missing
  contradiction

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem extension_same_separations : graph.SameSeparations extension := by
  apply sameSeparations_of_checks
  decide


end

end OpenCausalScience.RichardsonSpirtes2002.Figure9
