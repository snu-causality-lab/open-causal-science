module
public import OpenCausalScience.Graph.MixedGraph
public import OpenCausalScience.Papers.AliRichardsonSpirtes2009.EquivalenceNecessary

/-! # FCI rules R1, R2 and R8

Jiji Zhang, *On the completeness of orientation rules for causal discovery
in the presence of latent confounders and selection bias*, Artificial
Intelligence 172 (2008), 1873–1896, §3 and Theorem 1 (the R8 case).

Source: https://doi.org/10.1016/j.artint.2008.08.001
-/

namespace OpenCausalScience.Papers.Zhang2008OrientationRules.Orientations

open MarkedGraph
open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

/-- A definite directed edge in a fully marked graph. -/
def Directed (G : MarkedGraph n) (u v : Fin n) : Prop :=
  G.marks u v = some (false, true)

/-- The two ancestral restrictions used by these rules. In particular
the graph may have undirected edges. -/
structure AncestralMarks (G : MarkedGraph n) : Prop where
  no_head_at_undirected : ∀ {u v w}, G.marks u v = some (false, false) →
    G.arrowheadAt u w = false
  no_head_into_ancestor : ∀ {u v}, Reach (Directed G) u v →
    G.arrowheadAt u v = true → False

private theorem head_at_target {G : MarkedGraph n} {u v : Fin n}
    (edge : Directed G u v) : G.arrowheadAt v u = true := by
  change G.marks u v = some (false, true) at edge
  simp [MarkedGraph.arrowheadAt, G.swap_marks u v, edge, Prod.swap]

private theorem tail_with_incident_head {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {u v w : Fin n} {other : Bool} (tail : G.marks u v = some (false, other))
    (head : G.arrowheadAt u w = true) : Directed G u v := by
  cases other with
  | false =>
    have absent := ancestral.no_head_at_undirected tail (w := w)
    simp [head] at absent
  | true => exact tail

/-- R1. An unshielded triple has a noncollider completion. If the first
edge has a head at the middle vertex of an equivalent ancestral graph,
the second edge points from that vertex to the final vertex. -/
theorem r1_sound {G H : MarkedGraph n}
    (gMax : G.HasSeparators) (hMax : H.HasSeparators) (equivalent : G.SameSeparations H)
    (ancestral : AncestralMarks H) {a b c : Fin n} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (first : G.adjacent a b = true) (second : G.adjacent b c = true)
    (notAdjacent : G.adjacent a c = false) (noncollider : G.collider a b c = false)
    (head : H.arrowheadAt b a = true) : Directed H b c := by
  have same := AliRichardsonSpirtes2009.equivalent_adjacencies gMax hMax equivalent
  obtain ⟨marks, edge⟩ := Option.isSome_iff_exists.mp ((same b c).symm.trans second)
  obtain ⟨near, far⟩ := marks
  cases near with
  | false => exact tail_with_incident_head ancestral edge head
  | true =>
    have secondHead : H.arrowheadAt b c = true := by simp [MarkedGraph.arrowheadAt, edge]
    have collider : H.UnshieldedCollider a b c :=
      ⟨ab, ac, bc, (same a b).symm.trans first, (same b c).symm.trans second,
        (same a c).symm.trans notAdjacent, by simp [MarkedGraph.collider, head, secondHead]⟩
    have transferred := (AliRichardsonSpirtes2009.equivalent_unshielded_colliders
      gMax hMax equivalent a b c).mpr collider
    simp [MarkedGraph.UnshieldedCollider, noncollider] at transferred

/-- R2. The arrowhead at the target is fixed whenever either of the two
indicated two-edge configurations occurs and the shortcut is present. -/
theorem r2_sound {G : MarkedGraph n} (ancestral : AncestralMarks G) {a b c : Fin n}
    (shortcut : G.adjacent a c = true)
    (chain : (Directed G a b ∧ G.arrowheadAt c b = true) ∨
      (G.arrowheadAt b a = true ∧ Directed G b c)) : G.arrowheadAt c a = true := by
  obtain ⟨marks, edge⟩ := Option.isSome_iff_exists.mp shortcut
  obtain ⟨near, far⟩ := marks
  have reversed := G.swap_marks a c
  rw [edge] at reversed
  change G.marks c a = some (far, near) at reversed
  cases far with
  | true => simp [MarkedGraph.arrowheadAt, reversed]
  | false =>
    rcases chain with ⟨directed, head⟩ | ⟨head, directed⟩
    · have back := tail_with_incident_head ancestral reversed head
      exact (ancestral.no_head_into_ancestor (.extend (.extend (.refl c) back) directed) head).elim
    · have back := tail_with_incident_head ancestral reversed (head_at_target directed)
      exact (ancestral.no_head_into_ancestor (.extend (.extend (.refl b) directed) back) head).elim

/-- R8. A head at the shortcut target and a tail at the first vertex of
the two-edge chain force the directed shortcut. The other endpoint mark
on the first edge may be a tail or an arrowhead. -/
theorem r8_sound {G : MarkedGraph n} (ancestral : AncestralMarks G) {a b c : Fin n}
    {firstOther shortcutNear : Bool} (first : G.marks a b = some (false, firstOther))
    (second : Directed G b c) (shortcut : G.marks a c = some (shortcutNear, true)) :
    Directed G a c := by
  cases shortcutNear with
  | false => exact shortcut
  | true =>
    have head : G.arrowheadAt a c = true := by simp [MarkedGraph.arrowheadAt, shortcut]
    have directed := tail_with_incident_head ancestral first head
    exact (ancestral.no_head_into_ancestor (.extend (.extend (.refl a) directed) second) head).elim

end
end OpenCausalScience.Papers.Zhang2008OrientationRules.Orientations
