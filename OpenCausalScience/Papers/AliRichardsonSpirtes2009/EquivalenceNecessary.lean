module
public import OpenCausalScience.Graph.MSeparation

/-! # A necessary condition for Markov equivalence of MAGs

Ali, Richardson and Spirtes (2009), Proposition 3.6. Maximality supplies
a separating set for each missing edge. An edge itself precludes a
separator, and a separating set for an unshielded length-two path contains
its middle vertex exactly when that vertex is a noncollider.
Source: https://doi.org/10.1214/08-AOS626
-/

namespace OpenCausalScience.AliRichardsonSpirtes2009

@[expose] public section

open MarkedGraph

variable {n : Nat}

theorem equivalent_adjacencies {G H : MarkedGraph n} (gMax : G.HasSeparators)
    (hMax : H.HasSeparators) (eqv : G.SameSeparations H) (x y : Fin n) :
    G.adjacent x y = H.adjacent x y := by
  by_cases xy : x = y
  · subst y
    simp [adjacent, G.loop_free, H.loop_free]
  cases g : G.adjacent x y <;> cases h : H.adjacent x y
  · rfl
  · obtain ⟨cond, legal, sep⟩ := gMax x y xy g
    exact False.elim ((eqv x y cond legal).1 sep (H.adjacent_mConnected xy h cond))
  · obtain ⟨cond, legal, sep⟩ := hMax x y xy h
    exact False.elim ((eqv x y cond legal).2 sep (G.adjacent_mConnected xy g cond))
  · rfl

private theorem unshielded_collider_transfer {G H : MarkedGraph n}
    (gMax : G.HasSeparators) (hMax : H.HasSeparators) (eqv : G.SameSeparations H)
    {x b y : Fin n} (triple : G.UnshieldedCollider x b y) : H.UnshieldedCollider x b y := by
  have original := triple
  obtain ⟨xb, xy, by', gFirst, gSecond, gAbsent, _⟩ := triple
  have same := equivalent_adjacencies gMax hMax eqv
  have first : H.adjacent x b = true := (same x b).symm.trans gFirst
  have second : H.adjacent b y = true := (same b y).symm.trans gSecond
  have absent : H.adjacent x y = false := (same x y).symm.trans gAbsent
  refine ⟨xb, xy, by', first, second, absent, ?_⟩
  obtain ⟨cond, legal, gSep⟩ := gMax x y xy gAbsent
  have hSep := (eqv x y cond legal).1 gSep
  cases coll : H.collider x b y with
  | true => rfl
  | false =>
    have off := G.collider_excluded_from_separator original gSep
    have on := H.noncollider_in_separator xb xy by' first second coll hSep
    simp [off] at on

theorem equivalent_unshielded_colliders {G H : MarkedGraph n} (gMax : G.HasSeparators)
    (hMax : H.HasSeparators) (eqv : G.SameSeparations H) (x b y : Fin n) :
    G.UnshieldedCollider x b y ↔ H.UnshieldedCollider x b y :=
  ⟨unshielded_collider_transfer gMax hMax eqv,
    unshielded_collider_transfer hMax gMax (fun a c z legal => (eqv a c z legal).symm)⟩

end

end OpenCausalScience.AliRichardsonSpirtes2009
