module
public import OpenCausalScience.Papers.VermaPearl1990.Equivalence
public import OpenCausalScience.Papers.Meek1995.Closure
public import OpenCausalScience.Papers.Meek1995.ChordlessCycle
public import OpenCausalScience.Graph.MixedGraph

/-! The essential graph of Andersson, Madigan and Perlman (1997).
Compelled arrows are common to all Markov-equivalent DAGs. A normal
form for semidirected paths gives the collider and unshielded-triple
arguments in Facts 3 and 5. Facts 1, 2 and the essential-graph part
of Fact 4 also follow from collider invariance and acyclicity.
Source: https://doi.org/10.1214/aos/1031833662
-/

namespace OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph

open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.VermaPearl1990.Equivalence
open OpenCausalScience.Papers.Meek1995.Closure
open MixedGraph (Reach)

@[expose] public section

variable {n m : Nat}

def Compelled (G : DAG n) (x y : Fin n) : Prop :=
  ∀ H, SameDConnections G H → H.edge x y = true

def Reversible (G : DAG n) (x y : Fin n) : Prop :=
  (∃ H, SameDConnections G H ∧ H.edge x y = true) ∧
  (∃ H, SameDConnections G H ∧ H.edge y x = true)

theorem compelled_in_base {G : DAG n} {x y : Fin n} (arrow : Compelled G x y) :
    G.edge x y = true :=
  arrow G (fun _ _ _ => Iff.rfl)

private theorem orient_of_no_reverse {G : DAG n} {x y : Fin n}
    (edge : Adjacent G x y) (noReverse : ¬ ∃ H, SameDConnections G H ∧ H.edge y x = true) :
    Compelled G x y := by
  intro H equivalent
  exact ((sameSkeleton_of_sameDConnections equivalent x y).mp edge).resolve_right fun backward =>
    noReverse ⟨H, equivalent, backward⟩

/-- Every undirected essential-graph edge has witnesses in both orientations. -/
theorem unoriented_iff_reversible {G : DAG n} {x y : Fin n} :
    Unoriented G (Compelled G) x y ↔ Reversible G x y := by
  classical
  constructor
  · rintro ⟨edge, noForward, noReverse⟩
    refine ⟨Classical.byContradiction ?_, Classical.byContradiction ?_⟩
    · exact fun impossible => noReverse (orient_of_no_reverse (Or.symm edge) impossible)
    · exact fun impossible => noForward (orient_of_no_reverse edge impossible)
  · rintro ⟨⟨H, sameH, forward⟩, ⟨K, sameK, backward⟩⟩
    refine ⟨(sameSkeleton_of_sameDConnections sameH x y).mpr (Or.inl forward), ?_, ?_⟩
    · exact fun arrow =>
        K.no_directed_cycle x (.extend (.single (arrow K sameK)) backward)
    · exact fun arrow =>
        H.no_directed_cycle x (.extend (.single forward) (arrow H sameH))

/-- The two arrows of an unshielded collider occur in every representative. -/
theorem collider_arrows_compelled {G : DAG n} {a b c : Fin n}
    (collider : UnshieldedCollider G a b c) : Compelled G a b ∧ Compelled G c b := by
  constructor
  · exact fun H same => ((sameUnshieldedColliders_of_sameDConnections same a b c).mp
      collider).2.2.1
  · exact fun H same => ((sameUnshieldedColliders_of_sameDConnections same a b c).mp
      collider).2.2.2

/-- The semantic essential graph has no induced arrow followed by a line (Fact 1). -/
theorem no_induced_flag {G : DAG n} {a b c : Fin n}
    (arrow : Compelled G a b) (line : Unoriented G (Compelled G) b c)
    (distinct : a ≠ c) (missing : ¬ Adjacent G a c) : False := by
  obtain ⟨_, H, same, cb⟩ := unoriented_iff_reversible.mp line
  have collider : UnshieldedCollider H a b c :=
    ⟨distinct, fun edge => missing ((sameSkeleton_of_sameDConnections same _ _).mpr edge),
      arrow H same, cb⟩
  exact line.2.2 (collider_arrows_compelled
    ((sameUnshieldedColliders_of_sameDConnections same a b c).mpr collider)).2

/-- In the mixed triangle of Fact 2, the common third vertex is last
in one representative and first in another. -/
theorem triangle_witnesses {G : DAG n} {a b c : Fin n}
    (ab : Compelled G a b) (ac : Reversible G a c) (bc : Reversible G b c) :
    (∃ H, SameDConnections G H ∧ H.edge a c = true ∧ H.edge b c = true) ∧
    (∃ H, SameDConnections G H ∧ H.edge c a = true ∧ H.edge c b = true) := by
  obtain ⟨H, sameH, bToC⟩ := bc.1
  obtain ⟨K, sameK, cToA⟩ := ac.2
  have adjH : Adjacent H a c := (sameSkeleton_of_sameDConnections sameH a c).mp
    (unoriented_iff_reversible.mpr ac).1
  have adjK : Adjacent K b c := (sameSkeleton_of_sameDConnections sameK b c).mp
    (unoriented_iff_reversible.mpr bc).1
  exact ⟨⟨H, sameH, adjH.resolve_right (fun ca =>
      H.no_directed_cycle a (.extend (.extend (.single (ab H sameH)) bToC) ca)), bToC⟩,
    ⟨K, sameK, cToA, adjK.resolve_left (fun bc =>
      K.no_directed_cycle a (.extend (.extend (.single (ab K sameK)) bc) cToA))⟩⟩

/-- Some corner of every chordless skeleton cycle is an unshielded
collider with two compelled incoming edges (Fact 4 for the essential graph). -/
theorem chordless_cycle_has_compelled_arrows {G : DAG n}
    (cycle : Meek1995.ChordlessCycle.Cycle G m) :
    ∃ k, Compelled G (cycle.vertex (cycle.previous k)) (cycle.vertex k) ∧
      Compelled G (cycle.vertex (cycle.following k)) (cycle.vertex k) := by
  obtain ⟨k, collider⟩ := Meek1995.ChordlessCycle.contains_collider cycle
  exact ⟨k, collider_arrows_compelled collider⟩

theorem no_chordless_undirected_cycle {G : DAG n}
    (cycle : Meek1995.ChordlessCycle.Cycle G m)
    (lines : ∀ k, Unoriented G (Compelled G) (cycle.vertex (cycle.previous k))
      (cycle.vertex k)) : False := by
  obtain ⟨k, arrow, _⟩ := chordless_cycle_has_compelled_arrows cycle
  exact (lines k).2.1 arrow

/-- The valid extensions of the essential graph are precisely its
Markov-equivalent DAGs. The skeleton and unshielded colliders suffice. -/
theorem extension_iff_same_d_connections {G H : DAG n} :
    Extension G (Compelled G) H ↔ SameDConnections G H := by
  constructor
  · intro ext
    exact same_dConnections_iff_same_signature.mpr ⟨ext.skeleton, ext.colliders⟩
  · intro same
    exact ⟨sameSkeleton_of_sameDConnections same,
      sameUnshieldedColliders_of_sameDConnections same, fun _ _ arrow => arrow H same⟩

/-- A directed edge occurs in at least one equivalent DAG. A line in the
essential graph therefore gives a step in either direction. -/
def PossibleArrow (G : DAG n) (x y : Fin n) : Prop :=
  ∃ H, SameDConnections G H ∧ H.edge x y = true

theorem possible_iff {G : DAG n} {x y : Fin n} :
    PossibleArrow G x y ↔ Compelled G x y ∨ Reversible G x y := by
  constructor
  · rintro ⟨H, same, edge⟩
    by_cases reverse : PossibleArrow G y x
    · exact Or.inr ⟨⟨H, same, edge⟩, reverse⟩
    · exact Or.inl (orient_of_no_reverse
        ((sameSkeleton_of_sameDConnections same x y).mpr (Or.inl edge)) reverse)
  · rintro (fixed | both)
    · exact ⟨G, fun _ _ _ => Iff.rfl, compelled_in_base fixed⟩
    · exact both.1

/-- An arrow followed by a line has a shortcut permitting the same direction. -/
theorem shortcut_arrow_line {G : DAG n} {a b c : Fin n}
    (arrow : Compelled G a b) (line : Reversible G b c) : PossibleArrow G a c := by
  obtain ⟨H, same, bc⟩ := line.1
  have ab := arrow H same
  have ac : a ≠ c := by
    rintro rfl
    exact H.no_directed_cycle a (.extend (.single ab) bc)
  have adjacent : Adjacent G a c := Classical.byContradiction fun missing =>
    no_induced_flag arrow (unoriented_iff_reversible.mpr line) ac missing
  have hAdjacent := (sameSkeleton_of_sameDConnections same a c).mp adjacent
  exact ⟨H, same, hAdjacent.resolve_right fun ca =>
    H.no_directed_cycle a (.extend (.extend (.single ab) bc) ca)⟩

private theorem append_line {G : DAG n} {a b : Fin n}
    (path : Reach (Compelled G) a b) {c : Fin n} (line : Reversible G b c) :
    ∃ d, Reach (Reversible G) a d ∧ Reach (Compelled G) d c := by
  induction path generalizing c with
  | refl => exact ⟨c, .extend (.refl a) line, .refl c⟩
  | extend earlier arrow ih =>
    rcases possible_iff.mp (shortcut_arrow_line arrow line) with fixed | openEdge
    · exact ⟨a, .refl a, .extend earlier fixed⟩
    · exact ih openEdge

/-- Compress an arrow followed by a line. Any semidirected walk can be
replaced by a walk of lines followed by a walk of compelled arrows. -/
theorem possible_path_normal_form {G : DAG n} {a b : Fin n}
    (path : Reach (PossibleArrow G) a b) :
    ∃ d, Reach (Reversible G) a d ∧ Reach (Compelled G) d b := by
  have concatenate {u v w : Fin n} (first : Reach (Reversible G) u v)
      (second : Reach (Reversible G) v w) : Reach (Reversible G) u w := by
    induction second with
    | refl => exact first
    | extend _ edge ih => exact .extend ih edge
  induction path with
  | refl => exact ⟨a, .refl a, .refl a⟩
  | extend _ edge ih =>
    obtain ⟨m, lines, arrows⟩ := ih
    rcases possible_iff.mp edge with fixed | line
    · exact ⟨m, lines, .extend arrows fixed⟩
    · obtain ⟨d, moreLines, rest⟩ := append_line arrows line
      exact ⟨d, concatenate lines moreLines, rest⟩

private theorem rank_le_of_compelled_path {G : DAG n} {a b : Fin n}
    (path : Reach (Compelled G) a b) : G.rank a ≤ G.rank b := by
  induction path with
  | refl => exact Nat.le_refl _
  | extend _ edge ih => exact Nat.le_trans ih (Nat.le_of_lt (G.edge_increases _ _ (compelled_in_base edge)))

/-- A reversible step away from the head of an unshielded collider
moves that collider to the adjacent vertex with the same two parents. -/
theorem collider_along_line {G : DAG n} {a b c d : Fin n}
    (collider : UnshieldedCollider G a b c) (line : Reversible G b d) :
    UnshieldedCollider G a d c := by
  have fixed := collider_arrows_compelled collider
  obtain ⟨H, same, bd⟩ := line.1
  have toward {x : Fin n} (xb : Compelled G x b) : H.edge x d = true := by
    have xd : PossibleArrow G x d := shortcut_arrow_line xb line
    obtain ⟨K, sameK, kd⟩ := xd
    have adj := (sameSkeleton_of_sameDConnections same x d).mp
      ((sameSkeleton_of_sameDConnections sameK x d).mpr (Or.inl kd))
    exact adj.resolve_right fun dx =>
      H.no_directed_cycle x (.extend (.extend (.single (xb H same)) bd) dx)
  have transferred : UnshieldedCollider H a d c :=
    ⟨collider.1, fun adj => collider.2.1
        ((sameSkeleton_of_sameDConnections same a c).mpr adj),
      toward fixed.1, toward fixed.2⟩
  exact (sameUnshieldedColliders_of_sameDConnections same a d c).mpr transferred

/-- Neither arrow of an unshielded collider is internal to a strongly
connected component of the possible-arrow relation (Fact 3). -/
theorem collider_arrow_has_no_return {G : DAG n} {a b c : Fin n}
    (collider : UnshieldedCollider G a b c) (back : Reach (PossibleArrow G) b a) : False := by
  obtain ⟨d, lines, arrows⟩ := possible_path_normal_form back
  have moved {u : Fin n} (path : Reach (Reversible G) b u) : UnshieldedCollider G a u c := by
    induction path with
    | refl => exact collider
    | extend _ edge ih => exact collider_along_line ih edge
  exact Nat.not_lt_of_ge (rank_le_of_compelled_path arrows)
    (G.edge_increases _ _ (moved lines).2.2.1)

private theorem move_induced_chain {G : DAG n} {a b c d : Fin n}
    (ab : Compelled G a b) (bc : Compelled G b c) (absent : ¬ Adjacent G a c)
    (line : Reversible G c d) : Compelled G b d ∧ ¬ Adjacent G a d := by
  obtain ⟨H, sameH, cd⟩ := line.1
  have chain := DAG.DirectedWalk.extend (.extend (.single (ab H sameH)) (bc H sameH)) cd
  have noAD : ¬ Adjacent G a d := by
    intro adj
    have goes := ((sameSkeleton_of_sameDConnections sameH a d).mp adj).resolve_right
      fun da => H.no_directed_cycle a (.extend chain da)
    have collider : UnshieldedCollider H a d c :=
      ⟨(fun eq => (H.no_directed_cycle a
          ((congrArg (H.DirectedWalk a) eq).mpr (.extend (.single (ab H sameH)) (bc H sameH))))),
        fun edge => absent ((sameSkeleton_of_sameDConnections sameH a c).mpr edge), goes, cd⟩
    exact (unoriented_iff_reversible.mpr line).2.1
      (collider_arrows_compelled ((sameUnshieldedColliders_of_sameDConnections sameH a d c).mpr
        collider)).2
  have adjBD : Adjacent G b d := by
    obtain ⟨K, sameK, bd⟩ := shortcut_arrow_line bc line
    exact (sameSkeleton_of_sameDConnections sameK b d).mpr (Or.inl bd)
  have hd : H.edge b d = true := by
    exact ((sameSkeleton_of_sameDConnections sameH b d).mp adjBD).resolve_right fun db =>
      H.no_directed_cycle b (.extend (.extend (.single (bc H sameH)) cd) db)
  have distinct : a ≠ d := fun same =>
    H.no_directed_cycle a ((congrArg (H.DirectedWalk a) same).mpr chain)
  have notCollider : ¬ UnshieldedCollider H a b d :=
    fun h => H.no_directed_cycle b (.extend (.single hd) h.2.2.2)
  have bd : Compelled G b d := by
    intro K sameK
    exact ((sameSkeleton_of_sameDConnections sameK b d).mp adjBD).resolve_right fun db =>
      notCollider ((sameUnshieldedColliders_of_sameDConnections sameH a b d).mp
        ((sameUnshieldedColliders_of_sameDConnections sameK a b d).mpr
          ⟨distinct, fun edge => noAD ((sameSkeleton_of_sameDConnections sameK a d).mpr edge),
            ab K sameK, db⟩))
  exact ⟨bd, noAD⟩

/-- The second arrow of an induced compelled chain has no semidirected
return path. This is the remaining case of Fact 5. -/
theorem induced_chain_has_no_return {G : DAG n} {a b c : Fin n}
    (ab : Compelled G a b) (bc : Compelled G b c) (absent : ¬ Adjacent G a c)
    (back : Reach (PossibleArrow G) c b) : False := by
  obtain ⟨d, lines, arrows⟩ := possible_path_normal_form back
  have moved {u : Fin n} (path : Reach (Reversible G) c u) :
      Compelled G b u ∧ ¬ Adjacent G a u := by
    induction path with
    | refl => exact ⟨bc, absent⟩
    | extend _ edge ih => exact move_induced_chain ab ih.1 ih.2 edge
  exact Nat.not_lt_of_ge (rank_le_of_compelled_path arrows)
    (G.edge_increases _ _ (compelled_in_base (moved lines).1))

/-- Enlarging the undirected components by forgetting every arrow internal
to a strongly connected component still creates no induced flag (Fact 5). -/
theorem no_flag_after_forgetting_internal_arrows {G : DAG n} {a b c : Fin n}
    (ab : Compelled G a b) (adj : Adjacent G b c)
    (bc : Reach (PossibleArrow G) b c) (cb : Reach (PossibleArrow G) c b)
    (distinct : a ≠ c) (absent : ¬ Adjacent G a c) : False := by
  have neverCA : ¬ PossibleArrow G c b := by
    rintro ⟨H, same, arrow⟩
    have collider : UnshieldedCollider H a b c :=
      ⟨distinct, fun edge => absent ((sameSkeleton_of_sameDConnections same a c).mpr edge),
        ab H same, arrow⟩
    have fromH := (sameUnshieldedColliders_of_sameDConnections same a b c).mpr collider
    exact collider_arrow_has_no_return
      ⟨distinct.symm, fun edge => fromH.2.1 (Or.symm edge), fromH.2.2.2, fromH.2.2.1⟩ bc
  exact induced_chain_has_no_return ab (orient_of_no_reverse adj neverCA) absent cb

end
end OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph
