module
public import OpenCausalScience.Papers.Chickering2002.CliqueExtensions

/-! The necessity of the semidirected blocking test in Chickering
(2002), Theorem 15. A shortest avoiding walk has unshielded triples.
Acyclicity of the edited DAG and the prescribed collider signature
rule out such a walk. -/

namespace OpenCausalScience.Papers.Chickering2002.InsertBlocking

open OpenCausalScience.Papers.Chickering2002.Insert
open OpenCausalScience.Papers.Chickering2002.CliqueExtensions
open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.ChainComponents
open OpenCausalScience.Papers.Meek1995.JoinTreeOrientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n m : Nat} {base G H : DAG n} {fixed : Orientations n} {x y : Fin n}

inductive AvoidingRoute (base : DAG n) (fixed : Orientations n) (blocked : Vertices n) :
    Fin n → List (Fin n) → Fin n → Prop
  | stop {u} : ¬ blocked u → AvoidingRoute base fixed blocked u [] u
  | take {u v w rest} : ¬ blocked u → Adjacent base u v → ¬ fixed v u →
      AvoidingRoute base fixed blocked v rest w → AvoidingRoute base fixed blocked u (v :: rest) w

namespace AvoidingRoute

variable {blocked : Vertices n} {u v : Fin n} {route : List (Fin n)}

theorem start_avoids (walk : AvoidingRoute base fixed blocked u route v) : ¬ blocked u := by
  cases walk with
  | stop out => exact out
  | take out _ _ _ => exact out

private theorem appendEdge (walk : AvoidingRoute base fixed blocked u route v)
    {w : Fin n} (vw : Adjacent base v w) (noReverse : ¬ fixed w v) (outside : ¬ blocked w) :
    AvoidingRoute base fixed blocked u (route ++ [w]) w := by
  induction walk with
  | stop out => exact .take out vw noReverse (.stop outside)
  | take out edge backwards _ ih => exact .take out edge backwards (ih vw noReverse)

theorem of_walk (walk : AvoidingWalk base fixed blocked u v) :
    ∃ route, AvoidingRoute base fixed blocked u route v := by
  induction walk with
  | single outU outV edge noRev =>
    exact ⟨[_], .take outU edge noRev (.stop outV)⟩
  | extend _ out edge noRev ih =>
    obtain ⟨route, found⟩ := ih
    exact ⟨_, found.appendEdge edge noRev out⟩

private theorem level_nondecreasing (components : Components base fixed)
    {a b : Fin n} (edge : Adjacent base a b) (noReverse : ¬ fixed b a) :
    components.label a ≤ components.label b := by
  by_cases same : components.label a = components.label b
  · exact Nat.le_of_eq same
  · exact Nat.le_of_lt (components.fixed_increases _ _
      ((components.directions_between a b edge same).resolve_right noReverse))

/-- Every consecutive triple on a shortest semidirected avoiding route
has distinct and nonadjacent endpoints. -/
def UnshieldedTriples (base : DAG n) (u : Fin n) : List (Fin n) → Prop
  | v :: w :: rest => u ≠ w ∧ ¬ Adjacent base u w ∧ UnshieldedTriples base v (w :: rest)
  | _ => True

theorem shortest_unshielded (components : Components base fixed)
    (walk : AvoidingRoute base fixed blocked u route v)
    (shortest : ∀ other, AvoidingRoute base fixed blocked u other v → route.length ≤ other.length) :
    UnshieldedTriples base u route := by
  induction walk with
  | stop _ => trivial
  | @take u middle v rest out um noRev tail ih =>
    have tailShortest : ∀ next, AvoidingRoute base fixed blocked middle next v →
        rest.length ≤ next.length := by
      intro next other
      have le := shortest _ (.take out um noRev other)
      simpa only [List.length_cons, Nat.add_le_add_iff_right] using le
    have restUnshielded := ih tailShortest
    cases tail with
    | stop _ => trivial
    | @take _ w _ remaining _ mw noRevMW shorter =>
      have noReturn : u ≠ w := by
        intro h
        subst w
        have shorterRoute := shortest _ shorter
        simp only [List.length_cons] at shorterRoute
        omega
      have noChord : ¬ Adjacent base u w := by
        intro chord
        have levelUM := level_nondecreasing components um noRev
        have levelMW := level_nondecreasing components mw noRevMW
        have noBackward : ¬ fixed w u :=
          fun back => Nat.not_lt_of_ge (Nat.le_trans levelUM levelMW) (components.fixed_increases _ _ back)
        have shorterRoute := shortest _ (.take out chord noBackward shorter)
        simp only [List.length_cons] at shorterRoute
        omega
      exact ⟨noReturn, noChord, restUnshielded⟩

private theorem exists_minimum {P : Nat → Prop} (some : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  obtain ⟨k, hk⟩ := some
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases earlier : ∃ j, j < k ∧ P j
    · obtain ⟨j, less, hj⟩ := earlier
      exact ih j less hj
    · exact ⟨k, hk, fun j hj => Nat.le_of_not_gt (fun hjk => earlier ⟨j, hjk, hj⟩)⟩

theorem exists_unshielded_route (components : Components base fixed)
    (hasWalk : AvoidingWalk base fixed blocked u v) :
    ∃ route, AvoidingRoute base fixed blocked u route v ∧ UnshieldedTriples base u route := by
  obtain ⟨initial, walk⟩ := of_walk hasWalk
  obtain ⟨_, ⟨route, chosen, eq⟩, minimal⟩ :=
    exists_minimum (P := fun k => ∃ route, AvoidingRoute base fixed blocked u route v ∧ route.length = k)
      ⟨initial.length, initial, walk, rfl⟩
  exact ⟨route, chosen, shortest_unshielded components chosen fun other candidate => eq ▸
    minimal other.length ⟨other, candidate, rfl⟩⟩


private theorem suffix_of_occurrence (walk : AvoidingRoute base fixed blocked u route v)
    {w : Fin n} (appears : w ∈ route) :
    ∃ rest, AvoidingRoute base fixed blocked w rest v ∧ rest.length < route.length := by
  induction walk with
  | stop _ => cases appears
  | @take _ middle _ tail _ _ _ rest ih =>
    rcases List.mem_cons.mp appears with same | next
    · subst w
      exact ⟨tail, rest, by simp⟩
    · obtain ⟨suffix, starts, shorter⟩ := ih next
      refine ⟨suffix, starts, ?_⟩
      simp only [List.length_cons]
      omega

theorem shortest_is_simple (walk : AvoidingRoute base fixed blocked u route v)
    (shortest : ∀ other, AvoidingRoute base fixed blocked u other v → route.length ≤ other.length) :
    (u :: route).Nodup := by
  induction walk with
  | stop _ => simp
  | @take u middle v tail outside edge noBack remaining ih =>
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro again
      obtain ⟨suffix, onward, shorter⟩ := suffix_of_occurrence
        (.take outside edge noBack remaining) again
      exact Nat.not_lt_of_ge (shortest suffix onward) shorter
    · apply ih
      intro other routeAfter
      have bound := shortest _ (.take outside edge noBack routeAfter)
      simpa only [List.length_cons, Nat.add_le_add_iff_right] using bound

private theorem to_walk (walk : AvoidingRoute base fixed blocked u route v) (different : u ≠ v) :
    AvoidingWalk base fixed blocked u v := by
  have append {p q : Fin n} {path : List (Fin n)}
      (existing : AvoidingWalk base fixed blocked u p)
      (go : AvoidingRoute base fixed blocked p path q) : AvoidingWalk base fixed blocked u q := by
    induction go with
    | stop _ => exact existing
    | take _ edge noBack suffix ih =>
      exact ih (.extend existing suffix.start_avoids edge noBack)
  cases walk with
  | stop _ => exact (different rfl).elim
  | take outside edge noBack after =>
    exact append (.single outside after.start_avoids edge noBack) after

/-- Avoiding walks and simple avoiding paths give the same test for
distinct endpoints. -/
theorem walk_iff_simple_route (different : u ≠ v) :
    AvoidingWalk base fixed blocked u v ↔
      ∃ route, AvoidingRoute base fixed blocked u route v ∧ (u :: route).Nodup := by
  constructor
  · intro hasWalk
    obtain ⟨initial, walk⟩ := of_walk hasWalk
    obtain ⟨_, ⟨route, chosen, eq⟩, minimal⟩ :=
      exists_minimum (P := fun k => ∃ route, AvoidingRoute base fixed blocked u route v ∧ route.length = k)
        ⟨initial.length, initial, walk, rfl⟩
    exact ⟨route, chosen, shortest_is_simple chosen fun other candidate => eq ▸
      minimal other.length ⟨other, candidate, rfl⟩⟩
  · rintro ⟨_, walk, _⟩
    exact walk.to_walk different

private theorem directed_tail {a b v} {rest : List (Fin n)}
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (ab : G.edge a b = true) (walk : AvoidingRoute base fixed blocked b rest v)
    (chain : UnshieldedTriples base a (b :: rest)) :
    G.DirectedWalk a v := by
  induction walk generalizing a with
  | stop _ => exact .single ab
  | @take b c v rest _ bc noReverse _ ih =>
    have chain' : a ≠ c ∧ ¬ Adjacent base a c ∧ UnshieldedTriples base b (c :: rest) := chain
    have forward : G.edge b c = true := by
      rcases (ext.skeleton b c).mp bc with forward | reverse
      · exact forward
      · have collider : UnshieldedCollider G a b c :=
          ⟨chain'.1, fun adj => chain'.2.1 ((ext.skeleton a c).mpr adj), ab, reverse⟩
        exact (noReverse (contains a b c ((ext.colliders a b c).mpr collider)).2).elim
    have prepend {v w z : Fin n} (edge : G.edge v w = true) (walk : G.DirectedWalk w z) :
        G.DirectedWalk v z := by
      induction walk with
      | single next => exact .extend (.single edge) next
      | extend _ next previous => exact .extend previous next
    exact prepend ab (ih forward chain'.2.2)


end AvoidingRoute

/-- The semidirected path condition in Theorem 15 is necessary under
the component structure. A shortest route that avoided the required
parents would be directed from Y to X in the original extension. -/
theorem blocks_of_realization (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (tails : Vertices n) (choice : Choice base fixed x y tails)
    (edit : G.IsInsertion H x y) (realizes : Realizes base fixed x y tails H) :
    ¬ AvoidingWalk base fixed (fun v => NeighborsAdjacentToSource base fixed x y v ∨ tails v) y x := by
  intro avoids
  obtain ⟨route, path, chain⟩ := AvoidingRoute.exists_unshielded_route components avoids
  have tailMatch := matching_tails_of_realized choice edit realizes
  have directed : G.DirectedWalk y x := by
    cases path with
    | stop _ => exact (choice.distinct rfl).elim
    | @take _ v _ rest _ yv noReverse suffix =>
      have first : G.edge y v = true := by
        by_cases known : fixed y v
        · exact ext.oriented _ _ known
        · have openEdge : Unoriented base fixed v y := ⟨Or.symm yv, noReverse, known⟩
          have outside := suffix.start_avoids
          have shield : ¬ Adjacent base x v := fun a => outside (.inl ⟨openEdge, a⟩)
          exact ((ext.skeleton y v).mp yv).resolve_right
            (fun back => outside (.inr ((tailMatch v openEdge shield).mp back)))
      exact AvoidingRoute.directed_tail ext contains first suffix chain
  exact ((G.exists_insertion_iff choice.distinct).mp ⟨H, edit⟩) directed

/-- The two Insert tests characterize single-edge realization for the
rooted-clique component structure. The source's clique condition at
the chosen component is witnessed by the root bag. -/
theorem insert_iff_blocks_of_root_clique (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (tails : Vertices n) (choice : Choice base fixed x y tails)
    (tree : RootedJoinTree (components.adjacency (components.label y)) m)
    (inRoot : ∀ v, insertClique base fixed x y tails v → tree.inBag tree.root v) :
    (∃ K H : DAG n, Extension base fixed K ∧ K.IsInsertion H x y ∧ Realizes base fixed x y tails H) ↔
      ¬ AvoidingWalk base fixed (fun v => NeighborsAdjacentToSource base fixed x y v ∨ tails v) y x := by
  constructor
  · rintro ⟨_, _, before, edit, after⟩
    exact blocks_of_realization components before contains tails choice edit after
  · exact insert_from_root_clique components ext contains tails choice tree inRoot

end
end OpenCausalScience.Papers.Chickering2002.InsertBlocking
