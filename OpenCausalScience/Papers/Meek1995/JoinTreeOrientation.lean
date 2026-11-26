module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! Orient a finite undirected graph with a rooted join tree by the first
bag containing each vertex. See Meek (1995), Lemmas 4–5, and
Chickering (2002), Lemma 36. -/

namespace OpenCausalScience.Papers.Meek1995.JoinTreeOrientation

open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n m : Nat}

abbrev Adjacency (n : Nat) := Fin n → Fin n → Prop

/-- The rooted tree properties used by the orientation construction.
The ancestors of any one bag are comparable. Bags containing a vertex
satisfy running intersection along the tree. -/
structure RootedJoinTree (adj : Adjacency n) (m : Nat) where
  root : Fin m
  inBag : Fin m → Fin n → Prop
  ancestor : Fin m → Fin m → Prop
  depth : Fin m → Nat
  refl : ∀ i, ancestor i i
  trans : ∀ {i j k}, ancestor i j → ancestor j k → ancestor i k
  strict : ∀ {i j}, ancestor i j → i ≠ j → depth i < depth j
  root_ancestor : ∀ i, ancestor root i
  comparable : ∀ {i j k}, ancestor i k → ancestor j k → ancestor i j ∨ ancestor j i
  covers_edges : ∀ u v, adj u v ↔ u ≠ v ∧ ∃ i, inBag i u ∧ inBag i v
  connected : ∀ {i j k u}, ancestor i j → ancestor j k → inBag i u → inBag k u → inBag j u
  common_ancestor : ∀ {i j u}, inBag i u → inBag j u →
    ∃ k, ancestor k i ∧ ancestor k j ∧ inBag k u

private theorem minimum_in_list {α : Type} (rank : α → Nat) (admit : α → Prop)
    (xs : List α) (existsIn : ∃ x, x ∈ xs ∧ admit x) :
    ∃ x, x ∈ xs ∧ admit x ∧ ∀ y, y ∈ xs → admit y → rank x ≤ rank y := by
  classical
  induction xs with
  | nil =>
    rcases existsIn with ⟨_, hm, _⟩
    cases hm
  | cons first rest ih =>
    by_cases tail : ∃ x, x ∈ rest ∧ admit x
    · obtain ⟨best, hm, good, bestRank⟩ := ih tail
      by_cases useFirst : admit first ∧ rank first ≤ rank best
      · refine ⟨first, .head _, useFirst.1, ?_⟩
        intro y present hy
        rcases List.mem_cons.mp present with rfl | inRest
        · exact Nat.le_refl _
        · exact Nat.le_trans useFirst.2 (bestRank y inRest hy)
      · refine ⟨best, .tail _ hm, good, ?_⟩
        intro y present hy
        rcases List.mem_cons.mp present with rfl | inRest
        · exact Nat.le_of_lt (Nat.lt_of_not_ge (fun ge => useFirst ⟨hy, ge⟩))
        · exact bestRank y inRest hy
    · obtain ⟨x, hm, hx⟩ := existsIn
      have firstAllowed : admit first := by
        rcases List.mem_cons.mp hm with rfl | inRest
        · exact hx
        · exact (tail ⟨x, inRest, hx⟩).elim
      refine ⟨first, .head _, firstAllowed, ?_⟩
      intro y present hy
      rcases List.mem_cons.mp present with rfl | inRest
      · exact Nat.le_refl _
      · exact (tail ⟨y, inRest, hy⟩).elim

namespace RootedJoinTree

variable {adj : Adjacency n}

theorem adj_symm (tree : RootedJoinTree adj m) {u v : Fin n} (edge : adj u v) :
    adj v u := by
  obtain ⟨ne, i, hu, hv⟩ := (tree.covers_edges u v).mp edge
  exact (tree.covers_edges v u).mpr ⟨ne.symm, i, hv, hu⟩

/-- The first bag is an ancestor of every bag containing the vertex.
For an isolated vertex outside all bags the choice is immaterial. -/
theorem exists_first_bags (tree : RootedJoinTree adj m) :
    ∃ first : Fin n → Fin m, ∀ i v, tree.inBag i v →
      tree.inBag (first v) v ∧ tree.ancestor (first v) i := by
  classical
  have chooseFor (v : Fin n) : ∃ chosen, ∀ i, tree.inBag i v →
      tree.inBag chosen v ∧ tree.ancestor chosen i := by
    by_cases occurs : ∃ i, tree.inBag i v
    · have occursIn : ∃ i, i ∈ List.finRange m ∧ tree.inBag i v := by
        obtain ⟨i, hi⟩ := occurs
        exact ⟨i, List.mem_finRange _, hi⟩
      obtain ⟨k, _, hk, minK⟩ :=
        minimum_in_list tree.depth (fun i => tree.inBag i v) _ occursIn
      refine ⟨k, fun i hi => ⟨hk, ?_⟩⟩
      obtain ⟨l, lk, li, hl⟩ := tree.common_ancestor hk hi
      by_cases same : l = k
      · exact same ▸ li
      · have before := tree.strict lk same
        have bound := minK l (List.mem_finRange _) hl
        omega
    · exact ⟨tree.root, fun i hi => (occurs ⟨i, hi⟩).elim⟩
  exact ⟨fun v => (chooseFor v).choose, fun i v => (chooseFor v).choose_spec i⟩

private theorem appears_in_center_bag (tree : RootedJoinTree adj m)
    (first : Fin n → Fin m)
    (first_spec : ∀ i v, tree.inBag i v → tree.inBag (first v) v ∧ tree.ancestor (first v) i)
    {u v : Fin n} (edge : adj u v) (before : tree.depth (first u) ≤ tree.depth (first v)) :
    tree.inBag (first v) u := by
  obtain ⟨_, bag, hu, hv⟩ := (tree.covers_edges u v).mp edge
  obtain ⟨huFirst, huEarlier⟩ := first_spec bag u hu
  have hvEarlier := (first_spec bag v hv).2
  have order : tree.ancestor (first u) (first v) := by
    rcases tree.comparable huEarlier hvEarlier with forward | backward
    · exact forward
    · by_cases equal : first v = first u
      · rw [equal]
        exact tree.refl _
      · have strict := tree.strict backward equal
        omega
  exact tree.connected order hvEarlier huFirst hu

private def maxKey (key : Fin n → Nat) : Nat :=
  ((List.finRange n).foldr (fun v acc => max (key v) acc) 0) + 1

private theorem key_lt_max (key : Fin n → Nat) (v : Fin n) : key v < maxKey key := by
  have within (xs : List (Fin n)) (present : v ∈ xs) :
      key v ≤ xs.foldr (fun a acc => max (key a) acc) 0 := by
    induction xs with
    | nil => cases present
    | cons a rest ih =>
      rcases List.mem_cons.mp present with rfl | p
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih p) (Nat.le_max_right _ _)
  exact Nat.lt_succ_of_le (within _ (List.mem_finRange _))


/-- Every clique covered by the bags lies in a single bag. Choose its
vertex with deepest first occurrence and apply running intersection
to the first bags of the other vertices. -/
theorem exists_bag_containing_clique (tree : RootedJoinTree adj m)
    (clique : Fin n → Prop)
    (pairwise : ∀ u v, clique u → clique v → u ≠ v → adj u v)
    (covered : ∀ u, clique u → ∃ i, tree.inBag i u) :
    ∃ i, ∀ u, clique u → tree.inBag i u := by
  classical
  obtain ⟨first, first_spec⟩ := tree.exists_first_bags
  let depth := fun v => tree.depth (first v)
  let ceiling := maxKey depth
  by_cases present : ∃ v, clique v
  · obtain ⟨v, _, selected, deepest⟩ :=
      minimum_in_list (fun u => ceiling - depth u) clique (List.finRange n) (by
        obtain ⟨u, hu⟩ := present
        exact ⟨u, List.mem_finRange _, hu⟩)
    refine ⟨first v, ?_⟩
    intro u hu
    by_cases same : u = v
    · subst u
      obtain ⟨i, occurs⟩ := covered v selected
      exact (first_spec i v occurs).1
    · have uv := pairwise u v hu selected same
      have bound := deepest u (List.mem_finRange _) hu
      have one : depth u < ceiling := key_lt_max depth u
      have two : depth v < ceiling := key_lt_max depth v
      exact tree.appears_in_center_bag first first_spec uv (by
        change depth u ≤ depth v
        omega)
  · exact ⟨tree.root, fun u hu => (present ⟨u, hu⟩).elim⟩

private theorem lex_lt {base lower higher lowTail highTail : Nat}
    (depthLt : lower < higher) (fits : lowTail < base) :
    base * lower + lowTail < base * higher + highTail := by
  have mulLe := Nat.mul_le_mul_left base depthLt
  rw [Nat.mul_succ] at mulLe
  omega

private theorem tie_lt {key : Fin n → Nat} {u v : Fin n} (ordered : key u < key v) :
    n * key u + u.val < n * key v + v.val :=
  lex_lt ordered u.isLt

private theorem tie_injective (key : Fin n → Nat) {u v : Fin n}
    (same : n * key u + u.val = n * key v + v.val) : u = v := by
  rcases Nat.lt_trichotomy (key u) (key v) with before | equal | after
  · exact (Nat.ne_of_lt (tie_lt before) same).elim
  · exact Fin.ext (by simpa [equal] using same)
  · exact (Nat.ne_of_lt (tie_lt after) same.symm).elim

/-- A root clique can be placed first, with its vertices ordered by the
supplied priority. The rest of the graph is oriented without creating
any unshielded collider. -/
theorem orient_with_root_clique (tree : RootedJoinTree adj m)
    (clique : Fin n → Prop) (inRoot : ∀ v, clique v → tree.inBag tree.root v)
    (priority : Fin n → Nat) :
    ∃ H : DAG n,
      (∀ u v, Adjacent H u v ↔ adj u v) ∧
      (∀ u v w, ¬ UnshieldedCollider H u v w) ∧
      (∀ u v, clique u → clique v → priority u < priority v → adj u v → H.edge u v = true) ∧
      (∀ u v, clique u → ¬ clique v → adj u v → H.edge u v = true) := by
  classical
  obtain ⟨first, first_spec⟩ := tree.exists_first_bags
  let tie := fun v => n * priority v + v.val
  let bound := maxKey tie
  let offset := fun v => if clique v then tie v else bound + tie v
  let rank := fun v => (2 * bound) * tree.depth (first v) + offset v
  have bounded (u) : offset u < 2 * bound := by
    have known := key_lt_max tie u
    change tie u < bound at known
    by_cases chosen : clique u <;> simp [offset, chosen] <;> omega
  have depthBefore {u v : Fin n} (earlier : tree.depth (first u) < tree.depth (first v)) :
      rank u < rank v := lex_lt earlier (bounded u)
  have injective {u v : Fin n} (eq : rank u = rank v) : u = v := by
    rcases Nat.lt_trichotomy (tree.depth (first u)) (tree.depth (first v)) with before | same | after
    · exact (Nat.ne_of_lt (depthBefore before) eq).elim
    · have offsetEq : offset u = offset v := by
        simp only [rank, same, Nat.add_left_cancel_iff] at eq
        exact eq
      have hu : tie u < bound := key_lt_max tie u
      have hv : tie v < bound := key_lt_max tie v
      have tieEq : tie u = tie v := by
        by_cases huC : clique u <;> by_cases hvC : clique v <;>
          simp [offset, huC, hvC] at offsetEq <;> omega
      exact tie_injective priority tieEq
    · exact (Nat.ne_of_lt (depthBefore after) eq.symm).elim
  let H : DAG n := ⟨fun u v => decide (adj u v ∧ rank u < rank v), rank,
    fun _ _ h => (of_decide_eq_true h).2⟩
  have skeleton (u v) : Adjacent H u v ↔ adj u v := by
    constructor
    · rintro (fwd | rev)
      · exact (of_decide_eq_true fwd).1
      · exact tree.adj_symm (of_decide_eq_true rev).1
    · intro edge
      rcases Nat.lt_trichotomy (rank u) (rank v) with before | equal | after
      · exact .inl (decide_eq_true ⟨edge, before⟩)
      · exact (((tree.covers_edges u v).mp edge).1 (injective equal)).elim
      · exact .inr (decide_eq_true ⟨tree.adj_symm edge, after⟩)
  have depthLe {u v : Fin n} (h : H.edge u v = true) :
      tree.depth (first u) ≤ tree.depth (first v) := by
    apply Nat.le_of_not_gt
    intro earlier
    exact Nat.lt_asymm (H.edge_increases _ _ h) (depthBefore earlier)
  have rootDepth (v) (chosen : clique v) : tree.depth (first v) = tree.depth tree.root := by
    have towardRoot := (first_spec tree.root v (inRoot v chosen)).2
    by_cases same : first v = tree.root
    · rw [same]
    · have before := tree.strict towardRoot same
      have later := tree.strict (tree.root_ancestor (first v)) (fun h => same h.symm)
      omega
  refine ⟨H, skeleton, ?_, ?_, ?_⟩
  · intro u v w collider
    have appears (s) (edge : H.edge s v = true) : tree.inBag (first v) s :=
      tree.appears_in_center_bag first first_spec (skeleton s v |>.mp (.inl edge)) (depthLe edge)
    exact collider.2.1 ((skeleton u w).mpr ((tree.covers_edges u w).mpr
      ⟨collider.1, first v, appears u collider.2.2.1, appears w collider.2.2.2⟩))
  · intro u v cu cv h edge
    have before : tie u < tie v := tie_lt h
    apply decide_eq_true
    refine ⟨edge, ?_⟩
    simpa [rank, offset, cu, cv, rootDepth u cu, rootDepth v cv] using before
  · intro u v cu cv edge
    have depthBound : tree.depth (first u) ≤ tree.depth (first v) := by
      rw [rootDepth u cu]
      by_cases equal : tree.root = first v
      · rw [equal]
        exact Nat.le_refl _
      · exact Nat.le_of_lt (tree.strict (tree.root_ancestor _) equal)
    apply decide_eq_true
    refine ⟨edge, ?_⟩
    rcases Nat.lt_or_eq_of_le depthBound with lower | same
    · exact depthBefore lower
    · have earlier : tie u < bound + tie v := by
        have hu : tie u < bound := key_lt_max tie u
        omega
      simpa [rank, offset, cu, cv, same] using earlier

end RootedJoinTree
end
end OpenCausalScience.Papers.Meek1995.JoinTreeOrientation
