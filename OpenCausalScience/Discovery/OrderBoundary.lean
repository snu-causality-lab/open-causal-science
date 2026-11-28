module
public import OpenCausalScience.Probability.Graphoid
public import OpenCausalScience.Discovery.OrderDAG

/-! # Ordered Markov boundaries from singleton queries

The boundary rule is (RU) in Lam, Andrews and Ramsey, Supplement A.3,
https://proceedings.mlr.press/v180/lam22a/lam22a-supp.pdf#page=2.
-/

namespace OpenCausalScience.Discovery

open Probability.CI

@[expose] public section

variable {n : Nat}

def MatchesOracle (J : Relation n) (independent : CIOracle n) : Prop :=
  ∀ x y Z, x ≠ y → Z x = false → Z y = false →
    (independent x y Z = true ↔ J (single x) (single y) Z)

/-- A classical singleton oracle for any set-valued independence relation. -/
noncomputable def singletonOracle (J : Relation n) : CIOracle n := by
  classical
  exact fun x y Z => decide (J (single x) (single y) Z)

theorem singleton_oracle_matches (J : Relation n) : MatchesOracle J (singletonOracle J) := by
  classical
  intro x y Z _ _ _
  simp [singletonOracle]

def predecessors (order : Fin n → Nat) (v : Fin n) : Mask n :=
  fun u => decide (order u < order v)

def OrderedLocalMarkov (G : DAG n) (order : Fin n → Nat) (J : Relation n) : Prop :=
  ∀ v, J (single v) (diff (predecessors order v) (fun u => G.edge u v))
    (fun u => G.edge u v)

def IsBlanket (J : Relation n) (x : Fin n) (U B : Mask n) : Prop :=
  Subset B U ∧ J (single x) (diff U B) B

private def ofList (xs : List (Fin n)) : Mask n := fun x => xs.contains x

private theorem of_list_cons (x : Fin n) (xs : List (Fin n)) :
    ofList (x :: xs) = union (single x) (ofList xs) := by
  funext v
  by_cases equal : v = x <;> simp [ofList, union, single, equal]

private theorem diff_pair_cancel {U A B : Mask n} (bInside : Subset B U)
    (abDisjoint : Disjoint A B) : union (diff U (union A B)) B = diff U A := by
  funext v
  cases hb : B v with
  | false => simp [union, diff, hb]
  | true => simp [union, diff, hb, bInside v hb, abDisjoint.symm v hb]

private theorem joint_of_list {J : Relation n} (g : Graphoid J) {X U : Mask n}
    (disj : Disjoint X U) (xs : List (Fin n)) (nodup : xs.Nodup)
    (inside : ∀ v ∈ xs, U v = true)
    (each : ∀ v ∈ xs, J X (single v) (diff U (single v))) :
    J X (ofList xs) (diff U (ofList xs)) := by
  induction xs with
  | nil =>
    have none : ofList ([] : List (Fin n)) = empty := rfl
    rw [none, show diff U empty = U by funext v; simp [diff, empty]]
    exact g.empty_right X U
  | cons v rest ih =>
    obtain ⟨fresh, restDistinct⟩ := List.nodup_cons.mp nodup
    let A := single v
    let B := ofList rest
    let C := diff U (union A B)
    have subA : Subset A U := by
      intro u inA
      have same : u = v := by simpa [A, single] using inA
      simpa [same] using inside v (List.mem_cons_self)
    have subB : Subset B U := fun u inB => inside u (List.mem_cons_of_mem _ (List.contains_iff_mem.mp inB))
    have ab : Disjoint A B := by
      intro u inA
      have same : u = v := by simpa [A, single] using inA
      simpa [B, ofList, same] using fresh
    have ca : Disjoint C A := (disjoint_diff_right U (union A B)).restrict_right (subset_union_left A B)
    have cb : Disjoint C B := (disjoint_diff_right U (union A B)).restrict_right (subset_union_right A B)
    have blocks : Disjoint4 X A B C :=
      ⟨⟨disj.restrict_right subA, disj.restrict_right subB, ab⟩,
        disj.restrict_right (subset_diff_left U _), ca.symm, cb.symm⟩
    have first : J X A (union C B) := by
      rw [show union C B = diff U A from diff_pair_cancel subB ab]
      exact each v List.mem_cons_self
    have second : J X B (union C A) := by
      have eqUnion : union A B = union B A := by
        funext u
        simp [union, Bool.or_comm]
      change J X B (union (diff U (union A B)) A)
      rw [eqUnion, diff_pair_cancel subA ab.symm]
      exact ih restDistinct (fun u mem => inside u (List.mem_cons_of_mem _ mem))
        (fun u mem => each u (List.mem_cons_of_mem _ mem))
    rw [of_list_cons]
    exact g.intersection blocks first second

/-- Intersection combines all singleton exclusions relative to one fixed set. -/
theorem joint_of_singleton_exclusions {J : Relation n} (g : Graphoid J) {X U Y : Mask n}
    (disj : Disjoint X U) (sub : Subset Y U)
    (each : ∀ v, Y v = true → J X (single v) (diff U (single v))) :
    J X Y (diff U Y) := by
  let xs := (List.finRange n).filter Y
  have eq : ofList xs = Y := by
    funext v
    apply Bool.eq_iff_iff.mpr
    simp [xs, ofList]
  rw [← eq]
  apply joint_of_list g disj xs ((List.nodup_finRange n).filter _)
  · intro v mem
    exact sub v (List.mem_filter.mp mem).2
  · intro v mem
    exact each v (List.mem_filter.mp mem).2

private theorem remove_nonparents {U B : Mask n} (sub : Subset B U) :
    diff U (diff U B) = B := by
  funext v
  cases hb : B v with
  | false => simp [diff, hb]
  | true => simp [diff, hb, sub v hb]

/-- Retain a vertex of the ambient set precisely when its exclusion fails
the test conditional on all other vertices of that set. -/
def markovBoundary (independent : CIOracle n) (x : Fin n) (U : Mask n) : Mask n :=
  fun u => U u && !independent x u (diff U (single u))

/-- The singleton exclusions simultaneously produce a Markov blanket. -/
theorem markov_boundary_is_blanket {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent)
    (x : Fin n) (U : Mask n) (outside : U x = false) :
    IsBlanket J x U (markovBoundary independent x U) := by
  let pa := markovBoundary independent x U
  have sub : Subset pa U := fun u hu => (Bool.and_eq_true_iff.mp hu).1
  have disj : Disjoint (single x) U := by
    intro u hu
    simpa [show u = x by simpa [single] using hu] using outside
  refine ⟨sub, ?_⟩
  have joint := joint_of_singleton_exclusions g disj (subset_diff_left U pa)
    (Y := diff U pa) (by
      intro u excluded
      have mem : U u = true := (Bool.and_eq_true_iff.mp excluded).1
      have distinct : x ≠ u := by
        intro same
        exact Bool.false_ne_true ((same ▸ outside).symm.trans mem)
      have absent : pa u = false := by simpa using (Bool.and_eq_true_iff.mp excluded).2
      have indep : independent x u (diff U (single u)) = true := by
        cases fail : independent x u (diff U (single u))
        · simp [pa, markovBoundary, mem, fail] at absent
        · rfl
      exact (agrees x u (diff U (single u)) distinct
        (by simp [diff, outside]) (by simp [diff, single])).mp indep)
  rwa [remove_nonparents sub] at joint

private theorem omitted_independent {J : Relation n} (g : Semigraphoid J)
    {x u : Fin n} {U B : Mask n} (xOutside : U x = false) (uInside : U u = true)
    (uOutside : B u = false) (blanket : IsBlanket J x U B) :
    J (single x) (single u) (diff U (single u)) := by
  let Y := diff U B
  let V := single u
  have sU : Disjoint (single x) U := by
    intro v hv
    simpa [show v = x by simpa [single] using hv] using xOutside
  have vY : Subset V Y := by
    intro v hv
    have equal : v = u := by simpa [V, single] using hv
    simp [Y, diff, equal, uInside, uOutside]
  have vyU := vY.trans (subset_diff_left U B)
  have restY := subset_diff_left Y V
  have restU := restY.trans (subset_diff_left U B)
  have offB := disjoint_diff_right U B
  have blocks : Disjoint4 (single x) V (diff Y V) B :=
    ⟨⟨sU.restrict_right vyU, sU.restrict_right restU, (disjoint_diff_right Y V).symm⟩,
      sU.restrict_right blanket.1, offB.restrict_left vY, offB.restrict_left restY⟩
  have split : J (single x) (union V (diff Y V)) B := by
    rw [union_eq_of_subset_diff vY]
    exact blanket.2
  have cond : union B (diff Y V) = diff U V := by
    funext v
    cases hb : B v with
    | false => simp [union, diff, Y, hb]
    | true =>
      have different : v ≠ u := fun equal => Bool.false_ne_true (uOutside.symm.trans (equal ▸ hb))
      simp [union, diff, Y, V, single, hb, blanket.1 v hb, different]
  have shifted := g.weak_union blocks split
  rwa [cond] at shifted

/-- The (RU) blanket is contained in every blanket, as in Lemma A.3. -/
theorem markov_boundary_subset_of_blanket {J : Relation n} {independent : CIOracle n}
    (g : Semigraphoid J) (agrees : MatchesOracle J independent) {x : Fin n} {U B : Mask n}
    (outside : U x = false) (blanket : IsBlanket J x U B) :
    Subset (markovBoundary independent x U) B := by
  intro u retain
  cases absent : B u with
  | true => rfl
  | false =>
    obtain ⟨inside, dependent⟩ := Bool.and_eq_true_iff.mp retain
    have distinct : x ≠ u := by
      intro same
      exact Bool.false_ne_true ((same ▸ outside).symm.trans inside)
    have indep := (agrees x u (diff U (single u)) distinct
      (by simp [diff, outside]) (by simp [diff, single])).mpr
      (omitted_independent g outside inside absent blanket)
    simp [indep] at dependent

/-- A minimal blanket equals the (RU) blanket. This identifies the unique
boundary of Lemma A.2 and the arrow sets of the two constructions in A.4. -/
theorem markov_boundary_eq_of_minimal_blanket {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) {x : Fin n} {U B : Mask n}
    (outside : U x = false) (blanket : IsBlanket J x U B)
    (minimal : ∀ C, IsBlanket J x U C → Subset C B → Subset B C) :
    markovBoundary independent x U = B := by
  have sub := markov_boundary_subset_of_blanket g.toSemigraphoid agrees outside blanket
  have sup := minimal _ (markov_boundary_is_blanket g agrees x U outside) sub
  funext v
  exact Bool.eq_iff_iff.mpr ⟨sub v, sup v⟩

/-- The pairwise order tests yield the ordered local independence statement
with all nonparents in one joint block. -/
theorem order_dag_ordered_local {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (order : Fin n → Nat) :
    OrderedLocalMarkov (orderDAG order independent) order J := by
  intro v
  exact (markov_boundary_is_blanket g agrees v (predecessors order v)
    (by simp [predecessors])).2

end

end OpenCausalScience.Discovery
