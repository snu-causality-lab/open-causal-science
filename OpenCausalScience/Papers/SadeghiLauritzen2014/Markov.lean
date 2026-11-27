module
public import OpenCausalScience.Graph.MixedSeparators

/-!
# The compositional graphoid of m-separation

Sadeghi and Lauritzen (2014), Theorem 1, on the finite mixed graphs
supported by `MixedGraph`. The change-of-conditioning arguments use
active walks and stop at the first vertex of the target set.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n} {A B C D : Fin n → Bool}

def SetUnion (A B : Fin n → Bool) : Fin n → Bool :=
  fun v => A v || B v

/-- The independence relation induced by m-separation. -/
def MIndependent (G : MixedGraph n) (A B C : Fin n → Bool) : Prop :=
  ¬ G.WalkConnected A B C

private theorem swap_reach {α : Type} {edge : α → α → Prop}
    {X Z : α → Prop} {v : α} (reach : SeparatorBoundary.Reach edge X Z v)
    (symm : ∀ u w, edge u w → edge w u) (openLast : ¬ Z v) :
    ∃ u, X u ∧ SeparatorBoundary.Reach edge (· = v) Z u := by
  induction reach with
  | seed start => exact ⟨_, start, .seed rfl⟩
  | step _ openVertex next ih =>
    obtain ⟨u, start, rev⟩ := ih openVertex
    exact ⟨u, start, rev.map
      (fun w same => same.symm ▸ .step (.seed rfl) openLast (symm _ _ next))
      (fun _ _ h => h) (fun _ h => h)⟩

theorem m_independent_symmetry
    (aOutside : ∀ v, A v = true → C v = false)
    (bOutside : ∀ v, B v = true → C v = false)
    (disjoint : ∀ v, A v = true → B v = false)
    (sep : G.MIndependent A B C) : G.MIndependent B A C := by
  have disjoint' : ∀ v, B v = true → A v = false := by
    intro v bv
    exact Bool.eq_false_iff.mpr (fun av => by simp [disjoint v av] at bv)
  have antEq : G.queryAnterior A B C = G.queryAnterior B A C := by
    simp only [queryAnterior, Bool.or_comm (A _) (B _)]
  have block := (G.no_walkConnected_iff_augmented_separated _ _ _ aOutside bOutside disjoint).mp sep
  rw [antEq] at block
  apply (G.no_walkConnected_iff_augmented_separated _ _ _ bOutside aOutside disjoint').mpr
  intro v av rev
  obtain ⟨u, bu, forward⟩ := swap_reach rev
    (fun x y h => (G.collider_augmented_symmetric _ x y).symm.trans h) (by simp [aOutside v av])
  exact block u bu (forward.map (fun _ eq => eq.symm ▸ .seed av)
    (fun _ _ h => h) (fun _ h => h))

theorem connected_union_iff :
    G.WalkConnected A (SetUnion B D) C ↔ G.WalkConnected A B C ∨ G.WalkConnected A D C := by
  constructor
  · rintro ⟨first, last, seed, reach, hit⟩
    exact (Bool.or_eq_true_iff.mp hit).imp (⟨first, last, seed, reach, ·⟩)
      (⟨first, last, seed, reach, ·⟩)
  · rintro (⟨first, last, seed, reach, hit⟩ | ⟨first, last, seed, reach, hit⟩)
    · exact ⟨first, last, seed, reach, by simp [SetUnion, hit]⟩
    · exact ⟨first, last, seed, reach, by simp [SetUnion, hit]⟩

/-- Decomposition and composition, respectively the forward and reverse directions. -/
theorem m_independent_union_iff :
    G.MIndependent A (SetUnion B D) C ↔ G.MIndependent A B C ∧ G.MIndependent A D C := by
  simp only [MIndependent, connected_union_iff, not_or]

private theorem reach_append {α : Type} {R : α → α → Prop} {x y z : α}
    (first : Reach R x y) (second : Reach R y z) : Reach R x z := by
  induction second with
  | refl => exact first
  | extend _ h ih => exact .extend ih h

private theorem reach_map {α : Type} {R S : α → α → Prop} {x y : α}
    (path : Reach R x y) (step : ∀ u v, R u v → S u v) : Reach S x y := by
  induction path with
  | refl => exact .refl _
  | extend _ h ih => exact .extend ih (step _ _ h)

private theorem ancestor_grows {v : Fin n} (h : G.AncestorOf C v) :
    G.AncestorOf (SetUnion C D) v := by
  induction h with
  | conditioned present => exact .conditioned (by simp [SetUnion, present])
  | parent arrow _ ih => exact .parent arrow ih

private theorem reaches_descendant {v : Fin n} (h : G.AncestorOf D v)
    (avoid : ¬ G.AncestorOf C v) (incoming : Bool) :
    ∃ last, Reach (G.Step C) (v, incoming) last ∧ D last.1 = true := by
  induction h generalizing incoming with
  | conditioned present => exact ⟨(_, incoming), .refl _, present⟩
  | @parent u v arrow _ ih =>
    obtain ⟨last, path, hit⟩ := ih (fun h => avoid (.parent arrow h)) true
    have outside : C u = false := Bool.eq_false_iff.mpr (fun present => avoid (.conditioned present))
    have directed : G.Step C (u, incoming) (v, true) :=
      ⟨false, arrow, by simpa [openTurn] using outside⟩
    exact ⟨last, reach_append (.extend (.refl _) directed) path, hit⟩

theorem m_independent_weak_union (sep : G.MIndependent A (SetUnion B D) C) :
    G.MIndependent A B (SetUnion C D) := by
  obtain ⟨avoidB, avoidD⟩ := m_independent_union_iff.mp sep
  rintro ⟨first, last, seed, path, hit⟩
  apply avoidB
  refine ⟨first, last, seed, ?_, hit⟩
  clear hit
  induction path with
  | refl => exact .refl _
  | @extend u v _ step ih =>
    obtain ⟨mark, edge, turn⟩ := step
    unfold openTurn at turn
    refine .extend ih ⟨mark, edge, ?_⟩
    unfold openTurn
    by_cases collider : (u.2 && mark) = true
    · simp only [collider, ↓reduceIte] at turn ⊢
      rcases turn.union with old | new
      · exact old
      · classical
        by_cases active : G.AncestorOf C u.1
        · exact active
        · obtain ⟨w, suffix, d⟩ := reaches_descendant new active u.2
          exact (avoidD ⟨first, w, seed, reach_append ih suffix, d⟩).elim
    · simp only [collider, SetUnion, Bool.or_eq_false_iff] at turn ⊢
      exact turn.1

private theorem step_after_adding {s t : Arrival n} (step : G.Step C s t)
    (outside : D s.1 = false) : G.Step (SetUnion C D) s t := by
  obtain ⟨mark, edge, turn⟩ := step
  refine ⟨mark, edge, ?_⟩
  unfold openTurn at turn ⊢
  by_cases collider : (s.2 && mark) = true
  · simp only [collider, ↓reduceIte] at turn ⊢
    exact ancestor_grows turn
  · simp [collider, SetUnion, outside] at turn ⊢
    exact turn

private theorem reach_first_target {Q : Fin n → Bool} {first last : Arrival n}
    (path : Reach (G.Step C) first last) :
    (∃ x, Q x.1 = true ∧ Reach (fun a b => G.Step C a b ∧ Q a.1 = false) first x) ∨
      (Q last.1 = false ∧ Reach (fun a b => G.Step C a b ∧ Q a.1 = false) first last) := by
  induction path with
  | refl =>
    cases hit : Q first.1
    · exact .inr ⟨rfl, .refl _⟩
    · exact .inl ⟨first, hit, .refl _⟩
  | @extend u v _ step ih =>
    rcases ih with found | ⟨avoid, initial⟩
    · exact .inl found
    · have extended := initial.extend ⟨step, avoid⟩
      cases hit : Q v.1
      · exact .inr ⟨rfl, extended⟩
      · exact .inl ⟨v, hit, extended⟩

private theorem reaches_first_of_union {first last : Arrival n}
    (path : Reach (G.Step C) first last) (hit : SetUnion B D last.1 = true) :
    ∃ x, (B x.1 = true ∨ D x.1 = true) ∧
      Reach (G.Step C) first x ∧ Reach (G.Step (SetUnion C B)) first x ∧
        Reach (G.Step (SetUnion C D)) first x := by
  rcases reach_first_target (Q := SetUnion B D) path with ⟨x, hx, initialPath⟩ | avoid
  · exact ⟨x, Bool.or_eq_true_iff.mp hx, reach_map initialPath (fun _ _ h => h.1),
      reach_map initialPath (fun _ _ h => step_after_adding h.1 (Bool.or_eq_false_iff.mp h.2).1),
      reach_map initialPath (fun _ _ h => step_after_adding h.1 (Bool.or_eq_false_iff.mp h.2).2)⟩
  · simp [avoid.1] at hit

theorem m_independent_contraction
    (left : G.MIndependent A B C) (right : G.MIndependent A D (SetUnion C B)) :
    G.MIndependent A (SetUnion B D) C := by
  rintro ⟨first, last, seed, path, hit⟩
  obtain ⟨x, hx, original, withB, _⟩ := reaches_first_of_union path hit
  exact hx.elim (fun b => left ⟨first, x, seed, original, b⟩)
    (fun d => right ⟨first, x, seed, withB, d⟩)

theorem m_independent_intersection
    (left : G.MIndependent A B (SetUnion C D))
    (right : G.MIndependent A D (SetUnion C B)) :
    G.MIndependent A (SetUnion B D) C := by
  rintro ⟨first, last, seed, path, hit⟩
  obtain ⟨x, hx, _, withB, withD⟩ := reaches_first_of_union path hit
  exact hx.elim (fun b => left ⟨first, x, seed, withD, b⟩)
    (fun d => right ⟨first, x, seed, withB, d⟩)

/-- The anterior set of the endpoints, with the endpoints removed. -/
def canonicalPairwiseSet (G : MixedGraph n) (A B : Fin n → Bool) : Fin n → Bool :=
  fun v => !A v && !B v && G.queryAnterior A B (fun _ => false) v

private theorem canonicalOutsideLeft {v : Fin n} (hv : A v = true) :
    G.canonicalPairwiseSet A B v = false := by
  simp [canonicalPairwiseSet, hv]

private theorem canonicalOutsideRight {v : Fin n} (hv : B v = true) :
    G.canonicalPairwiseSet A B v = false := by
  simp [canonicalPairwiseSet, hv]

/-- With no mandatory or forbidden covariates, a separator exists exactly
when the full anterior set minus the endpoints separates. -/
theorem canonical_pairwise_separator (apart : ∀ v, A v = true → B v = false)
    (aOutside : ∀ v, A v = true → C v = false)
    (bOutside : ∀ v, B v = true → C v = false) (sep : G.MIndependent A B C) :
    G.MIndependent A B (G.canonicalPairwiseSet A B) := by
  let I : Fin n → Bool := fun _ => false
  have fixed : G.queryAnterior A B I = G.queryAnterior A B (G.canonicalPairwiseSet A B) :=
    query_anterior_eq (fun _ h => Bool.noConfusion h) (fun _ h => (Bool.and_eq_true_iff.mp h).2)
  have separated := (G.no_walkConnected_iff_augmented_separated _ _ _ aOutside bOutside apart).mp sep
  apply (G.no_walkConnected_iff_augmented_separated _ _ _
    (fun _ => canonicalOutsideLeft) (fun _ => canonicalOutsideRight) apart).mpr
  rw [← fixed]
  intro v bv path
  apply separated v bv
  apply lift_clamped_reach (I := I) (fun _ h => Bool.noConfusion h)
  apply path.map (fun _ h => .seed h) (fun _ _ h => h)
  intro w ⟨cw, anterior⟩
  have aw : A w = false := Bool.eq_false_iff.mpr (fun yes => by simp [aOutside w yes] at cw)
  have bw : B w = false := Bool.eq_false_iff.mpr (fun yes => by simp [bOutside w yes] at cw)
  simp [canonicalPairwiseSet, aw, bw, anterior, I]

/-- Maximality stated by the availability of a separator for every
nonadjacent pair of distinct vertices. -/
def HasPairwiseSeparators (G : MixedGraph n) : Prop :=
  ∀ i j, i ≠ j → (∀ a b, G.edge i a j b = false) →
    ∃ C : Fin n → Bool, C i = false ∧ C j = false ∧ G.MIndependent (· == i) (· == j) C

/-- The global Markov property entails the §6.1 pairwise statements
whenever every nonadjacent pair admits a separator. -/
theorem pairwise_of_global
    {J : (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → Prop}
    (maximal : G.HasPairwiseSeparators)
    (global : ∀ A B C : Fin n → Bool,
      (∀ v, A v = true → B v = false) →
      (∀ v, A v = true → C v = false) →
      (∀ v, B v = true → C v = false) → G.MIndependent A B C → J A B C)
    {i j : Fin n} (different : i ≠ j) (nonadjacent : ∀ a b, G.edge i a j b = false) :
    J (· == i) (· == j) (G.canonicalPairwiseSet (· == i) (· == j)) := by
  obtain ⟨C, ci, cj, sep⟩ := maximal i j different nonadjacent
  have apart : ∀ v : Fin n, (v == i) = true → (v == j) = false := by
    intro v hx
    obtain rfl := beq_iff_eq.mp hx
    exact Bool.eq_false_iff.mpr (fun hy => different (beq_iff_eq.mp hy))
  apply global (· == i) (· == j) (G.canonicalPairwiseSet (· == i) (· == j)) apart
    (fun _ h => by simp [canonicalPairwiseSet, h]) (fun _ h => by simp [canonicalPairwiseSet, h])
  exact canonical_pairwise_separator apart
    (fun _ h => (beq_iff_eq.mp h).symm ▸ ci) (fun _ h => (beq_iff_eq.mp h).symm ▸ cj) sep

end
end OpenCausalScience.MixedGraph
