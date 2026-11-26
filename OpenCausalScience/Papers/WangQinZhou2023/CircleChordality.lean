module
public import OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge

/-! The circle-graph argument of Wang, Qin and Zhou (2023), Appendix B,
Lemma 14. Step 2 is represented by its strict-inclusion and propagation
demands. The last step assumes the circle preservation conclusion of
Lemma 13 and the relevant R2 closure of the final graph.
Source: https://doi.org/10.1016/j.artint.2023.103964
-/

namespace OpenCausalScience.Papers.WangQinZhou2023.CircleChordality

open LocalBackgroundKnowledge MixedGraph

@[expose] public section

variable {n : Nat}

def FSubset (F : Fin n → Fin n → Prop) (u v : Fin n) : Prop :=
  ∀ t, F u t → F v t

def FEqual (F : Fin n → Fin n → Prop) (u v : Fin n) : Prop :=
  ∀ t, F u t ↔ F v t

/-- The directions demanded by the two clauses of Step 2, on the
circle edges among the possible descendants other than the treatment. -/
inductive Step2 (P : PMG n) (active : Fin n → Prop) (F : Fin n → Fin n → Prop) :
    Fin n → Fin n → Prop
  | strict {u v} : active u → active v → P.CircleEdge u v →
      FSubset F v u → (∃ t, F u t ∧ ¬ F v t) → Step2 P active F u v
  | propagate {a u v} : Step2 P active F a u → active v → P.CircleEdge u v →
      FEqual F u v → a ≠ v → ¬ P.Adjacent a v → Step2 P active F u v

variable {P Q : PMG n} {active : Fin n → Prop} {F : Fin n → Fin n → Prop}

private theorem circle_symm {u v : Fin n} (circle : P.CircleEdge u v) : P.CircleEdge v u :=
  ⟨circle.2, circle.1⟩

private theorem circle_adjacent {u v : Fin n} (circle : P.CircleEdge u v) :
    P.Adjacent u v := by
  simp [PMG.Adjacent, circle.1]

private theorem adjacent_symm {u v : Fin n} (adjacent : P.Adjacent u v) : P.Adjacent v u := by
  unfold PMG.Adjacent at *
  rw [P.same_adjacencies v u]
  exact adjacent

/-- A circle edge connects distinct vertices. -/
theorem circle_distinct {u v : Fin n} (circle : P.CircleEdge u v) : u ≠ v := by
  intro same
  subst v
  have mark := circle.1
  simp [P.loop_free] at mark

/-- Both endpoints of any Step 2 demand are active and were joined by a circle edge. -/
theorem step2_endpoints {u v : Fin n} (demand : Step2 P active F u v) :
    active u ∧ active v ∧ P.CircleEdge u v := by
  induction demand with
  | strict left right circle _ _ => exact ⟨left, right, circle⟩
  | propagate _ right circle _ _ _ prior => exact ⟨prior.2.1, right, circle⟩

/-- A demanded direction goes from a superset to a subset of the
Algorithm 1 sets. -/
theorem subset_along_step2 {u v : Fin n} (demand : Step2 P active F u v) : FSubset F v u := by
  cases demand with
  | strict _ _ _ includes _ => exact includes
  | propagate _ _ _ equal _ _ => exact fun t => (equal t).mpr

def ResidualCircle (P : PMG n) (active : Fin n → Prop) (F : Fin n → Fin n → Prop)
    (u v : Fin n) : Prop :=
  P.CircleEdge u v ∧ ¬ Step2 P active F u v ∧ ¬ Step2 P active F v u

private theorem residual_symm {u v : Fin n} (edge : ResidualCircle P active F u v) :
    ResidualCircle P active F v u :=
  ⟨circle_symm edge.1, edge.2.2, edge.2.1⟩

def Comparable (P : PMG n) (active : Fin n → Prop) (F : Fin n → Fin n → Prop) : Prop :=
  ∀ {u v}, active u → active v → P.CircleEdge u v → FSubset F u v ∨ FSubset F v u

/-- Comparable F sets on an edge that stays a circle must be equal. -/
theorem equal_on_residual {u v : Fin n}
    (comparable : Comparable P active F) (uActive : active u) (vActive : active v)
    (circle : ResidualCircle P active F u v) : FEqual F u v := by
  intro t
  rcases comparable uActive vActive circle.1 with uv | vu
  · refine ⟨uv t, ?_⟩
    intro vt
    apply Classical.byContradiction
    intro notUt
    exact circle.2.2 (.strict vActive uActive (circle_symm circle.1) uv ⟨t, vt, notUt⟩)
  · refine ⟨?_, vu t⟩
    intro ut
    apply Classical.byContradiction
    intro notVt
    exact circle.2.1 (.strict uActive vActive circle.1 vu ⟨t, ut, notVt⟩)

/-- Under the earlier PMG's Balanced property and R11, an adjacency
within a circle component is itself a circle edge. -/
theorem adjacent_in_circle_component {u v : Fin n} (balanced : P.BalancedArrowheads)
    (tailIntoHead : ∀ {a b}, P.markAt a b = some .tail → P.ArrowInto a b)
    (path : Reach P.CircleEdge u v) (reversePath : Reach P.CircleEdge v u)
    (adjacent : P.Adjacent u v) : P.CircleEdge u v := by
  have noUv : ¬ P.ArrowInto u v := fun arrow =>
    PMG.source_outside_circle_component balanced arrow reversePath
  have noVu : ¬ P.ArrowInto v u := fun arrow =>
    PMG.source_outside_circle_component balanced arrow path
  have markCircle {a b : Fin n} (adj : P.Adjacent a b)
      (noAb : ¬ P.ArrowInto a b) (noBa : ¬ P.ArrowInto b a) :
      P.markAt a b = some .circle := by
    obtain ⟨mark, here⟩ := Option.isSome_iff_exists.mp adj
    cases mark with
    | circle => exact here
    | tail => exact (noAb (tailIntoHead here)).elim
    | arrow => exact (noBa here).elim
  exact ⟨markCircle adjacent noUv noVu, markCircle (adjacent_symm adjacent) noVu noUv⟩

/-- A directed chain cannot meet a circle shortcut in an R2-closed PMG. -/
def NoDirectedChainWithCircleShortcut (P : PMG n) (active : Fin n → Prop)
    (F : Fin n → Fin n → Prop) : Prop :=
  ∀ {a b c}, Step2 P active F a b → Step2 P active F b c →
    ResidualCircle P active F a c → False

/-- The triangle obstruction in Lemma 14. The argument descends the
finite Step 2 derivation and keeps the third vertex fixed. -/
theorem no_directed_chord_of_residual_two_step
    (balanced : P.BalancedArrowheads)
    (tailIntoHead : ∀ {a b}, P.markAt a b = some .tail → P.ArrowInto a b)
    (comparable : Comparable P active F)
    (noChain : NoDirectedChainWithCircleShortcut P active F)
    {u v w : Fin n} (directed : Step2 P active F u v) (wActive : active w) :
    ResidualCircle P active F u w → ResidualCircle P active F w v → False := by
  induction directed with
  | @strict u v hu hv _ _ strict =>
    intro uw wv
    have equiv₁ := equal_on_residual comparable hu wActive uw
    have equiv₂ := equal_on_residual comparable wActive hv wv
    obtain ⟨t, ut, notVt⟩ := strict
    exact notVt ((equiv₂ t).mp ((equiv₁ t).mp ut))
  | @propagate a u v earlier vActive _ _ distinct notAv ih =>
    intro uw wv
    have ⟨aActive, uActive, au⟩ := step2_endpoints earlier
    have uwEqual := equal_on_residual comparable uActive wActive uw
    have wvEqual := equal_on_residual comparable wActive vActive wv
    have aAdjacentW : P.Adjacent a w := by
      apply Classical.byContradiction
      intro absent
      have different : a ≠ w := by
        intro same
        subst a
        exact notAv (circle_adjacent wv.1)
      exact uw.2.1 (.propagate earlier wActive uw.1 uwEqual different absent)
    have aw := adjacent_in_circle_component balanced tailIntoHead
      (.extend (.extend (.refl a) au) uw.1)
      (.extend (.extend (.refl w) (circle_symm uw.1)) (circle_symm au))
      aAdjacentW
    have notAW : ¬ Step2 P active F a w := fun head =>
      wv.2.1 (.propagate head vActive wv.1 wvEqual distinct notAv)
    have notWA : ¬ Step2 P active F w a := fun head =>
      noChain head earlier (residual_symm uw)
    exact ih ⟨aw, notAW, notWA⟩ (residual_symm uw)

/-- The original circle triangle case of Lemma 15. A new head propagates
to the third vertex if the second edge stays a circle. -/
theorem step2_head_along_residual (balanced : P.BalancedArrowheads)
    (tailIntoHead : ∀ {a b}, P.markAt a b = some .tail → P.ArrowInto a b)
    (comparable : Comparable P active F) (noChain : NoDirectedChainWithCircleShortcut P active F)
    {a b c : Fin n} (ab : Step2 P active F a b) (cActive : active c)
    (bc : ResidualCircle P active F b c) (ac : P.CircleEdge a c) : Step2 P active F a c := by
  apply Classical.byContradiction
  intro notAc
  have notCa : ¬ Step2 P active F c a := fun ca => noChain ca ab (residual_symm bc)
  exact no_directed_chord_of_residual_two_step balanced tailIntoHead comparable noChain ab cActive
    ⟨ac, notAc, notCa⟩ (residual_symm bc)

/-- One of the local hypotheses used to carry Step 2's circle structure
through Step 3. It follows from closure under the directed case of R2. -/
theorem no_chain_of_r2
    (directed : ∀ {u v}, Step2 P active F u v → Q.Directed u v)
    (retained : ∀ {u v}, active u → active v → ResidualCircle P active F u v → Q.CircleEdge u v)
    (r2 : ∀ {a b c}, Q.Directed a b → Q.Directed b c →
      Q.markAt c a = some .circle → Q.ArrowInto a c) :
    NoDirectedChainWithCircleShortcut P active F := by
  intro a b c ab bc ac
  have circ := (retained (step2_endpoints ab).1 (step2_endpoints bc).2.1 ac).2
  have arrow := r2 (directed ab) (directed bc) circ
  simp [PMG.ArrowInto, circ] at arrow

/-- A simple cycle of circle edges on at least four vertices. The
function is inspected only at indices less than its length. -/
structure CircleCycle (P : PMG n) (v : Nat → Fin n) (length : Nat) : Prop where
  large : 4 ≤ length
  along : ∀ i, i + 1 < length → P.CircleEdge (v i) (v (i + 1))
  closing : P.CircleEdge (v (length - 1)) (v 0)
  simple : ∀ {i j}, i < length → j < length → v i = v j → i = j

def ChordAt (P : PMG n) (v : Nat → Fin n) (length i j : Nat) : Prop :=
  i + 1 < j ∧ j < length ∧ (i ≠ 0 ∨ j + 1 < length) ∧ P.CircleEdge (v i) (v j)

def CircleChordal (P : PMG n) : Prop :=
  ∀ {v length}, CircleCycle P v length → ∃ i j, ChordAt P v length i j

private theorem elementary_chord {v : Nat → Fin n} {length : Nat}
    (chordal : CircleChordal P) (cycle : CircleCycle P v length) {i j : Nat}
    (chord : ChordAt P v length i j) : ∃ k, ChordAt P v length k (k + 2) := by
  suffices reduce : ∀ span i j, j - i = span → ChordAt P v length i j →
      ∃ k, ChordAt P v length k (k + 2) by exact reduce _ _ _ rfl chord
  intro span
  induction span using Nat.strongRecOn with
  | ind span ih =>
    rintro i j jump ⟨nonconsecutive, inside, notClosing, edge⟩
    by_cases small : j = i + 2
    · subst j
      exact ⟨i, nonconsecutive, inside, notClosing, edge⟩
    have distance : i + span = j := by omega
    let segment := fun t => v (i + t)
    have subCycle : CircleCycle P segment (span + 1) :=
      ⟨by omega,
        fun k within => by
          simpa [segment, Nat.add_assoc] using cycle.along (i + k) (by omega),
        by simpa [segment, distance] using circle_symm edge,
        fun pBound qBound same => by
          have positions := cycle.simple (by omega) (by omega) same
          omega⟩
    obtain ⟨a,b,apart, subInside, notEnds, subEdge⟩ := chordal subCycle
    have strict : (i + b) - (i + a) < span := by
      rcases notEnds with notA | notB <;> omega
    have keep : i + a ≠ 0 ∨ i + b + 1 < length := by
      rcases notClosing with notI | space
      · left
        omega
      · right
        omega
    exact ih _ strict (i + a) (i + b) rfl ⟨by omega, by omega, keep, subEdge⟩

/-- The three circle-region facts in the proof of Lemma 14. In the
application, the active region is the possible descendants after
excluding the selected vertices and the treatment. The treatment can
lose its old circle edges and has no incident circle edge in the result. -/
structure UpdatedCircles (P Q : PMG n) (active : Fin n → Prop) (F : Fin n → Fin n → Prop) :
    Prop where
  noCrossing : ∀ {u v}, Q.CircleEdge u v → (active u ↔ active v)
  outside : ∀ {u v}, ¬ active u → ¬ active v →
    (∃ a, Q.CircleEdge u a) → (∃ b, Q.CircleEdge v b) → (Q.CircleEdge u v ↔ P.CircleEdge u v)
  inside : ∀ {u v}, active u → active v → (Q.CircleEdge u v ↔ ResidualCircle P active F u v)

/-- Chordality preservation in Lemma 14. Only the unchanged circle
region and the residual Step 2 region need to be considered. Any
shortest old chord in the latter spans two steps and the triangle
obstruction prevents assigning either direction to that chord. -/
theorem chordal_after_local_updates_of_no_chain (priorChordal : CircleChordal P)
    (balanced : P.BalancedArrowheads)
    (tailIntoHead : ∀ {a b}, P.markAt a b = some .tail → P.ArrowInto a b)
    (comparable : Comparable P active F)
    (noChain : NoDirectedChainWithCircleShortcut P active F)
    (updated : UpdatedCircles P Q active F) :
    CircleChordal Q := by
  intro vertices length cycle
  have region : ∀ i, i < length → (active (vertices 0) ↔ active (vertices i)) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro bound
      exact (ih (by omega)).trans (updated.noCrossing (cycle.along i bound))
  by_cases inActive : active (vertices 0)
  · have allActive i (bound : i < length) := (region i bound).mp inActive
    have oldCycle : CircleCycle P vertices length :=
      ⟨cycle.large,
        fun i bound => ((updated.inside (allActive i (by omega))
          (allActive (i + 1) bound)).mp (cycle.along i bound)).1,
        ((updated.inside (allActive (length - 1) (by have := cycle.large; omega))
          inActive).mp cycle.closing).1,
        cycle.simple⟩
    obtain ⟨i,j, oldChord⟩ := priorChordal oldCycle
    obtain ⟨k, apart, bound, notClosing, chord⟩ := elementary_chord priorChordal oldCycle oldChord
    have aActive := allActive k (by omega)
    have bActive := allActive (k+1) (by omega)
    have cActive := allActive (k+2) bound
    have ab := (updated.inside aActive bActive).mp (cycle.along k (by omega))
    have bc := (updated.inside bActive cActive).mp (cycle.along (k+1) bound)
    have noAC : ¬ Step2 P active F (vertices k) (vertices (k+2)) := fun arrow =>
      no_directed_chord_of_residual_two_step balanced tailIntoHead comparable noChain arrow bActive ab bc
    have noCA : ¬ Step2 P active F (vertices (k+2)) (vertices k) := fun arrow =>
      no_directed_chord_of_residual_two_step balanced tailIntoHead comparable noChain arrow bActive
        (residual_symm bc) (residual_symm ab)
    exact ⟨k, k+2, apart, bound, notClosing, (updated.inside aActive cActive).mpr ⟨chord, noAC, noCA⟩⟩
  · have allOutside i (bound : i < length) : ¬ active (vertices i) :=
      fun activeI => inActive ((region i bound).mpr activeI)
    have incident i (bound : i < length) : ∃ w, Q.CircleEdge (vertices i) w := by
      by_cases next : i + 1 < length
      · exact ⟨vertices (i + 1), cycle.along i next⟩
      · have last : i = length - 1 := by omega
        exact ⟨vertices 0, last ▸ cycle.closing⟩
    have outsideEdges {i j : Nat} (hi : i < length) (hj : j < length) :
        Q.CircleEdge (vertices i) (vertices j) ↔ P.CircleEdge (vertices i) (vertices j) :=
      updated.outside (allOutside i hi) (allOutside j hj) (incident i hi) (incident j hj)
    have oldCycle : CircleCycle P vertices length :=
      ⟨cycle.large,
        fun i bound => (outsideEdges (by omega) bound).mp (cycle.along i bound),
        (outsideEdges (by have := cycle.large; omega) (by have := cycle.large; omega)).mp cycle.closing,
        cycle.simple⟩
    obtain ⟨i,j, apart, bound, notClosing, chord⟩ := priorChordal oldCycle
    exact ⟨i, j, apart, bound, notClosing, (outsideEdges (by omega) bound).mpr chord⟩

/-- Corollary when the triangle constraint comes from R2 closure. -/
theorem chordal_after_local_updates (priorChordal : CircleChordal P)
    (balanced : P.BalancedArrowheads)
    (tailIntoHead : ∀ {a b}, P.markAt a b = some .tail → P.ArrowInto a b)
    (comparable : Comparable P active F)
    (updated : UpdatedCircles P Q active F)
    (directed : ∀ {u v}, Step2 P active F u v → Q.Directed u v)
    (r2 : ∀ {a b c}, Q.Directed a b → Q.Directed b c →
      Q.markAt c a = some .circle → Q.ArrowInto a c) :
    CircleChordal Q :=
  chordal_after_local_updates_of_no_chain priorChordal balanced tailIntoHead comparable
    (no_chain_of_r2 directed (fun h₁ h₂ edge => (updated.inside h₁ h₂).mpr edge) r2) updated

end
end OpenCausalScience.Papers.WangQinZhou2023.CircleChordality
