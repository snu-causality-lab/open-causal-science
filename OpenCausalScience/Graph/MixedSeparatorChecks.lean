module
public import OpenCausalScience.Graph.MixedSeparators

/-! # Feasible separators and the relative minimality check

The first boundary pass decides feasibility. A proposed separator is
minimal when every optional vertex is anterior to the endpoints or a
required vertex and appears on both search boundaries.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n}

private theorem no_walkConnected_iff_fixed_augmentation {X Y I Z : Fin n → Bool}
    (disjoint : ∀ v, X v = true → Y v = false)
    (leftOutside : ∀ v, X v = true → Z v = false)
    (rightOutside : ∀ v, Y v = true → Z v = false)
    (includes : ∀ v, I v = true → Z v = true)
    (relevant : ∀ v, Z v = true → G.queryAnterior X Y I v = true) :
    ¬ G.WalkConnected X Y Z ↔
      SeparatorBoundary.Separated
        (fun u v => G.colliderAugmented (G.queryAnterior X Y I) u v = true)
        (fun v => X v = true) (fun v => Y v = true) (fun v => Z v = true) := by
  rw [query_anterior_eq includes relevant]
  exact G.no_walkConnected_iff_augmented_separated X Y Z leftOutside rightOutside disjoint

/-- Return all allowed anterior vertices, when that set separates. -/
def findMSeparator (G : MixedGraph n) (X Y I R : Fin n → Bool) : Option (Fin n → Bool) :=
  let A := G.queryAnterior X Y I
  SeparatorBoundary.findSeparator (G.colliderAugmented A) X Y (fun v => R v && A v)

/-- The first pass succeeds exactly when a permitted m-separator exists. -/
theorem find_m_separator_correct (G : MixedGraph n) (X Y I R : Fin n → Bool)
    (disjoint : ∀ v, X v = true → Y v = false)
    (requiredAllowed : ∀ v, I v = true → R v = true)
    (allowedLeft : ∀ v, R v = true → X v = false)
    (allowedRight : ∀ v, R v = true → Y v = false) :
    match G.findMSeparator X Y I R with
    | none => ¬ ∃ Z, G.IsMSeparator X Y I R Z
    | some Z => G.IsMSeparator X Y I R Z := by
  let A := G.queryAnterior X Y I
  let adj := G.colliderAugmented A
  let initial : Fin n → Bool := fun v => R v && A v
  have initialRequired (v) (h : I v = true) : initial v = true :=
    Bool.and_eq_true_iff.mpr ⟨requiredAllowed v h, relevant_condition h⟩
  have separation (Z : Fin n → Bool) (onlyAllowed : ∀ v, Z v = true → R v = true) :=
    G.no_walkConnected_iff_augmented_separated X Y Z
      (fun v hx => Bool.eq_false_iff.mpr (fun hz =>
        Bool.eq_false_iff.mp (allowedLeft v (onlyAllowed v hz)) hx))
      (fun v hy => Bool.eq_false_iff.mpr (fun hz =>
        Bool.eq_false_iff.mp (allowedRight v (onlyAllowed v hz)) hy)) disjoint
  have graphOutput := SeparatorBoundary.find_separator_correct adj X Y I initial initialRequired
  change match SeparatorBoundary.findSeparator adj X Y initial with
    | none => ¬ ∃ Z, G.IsMSeparator X Y I R Z
    | some Z => G.IsMSeparator X Y I R Z
  generalize SeparatorBoundary.findSeparator adj X Y initial = result at graphOutput ⊢
  cases result with
  | none =>
    rintro ⟨Z, includes, inR, separated⟩
    apply graphOutput
    refine ⟨fun v => Z v = true ∧ A v = true, fun v hi => ⟨includes v hi, relevant_condition hi⟩,
      fun v h => Bool.and_eq_true_iff.mpr ⟨inR v h.1, h.2⟩, ?_⟩
    exact fun v hy reach => ((separation Z inR).mp separated) v hy (lift_clamped_reach includes reach)
  | some Z =>
    obtain ⟨includes, inInitial, separated⟩ := graphOutput
    have inR (v) (h : Z v = true) := (Bool.and_eq_true_iff.mp (inInitial v h)).1
    have inA (v) (h : Z v = true) := (Bool.and_eq_true_iff.mp (inInitial v h)).2
    have same : A = G.queryAnterior X Y Z := query_anterior_eq includes inA
    refine ⟨includes, inR, (separation Z inR).mpr ?_⟩
    simpa only [← same] using separated

/-- Require a valid separator, relevance to the fixed anterior set,
and two boundary witnesses for every optional vertex. -/
def mSeparatorIsMinimal (G : MixedGraph n) (X Y I Z : Fin n → Bool) : Bool :=
  let vertices := List.finRange n
  let A := G.queryAnterior X Y I
  let adj := G.colliderAugmented A
  let fromLeft := SeparatorBoundary.boundaryVertices adj X Z
  let fromRight := SeparatorBoundary.boundaryVertices adj Y Z
  (vertices.all fun v => !I v || Z v) &&
    G.mSeparated X Y Z &&
    (vertices.all fun v => !Z v || A v) &&
    (vertices.all fun v => !(Z v && !I v) || (fromLeft.contains v && fromRight.contains v))

private theorem all_implies_iff (left right : Fin n → Bool) :
    ((List.finRange n).all fun v => !left v || right v) = true ↔
      ∀ v, left v = true → right v = true := by
  rw [List.all_eq_true]
  constructor
  · intro all v mem
    simpa [mem] using all v (List.mem_finRange v)
  · intro implies v _
    cases h : left v <;> simp [h, implies v]

private theorem all_boundary_witnesses_iff (G : MixedGraph n) (A X Y I Z : Fin n → Bool) :
    let adj := G.colliderAugmented A
    let fromLeft := SeparatorBoundary.boundaryVertices adj X Z
    let fromRight := SeparatorBoundary.boundaryVertices adj Y Z
    ((List.finRange n).all fun v =>
      !(Z v && !I v) || (fromLeft.contains v && fromRight.contains v)) = true ↔
        ∀ v, Z v = true → I v ≠ true → G.AugmentedReach A X Z v ∧ G.AugmentedReach A Y Z v := by
  dsimp only
  rw [List.all_eq_true]
  constructor
  · intro all v hz hi
    have notRequired := Bool.eq_false_iff.mpr hi
    simpa [hz, notRequired, SeparatorBoundary.mem_boundary_vertices_iff]
      using all v (List.mem_finRange v)
  · intro witnesses v _
    cases hz : Z v
    · simp
    · cases hi : I v
      · simpa [hz, hi, SeparatorBoundary.mem_boundary_vertices_iff]
          using witnesses v hz (by simp [hi])
      · simp

private theorem clamp_m_separator {X Y I R Z : Fin n → Bool}
    (disjoint : ∀ v, X v = true → Y v = false)
    (leftOutside : ∀ v, X v = true → Z v = false)
    (rightOutside : ∀ v, Y v = true → Z v = false)
    (separator : G.IsMSeparator X Y I R Z) :
    G.IsMSeparator X Y I R (fun v => Z v && G.queryAnterior X Y I v) := by
  let A := G.queryAnterior X Y I
  let W : Fin n → Bool := fun v => Z v && A v
  have includes (v) (hi : I v = true) : W v = true :=
    Bool.and_eq_true_iff.mpr ⟨separator.1 v hi, relevant_condition hi⟩
  have within (v) (hw : W v = true) : A v = true :=
    (Bool.and_eq_true_iff.mp hw).2
  have leftW (v) (hx : X v = true) : W v = false := by simp [W, leftOutside v hx]
  have rightW (v) (hy : Y v = true) : W v = false := by simp [W, rightOutside v hy]
  refine ⟨includes, fun v h => separator.2.1 v (Bool.and_eq_true_iff.mp h).1, ?_⟩
  apply (no_walkConnected_iff_fixed_augmentation disjoint leftW rightW includes within).mpr
  intro v hy reach
  apply (G.no_walkConnected_iff_augmented_separated X Y Z
    leftOutside rightOutside disjoint).mp separator.2.2 v hy
  exact lift_clamped_reach separator.1 (reach.map (fun _ hx => .seed hx)
    (fun _ _ same => same) (fun _ h => Bool.and_eq_true_iff.mpr h))

/-- On legal endpoint and candidate sets, the executable test is true
exactly for an inclusion-minimal m-separator that contains the required set. -/
theorem m_separator_is_minimal_correct (G : MixedGraph n) (X Y I Z : Fin n → Bool)
    (disjoint : ∀ v, X v = true → Y v = false)
    (leftOutside : ∀ v, X v = true → Z v = false)
    (rightOutside : ∀ v, Y v = true → Z v = false) :
    G.mSeparatorIsMinimal X Y I Z = true ↔
      G.IsMinimalMSeparator X Y I (fun v => !X v && !Y v) Z := by
  let A := G.queryAnterior X Y I
  let adj := G.colliderAugmented A
  let allowed : Fin n → Bool := fun v => !X v && !Y v
  have allowedZ (v) (hz : Z v = true) : allowed v = true := by
    have hx : X v = false := Bool.eq_false_iff.mpr fun hx =>
      Bool.eq_false_iff.mp (leftOutside v hx) hz
    have hy : Y v = false := Bool.eq_false_iff.mpr fun hy =>
      Bool.eq_false_iff.mp (rightOutside v hy) hz
    simp [allowed, hx, hy]
  have symm : ∀ u v, adj u v = true → adj v u = true := fun u v edge =>
    (G.collider_augmented_symmetric A u v).symm.trans edge
  have transfer (W : Fin n → Bool) (includes : ∀ v, I v = true → W v = true)
      (inside : ∀ v, W v = true → A v = true) (subset : ∀ v, W v = true → Z v = true) :=
    no_walkConnected_iff_fixed_augmentation (G := G) disjoint
      (fun v hx => Bool.eq_false_iff.mpr (fun hw => Bool.eq_false_iff.mp (leftOutside v hx) (subset v hw)))
      (fun v hy => Bool.eq_false_iff.mpr (fun hw => Bool.eq_false_iff.mp (rightOutside v hy) (subset v hw)))
      includes inside
  have boundary_iff (includes : ∀ v, I v = true → Z v = true)
      (inside : ∀ v, Z v = true → A v = true) (separates : ¬ G.WalkConnected X Y Z) :=
    SeparatorBoundary.is_minimal_separator_iff_boundary symm
      (fun v hx => Bool.eq_false_iff.mp (leftOutside v hx)) (fun v hy => Bool.eq_false_iff.mp (rightOutside v hy))
      ⟨includes, allowedZ, (transfer Z includes inside (fun _ h => h)).mp separates⟩
  simp only [mSeparatorIsMinimal, Bool.and_eq_true_iff, m_separated_iff_no_walk,
    all_boundary_witnesses_iff]
  simp only [all_implies_iff]
  constructor
  · rintro ⟨⟨⟨includes, separates⟩, inside⟩, witnesses⟩
    have minimal := (boundary_iff includes inside separates).mpr witnesses
    refine ⟨⟨includes, allowedZ, separates⟩, ?_⟩
    rintro W ⟨requiredW, allowedW, sepW⟩ subset
    exact minimal.2 (fun v => W v = true)
      ⟨requiredW, allowedW, (transfer W requiredW (fun v h => inside v (subset v h)) subset).mp sepW⟩ subset
  · intro minimal
    obtain ⟨includes, _, separates⟩ := minimal.1
    have clamped := clamp_m_separator disjoint leftOutside rightOutside minimal.1
    have inside (v) (hz : Z v = true) : A v = true :=
      (Bool.and_eq_true_iff.mp (minimal.2 _ clamped (fun _ h => (Bool.and_eq_true_iff.mp h).1) v hz)).2
    refine ⟨⟨⟨includes, separates⟩, inside⟩, (boundary_iff includes inside separates).mp ?_⟩
    refine ⟨⟨includes, allowedZ, (transfer Z includes inside (fun _ h => h)).mp separates⟩, ?_⟩
    classical
    intro other permitted subset
    let W : Fin n → Bool := fun v => decide (other v)
    have holds (v) : W v = true ↔ other v := by simp [W]
    have requiredW (v) (h : I v = true) : W v = true := (holds v).mpr (permitted.1 v h)
    have subW (v) (h : W v = true) : Z v = true := subset v ((holds v).mp h)
    have sepW := (transfer W requiredW (fun v h => inside v (subW v h)) subW).mpr (by
      simpa only [holds] using permitted.2.2)
    intro v hz
    exact (holds v).mp (minimal.2 W ⟨requiredW, fun u h => allowedZ u (subW u h), sepW⟩ subW v hz)

end

end OpenCausalScience.MixedGraph
