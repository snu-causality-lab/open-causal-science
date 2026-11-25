import MecLean.CtfScb.MIS

set_option linter.unusedSectionVars false

/-!
# Reducing a counterfactual action to a minimal one

The reduction removes targets whose paths to the reward are blocked by other targets, then
removes those that fail the fixed-input test. A fixed parent-input specification and a complete
target order support the reward and realizability preservation results.
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec

variable {n : ℕ}

/-! ## Auxiliary lemmas -/

/-- The listed arguments of a mechanism are the parents in its diagram. -/
theorem mem_pa_iff_of_diag_eq {G : ADMG n} {Ω : Fin n → Type} {L : Type} {U : L → Type}
    [DecidableEq L] {M : Mech n Ω L U} (hM : M.diag = G) {j v : Fin n} :
    j ∈ M.pa v ↔ G.dir j v = true := by
  rw [← hM]
  exact (M.diag_dir).symm

/-- A directed path of `𝒢_F` is a directed path of `𝒢`. -/
theorem ancAvoid_of_ancAvoid_cutE {G : ADMG n} {F : EdgeSet n} {D : Finset (Fin n)}
    {a b : Fin n} (h : (G.cutE F).AncAvoid D a b) : G.AncAvoid D a b :=
  Reach.mono_rel (R := (G.cutE F).dir) (R' := G.dir)
    (fun _ _ _ h' => (ADMG.cutE_dir.mp h').1) h

theorem mem_reqEdges {G : ADMG n} {X : Finset (Fin n)} {F : EdgeSet n} {e : Fin n × Fin n} :
    e ∈ reqEdges G X F ↔ e ∈ F ∧ G.dir e.1 e.2 = true ∧ ∃ x ∈ X, (G.cutE F).Anc e.2 x := by
  unfold reqEdges
  exact Finset.mem_filter

/-! ## `prop: cover realizable nested counterfactuals` -/

section Cover

variable {G : ADMG n} {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L]
  [∀ i, Inhabited (Ω i)] {M : Mech n Ω L U}

/-- **`prop: cover realizable nested counterfactuals`** for outer-target
actions: the reward of a realizable action equals, on every unit, the reward of its parent-input
specification, the selected inputs required by its targets (`reqEdges`).  ("Inputs that cannot
affect `Y` may be discarded",.) -/
theorem resp_eq_respE_reqEdges (hM : M.diag = G) {y : Fin n} {X : Finset (Fin n)}
    {F : EdgeSet n} (h : Realizable G y X F) (c : Fin n → ∀ p, Ω p) (u : ∀ l, U l) :
    M.resp X (M.respE F c u) u y = M.respE (reqEdges G X F) c u y := by
  -- In the targets' world, a vertex with a directed path of `𝒢_F` to a target receives the
  -- same constants under `F` and under the required inputs.
  have hW : ∀ v, (∃ x ∈ X, (G.cutE F).Anc v x) →
      M.respE F c u v = M.respE (reqEdges G X F) c u v := by
    intro v
    refine rank_induction M.rank (P := fun v => (∃ x ∈ X, (G.cutE F).Anc v x) →
      M.respE F c u v = M.respE (reqEdges G X F) c u v) (fun v ih hv => ?_) v
    rw [M.respE_spec F c u v, M.respE_spec (reqEdges G X F) c u v]
    apply M.f_pa
    intro j hj
    have hjv : G.dir j v = true := (mem_pa_iff_of_diag_eq hM).mp hj
    show (if (j, v) ∈ F then c v j else M.respE F c u j) =
      (if (j, v) ∈ reqEdges G X F then c v j else M.respE (reqEdges G X F) c u j)
    by_cases hjF : (j, v) ∈ F
    · have hjR : (j, v) ∈ reqEdges G X F := mem_reqEdges.mpr ⟨hjF, hjv, hv⟩
      rw [ite_eq_left hjF, ite_eq_left hjR]
    · have hjR : (j, v) ∉ reqEdges G X F := fun hjR => hjF (mem_reqEdges.mp hjR).1
      rw [ite_eq_right hjF, ite_eq_right hjR]
      obtain ⟨x, hx, hvx⟩ := hv
      exact ih j (M.pa_rank hj)
        ⟨x, hx, Reach.head (ADMG.cutE_dir.mpr ⟨hjv, hjF⟩) (Finset.notMem_empty v) hvx⟩
  -- The outer system: a vertex that is a target or reaches `y` avoiding the targets takes its
  -- value in the world of the required inputs; realizability leaves the latter unfixed.
  have hO : ∀ v, (v ∈ X ∨ G.AncAvoid X v y) →
      M.resp X (M.respE F c u) u v = M.respE (reqEdges G X F) c u v := by
    intro v
    refine rank_induction M.rank (P := fun v => (v ∈ X ∨ G.AncAvoid X v y) →
      M.resp X (M.respE F c u) u v = M.respE (reqEdges G X F) c u v) (fun v ih hv => ?_) v
    by_cases hvX : v ∈ X
    · rw [M.resp_of_mem hvX]
      exact hW v ⟨v, hvX, Reach.refl v⟩
    · have hvy : G.AncAvoid X v y := hv.resolve_left hvX
      rw [M.resp_of_not_mem hvX, M.respE_spec (reqEdges G X F) c u v]
      apply M.f_pa
      intro j hj
      have hjv : G.dir j v = true := (mem_pa_iff_of_diag_eq hM).mp hj
      have hjR : (j, v) ∉ reqEdges G X F := by
        intro hjR
        obtain ⟨hjF, -, hex⟩ := mem_reqEdges.mp hjR
        have h0 := h v hvX hvy hex j hjF
        rw [hjv] at h0
        exact Bool.false_ne_true h0.symm
      show M.resp X (M.respE F c u) u j =
        (if (j, v) ∈ reqEdges G X F then c v j else M.respE (reqEdges G X F) c u j)
      rw [ite_eq_right hjR]
      apply ih j (M.pa_rank hj)
      by_cases hjX : j ∈ X
      · exact Or.inl hjX
      · exact Or.inr (Reach.head hjv hvX hvy)
  by_cases hyX : y ∈ X
  · exact hO y (Or.inl hyX)
  · exact hO y (Or.inr (Reach.refl y))

end Cover

/-! ## `ctf-MISify` -/

/-! ### The pass of `ctf-MISify` -/

theorem misifyPass_cons (G : ADMG n) (F : EdgeSet n) (x : Fin n) (ord : List (Fin n))
    (X : Finset (Fin n)) :
    misifyPass G F (x :: ord) X =
      misifyPass G F ord (if x ∈ X ∧ ¬ Cond2 G X F x then X.erase x else X) := rfl

theorem misifyPass_subset (G : ADMG n) (F : EdgeSet n) (ord : List (Fin n)) :
    ∀ X : Finset (Fin n), misifyPass G F ord X ⊆ X := by
  induction ord with
  | nil => exact fun X => Finset.Subset.refl X
  | cons a ord ih =>
    intro X z hz
    rw [misifyPass_cons] at hz
    have hz' := ih _ hz
    by_cases hc : a ∈ X ∧ ¬ Cond2 G X F a
    · rw [ite_eq_left hc] at hz'
      exact Finset.mem_of_mem_erase hz'
    · rw [ite_eq_right hc] at hz'
      exact hz'

/-- A target kept by the pass satisfied condition 2 when it was visited, and keeps it for the
final target set (`Cond2.mono`). -/
theorem misifyPass_cond2 (G : ADMG n) (F : EdgeSet n) (ord : List (Fin n)) :
    ∀ X : Finset (Fin n), ∀ x ∈ misifyPass G F ord X, x ∈ ord →
      Cond2 G (misifyPass G F ord X) F x := by
  induction ord with
  | nil =>
    intro X x _ hx
    exact absurd hx List.not_mem_nil
  | cons a ord ih =>
    intro X x hx hxo
    rw [misifyPass_cons] at hx ⊢
    rcases List.mem_cons.mp hxo with hxa | hxo'
    · rw [hxa] at hx ⊢
      by_cases hc : a ∈ X ∧ ¬ Cond2 G X F a
      · rw [ite_eq_left hc] at hx
        exact absurd (misifyPass_subset G F ord _ hx) (Finset.notMem_erase a X)
      · rw [ite_eq_right hc] at hx ⊢
        have haX : a ∈ X := misifyPass_subset G F ord X hx
        have h2 : Cond2 G X F a := by
          by_contra h2
          exact hc ⟨haX, h2⟩
        exact Cond2.mono (misifyPass_subset G F ord X) h2
    · exact ih _ x hx hxo'

section Resp

variable {G : ADMG n} {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L]
  [∀ i, Inhabited (Ω i)] {M : Mech n Ω L U}

/-- Every deletion of the pass removes a target that fails condition 2 for the current target
set, which preserves the reward on every unit (`resp_erase_of_not_cond2`). -/
theorem misifyPass_resp (hM : M.diag = G) (y : Fin n) (F : EdgeSet n) (c : Fin n → ∀ p, Ω p)
    (u : ∀ l, U l) (ord : List (Fin n)) :
    ∀ S : Finset (Fin n), M.resp (misifyPass G F ord S) (M.respE F c u) u y =
      M.resp S (M.respE F c u) u y := by
  induction ord with
  | nil => intro S; rfl
  | cons a ord ih =>
    intro S
    rw [misifyPass_cons, ih]
    by_cases hc : a ∈ S ∧ ¬ Cond2 G S F a
    · rw [ite_eq_left hc]
      exact resp_erase_of_not_cond2 hM hc.1 hc.2 c u y
    · rw [ite_eq_right hc]

end Resp

/-- The first step of `ctf-MISify` preserves realizability: a directed path to `y` avoiding the
retained targets avoids every target, since its last deleted target would satisfy condition 1. -/
theorem realizable_filter_ancAvoid {G : ADMG n} {y : Fin n} {X : Finset (Fin n)}
    {F : EdgeSet n} (h : Realizable G y X F) :
    Realizable G y (X.filter (fun x => G.AncAvoid X x y)) F := by
  intro v hv hvy hex p hp
  have hvyX : G.AncAvoid X v y := by
    rcases Reach.split_last X hvy with h' | ⟨w, hwX, hwX1, hw⟩
    · exact Reach.mono_avoid Finset.subset_union_right h'
    · exact (hwX1 (Finset.mem_filter.mpr
        ⟨hwX, Reach.mono_avoid Finset.subset_union_right hw⟩)).elim
  have hvX : v ∉ X := fun hvX => hv (Finset.mem_filter.mpr ⟨hvX, hvyX⟩)
  obtain ⟨x, hx, hvx⟩ := hex
  exact h v hvX hvyX ⟨x, Finset.filter_subset _ _ hx, hvx⟩ p hp

/-- Deleting a target `a` that fails condition 2 preserves realizability.  A vertex receiving a
constant whose path to `y` passes through `a` would witness condition 2 for `a`: along the path,
the last selected input before `a` enters a vertex with a path of `𝒢_F` to `a`. -/
theorem realizable_erase_of_not_cond2 {G : ADMG n} {y : Fin n} {S : Finset (Fin n)}
    {F : EdgeSet n} {a : Fin n} (h : Realizable G y S F) (ha : ¬ Cond2 G S F a) :
    Realizable G y (S.erase a) F := by
  intro v hv hvy hex p hp
  cases hpv : G.dir p v with
  | false => rfl
  | true =>
    have key : ∀ w, Reach G.dir (S.erase a) v w →
        (∃ q b, (q, b) ∈ F ∧ G.dir q b = true ∧ b ∉ S.erase a ∧
          (G.cutE F).AncAvoid (S.erase a) b w) ∧ Reach G.dir S v w := by
      intro w hw
      induction hw with
      | refl => exact ⟨⟨p, v, hp, hpv, hv, Reach.refl v⟩, Reach.refl v⟩
      | @tail b c _ hbc ih =>
        obtain ⟨⟨q, d, hqd, hqd', hd, hdb⟩, hvb⟩ := ih
        have hQ : ∃ q b, (q, b) ∈ F ∧ G.dir q b = true ∧ b ∉ S.erase a ∧
            (G.cutE F).AncAvoid (S.erase a) b c := by
          by_cases hbcF : (b, c) ∈ F
          · exact ⟨b, c, hbcF, hbc.1, hbc.2, Reach.refl c⟩
          · exact ⟨q, d, hqd, hqd', hd,
              Reach.tail hdb (ADMG.cutE_dir.mpr ⟨hbc.1, hbcF⟩) hbc.2⟩
        refine ⟨hQ, Reach.tail hvb hbc.1 ?_⟩
        intro hcS
        have hca : c = a := by
          by_contra hne
          exact hbc.2 (Finset.mem_erase.mpr ⟨hne, hcS⟩)
        obtain ⟨q', b', h1, h2, h3, h4⟩ := hQ
        rw [hca] at h4
        exact ha ⟨q', b', h1, h2, h3, h4⟩
    have hvS : v ∉ S := by
      intro hvS
      have hva : v = a := by
        by_contra hne
        exact hv (Finset.mem_erase.mpr ⟨hne, hvS⟩)
      rw [← hva] at ha
      exact ha ⟨p, v, hp, hpv, Finset.notMem_erase v S, Reach.refl v⟩
    obtain ⟨x, hx, hvx⟩ := hex
    have h' := h v hvS (key y hvy).2 ⟨x, Finset.mem_of_mem_erase hx, hvx⟩ p hp
    rw [hpv] at h'
    exact h'

theorem misifyPass_realizable {G : ADMG n} {y : Fin n} {F : EdgeSet n} (ord : List (Fin n)) :
    ∀ S : Finset (Fin n), Realizable G y S F → Realizable G y (misifyPass G F ord S) F := by
  induction ord with
  | nil => exact fun S h => h
  | cons a ord ih =>
    intro S h
    rw [misifyPass_cons]
    apply ih
    by_cases hc : a ∈ S ∧ ¬ Cond2 G S F a
    · rw [ite_eq_left hc]
      exact realizable_erase_of_not_cond2 h hc.2
    · rw [ite_eq_right hc]
      exact h

/-! ### `cor:ctf-misify` -/

/-- `ctf-MISify` returns a subset of its input. -/
theorem misify_subset (G : ADMG n) (y : Fin n) (X : Finset (Fin n)) (F : EdgeSet n)
    (ord : List (Fin n)) : misify G y X F ord ⊆ X :=
  (misifyPass_subset G F ord _).trans (Finset.filter_subset _ _)

/-- The output of `ctf-MISify` is a ctf-MIS when the order visits every target. -/
theorem misify_ctfMIS {G : ADMG n} (hG : G.WF) {y : Fin n} {X : Finset (Fin n)} {F : EdgeSet n}
    (hy : y ∉ X) {ord : List (Fin n)} (hord : ∀ x ∈ X, x ∈ ord) :
    CtfMIS G y (misify G y X F ord) F := by
  have hsub := misify_subset G y X F ord
  have hy' : y ∉ misify G y X F ord := fun h => hy (hsub h)
  rw [ctfMIS_iff hG hy']
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hx1 : x ∈ X.filter (fun x => G.AncAvoid X x y) := misifyPass_subset G F ord _ hx
    exact Reach.mono_avoid hsub (Finset.mem_filter.mp hx1).2
  · exact misifyPass_cond2 G F ord _ x hx (hord x (hsub hx))

/-- Both deletion steps of `ctf-MISify` preserve the reward on every unit,
for every order. -/
theorem misify_resp {G : ADMG n} {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L]
    [∀ i, Inhabited (Ω i)] {M : Mech n Ω L U} (hM : M.diag = G) (y : Fin n) (X : Finset (Fin n))
    (F : EdgeSet n) (ord : List (Fin n)) (c : Fin n → ∀ p, Ω p) (u : ∀ l, U l) :
    M.resp (misify G y X F ord) (M.respE F c u) u y = M.resp X (M.respE F c u) u y := by
  have hT : ∀ z ∈ X, M.diag.AncAvoid X z y → z ∈ X.filter (fun x => G.AncAvoid X x y) := by
    intro z hz hzy
    rw [hM] at hzy
    exact Finset.mem_filter.mpr ⟨hz, hzy⟩
  have h1 := Mech.resp_core (Finset.filter_subset _ X) hT (M.respE F c u) u
  exact (misifyPass_resp hM y F c u ord _).trans h1.symm

/-- `ctf-MISify` preserves realizability. -/
theorem misify_realizable {G : ADMG n} {y : Fin n} {X : Finset (Fin n)} {F : EdgeSet n}
    (ord : List (Fin n)) (h : Realizable G y X F) : Realizable G y (misify G y X F ord) F :=
  misifyPass_realizable ord _ (realizable_filter_ancAvoid h)

/-- **`cor:ctf-misify`**: `ctf-MISify` returns an equivalent and realizable
ctf-MIS subset of its input.  "Equivalent": the same reward on every unit, for every model
conforming to `𝒢` and every assignment of the selected inputs.  The input is realizable, the
standing assumption of. -/
theorem cor_ctf_misify {G : ADMG n} (hG : G.WF) {y : Fin n} {X : Finset (Fin n)} {F : EdgeSet n}
    (hy : y ∉ X) (hR : Realizable G y X F) {ord : List (Fin n)} (hord : ∀ x ∈ X, x ∈ ord) :
    misify G y X F ord ⊆ X ∧ CtfMIS G y (misify G y X F ord) F ∧
      Realizable G y (misify G y X F ord) F ∧
      ∀ m : Model n, ConfDiag G m → ∀ (c : Fin n → ∀ p, m.X p) (u : ∀ l, m.U l),
        m.scm.toMech.resp (misify G y X F ord) (m.scm.toMech.respE F c u) u y =
          m.scm.toMech.resp X (m.scm.toMech.respE F c u) u y :=
  ⟨misify_subset G y X F ord, misify_ctfMIS hG hy hord, misify_realizable ord hR,
    fun _ hm c u => misify_resp hm y X F ord c u⟩

/-! ## The required inputs -/

/-- For a target `x`, the directed paths into `x` are the same in `𝒢_F` and in the graph of the
required inputs, whatever vertices they avoid. -/
theorem ancAvoid_cutE_reqEdges {G : ADMG n} {X : Finset (Fin n)} {F : EdgeSet n} {x : Fin n}
    (hx : x ∈ X) (D : Finset (Fin n)) (v : Fin n) :
    (G.cutE (reqEdges G X F)).AncAvoid D v x ↔ (G.cutE F).AncAvoid D v x := by
  constructor
  · -- An edge of the path selected by `F` but not required would enter a vertex with no
    -- directed path of `𝒢_F` to a target; the rest of the path is such a path.
    intro h
    unfold ADMG.AncAvoid Reach at h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact Reach.refl x
    | @head a b hab _ ih =>
      obtain ⟨hab1, hbD⟩ := hab
      obtain ⟨hdir, hnotR⟩ := ADMG.cutE_dir.mp hab1
      have habF : (a, b) ∉ F := by
        intro habF
        exact hnotR (mem_reqEdges.mpr ⟨habF, hdir, x, hx, (G.cutE F).anc_of_avoid ih⟩)
      exact Reach.head (ADMG.cutE_dir.mpr ⟨hdir, habF⟩) hbD ih
  · -- The required inputs are selected inputs, so `𝒢_F` has fewer edges.
    intro h
    exact Reach.mono_rel (R := (G.cutE F).dir) (R' := (G.cutE (reqEdges G X F)).dir)
      (fun _ _ _ h' => ADMG.cutE_dir.mpr ⟨(ADMG.cutE_dir.mp h').1,
        fun hR => (ADMG.cutE_dir.mp h').2 (mem_reqEdges.mp hR).1⟩) h

/-- A vertex with a directed path of `𝒢_F` to a target receives exactly the same constants under
`F` and under the required inputs. -/
theorem mem_reqEdges_iff {G : ADMG n} {X : Finset (Fin n)} {F : EdgeSet n} {x v : Fin n}
    (hx : x ∈ X) (hv : (G.cutE F).Anc v x) (p : Fin n) :
    (p, v) ∈ reqEdges G X F ↔ (p, v) ∈ F ∧ G.dir p v = true := by
  rw [mem_reqEdges]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, x, hx, hv⟩⟩

/-- Condition 2 is the same whether `𝒢_{𝐗_{∗∗}}` deletes all selected inputs or only the required
ones. -/
theorem cond2_reqEdges {G : ADMG n} {X : Finset (Fin n)} {F : EdgeSet n} {x : Fin n}
    (hx : x ∈ X) : Cond2 G X (reqEdges G X F) x ↔ Cond2 G X F x := by
  constructor
  · rintro ⟨p, v, hpv, hd, hv, hpath⟩
    exact ⟨p, v, (mem_reqEdges.mp hpv).1, hd, hv, (ancAvoid_cutE_reqEdges hx _ _).mp hpath⟩
  · rintro ⟨p, v, hpv, hd, hv, hpath⟩
    exact ⟨p, v, (mem_reqEdges_iff hx ((G.cutE F).anc_of_avoid hpath) p).mpr ⟨hpv, hd⟩, hd, hv,
      (ancAvoid_cutE_reqEdges hx _ _).mpr hpath⟩

end Mec.CtfScb
