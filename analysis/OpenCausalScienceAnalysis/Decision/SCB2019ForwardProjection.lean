import OpenCausalScienceAnalysis.Decision.SCB2019ForwardMechanism

/-!
# Forward projection of an arbitrary finite structural causal model

Lee and Bareinboim (2019), corrected Proposition 2. The projected model keeps the
original root laws and gives any added roots a one-point law. It preserves the mean
of every retained intervention arm and hence its intervention-set optimum.

https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Finset Mec Mec.ScbMec

variable {n : ℕ}

@[instance_reducible] private def forwardFintype (m : Model n) :
    ∀ l : ForwardRoots m, Fintype (ForwardNoise m l)
  | .inl l => inferInstanceAs (Fintype (m.U l))
  | .inr _ => inferInstanceAs (Fintype Unit)

private noncomputable def forwardP (m : Model n) : ∀ l, ForwardNoise m l → ℝ
  | .inl l, u => m.scm.p l u
  | .inr _, _ => 1

/-- Substitute the eliminated equation into its children while retaining the old
state domains and the independent exogenous laws. -/
noncomputable def forwardModel (m : Model n) (w : Fin n) : Model n := by
  let : ∀ l, Fintype (ForwardNoise m l) := forwardFintype m
  exact {
    X := m.X
    L := ForwardRoots m
    U := ForwardNoise m
    fX := m.fX
    dX := m.dX
    iX := m.iX
    scm := {
      toMech := forwardMech m w
      p := forwardP m
      p_nonneg := fun l u => by
        cases l
        · exact m.scm.p_nonneg _ u
        · exact zero_le_one
      p_sum := fun l => by
        cases l
        · exact m.scm.p_sum _
        · change (∑ _ : Unit, (1 : ℝ)) = 1
          simp
    }
  }

private def forwardWorldEquiv (m : Model n) :
    (∀ l, ForwardNoise m l) ≃ (∀ l, m.U l) where
  toFun := forwardNoise m
  invFun := fun u l => match l with
    | .inl k => u k
    | .inr _ => ()
  right_inv _ := rfl
  left_inv u := by
    funext l
    cases l
    · rfl
    · exact Subsingleton.elim (α := Unit) _ _

private theorem forward_prob (m : Model n) (w : Fin n) (u : ∀ l, ForwardNoise m l) :
    (forwardModel m w).scm.prob u = m.scm.prob (forwardNoise m u) := by
  unfold SCM.prob
  change (∏ l : ForwardRoots m, forwardP m l (u l)) = ∏ l : m.L, m.scm.p l (u (.inl l))
  rw [Fintype.prod_sum_type]
  simp [forwardP]

theorem forwardModel_diag (m : Model n) (w : Fin n) :
    (forwardModel m w).scm.toMech.diag = eliminate m.scm.toMech.diag w :=
  forwardMech_diag m w

private theorem forward_expectation_eq (m : Model n) (w : Fin n) {S : Finset (Fin n)}
    (hw : w ∉ S) (score : (∀ i, m.X i) → ℝ) (depends : DepOn (fun i => i ≠ w) score)
    (x : ∀ i, m.X i) :
    (forwardModel m w).scm.E (fun u => score ((forwardMech m w).resp S x u)) =
      m.scm.E (fun u => score (m.scm.toMech.resp S x u)) := by
  let : ∀ l, Fintype (ForwardNoise m l) := forwardFintype m
  unfold SCM.E
  change (∑ u : ∀ l, ForwardNoise m l, (forwardModel m w).scm.prob u *
      score ((forwardMech m w).resp S x u)) =
    ∑ u : ∀ l, m.U l, m.scm.prob u * score (m.scm.toMech.resp S x u)
  apply Fintype.sum_equiv (forwardWorldEquiv m)
  intro u
  exact congrArg₂ (· * ·) (forward_prob m w u)
    (depends _ _ (fun _ hi => forwardMech_resp m w hw x u hi))

theorem forwardModel_mean_eq (m : Model n) (w : Fin n) {S : Finset (Fin n)}
    (hw : w ∉ S) {y : Fin n} (hy : y ≠ w) (r : m.X y → ℝ) (x : ∀ i, m.X i) :
    (forwardModel m w).mu y r S x = m.mu y r S x :=
  forward_expectation_eq m w hw (fun z => r (z y)) (fun _ _ agree => congrArg r (agree y hy)) x

theorem forwardModel_best_eq (m : Model n) (w : Fin n) {S : Finset (Fin n)}
    (hw : w ∉ S) {y : Fin n} (hy : y ≠ w) (r : m.X y → ℝ) :
    (forwardModel m w).best y r S = m.best y r S := by
  have equalMeans : (fun x : ∀ i, m.X i => (forwardModel m w).mu y r S x) =
      fun x => m.mu y r S x :=
    funext (forwardModel_mean_eq m w hw hy r)
  unfold Model.best
  exact congrArg (Finset.univ.sup' Finset.univ_nonempty) equalMeans

/-- Apply the forward substitution to the listed vertices in order. -/
noncomputable def projectModel (m : Model n) (removed : List (Fin n)) : Model n :=
  removed.foldl forwardModel m

theorem projectModel_domains (m : Model n) (removed : List (Fin n)) :
    (projectModel m removed).X = m.X := by
  induction removed generalizing m with
  | nil => rfl
  | cons w rest ih => exact ih (forwardModel m w)

theorem projectModel_diag (m : Model n) (removed : List (Fin n)) :
    (projectModel m removed).scm.toMech.diag = project m.scm.toMech.diag removed := by
  induction removed generalizing m with
  | nil => rfl
  | cons w rest ih =>
    change (projectModel (forwardModel m w) rest).scm.toMech.diag =
      project (eliminate m.scm.toMech.diag w) rest
    rw [ih, forwardModel_diag]

/-- Expectations of scores on the retained coordinates are invariant under projection.
In particular, a retained event's indicator gives the same interventional probability. -/
theorem projectModel_expectation_eq (m : Model n) (removed : List (Fin n))
    {S : Finset (Fin n)} (hs : ∀ w ∈ removed, w ∉ S) (score : (∀ i, m.X i) → ℝ)
    (depends : DepOn (fun i => i ∉ removed) score) (x : ∀ i, m.X i) :
    (projectModel m removed).scm.E (fun u => score (fun i =>
      cast (congrFun (projectModel_domains m removed) i)
        ((projectModel m removed).scm.toMech.resp S
          (fun j => cast (congrFun (projectModel_domains m removed) j).symm (x j)) u i))) =
      m.scm.E (fun u => score (m.scm.toMech.resp S x u)) := by
  induction removed generalizing m with
  | nil => rfl
  | cons w rest ih =>
    have hSrest : ∀ v ∈ rest, v ∉ S := fun v hv => hs v (List.mem_cons_of_mem w hv)
    have dependRest : DepOn (fun i => i ∉ rest) score :=
      fun _ _ agree => depends _ _ (fun i hi => agree i (fun hr => hi (List.mem_cons_of_mem w hr)))
    have dependStep : DepOn (fun i => i ≠ w) score :=
      fun _ _ agree => depends _ _ (fun i hi => agree i (fun he => hi (List.mem_cons.mpr (.inl he))))
    exact (ih (forwardModel m w) hSrest score dependRest x).trans
      (forward_expectation_eq m w (hs w List.mem_cons_self) score dependStep x)

/-- A single projected model agrees on every retained intervention arm and every
reward function of a retained outcome. -/
theorem projectModel_mean_eq (m : Model n) (removed : List (Fin n)) {S : Finset (Fin n)}
    (hs : ∀ w ∈ removed, w ∉ S) {y : Fin n} (hy : y ∉ removed)
    (r : m.X y → ℝ) (x : ∀ i, m.X i) :
    (projectModel m removed).mu y (fun v => r (cast (congrFun (projectModel_domains m removed) y) v))
      S (fun i => cast (congrFun (projectModel_domains m removed) i).symm (x i)) = m.mu y r S x :=
  projectModel_expectation_eq m removed hs (fun z => r (z y))
    (fun _ _ agree => congrArg r (agree y hy)) x

theorem projectModel_best_eq (m : Model n) (removed : List (Fin n)) {S : Finset (Fin n)}
    (hs : ∀ w ∈ removed, w ∉ S) {y : Fin n} (hy : y ∉ removed) (r : m.X y → ℝ) :
    (projectModel m removed).best y (fun v => r (cast (congrFun (projectModel_domains m removed) y) v))
      S = m.best y r S := by
  induction removed generalizing m with
  | nil => rfl
  | cons w rest ih =>
    have hw : y ≠ w := fun eq => hy (List.mem_cons.mpr (Or.inl eq))
    have hrest : y ∉ rest := fun h => hy (List.mem_cons_of_mem w h)
    have hSrest : ∀ v ∈ rest, v ∉ S := fun v hv => hs v (List.mem_cons_of_mem w hv)
    exact (ih (forwardModel m w) hSrest hrest r).trans
      (forwardModel_best_eq m w (hs w List.mem_cons_self) hw r)

/-- Corrected Proposition 2 at the level of the optimized reward of every retained
intervention set. The original SCM can have roots shared by arbitrarily many vertices. -/
theorem project_model_preserves_best {G : ADMG n} (removed : List (Fin n))
    (m : Model n) (hm : ConfDiag G m) {y : Fin n} (hy : y ∉ removed) (r : m.X y → ℝ) :
    ∃ (projected : Model n) (reward : projected.X y → ℝ), ConfDiag (project G removed) projected ∧
      ∀ S, (∀ w ∈ removed, w ∉ S) → projected.best y reward S = m.best y r S := by
  refine ⟨projectModel m removed, fun v => r (cast (congrFun (projectModel_domains m removed) y) v),
    ?_, fun _ hs => projectModel_best_eq m removed hs hy r⟩
  exact (projectModel_diag m removed).trans (congrArg (fun diagram => project diagram removed) hm)

end OpenCausalScienceAnalysis.Scb2019
