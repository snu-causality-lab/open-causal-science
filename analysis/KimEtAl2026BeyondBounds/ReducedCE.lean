import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # The reduced counterfactual effect in Beyond Bounds

Proposition 3 and Appendix B.2 of [Kim, Cho, and Lee (UAI 2026)]
(https://proceedings.mlr.press/v337/kim26b.html).
The fixed directed graph is represented by ranked parents. The component map
assigns each variable to a maximal C-component, whose exogenous states are drawn
independently. Each response reads the endogenous parents and its own block.

The reduction below uses the full observational distribution at the factual
assignment. It cancels the removed blocks using the product of the retained
factual factors, and handles zeros using nonnegativity. This establishes the
conclusion without requiring a separate Q-factor identification theorem.
-/

namespace KimEtAl2026BeyondBounds

open scoped BigOperators

universe u v w z

/-- A ranked structural model where each response reads the noise of one block. -/
structure RankedSCM (V : Type u) (C : Type v)
    (Value : V → Type w) (Noise : C → Type z) where
  block : V → C
  parent : V → V → Prop
  rank : V → Nat
  below : ∀ {p i}, parent p i → rank p < rank i
  response : ∀ i, ((p : {p // parent p i}) → Value p.val) → Noise (block i) → Value i


/-- The noise of a canonical block is one response table for each variable in
that block. Each table returns the variable's value for every parent assignment. -/
abbrev ResponseTables {V : Type u} {C : Type v} (Value : V → Type w)
    (block : V → C) (parent : V → V → Prop) (c : C) :=
  (i : {i // block i = c}) → ((p : {p // parent p i.val}) → Value p.val) → Value i.val

noncomputable instance responseTablesFintype {V : Type u} {C : Type v}
    (Value : V → Type w) [Fintype V] [∀ i, Fintype (Value i)]
    (block : V → C) (parent : V → V → Prop) (c : C) :
    Fintype (ResponseTables Value block parent c) := by
  classical
  unfold ResponseTables
  infer_instance

/-- Canonical structural equations by evaluation of the block's response tables. -/
def responseTableSCM {V : Type u} {C : Type v} (Value : V → Type w)
    (block : V → C) (parent : V → V → Prop) (rank : V → Nat)
    (below : ∀ {p i}, parent p i → rank p < rank i) :
    RankedSCM V C Value (ResponseTables Value block parent) where
  block := block
  parent := parent
  rank := rank
  below := below
  response := fun i parents tables => tables ⟨i, rfl⟩ parents

namespace RankedSCM

variable {V : Type u} {C : Type v} {Value : V → Type w} {Noise : C → Type z}
variable (G : RankedSCM V C Value Noise)

/-- The endogenous solution after applying the specified point interventions. -/
def evaluate (noise : ∀ c, Noise c) (override : ∀ i, Option (Value i))
    (i : V) : Value i :=
  match override i with
  | some a => a
  | none => G.response i (fun p => evaluate noise override p.val) (noise (G.block i))
termination_by G.rank i
decreasing_by exact G.below p.prop

private def Satisfies (noise : ∀ c, Noise c) (override : ∀ i, Option (Value i))
    (assignment : ∀ i, Value i) : Prop :=
  ∀ i, assignment i =
    match override i with
    | some a => a
    | none => G.response i (fun p => assignment p.val) (noise (G.block i))

private theorem evaluate_satisfies (noise : ∀ c, Noise c)
    (override : ∀ i, Option (Value i)) :
    G.Satisfies noise override (G.evaluate noise override) := by
  intro i
  conv_lhs => rw [evaluate]

private theorem eq_evaluate_of_satisfies (noise : ∀ c, Noise c)
    (override : ∀ i, Option (Value i)) (a : ∀ i, Value i)
    (h : G.Satisfies noise override a) :
    a = G.evaluate noise override := by
  funext i
  induction i using (measure G.rank).wf.induction with
  | h i ih =>
    rw [h i, evaluate]
    split
    · rfl
    · congr 1
      funext p
      exact ih p.val (G.below p.prop)

def factual (noise : ∀ c, Noise c) : ∀ i, Value i :=
  G.evaluate noise (fun _ => none)

def StrictDescendant (s i : V) : Prop := Relation.TransGen G.parent s i

/-- A block stays if it contains at least one strict descendant of the intervention. -/
def Retained (s : V) (c : C) : Prop :=
  ∃ i, G.block i = c ∧ G.StrictDescendant s i

variable [DecidableEq V]

private def force (s : V) (t : Value s) (i : V) : Option (Value i) :=
  if h : i = s then some (h.symm ▸ t) else none

def intervened (s : V) (t : Value s) (noise : ∀ c, Noise c) : ∀ i, Value i :=
  G.evaluate noise (force s t)

@[simp] theorem intervened_at (s : V) (t : Value s) (noise : ∀ c, Noise c) :
    G.intervened s t noise s = t := by
  rw [intervened, evaluate]
  simp [force]

omit [DecidableEq V] in
theorem factual_at (noise : ∀ c, Noise c) (i : V) :
    G.factual noise i = G.response i (fun p => G.factual noise p.val) (noise (G.block i)) :=
  (G.evaluate_satisfies noise (fun _ => none)) i

private theorem intervened_at_ne (s : V) (t : Value s) (noise : ∀ c, Noise c)
    (i : V) (hi : i ≠ s) :
    G.intervened s t noise i =
      G.response i (fun p => G.intervened s t noise p.val) (noise (G.block i)) := by
  have h := G.evaluate_satisfies noise (force s t) i
  simpa only [force, dite_eq_right hi, intervened] using h

omit [DecidableEq V] in
private theorem parent_not_affected {s i p : V} (h : G.parent p i)
    (hi : ¬ G.StrictDescendant s i) : p ≠ s ∧ ¬ G.StrictDescendant s p := by
  constructor
  · rintro rfl
    exact hi (.single h)
  · intro hp
    exact hi (.tail hp h)

/-- A nondescendant other than the intervened variable keeps its factual value. -/
theorem unchanged_of_not_descendant (s : V) (t : Value s) (noise : ∀ c, Noise c)
    (i : V) (hNE : i ≠ s) (hNo : ¬ G.StrictDescendant s i) :
    G.intervened s t noise i = G.factual noise i := by
  induction i using (measure G.rank).wf.induction with
  | h i ih =>
    rw [G.intervened_at_ne s t noise i hNE, G.factual_at noise i]
    congr 1
    funext p
    obtain ⟨hpn, hpd⟩ := G.parent_not_affected p.prop hNo
    exact ih p.val (G.below p.prop) hpn hpd

private def FactualLocal (a : ∀ i, Value i) (c : C) (u : Noise c) : Prop :=
  ∀ i (hc : G.block i = c),
    a i = G.response i (fun p => a p.val) (hc.symm ▸ u)

private def PairLocal (s : V) (a b : ∀ i, Value i) (c : C) (u : Noise c) : Prop :=
  G.FactualLocal a c u ∧
    ∀ i (hc : G.block i = c), i ≠ s →
      b i = G.response i (fun p => b p.val) (hc.symm ▸ u)

private def CompatiblePair (s : V) (t : Value s) (a b : ∀ i, Value i) : Prop :=
  b s = t ∧ ∀ i, i ≠ s → ¬ G.StrictDescendant s i → b i = a i

omit [DecidableEq V] in
private theorem factual_eq_iff_local (noise : ∀ c, Noise c) (a : ∀ i, Value i) :
    G.factual noise = a ↔ ∀ c, G.FactualLocal a c (noise c) := by
  constructor
  · rintro rfl c i hc
    subst c
    exact G.factual_at noise i
  · intro h
    symm
    apply G.eq_evaluate_of_satisfies
    intro i
    exact h (G.block i) i rfl

private theorem pair_eq_iff_local (s : V) (t : Value s)
    (noise : ∀ c, Noise c) (a b : ∀ i, Value i)
    (h : G.CompatiblePair s t a b) :
    (G.factual noise = a ∧ G.intervened s t noise = b) ↔
      ∀ c, G.PairLocal s a b c (noise c) := by
  constructor
  · rintro ⟨rfl, rfl⟩ c
    refine ⟨(G.factual_eq_iff_local noise _).mp rfl c, ?_⟩
    intro i hc hn
    subst c
    exact G.intervened_at_ne s t noise i hn
  · intro hLocal
    refine ⟨(G.factual_eq_iff_local noise a).mpr (fun c => (hLocal c).1), ?_⟩
    symm
    apply G.eq_evaluate_of_satisfies
    intro i
    by_cases hi : i = s
    · subst i
      simpa [force] using h.1
    · simpa only [force, dite_eq_right hi] using (hLocal (G.block i)).2 i rfl hi

private theorem compatiblePair_of_matches (s : V) (t : Value s)
    (noise : ∀ c, Noise c) (a b : ∀ i, Value i)
    (h : G.factual noise = a ∧ G.intervened s t noise = b) :
    G.CompatiblePair s t a b := by
  rcases h with ⟨rfl, rfl⟩
  exact ⟨G.intervened_at s t noise, G.unchanged_of_not_descendant s t noise⟩

omit [DecidableEq V] in
private theorem pairLocal_eq_of_removed (s : V) (t : Value s) (a b : ∀ i, Value i)
    (h : G.CompatiblePair s t a b) (c : C) (hc : ¬ G.Retained s c) (u : Noise c) :
    G.PairLocal s a b c u ↔ G.FactualLocal a c u := by
  refine ⟨And.left, fun hf => ⟨hf, ?_⟩⟩
  intro i he hn
  have hNo : ¬ G.StrictDescendant s i := fun hd => hc ⟨i, he, hd⟩
  have hParents : (fun p : {p // G.parent p i} => b p.val) =
      fun p : {p // G.parent p i} => a p.val := by
    funext p
    obtain ⟨hp, hd⟩ := G.parent_not_affected p.prop hNo
    exact h.2 p.val hp hd
  rw [h.2 i hn hNo, hParents]
  exact hf i he

noncomputable section

attribute [local instance] Classical.propDecidable

variable [Fintype C] [DecidableEq C] [∀ c, Fintype (Noise c)]

/-- Weights of independent finite exogenous blocks, with one simplex per block. -/
structure BlockWeights where
  weight : ∀ c, Noise c → ℝ
  nonnegative : ∀ c r, 0 ≤ weight c r
  normalized : ∀ c, ∑ r, weight c r = 1

variable (θ : BlockWeights (Noise := Noise))

def exogenousMass (noise : ∀ c, Noise c) : ℝ :=
  ∏ c, θ.weight c (noise c)

theorem exogenousMass_normalized : ∑ noise, exogenousMass θ noise = 1 := by
  simp only [exogenousMass]
  rw [← Fintype.prod_sum θ.weight]
  simp [θ.normalized]

def localMass {U : Type*} [Fintype U] (weight : U → ℝ) (ok : U → Prop) : ℝ :=
  ∑ u, if ok u then weight u else 0

private theorem localMass_nonnegative {U : Type*} [Fintype U]
    (weight : U → ℝ) (nonnegative : ∀ u, 0 ≤ weight u) (ok : U → Prop) :
    0 ≤ localMass weight ok := by
  apply Finset.sum_nonneg
  intro u _
  split <;> simp [nonnegative]

private theorem localMass_mono {U : Type*} [Fintype U]
    (weight : U → ℝ) (nonnegative : ∀ u, 0 ≤ weight u)
    (p q : U → Prop) (hs : ∀ u, p u → q u) :
    localMass weight p ≤ localMass weight q := by
  apply Finset.sum_le_sum
  intro u _
  by_cases hP : p u
  · simp [hP, hs u hP]
  · by_cases hQ : q u <;> simp [hP, hQ, nonnegative]

theorem sum_product_independent (accept : ∀ c, Noise c → Prop) :
    (∑ noise : ∀ c, Noise c,
      if ∀ c, accept c (noise c) then exogenousMass θ noise else 0) =
      ∏ c, localMass (θ.weight c) (accept c) := by
  simp only [localMass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro noise _
  by_cases h : ∀ c, accept c (noise c)
  · simp [h, exogenousMass]
  · rw [ite_eq_right h]
    obtain ⟨c, hc⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ c) (ite_eq_right hc)

/-- Factual assignment mass under the independent exogenous blocks. -/
def observationalMass (a : ∀ i, Value i) : ℝ :=
  ∑ noise : ∀ c, Noise c, if G.factual noise = a then exogenousMass θ noise else 0

/-- Factual/intervened assignment mass on the same exogenous context. -/
def jointPairMass (s : V) (t : Value s) (a b : ∀ i, Value i) : ℝ :=
  ∑ noise : ∀ c, Noise c,
    if G.factual noise = a ∧ G.intervened s t noise = b then exogenousMass θ noise else 0

omit [DecidableEq V] in
private theorem factual_factorization (a : ∀ i, Value i) :
    G.observationalMass θ a = ∏ c, localMass (θ.weight c) (G.FactualLocal a c) := by
  unfold observationalMass
  simp only [G.factual_eq_iff_local]
  exact sum_product_independent θ (G.FactualLocal a)

private theorem pair_factorization (s : V) (t : Value s) (a b : ∀ i, Value i)
    (h : G.CompatiblePair s t a b) :
    G.jointPairMass θ s t a b =
      ∏ c, localMass (θ.weight c) (G.PairLocal s a b c) := by
  unfold jointPairMass
  simp only [G.pair_eq_iff_local s t _ a b h]
  exact sum_product_independent θ (G.PairLocal s a b)

/-- A reduced parameter has one real coordinate per state of each retained block. -/
abbrev ReducedWeights (s : V) := ∀ c : Subtype (G.Retained s), Noise c.val → ℝ

def project (s : V) : G.ReducedWeights s :=
  fun c => θ.weight c.val

omit [DecidableEq C] in
private theorem product_split (r : C → Prop) (f : C → ℝ) :
    (∏ c, f c) = (∏ c : Subtype r, f c.val) * (∏ c : {c // ¬ r c}, f c.val) :=
  (Fintype.prod_subtype_mul_prod_subtype r f).symm

/-- Reconstruct one factual/intervened mass using the reduced weights and the
observed mass at the factual assignment. The real quotient is zero if the
product of retained factual masses vanishes. -/
def reducedPairMass (observed : (∀ i, Value i) → ℝ)
    (s : V) (t : Value s) (a b : ∀ i, Value i) (φ : G.ReducedWeights s) : ℝ :=
  if G.CompatiblePair s t a b then
    observed a *
      ((∏ c : Subtype (G.Retained s), localMass (φ c) (G.PairLocal s a b c.val)) /
       (∏ c : Subtype (G.Retained s), localMass (φ c) (G.FactualLocal a c.val)))
  else 0

/-- Block cancellation for one assignment pair, including zero-probability
factual assignments. -/
theorem jointPairMass_eq_reduced (observed : (∀ i, Value i) → ℝ)
    (hObserved : ∀ a, G.observationalMass θ a = observed a)
    (s : V) (t : Value s) (a b : ∀ i, Value i) :
    G.jointPairMass θ s t a b = G.reducedPairMass observed s t a b (G.project θ s) := by
  by_cases h : G.CompatiblePair s t a b
  · rw [reducedPairMass, ite_eq_left h, G.pair_factorization θ s t a b h,
      product_split (G.Retained s), ← hObserved a, G.factual_factorization θ a,
      product_split (G.Retained s)]
    have hRemoved :
        (∏ c : {c // ¬ G.Retained s c}, localMass (θ.weight c.val)
          (G.PairLocal s a b c.val)) =
        ∏ c : {c // ¬ G.Retained s c}, localMass (θ.weight c.val) (G.FactualLocal a c.val) := by
      apply Finset.prod_congr rfl
      intro c _
      unfold localMass
      apply Finset.sum_congr rfl
      intro u _
      rw [G.pairLocal_eq_of_removed s t a b h c.val c.prop u]
    rw [hRemoved]
    let A := ∏ c : Subtype (G.Retained s), localMass (θ.weight c.val)
      (G.PairLocal s a b c.val)
    let B := ∏ c : Subtype (G.Retained s), localMass (θ.weight c.val)
      (G.FactualLocal a c.val)
    let D := ∏ c : {c // ¬ G.Retained s c}, localMass (θ.weight c.val)
      (G.FactualLocal a c.val)
    change A * D = (B * D) * (A / B)
    by_cases hz : B = 0
    · have hA : 0 ≤ A := Finset.prod_nonneg fun c _ =>
        localMass_nonnegative _ (θ.nonnegative c.val) _
      have hAB : A ≤ B := Finset.prod_le_prod₀
        (fun c _ => localMass_nonnegative _ (θ.nonnegative c.val) _)
        (fun c _ => localMass_mono _ (θ.nonnegative c.val) _ _ fun _ hp => hp.1)
      rw [hz] at hAB ⊢
      rw [le_antisymm hAB hA]
      simp
    · field_simp [hz]
  · rw [reducedPairMass, ite_eq_right h]
    unfold jointPairMass
    apply Finset.sum_eq_zero
    intro noise _
    exact ite_eq_right (fun hm => h (G.compatiblePair_of_matches s t noise a b hm))

variable [Fintype V] [∀ i, Fintype (Value i)]

/-- The factual evidence records every coordinate except the predictor. -/
def Evidence (predictor : V) (context a : ∀ i, Value i) : Prop :=
  ∀ i, i ≠ predictor → a i = context i

def evidenceMass (observed : (∀ i, Value i) → ℝ)
    (predictor : V) (context : ∀ i, Value i) : ℝ :=
  ∑ a, if Evidence predictor context a then observed a else 0

def factualOutcomeMass (observed : (∀ i, Value i) → ℝ)
    (predictor : V) (context : ∀ i, Value i) (y : Value predictor) : ℝ :=
  ∑ a, if Evidence predictor context a ∧ a predictor = y then observed a else 0

/-- Sum the twin-assignment masses over the assignments realizing the query. -/
def counterfactualOutcomeMass (s : V) (t : Value s) (predictor : V)
    (context : ∀ i, Value i) (y : Value predictor) : ℝ :=
  ∑ a, ∑ b, if Evidence predictor context a ∧ b predictor = y then
    G.jointPairMass θ s t a b else 0


private theorem event_pushforward {A : Type*} {B : Type*} [Fintype A] [Fintype B]
    [eqB : DecidableEq B] (weight : A → ℝ) (outcome : A → B) (event : B → Prop)
    [DecidablePred event] :
    (∑ b, if event b then ∑ a, if outcome a = b then weight a else 0 else 0) =
      ∑ a, if event (outcome a) then weight a else 0 := by
  calc
    _ = ∑ b, ∑ a, if event b ∧ outcome a = b then weight a else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : event b <;> simp [hb]
    _ = ∑ a, ∑ b, if event b ∧ outcome a = b then weight a else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (outcome a)]
      · simp
      · intro b _ h
        simp [Ne.symm h]
      · simp

/-- Sum the factual assignment masses to obtain the same event probability as
summing over the exogenous contexts where the factual assignment lies in it. -/
theorem observationalMass_event (event : ((i : V) → Value i) → Prop) :
    (∑ a, if event a then G.observationalMass θ a else 0) =
      ∑ noise : ∀ c, Noise c,
        if event (G.factual noise) then exogenousMass θ noise else 0 := by
  exact event_pushforward (eqB := fun x y => Classical.propDecidable (x = y))
    (exogenousMass θ) G.factual event

/-- The twin-assignment sum evaluates the joint event on one shared noise draw
for factual evidence and the intervened prediction. -/
theorem counterfactualOutcomeMass_eq_noise_event (s : V) (t : Value s)
    (predictor : V) (context : ∀ i, Value i) (y : Value predictor) :
    G.counterfactualOutcomeMass θ s t predictor context y =
      ∑ noise : ∀ c, Noise c,
        if Evidence predictor context (G.factual noise) ∧ G.intervened s t noise predictor = y
        then exogenousMass θ noise else 0 := by
  let output (noise : ∀ c, Noise c) := (G.factual noise, G.intervened s t noise)
  let event (ab : ((i : V) → Value i) × ((i : V) → Value i)) :=
    Evidence predictor context ab.1 ∧ ab.2 predictor = y
  calc
    _ = ∑ ab, if event ab then ∑ noise, if output noise = ab
        then exogenousMass θ noise else 0 else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [counterfactualOutcomeMass, event, output, Prod.mk.injEq, jointPairMass]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : Evidence predictor context a ∧ b predictor = y
      · simp only [ite_eq_left h]
        apply Finset.sum_congr rfl
        intro noise _
        by_cases hh : G.factual noise = a ∧ G.intervened s t noise = b <;> simp [hh]
      · simp [h]
    _ = _ := event_pushforward (exogenousMass θ) output event

/-- Under observational compatibility, the denominator in Definition 4 is the
same finite factual evidence probability computed from the SCM. -/
theorem evidenceMass_eq_noise_event (observed : (∀ i, Value i) → ℝ)
    (hObserved : ∀ a, G.observationalMass θ a = observed a)
    (predictor : V) (context : ∀ i, Value i) :
    evidenceMass observed predictor context =
      ∑ noise : ∀ c, Noise c,
        if Evidence predictor context (G.factual noise) then exogenousMass θ noise else 0 := by
  simp only [evidenceMass, ← hObserved, observationalMass]
  exact event_pushforward (eqB := fun x y => Classical.propDecidable (x = y))
    (exogenousMass θ) G.factual (Evidence predictor context)

/-- Under observational compatibility, the factual outcome and evidence
probability agrees with the observational numerator in Definition 4. -/
theorem factualOutcomeMass_eq_noise_event (observed : (∀ i, Value i) → ℝ)
    (hObserved : ∀ a, G.observationalMass θ a = observed a)
    (predictor : V) (context : ∀ i, Value i) (y : Value predictor) :
    factualOutcomeMass observed predictor context y =
      ∑ noise : ∀ c, Noise c,
        if Evidence predictor context (G.factual noise) ∧ G.factual noise predictor = y
        then exogenousMass θ noise else 0 := by
  simp only [factualOutcomeMass, ← hObserved, observationalMass]
  exact event_pushforward (eqB := fun x y => Classical.propDecidable (x = y))
    (exogenousMass θ) G.factual
    (fun a => Evidence predictor context a ∧ a predictor = y)

/-- The conditional prediction contrast for a single intervention value. -/
def counterfactualEffect (observed : (∀ i, Value i) → ℝ)
    (s : V) (t : Value s) (predictor : V)
    (context : ∀ i, Value i) (y : Value predictor) : ℝ :=
  let p := evidenceMass observed predictor context
  G.counterfactualOutcomeMass θ s t predictor context y / p -
    factualOutcomeMass observed predictor context y / p

/-- The contrast as a function of exactly the retained C-parameter coordinates. -/
def reducedEffect (observed : (∀ i, Value i) → ℝ)
    (s : V) (t : Value s) (predictor : V)
    (context : ∀ i, Value i) (y : Value predictor) (φ : G.ReducedWeights s) : ℝ :=
  let p := evidenceMass observed predictor context
  (∑ a, ∑ b, if Evidence predictor context a ∧ b predictor = y then
    G.reducedPairMass observed s t a b φ else 0) / p -
    factualOutcomeMass observed predictor context y / p

private theorem localMass_measurable {U : Type*} [Fintype U] (ok : U → Prop) :
    Measurable (fun p : U → ℝ => localMass p ok) := by
  apply Finset.measurable_fun_sum
  intro u _
  by_cases h : ok u
  · simpa [h] using (measurable_pi_apply u : Measurable (fun p : U → ℝ => p u))
  · simp [h]

omit [DecidableEq V] [DecidableEq C] [Fintype V] [(i : V) → Fintype (Value i)] in
private theorem reducedPairMass_measurable (observed : (∀ i, Value i) → ℝ)
    (s : V) (t : Value s) (a b : ∀ i, Value i) :
    Measurable (G.reducedPairMass observed s t a b) := by
  unfold reducedPairMass
  by_cases h : G.CompatiblePair s t a b
  · simp only [ite_eq_left h]
    refine measurable_const.mul (Measurable.div ?_ ?_)
    · apply Finset.measurable_fun_prod
      intro c _
      exact (localMass_measurable _).comp (measurable_pi_apply c)
    · apply Finset.measurable_fun_prod
      intro c _
      exact (localMass_measurable _).comp (measurable_pi_apply c)
  · simp [h]

/-- Proposition 3 on ranked finite SCMs with independent C-component weights.
The map is constructed on all retained coordinates and therefore restricts to
the image of the observationally compatible models. Positive evidence ensures
that both terms of the contrast are conditional probabilities. -/
theorem exists_measurable_reduced_effect (observed : (∀ i, Value i) → ℝ)
    (s : V) (t : Value s) (predictor : V)
    (context : ∀ i, Value i) (y : Value predictor)
    (hSupport : 0 < evidenceMass observed predictor context) :
    ∃ g : G.ReducedWeights s → ℝ, Measurable g ∧
      ∀ θ' : BlockWeights (Noise := Noise),
        (∀ a, G.observationalMass θ' a = observed a) →
        evidenceMass observed predictor context ≠ 0 ∧
        G.counterfactualEffect θ' observed s t predictor context y = g (G.project θ' s) := by
  refine ⟨G.reducedEffect observed s t predictor context y, ?_, ?_⟩
  · unfold reducedEffect
    apply Measurable.sub _ measurable_const
    apply Measurable.div _ measurable_const
    apply Finset.measurable_fun_sum
    intro a _
    apply Finset.measurable_fun_sum
    intro b _
    by_cases h : Evidence predictor context a ∧ b predictor = y
    · simpa only [ite_eq_left h] using G.reducedPairMass_measurable observed s t a b
    · simp [h]
  · intro θ' hObs
    refine ⟨ne_of_gt hSupport, ?_⟩
    unfold counterfactualEffect reducedEffect counterfactualOutcomeMass
    simp only [G.jointPairMass_eq_reduced θ' observed hObs s t]

end
end RankedSCM

end KimEtAl2026BeyondBounds
