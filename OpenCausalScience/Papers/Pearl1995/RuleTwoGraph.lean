module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Papers.Pearl1995.RuleTwo

/-! # Action and observation exchange in a separated finite SCM

Pearl (1995), Theorem 4.1, Rule 2. In this specialization, all earlier
actions have been applied, the exchanged variable is binary, and the
conditioned variables are observed roots. Their joint value and the
two non-root noise blocks have independent finite laws.

When cutting the outgoing arrows of Z leaves a parent-closed partition
of the non-root vertices into a Z side and a Y side, evaluating the
modified model gives independent natural Z and set Y at fixed root
values. Probability is the product law on the primitive inputs.
Source: https://proceedings.mlr.press/r0/pearl95a.html
-/

namespace OpenCausalScience.Papers.Pearl1995.RuleTwoGraph

@[expose] public section

structure Law (A : Type) where
  atoms : List A
  weight : A → Rat
  nonnegative : ∀ a ∈ atoms, 0 ≤ weight a
  normalized : (atoms.map weight).sum = 1

def Law.mass {A : Type} (law : Law A) (event : A → Bool) : Rat :=
  (law.atoms.map fun a => if event a then law.weight a else 0).sum

private theorem sum_times {A : Type} (values : List A) (term : A → Rat) (c : Rat) :
    (values.map fun a => c * term a).sum = c * (values.map term).sum := by
  induction values with
  | nil => simp [Rat.mul_zero]
  | cons a rest ih => simp [ih, Rat.mul_add]

theorem Law.mass_all {A : Type} (law : Law A) :
    law.mass (fun _ => true) = 1 := by
  simpa [Law.mass] using law.normalized

private theorem product_sum {A B : Type} (as : List A) (bs : List B)
    (p : A → Rat) (q : B → Rat) :
    ((as.flatMap fun a => bs.map fun b => (a, b)).map
      fun ab => p ab.1 * q ab.2).sum = (as.map p).sum * (bs.map q).sum := by
  induction as with
  | nil => simp [Rat.zero_mul]
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      List.map_cons, List.sum_cons, ih, Rat.add_mul]
    change (bs.map (fun b => p a * q b)).sum + _ = _
    rw [sum_times]

def Law.product {A B : Type} (p : Law A) (q : Law B) : Law (A × B) where
  atoms := p.atoms.flatMap fun a => q.atoms.map fun b => (a, b)
  weight ab := p.weight ab.1 * q.weight ab.2
  nonnegative := by
    intro ab member
    obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp member
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact Rat.mul_nonneg (p.nonnegative a ha) (q.nonnegative b hb)
  normalized := by
    rw [product_sum, p.normalized, q.normalized, Rat.one_mul]

theorem Law.mass_product {A B : Type} (p : Law A) (q : Law B)
    (left : A → Bool) (right : B → Bool) :
    (p.product q).mass (fun ab => left ab.1 && right ab.2) = p.mass left * q.mass right := by
  unfold Law.mass
  change ((p.atoms.flatMap fun a => q.atoms.map fun b => (a, b)).map
      fun ab => if left ab.1 && right ab.2 then p.weight ab.1 * q.weight ab.2 else 0).sum = _
  rw [← product_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  cases left ab.1 <;> cases right ab.2 <;> simp [Rat.zero_mul, Rat.mul_zero]

inductive Block
  | observedRoot | left | right
  deriving DecidableEq

variable {n : Nat} {G : DAG n} {L R W : Type}

/-- The root block returns its observed values. A mechanism in either
non-root block receives that block's noise and its incoming parent values. -/
structure SCM (G : DAG n) (L R W : Type) where
  block : Fin n → Block
  rootValue : Fin n → W → Bool
  leftValue : Fin n → L → (Fin n → Bool) → Bool
  rightValue : Fin n → R → (Fin n → Bool) → Bool
  observedRoots : ∀ u v, block v = .observedRoot → G.edge u v = false
  rootValuesDetermine : ∀ w w', (∀ v, block v = .observedRoot →
    rootValue v w = rootValue v w') → w = w'

namespace SCM

def applyMechanism (model : SCM G L R W) (noise : W × (L × R))
    (v : Fin n) (parents : Fin n → Bool) : Bool :=
  match model.block v with
  | .observedRoot => model.rootValue v noise.1
  | .left => model.leftValue v noise.2.1 parents
  | .right => model.rightValue v noise.2.2 parents

/-- The natural equation for Z still runs. Every child instead receives
the assigned Z when a setting is supplied. The resulting natural Z is
used as a separate response in the action–observation comparison. -/
def evaluate (model : SCM G L R W) (z : Fin n) (setting : Option Bool)
    (noise : W × (L × R)) (v : Fin n) : Bool :=
  let parents (u : Fin n) := if _edge : G.edge u v = true then
    if u = z then
      match setting with
      | some value => value
      | none => model.evaluate z setting noise u
    else model.evaluate z setting noise u
  else false
  model.applyMechanism noise v parents
termination_by G.rank v
decreasing_by all_goals exact G.edge_increases _ _ _edge

theorem evaluate_set (model : SCM G L R W) (z : Fin n) (setting : Bool)
    (noise : W × (L × R)) (v : Fin n) :
    model.evaluate z (some setting) noise v =
      model.applyMechanism noise v (fun u => if G.edge u v then
        if u = z then setting else model.evaluate z (some setting) noise u else false) := by
  rw [evaluate]
  apply congrArg (model.applyMechanism noise v)
  funext u
  cases G.edge u v <;> simp

/-- When the outgoing edges of z are cut, a parent of a non-root
variable must be in its block or in the observed root set. -/
def respectsCut (model : SCM G L R W) (z : Fin n) : Prop :=
  ∀ u v, G.edge u v = true → u ≠ z → model.block v ≠ .observedRoot →
    model.block u = .observedRoot ∨ model.block u = model.block v

/-- Reachability from Z after deleting its outgoing arrows, removing
observed roots, and ignoring the directions of the remaining arrows. -/
inductive CutReach (model : SCM G L R W) (z : Fin n) : Fin n → Prop
  | start : model.block z ≠ .observedRoot → CutReach model z z
  | forward {u v} : CutReach model z u → model.block v ≠ .observedRoot →
      u ≠ z → G.edge u v = true → CutReach model z v
  | backward {u v} : CutReach model z v → model.block u ≠ .observedRoot →
      u ≠ z → G.edge u v = true → CutReach model z u

theorem respects_cut_of_reachable_partition (model : SCM G L R W) (z : Fin n)
    (aligned : ∀ v, model.block v = .left ↔ model.CutReach z v) : model.respectsCut z := by
  intro u v edge notZ vOutside
  by_cases uRoot : model.block u = .observedRoot
  · exact .inl uRoot
  · apply Or.inr
    cases source : model.block u with
    | observedRoot => exact (uRoot source).elim
    | left =>
      exact ((aligned v).mpr (.forward ((aligned u).mp source) vOutside notZ edge)).symm
    | right =>
      cases target : model.block v with
      | observedRoot => exact (vOutside target).elim
      | left =>
        have invalid := (aligned u).mpr (.backward ((aligned v).mp target) uRoot notZ edge)
        rw [source] at invalid
        contradiction
      | right => rfl

theorem natural_eq_set (model : SCM G L R W) (z : Fin n) (setting : Bool)
    (noise : W × (L × R)) (v : Fin n)
    (beforeOrRealized : G.rank v ≤ G.rank z ∨ model.evaluate z none noise z = setting) :
    model.evaluate z none noise v = model.evaluate z (some setting) noise v := by
  induction bound : G.rank v using Nat.strongRecOn generalizing v with
  | ind k ih =>
    have parents :
        (fun u : Fin n => if _edge : G.edge u v = true then
          if u = z then (match (none : Option Bool) with
            | some value => value
            | none => model.evaluate z none noise u)
          else model.evaluate z none noise u
        else false) =
        (fun u : Fin n => if _edge : G.edge u v = true then
          if u = z then (match some setting with
            | some value => value
            | none => model.evaluate z (some setting) noise u)
          else model.evaluate z (some setting) noise u
        else false) := by
      funext u
      by_cases edge : G.edge u v = true
      · have rank := G.edge_increases _ _ edge
        by_cases atZ : u = z
        · subst u
          obtain before | consistent := beforeOrRealized
          · omega
          · simp [edge, consistent]
        · have condition : G.rank u ≤ G.rank z ∨ model.evaluate z none noise z = setting :=
            beforeOrRealized.imp (fun _ => by omega) id
          simpa [edge, atZ] using ih (G.rank u) (by omega) u condition rfl
      · simp [edge]
    rw [evaluate, evaluate]
    rw [parents]

def sameInputs (block : Block) (first second : W × (L × R)) : Prop :=
  first.1 = second.1 ∧ match block with
    | .observedRoot => True
    | .left => first.2.1 = second.2.1
    | .right => first.2.2 = second.2.2

/-- Given its observed root inputs, each side depends only on its own
noise. The partition condition concerns the cut graph. -/
theorem set_depends_on_own_block (model : SCM G L R W) (z : Fin n) (setting : Bool)
    (cut : model.respectsCut z) (block : Block) (first second : W × (L × R))
    (same : sameInputs block first second) (v : Fin n)
    (belongs : model.block v = .observedRoot ∨ model.block v = block) :
    model.evaluate z (some setting) first v = model.evaluate z (some setting) second v := by
  induction bound : G.rank v using Nat.strongRecOn generalizing v with
  | ind rank ih =>
    by_cases root : model.block v = .observedRoot
    · simp [evaluate_set, applyMechanism, root, same.1]
    · have own := belongs.resolve_left root
      have parents : (fun u : Fin n => if G.edge u v then
          if u = z then setting else model.evaluate z (some setting) first u else false) =
          (fun u : Fin n => if G.edge u v then
          if u = z then setting else model.evaluate z (some setting) second u else false) := by
        funext u
        cases edge : G.edge u v
        · simp
        · by_cases atZ : u = z
          · simp [atZ]
          · have parent := cut u v edge atZ root
            have parentBelongs : model.block u = .observedRoot ∨ model.block u = block :=
              parent.imp id (·.trans own)
            have smaller := G.edge_increases _ _ edge
            simpa [atZ] using ih (G.rank u) (by omega) u parentBelongs rfl
      rw [evaluate_set, evaluate_set, parents]
      cases block with
      | observedRoot => exact (root own).elim
      | left => simp [applyMechanism, own, same.2]
      | right => simp [applyMechanism, own, same.2]

def exchangeModel (model : SCM G L R W) (rootLaw : Law W) (leftLaw : Law L)
    (rightLaw : Law R) (z y : Fin n) : RuleTwo.Model (W × (L × R)) Bool Bool W :=
  let law := rootLaw.product (leftLaw.product rightLaw)
  { atoms := law.atoms
    weight := law.weight
    nonnegative := law.nonnegative
    normalized := law.normalized
    observe := fun noise => model.evaluate z none noise z
    respond := fun setting noise => (model.evaluate z (some setting) noise y, noise.1) }

theorem observed_response_is_natural (model : SCM G L R W) (rootLaw : Law W)
    (leftLaw : Law L) (rightLaw : Law R) (z y : Fin n) (noise : W × (L × R)) :
    let exchange := model.exchangeModel rootLaw leftLaw rightLaw z y
    exchange.respond (exchange.observe noise) noise = (model.evaluate z none noise y, noise.1) := by
  unfold exchangeModel
  exact congrArg (fun b => (b, noise.1))
    (model.natural_eq_set z _ noise y (.inr rfl)).symm

variable [Inhabited L] [Inhabited R] [DecidableEq W]

theorem mass_splits_at_roots (model : SCM G L R W) (rootLaw : Law W) (leftLaw : Law L)
    (rightLaw : Law R) (z y : Fin n) (zSide : model.block z = .left)
    (ySide : model.block y = .right) (cut : model.respectsCut z)
    (setting : Bool) (w : W) (zEvent yEvent : Bool → Bool) :
    (model.exchangeModel rootLaw leftLaw rightLaw z y).mass
      (fun noise => decide (noise.1 = w) &&
        (zEvent (model.evaluate z none noise z) &&
          yEvent (model.evaluate z (some setting) noise y))) =
      rootLaw.mass (fun root => decide (root = w)) *
      (leftLaw.mass (fun l => zEvent (model.evaluate z (some setting) (w, (l, default)) z)) *
        rightLaw.mass (fun r => yEvent (model.evaluate z (some setting) (w, (default, r)) y))) := by
  let zOnLeft (l : L) := zEvent (model.evaluate z (some setting) (w, (l, default)) z)
  let yOnRight (r : R) := yEvent (model.evaluate z (some setting) (w, (default, r)) y)
  let law := rootLaw.product (leftLaw.product rightLaw)
  change law.mass _ = rootLaw.mass _ * (leftLaw.mass zOnLeft * rightLaw.mass yOnRight)
  rw [← Law.mass_product leftLaw rightLaw, ← Law.mass_product rootLaw]
  apply congrArg law.mass
  funext noise
  obtain ⟨root, l, r⟩ := noise
  by_cases same : root = w
  · subst root
    have zNatural := model.natural_eq_set z setting (w, (l, r)) z (.inl (Nat.le_refl _))
    have lSame : sameInputs .left (w, (l, r)) (w, (l, default)) := ⟨rfl, rfl⟩
    have rSame : sameInputs .right (w, (l, r)) (w, (default, r)) := ⟨rfl, rfl⟩
    have zLocal := model.set_depends_on_own_block z setting cut .left _ _ lSame z (.inr zSide)
    have yLocal := model.set_depends_on_own_block z setting cut .right _ _ rSame y (.inr ySide)
    simp [zNatural, zLocal, yLocal, zOnLeft, yOnRight]
  · simp [same]

/-- Rule 2's conditional independence is a consequence of the split
in the cut graph and the independent input law. -/
theorem conditional_independence_of_cut (model : SCM G L R W) (rootLaw : Law W)
    (leftLaw : Law L) (rightLaw : Law R) (z y : Fin n) (zSide : model.block z = .left)
    (ySide : model.block y = .right) (cut : model.respectsCut z)
    (setting outcome : Bool) (w : W) :
    (model.exchangeModel rootLaw leftLaw rightLaw z y).independentAt setting outcome w := by
  let exchange := model.exchangeModel rootLaw leftLaw rightLaw z y
  let wEvent (root : W) := decide (root = w)
  let zEvent (value : Bool) := decide (value = setting)
  let yEvent (value : Bool) := decide (value = outcome)
  let mass (p q : Bool → Bool) := exchange.mass fun noise =>
    wEvent noise.1 && (p (model.evaluate z none noise z) &&
      q (model.evaluate z (some setting) noise y))
  have event_true (zTest yTest : Bool → Bool) :
      mass zTest yTest =
        rootLaw.mass wEvent *
          (leftLaw.mass (fun l => zTest (model.evaluate z (some setting) (w, (l, default)) z)) *
            rightLaw.mass (fun r => yTest (model.evaluate z (some setting) (w, (default, r)) y))) :=
    model.mass_splits_at_roots rootLaw leftLaw rightLaw z y zSide ySide cut setting w zTest yTest
  have setZYW : exchange.setNaturalJointMass setting outcome w = mass zEvent yEvent := by
    apply congrArg exchange.mass
    funext noise
    simp [exchange, exchangeModel, zEvent, yEvent, wEvent, Bool.and_comm, Bool.and_left_comm,
      Prod.mk.injEq]
  have setW : exchange.setCovariateMass setting w = mass (fun _ => true) (fun _ => true) := by
    apply congrArg exchange.mass
    funext noise
    simp [exchange, exchangeModel, wEvent]
  have setYW : exchange.setJointMass setting outcome w = mass (fun _ => true) yEvent := by
    apply congrArg exchange.mass
    funext noise
    simp [exchange, exchangeModel, yEvent, wEvent, Bool.and_comm, Prod.mk.injEq]
  have setZW : exchange.setNaturalCovariateMass setting w = mass zEvent (fun _ => true) := by
    apply congrArg exchange.mass
    funext noise
    simp [exchange, exchangeModel, zEvent, wEvent, Bool.and_comm]
  change exchange.setNaturalJointMass setting outcome w * exchange.setCovariateMass setting w =
    exchange.setJointMass setting outcome w * exchange.setNaturalCovariateMass setting w
  rw [setZYW, setW, setYW, setZW, event_true zEvent yEvent,
    event_true (fun _ => true) (fun _ => true), event_true (fun _ => true) yEvent,
    event_true zEvent (fun _ => true)]
  simp only [Law.mass_all, Rat.one_mul, Rat.mul_one]
  generalize rootLaw.mass wEvent = p
  generalize leftLaw.mass (fun l => zEvent (model.evaluate z (some setting) (w, (l, default)) z)) = q
  generalize rightLaw.mass (fun r => yEvent (model.evaluate z (some setting) (w, (default, r)) y)) = r
  rw [Rat.mul_comm q r, ← Rat.mul_assoc p r q, Rat.mul_assoc (p * r) q p, Rat.mul_comm q p]

theorem supported_rule_two_of_cut (model : SCM G L R W) (rootLaw : Law W)
    (leftLaw : Law L) (rightLaw : Law R) (z y : Fin n) (zSide : model.block z = .left)
    (ySide : model.block y = .right) (cut : model.respectsCut z)
    (setting outcome : Bool) (w : W)
    (observed : 0 < (model.exchangeModel rootLaw leftLaw rightLaw z y).observationalCovariateMass
      setting w)
    (set : 0 < (model.exchangeModel rootLaw leftLaw rightLaw z y).setCovariateMass setting w) :
    let exchange := model.exchangeModel rootLaw leftLaw rightLaw z y
    exchange.setJointMass setting outcome w / exchange.setCovariateMass setting w =
      exchange.observationalJointMass setting outcome w / exchange.observationalCovariateMass setting w :=
  (model.exchangeModel rootLaw leftLaw rightLaw z y).supported_action_observation_exchange
    setting outcome w observed set
    (model.conditional_independence_of_cut rootLaw leftLaw rightLaw z y zSide ySide cut setting outcome w)

theorem supported_rule_two_of_separated_skeleton (model : SCM G L R W) (rootLaw : Law W)
    (leftLaw : Law L) (rightLaw : Law R) (z y : Fin n)
    (zOutside : model.block z ≠ .observedRoot) (yOutside : model.block y ≠ .observedRoot)
    (aligned : ∀ v, model.block v = .left ↔ model.CutReach z v)
    (separated : ¬ model.CutReach z y) (setting outcome : Bool) (w : W)
    (observed : 0 < (model.exchangeModel rootLaw leftLaw rightLaw z y).observationalCovariateMass
      setting w)
    (set : 0 < (model.exchangeModel rootLaw leftLaw rightLaw z y).setCovariateMass setting w) :
    let exchange := model.exchangeModel rootLaw leftLaw rightLaw z y
    exchange.setJointMass setting outcome w / exchange.setCovariateMass setting w =
      exchange.observationalJointMass setting outcome w / exchange.observationalCovariateMass setting w := by
  have zSide : model.block z = .left := (aligned z).mpr (.start zOutside)
  have ySide : model.block y = .right := by
    cases value : model.block y with
    | observedRoot => exact (yOutside value).elim
    | left => exact (separated ((aligned y).mp value)).elim
    | right => rfl
  exact model.supported_rule_two_of_cut rootLaw leftLaw rightLaw z y zSide ySide
    (model.respects_cut_of_reachable_partition z aligned) setting outcome w observed set

end SCM

end

end OpenCausalScience.Papers.Pearl1995.RuleTwoGraph
