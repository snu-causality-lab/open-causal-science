module
public import OpenCausalScience.Graph.DAG

/-! # The finite edge g-formula

Shpitser and Tchetgen Tchetgen (2016), Lemma 5.6, Equation (5).
Each endogenous vertex has a mechanism and an independently sampled
finite exogenous coordinate. An edge intervention replaces the input
on one arrow, including when another child uses its parent's natural
value. At every full response assignment, the joint mass is a product
of local masses at the edge-adjusted parent assignments.
Source: https://arxiv.org/pdf/1411.2127#page=25
-/

namespace OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeGFormula

@[expose] public section

variable {n : Nat} {Ω : Type}

abbrev Assignment (n : Nat) := Fin n → Bool
abbrev EdgeSetting (n : Nat) := Fin n → Fin n → Option Bool

/-- The recursion reads only graph parents, with false at nonparent inputs. -/
def parents (G : DAG n) (edges : EdgeSetting n) (response : Assignment n)
    (v : Fin n) : Assignment n :=
  fun u => if G.edge u v then (edges u v).getD (response u) else false

/-- Responses on one unit under a setting indexed by edges. -/
def evaluate (G : DAG n) (mechanism : Fin n → Ω → Assignment n → Bool)
    (unit : Fin n → Ω) (edges : EdgeSetting n) (v : Fin n) : Bool :=
  mechanism v (unit v) (fun u =>
    if _parent : G.edge u v = true then
      match edges u v with
      | some assigned => assigned
      | none => evaluate G mechanism unit edges u
    else false)
termination_by G.rank v
decreasing_by exact G.edge_increases _ _ _parent

theorem evaluate_eq_mechanism (G : DAG n) (mechanism : Fin n → Ω → Assignment n → Bool)
    (unit : Fin n → Ω) (edges : EdgeSetting n) (v : Fin n) :
    evaluate G mechanism unit edges v =
      mechanism v (unit v) (parents G edges (evaluate G mechanism unit edges) v) := by
  rw [evaluate]
  apply congrArg (mechanism v (unit v))
  funext u
  by_cases h : G.edge u v = true
  · cases set : edges u v <;> simp [parents, h, set]
  · simp [parents, h]

/-- The local response events at a full candidate row determine the
actual response row, by induction along the graph. -/
theorem evaluate_eq_iff_local (G : DAG n) (mechanism : Fin n → Ω → Assignment n → Bool)
    (unit : Fin n → Ω) (edges : EdgeSetting n) (row : Assignment n) :
    (∀ v, evaluate G mechanism unit edges v = row v) ↔
      ∀ v, mechanism v (unit v) (parents G edges row v) = row v := by
  constructor
  · intro actual v
    have same : evaluate G mechanism unit edges = row := funext actual
    rw [← same]
    exact (evaluate_eq_mechanism G mechanism unit edges v).symm
  · intro localEq v
    induction h : G.rank v using Nat.strongRecOn generalizing v with
    | ind rank ih =>
      rw [evaluate_eq_mechanism, ← localEq v]
      apply congrArg (mechanism v (unit v))
      funext u
      by_cases hasEdge : G.edge u v = true
      · have smaller := G.edge_increases u v hasEdge
        simp [parents, hasEdge, ih (G.rank u) (h ▸ smaller) u rfl]
      · simp [parents, hasEdge]

/-- A product noise law, with one finite marginal for each vertex. -/
structure Model (n : Nat) (Ω : Type) where
  graph : DAG n
  mechanism : Fin n → Ω → Assignment n → Bool
  atoms : Fin n → List Ω
  weight : Fin n → Ω → Rat
  nonnegative : ∀ v a, a ∈ atoms v → 0 ≤ weight v a
  normalized : ∀ v, ((atoms v).map (weight v)).sum = 1

def setNoise (unit : Fin n → Ω) (v : Fin n) (a : Ω) : Fin n → Ω :=
  fun u => if u = v then a else unit u

/-- Sum over independently drawn vertex noises in the given order. -/
def integrate (m : Model n Ω) : List (Fin n) → (Fin n → Ω) → ((Fin n → Ω) → Rat) → Rat
  | [], unit, f => f unit
  | v :: rest, unit, f =>
      ((m.atoms v).map fun a => m.weight v a * integrate m rest (setNoise unit v a) f).sum

def indicator (holds : Bool) : Rat := if holds then 1 else 0

private theorem integrate_congr (m : Model n Ω) (order : List (Fin n)) (unit : Fin n → Ω)
    {f g : (Fin n → Ω) → Rat} (eq : ∀ u, f u = g u) :
    integrate m order unit f = integrate m order unit g := by
  induction order generalizing unit with
  | nil => exact eq unit
  | cons v rest ih =>
    simp only [integrate]
    apply congrArg List.sum
    exact List.map_congr_left fun a _ => congrArg (m.weight v a * ·) (ih (setNoise unit v a))

private theorem sum_mul_right {A : Type} (xs : List A) (f : A → Rat) (c : Rat) :
    (xs.map fun a => f a * c).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp [Rat.zero_mul]
  | cons a tail ih => simp [ih, Rat.add_mul]

private theorem integrate_mul_coordinate (m : Model n Ω) (order : List (Fin n))
    (unit : Fin n → Ω) (v : Fin n) (absent : v ∉ order) (h : Ω → Rat)
    (f : (Fin n → Ω) → Rat) :
    integrate m order unit (fun u => f u * h (u v)) = integrate m order unit f * h (unit v) := by
  induction order generalizing unit with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.mem_cons, not_or] at absent
    simp only [integrate, ← sum_mul_right]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    rw [ih (setNoise unit w a) absent.2, ← Rat.mul_assoc]
    simp [setNoise, absent.1]

private theorem integrate_product (m : Model n Ω) (order : List (Fin n))
    (unit : Fin n → Ω) (noRepeat : order.Nodup) (f : Fin n → Ω → Rat) :
    integrate m order unit (fun u => (order.map fun v => f v (u v)).prod) =
      (order.map fun v => ((m.atoms v).map fun a => m.weight v a * f v a).sum).prod := by
  induction order generalizing unit with
  | nil => rfl
  | cons v rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp noRepeat
    simp only [List.map_cons, List.prod_cons, integrate]
    rw [← sum_mul_right]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    have eq (u : Fin n → Ω) :
        f v (u v) * (rest.map fun w => f w (u w)).prod =
          (rest.map fun w => f w (u w)).prod * f v (u v) := Rat.mul_comm _ _
    rw [integrate_congr m rest _ eq, integrate_mul_coordinate m rest _ v absent,
      ih (setNoise unit v a) tailUnique]
    simp only [setNoise, ↓reduceIte]
    have commute (c : Rat) : m.weight v a * (c * f v a) = (m.weight v a * f v a) * c := by
      rw [Rat.mul_comm c (f v a), Rat.mul_assoc]
    exact commute _

private theorem prod_indicator {A : Type} (xs : List A) (test : A → Bool) :
    (xs.map fun a => indicator (test a)).prod = indicator (xs.all test) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.prod_cons, List.all_cons, ih]
    cases test a <;> simp [indicator, Rat.zero_mul, Rat.one_mul]

def localMass (m : Model n Ω) (v : Fin n) (input : Assignment n) (value : Bool) : Rat :=
  ((m.atoms v).map fun a => m.weight v a * indicator (m.mechanism v a input == value)).sum

def jointMass (m : Model n Ω) (defaultUnit : Fin n → Ω) (edges : EdgeSetting n)
    (row : Assignment n) : Rat :=
  integrate m (List.finRange n) defaultUnit fun u =>
    indicator ((List.finRange n).all fun v => evaluate m.graph m.mechanism u edges v == row v)

/-- The response cell equals the product of the independently
coupled local response probabilities at the edge-adjusted parent inputs. -/
theorem edge_joint_mass_eq_product (m : Model n Ω) (defaultUnit : Fin n → Ω)
    (edges : EdgeSetting n) (row : Assignment n) :
    jointMass m defaultUnit edges row =
      ((List.finRange n).map fun v => localMass m v (parents m.graph edges row v) (row v)).prod := by
  let vs := List.finRange n
  let localTest (v : Fin n) (a : Ω) := m.mechanism v a (parents m.graph edges row v) == row v
  have eq (unit : Fin n → Ω) :
      indicator (vs.all fun v => evaluate m.graph m.mechanism unit edges v == row v) =
        (vs.map fun v => indicator (localTest v (unit v))).prod := by
    rw [prod_indicator]
    apply congrArg indicator
    apply Bool.eq_iff_iff.mpr
    simpa [vs, List.all_eq_true, localTest] using
      evaluate_eq_iff_local m.graph m.mechanism unit edges row
  rw [jointMass, integrate_congr m vs defaultUnit eq]
  exact integrate_product m vs defaultUnit (List.nodup_finRange n) fun v a => indicator (localTest v a)

private theorem setNoise_commute (unit : Fin n → Ω) {v w : Fin n} (distinct : v ≠ w)
    (a b : Ω) : setNoise (setNoise unit v a) w b = setNoise (setNoise unit w b) v a := by
  funext u
  by_cases isV : u = v
  · subst u
    simp [setNoise, distinct]
  · by_cases isW : u = w
    · subst u
      simp [setNoise, distinct.symm]
    · simp [setNoise, isV, isW]

private theorem integrate_ignores_coordinate (m : Model n Ω) (order : List (Fin n))
    (unit : Fin n → Ω) (v : Fin n) (a : Ω) (absent : v ∉ order) (f : (Fin n → Ω) → Rat)
    (irrelevant : ∀ u b, f (setNoise u v b) = f u) :
    integrate m order (setNoise unit v a) f = integrate m order unit f := by
  induction order generalizing unit with
  | nil => exact irrelevant unit a
  | cons w rest ih =>
    simp only [List.mem_cons, not_or] at absent
    simp only [integrate]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b _
    rw [setNoise_commute unit absent.1, ih (setNoise unit w b) absent.2]

private theorem integrate_local_factor (m : Model n Ω) (order : List (Fin n))
    (unit : Fin n → Ω) (v : Fin n) (present : v ∈ order) (unique : order.Nodup)
    (f : (Fin n → Ω) → Rat) (irrelevant : ∀ u b, f (setNoise u v b) = f u) (g : Ω → Rat) :
    integrate m order unit (fun u => f u * g (u v)) =
      integrate m order unit f * ((m.atoms v).map fun a => m.weight v a * g a).sum := by
  induction order generalizing unit with
  | nil => simp at present
  | cons w rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases same : v = w
    · subst w
      have fixed (a : Ω) := integrate_ignores_coordinate m rest unit v a absent f irrelevant
      have denominator : integrate m (v :: rest) unit f = integrate m rest unit f := by
        simp only [integrate]
        rw [List.map_congr_left (fun a _ => congrArg (m.weight v a * ·) (fixed a)),
          sum_mul_right, m.normalized, Rat.one_mul]
      rw [denominator, Rat.mul_comm, ← sum_mul_right]
      simp only [integrate]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a _
      rw [integrate_mul_coordinate m rest _ v absent g f, fixed a]
      simp only [setNoise, ↓reduceIte]
      have commute (c : Rat) : m.weight v a * (c * g a) = (m.weight v a * g a) * c := by
        rw [Rat.mul_comm c (g a), Rat.mul_assoc]
      exact commute _
    · have inRest : v ∈ rest := (List.mem_cons.mp present).resolve_left same
      simp only [integrate, ← sum_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a _
      rw [ih (setNoise unit w a) inRest tailUnique, Rat.mul_assoc]

private theorem evaluate_ignores_later_noise (G : DAG n)
    (mechanism : Fin n → Ω → Assignment n → Bool) (unit : Fin n → Ω) (edges : EdgeSetting n)
    (changed v : Fin n) (a : Ω) (earlier : G.rank v < G.rank changed) :
    evaluate G mechanism (setNoise unit changed a) edges v = evaluate G mechanism unit edges v := by
  induction bound : G.rank v using Nat.strongRecOn generalizing v with
  | ind rank ih =>
    rw [evaluate_eq_mechanism, evaluate_eq_mechanism]
    have unequal : v ≠ changed := fun eq => (Nat.lt_irrefl _ (eq ▸ earlier))
    simp only [setNoise, ite_eq_right unequal]
    apply congrArg (mechanism v (unit v))
    funext u
    by_cases parent : G.edge u v = true
    · have hu := G.edge_increases u v parent
      have smaller : G.rank u < rank := bound ▸ hu
      have prior := ih (G.rank u) smaller u (Nat.lt_trans hu earlier) rfl
      simp only [parents, parent, ↓reduceIte, prior]
    · simp [parents, parent]

/-- The graph's observational regime has no overridden parent inputs. -/
def observational : EdgeSetting n := fun _ _ => none

def observesParents (m : Model n Ω) (unit : Fin n → Ω) (v : Fin n) (input : Assignment n) : Bool :=
  (List.finRange n).all fun u => !m.graph.edge u v ||
    evaluate m.graph m.mechanism unit observational u == input u

private theorem observes_parents_ignores_own_noise (m : Model n Ω) (unit : Fin n → Ω)
    (v : Fin n) (input : Assignment n) (a : Ω) :
    observesParents m (setNoise unit v a) v input = observesParents m unit v input := by
  apply congrArg ((List.finRange n).all)
  funext u
  by_cases parent : m.graph.edge u v = true
  · simp [parent, evaluate_ignores_later_noise m.graph m.mechanism unit observational v u a
      (m.graph.edge_increases u v parent)]
  · simp [parent]

def observedParentMass (m : Model n Ω) (defaultUnit : Fin n → Ω) (v : Fin n)
    (input : Assignment n) : Rat :=
  integrate m (List.finRange n) defaultUnit fun u => indicator (observesParents m u v input)

def observedLocalJointMass (m : Model n Ω) (defaultUnit : Fin n → Ω) (v : Fin n)
    (input : Assignment n) (value : Bool) : Rat :=
  integrate m (List.finRange n) defaultUnit fun u => indicator (observesParents m u v input &&
    evaluate m.graph m.mechanism u observational v == value)

def observedConditional (m : Model n Ω) (defaultUnit : Fin n → Ω) (v : Fin n)
    (input : Assignment n) (value : Bool) : Rat :=
  observedLocalJointMass m defaultUnit v input value / observedParentMass m defaultUnit v input

private theorem observed_local_joint_eq_product (m : Model n Ω) (defaultUnit : Fin n → Ω)
    (v : Fin n) (input : Assignment n) (value : Bool) :
    observedLocalJointMass m defaultUnit v input value =
      observedParentMass m defaultUnit v input * localMass m v (parents m.graph observational input v) value := by
  let f (unit : Fin n → Ω) := indicator (observesParents m unit v input)
  let g (a : Ω) := indicator (m.mechanism v a (parents m.graph observational input v) == value)
  have pointwise (unit : Fin n → Ω) :
      indicator (observesParents m unit v input && evaluate m.graph m.mechanism unit observational v == value) =
      f unit * g (unit v) := by
    cases seen : observesParents m unit v input with
    | false => simp [f, seen, indicator, Rat.zero_mul]
    | true =>
      have same : parents m.graph observational (evaluate m.graph m.mechanism unit observational) v =
          parents m.graph observational input v := by
        funext u
        have atU := List.all_eq_true.mp seen u (List.mem_finRange u)
        by_cases parent : m.graph.edge u v = true
        · simpa [parents, observational, parent] using atU
        · simp [parents, parent]
      rw [evaluate_eq_mechanism, same]
      simp [f, g, seen, indicator, Rat.one_mul]
  rw [observedLocalJointMass, integrate_congr m _ defaultUnit pointwise]
  exact integrate_local_factor m _ defaultUnit v (List.mem_finRange v) (List.nodup_finRange n)
    f (fun u a => congrArg indicator (observes_parents_ignores_own_noise m u v input a)) g

/-- Observational conditioning recovers the local response law where
its parent assignment has positive observed mass. -/
theorem observed_conditional_eq_local_mass (m : Model n Ω) (defaultUnit : Fin n → Ω)
    (v : Fin n) (input : Assignment n) (value : Bool)
    (supported : observedParentMass m defaultUnit v input ≠ 0) :
    observedConditional m defaultUnit v input value =
      localMass m v (parents m.graph observational input v) value := by
  rw [observedConditional, observed_local_joint_eq_product, Rat.div_def, Rat.mul_comm _ (localMass _ _ _ _),
    Rat.mul_assoc, Rat.mul_inv_cancel _ supported, Rat.mul_one]

/-- Equation (5) for a finite binary DAG with independent vertex noises,
using the conditionals of the same observational law. -/
theorem edge_g_formula (m : Model n Ω) (defaultUnit : Fin n → Ω)
    (edges : EdgeSetting n) (row : Assignment n)
    (supported : ∀ v, observedParentMass m defaultUnit v (parents m.graph edges row v) ≠ 0) :
    jointMass m defaultUnit edges row =
      ((List.finRange n).map fun v => observedConditional m defaultUnit v
        (parents m.graph edges row v) (row v)).prod := by
  rw [edge_joint_mass_eq_product]
  apply congrArg List.prod
  apply List.map_congr_left
  intro v _
  rw [observed_conditional_eq_local_mass _ _ _ _ _ (supported v)]
  congr 1
  funext u
  by_cases parent : m.graph.edge u v = true <;> simp [parents, observational, parent]

end
end OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeGFormula
