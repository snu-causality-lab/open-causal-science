module
public import Std

/-! # Multiplicative Möbius inversion for finite positive tables

Corresponds to the finite Hammersley–Clifford argument in Grimmett
(1973), pp. 82–84, and the canonical interactions of Besag (1974), §3.
Ratios of probabilities avoid logarithms.
-/

namespace OpenCausalScience.Papers.Grimmett1973

@[expose] public section

variable {V : Type} {States : V → Type}

abbrev Assignment (States : V → Type) := (v : V) → States v
abbrev Table (States : V → Type) := Assignment States → Rat

def Positive (p : Table States) : Prop := ∀ x, 0 < p x

def setAt [DecidableEq V] (x : Assignment States) (v : V) (value : States v) :
    Assignment States :=
  fun u => if equal : v = u then equal ▸ value else x u

@[simp] theorem setAt_same [DecidableEq V] (x : Assignment States) (v : V) (a : States v) :
    setAt x v a v = a := by
  simp [setAt]

@[simp] theorem setAt_other [DecidableEq V] (x : Assignment States) {v u : V}
    (a : States v) (different : v ≠ u) : setAt x v a u = x u := by
  simp [setAt, different]

theorem setAt_current [DecidableEq V] (x : Assignment States) (v : V) :
    setAt x v (x v) = x := by
  funext u
  by_cases same : v = u
  · subst u
    simp
  · exact setAt_other _ _ same

theorem setAt_twice [DecidableEq V] (x : Assignment States) (v : V)
    (a b : States v) : setAt (setAt x v a) v b = setAt x v b := by
  funext u
  by_cases same : v = u
  · subst u
    simp
  · simp [same]

theorem setAt_commute [DecidableEq V] (x : Assignment States) {v u : V} (different : v ≠ u)
    (a : States v) (b : States u) : setAt (setAt x v a) u b = setAt (setAt x u b) v a := by
  funext w
  by_cases left : v = w
  · subst w
    simp [Ne.symm different]
  · by_cases right : u = w
    · subst w
      simp [different]
    · simp [left, right]

def retain [DecidableEq V] (anchor x : Assignment States) (scope : List V) :
    Assignment States :=
  fun v => if v ∈ scope then x v else anchor v

theorem retain_cons [DecidableEq V] (anchor x : Assignment States) (v : V) (rest : List V) :
    retain anchor x (v :: rest) = setAt (retain anchor x rest) v (x v) := by
  funext u
  by_cases same : v = u
  · subst u
    simp [retain]
  · simp [retain, same, Ne.symm same]

theorem retain_set_anchor [DecidableEq V] (anchor x : Assignment States) (scope : List V)
    {v : V} (absent : v ∉ scope) :
    setAt (retain anchor x scope) v (anchor v) = retain anchor x scope := by
  have equal : retain anchor x scope v = anchor v := by simp [retain, absent]
  rw [← equal, setAt_current]

def sublists : List V → List (List V)
  | [] => [[]]
  | v :: rest => sublists rest ++ (sublists rest).map (v :: ·)

theorem sublists_subset {scope xs : List V} (member : scope ∈ sublists xs) :
    ∀ v ∈ scope, v ∈ xs := by
  induction xs generalizing scope with
  | nil =>
    simp [sublists] at member
    subst scope
    exact fun _ h => h
  | cons u tail ih =>
    rcases List.mem_append.mp (show scope ∈ sublists tail ++
        (sublists tail).map (u :: ·) from member) with without | withU
    · exact fun v h => List.mem_cons_of_mem _ (ih without v h)
    · obtain ⟨rest, restMem, rfl⟩ := List.mem_map.mp withU
      intro v hv
      rcases List.mem_cons.mp hv with same | later
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem _ (ih restMem v later)

def contrast [DecidableEq V] (p : Table States) (v : V) (a b : States v) :
    Table States :=
  fun x => p (setAt x v a) / p (setAt x v b)

theorem contrast_positive [DecidableEq V] {p : Table States} (positive : Positive p)
    (v : V) (a b : States v) : Positive (contrast p v a b) := by
  intro x
  rw [contrast, Rat.div_def]
  exact Rat.mul_pos (positive _) (Rat.inv_pos.mpr (positive _))

def interaction [DecidableEq V] (anchor x : Assignment States) (p : Table States) :
    List V → Rat
  | [] => p anchor
  | v :: rest => interaction anchor x (contrast p v (x v) (anchor v)) rest

theorem interaction_positive [DecidableEq V] (anchor x : Assignment States) (p : Table States)
    (positive : Positive p) (xs : List V) : 0 < interaction anchor x p xs := by
  induction xs generalizing p with
  | nil => exact positive _
  | cons v rest ih =>
    exact ih _ (contrast_positive positive v (x v) (anchor v))

theorem interaction_local [DecidableEq V] (p : Table States) (anchor x y : Assignment States)
    (scope : List V) (same : ∀ v ∈ scope, x v = y v) :
    interaction anchor x p scope = interaction anchor y p scope := by
  induction scope generalizing p with
  | nil => rfl
  | cons v rest ih =>
    simp only [interaction]
    rw [same v List.mem_cons_self]
    exact ih _ (fun v h => same v (List.mem_cons_of_mem _ h))

private theorem prod_concat (xs ys : List Rat) :
    (xs ++ ys).prod = xs.prod * ys.prod := by
  induction xs with
  | nil => simp [Rat.one_mul]
  | cons x tail ih =>
    simp only [List.cons_append, List.prod_cons, ih, Rat.mul_assoc]

theorem multiplicative_mobius_inversion [DecidableEq V] (p : Table States)
    (positive : Positive p) (anchor x : Assignment States) (scope : List V)
    (unique : scope.Nodup) :
    ((sublists scope).map (interaction anchor x p)).prod = p (retain anchor x scope) := by
  induction scope generalizing p with
  | nil =>
    simp only [sublists, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      interaction, Rat.mul_one]
    rfl
  | cons v rest ih =>
    have up := List.nodup_cons.mp unique
    simp only [sublists, List.map_append, prod_concat, List.map_map]
    change ((sublists rest).map (interaction anchor x p)).prod *
      ((sublists rest).map (interaction anchor x (contrast p v (x v) (anchor v)))).prod =
        p (retain anchor x (v :: rest))
    rw [ih p positive up.2,
      ih _ (contrast_positive positive v (x v) (anchor v)) up.2,
      retain_cons, contrast, retain_set_anchor _ _ _ up.1, Rat.mul_comm (p (retain anchor x rest))]
    exact Rat.div_mul_cancel (Rat.ne_of_gt (positive _))

def pairChanges [DecidableEq V] (x : Assignment States) (u v : V)
    (a : States u) (b : States v) : Assignment States :=
  setAt (setAt x u a) v b

def Rectangle [DecidableEq V] (p : Table States) (u v : V) : Prop :=
  ∀ x a a' b b',
    p (pairChanges x u v a b) * p (pairChanges x u v a' b') =
      p (pairChanges x u v a b') * p (pairChanges x u v a' b)

def PairwiseMarkov [DecidableEq V] (graph : V → V → Prop) (p : Table States) : Prop :=
  ∀ u v, u ≠ v → ¬ graph u v → Rectangle p u v

def IsClique (graph : V → V → Prop) (scope : List V) : Prop :=
  ∀ u ∈ scope, ∀ v ∈ scope, u ≠ v → graph u v

def Ignores [DecidableEq V] (p : Table States) (v : V) : Prop :=
  ∀ x a, p (setAt x v a) = p x

private theorem div_times_div (a b c d : Rat) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  rw [Rat.div_def (a * c), Rat.inv_mul_rev]
  simp only [Rat.div_def]
  grind

private theorem ratio_eq_from_rectangle (a b c d : Rat)
    (hb : 0 < b) (hd : 0 < d) (cross : a * d = c * b) :
    a / b = c / d := by
  have scaled : (a / b) * (b * d) = (c / d) * (b * d) := by
    have left : (a / b) * b = a := Rat.div_mul_cancel (Rat.ne_of_gt hb)
    have right : (c / d) * d = c := Rat.div_mul_cancel (Rat.ne_of_gt hd)
    grind
  simpa only [Rat.mul_div_cancel (Rat.ne_of_gt (Rat.mul_pos hb hd))] using
    congrArg (fun y => y / (b * d)) scaled

theorem contrast_rectangle [DecidableEq V] {p : Table States} {u v s : V}
    (hu : u ≠ s) (hv : v ≠ s) (a b : States s) (rect : Rectangle p u v) :
    Rectangle (contrast p s a b) u v := by
  intro x au av bu bv
  have move (i : States u) (j : States v) (k : States s) :
      setAt (pairChanges x u v i j) s k = pairChanges (setAt x s k) u v i j := by
    unfold pairChanges
    rw [setAt_commute _ hv, setAt_commute x hu]
  simp only [contrast, div_times_div, move]
  rw [rect (setAt x s a), rect (setAt x s b)]

theorem contrast_ignores_nonedge [DecidableEq V] {p : Table States} {u v : V}
    (distinct : u ≠ v) (positive : Positive p) (rectangle : Rectangle p u v)
    (a b : States u) : Ignores (contrast p u a b) v := by
  intro x value
  have h := rectangle x a b value (x v)
  have same (k : States u) : pairChanges x u v k (x v) = setAt x u k := by
    unfold pairChanges
    have e := setAt_other x k distinct
    calc
      _ = setAt (setAt x u k) v (setAt x u k v) :=
        congrArg (setAt (setAt x u k) v) e.symm
      _ = _ := setAt_current _ _
  rw [same a, same b] at h
  simp only [contrast, ← setAt_commute _ distinct]
  exact ratio_eq_from_rectangle _ _ _ _ (positive _) (positive _) h

theorem contrast_preserves_ignores [DecidableEq V] {p : Table States} {u v : V}
    (distinct : u ≠ v) (ignores : Ignores p v) (a b : States u) :
    Ignores (contrast p u a b) v := by
  intro x value
  simp only [contrast, ← setAt_commute _ distinct]
  rw [ignores _ _, ignores _ _]

theorem interaction_unit [DecidableEq V] (anchor x : Assignment States) (p : Table States)
    (unit : ∀ a, p a = 1) (scope : List V) : interaction anchor x p scope = 1 := by
  induction scope generalizing p with
  | nil => exact unit _
  | cons head tail ih =>
    apply ih
    intro a
    rw [contrast, unit, unit]
    decide +kernel

theorem interaction_one_of_ignores [DecidableEq V] {anchor x : Assignment States}
    {p : Table States} {v : V} (positive : Positive p) (ignores : Ignores p v)
    {scope : List V} (member : v ∈ scope) :
    interaction anchor x p scope = 1 := by
  induction scope generalizing p with
  | nil => contradiction
  | cons u tail ih =>
    by_cases equal : u = v
    · subst u
      change interaction anchor x (contrast p v (x v) (anchor v)) tail = 1
      apply interaction_unit
      intro a
      rw [contrast, ignores _ _, ignores _ _, Rat.div_def]
      exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (positive a))
    · have tailMem : v ∈ tail :=
        (List.mem_cons.mp member).resolve_left (Ne.symm equal)
      exact ih (contrast_positive positive u (x u) (anchor u))
        (contrast_preserves_ignores equal ignores _ _) tailMem

theorem interaction_one_of_rectangles [DecidableEq V] {anchor x : Assignment States}
    {p : Table States} {u v : V} (positive : Positive p) (distinct : u ≠ v)
    (forward : Rectangle p u v) (reverse : Rectangle p v u) {scope : List V}
    (memU : u ∈ scope) (memV : v ∈ scope) :
    interaction anchor x p scope = 1 := by
  induction scope generalizing p with
  | nil => contradiction
  | cons head tail ih =>
    by_cases equalU : head = u
    · subst head
      exact interaction_one_of_ignores (contrast_positive positive u (x u) (anchor u))
        (contrast_ignores_nonedge distinct positive forward _ _)
        ((List.mem_cons.mp memV).resolve_left (Ne.symm distinct))
    · by_cases equalV : head = v
      · subst head
        exact interaction_one_of_ignores (contrast_positive positive v (x v) (anchor v))
          (contrast_ignores_nonedge (Ne.symm distinct) positive reverse _ _)
          ((List.mem_cons.mp memU).resolve_left distinct)
      · have hU := (List.mem_cons.mp memU).resolve_left (Ne.symm equalU)
        have hV := (List.mem_cons.mp memV).resolve_left (Ne.symm equalV)
        exact ih (contrast_positive positive head (x head) (anchor head))
          (contrast_rectangle (Ne.symm equalU) (Ne.symm equalV) _ _ forward)
          (contrast_rectangle (Ne.symm equalV) (Ne.symm equalU) _ _ reverse) hU hV

theorem interaction_one_of_nonedge [DecidableEq V] {edge : V → V → Prop}
    (symm : ∀ u v, edge u v ↔ edge v u) {anchor x : Assignment States}
    {p : Table States} {u v : V} (positive : Positive p) (markov : PairwiseMarkov edge p)
    (distinct : u ≠ v) (missing : ¬ edge u v) {scope : List V}
    (memU : u ∈ scope) (memV : v ∈ scope) :
    interaction anchor x p scope = 1 :=
  interaction_one_of_rectangles positive distinct (markov u v distinct missing)
    (markov v u (Ne.symm distinct) (fun h => missing ((symm u v).mpr h))) memU memV

structure Potential (States : V → Type) where
  scope : List V
  value : Table States
  localValue : ∀ x y, (∀ v ∈ scope, x v = y v) → value x = value y

def CliqueFactorization (edge : V → V → Prop) (p : Table States) : Prop :=
  ∃ factors : List (Potential States),
    (∀ f ∈ factors, IsClique edge f.scope) ∧
    (∀ x, p x = (factors.map fun f => f.value x).prod)

private theorem product_filter_of_unit {α : Type} (xs : List α) (keep : α → Bool)
    (value : α → Rat) (unit : ∀ a ∈ xs, keep a = false → value a = 1) :
    ((xs.filter keep).map value).prod = (xs.map value).prod := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    have tailEqual := ih (fun a ha h => unit a (List.mem_cons_of_mem _ ha) h)
    cases h : keep head
    · rw [List.filter_cons, h]
      simpa [unit head List.mem_cons_self h, Rat.one_mul] using tailEqual
    · rw [List.filter_cons, h]
      simp [tailEqual]

theorem nonclique_interaction_is_one [DecidableEq V] {edge : V → V → Prop}
    (symm : ∀ u v, edge u v ↔ edge v u) {p : Table States}
    (positive : Positive p) (markov : PairwiseMarkov edge p)
    (anchor x : Assignment States) {scope : List V} (nonclique : ¬ IsClique edge scope) :
    interaction anchor x p scope = 1 := by
  classical
  have witness : ∃ u ∈ scope, ∃ v ∈ scope, u ≠ v ∧ ¬ edge u v := by
    apply Classical.byContradiction
    intro none
    apply nonclique
    intro u hu v hv different
    apply Classical.byContradiction
    intro missing
    exact none ⟨u, hu, v, hv, different, missing⟩
  obtain ⟨u, hu, v, hv, different, missing⟩ := witness
  exact interaction_one_of_nonedge symm positive markov different missing hu hv

theorem positive_clique_factors_of_unit_interactions [DecidableEq V] {edge : V → V → Prop}
    (vertices : List V) (complete : ∀ v, v ∈ vertices) (unique : vertices.Nodup)
    (anchor : Assignment States) {p : Table States} (positive : Positive p)
    (unit : ∀ x scope, scope ∈ sublists vertices → ¬ IsClique edge scope →
      interaction anchor x p scope = 1) :
    ∃ factors : List (Potential States),
      (∀ f ∈ factors, IsClique edge f.scope ∧ ∀ x, 0 < f.value x) ∧
      (∀ x, p x = (factors.map fun f => f.value x).prod) := by
  classical
  let keep := fun l : List V => decide (IsClique edge l)
  let potential := fun scope : List V =>
    ({scope := scope
      value := fun x => interaction anchor x p scope
      localValue := fun x y same => interaction_local p anchor x y scope same} : Potential States)
  refine ⟨((sublists vertices).filter keep).map potential, ?_, ?_⟩
  · intro f hf
    obtain ⟨scope, hs, rfl⟩ := List.mem_map.mp hf
    exact ⟨of_decide_eq_true (List.mem_filter.mp hs).2, fun x => interaction_positive _ _ _ positive _⟩
  · intro x
    have factor_neutral (l : List V) (mem : l ∈ sublists vertices) (hc : keep l = false) :
        interaction anchor x p l = 1 := unit x l mem (of_decide_eq_false hc)
    rw [List.map_map]
    change p x = (((sublists vertices).filter keep).map (interaction anchor x p)).prod
    rw [product_filter_of_unit _ _ _ factor_neutral,
      multiplicative_mobius_inversion p positive anchor x vertices unique]
    have retain_all : retain anchor x vertices = x := by
      funext v
      simp [retain, complete v]
    rw [retain_all]

theorem positive_clique_factorization [DecidableEq V] {edge : V → V → Prop}
    (symm : ∀ u v, edge u v ↔ edge v u) (vertices : List V)
    (complete : ∀ v, v ∈ vertices) (unique : vertices.Nodup)
    (anchor : Assignment States) {p : Table States}
    (positive : Positive p) (markov : PairwiseMarkov edge p) :
    ∃ factors : List (Potential States),
      (∀ f ∈ factors, IsClique edge f.scope ∧ ∀ x, 0 < f.value x) ∧
      (∀ x, p x = (factors.map fun f => f.value x).prod) :=
  positive_clique_factors_of_unit_interactions vertices complete unique anchor positive
    (fun x _ _ nc => nonclique_interaction_is_one symm positive markov anchor x nc)

theorem clique_factors_imply_pairwise_markov [DecidableEq V] {edge : V → V → Prop}
    {p : Table States} (factorized : CliqueFactorization edge p) :
    PairwiseMarkov edge p := by
  obtain ⟨factors, cliques, factor⟩ := factorized
  intro u v distinct missing x a a' b b'
  rw [factor, factor, factor, factor]
  clear factor
  have missing_term (f : Potential States) (w : V) (hw : w ∉ f.scope)
      (z : Assignment States) (value : States w) : f.value (setAt z w value) = f.value z := by
    apply f.localValue
    intro k hk
    exact setAt_other z value (fun equal => hw (equal ▸ hk))
  have single (f : Potential States) (hf : IsClique edge f.scope) :
      f.value (pairChanges x u v a b) * f.value (pairChanges x u v a' b') =
        f.value (pairChanges x u v a b') * f.value (pairChanges x u v a' b) := by
    by_cases hu : u ∈ f.scope
    · have hv : v ∉ f.scope := fun h => missing (hf u hu v h distinct)
      simp only [pairChanges, missing_term f v hv]
    · simp only [pairChanges, setAt_commute x distinct, missing_term f u hu]
      exact Rat.mul_comm _ _
  induction factors with
  | nil => rfl
  | cons head tail ih =>
    have headRect := single head (cliques head List.mem_cons_self)
    have tailRect := ih (fun f hf => cliques f (List.mem_cons_of_mem _ hf))
    simp only [List.map_cons, List.prod_cons]
    grind only

theorem pairwise_markov_iff_clique_factorization [DecidableEq V] {edge : V → V → Prop}
    (symm : ∀ u v, edge u v ↔ edge v u) (vertices : List V)
    (complete : ∀ v, v ∈ vertices) (unique : vertices.Nodup)
    (anchor : Assignment States) {p : Table States} (positive : Positive p) :
    PairwiseMarkov edge p ↔ CliqueFactorization edge p :=
  ⟨fun markov => by
    obtain ⟨factors, cliques, factor⟩ :=
      positive_clique_factorization symm vertices complete unique anchor positive markov
    exact ⟨factors, fun f hf => (cliques f hf).1, factor⟩,
    clique_factors_imply_pairwise_markov⟩

theorem pairwise_markov_iff_unit_nonclique_interactions [DecidableEq V]
    {edge : V → V → Prop} (symm : ∀ u v, edge u v ↔ edge v u) (vertices : List V)
    (complete : ∀ v, v ∈ vertices) (unique : vertices.Nodup)
    (anchor : Assignment States) {p : Table States} (positive : Positive p) :
    PairwiseMarkov edge p ↔
      ∀ x scope, scope ∈ sublists vertices → ¬ IsClique edge scope →
        interaction anchor x p scope = 1 := by
  constructor
  · exact fun markov x _ _ nc => nonclique_interaction_is_one symm positive markov anchor x nc
  · intro units
    obtain ⟨factors, cliques, factor⟩ :=
      positive_clique_factors_of_unit_interactions vertices complete unique anchor positive units
    exact clique_factors_imply_pairwise_markov ⟨factors, fun f hf => (cliques f hf).1, factor⟩

theorem factored_nonzero_of_locally_realized {edge : V → V → Prop} {p : Table States}
    (factorized : CliqueFactorization edge p) (x : Assignment States)
    (realized : ∀ scope : List V, IsClique edge scope →
      ∃ y : Assignment States, p y ≠ 0 ∧ ∀ v ∈ scope, x v = y v) :
    p x ≠ 0 := by
  obtain ⟨factors, cliques, factor⟩ := factorized
  have term_nonzero (f : Potential States) (hf : f ∈ factors) : f.value x ≠ 0 := by
    obtain ⟨y, positive, agreement⟩ := realized f.scope (cliques f hf)
    rw [f.localValue x y agreement]
    intro zero
    apply positive
    rw [factor]
    have has_zero : (0 : Rat) ∈ factors.map (fun f => f.value y) :=
      List.mem_map.mpr ⟨f, hf, zero⟩
    generalize factors.map (fun f => f.value y) = xs at has_zero ⊢
    induction xs with
    | nil => contradiction
    | cons head tail ih =>
      rcases List.mem_cons.mp has_zero with here | later
      · rw [List.prod_cons, ← here, Rat.zero_mul]
      · rw [List.prod_cons, ih later, Rat.mul_zero]
  rw [factor]
  clear factor cliques realized
  induction factors with
  | nil =>
    change (1 : Rat) ≠ 0
    decide +kernel
  | cons head tail ih =>
    have head_nonzero := term_nonzero head List.mem_cons_self
    have tail_nonzero := ih (fun f hf => term_nonzero f (List.mem_cons_of_mem _ hf))
    simp only [List.map_cons, List.prod_cons]
    intro zero
    have h : (head.value x * (tail.map fun f => f.value x).prod) / head.value x = 0 := by
      rw [zero, Rat.div_def, Rat.zero_mul]
    rw [Rat.mul_comm, Rat.mul_div_cancel head_nonzero] at h
    exact tail_nonzero h

end

end OpenCausalScience.Papers.Grimmett1973
