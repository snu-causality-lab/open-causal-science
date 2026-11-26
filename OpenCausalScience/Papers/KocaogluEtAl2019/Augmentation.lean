module
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

/-! # F-node augmentation for controlled soft interventions

The graph construction in Kocaoglu et al. (2019), Definition 3. The root
construction also serves the indexed comparisons of Jaber et al. (2020).
The original graph includes any explicit latent vertices.
-/

namespace OpenCausalScience.Papers.KocaogluEtAl2019.Augmentation

open OpenCausalScience.Papers.KimEtAl2026
open BayesBall BayesBallCorrectness

@[expose] public section

variable {n k : Nat}

abbrev Target (n : Nat) := Fin n → Bool

/-- Canonical vertex lists give extensional equality of target sets. -/
def differences (regimes : List (Target n)) : List (List (Fin n)) :=
  (regimes.flatMap fun left => regimes.map fun right =>
    (List.finRange n).filter fun v => left v != right v).eraseDups

theorem mem_differences_iff (regimes : List (Target n)) (d : List (Fin n)) :
    d ∈ differences regimes ↔
      ∃ left ∈ regimes, ∃ right ∈ regimes,
        (List.finRange n).filter (fun v => left v != right v) = d := by
  simp [differences, List.mem_flatMap, List.mem_map]

def addRoots (G : DAG n) (children : Fin k → Target n) : DAG (n + k) where
  edge := fun u v => Fin.addCases
    (fun a => Fin.addCases (G.edge a) (fun _ => false) v)
    (fun i => Fin.addCases (children i) (fun _ => false) v) u
  rank := Fin.addCases (fun a => G.rank a + 1) (fun _ => 0)
  edge_increases := by
    intro u v
    refine Fin.addCases (fun a => ?_) (fun i => ?_) u
    · refine Fin.addCases (fun b => ?_) (fun j => ?_) v
      · simpa using fun h => Nat.succ_lt_succ (G.edge_increases a b h)
      · simp
    · refine Fin.addCases (fun b => ?_) (fun j => ?_) v <;> simp

@[simp] theorem base_edge (G : DAG n) (children : Fin k → Target n) (u v : Fin n) :
    (addRoots G children).edge (Fin.castAdd k u) (Fin.castAdd k v) = G.edge u v := by
  simp [addRoots]

@[simp] theorem root_edge (G : DAG n) (children : Fin k → Target n) (i : Fin k) (v : Fin n) :
    (addRoots G children).edge (Fin.natAdd n i) (Fin.castAdd k v) = children i v := by
  simp [addRoots]

@[simp] theorem no_incoming_root (G : DAG n) (children : Fin k → Target n)
    (u : Fin (n + k)) (i : Fin k) :
    (addRoots G children).edge u (Fin.natAdd n i) = false := by
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) u <;> simp [addRoots]

/-- The controlled-experiment augmentation. An empty difference has only
an isolated root, which may also be suppressed from drawings. -/
def augmented (G : DAG n) (regimes : List (Target n)) : DAG (n + (differences regimes).length) :=
  addRoots G (fun i v => (differences regimes)[i].contains v)

/-- Condition on the same old variables and on every freshly added root. -/
def withRootsConditioned (W : Target n) : Target (n + k) :=
  Fin.addCases W (fun _ => true)

private theorem lift_directed {G : DAG n} {children : Fin k → Target n} {u v : Fin n}
    (walk : G.DirectedWalk u v) :
    (addRoots G children).DirectedWalk (Fin.castAdd k u) (Fin.castAdd k v) := by
  induction walk with
  | single edge => exact .single (by simpa only [base_edge] using edge)
  | extend _ edge ih => exact .extend ih (by simpa only [base_edge] using edge)

private theorem recover_base_edge {G : DAG n} {children : Fin k → Target n}
    {u : Fin n} {v : Fin (n + k)}
    (edge : (addRoots G children).edge (Fin.castAdd k u) v = true) :
    ∃ v₀ : Fin n, v = Fin.castAdd k v₀ ∧ G.edge u v₀ = true := by
  revert edge
  refine Fin.addCases (fun v₀ => ?_) (fun j => ?_) v
  · intro edge
    exact ⟨v₀, rfl, by simpa only [base_edge] using edge⟩
  · simp

private theorem project_directed {G : DAG n} {children : Fin k → Target n}
    {u v : Fin (n + k)} (walk : (addRoots G children).DirectedWalk u v)
    {u₀ : Fin n} (start : u = Fin.castAdd k u₀) :
    ∃ v₀ : Fin n, v = Fin.castAdd k v₀ ∧ G.DirectedWalk u₀ v₀ := by
  induction walk with
  | single edge =>
    rw [start] at edge
    obtain ⟨v₀, eq, oldEdge⟩ := recover_base_edge edge
    exact ⟨v₀, eq, .single oldEdge⟩
  | extend _ edge ih =>
    obtain ⟨w₀, eq, oldWalk⟩ := ih
    rw [eq] at edge
    obtain ⟨v₀, eq', oldEdge⟩ := recover_base_edge edge
    exact ⟨v₀, eq', .extend oldWalk oldEdge⟩

private theorem member_base {G : DAG n} {children : Fin k → Target n}
    (W : Target n) (u : Fin n) :
    (Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W)).member
      (Fin.castAdd k u) = (Conditioning.ofPredicate G W).member u := by
  simp [Conditioning.ofPredicate, withRootsConditioned]

private theorem activation_base {G : DAG n} {children : Fin k → Target n}
    (W : Target n) (v : Fin n) :
    (Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W)).activated
        (Fin.castAdd k v) = (Conditioning.ofPredicate G W).activated v := by
  let C := Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W)
  let D := Conditioning.ofPredicate G W
  have descendants : C.descendantHit (Fin.castAdd k v) = D.descendantHit v := by
    apply Bool.eq_iff_iff.mpr
    rw [C.descendant_spec, D.descendant_spec]
    constructor
    · rintro ⟨w, has, walk⟩
      obtain ⟨w₀, rfl, oldWalk⟩ := project_directed walk rfl
      exact ⟨w₀, (member_base (G := G) (children := children) W w₀).symm.trans has, oldWalk⟩
    · rintro ⟨w, has, walk⟩
      exact ⟨Fin.castAdd k w, (member_base (G := G) (children := children) W w).trans has,
        lift_directed walk⟩
  unfold Conditioning.activated
  change (C.member (Fin.castAdd k v) || C.descendantHit (Fin.castAdd k v)) =
    (D.member v || D.descendantHit v)
  rw [descendants, member_base]

private def liftState (k : Nat) (u : State (Fin n)) : State (Fin (n+k)) :=
  (Fin.castAdd k u.1, u.2)

private theorem step_base_iff {G : DAG n} {children : Fin k → Target n}
    (W : Target n) (u v : State (Fin n)) :
    ActiveStep (Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W))
      (liftState k u) (liftState k v) ↔ ActiveStep (Conditioning.ofPredicate G W) u v := by
  obtain ⟨a, arrival⟩ := u
  obtain ⟨b, outgoing⟩ := v
  cases arrival <;> cases outgoing <;>
    simp [ActiveStep, Move, OpenTurn, liftState, member_base, activation_base]

private theorem lift_active {G : DAG n} {children : Fin k → Target n} {W : Target n}
    {u v : State (Fin n)} {route : List (Fin n)}
    (walk : ActiveWalk (Conditioning.ofPredicate G W) u route v) :
    ActiveWalk (Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W))
      (liftState k u) (route.map (Fin.castAdd k)) (liftState k v) := by
  induction walk with
  | nil => exact .nil _
  | cons step _ ih => exact .cons ((step_base_iff W _ _).mpr step) ih

private theorem castAdd_inj {x y : Fin n} (eq : Fin.castAdd k x = Fin.castAdd k y) : x = y :=
  Fin.ext (congrArg (fun v : Fin (n+k) => v.val) eq)

private theorem root_ne_base (i : Fin k) (v : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd k v := by
  intro same
  have val := congrArg Fin.val same
  change n + i.val = v.val at val
  omega

private theorem project_active {G : DAG n} {children : Fin k → Target n} {W : Target n}
    {u v : State (Fin (n+k))} {route : List (Fin (n+k))}
    (walk : ActiveWalk (Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W))
      u route v) (a b : State (Fin n)) (left : u = liftState k a) (right : v = liftState k b) :
    ∃ oldRoute, ActiveWalk (Conditioning.ofPredicate G W) a oldRoute b := by
  induction walk generalizing a b with
  | nil =>
    have eq := left.symm.trans right
    have value : a.1 = b.1 := castAdd_inj (congrArg Prod.fst eq)
    have direction : a.2 = b.2 := congrArg (fun s : State (Fin (n+k)) => s.2) eq
    have ab : a = b := Prod.ext value direction
    subst b
    exact ⟨[], .nil _⟩
  | @cons start next finish visited step tail ih =>
    obtain ⟨vertex, dir⟩ := next
    revert step tail ih
    refine Fin.addCases (fun w => ?_) (fun i => ?_) vertex
    · intro step _ ih
      let mid : State (Fin n) := (w, dir)
      obtain ⟨rest, path⟩ := ih mid b rfl right
      rw [left] at step
      exact ⟨w :: rest, .cons ((step_base_iff W a mid).mp step) path⟩
    · intro step tail _
      have arrived : dir = .up := by
        cases dir with
        | up => rfl
        | down =>
          have impossible := step.1
          simp [Move] at impossible
      subst dir
      cases tail with
      | nil =>
        exact False.elim (root_ne_base i b.1 (congrArg Prod.fst right))
      | cons nextStep _ =>
        have impossible := nextStep.2
        simp [OpenTurn, Conditioning.ofPredicate, withRootsConditioned] at impossible

/-- Proposition 1(1). Ordinary d-connections are preserved after all F-roots
are conditioned on. A conditioned F-root cannot be a collider on a path. -/
theorem dconnected_with_roots_conditioned_iff {G : DAG n} (children : Fin k → Target n)
    (W : Target n) (a b : Fin n) :
    DConnected (Conditioning.ofPredicate (addRoots G children) (withRootsConditioned W))
      (Fin.castAdd k a) (Fin.castAdd k b) ↔ DConnected (Conditioning.ofPredicate G W) a b := by
  constructor
  · rintro ⟨ha, hb, route, arrival, walk, _⟩
    obtain ⟨oldRoute, path⟩ := project_active walk (a, .up) (b, arrival) rfl rfl
    obtain ⟨shorter, last, simple, endpoint, distinct, _⟩ := path.to_simple
    obtain ⟨v, dir⟩ := last
    change v = b at endpoint
    subst v
    exact ⟨by simpa [Conditioning.ofPredicate, withRootsConditioned] using ha,
      by simpa [Conditioning.ofPredicate, withRootsConditioned] using hb, shorter, dir, simple,
      distinct⟩
  · rintro ⟨ha, hb, route, arrival, walk, _⟩
    let path := lift_active (children := children) walk
    obtain ⟨shorter, last, simple, endpoint, distinct, _⟩ := path.to_simple
    obtain ⟨v, dir⟩ := last
    change v = Fin.castAdd k b at endpoint
    subst v
    exact ⟨by simpa [Conditioning.ofPredicate, withRootsConditioned] using ha,
      by simpa [Conditioning.ofPredicate, withRootsConditioned] using hb, shorter, dir, simple,
      distinct⟩

end
end OpenCausalScience.Papers.KocaogluEtAl2019.Augmentation
