module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Probability.FiniteSummation

/-! # Ancestral marginals of a recursive product

Summing a sink's own coordinate eliminates its normalized local
factor. Iteration gives the retained factor product for any checked
sink elimination order. Neither the factors nor their product need
to be strictly positive. Source: https://doi.org/10.1002/net.3230200503
-/

namespace OpenCausalScience.Papers.LauritzenEtAl1990.KernelElimination

open Probability.FiniteSummation (sumOver productOver sum_congr sum_mul_right product_congr
  product_partition)

@[expose] public section

variable {n : Nat} {A : Type}

abbrev State (n : Nat) (A : Type) := Fin n → A

def assign (x : State n A) (vertex : Fin n) (value : A) : State n A :=
  fun v => if v = vertex then value else x v

def Family (G : DAG n) (child u : Fin n) : Prop := u = child ∨ G.edge u child = true

structure Kernels (G : DAG n) (states : List A) where
  value : Fin n → State n A → Rat
  readsFamily : ∀ child x y, (∀ u, Family G child u → x u = y u) →
    value child x = value child y
  normalized : ∀ child x, sumOver states (fun a => value child (assign x child a)) = 1

def density {G : DAG n} {states : List A} (K : Kernels G states)
    (vertices : List (Fin n)) (x : State n A) : Rat :=
  productOver vertices (fun v => K.value v x)

def sumOut (states : List A) (vertex : Fin n) (table : State n A → Rat) (x : State n A) :
    Rat := sumOver states (fun value => table (assign x vertex value))

theorem eliminate_sink {G : DAG n} {states : List A} (K : Kernels G states)
    (sink : Fin n) (remaining : List (Fin n)) (x : State n A)
    (fresh : sink ∉ remaining)
    (noChild : ∀ child ∈ remaining, G.edge sink child = false) :
    sumOut states sink (density K (sink :: remaining)) x = density K remaining x := by
  have remains (a : A) : density K remaining (assign x sink a) = density K remaining x := by
    apply product_congr
    intro child childMember
    apply K.readsFamily
    intro u inFamily
    have ne : u ≠ sink := by
      intro equal
      subst u
      rcases inFamily with rfl | arrow
      · exact fresh childMember
      · exact Bool.false_ne_true ((noChild child childMember).symm.trans arrow)
    simp [assign, ne]
  calc
    _ = sumOver states (fun a => K.value sink (assign x sink a) * density K remaining x) := by
      apply sum_congr
      intro a _
      change K.value sink (assign x sink a) * density K remaining (assign x sink a) = _
      rw [remains a]
    _ = _ := by rw [sum_mul_right, K.normalized, Rat.one_mul]

inductive SinkOrder (G : DAG n) (kept : List (Fin n)) : List (Fin n) → Prop
  | nil : SinkOrder G kept []
  | cons {v removed} : v ∉ removed ++ kept →
      (∀ child ∈ removed ++ kept, G.edge v child = false) →
      SinkOrder G kept removed → SinkOrder G kept (v :: removed)

def marginalize (states : List A) (table : State n A → Rat) : List (Fin n) → State n A → Rat
  | [] => table
  | v :: remaining => marginalize states (sumOut states v table) remaining

theorem marginalize_sinks {G : DAG n} {states : List A} (K : Kernels G states)
    (kept removed : List (Fin n)) (valid : SinkOrder G kept removed) :
    marginalize states (density K (removed ++ kept)) removed = density K kept := by
  induction valid with
  | nil => rfl
  | @cons v remaining fresh noChild _ ih =>
    change marginalize states (sumOut states v (density K (v :: (remaining ++ kept)))) remaining = _
    have one : sumOut states v (density K (v :: (remaining ++ kept))) =
        density K (remaining ++ kept) :=
      funext fun x => eliminate_sink K v (remaining ++ kept) x fresh noChild
    rw [one]
    exact ih

def splice (side : Fin n → Bool) (left right : State n A) : State n A :=
  fun v => if side v then left v else right v

theorem splice_projections (side : Fin n → Bool) (x fixed : State n A) :
    splice side (splice side x fixed) (splice side fixed x) = x := by
  funext v
  cases h : side v <;> simp [splice, h]

/-- Once the unused coordinates of each component are fixed, a full
assignment determines each of its component assignments uniquely. -/
theorem splice_eq_iff (side : Fin n → Bool) (left right x fixed : State n A)
    (leftFixed : ∀ v, side v = false → left v = fixed v)
    (rightFixed : ∀ v, side v = true → right v = fixed v) :
    splice side left right = x ↔
      left = splice side x fixed ∧ right = splice side fixed x := by
  constructor
  · intro same
    constructor <;> funext v <;> cases h : side v
    · simp [splice, h, leftFixed v h]
    · simpa [splice, h] using congrFun same v
    · simpa [splice, h] using congrFun same v
    · simp [splice, h, rightFixed v h]
  · rintro ⟨rfl, rfl⟩
    exact splice_projections side x fixed

/-- If each factor reads only its assigned side and the conditioned
coordinates, the fixed-condition product splits into two factors. -/
theorem split_conditioned_families {G : DAG n} {states : List A} (K : Kernels G states)
    (vertices : List (Fin n)) (conditioned side owner : Fin n → Bool)
    (left right : State n A)
    (agree : ∀ u, conditioned u = true → left u = right u)
    (owned : ∀ child ∈ vertices, ∀ u, Family G child u →
      conditioned u = false → side u = owner child) :
    density K vertices (splice side left right) =
      density K (vertices.filter owner) left *
        density K (vertices.filter (fun v => !owner v)) right := by
  unfold density
  rw [product_partition vertices owner]
  congr 1
  · apply product_congr
    intro child member
    obtain ⟨inVertices, which⟩ := List.mem_filter.mp member
    apply K.readsFamily
    intro u family
    cases h : conditioned u
    · simp [splice, owned child inVertices u family h, which]
    · simp [splice, agree u h]
  · apply product_congr
    intro child member
    obtain ⟨inVertices, which⟩ := List.mem_filter.mp member
    have other : owner child = false := Bool.not_eq_true' _ ▸ which
    apply K.readsFamily
    intro u family
    cases h : conditioned u
    · simp [splice, owned child inVertices u family h, other]
    · simp [splice, agree u h]

end
end OpenCausalScience.Papers.LauritzenEtAl1990.KernelElimination
