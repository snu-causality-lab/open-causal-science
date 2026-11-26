module
public import OpenCausalScience.Graph.MixedSeparationExecutable

/-! # Anterior closure in a mixed graph

Follow directed edges backwards and undirected edges in either direction,
as in the anterior restriction used before CGA's separator search.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n}

/-- A vertex is anterior to a seed if it has a path of edges with a tail
at each departure toward the seed. The zero-length path is allowed. -/
inductive AnteriorOf (G : MixedGraph n) (seeds : Fin n → Bool) : Fin n → Prop
  | seed {v} : seeds v = true → AnteriorOf G seeds v
  | step {u v mark} : G.edge u false v mark = true →
      AnteriorOf G seeds v → AnteriorOf G seeds u

theorem AnteriorOf.closed {S : Fin n → Bool} {T : Fin n → Prop} {v : Fin n}
    (path : G.AnteriorOf S v) (seeds : ∀ w, S w = true → T w)
    (step : ∀ {u w mark}, G.edge u false w mark = true → T w → T u) : T v := by
  induction path with
  | seed present => exact seeds _ present
  | step edge _ ih => exact step edge ih

theorem AnteriorOf.mono {S T : Fin n → Bool} {v : Fin n}
    (path : G.AnteriorOf S v) (sub : ∀ w, S w = true → T w = true) :
    G.AnteriorOf T v :=
  path.closed (fun w mem => .seed (sub w mem)) AnteriorOf.step

theorem AnteriorOf.trans {S T : Fin n → Bool} {v : Fin n}
    (path : G.AnteriorOf S v) (sub : ∀ w, S w = true → G.AnteriorOf T w) :
    G.AnteriorOf T v :=
  path.closed sub AnteriorOf.step

theorem AncestorOf.to_anterior {S : Fin n → Bool} {v : Fin n}
    (path : G.AncestorOf S v) : G.AnteriorOf S v := by
  induction path with
  | conditioned mem => exact .seed mem
  | parent edge _ ih => exact .step edge ih

/-- An anterior path starting at a vertex with an incoming arrowhead is
directed. Its first edge cannot be undirected, and each step then supplies
an incoming arrowhead at the next vertex. -/
theorem AnteriorOf.to_ancestor {S : Fin n → Bool} {v : Fin n}
    (path : G.AnteriorOf S v)
    (incident : ∃ w mark, G.edge v true w mark = true) : G.AncestorOf S v := by
  induction path with
  | seed present => exact .conditioned present
  | @step u v mark edge _ ih =>
    cases mark with
    | false =>
      obtain ⟨w, mark, arrow⟩ := incident
      rw [G.no_arrow_of_undirected edge] at arrow
      contradiction
    | true =>
      exact .parent edge (ih ⟨u, false, (G.symmetric _ _ _ _).symm.trans edge⟩)

theorem AnteriorOf.union {S T : Fin n → Bool} {v : Fin n}
    (path : G.AnteriorOf (fun w => S w || T w) v) :
    G.AnteriorOf S v ∨ G.AnteriorOf T v := by
  induction path with
  | seed mem => exact (Bool.or_eq_true_iff.mp mem).imp AnteriorOf.seed AnteriorOf.seed
  | step edge _ ih => exact ih.imp (AnteriorOf.step edge) (AnteriorOf.step edge)

theorem AncestorOf.union {S T : Fin n → Bool} {v : Fin n}
    (path : G.AncestorOf (fun w => S w || T w) v) :
    G.AncestorOf S v ∨ G.AncestorOf T v := by
  induction path with
  | conditioned mem =>
    exact (Bool.or_eq_true_iff.mp mem).imp AncestorOf.conditioned AncestorOf.conditioned
  | parent edge _ ih => exact ih.imp (AncestorOf.parent edge) (AncestorOf.parent edge)

def anteriorNext (G : MixedGraph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun u => G.edge u false v false || G.edge u false v true

/-- The reflexive anterior closure, found by scanning backwards from
the seeds. -/
def anterior (G : MixedGraph n) (seeds : Fin n → Bool) : Fin n → Bool :=
  let vertices := List.finRange n
  let visited := exploreStack (anteriorNext G) vertices (vertices.filter seeds)
  fun v => visited.contains v

theorem anterior_iff (G : MixedGraph n) (seeds : Fin n → Bool) (v : Fin n) :
    G.anterior seeds v = true ↔ G.AnteriorOf seeds v := by
  have neighbors (u w : Fin n) :
      w ∈ anteriorNext G u ↔ ∃ mark, G.edge w false u mark = true := by
    simp only [anteriorNext, List.mem_filter, List.mem_finRange, true_and,
      Bool.or_eq_true_iff]
    exact ⟨fun h => h.elim (⟨false, ·⟩) (⟨true, ·⟩),
      fun ⟨mark, h⟩ => by cases mark <;> simp_all⟩
  simp only [anterior, List.contains_iff_mem, mem_exploreStack_iff List.mem_finRange,
    List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨s, seed, path⟩
    induction path with
    | refl => exact .seed seed
    | extend _ moved ih =>
      obtain ⟨_, edge⟩ := (neighbors _ _).mp moved
      exact .step edge ih
  · intro path
    induction path with
    | seed present => exact ⟨_, present, .refl _⟩
    | step edge _ ih =>
      obtain ⟨s, present, reach⟩ := ih
      exact ⟨s, present, .extend reach ((neighbors _ _).mpr ⟨_, edge⟩)⟩

end
end OpenCausalScience.MixedGraph
