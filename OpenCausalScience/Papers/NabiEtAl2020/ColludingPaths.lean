module
public import OpenCausalScience.Graph.MixedGraph

/-! Nabi, Bhattacharya and Shpitser (2020), §6. A colluding path has an
arrowhead on both sides of every interior vertex and avoids deterministic
proxy vertices. Between two successive interior vertices the same edge must
supply both arrowheads. -/

@[expose] public section

namespace OpenCausalScience.Papers.NabiEtAl2020.ColludingPaths

variable {n : Nat}

/-- The current vertex is an interior collider, with its incoming arrowhead
already supplied by the preceding edge. The list starts after that vertex. -/
inductive ColliderTail (G : MixedGraph n) (admissible : Fin n → Prop)
    (target : Fin n) : Fin n → List (Fin n) → Prop
  | finish {u mark} :
      admissible u → G.edge u true target mark = true → ColliderTail G admissible target u [target]
  | next {u v rest} :
      admissible u → G.edge u true v true = true → ColliderTail G admissible target v rest →
      ColliderTail G admissible target u (v :: rest)

/-- A path through candidate interior vertices. The initial vertex is
omitted from the list, whereas the final vertex is included unless the
path has no edges. -/
inductive InteriorChain (G : MixedGraph n) (admissible : Fin n → Prop) :
    Fin n → List (Fin n) → Fin n → Prop
  | zero {u} : admissible u → InteriorChain G admissible u [] u
  | next {u v tail w} :
      admissible u → G.edge u true v true = true → InteriorChain G admissible v tail w →
      InteriorChain G admissible u (v :: tail) w

theorem collider_tail_iff_chain {G : MixedGraph n} {allowed : Fin n → Prop}
    {start indicator : Fin n} {path : List (Fin n)} :
    ColliderTail G allowed indicator start path ↔
      ∃ interior last mark, path = interior ++ [indicator] ∧
        InteriorChain G allowed start interior last ∧ G.edge last true indicator mark = true := by
  constructor
  · intro walk
    induction walk with
    | finish allowed edge => exact ⟨[], _, _, rfl, .zero allowed, edge⟩
    | next allowed edge _ ih =>
        obtain ⟨interior, last, mark, path, chain, endpoint⟩ := ih
        exact ⟨_ :: interior, last, mark, congrArg (_ :: ·) path, .next allowed edge chain, endpoint⟩
  · rintro ⟨interior, last, mark, rfl, chain, endpoint⟩
    induction chain with
    | zero allowed => exact .finish allowed endpoint
    | next allowed edge _ ih => exact .next allowed edge (ih endpoint)

/-- A direct edge qualifies, and a longer path has only non-proxy colliders
as interior vertices. Individual marks are attached to edges. -/
def ColludingPath (G : MixedGraph n) (allowed : Fin n → Prop)
    (trueValue indicator : Fin n) (path : List (Fin n)) : Prop :=
  path.Nodup ∧
    ((path = [trueValue, indicator] ∧ ∃ m k, G.edge trueValue m indicator k = true) ∨
      ∃ first rest mark, path = trueValue :: first :: rest ∧ G.edge trueValue mark first true = true ∧
        ColliderTail G allowed indicator first rest)

theorem colluding_path_iff_bidirected_interior {G : MixedGraph n} {allowed : Fin n → Prop}
    {trueValue indicator : Fin n} {path : List (Fin n)} :
    ColludingPath G allowed trueValue indicator path ↔ path.Nodup ∧
      ((path = [trueValue, indicator] ∧ ∃ m k, G.edge trueValue m indicator k = true) ∨
        ∃ first interior last m k, path = trueValue :: first :: (interior ++ [indicator]) ∧
          G.edge trueValue m first true = true ∧ InteriorChain G allowed first interior last ∧
          G.edge last true indicator k = true) := by
  constructor
  · rintro ⟨unique, direct | ⟨first, rest, mark, path, edge, tail⟩⟩
    · exact ⟨unique, .inl direct⟩
    · obtain ⟨inner, last, exitMark, restEq, chain, exitEdge⟩ := collider_tail_iff_chain.mp tail
      exact ⟨unique, .inr ⟨first, inner, last, mark, exitMark,
        path.trans (congrArg (fun xs => trueValue :: first :: xs) restEq), edge, chain, exitEdge⟩⟩
  · rintro ⟨unique, direct | ⟨first, inner, last, mark, exitMark, path, edge, chain, exitEdge⟩⟩
    · exact ⟨unique, .inl direct⟩
    · exact ⟨unique, .inr ⟨first, inner ++ [indicator], mark, path, edge,
        collider_tail_iff_chain.mpr ⟨inner, last, exitMark, rfl, chain, exitEdge⟩⟩⟩

end OpenCausalScience.Papers.NabiEtAl2020.ColludingPaths
