module
public import OpenCausalScience.Graph.MixedPath
public import OpenCausalScience.Graph.MixedSeparationExecutable

namespace OpenCausalScience.MixedGraph

@[expose] public section

/-- The mixed-graph arrival search returns separation exactly when no
vertex-simple, edge-marked active path joins the query sets. -/
theorem m_separated_iff_no_path {n : Nat} (G : MixedGraph n)
    (left right conditioning : Fin n → Bool)
    (leftOutside : ∀ v, left v = true → conditioning v = false)
    (leftRightDisjoint : ∀ v, left v = true → right v = false) :
    G.mSeparated left right conditioning = true ↔ ¬ G.PathConnected left right conditioning :=
  (G.m_separated_iff_no_walk left right conditioning).trans
    (not_congr (G.walkConnected_iff_pathConnected left right conditioning leftOutside leftRightDisjoint))

end
end OpenCausalScience.MixedGraph
