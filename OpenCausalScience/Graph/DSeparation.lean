module
public import OpenCausalScience.Graph.DAG

namespace OpenCausalScience.DAG

@[expose] public section

variable {n : Nat}

/-- Close the conditioning set under parents. Each round adds all immediate
parents of vertices already found. A directed path in a DAG cannot repeat a
vertex, so `n` rounds suffice to include all ancestors. -/
def conditioningAncestors (G : DAG n) (conditioned : List (Fin n)) : List (Fin n) :=
  let vertices := List.finRange n
  let parentsStep (known : List (Fin n)) :=
    vertices.filter fun u => known.contains u || known.any (G.edge u)
  (List.range n).foldl (fun known _ => parentsStep known) conditioned

/-- Extend a path by an adjacent, unvisited vertex. Extending the path fixes
the two edges at `current`, so this is when its interior-vertex rule is checked.
The first and last vertices have no interior-vertex rule. The caller supplies
the ancestral closure as `activated` and excludes the vertices already on the
path from `unvisited`. Use `dSeparated` to initialize a complete query. -/
def searchActivePath (G : DAG n) (target : Fin n)
    (conditioned activated : List (Fin n)) :
    Nat → Option (Fin n) → Fin n → List (Fin n) → Bool
  | 0, _, _, _ => false
  | fuel + 1, previous, current, unvisited =>
    if current == target then true
    else unvisited.any fun next =>
      (G.edge current next || G.edge next current) &&
      (match previous with
        | none => true
        | some prev =>
          if G.edge prev current && G.edge next current then
            activated.contains current
          else
            !(conditioned.contains current)) &&
      searchActivePath G target conditioned activated fuel (some current) next
        (unvisited.filter (· != next))

/-- Check d-separation of two distinct vertices in a finite DAG. Each collider
on an active simple path is conditioned on or has a conditioned descendant.
Other interior vertices must lie outside the conditioning set. The result is
`none` if the endpoints coincide or an endpoint is conditioned on. Otherwise
`some true` means there is no active simple path. The conditioning list is
interpreted as a set. -/
def dSeparated (G : DAG n) (x y : Fin n) (conditioned : List (Fin n)) : Option Bool :=
  if x == y || conditioned.contains x || conditioned.contains y then
    none
  else
    let activated := conditioningAncestors G conditioned
    let unvisited := (List.finRange n).filter (· != x)
    -- A simple path can visit at most `n` vertices, including its endpoints.
    some (!(searchActivePath G y conditioned activated n none x unvisited))

end

end OpenCausalScience.DAG
