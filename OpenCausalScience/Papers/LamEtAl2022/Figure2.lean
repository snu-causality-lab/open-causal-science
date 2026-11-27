module
public import OpenCausalScience.Discovery.OrderDAG
public import OpenCausalScience.Papers.LamEtAl2022.Tuck
public import OpenCausalScience.Papers.LamEtAl2022.Search

/-! The three-variable oracle example in Figure 2. For the distinct
endpoint queries used by (RU), only variables 1 and 2 are marginally
independent. Their conditional independence fails given vertex 3. -/

namespace OpenCausalScience.Papers.LamEtAl2022.Figure2

@[expose] public section

abbrev Vertex := Fin 3

def one : Vertex := 0
def two : Vertex := 1
def three : Vertex := 2

def vertices : List Vertex := List.finRange 3

def independent : Discovery.CIOracle 3 := fun u v condition =>
  vertices.all (fun w => !condition w) && ((u == one && v == two) || (u == two && v == one))

/-- Formula (RU) in Section 3, applied to the Figure 2 CI oracle. -/
def induced (order : List Vertex) : DAG 3 := Discovery.orderDAG order.idxOf independent

def arrow (order : List Vertex) : Vertex → Vertex → Bool := (induced order).edge

def orderedPairs : List (Vertex × Vertex) :=
  vertices.flatMap fun u => vertices.map fun v => (u, v)

def graphKey (order : List Vertex) : List (Vertex × Vertex) :=
  orderedPairs.filter fun (u, v) => arrow order u v

def size (order : List Vertex) : Nat := (graphKey order).length

def covered (order : List Vertex) (u v : Vertex) : Bool :=
  arrow order u v && vertices.all fun p =>
    p == u || p == v || arrow order p u == arrow order p v

def ancestor (order : List Vertex) (v u : Vertex) : Bool :=
  arrow order u v || vertices.any fun p => arrow order u p && arrow order p v

def coveredTuck (order : List Vertex) (u v : Vertex) : Option (List Vertex) :=
  if covered order u v then
    (OrderSplit.fromOrder? order u v).map fun s => s.tuck true (ancestor order v)
  else none

def coveredMoves (order : List Vertex) : List (List Vertex) :=
  orderedPairs.filterMap fun (u, v) => coveredTuck order u v

def π₁ : List Vertex := [three, one, two]
def π₂ : List Vertex := [one, three, two]
def π₃ : List Vertex := [one, two, three]

theorem edge_sets : graphKey π₁ = [(one, two), (three, one), (three, two)] ∧
    graphKey π₂ = [(one, two), (one, three), (three, two)] ∧
    graphKey π₃ = [(one, three), (two, three)] := by decide +kernel

theorem covered_tuck_trace :
    coveredTuck π₁ three one = some π₂ ∧ coveredTuck π₂ three two = some π₃ ∧
      size π₁ = 3 ∧ size π₂ = 3 ∧ size π₃ = 2 := by decide +kernel

theorem depth_two_needed :
    Search.firstImprovement coveredMoves size graphKey 1 [graphKey π₁] π₁ = none ∧
      Search.firstImprovement coveredMoves size graphKey 2 [graphKey π₁] π₁ = some π₃ := by
  decide +kernel

def secondDAG : DAG 3 := induced π₂

def reversal : DAG 3 :=
  Chickering1995.CoveredReversal.Reversal.flip secondDAG three two
    (by decide +kernel) (by decide +kernel)

/-- Figure 2 realizes strict inequality in Lemma B.8(c). A covered
reversal alone keeps the edge count, and reinducing the DAG removes
an edge. -/
theorem edge_count_after_reversal :
    (orderedPairs.filter fun (u, v) => reversal.edge u v).length = size π₂ ∧
      size π₃ < (orderedPairs.filter fun (u, v) => reversal.edge u v).length := by
  decide +kernel

end

end OpenCausalScience.Papers.LamEtAl2022.Figure2
