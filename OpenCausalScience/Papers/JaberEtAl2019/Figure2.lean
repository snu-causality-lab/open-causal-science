module
public import Std

/-! # The Figure 2 query decomposition

Jaber, Zhang and Bareinboim (2019), Figure 2(a), Corollary 1, and
Algorithm 1. Compute the three regions for the seed Y₃ from the PAG,
including its visible edges, and check the recursive removals. The
probability calculation assumes the district products in Equation (5).
Source: https://proceedings.mlr.press/v97/jaber19a/jaber19a.pdf#page=5
-/

namespace OpenCausalScience.Papers.JaberEtAl2019.Figure2

@[expose] public section

inductive Vertex
  | x₁ | x₂ | y₁ | y₂ | y₃ | y₄ | y₅
  deriving DecidableEq, BEq

inductive Mark
  | tail | arrow | circle
  deriving DecidableEq, BEq

def vertices : List Vertex := [.x₁, .x₂, .y₁, .y₂, .y₃, .y₄, .y₅]

def outcome : List Vertex := [.y₁, .y₂, .y₃, .y₄, .y₅]

/-- One entry per edge from the published drawing. -/
def markedEdge : Vertex → Vertex → Option (Mark × Mark)
  | .x₁, .x₂ | .x₁, .y₃ | .x₂, .y₁ | .y₂, .y₃ => some (.arrow, .arrow)
  | .x₁, .y₁ | .x₂, .y₂ => some (.tail, .arrow)
  | .y₄, .y₃ | .y₅, .y₁ => some (.circle, .arrow)
  | .y₄, .y₅ => some (.circle, .circle)
  | _, _ => none

def markAt (u v : Vertex) : Option Mark :=
  (markedEdge u v).map Prod.fst <|> (markedEdge v u).map Prod.snd

def visible (u v : Vertex) : Bool :=
  match u, v with
  | .x₁, .y₁ | .y₁, .x₁ | .x₂, .y₂ | .y₂, .x₂ => true
  | _, _ => false

def simplePath (current : List Vertex) (uses : Vertex → Vertex → Bool)
    (internal : Vertex → Vertex → Vertex → Bool) (target : Vertex) :
    Nat → Option Vertex → Vertex → List Vertex → Bool
  | 0, _, atVertex, _ => atVertex == target
  | fuel + 1, previous, atVertex, visited =>
    atVertex == target || current.any (fun next =>
      next != atVertex && !visited.contains next && uses atVertex next &&
        (previous.map (fun prev => internal prev atVertex next)).getD true &&
        simplePath current uses internal target fuel (some atVertex) next (atVertex :: visited))

/-- Definition 4, testing simple paths on the induced sub-PAG. -/
def pcConnected (current : List Vertex) (u v : Vertex) : Bool :=
  current.contains u && current.contains v &&
    simplePath current
      (fun a b => (markAt a b).isSome && !visible a b)
      (fun prev mid next => markAt mid prev == some .arrow && markAt mid next == some .arrow)
      v current.length none u []

def sameBucket (current : List Vertex) (u v : Vertex) : Bool :=
  current.contains u && current.contains v &&
    simplePath current
      (fun a b => markAt a b == some .circle && markAt b a == some .circle)
      (fun _ _ _ => true) v current.length none u []

def region (current seed : List Vertex) : List Vertex :=
  current.filter fun v => current.any fun u =>
    sameBucket current u v && seed.any (fun s => pcConnected current s u)

def firstRegion : List Vertex := region outcome [.y₃]
def secondRegion : List Vertex := region outcome (outcome.filter (!firstRegion.contains ·))
def overlap : List Vertex := firstRegion.filter secondRegion.contains

def possibleChild (parent child : Vertex) : Bool :=
  markAt parent child == some .tail || markAt parent child == some .circle

def removable (current target bucket : List Vertex) : Bool :=
  bucket.all (fun v => !target.contains v) &&
    bucket.all (fun z => current.all fun child =>
      bucket.contains child || !(possibleChild z child && pcConnected current z child))

def bucketAt (current : List Vertex) (root : Vertex) : List Vertex :=
  current.filter (sameBucket current root)

def removalPlan (target : List Vertex) : Nat → List Vertex → Option (List (List Vertex))
  | 0, current => if current == target then some [] else none
  | fuel + 1, current =>
    if current == target then some [] else
      match (current.map (bucketAt current)).find? (removable current target) with
      | none => none
      | some bucket =>
        (removalPlan target fuel (current.filter (!bucket.contains ·))).map (bucket :: ·)

theorem initial_bucket_removals_blocked :
    removable vertices outcome [.x₁] = false ∧
      removable vertices outcome [.x₂] = false := by decide +kernel

theorem corollary_regions :
    firstRegion = [.y₂, .y₃, .y₄, .y₅] ∧
      secondRegion = [.y₁, .y₄, .y₅] ∧ overlap = [.y₄, .y₅] := by decide +kernel

theorem recursive_bucket_removals :
    removalPlan firstRegion vertices.length vertices = some [[.y₁], [.x₁], [.x₂]] ∧
      removalPlan secondRegion vertices.length vertices = some [[.y₂], [.x₂], [.x₁], [.y₃]] ∧
      removalPlan overlap vertices.length vertices = some [[.y₁], [.x₁], [.x₂], [.y₂], [.y₃]] := by
  decide +kernel

/-- The bidirected edges among the outcomes in the two causal diagrams
shown in Figure 2(b–c). The directed arrows do not enter the district test. -/
inductive Representative
  | figure2b | figure2c

def outcomeSpouse (diagram : Representative) (u v : Vertex) : Bool :=
  match u, v with
  | .y₂, .y₃ | .y₃, .y₂ => true
  | .y₄, .y₅ | .y₅, .y₄ => match diagram with
    | .figure2b => true
    | .figure2c => false
  | .y₃, .y₄ | .y₄, .y₃ => match diagram with
    | .figure2b => false
    | .figure2c => true
  | _, _ => false

def district (diagram : Representative) (current : List Vertex) (root : Vertex) : List Vertex :=
  current.filter fun v =>
    simplePath current (outcomeSpouse diagram) (fun _ _ _ => true) v current.length none root []

/-- The district containing Y₃ changes between the drawings, so the
district split used in Equation (3) cannot be read directly from the PAG. -/
theorem districts_differ_across_representatives :
    district .figure2b outcome .y₃ = [.y₂, .y₃] ∧
      district .figure2b outcome .y₄ = [.y₄, .y₅] ∧
      district .figure2c outcome .y₃ = [.y₂, .y₃, .y₄] ∧
      district .figure2c outcome .y₅ = [.y₅] := by decide +kernel

/-- Corollary 1 after the four district products used in Equation (5)
have been supplied at the same cell. The overlap must be supported. -/
theorem region_quotient_of_district_products
    (whole first second intersection leftOnly rightOnly sharedLeft sharedRight : Rat)
    (wholeFactors : whole = leftOnly * rightOnly)
    (firstFactors : first = leftOnly * sharedRight)
    (secondFactors : second = rightOnly * sharedLeft)
    (intersectionFactors : intersection = sharedLeft * sharedRight)
    (support : intersection ≠ 0) :
    whole = first * second / intersection := by
  rw [wholeFactors, firstFactors, secondFactors, intersectionFactors] at ⊢
  rw [intersectionFactors] at support
  have reorder : (leftOnly * sharedRight) * (rightOnly * sharedLeft) =
      (leftOnly * rightOnly) * (sharedLeft * sharedRight) := by
    rw [Rat.mul_assoc leftOnly sharedRight, Rat.mul_comm sharedRight (rightOnly * sharedLeft),
      Rat.mul_assoc rightOnly sharedLeft, ← Rat.mul_assoc leftOnly rightOnly]
  rw [reorder, Rat.mul_div_cancel support]

/-- Combining the three recursively obtained cells in Equations (11)–(13)
gives Equation (14), given the district products. -/
theorem figure2_expression (q : List Vertex → Rat)
    (pLeft pRight pShared leftOnly rightOnly sharedLeft sharedRight : Rat)
    (wholeFactors : q outcome = leftOnly * rightOnly)
    (leftFactors : q firstRegion = leftOnly * sharedRight)
    (rightFactors : q secondRegion = rightOnly * sharedLeft)
    (sharedFactors : q overlap = sharedLeft * sharedRight)
    (leftIdentified : q [.y₂, .y₃, .y₄, .y₅] = pLeft)
    (rightIdentified : q [.y₁, .y₄, .y₅] = pRight)
    (sharedIdentified : q [.y₄, .y₅] = pShared)
    (support : pShared ≠ 0) :
    q outcome = pLeft * pRight / pShared := by
  obtain ⟨h₁, h₂, h₃⟩ := corollary_regions
  have first : q firstRegion = pLeft := h₁ ▸ leftIdentified
  have second : q secondRegion = pRight := h₂ ▸ rightIdentified
  have common : q overlap = pShared := h₃ ▸ sharedIdentified
  rw [← first, ← second, ← common]
  exact region_quotient_of_district_products _ _ _ _ _ _ _ _ wholeFactors leftFactors rightFactors
    sharedFactors (common ▸ support)

end
end OpenCausalScience.Papers.JaberEtAl2019.Figure2
