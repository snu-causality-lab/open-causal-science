module
public import OpenCausalScience.Graph.MixedGraph

/-! Elahi, Akbari, Etesami, Kiyavash and Thiran (2024), Algorithm 1,
lines 5–10 and the path correspondence in the proof of Theorem 3.

Source: https://papers.nips.cc/paper/2024/file/5bd9fbb3a5a985f80c16ddd0ec1dfc43-Paper-Conference.pdf
-/

@[expose] public section

namespace OpenCausalScience.Papers.ElahiEtAl2024.SplitNetwork

open MixedGraph (Reach)

universe u

variable {Vertex : Type u}

/-- Before taking the moral graph, delete the incoming arrows at the
intervened vertices. The input arrow relation has already been expanded
to a DAG and has no outgoing arrows from the query's parent set. -/
def remainingArrow (arrow : Vertex → Vertex → Prop) (intervene : Vertex → Prop)
    (source target : Vertex) : Prop :=
  arrow source target ∧ ¬ intervene target

/-- Each intervention or adjustment has its own copy of the vertex. -/
inductive Copy (Vertex : Type u)
  | first : Vertex → Copy Vertex
  | second : Vertex → Copy Vertex

/-- Surviving edges between the first and second copies. The intervention
gate for a vertex with incoming arrows is on its second copy. -/
def HalfEdge (arrow : Vertex → Vertex → Prop) (intervene adjust : Vertex → Prop)
    (first second : Vertex) : Prop :=
  ¬ adjust first ∧ ¬ intervene second ∧ (first = second ∨ arrow first second)

def SplitEdge (arrow : Vertex → Vertex → Prop) (intervene adjust : Vertex → Prop) :
    Copy Vertex → Copy Vertex → Prop
  | .first v, .second w | .second w, .first v => HalfEdge arrow intervene adjust v w
  | _, _ => False

/-- Adjacency in the moral graph, after blocking the adjustment vertices. -/
def MoralEdge (arrow : Vertex → Vertex → Prop) (intervene adjust : Vertex → Prop)
    (a b : Vertex) : Prop :=
  ¬ adjust a ∧ ¬ adjust b ∧ a ≠ b ∧
    (remainingArrow arrow intervene a b ∨ remainingArrow arrow intervene b a ∨
      ∃ child, remainingArrow arrow intervene a child ∧ remainingArrow arrow intervene b child)

private theorem moral_edge_to_two_edges {arrow : Vertex → Vertex → Prop}
    {intervene adjust : Vertex → Prop} {a b : Vertex}
    (edge : MoralEdge arrow intervene adjust a b) :
    ∃ child, HalfEdge arrow intervene adjust a child ∧ HalfEdge arrow intervene adjust b child := by
  rcases edge with ⟨ha, hb, _, ⟨arrow, available⟩ | ⟨arrow, available⟩ | ⟨c, ac, bc⟩⟩
  · exact ⟨b, ⟨ha, available, .inr arrow⟩, ⟨hb, available, .inl rfl⟩⟩
  · exact ⟨a, ⟨ha, available, .inl rfl⟩, ⟨hb, available, .inr arrow⟩⟩
  · exact ⟨c, ⟨ha, ac.2, .inr ac.1⟩, ⟨hb, bc.2, .inr bc.1⟩⟩

private theorem two_edges_to_moral_edge {arrow : Vertex → Vertex → Prop}
    {intervene adjust : Vertex → Prop} {a b child : Vertex}
    (ha : HalfEdge arrow intervene adjust a child) (hb : HalfEdge arrow intervene adjust b child) :
    a = b ∨ MoralEdge arrow intervene adjust a b := by
  rcases ha with ⟨openA, openChild, aEq | aArrow⟩
  · subst child
    rcases hb.2.2 with bEq | bArrow
    · exact .inl bEq.symm
    · by_cases equal : a = b
      · exact .inl equal
      · exact .inr ⟨openA, hb.1, equal, .inr (.inl ⟨bArrow, openChild⟩)⟩
  · by_cases equal : a = b
    · exact .inl equal
    · apply Or.inr
      refine ⟨openA, hb.1, equal, ?_⟩
      rcases hb.2.2 with bEq | bArrow
      · subst child
        exact .inl ⟨aArrow, openChild⟩
      · exact .inr (.inr ⟨child, ⟨aArrow, openChild⟩, ⟨bArrow, openChild⟩⟩)

private theorem expand_moral_route {arrow : Vertex → Vertex → Prop} {intervene adjust : Vertex → Prop}
    {a b : Vertex} (walk : Reach (MoralEdge arrow intervene adjust) a b) :
    Reach (SplitEdge arrow intervene adjust) (.first a) (.first b) := by
  induction walk with
  | refl => exact .refl _
  | @extend middle last _ step ih =>
      obtain ⟨child, toChild, fromChild⟩ := moral_edge_to_two_edges step
      have first : SplitEdge arrow intervene adjust (.first middle) (.second child) := toChild
      have second : SplitEdge arrow intervene adjust (.second child) (.first last) := fromChild
      exact .extend (.extend ih first) second

private theorem collapse_split_route {arrow : Vertex → Vertex → Prop}
    {intervene adjust : Vertex → Prop} {a : Vertex} {b : Copy Vertex}
    (walk : Reach (SplitEdge arrow intervene adjust) (.first a) b) :
    match b with
    | .first v => Reach (MoralEdge arrow intervene adjust) a v
    | .second c => ∃ v, Reach (MoralEdge arrow intervene adjust) a v ∧
        HalfEdge arrow intervene adjust v c := by
  induction walk with
  | refl => exact .refl _
  | @extend middle last _ edge ih =>
      cases middle with
      | first v =>
          cases last with
          | first w => exact False.elim edge
          | second c => exact ⟨v, ih, edge⟩
      | second c =>
          cases last with
          | first w =>
              obtain ⟨v, part, half⟩ := ih
              rcases two_edges_to_moral_edge half edge with equal | moral
              · exact equal ▸ part
              · exact .extend part moral
          | second d => exact False.elim edge

/-- The path correspondence of Appendix C.2. Repeated vertices in walks
do not change whether distinct cut terminals are connected. -/
theorem split_route_iff_moral_route (arrow : Vertex → Vertex → Prop)
    (intervene adjust : Vertex → Prop) (a b : Vertex) :
    Reach (SplitEdge arrow intervene adjust) (.first a) (.first b) ↔
      Reach (MoralEdge arrow intervene adjust) a b :=
  ⟨collapse_split_route, expand_moral_route⟩

def IsSplitCut (arrow : Vertex → Vertex → Prop) (left right intervene adjust : Vertex → Prop) :
    Prop :=
  ∀ a b, left a → right b → ¬ Reach (SplitEdge arrow intervene adjust) (.first a) (.first b)

def IsMoralCut (arrow : Vertex → Vertex → Prop) (left right intervene adjust : Vertex → Prop) :
    Prop :=
  ∀ a b, left a → right b → ¬ Reach (MoralEdge arrow intervene adjust) a b

theorem split_cut_iff_moral_cut (arrow : Vertex → Vertex → Prop)
    (left right intervene adjust : Vertex → Prop) :
    IsSplitCut arrow left right intervene adjust ↔ IsMoralCut arrow left right intervene adjust := by
  simp only [IsSplitCut, IsMoralCut, split_route_iff_moral_route]

/-- If every retained arrow stays on one side of a partition,
moralization also stays inside each side. -/
theorem moral_cut_of_arrow_partition (arrow : Vertex → Vertex → Prop)
    (left right intervene adjust : Vertex → Prop) (side : Vertex → Bool)
    (leftSide : ∀ v, left v → side v = true)
    (rightSide : ∀ v, right v → side v = false)
    (stays : ∀ a b, remainingArrow arrow intervene a b → side a = side b) :
    IsMoralCut arrow left right intervene adjust := by
  have moralStays {a b : Vertex} (h : MoralEdge arrow intervene adjust a b) : side a = side b := by
    rcases h with ⟨_, _, _, forward | backward | ⟨child, ac, bc⟩⟩
    · exact stays a b forward
    · exact (stays b a backward).symm
    · exact (stays a child ac).trans (stays b child bc).symm
  intro a b ha hb walk
  have sameSide : side a = side b := by
    clear hb
    induction walk with
    | refl => rfl
    | extend _ edge ih => exact ih.trans (moralStays edge)
  have impossible := (leftSide a ha).symm.trans (sameSide.trans (rightSide b hb))
  contradiction

/-- A finite cut may contain first copies of eligible adjustment variables
or second copies of eligible intervention variables. In particular, latent
vertices and designated terminals can be excluded from either side. -/
def Eligible (mayIntervene mayAdjust intervene adjust : Vertex → Prop) : Prop :=
  (∀ v, intervene v → mayIntervene v) ∧ (∀ v, adjust v → mayAdjust v)

def Minimum {Cost : Type} [LE Cost] (cost : (Vertex → Prop) → Cost)
    (feasible : (Vertex → Prop) → (Vertex → Prop) → Prop) (intervene adjust : Vertex → Prop) :
    Prop :=
  feasible intervene adjust ∧
    ∀ alternative adjustment, feasible alternative adjustment → cost intervene ≤ cost alternative

/-- With zero cost on eligible first copies and the experiment cost on
second copies, the two feasible problems have the same minimizers. -/
theorem minimum_split_cut_iff_minimum_moral_cut {Cost : Type} [LE Cost]
    (arrow : Vertex → Vertex → Prop) (left right mayIntervene mayAdjust : Vertex → Prop)
    (cost : (Vertex → Prop) → Cost) (intervene adjust : Vertex → Prop) :
    Minimum cost
      (fun I Z => Eligible mayIntervene mayAdjust I Z ∧ IsSplitCut arrow left right I Z)
      intervene adjust ↔
    Minimum cost
      (fun I Z => Eligible mayIntervene mayAdjust I Z ∧ IsMoralCut arrow left right I Z)
      intervene adjust := by
  simp only [Minimum, split_cut_iff_moral_cut]

end OpenCausalScience.Papers.ElahiEtAl2024.SplitNetwork
