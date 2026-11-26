module
public import OpenCausalScience.Papers.ElahiEtAl2024.SplitNetwork

/-! Elahi et al. (2024), Figure 2(a). The original query has treatment
{v₂, v₃}, outcome y, and S = {w, y}. We check the §4 proxy cut on the
original graph after removing arrows from Pa(S) = {v₂, v₃}. -/

@[expose] public section

namespace OpenCausalScience.Papers.ElahiEtAl2024.Figure2A

open SplitNetwork
open MixedGraph (Reach)

inductive Vertex
  | v1 | v2 | v3 | w | y | u12 | u13 | u1w
  deriving DecidableEq

open Vertex

def directed : Vertex → Vertex → Prop
  | .v1, .v3 | .v3, .w | .w, .y | .v2, .y => True
  | _, _ => False

/-- One latent root for each of v₁ ↔ v₂, v₁ ↔ v₃ and v₁ ↔ w. -/
def latent : Vertex → Vertex → Prop
  | .u12, .v1 | .u12, .v2 | .u13, .v1 | .u13, .v3 | .u1w, .v1 | .u1w, .w => True
  | _, _ => False

def treatment : Vertex → Prop
  | .v2 | .v3 => True
  | _ => False

def target : Vertex → Prop
  | .w | .y => True
  | _ => False

def experiment (vertex : Vertex) : Prop := vertex = .v1

def noRemoval (_vertex : Vertex) : Prop := False

/-- Delete all directed arrows out of the treatment and expand the
three bidirected edges into latent roots. -/
def cutInput (a b : Vertex) : Prop :=
  (directed a b ∧ ¬ treatment a) ∨ latent a b

def treatmentSide : Vertex → Bool
  | .v1 | .v2 | .v3 | .u12 | .u13 => true
  | _ => false

/-- After intervening on v₁, no adjustment is needed in the cut criterion. -/
theorem proxy_without_adjustment :
    IsMoralCut cutInput treatment target experiment noRemoval := by
  apply moral_cut_of_arrow_partition _ _ _ _ _ treatmentSide
  · intro v selected
    cases v <;> simp [treatment, treatmentSide] at selected ⊢
  · intro v selected
    cases v <;> simp [target, treatmentSide] at selected ⊢
  · intro a b retained
    cases a <;> cases b <;>
      simp [remainingArrow, cutInput, directed, treatment, latent, experiment, treatmentSide]
        at retained ⊢

theorem proxy_split_cut :
    IsSplitCut cutInput treatment target experiment noRemoval :=
  (split_cut_iff_moral_cut ..).mpr proxy_without_adjustment

private theorem excluded {adjust : Vertex → Prop}
    (allowed : ∀ a, adjust a → a = v1) {a : Vertex} (other : a ≠ v1) :
    ¬ adjust a :=
  fun h => other (allowed a h)

/-- In the observational case the latent-only interior path
v₂ – u₁₂ – u₁w – w avoids every eligible adjustment set. -/
theorem observation_has_unblocked_route {adjust : Vertex → Prop}
    (allowed : ∀ a, adjust a → a = v1) :
    Reach (MoralEdge cutInput noRemoval adjust) v2 w := by
  have e₁ : MoralEdge cutInput noRemoval adjust v2 u12 := by
    exact ⟨excluded allowed (by decide), excluded allowed (by decide), by decide,
      .inr (.inl ⟨.inr trivial, fun h => h⟩)⟩
  have e₂ : MoralEdge cutInput noRemoval adjust u12 u1w := by
    exact ⟨excluded allowed (by decide), excluded allowed (by decide), by decide,
      .inr (.inr ⟨v1, ⟨.inr trivial, fun h => h⟩, ⟨.inr trivial, fun h => h⟩⟩)⟩
  have e₃ : MoralEdge cutInput noRemoval adjust u1w w := by
    exact ⟨excluded allowed (by decide), excluded allowed (by decide), by decide,
      .inl ⟨.inr trivial, fun h => h⟩⟩
  exact .extend (.extend (.extend (.refl _) e₁) e₂) e₃

theorem no_observational_adjustment {adjust : Vertex → Prop}
    (allowed : ∀ a, adjust a → a = v1) :
    ¬ IsSplitCut cutInput treatment target noRemoval adjust := by
  intro splitCut
  exact (split_cut_iff_moral_cut ..).mp splitCut v2 w trivial trivial
    (observation_has_unblocked_route allowed)

end OpenCausalScience.Papers.ElahiEtAl2024.Figure2A
