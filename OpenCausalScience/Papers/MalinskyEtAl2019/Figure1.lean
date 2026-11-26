module
public import OpenCausalScience.Graph.MixedSeparationExecutable
public import OpenCausalScience.Papers.Shpitser2013.RecantingDistrict
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # Conditional path-specific effects in Figure 1

The two source graphs differ in the relationship between the evidence
and mediator. The treatment copies in the SWIG can take different
values, but fixing the copies and attempting to exchange the evidence
never removes its bidirected edge to the outcome. The recanting
criterion nevertheless accepts a different set of reduced joint
queries in the two panels.
Source: https://proceedings.mlr.press/v89/malinsky19b/malinsky19b.pdf#page=3
-/

namespace OpenCausalScience.Papers.MalinskyEtAl2019.Figure1

open TianPearl2003.IdentifyRecurrence (Vertices district)
open Shpitser2013.RecantingDistrict (ancestralRegion recants)
open TianPearl2003.AncestralMarginal (Setting evaluate mass)

@[expose] public section

def marked {n : Nat} (arrows spouses : List (Fin n × Fin n))
    (u : Fin n) (atU : Bool) (v : Fin n) (atV : Bool) : Bool :=
  u != v && match atU, atV with
  | false, false => false
  | false, true => arrows.contains (u, v)
  | true, false => arrows.contains (v, u)
  | true, true => spouses.contains (u, v) || spouses.contains (v, u)

def graphFrom {n : Nat} (arrows spouses : List (Fin n × Fin n)) : MixedGraph n where
  edge := marked arrows spouses
  symmetric u h v k := by
    have unequal : (u != v) = (v != u) := congrArg (! ·) (BEq.comm (a := u) (b := v))
    cases h <;> cases k <;> simp [marked, unequal, Bool.or_comm]
  loop_free u h k := by simp [marked]
  no_arrow_of_undirected := by simp [marked]

abbrev c : Fin 4 := 0
abbrev a : Fin 4 := 1
abbrev m : Fin 4 := 2
abbrev y : Fin 4 := 3

def firstGraph : MixedGraph 4 := graphFrom [(c, a), (a, m), (m, y), (a, y)] [(c, m), (c, y)]
def secondGraph : MixedGraph 4 := graphFrom [(c, a), (a, m), (m, y), (a, y), (c, m)] [(c, y)]

/-- The path through `M` uses the baseline treatment. The direct path
uses the active treatment. Recanting is symmetric in the two labels. -/
def throughMediator (source first : Fin 4) (later : List (Fin 4)) : Bool :=
  source == a && first == m && later == [y]

theorem ancestral_and_district_trace :
    ancestralRegion firstGraph [a] [y] = [m, y] ∧
    ancestralRegion firstGraph [a] [c, y] = [c, m, y] ∧
    district firstGraph [c, m, y] m = [c, m, y] ∧
    ancestralRegion secondGraph [a] [c, y] = [c, m, y] ∧
    district secondGraph [c, m, y] m = [m] ∧
    district secondGraph [c, m, y] y = [c, y] := by decide +kernel

theorem recanting_trace :
    recants firstGraph [a] [y] throughMediator = false ∧
    recants firstGraph [a] [c, y] throughMediator = true ∧
    recants secondGraph [a] [y] throughMediator = false ∧
    recants secondGraph [a] [c, y] throughMediator = false := by decide +kernel

abbrev ec : Fin 6 := 0
abbrev ea : Fin 6 := 1
abbrev am : Fin 6 := 2
abbrev ay : Fin 6 := 3
abbrev em : Fin 6 := 4
abbrev ey : Fin 6 := 5

def extendedArrows (secondPanel : Bool) : List (Fin 6 × Fin 6) :=
  [(ec, ea), (ea, am), (ea, ay), (am, em), (ay, ey), (em, ey)] ++
    if secondPanel then [(ec, em)] else []

def extendedSpouses (secondPanel : Bool) : List (Fin 6 × Fin 6) :=
  [(ec, ey)] ++ if secondPanel then [] else [(ec, em)]

/-- For the first PS-IDC exchange test, both treatment copies are
fixed and outgoing arrows of the candidate exchange `C` are removed.
The split random half of `C` remains incident to its bidirected edges. -/
def exchangeGraph (secondPanel : Bool) : MixedGraph 6 := graphFrom
  ((extendedArrows secondPanel).filter fun (u, v) => u != ec && v != am && v != ay)
  (extendedSpouses secondPanel)

theorem no_rule_two_exchange (secondPanel : Bool) :
    (exchangeGraph secondPanel).mSeparated (· == ec) (· == ey)
      (fun v => v == am || v == ay) = false := by
  apply Bool.eq_false_iff.mpr
  intro separated
  apply ((exchangeGraph secondPanel).m_separated_iff_no_walk _ _ _).mp separated
  have direct : (exchangeGraph secondPanel).edge ec true ey true = true := by
    cases secondPanel <;> rfl
  exact ⟨(ey, true), (ey, true), ⟨ec, true, rfl, direct⟩, .refl _, rfl⟩

/-! Two finite structural models for the first panel. The latent DAG
has vertices `H₁, H₂, C, A, M, Y`. The two latent roots and the three
private noises are independent fair bits. `C` is the parity of the
hidden roots. In the active treatment, natural mediator noise masks
the distinction between the two outcome mechanisms. The baseline
mediator instead carries the first latent root into the nested outcome. -/

abbrev h₁ : Fin 6 := 0
abbrev h₂ : Fin 6 := 1
abbrev fc : Fin 6 := 2
abbrev fa : Fin 6 := 3
abbrev fm : Fin 6 := 4
abbrev fy : Fin 6 := 5

def latentArrow (u v : Fin 6) : Bool :=
  ([(h₁, fc), (h₂, fc), (fc, fa), (h₁, fm), (fa, fm), (h₂, fy), (fa, fy), (fm, fy)] :
    List (Fin 6 × Fin 6)).contains (u, v)

def latentDAG : DAG 6 where
  edge := latentArrow
  rank := Fin.val
  edge_increases := by decide +kernel

structure Roots where
  firstHidden : Bool
  secondHidden : Bool
  treatmentNoise : Bool
  mediatorNoise : Bool
  outcomeNoise : Bool
  deriving DecidableEq

def bits : List Bool := [false, true]

def roots : List Roots := bits.flatMap fun first => bits.flatMap fun second =>
  bits.flatMap fun aNoise => bits.flatMap fun mNoise => bits.map fun yNoise =>
    ⟨first, second, aNoise, mNoise, yNoise⟩

def mechanism (flip : Bool) (u : Roots) (v : Fin 6) (parents : Fin 6 → Bool) : Bool :=
  match v.val with
  | 0 => u.firstHidden
  | 1 => u.secondHidden
  | 2 => parents h₁ != parents h₂
  | 3 => u.treatmentNoise
  | 4 => if parents fa then u.mediatorNoise else parents h₁
  | _ => if parents fa then (parents h₂ != parents fm) != flip else u.outcomeNoise

def regime (flip : Bool) (fixed : Setting 6) (u : Roots) : Fin 6 → Bool :=
  evaluate latentDAG (mechanism flip) u fixed

def noSetting : Setting 6 := fun _ => none
def treatment (active : Bool) : Setting 6 := fun v => if v == fa then some active else none
def withMediator (active value : Bool) : Setting 6 :=
  fun v => if v == fm then some value else treatment active v

def nestedOutcome (flip : Bool) (u : Roots) : Bool :=
  regime flip (withMediator true (regime flip (treatment false) u fm)) u fy

def observationalCell (flip cv av mv yv : Bool) : Rat :=
  mass roots (fun _ => 1 / 32) fun u =>
    let obs := regime flip noSetting u
    obs fc == cv && obs fa == av && obs fm == mv && obs fy == yv

def evidenceMass (flip cv : Bool) : Rat :=
  mass roots (fun _ => 1 / 32) fun u => regime flip noSetting u fc == cv

def conditionalJoint (flip cv yv : Bool) : Rat :=
  mass roots (fun _ => 1 / 32) fun u => regime flip noSetting u fc == cv && nestedOutcome flip u == yv

def marginalNestedMass (flip yv : Bool) : Rat :=
  mass roots (fun _ => 1 / 32) fun u => nestedOutcome flip u == yv

/-- Both models give the same positive mass in each observed cell. -/
theorem positive_observational_agreement : ∀ flip cv av mv yv : Bool,
    observationalCell flip cv av mv yv = 1 / 16 := by decide +kernel

/-- The first model agrees with the observed `C` on every listed unit;
the second model agrees with the opposite value. -/
theorem nested_unit_response : ∀ flip : Bool, ∀ u ∈ roots,
    nestedOutcome flip u = (regime flip noSetting u fc != flip) := by
  decide +kernel

theorem marginal_agreement : ∀ flip yv : Bool, marginalNestedMass flip yv = 1 / 2 := by
  decide +kernel

theorem conditional_disagreement_at_supported_evidence :
    evidenceMass false true = 1 / 2 ∧ evidenceMass true true = 1 / 2 ∧
    conditionalJoint false true true / evidenceMass false true = 1 ∧
    conditionalJoint true true true / evidenceMass true true = 0 := by decide +kernel

end
end OpenCausalScience.Papers.MalinskyEtAl2019.Figure1
