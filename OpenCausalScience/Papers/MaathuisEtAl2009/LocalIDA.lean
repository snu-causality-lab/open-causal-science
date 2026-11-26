module
public import OpenCausalScience.Papers.AnderssonEtAl1997.Characterization

/-! # Maathuis, Kalisch and Bühlmann (2009), population IDA

The optional parents chosen at one target can be realized in the DAG
class exactly when they create no new unshielded collider at the target.
The resulting parent-set support is sufficient for any effect calculation
that only depends on the parent set. See Lemma 3.1 and Theorem 3.2.
https://stat.ethz.ch/Manuscripts/buhlmann/AOS685.pdf#page=11
-/

namespace OpenCausalScience.Papers.MaathuisEtAl2009.LocalIDA

open OpenCausalScience.Papers.AnderssonEtAl1997.Characterization
open OpenCausalScience.Papers.AnderssonEtAl1997.Condensation
open OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph
open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

def OptionalParents (G : DAG n) (target : Fin n) (chosen : Fin n → Prop) : Prop :=
  ∀ u, chosen u → Unoriented G (Compelled G) u target

def parentChoice (G : DAG n) (target : Fin n) (chosen : Fin n → Prop)
    (u : Fin n) : Prop :=
  Compelled G u target ∨ chosen u

/-- Orient the selected incident lines inward and the other lines outward.
An unshielded collider into the target must already have been present. -/
def NoNewCollider (G : DAG n) (target : Fin n) (chosen : Fin n → Prop) : Prop :=
  ∀ u v, u ≠ v → parentChoice G target chosen u → parentChoice G target chosen v →
    ¬ Adjacent G u v → UnshieldedCollider G u target v

def LocallyValid (G : DAG n) (target : Fin n) (chosen : Fin n → Prop) : Prop :=
  OptionalParents G target chosen ∧ NoNewCollider G target chosen

def HasParents (G : DAG n) (target : Fin n) (parents : Fin n → Prop) : Prop :=
  ∀ u, G.edge u target = true ↔ parents u

private theorem optional_same_component {G : DAG n} {u t : Fin n}
    (line : Unoriented G (Compelled G) u t) : label G u = label G t :=
  (essentialComponents G).label_eq_of_unoriented line

theorem no_new_collider_iff_clique {G : DAG n} {target : Fin n}
    {chosen : Fin n → Prop} (optional : OptionalParents G target chosen) :
    NoNewCollider G target chosen ↔
      ∀ u v, chosen u → chosen v → u ≠ v → Adjacent G u v := by
  classical
  constructor
  · intro valid u v hu hv distinct
    apply Classical.byContradiction
    intro missing
    have collider := valid u v distinct (.inr hu) (.inr hv) missing
    exact (optional u hu).2.1 (collider_arrows_compelled collider).1
  · intro clique u v distinct hu hv missing
    rcases hu with fixedU | inU <;> rcases hv with fixedV | inV
    · exact ⟨distinct, missing, compelled_in_base fixedU, compelled_in_base fixedV⟩
    · have fixedUV := (essentialComponents G).inherits_parents u target v fixedU
        (optional_same_component (optional v inV)).symm
      exact (missing (.inl (compelled_in_base fixedUV))).elim
    · have fixedVU := (essentialComponents G).inherits_parents v target u fixedV
        (optional_same_component (optional u inU)).symm
      exact (missing (.inr (compelled_in_base fixedVU))).elim
    · exact (missing (clique u v inU inV distinct)).elim

/-- Lemma 3.1: orienting only the incident lines gives a valid parent
set at the target precisely when a representative DAG realizes it. -/
theorem no_new_collider_iff_extension {G : DAG n} {target : Fin n}
    {chosen : Fin n → Prop} (optional : OptionalParents G target chosen) :
    NoNewCollider G target chosen ↔
      ∃ H : DAG n, SameDConnections G H ∧ HasParents H target (parentChoice G target chosen) := by
  classical
  constructor
  · intro valid
    let initial (u : Fin n) := u = target ∨ chosen u
    have within (u : Fin n) (member : initial u) : label G u = label G target := by
      rcases member with equal | inChoice
      · exact congrArg (label G) equal
      · exact optional_same_component (optional u inChoice)
    have pairwise (u v : Fin n) (hu : initial u) (hv : initial v) (distinct : u ≠ v) :
        Adjacent G u v := by
      rcases hu with equalU | inU <;> rcases hv with equalV | inV
      · exact (distinct (equalU.trans equalV.symm)).elim
      · exact equalU.symm ▸ Or.symm (optional v inV).1
      · exact equalV.symm ▸ (optional u inU).1
      · exact (no_new_collider_iff_clique optional).mp valid u v inU inV distinct
    let priority (u : Fin n) : Nat := if u = target then 1 else 0
    obtain ⟨H, extension, inside, outside⟩ :=
      extend_with_initial_clique G (label G target) initial within pairwise priority
    have same := extension_iff_same_d_connections.mp extension
    refine ⟨H, same, fun u => ⟨?_, ?_⟩⟩
    · intro edge
      rcases possible_iff.mp ⟨H, same, edge⟩ with fixed | reversible
      · exact .inl fixed
      · by_cases selected : chosen u
        · exact .inr selected
        · have different : u ≠ target := fun equal =>
            H.no_directed_cycle target (.single (equal ▸ edge))
          have out : ¬ initial u := fun member => member.elim different selected
          have line := unoriented_iff_reversible.mpr reversible
          have shape : (essentialComponents G).adjacency (label G target) target u :=
            ⟨Or.symm line.1, rfl, optional_same_component line⟩
          have backward := outside target u (.inl rfl) out shape
          exact (H.no_directed_cycle u (.extend (.single edge) backward)).elim
    · rintro (fixed | selected)
      · exact fixed H same
      · have line := optional u selected
        have different : u ≠ target := by
          intro equal
          subst u
          exact line.1.elim (fun e => G.no_directed_cycle target (.single e))
            (fun e => G.no_directed_cycle target (.single e))
        have earlier : priority u < priority target := by simp [priority, different]
        have shape : (essentialComponents G).adjacency (label G target) u target :=
          ⟨line.1, optional_same_component line, rfl⟩
        exact inside u target (.inr selected) (.inl rfl) earlier shape
  · rintro ⟨H, same, parents⟩ u v distinct hu hv missing
    apply (sameUnshieldedColliders_of_sameDConnections same u target v).mpr
    exact ⟨distinct, fun adjacent => missing ((sameSkeleton_of_sameDConnections same u v).mpr
      adjacent), (parents u).mpr hu, (parents v).mpr hv⟩

theorem parents_of_extension_are_local {G H : DAG n} {target : Fin n}
    (same : SameDConnections G H) :
    ∃ chosen : Fin n → Prop, LocallyValid G target chosen ∧
      HasParents H target (parentChoice G target chosen) := by
  let chosen (u : Fin n) := Unoriented G (Compelled G) u target ∧ H.edge u target = true
  have optional : OptionalParents G target chosen := fun _ hu => hu.1
  have parents : HasParents H target (parentChoice G target chosen) := by
    intro u
    constructor
    · intro edge
      rcases possible_iff.mp ⟨H, same, edge⟩ with fixed | reversible
      · exact .inl fixed
      · exact .inr ⟨unoriented_iff_reversible.mpr reversible, edge⟩
    · rintro (fixed | hu)
      · exact fixed H same
      · exact hu.2
  exact ⟨chosen, ⟨optional, (no_new_collider_iff_extension optional).mpr ⟨H, same, parents⟩⟩,
    parents⟩

/-- Theorem 3.2's set-level step, for any readout from the parent set.
The causal interpretation of the readout requires its own model result. -/
theorem parent_readout_support_iff {G : DAG n} {target : Fin n} {α : Type}
    (readout : (Fin n → Prop) → α) (value : α) :
    (∃ chosen, LocallyValid G target chosen ∧
      readout (parentChoice G target chosen) = value) ↔
    ∃ H : DAG n, SameDConnections G H ∧ readout (fun u => H.edge u target = true) = value := by
  have sets_equal {H : DAG n} {chosen : Fin n → Prop}
      (parents : HasParents H target (parentChoice G target chosen)) :
      (fun u => H.edge u target = true) = parentChoice G target chosen :=
    funext fun u => propext (parents u)
  constructor
  · rintro ⟨chosen, localValid, observed⟩
    obtain ⟨H, same, parents⟩ := (no_new_collider_iff_extension localValid.1).mp localValid.2
    exact ⟨H, same, (sets_equal parents).symm ▸ observed⟩
  · rintro ⟨H, same, observed⟩
    obtain ⟨chosen, localValid, parents⟩ := parents_of_extension_are_local (target := target) same
    exact ⟨chosen, localValid, sets_equal parents ▸ observed⟩

end
end OpenCausalScience.Papers.MaathuisEtAl2009.LocalIDA
