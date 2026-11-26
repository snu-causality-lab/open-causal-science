module
public import OpenCausalScience.Papers.Zhang2008OrientationRules.Orientations

/-! Graphical conditions for a legitimate mark change in Zhang and
Spirtes (2005), Lemmas 1–2. The graphs here have no undirected edges.
Source: https://www.cmu.edu/dietrich/philosophy/docs/spirtes/uai05.pdf
-/

namespace OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange

open MarkedGraph
open MixedGraph (Reach)
open Zhang2008OrientationRules.Orientations

@[expose] public section

variable {n : Nat}

def NoLines (G : MarkedGraph n) : Prop :=
  ∀ u v, G.marks u v ≠ some (false, false)

def Spouse (G : MarkedGraph n) (u v : Fin n) : Prop :=
  G.marks u v = some (true, true)

/-- Only the mark at the source of a directed edge changes. -/
structure AddedHead (G H : MarkedGraph n) (a b : Fin n) : Prop where
  original : Directed G a b
  changed : Spouse H a b
  other : ∀ u v, (u ≠ a ∨ v ≠ b) → (u ≠ b ∨ v ≠ a) → H.marks u v = G.marks u v

def DirectedWithout (G : MarkedGraph n) (a b u v : Fin n) : Prop :=
  Directed G u v ∧ (u ≠ a ∨ v ≠ b)

private theorem directed_reverse_marks {G : MarkedGraph n} {a b : Fin n}
    (ab : Directed G a b) : G.marks b a = some (true, false) := by
  change G.marks a b = some (false, true) at ab
  simp [G.swap_marks a b, ab, Prod.swap]

private theorem spouse_reverse {G : MarkedGraph n} {a b : Fin n}
    (ab : Spouse G a b) : Spouse G b a := by
  change G.marks a b = some (true, true) at ab
  change G.marks b a = some (true, true)
  simp [G.swap_marks a b, ab, Prod.swap]

private theorem head_of_directed {G : MarkedGraph n} {a b : Fin n}
    (ab : Directed G a b) : G.arrowheadAt b a = true := by
  simp [arrowheadAt, directed_reverse_marks ab]

private theorem directed_distinct {G : MarkedGraph n} {a b : Fin n}
    (ab : Directed G a b) : a ≠ b := by
  rintro rfl
  simp [Directed, G.loop_free] at ab

theorem directed_iff_without {G H : MarkedGraph n} {a b : Fin n} (changeHead : AddedHead G H a b)
    (u v : Fin n) : Directed H u v ↔ DirectedWithout G a b u v := by
  by_cases uv : u = a ∧ v = b
  · obtain ⟨uIsA, vIsB⟩ := uv
    subst u
    subst v
    simp [Directed, DirectedWithout, show H.marks a b = some (true, true) from changeHead.changed]
  by_cases vu : u = b ∧ v = a
  · obtain ⟨uIsB, vIsA⟩ := vu
    subst u
    subst v
    simp [Directed, DirectedWithout, directed_reverse_marks changeHead.original,
      show H.marks b a = some (true, true) from spouse_reverse changeHead.changed]
  have first : u ≠ a ∨ v ≠ b := by
    by_cases h : u = a
    · exact Or.inr fun same => uv ⟨h, same⟩
    · exact Or.inl h
  have second : u ≠ b ∨ v ≠ a := by
    by_cases h : u = b
    · exact Or.inr fun same => vu ⟨h, same⟩
    · exact Or.inl h
  rw [DirectedWithout, and_iff_left first]
  unfold Directed
  rw [changeHead.other u v first second]

private theorem reach_map {α : Type} {R S : α → α → Prop}
    (imp : ∀ {u v}, R u v → S u v) {a b : α} (walk : Reach R a b) : Reach S a b := by
  induction walk with
  | refl => exact .refl _
  | extend _ edge ih => exact .extend ih (imp edge)

theorem arrowhead_iff_after_addition {G H : MarkedGraph n} {a b : Fin n} (edit : AddedHead G H a b)
    (u v : Fin n) : H.arrowheadAt u v = true ↔
      G.arrowheadAt u v = true ∨ (u = a ∧ v = b) := by
  by_cases uv : u = a ∧ v = b
  · obtain ⟨uIsA, vIsB⟩ := uv
    subst u
    subst v
    simp [arrowheadAt, show H.marks a b = some (true, true) from edit.changed]
  by_cases vu : u = b ∧ v = a
  · obtain ⟨uIsB, vIsA⟩ := vu
    subst u
    subst v
    simp [arrowheadAt, directed_reverse_marks edit.original,
      show H.marks b a = some (true, true) from spouse_reverse edit.changed]
  have first : u ≠ a ∨ v ≠ b := by
    by_cases h : u = a
    · exact Or.inr fun same => uv ⟨h, same⟩
    · exact Or.inl h
  have second : u ≠ b ∨ v ≠ a := by
    by_cases h : u = b
    · exact Or.inr fun same => vu ⟨h, same⟩
    · exact Or.inl h
  simp [arrowheadAt, edit.other u v first second, uv]

/-- The ancestry requirement (t1) is necessary and sufficient for the
edited graph to be ancestral. The walk uses the original directed edges
other than the edited one. -/
theorem ancestral_iff_no_alternate_path {G H : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (ancestral : AncestralMarks G) (edit : AddedHead G H a b) :
    AncestralMarks H ↔ ¬ Reach (DirectedWithout G a b) a b := by
  constructor
  · intro after alternate
    have path := reach_map (fun h => (directed_iff_without edit _ _).mpr h) alternate
    exact after.no_head_into_ancestor path ((arrowhead_iff_after_addition edit a b).mpr (Or.inr ⟨rfl, rfl⟩))
  · intro noAlternate
    constructor
    · intro u v w line
      have unchanged : H.marks u v = G.marks u v := by
        apply edit.other
        · by_cases h : u = a
          · right
            intro j
            subst u
            subst v
            simp [show H.marks a b = some (true, true) from edit.changed] at line
          · exact Or.inl h
        · by_cases h : u = b
          · right
            intro j
            subst u
            subst v
            simp [show H.marks b a = some (true, true) from spouse_reverse edit.changed] at line
          · exact Or.inl h
      exact (noLines u v (unchanged.symm.trans line)).elim
    · intro u v path head
      have before := (arrowhead_iff_after_addition edit u v).mp head
      have kept := reach_map (fun h => (directed_iff_without edit _ _).mp h) path
      rcases before with old | ⟨rfl, rfl⟩
      · exact ancestral.no_head_into_ancestor (reach_map And.left kept) old
      · exact noAlternate kept

/-- The equality of the external parent and spouse sets in Lemma 2. -/
def MatchingParentsSpouses (G : MarkedGraph n) (a b : Fin n) : Prop :=
  ∀ c, c ≠ a → c ≠ b →
    (Directed G c a ↔ Directed G c b) ∧ (Spouse G c a ↔ Spouse G c b)

/-- Matching parents exclude a second directed route from source to target. -/
theorem no_alternate_of_matching {G : MarkedGraph n} {a b : Fin n}
    (ancestral : AncestralMarks G) (edge : Directed G a b)
    (matching : MatchingParentsSpouses G a b) :
    ¬ Reach (DirectedWithout G a b) a b := by
  intro route
  cases route with
  | refl => exact directed_distinct edge rfl
  | @extend c _ prior last =>
    have cb := directed_distinct last.1
    have ca : c ≠ a := last.2.resolve_right (fun denied => denied rfl)
    have parent := (matching c ca cb).1.mpr last.1
    exact ancestral.no_head_into_ancestor (reach_map And.left prior) (head_of_directed parent)

/-- The matching sets imply the local parent and spouse clauses of (t2). -/
theorem parent_and_spouse_conditions {G : MarkedGraph n} {a b : Fin n}
    (edge : Directed G a b) (matching : MatchingParentsSpouses G a b) :
    (∀ c, Directed G c a → Directed G c b) ∧
    (∀ c, Spouse G c a → c ≠ b → Directed G c b ∨ Spouse G c b) := by
  constructor
  · intro c parent
    have ca := directed_distinct parent
    have cb : c ≠ b := by
      rintro rfl
      have back := directed_reverse_marks edge
      simp [Directed, back] at parent
    exact (matching c ca cb).1.mp parent
  · intro c spouse cb
    have ca : c ≠ a := by
      rintro rfl
      simp [Spouse, G.loop_free] at spouse
    exact Or.inr ((matching c ca cb).2.mp spouse)

/-- A discriminating path ending with the edited edge would require a
preceding collider that is a parent of the target and receives an arrowhead
from its edge to the source. Matching parents and spouses exclude that turn. -/
theorem no_preceding_discriminating_collider {G : MarkedGraph n} {a b c : Fin n}
    (matching : MatchingParentsSpouses G a b) (parent : Directed G c b)
    (head : G.arrowheadAt c a = true) : False := by
  have ca : c ≠ a := by
    rintro rfl
    simp [arrowheadAt, G.loop_free] at head
  have cb := directed_distinct parent
  have parentA := (matching c ca cb).1.mpr parent
  change G.marks c a = some (false, true) at parentA
  simp [arrowheadAt, parentA] at head

end
end OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange
