module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDClassification

@[expose] public section

namespace RpCD

open Ground
open RelationalFiniteSearch

variable {A P S : Type} [DecidableEq A] [DecidableEq P]

def Ground.Dependency.relVar (d : Dependency A P) : A × P := (d.source, d.path)

/-- Schema-level laws for reversing paths and realizing one path in isolation. -/
structure PathSemantics (B : Schema A P S) where
  canonical : A → P
  reverse : Dependency A P → Dependency A P
  involution : ∀ q, reverse (reverse q) = q
  endpoints : ∀ q, (reverse q).source = q.target ∧ (reverse q).target = q.source
  reverse_realizes : ∀ s q x z, B.realizes s (reverse q) z x = B.realizes s q x z
  base_identity : ∀ s q x, B.realizes s q x x = true → q.path = canonical q.target
  valid : Dependency A P → Prop
  valid_reverse : ∀ d, valid d → valid (reverse d)
  isolate : ∀ d : Dependency A P, valid d → d.source ≠ d.target →
    ∃ s x z, B.realizes s d x z = true ∧
      ∀ q, B.realizes s q x z = true → q = d

def decode (target : A) (v : A × P) : Dependency A P := ⟨v.1, target, v.2⟩

def phaseQuery {B : Schema A P S} {M : Model A P} (L : PathSemantics B)
    (O : Oracle B M) : Query (Dependency A P) (A × P) where
  source := Dependency.relVar
  target := fun d => (d.target, L.canonical d.target)
  reverse := L.reverse
  independent := fun d selected => O.answer d (selected.map (decode d.target))

def trueDependency (M : Model A P) (d : Dependency A P) : Bool :=
  decide (d ∈ M.dependencies)

theorem adjacent_of_surviving {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) {d : Dependency A P}
    (present : pairPresent (phaseQuery L O) (trueDependency M) d)
    {s : S} {x z : Fin (B.size s)} (hit : B.realizes s d x z = true) :
    OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence.Adjacent (graph B M s) x z := by
  rcases present with forward | backward
  · exact .inr (List.any_eq_true.mpr ⟨d, of_decide_eq_true forward, hit⟩)
  · exact .inl (List.any_eq_true.mpr ⟨L.reverse d, of_decide_eq_true backward, by
      rw [L.reverse_realizes, hit]⟩)

private theorem phase_faithful {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M)
    (modelLegal : ∀ d ∈ M.dependencies, L.valid d)
    (d : Dependency A P) (present : pairPresent (phaseQuery L O) (trueDependency M) d)
    (C : List (A × P)) (otherOutside : d.relVar ∉ C)
    (baseOutside : (d.target, L.canonical d.target) ∉ C) :
    (phaseQuery L O).independent d C = false := by
  have different : d.source ≠ d.target := by
    intro same
    rcases present with forward | backward
    · have rankLt := M.acyclic d (of_decide_eq_true forward)
      simp [same] at rankLt
    · have ⟨source, target⟩ := L.endpoints d
      have rankLt := M.acyclic (L.reverse d) (of_decide_eq_true backward)
      simp [source, target, same] at rankLt
  have valid : L.valid d := by
    rcases present with forward | backward
    · exact modelLegal d (of_decide_eq_true forward)
    · have reversed := L.valid_reverse _ (modelLegal _ (of_decide_eq_true backward))
      simpa [phaseQuery, L.involution] using reversed
  obtain ⟨s, x, z, hit, isolated⟩ := L.isolate d valid different
  apply Bool.eq_false_iff.mpr
  intro verdict
  have ci := (O.exact d _).mp verdict
  apply ci s x z hit
  apply OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence.adjacent_dConnected
    _ (adjacent_of_surviving L O present hit)
  · apply Bool.eq_false_iff.mpr
    rintro conditioned
    obtain ⟨p, listed, pHit⟩ := List.any_eq_true.mp conditioned
    obtain ⟨v, inside, rfl⟩ := List.mem_map.mp listed
    apply baseOutside
    have source : v.1 = d.target :=
      (B.types s _ x x pHit).2.symm.trans (B.types s d x z hit).1
    have path : v.2 = L.canonical d.target := L.base_identity s _ x pHit
    have same : v = (d.target, L.canonical d.target) := Prod.ext source path
    exact same ▸ inside
  · apply Bool.eq_false_iff.mpr
    rintro conditioned
    obtain ⟨p, listed, pHit⟩ := List.any_eq_true.mp conditioned
    obtain ⟨v, inside, rfl⟩ := List.mem_map.mp listed
    apply otherOutside
    have same := congrArg Dependency.relVar (isolated _ pHit)
    exact (show v = d.relVar from same) ▸ inside

private theorem phase_parents {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (initial : List (Dependency A P))
    (included : ∀ p ∈ M.dependencies, p ∈ initial) {d : Dependency A P}
    (absent : d ∉ M.dependencies) :
    ∀ p, p ∈ ((trueParentCandidates (phaseQuery L O) (trueDependency M) initial d).map
      (phaseQuery L O).source).map (decode d.target) ↔ p ∈ parents M d.target := by
  intro p
  constructor
  · intro listed
    obtain ⟨v, mapped, decodedP⟩ := (List.mem_map (f := decode d.target)).mp listed
    rw [← decodedP]
    obtain ⟨c, candidateMember, equal⟩ := (List.mem_map (f := (phaseQuery L O).source)).mp mapped
    change c.relVar = v at equal
    rw [← equal]
    obtain ⟨candidate, active⟩ := List.mem_filter.mp candidateMember
    obtain ⟨_, test⟩ := List.mem_filter.mp candidate
    have eligible : c.target = d.target ∧ c.relVar ≠ d.relVar := by
      have h := of_decide_eq_true test
      exact ⟨congrArg Prod.fst h.1, h.2⟩
    have decoded : decode d.target c.relVar = c := by
      cases c
      simp [decode, Dependency.relVar, ← eligible.1]
    rw [decoded]
    exact List.mem_filter.mpr ⟨of_decide_eq_true active, by simp [eligible.1]⟩
  · intro mem
    obtain ⟨trueP, target⟩ := List.mem_filter.mp mem
    have same : p.target = d.target := eq_of_beq target
    have diff : p.relVar ≠ d.relVar := by
      intro equal
      have eq : p = d := by
        cases p
        cases d
        simp_all [Dependency.relVar, Prod.mk.injEq]
      exact absent (eq ▸ trueP)
    apply List.mem_map.mpr
    refine ⟨p.relVar, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨p, List.mem_filter.mpr ⟨?_, decide_eq_true trueP⟩, rfl⟩
      exact List.mem_filter.mpr ⟨included p trueP, by simp [eligible, phaseQuery, same, diff]⟩
    · cases p
      simp [decode, Dependency.relVar, ← same]

theorem phaseOne_ground_exact {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (initial : List (Dependency A P))
    (included : ∀ p ∈ M.dependencies, p ∈ initial)
    (closed : PairClosed (phaseQuery L O) initial)
    (valid : ∀ p ∈ initial, p.source ≠ p.target)
    (legal : ∀ p ∈ initial, L.valid p)
    (d : Dependency A P) :
    d ∈ phaseOne (phaseQuery L O) initial ↔
      d ∈ initial ∧ pairPresent (phaseQuery L O) (trueDependency M) d := by
  apply phaseOne_exact (phaseQuery L O) (trueDependency M) initial L.involution closed
  · intro c mem same
    exact valid c mem (congrArg Prod.fst same)
  · exact phase_faithful L O (fun q dep => legal q (included q dep))
  · intro c candidate missing
    have absent : c ∉ M.dependencies := fun mem => missing (.inl (decide_eq_true mem))
    have absentRev : L.reverse c ∉ M.dependencies :=
      fun mem => missing (.inr (decide_eq_true mem))
    rcases Nat.le_total (M.rank c.source) (M.rank c.target) with forward | backward
    · apply Or.inl
      apply (O.exact _ _).mpr
      apply (relCI_congr (phase_parents L O initial included absent)).mpr
      exact parents_separate B M (valid c candidate).symm forward
    · apply Or.inr
      apply (O.exact _ _).mpr
      apply (relCI_congr (phase_parents L O initial included absentRev)).mpr
      have ⟨source, target⟩ := L.endpoints c
      exact parents_separate B M (valid _ (closed c candidate)).symm
        (by simpa [phaseQuery, source, target] using backward)

end RpCD

end
