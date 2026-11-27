module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDLight

/-!
Lee and Honavar, AAAI 2016, Lemma 5 and Appendix (pp. 3267, 3269–3270).
https://faculty.ist.psu.edu/vhonavar/Papers/AAAI2016.pdf
-/

@[expose] public section

namespace RCDLemma5

open RCDLight

/-- A join factored at its shared pivot, before the schema filter. -/
inductive Splice : List K → List K → List K → Prop
  | atPivot (before overlap after : List K) (v : K) :
      Splice (before ++ v :: overlap.reverse) (overlap ++ v :: after) (before ++ v :: after)

private theorem take_at_boundary (before after : List K) (v : K) :
    (before ++ v :: after).take (before.length + 1) = before ++ [v] := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp

private theorem take_shared_pivot {s t : List K} {i : Nat} (h : Pivot s t i) :
    ∃ common v left right, i = common.length + 1 ∧
      s = common ++ v :: left ∧ t = common ++ v :: right := by
  let shared := s.take i
  have lp : shared.length = i := by simp [shared, List.length_take, Nat.min_eq_left h.2.1]
  have hp : shared ≠ [] := List.length_pos_iff.mp (by rw [lp]; exact h.1)
  have ht : shared = t.take i := h.2.2.2
  cases hv : shared.getLast? with
  | none => exact (hp (List.getLast?_eq_none_iff.mp hv)).elim
  | some v =>
    obtain ⟨common, eqPrefix⟩ := List.getLast?_eq_some_iff.mp hv
    refine ⟨common, v, s.drop i, t.drop i, ?_, ?_, ?_⟩
    · simpa only [eqPrefix, List.length_append, List.length_singleton] using lp.symm
    · calc
        s = shared ++ s.drop i := (List.take_append_drop i s).symm
        _ = common ++ v :: s.drop i := by simp [eqPrefix]
    · calc
        t = t.take i ++ t.drop i := (List.take_append_drop i t).symm
        _ = common ++ v :: t.drop i := by simp [← ht, eqPrefix]

/-- Exact positive-pivot list formulation of the paper's join before validity filtering. -/
theorem splice_iff {p q r : List K} : Splice p q r ↔
    ∃ i, Pivot p.reverse q i ∧ joinAt p q i = r := by
  constructor
  · rintro ⟨before, overlap, after, v⟩
    exact ⟨overlap.length + 1, join_reversed_suffix before overlap after v⟩
  · rintro ⟨i, pivot, rfl⟩
    obtain ⟨overlap, v, l, after, rfl, left, rfl⟩ := take_shared_pivot pivot
    have pForm : p = l.reverse ++ v :: overlap.reverse := by
      rw [← List.reverse_reverse p, left]
      simp [List.reverse_append, List.reverse_cons, List.append_assoc]
    rw [pForm, (join_reversed_suffix l.reverse overlap after v).2]
    exact .atPivot l.reverse overlap after v

/-- Triangle symmetry for joins, with the third word already available as a valid path. -/
theorem splice_triangle {p q r : List K} (h : Splice p q r) : Splice r q.reverse p := by
  cases h with
  | atPivot before overlap after v =>
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
      (Splice.atPivot before after.reverse overlap.reverse v)

/-- Reversing a join swaps its two inputs. -/
theorem splice_reverse {p q r : List K} (h : Splice p q r) :
    Splice q.reverse p.reverse r.reverse := by
  cases h with
  | atPivot before overlap after v =>
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
      (Splice.atPivot after.reverse overlap before.reverse v)

private theorem splice_at_canonical (p : List K) {x : K} (h : p.getLast? = some x) :
    Splice p p.reverse [p.head?.getD x] := by
  obtain ⟨before, rfl⟩ := List.getLast?_eq_some_iff.mp h
  cases before with
  | nil => exact .atPivot [] [] [] x
  | cons first rest =>
    have h' : Splice ([] ++ first :: (rest ++ [x]).reverse.reverse)
        ((rest ++ [x]).reverse ++ first :: []) ([] ++ first :: []) := .atPivot [] _ [] first
    simpa [List.reverse_cons] using h'

/-- A canonical result forces the inputs to be reverses. -/
theorem splice_canonicality {p q r : List K} {x : K} (h : Splice p q r)
    (eq : r = [x]) : q = p.reverse := by
  revert eq
  cases h with
  | atPivot before overlap after v =>
    intro eq
    have len : before.length + (after.length + 1) = 1 := by
      simpa using congrArg List.length eq
    have emptyBefore : before = [] := List.length_eq_zero_iff.mp (by omega)
    have emptyAfter : after = [] := List.length_eq_zero_iff.mp (by omega)
    simp [emptyBefore, emptyAfter, List.reverse_cons]

/-- Local two- and three-class tests for relational paths without repeated entity roles. -/
def Local (adj retrace : K → K → Prop) : List K → Prop
  | a :: b :: c :: rest => adj a b ∧ (a ≠ c ∨ retrace a b) ∧ Local adj retrace (b :: c :: rest)
  | [a, b] => adj a b
  | _ => True

/-- At the join, the outer classes may coincide only when the schema allows a repetition. -/
def Turn (retrace : K → K → Prop) (left : Option K) (v : K) (right : Option K) : Prop :=
  match left, right with
  | some a, some c => a ≠ c ∨ retrace a v
  | _, _ => True

/-- Splitting at a listed occurrence isolates its one possible new three-class test. -/
theorem local_split {adj retrace : K → K → Prop} (before after : List K) (v : K) :
    Local adj retrace (before ++ v :: after) ↔
      Local adj retrace (before ++ [v]) ∧ Local adj retrace (v :: after) ∧
        Turn retrace before.getLast? v after.head? := by
  induction before with
  | nil => simp [Local, Turn]
  | cons a tail ih =>
    cases tail with
    | nil =>
      cases after <;> simp [Local, Turn, and_comm]
    | cons b tail =>
      cases tail with
      | nil =>
        simp only [List.cons_append, List.nil_append, Local] at ih ⊢
        rw [ih]
        simp [and_assoc]
      | cons c rest =>
        simp only [List.cons_append, Local] at ih ⊢
        rw [ih]
        simp [and_assoc]

private theorem turn_flip {retrace : K → K → Prop} (l : Option K) (v : K) (r : Option K) :
    Turn retrace l v r ↔ Turn retrace r v l := by
  cases l <;> cases r <;> simp [Turn]
  rename_i a c
  by_cases h : a = c
  · subst c
    simp
  · simp [h, Ne.symm h]

/-- Reversal preserves the local tests on an undirected schema. -/
theorem local_reverse {adj retrace : K → K → Prop}
    (sym : ∀ {a b}, adj a b → adj b a) {p : List K} (h : Local adj retrace p) :
    Local adj retrace p.reverse := by
  induction p with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b tail =>
      have split := (local_split (adj := adj) (retrace := retrace) [a] tail b).mp h
      have suff := ih split.2.1
      have revSuff : Local adj retrace (tail.reverse ++ [b]) := by simpa using suff
      have boundary : Turn retrace tail.reverse.getLast? b (some a) := by
        rw [List.getLast?_reverse, ← turn_flip]
        exact split.2.2
      rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
      exact (local_split _ _ _).mpr ⟨revSuff, sym split.1, boundary⟩

private theorem left_of_local {adj retrace : K → K → Prop} {before after : List K} {v : K}
    (h : Local adj retrace (before ++ v :: after)) : Local adj retrace (before ++ [v]) :=
  ((local_split before after v).mp h).1

private theorem right_of_local {adj retrace : K → K → Prop} {before after : List K} {v : K}
    (h : Local adj retrace (before ++ v :: after)) : Local adj retrace (v :: after) :=
  ((local_split before after v).mp h).2.1

private theorem local_of_splice_at_new_turn {adj retrace : K → K → Prop}
    {before overlap after : List K} {v : K}
    (left : Local adj retrace (before ++ v :: overlap.reverse))
    (right : Local adj retrace (overlap ++ v :: after))
    (turn : Turn retrace before.getLast? v after.head?) :
    Local adj retrace (before ++ v :: after) :=
  (local_split _ _ _).mpr ⟨left_of_local left, right_of_local right, turn⟩

private theorem splice_join_m_lt_n {adj retrace : K → K → Prop}
    (sym : ∀ {a b}, adj a b → adj b a) {q d₁ d₂ p r : List K} {m n : Nat}
    (hm : Pivot q.reverse d₁ m) (hn : Pivot q.reverse d₂ n) (lt : m < n)
    (jp : joinAt q d₁ m = p) (jr : joinAt q d₂ n = r)
    (d1Valid : Local adj retrace d₁) (d2Valid : Local adj retrace d₂)
    (pValid : Local adj retrace p) :
    ∃ candidate, Local adj retrace candidate ∧ Splice d₁.reverse d₂ candidate ∧
      Pivot p.reverse candidate (d₁.length - m + 1 + (n - m)) ∧
      joinAt p candidate (d₁.length - m + 1 + (n - m)) = r := by
  obtain ⟨longOverlap, b, base, zTail, hnEq, qForm, d2Form⟩ := take_shared_pivot hn
  have bound : m ≤ longOverlap.length := by omega
  have sameTake : longOverlap.take m = d₁.take m := by
    have eq := hm.2.2.2
    rwa [qForm, List.take_append, Nat.sub_eq_zero_of_le bound, List.take_zero,
      List.append_nil] at eq
  have shorter : Pivot longOverlap d₁ m := ⟨hm.1, bound, hm.2.2.1, sameTake⟩
  obtain ⟨common, a, gap, xTail, hmEq, longForm, d1Form⟩ := take_shared_pivot shorter
  have qLeft : q = (base.reverse ++ b :: gap.reverse) ++ a :: common.reverse := by
    rw [← List.reverse_reverse q, qForm, longForm]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have qRight : q = base.reverse ++ b :: longOverlap.reverse := by
    rw [← List.reverse_reverse q, qForm]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have pForm : p = (base.reverse ++ b :: gap.reverse) ++ a :: xTail := by
    rw [← jp, qLeft, d1Form, hmEq]
    exact (join_reversed_suffix _ _ _ _).2
  have rForm : r = base.reverse ++ b :: zTail := by
    rw [← jr, qRight, d2Form, hnEq]
    exact (join_reversed_suffix _ _ _ _).2
  have d1Rev : d₁.reverse = xTail.reverse ++ a :: common.reverse := by
    simp [d1Form, List.reverse_append, List.reverse_cons, List.append_assoc]
  have d2Split : d₂ = common ++ a :: (gap ++ b :: zTail) := by
    simp [d2Form, longForm, List.append_assoc]
  have pRev : p.reverse = xTail.reverse ++ a :: (gap ++ b :: base) := by
    simp [pForm, List.reverse_append, List.reverse_cons, List.append_assoc]
  have turn : Turn retrace xTail.reverse.getLast? a (gap ++ b :: zTail).head? := by
    have h := local_reverse sym pValid
    rw [pRev] at h
    have eq : (gap ++ b :: zTail).head? = (gap ++ b :: base).head? := by
      cases gap <;> rfl
    rw [eq]
    exact ((local_split _ _ _).mp h).2.2
  have localCandidate := local_of_splice_at_new_turn (d1Rev ▸ local_reverse sym d1Valid)
    (d2Split ▸ d2Valid) turn
  have represent : Splice d₁.reverse d₂ (xTail.reverse ++ a :: (gap ++ b :: zTail)) := by
    rw [d1Rev, d2Split]
    exact .atPivot _ _ _ _
  have index : d₁.length - m + 1 + (n - m) = xTail.length + gap.length + 2 := by
    rw [d1Form, hmEq, hnEq, longForm]
    simp only [List.length_append, List.length_cons]
    omega
  refine ⟨_, localCandidate, represent, ?_⟩
  rw [index, pForm, rForm]
  simpa [List.append_assoc] using representative_pivot_m_lt_n base.reverse gap xTail zTail a b

private theorem heads_disagree_after_shared [DecidableEq K] (p q : List K) :
    ∃ common left right, p = common ++ left ∧ q = common ++ right ∧
      ∀ a, left.head? = some a → right.head? ≠ some a := by
  induction p generalizing q with
  | nil => exact ⟨[], [], q, rfl, rfl, by simp⟩
  | cons a rest ih =>
    cases q with
    | nil => exact ⟨[], a :: rest, [], rfl, rfl, by simp⟩
    | cons b tail =>
      by_cases eq : a = b
      · subst b
        obtain ⟨common, left, right, hp, hq, diff⟩ := ih tail
        exact ⟨a :: common, left, right, congrArg (a :: ·) hp, congrArg (a :: ·) hq, diff⟩
      · exact ⟨[], a :: rest, b :: tail, rfl, rfl, by simpa using Ne.symm eq⟩

private theorem splice_join_equal {adj retrace : K → K → Prop}
    (sym : ∀ {a b}, adj a b → adj b a) {q d₁ d₂ p r : List K} {m : Nat}
    (hm : Pivot q.reverse d₁ m) (hn : Pivot q.reverse d₂ m)
    (jp : joinAt q d₁ m = p) (jr : joinAt q d₂ m = r)
    (d1Valid : Local adj retrace d₁) (d2Valid : Local adj retrace d₂) :
    ∃ candidate, Local adj retrace candidate ∧ Splice d₁.reverse d₂ candidate ∧
      Splice p candidate r := by
  classical
  obtain ⟨common, a, base, xTail, hmEq, qForm, d1Form⟩ := take_shared_pivot hm
  let zTail := d₂.drop m
  have d2Form : d₂ = common ++ a :: zTail := by
    calc
      d₂ = d₂.take m ++ zTail := (List.take_append_drop _ _).symm
      _ = common ++ a :: zTail := by
        rw [← hn.2.2.2, qForm, hmEq, take_at_boundary]
        simp
  have qLeft : q = base.reverse ++ a :: common.reverse := by
    rw [← List.reverse_reverse q, qForm]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have pForm : p = base.reverse ++ a :: xTail := by
    rw [← jp, qLeft, d1Form, hmEq]
    exact (join_reversed_suffix _ _ _ _).2
  have rForm : r = base.reverse ++ a :: zTail := by
    rw [← jr, qLeft, d2Form, hmEq]
    exact (join_reversed_suffix _ _ _ _).2
  obtain ⟨extra, left, right, hx, hz, diff⟩ := heads_disagree_after_shared xTail zTail
  have sharedHead : ∃ padding v, a :: extra = padding ++ [v] := by
    cases h : (a :: extra).getLast? with
    | none => simp at h
    | some v => exact ⟨_, v, (List.getLast?_eq_some_iff.mp h).choose_spec⟩
  obtain ⟨padding, v, hPad⟩ := sharedHead
  have lForm : a :: xTail = padding ++ v :: left := by
    rw [hx, ← List.cons_append, hPad]
    simp
  have rTailForm : a :: zTail = padding ++ v :: right := by
    rw [hz, ← List.cons_append, hPad]
    simp
  have d1Split : d₁ = (common ++ padding) ++ v :: left := by
    rw [d1Form, lForm, List.append_assoc]
  have d2Split : d₂ = (common ++ padding) ++ v :: right := by
    rw [d2Form, rTailForm, List.append_assoc]
  have pSplit : p = (base.reverse ++ padding) ++ v :: left := by
    rw [pForm, lForm, List.append_assoc]
  have rSplit : r = (base.reverse ++ padding) ++ v :: right := by
    rw [rForm, rTailForm, List.append_assoc]
  have d1Rev : d₁.reverse = left.reverse ++ v :: (common ++ padding).reverse := by
    simp [d1Split, List.reverse_append, List.reverse_cons, List.append_assoc]
  have turn : Turn retrace left.reverse.getLast? v right.head? := by
    rw [List.getLast?_reverse]
    cases hLeft : left.head? <;> cases hRight : right.head?
    all_goals simp only [Turn]
    exact Or.inl (fun h => diff _ hLeft (h ▸ hRight))
  have localCandidate := local_of_splice_at_new_turn (d1Rev ▸ local_reverse sym d1Valid)
    (d2Split ▸ d2Valid) turn
  refine ⟨left.reverse ++ v :: right, localCandidate, ?_, ?_⟩
  · rw [d1Rev, d2Split]
    exact .atPivot _ _ _ _
  · rw [pSplit, rSplit]
    simpa only [List.reverse_reverse] using
      Splice.atPivot (base.reverse ++ padding) left.reverse right v

/-- Reroot both unrolled incidences at the first flanking attribute. The returned path is
compatible with the original third flank and passes the schema filter. -/
theorem compatible_representative {adj retrace : K → K → Prop}
    (sym : ∀ {a b}, adj a b → adj b a) {q d₁ d₂ p r : List K}
    (hp : Splice q d₁ p) (hr : Splice q d₂ r)
    (d1Valid : Local adj retrace d₁) (d2Valid : Local adj retrace d₂)
    (pValid : Local adj retrace p) (rValid : Local adj retrace r) :
    ∃ candidate, Local adj retrace candidate ∧ Splice d₁.reverse d₂ candidate ∧
      Splice p candidate r := by
  obtain ⟨m, hm, jp⟩ := splice_iff.mp hp
  obtain ⟨n, hn, jr⟩ := splice_iff.mp hr
  rcases Nat.lt_trichotomy m n with lt | eq | gt
  · obtain ⟨c, valid, first, piv, result⟩ :=
      splice_join_m_lt_n sym hm hn lt jp jr d1Valid d2Valid pValid
    exact ⟨c, valid, first, splice_iff.mpr ⟨_, piv, result⟩⟩
  · subst n
    exact splice_join_equal sym hm hn jp jr d1Valid d2Valid
  · obtain ⟨c, valid, first, piv, result⟩ :=
      splice_join_m_lt_n sym hn hm gt jr jp d2Valid d1Valid rValid
    have orig : Splice r c p := splice_iff.mpr ⟨_, piv, result⟩
    exact ⟨c.reverse, local_reverse sym valid, by simpa using splice_reverse first,
      splice_triangle orig⟩

private theorem splice_singleton_left {p q r : List K} {x : K} (h : Splice p q r)
    (hp : p = [x]) : q = r := by
  revert hp
  cases h with
  | atPivot before overlap after v =>
    intro hp
    have len : before.length + (overlap.length + 1) = 1 := by
      simpa using congrArg List.length hp
    have emptyBefore : before = [] := List.length_eq_zero_iff.mp (by omega)
    have emptyOverlap : overlap = [] := List.length_eq_zero_iff.mp (by omega)
    simp [emptyBefore, emptyOverlap]

private theorem splice_singleton_right {p q r : List K} {x : K} (h : Splice p q r)
    (hq : q = [x]) : p = r := by
  have revEq : p.reverse = r.reverse :=
    splice_singleton_left (x := x) (splice_reverse h) (by simp [hq])
  exact List.reverse_inj.mp revEq

private theorem splice_endpoints {p q r : List K} (h : Splice p q r) :
    r.head? = p.head? ∧ r.getLast? = q.getLast? := by
  cases h with
  | atPivot before overlap after v =>
    constructor
    · simp [List.head?_append]
    · simp [List.getLast?_append, List.getLast?_cons]

/-- Paper Appendix's `extend`, including the relational-path validity filter. -/
def Extend (valid : List K → Prop) (p q r : List K) : Prop := valid r ∧ Splice p q r

/-- The dependency candidates in Definition 3 following Phase I. `dependency d x y`
represents `d.X → [IY].Y`; both orientations are present before Phase II. -/
structure Candidates (K A : Type) where
  adj : K → K → Prop
  retrace : K → K → Prop
  owner : A → K
  dependency : List K → A → A → Prop
  symmetric_adj : ∀ {a b}, adj a b → adj b a
  valid_dependency : ∀ {d x y}, dependency d x y → Local adj retrace d
  dependency_endpoints : ∀ {d x y}, dependency d x y →
    d.head? = some (owner y) ∧ d.getLast? = some (owner x)
  reverse_dependency : ∀ {d x y}, dependency d x y → dependency d.reverse y x
  different_attributes : ∀ {d x y}, dependency d x y → x ≠ y

abbrev Variable (K A : Type) := List K × A

def WellTyped (M : Candidates K A) (b : K) (v : Variable K A) : Prop :=
  Local M.adj M.retrace v.1 ∧ v.1.head? = some b ∧ v.1.getLast? = some (M.owner v.2)

def UnrolledArrow (M : Candidates K A) (src dst : Variable K A) : Prop :=
  ∃ d, M.dependency d src.2 dst.2 ∧ Extend (Local M.adj M.retrace) dst.1 d src.1

def Unshielded (M : Candidates K A) (p q r : Variable K A) : Prop :=
  UnrolledArrow M p q ∧ UnrolledArrow M r q ∧
    p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ ¬ UnrolledArrow M r p ∧ ¬ UnrolledArrow M p r

private theorem unrolled_reverse {M : Candidates K A} {src dst : Variable K A}
    (dstValid : Local M.adj M.retrace dst.1) (h : UnrolledArrow M src dst) :
    UnrolledArrow M dst src := by
  obtain ⟨d, hDep, _, hSplice⟩ := h
  exact ⟨d.reverse, M.reverse_dependency hDep, dstValid, splice_triangle hSplice⟩

private theorem unrolled_canonical {M : Candidates K A} {r : List K} {x z : A}
    (h : UnrolledArrow M (r, z) ([M.owner x], x)) : M.dependency r z x := by
  obtain ⟨d, hDep, _, hSplice⟩ := h
  have equality : d = r := splice_singleton_left (x := M.owner x) hSplice rfl
  simpa [equality] using hDep

private theorem splice_reverse_to_canonical {d : List K} {x : K}
    (h : d.getLast? = some x) : Splice d.reverse d [x] := by
  have hRev : d.reverse.getLast? = some (d.head?.getD x) := by
    rw [List.getLast?_reverse]
    cases hHead : d.head? with
    | none => simp [List.head?_eq_none_iff.mp hHead] at h
    | some v => simp
  have hx : (d.reverse.head?.getD (d.head?.getD x)) = x := by simp [List.head?_reverse, h]
  simpa only [hx, List.reverse_reverse] using splice_at_canonical d.reverse hRev

/-- Lemma 5 with the two inducing dependencies retained, so the representative can
be used to orient those same dependencies. The model uses local schema path tests. -/
theorem representative_unshielded_triple {M : Candidates K A} {p q r : List K} {x y z : A}
    (h : Unshielded M (p, x) (q, y) (r, z)) :
    ∃ d₁ d₂ candidate, M.dependency d₁ x y ∧ M.dependency d₂ z y ∧
      Extend (Local M.adj M.retrace) q d₁ p ∧ Extend (Local M.adj M.retrace) q d₂ r ∧
      WellTyped M (M.owner x) ([M.owner x], x) ∧
      WellTyped M (M.owner x) (d₁.reverse, y) ∧ WellTyped M (M.owner x) (candidate, z) ∧
      Unshielded M ([M.owner x], x) (d₁.reverse, y) (candidate, z) ∧
      Extend (Local M.adj M.retrace) d₁.reverse d₂ candidate ∧ Splice p candidate r := by
  obtain ⟨⟨d₁, dep1, pValid, pSplice⟩, ⟨d₂, dep2, rValid, rSplice⟩, _, _, different,
    noRight, _⟩ := h
  have d1Valid := M.valid_dependency dep1
  have d2Valid := M.valid_dependency dep2
  obtain ⟨candidate, valid, first, compat⟩ := compatible_representative M.symmetric_adj
    pSplice rSplice d1Valid d2Valid pValid rValid
  have canonicalValid : Local M.adj M.retrace [M.owner x] := trivial
  have centerValid := local_reverse M.symmetric_adj d1Valid
  have d1Ends := M.dependency_endpoints dep1
  have d2Ends := M.dependency_endpoints dep2
  have toCenter : UnrolledArrow M ([M.owner x], x) (d₁.reverse, y) :=
    ⟨d₁, dep1, canonicalValid, splice_reverse_to_canonical d1Ends.2⟩
  have fromRight : UnrolledArrow M (candidate, z) (d₁.reverse, y) := ⟨d₂, dep2, valid, first⟩
  have noShield : ¬ UnrolledArrow M (candidate, z) ([M.owner x], x) := by
    intro shield
    exact noRight ⟨candidate, unrolled_canonical shield, rValid, compat⟩
  have diffFlanks : ([M.owner x], x) ≠ (candidate, z) := by
    intro eq
    have sameAttr : x = z := congrArg Prod.snd eq
    have sameWord : candidate = [M.owner x] := (congrArg Prod.fst eq).symm
    have origEq := splice_singleton_right compat sameWord
    exact different (Prod.ext origEq sameAttr)
  have headCenter : d₁.reverse.head? = some (M.owner x) := by simpa using d1Ends.2
  refine ⟨d₁, d₂, candidate, dep1, dep2, ⟨pValid, pSplice⟩, ⟨rValid, rSplice⟩,
    ⟨canonicalValid, rfl, rfl⟩, ⟨centerValid, headCenter, by simpa using d1Ends.1⟩,
    ⟨valid, (splice_endpoints first).1.trans headCenter,
      (splice_endpoints first).2.trans d2Ends.2⟩, ?_, ⟨valid, first⟩, compat⟩
  exact ⟨toCenter, fromRight,
    fun eq => M.different_attributes dep1 (show x = y from congrArg Prod.snd eq),
    fun eq => M.different_attributes dep2 (show z = y from congrArg Prod.snd eq),
    diffFlanks, noShield, fun shield => noShield (unrolled_reverse valid shield)⟩

end RCDLemma5

end
