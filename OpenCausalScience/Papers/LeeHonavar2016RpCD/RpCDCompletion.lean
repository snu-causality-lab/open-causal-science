module
public import Std

@[expose] public section

namespace RpCD.Completion

structure Constraints (V : Type) where
  adjacent : V → V → Bool
  fixed : V → V → Bool
  noncollider : V → V → V → Bool

variable {V : Type}

/-- A sink can have no fixed outgoing arrow or forbidden pair of remaining neighbors. -/
def eligible (C : Constraints V) (live : List V) (y : V) : Bool :=
  (live.all fun x => !C.fixed y x) &&
  (live.all fun x => live.all fun z =>
    !(C.adjacent x y && C.adjacent z y && C.noncollider x y z))

theorem eligible_iff (C : Constraints V) (live : List V) (y : V) :
    eligible C live y = true ↔
      (∀ x ∈ live, C.fixed y x ≠ true) ∧
      (∀ x ∈ live, ∀ z ∈ live, C.adjacent x y = true →
        C.adjacent z y = true → C.noncollider x y z ≠ true) := by
  simp only [eligible, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨outgoing, pairs⟩
    refine ⟨fun x hx => by simp [outgoing x hx], ?_⟩
    intro x hx z hz xy zy
    simpa [xy, zy] using pairs x hx z hz
  · rintro ⟨outgoing, pairs⟩
    refine ⟨fun x hx => Bool.eq_false_iff.mpr (outgoing x hx), ?_⟩
    intro x hx z hz
    apply Bool.eq_false_iff.mpr
    rintro both
    simp only [Bool.and_eq_true] at both
    exact pairs x hx z hz both.1.1 both.1.2 both.2

private theorem eligible_mono {C : Constraints V} {live small : List V} {y : V}
    (subset : ∀ x ∈ small, x ∈ live) (sink : eligible C live y = true) :
    eligible C small y = true := by
  obtain ⟨arrows, colliders⟩ := (eligible_iff C live y).mp sink
  exact (eligible_iff C small y).mpr
    ⟨fun x hx => arrows x (subset x hx),
      fun x hx z hz => colliders x (subset x hx) z (subset z hz)⟩

variable [DecidableEq V]

/-- A sink order witnesses an acyclic orientation preserving the constraints. -/
inductive SinkOrder (C : Constraints V) : List V → List V → Prop
  | nil : SinkOrder C [] []
  | cons {live order : List V} {y : V} :
      y ∈ live → eligible C live y = true →
      SinkOrder C (live.erase y) order → SinkOrder C live (y :: order)

theorem mem_of_sinkOrder {C : Constraints V} {live order : List V}
    (valid : SinkOrder C live order) (unique : live.Nodup) {v : V} :
    v ∈ order ↔ v ∈ live := by
  induction valid with
  | nil => simp
  | @cons live tail y member _ _ ih =>
    rw [List.mem_cons, ih (unique.erase y), unique.mem_erase_iff]
    constructor
    · rintro (rfl | ⟨_, h⟩)
      · exact member
      · exact h
    · intro here
      by_cases same : v = y
      · exact .inl same
      · exact .inr ⟨same, here⟩

theorem nodup_of_sinkOrder {C : Constraints V} {live order : List V}
    (valid : SinkOrder C live order) (unique : live.Nodup) : order.Nodup := by
  induction valid with
  | nil => simp
  | @cons live tail y _ _ smaller ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (unique.erase y)⟩
    intro member
    have earlier := (mem_of_sinkOrder smaller (unique.erase y)).mp member
    exact (unique.mem_erase_iff.mp earlier).1 rfl

private theorem restrict_sinkOrder {C : Constraints V} {live order : List V}
    (valid : SinkOrder C live order) (unique : live.Nodup) (x : V) :
    SinkOrder C (live.erase x) (order.erase x) := by
  induction valid with
  | nil => exact .nil
  | @cons live tail y member sink rest ih =>
    by_cases same : y = x
    · subst y
      simpa using rest
    · simp only [List.erase_cons, beq_iff_eq, same, ↓reduceIte]
      apply SinkOrder.cons (List.mem_erase_of_ne same |>.mpr member)
      · exact eligible_mono (fun _ => List.mem_of_mem_erase) sink
      · rw [List.erase_comm x y]
        exact ih (unique.erase y)

/-- Greedy elimination uses the first eligible sink each time. -/
def extend (C : Constraints V) : Nat → List V → Option (List V)
  | 0, live => if live.isEmpty then some [] else none
  | fuel + 1, live =>
      if live.isEmpty then some []
      else
        (live.find? (eligible C live)).bind fun sink =>
          (extend C fuel (live.erase sink)).map (sink :: ·)

theorem extend_sound {C : Constraints V} {fuel : Nat} {live order : List V}
    (result : extend C fuel live = some order) : SinkOrder C live order := by
  induction fuel generalizing live order with
  | zero =>
    cases live with
    | nil => simp [extend] at result; subst order; exact .nil
    | cons => simp [extend] at result
  | succ fuel ih =>
    cases live with
    | nil => simp [extend] at result; subst order; exact .nil
    | cons first rest =>
      let live := first :: rest
      change extend C (fuel + 1) live = _ at result
      simp only [extend, show live.isEmpty = false from rfl, Bool.false_eq_true, ↓reduceIte] at result
      cases chosen : live.find? (eligible C live) with
      | none => simp [chosen] at result
      | some sink =>
        cases next : extend C fuel (live.erase sink) with
        | none => simp [chosen, next] at result
        | some remaining =>
          simp [chosen, next] at result
          subst order
          exact .cons (List.mem_of_find?_eq_some chosen) (List.find?_some chosen) (ih next)

theorem extend_complete {C : Constraints V} {fuel : Nat} {live order : List V}
    (unique : live.Nodup) (enough : live.length ≤ fuel)
    (valid : SinkOrder C live order) : ∃ found, extend C fuel live = some found := by
  induction fuel generalizing live order with
  | zero =>
    have empty := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp enough)
    subst live
    exact ⟨[], rfl⟩
  | succ fuel ih =>
    cases valid with
    | nil => exact ⟨[], rfl⟩
    | @cons live tail y member sink next =>
      have nonempty : live.isEmpty = false := by
        cases live with
        | nil => simp at member
        | cons => rfl
      cases chosen : live.find? (eligible C live) with
      | none => exact ((List.find?_eq_none.mp chosen) y member sink).elim
      | some x =>
        have current := List.mem_of_find?_eq_some chosen
        have less := List.length_erase_of_mem current
        obtain ⟨found, result⟩ := ih (unique.erase x) (by omega)
          (restrict_sinkOrder (.cons member sink next) unique x)
        exact ⟨x :: found, by simp [extend, nonempty, chosen, result]⟩

/-- Arrows point from a later vertex in the sink order to an earlier one. -/
def arrow (C : Constraints V) (order : List V) (x y : V) : Prop :=
  C.adjacent x y = true ∧ order.idxOf y < order.idxOf x

structure Consistent (C : Constraints V) (live order : List V) : Prop where
  nodup : order.Nodup
  members : ∀ v, v ∈ order ↔ v ∈ live
  fixed : ∀ x ∈ live, ∀ y ∈ live, C.fixed x y = true → arrow C order x y
  noncollider : ∀ x ∈ live, ∀ y ∈ live, ∀ z ∈ live,
    C.noncollider x y z = true → ¬ (arrow C order x y ∧ arrow C order z y)

structure ValidInput (C : Constraints V) : Prop where
  symmetric : ∀ x y, C.adjacent x y = C.adjacent y x
  loopless : ∀ x, C.adjacent x x = false
  fixed_adjacent : ∀ x y, C.fixed x y = true → C.adjacent x y = true

theorem arrow_irrefl (C : Constraints V) (order : List V) (x : V) :
    ¬ arrow C order x x := fun h => Nat.lt_irrefl _ h.2

theorem arrow_direction {C : Constraints V} (input : ValidInput C)
    {order : List V} {x y : V} (hx : x ∈ order) (hy : y ∈ order)
    (adj : C.adjacent x y = true) : arrow C order x y ∨ arrow C order y x := by
  have distinct : x ≠ y := by
    rintro rfl
    simp [input.loopless] at adj
  have different : order.idxOf x ≠ order.idxOf y := by
    intro same
    have xIndex := List.idxOf_lt_length_iff.mpr hx
    have yIndex := List.idxOf_lt_length_iff.mpr hy
    have lookup := congrArg (fun i => order[i]?) same
    rw [List.getElem?_eq_getElem xIndex, List.getElem?_eq_getElem yIndex,
      List.getElem_idxOf xIndex, List.getElem_idxOf yIndex] at lookup
    exact distinct (Option.some.inj lookup)
  rcases Nat.lt_or_gt_of_ne different with before | after
  · exact .inr ⟨input.symmetric y x ▸ adj, before⟩
  · exact .inl ⟨adj, after⟩

private theorem arrow_cons {C : Constraints V} {order : List V} {x y sink : V}
    (xOther : x ≠ sink) (yOther : y ≠ sink) :
    arrow C (sink :: order) x y ↔ arrow C order x y := by
  simp [arrow, List.idxOf_cons, Ne.symm xOther, Ne.symm yOther]

private theorem into_sink {C : Constraints V} {order : List V} {x sink : V}
    (other : x ≠ sink) : arrow C (sink :: order) x sink ↔ C.adjacent x sink = true := by
  simp [arrow, List.idxOf_cons, Ne.symm other]

private theorem no_out_of_sink (C : Constraints V) (order : List V) (x sink : V) :
    ¬ arrow C (sink :: order) sink x := by
  simp [arrow, List.idxOf_cons]

theorem sinkOrder_consistent {C : Constraints V} (input : ValidInput C)
    {live order : List V} (unique : live.Nodup) (valid : SinkOrder C live order) :
    Consistent C live order := by
  refine ⟨nodup_of_sinkOrder valid unique, fun _ => mem_of_sinkOrder valid unique, ?_, ?_⟩
  · induction valid with
    | nil => simp
    | @cons live tail sink _ eligible rest ih =>
      intro x hx y hy fixed
      have outgoing := ((eligible_iff C live sink).mp eligible).1
      have xOther : x ≠ sink := by
        rintro rfl
        exact outgoing y hy fixed
      by_cases yOther : y = sink
      · subst y
        exact into_sink xOther |>.mpr (input.fixed_adjacent _ _ fixed)
      · exact (arrow_cons xOther yOther).mpr
          (ih (unique.erase sink) x (List.mem_erase_of_ne xOther |>.mpr hx)
            y (List.mem_erase_of_ne yOther |>.mpr hy) fixed)
  · induction valid with
    | nil => simp
    | @cons live tail sink _ eligible rest ih =>
      intro x hx y hy z hz forbidden both
      have xOther : x ≠ sink := fun same =>
        no_out_of_sink C tail y sink (same ▸ both.1)
      have zOther : z ≠ sink := fun same =>
        no_out_of_sink C tail y sink (same ▸ both.2)
      by_cases yOther : y = sink
      · subst y
        exact ((eligible_iff C live sink).mp eligible).2 x hx z hz both.1.1 both.2.1 forbidden
      · exact ih (unique.erase sink)
          x (List.mem_erase_of_ne xOther |>.mpr hx)
          y (List.mem_erase_of_ne yOther |>.mpr hy)
          z (List.mem_erase_of_ne zOther |>.mpr hz) forbidden
          ⟨(arrow_cons xOther yOther).mp both.1, (arrow_cons zOther yOther).mp both.2⟩

theorem consistent_sinkOrder {C : Constraints V} (input : ValidInput C)
    {live order : List V} (unique : live.Nodup) (valid : Consistent C live order) :
    SinkOrder C live order := by
  induction order generalizing live with
  | nil =>
    cases live with
    | nil => exact .nil
    | cons x xs => exact (List.not_mem_nil (valid.members x |>.mpr (by simp))).elim
  | cons sink tail ih =>
    have here : sink ∈ live := (valid.members sink).mp (by simp)
    have outside : sink ∉ tail := (List.nodup_cons.mp valid.nodup).1
    have eligible : eligible C live sink = true := by
      apply (eligible_iff C live sink).mpr
      refine ⟨?_, ?_⟩
      · intro x hx fixed
        exact no_out_of_sink C tail x sink (valid.fixed sink here x hx fixed)
      · intro x hx z hz xy zy forbidden
        have xOther : x ≠ sink := by rintro rfl; simp [input.loopless] at xy
        have zOther : z ≠ sink := by rintro rfl; simp [input.loopless] at zy
        exact valid.noncollider x hx sink here z hz forbidden
          ⟨(into_sink xOther).mpr xy, (into_sink zOther).mpr zy⟩
    refine .cons here eligible (ih (unique.erase sink) ⟨(List.nodup_cons.mp valid.nodup).2, ?_, ?_, ?_⟩)
    · intro v
      rw [unique.mem_erase_iff, ← valid.members v, List.mem_cons]
      constructor
      · intro member
        exact ⟨fun same => outside (same ▸ member), .inr member⟩
      · rintro ⟨different, same | member⟩
        · exact (different same).elim
        · exact member
    · intro x hx y hy fixed
      exact (arrow_cons (unique.mem_erase_iff.mp hx).1 (unique.mem_erase_iff.mp hy).1).mp
        (valid.fixed x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy) fixed)
    · intro x hx y hy z hz forbidden both
      exact valid.noncollider x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy)
        z (List.mem_of_mem_erase hz) forbidden
        ⟨(arrow_cons (unique.mem_erase_iff.mp hx).1 (unique.mem_erase_iff.mp hy).1).mpr both.1,
          (arrow_cons (unique.mem_erase_iff.mp hz).1 (unique.mem_erase_iff.mp hy).1).mpr both.2⟩

theorem extend_iff {C : Constraints V} (input : ValidInput C)
    {live : List V} (unique : live.Nodup) :
    (extend C live.length live).isSome = true ↔ ∃ order, Consistent C live order := by
  constructor
  · intro success
    cases result : extend C live.length live with
    | none => simp [result] at success
    | some order => exact ⟨order, sinkOrder_consistent input unique (extend_sound result)⟩
  · rintro ⟨order, valid⟩
    obtain ⟨found, result⟩ := extend_complete unique (Nat.le_refl _) (consistent_sinkOrder input unique valid)
    simp [result]

def requireArrow (C : Constraints V) (u v : V) : Constraints V :=
  { C with fixed := fun x y => C.fixed x y || (x == u && y == v) }

private theorem requireArrow_valid {C : Constraints V} (input : ValidInput C)
    {u v : V} (uv : C.adjacent u v = true) : ValidInput (requireArrow C u v) where
  symmetric := input.symmetric
  loopless := input.loopless
  fixed_adjacent x y h := by
    simp [requireArrow] at h
    rcases h with fixed | ⟨rfl, rfl⟩
    · exact input.fixed_adjacent x y fixed
    · exact uv

theorem trial_iff {C : Constraints V} (input : ValidInput C) {live : List V}
    (unique : live.Nodup) {u v : V} (hu : u ∈ live) (hv : v ∈ live)
    (uv : C.adjacent u v = true) :
    (extend (requireArrow C u v) live.length live).isSome = true ↔
      ∃ order, Consistent C live order ∧ arrow C order u v := by
  rw [extend_iff (requireArrow_valid input uv) unique]
  constructor
  · rintro ⟨order, valid⟩
    exact ⟨order, ⟨valid.nodup, valid.members,
      fun x hx y hy fixed => valid.fixed x hx y hy (by simp [requireArrow, fixed]),
      valid.noncollider⟩, valid.fixed u hu v hv (by simp [requireArrow])⟩
  · rintro ⟨order, valid, edge⟩
    refine ⟨order, ⟨valid.nodup, valid.members, ?_, valid.noncollider⟩⟩
    intro x hx y hy fixed
    simp [requireArrow] at fixed
    rcases fixed with prior | ⟨rfl, rfl⟩
    · exact valid.fixed x hx y hy prior
    · exact edge

/-- A direction is compelled if the opposite trial has no extension. -/
def compelled (C : Constraints V) (live : List V) (u v : V) : Bool :=
  C.adjacent u v && !(extend (requireArrow C v u) live.length live).isSome

theorem compelled_iff {C : Constraints V} (input : ValidInput C) {live : List V}
    (unique : live.Nodup) {u v : V} (hu : u ∈ live) (hv : v ∈ live)
    (adj : C.adjacent u v = true) :
    compelled C live u v = true ↔ ∀ order, Consistent C live order → arrow C order u v := by
  have reverseAdj := input.symmetric v u ▸ adj
  have reverseTrial := trial_iff input unique hv hu reverseAdj
  simp only [compelled, adj, Bool.true_and, Bool.not_eq_true']
  constructor
  · intro failure order valid
    rcases arrow_direction input ((valid.members u).mpr hu) ((valid.members v).mpr hv) adj with forward | back
    · exact forward
    · have success := reverseTrial.mpr ⟨order, valid, back⟩
      rw [failure] at success
      contradiction
  · intro all
    apply Bool.eq_false_iff.mpr
    intro success
    obtain ⟨order, valid, back⟩ := reverseTrial.mp success
    exact Nat.lt_asymm (all order valid).2 back.2

end RpCD.Completion

end
