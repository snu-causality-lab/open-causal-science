module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyReachability

/-! # Recanting districts

Shpitser (2013), Definition 2. A recanting district contains the first
successors of two proper paths from the same treatment, with one path
selected and the other excluded. The two successors can coincide.
Source: https://doi.org/10.1111/cogs.12058
-/

namespace OpenCausalScience.Papers.Shpitser2013.RecantingDistrict

open TianPearl2003.IdentifyRecurrence (Vertices ancestors district)
open TianPearl2003.IdentifyReachability (Reached mem_ancestors_iff mem_district_iff)

@[expose] public section

variable {n : Nat}

/-- The path selector reads the treatment, its first successor, and the rest of the path. -/
abbrev PathSelection (n : Nat) := Fin n → Fin n → Vertices n → Bool

def untreated (treatments : Vertices n) : Vertices n :=
  (List.finRange n).filter fun v => !treatments.contains v

def ancestralRegion (G : MixedGraph n) (treatments outcomes : Vertices n) : Vertices n :=
  ancestors G (untreated treatments) outcomes

theorem mem_ancestralRegion_iff (G : MixedGraph n) (treatments outcomes : Vertices n) (v : Fin n) :
    v ∈ ancestralRegion G treatments outcomes ↔
      Reached (fun u w => G.edge w false u true) (untreated treatments) outcomes.contains v :=
  mem_ancestors_iff G (untreated treatments) outcomes v

/-- A directed continuation to an outcome within the available vertices.
The first vertex is indexed separately from the remaining path. The
treatment-removed vertex list has no duplicates, so erasing the first
vertex at each step prevents repetition. -/
inductive Suffix (G : MixedGraph n) (outcomes : Vertices n) :
    Vertices n → Fin n → Vertices n → Prop
  | stop {available v} : v ∈ available → v ∈ outcomes → Suffix G outcomes available v []
  | step {available v w tail} : v ∈ available → G.edge v false w true = true →
      Suffix G outcomes (available.erase v) w tail → Suffix G outcomes available v (w :: tail)

private theorem suffix_length_lt {G : MixedGraph n} {outcomes available tail : Vertices n}
    {v : Fin n} (route : Suffix G outcomes available v tail) : tail.length < available.length := by
  induction route with
  | @stop available v here _ =>
    have nonempty := List.ne_nil_of_mem here
    cases available with
    | nil => contradiction
    | cons => simp
  | step here _ _ ih =>
    rw [List.length_erase_of_mem here] at ih
    simp only [List.length_cons]
    omega

def suffixes (G : MixedGraph n) (outcomes : Vertices n) : Nat →
    Vertices n → Fin n → List (Vertices n)
  | 0, _, _ => []
  | fuel + 1, available, v =>
    if available.contains v then
      (if outcomes.contains v then [[]] else []) ++
        (List.finRange n).flatMap fun w =>
          if G.edge v false w true then
            (suffixes G outcomes fuel (available.erase v) w).map (w :: ·)
          else []
    else []

theorem mem_suffixes_iff (G : MixedGraph n) (outcomes : Vertices n) (fuel : Nat)
    (available : Vertices n) (v : Fin n) (tail : Vertices n) :
    tail ∈ suffixes G outcomes fuel available v ↔
      Suffix G outcomes available v tail ∧ tail.length < fuel := by
  induction fuel generalizing available v tail with
  | zero => simp [suffixes]
  | succ fuel ih =>
    by_cases here : v ∈ available
    · have present := List.contains_iff_mem.mpr here
      simp only [suffixes, present, ite_true, List.mem_append, List.mem_flatMap]
      constructor
      · rintro (stop | ⟨w, _, next⟩)
        · simp at stop
          obtain ⟨outcome, rfl⟩ := stop
          exact ⟨.stop here outcome, by simp⟩
        · by_cases edge : G.edge v false w true = true
          · simp only [edge, ite_true, List.mem_map] at next
            obtain ⟨rest, found, rfl⟩ := next
            have ⟨route, within⟩ := (ih _ _ _).mp found
            exact ⟨.step here edge route, by simpa using Nat.succ_lt_succ within⟩
          · simp [Bool.not_eq_true _ ▸ edge] at next
      · rintro ⟨route, within⟩
        cases route with
        | stop _ outcome =>
          exact Or.inl (by simpa using outcome)
        | @step _ _ w rest _ edge route =>
          refine Or.inr ⟨w, List.mem_finRange w, ?_⟩
          simp only [edge, ite_true, List.mem_map]
          exact ⟨rest, (ih _ _ _).mpr ⟨route, Nat.lt_of_succ_lt_succ within⟩, rfl⟩
    · have absent : ¬available.contains v = true := fun h => here (List.contains_iff_mem.mp h)
      simp only [suffixes, show available.contains v = false from Bool.not_eq_true _ ▸ absent, Bool.false_eq_true, ite_false, List.not_mem_nil, false_iff]
      rintro ⟨route, _⟩
      cases route <;> contradiction

/-- Proper directed paths from a treatment with a given first successor. -/
def ProperPath (G : MixedGraph n) (treatments outcomes : Vertices n)
    (source first : Fin n) (tail : Vertices n) : Prop :=
  source ∈ treatments ∧ G.edge source false first true = true ∧
    Suffix G outcomes (untreated treatments) first tail

/-- Definition 2, represented by the two first successors and a bidirected
connection within the outcome's ancestral region. -/
def Recants (G : MixedGraph n) (treatments outcomes : Vertices n)
    (selected : PathSelection n) : Prop :=
  ∃ source first, first ∈ ancestralRegion G treatments outcomes ∧
    (∃ tail, ProperPath G treatments outcomes source first tail ∧ selected source first tail = true) ∧
    ∃ other,
      Reached (fun v w => G.edge v true w true) (ancestralRegion G treatments outcomes)
        (· == first) other ∧
      ∃ tail, ProperPath G treatments outcomes source other tail ∧ selected source other tail = false

def existsPath (G : MixedGraph n) (treatments outcomes : Vertices n)
    (pathTest : PathSelection n) (source first : Fin n) : Bool :=
  let available := untreated treatments
  G.edge source false first true &&
    (suffixes G outcomes available.length available first).any (pathTest source first)

private theorem existsPath_iff {G : MixedGraph n} {treatments outcomes : Vertices n}
    {pathTest : PathSelection n} {source first : Fin n} (treated : source ∈ treatments) :
    existsPath G treatments outcomes pathTest source first = true ↔
      ∃ tail, ProperPath G treatments outcomes source first tail ∧ pathTest source first tail = true := by
  simp only [existsPath, Bool.and_eq_true, List.any_eq_true, mem_suffixes_iff, ProperPath]
  constructor
  · rintro ⟨edge, tail, ⟨route, _⟩, yes⟩
    exact ⟨tail, ⟨treated, edge, route⟩, yes⟩
  · rintro ⟨tail, ⟨_, edge, route⟩, yes⟩
    exact ⟨edge, tail, ⟨route, suffix_length_lt route⟩, yes⟩

def recants (G : MixedGraph n) (treatments outcomes : Vertices n)
    (selected : PathSelection n) : Bool :=
  let live := ancestralRegion G treatments outcomes
  treatments.any fun source => live.any fun first =>
    existsPath G treatments outcomes selected source first &&
      (district G live first).any fun other =>
        existsPath G treatments outcomes (fun a b tail => !selected a b tail) source other

theorem recants_eq_true_iff (G : MixedGraph n) (treatments outcomes : Vertices n)
    (selected : PathSelection n) : recants G treatments outcomes selected = true ↔
      Recants G treatments outcomes selected := by
  simp only [recants, Recants, List.any_eq_true, Bool.and_eq_true, mem_district_iff]
  constructor
  · rintro ⟨source, treated, first, live, active, other, connected, baseline⟩
    obtain ⟨tail, proper, excluded⟩ := (existsPath_iff (pathTest := fun a b tail => !selected a b tail) treated).mp baseline
    exact ⟨source, first, live, (existsPath_iff treated).mp active, other, connected, tail,
      proper, (Bool.not_eq_true' _ ▸ excluded)⟩
  · rintro ⟨source, first, live, ⟨activeTail, active, chosen⟩, other, connected, tail, proper,
      excluded⟩
    have treated := active.1
    exact ⟨source, treated, first, live, (existsPath_iff treated).mpr ⟨activeTail, active, chosen⟩,
      other, connected, (existsPath_iff (pathTest := fun a b tail => !selected a b tail) treated).mpr
        ⟨tail, proper, (Bool.not_eq_true' _).symm ▸ excluded⟩⟩

end
end OpenCausalScience.Papers.Shpitser2013.RecantingDistrict
