module
public import OpenCausalScience.Papers.Richardson2003.OrderedLocal

/-!
# Recursive head partitions and tails

Richardson, *A factorization criterion for acyclic directed mixed graphs*,
UAI 2009, §§2.2–3.2. Each round takes the barren vertices in each induced
district, then deletes those heads from the remaining set.
-/

namespace OpenCausalScience.MixedGraph

open Papers.TianPearl2003.IdentifyRecurrence (ancestors)
open Papers.TianPearl2003.IdentifyReachability (Reached mem_ancestors_iff)

@[expose] public section

variable {n : Nat} {G : MixedGraph n}

private theorem district_trans {A : VertexMask n} {x y z : Fin n}
    (hxy : y ∈ G.inducedDistrict A x) (hyz : z ∈ G.inducedDistrict A y) :
    z ∈ G.inducedDistrict A x := by
  have walk := mem_inducedDistrict_iff.mp hyz
  clear hyz
  induction walk with
  | seed _ atRoot =>
    obtain rfl := beq_iff_eq.mp atRoot
    exact hxy
  | step _ member edge ih => exact mem_inducedDistrict_step ih (List.mem_filter.mp member).2 edge

private theorem district_symm {A : VertexMask n} {x y : Fin n}
    (hxy : y ∈ G.inducedDistrict A x) : x ∈ G.inducedDistrict A y := by
  have walk := mem_inducedDistrict_iff.mp hxy
  clear hxy
  induction walk with
  | seed member atRoot =>
    obtain rfl := beq_iff_eq.mp atRoot
    exact mem_inducedDistrict_self (List.mem_filter.mp member).2
  | @step a b before member edge ih =>
    have root : b ∈ G.inducedDistrict A b := mem_inducedDistrict_self (List.mem_filter.mp member).2
    have rev : a ∈ G.inducedDistrict A b :=
      mem_inducedDistrict_step root (List.mem_filter.mp before.in_current).2
        ((G.symmetric _ _ _ _).symm.trans edge)
    exact district_trans rev ih

/-- The canonical enumerations are equal when their roots are in the same district. -/
theorem inducedDistrict_eq_of_mem {A : VertexMask n} {x y : Fin n}
    (hxy : y ∈ G.inducedDistrict A x) : G.inducedDistrict A x = G.inducedDistrict A y := by
  have same : ∀ z, z ∈ G.inducedDistrict A x ↔ z ∈ G.inducedDistrict A y :=
    fun z => ⟨district_trans (district_symm hxy), district_trans hxy⟩
  apply List.filter_congr
  intro v hv
  let W := (List.finRange n).filter A
  let visited z := Papers.TianPearl2003.IdentifyRecurrence.close
    (fun u w => G.edge u true w true) W (W.filter (· == z)) W.length
  have checked (z : Fin n) :
      v ∈ G.inducedDistrict A z ↔ (visited z).contains v = true :=
    List.mem_filter.trans (and_iff_right hv)
  exact Bool.eq_iff_iff.mpr ((checked x).symm.trans ((same v).trans (checked y)))

/-- Full-graph directed ancestors, including the seeds. -/
def ancestorsOf (G : MixedGraph n) (S : VertexMask n) : List (Fin n) :=
  ancestors G (List.finRange n) ((List.finRange n).filter S)

theorem mem_ancestorsOf_iff {S : VertexMask n} {v : Fin n} :
    v ∈ G.ancestorsOf S ↔ G.AncestorOf S v := by
  rw [ancestorsOf, mem_ancestors_iff]
  constructor
  · intro reached
    induction reached with
    | seed _ atRoot => exact .conditioned (List.mem_filter.mp (List.contains_iff_mem.mp atRoot)).2
    | step _ _ arrow ih => exact .parent arrow ih
  · intro path
    induction path with
    | conditioned present =>
      exact .seed (List.mem_finRange _) (List.contains_iff_mem.mpr (List.mem_filter.mpr
        ⟨List.mem_finRange _, present⟩))
    | parent arrow _ ih => exact .step ih (List.mem_finRange _) arrow

/-- Barren vertices have no strict directed descendant in the listed set.
The ancestry test stays in the full graph. -/
def barren (G : MixedGraph n) (D : List (Fin n)) : List (Fin n) :=
  D.filter fun u => !(G.ancestorsOf (fun v => D.contains v && v != u)).contains u

theorem mem_barren_iff {D : List (Fin n)} {v : Fin n} :
    v ∈ G.barren D ↔ v ∈ D ∧
      ¬ G.AncestorOf (fun w => D.contains w && w != v) v := by
  simp [barren, mem_ancestorsOf_iff]

private theorem rank_of_ancestry {rank : Fin n → Nat}
    (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {S : VertexMask n} {v : Fin n} (path : G.AncestorOf S v) :
    (∃ w, S w = true ∧ rank v < rank w) ∨ S v = true := by
  induction path with
  | conditioned present => exact .inr present
  | @parent u v arrow _ ih =>
    rcases ih with ⟨w, present, bigger⟩ | present
    · exact .inl ⟨w, present, Nat.lt_trans (increases _ _ arrow) bigger⟩
    · exact .inl ⟨v, present, increases _ _ arrow⟩

private theorem max_rank (rank : Fin n → Nat) (L : List (Fin n)) (nonempty : L ≠ []) :
    ∃ x ∈ L, ∀ v ∈ L, rank v ≤ rank x := by
  induction L with
  | nil => contradiction
  | cons a rest ih =>
    by_cases empty : rest = []
    · subst rest
      exact ⟨a, by simp, fun v h => by simp at h; subst v; exact Nat.le_refl _⟩
    · obtain ⟨x, mem, le⟩ := ih empty
      by_cases isMax : rank a ≤ rank x
      · exact ⟨x, by simp [mem], fun v hv =>
          (List.mem_cons.mp hv).elim (fun same => same ▸ isMax) (le v)⟩
      · have top : rank x ≤ rank a := Nat.le_of_lt (Nat.lt_of_not_ge isMax)
        exact ⟨a, by simp, fun v hv => (List.mem_cons.mp hv).elim
          (fun same => same ▸ Nat.le_refl _) (fun m => Nat.le_trans (le v m) top)⟩

theorem barren_nonempty {rank : Fin n → Nat}
    (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {D : List (Fin n)} (nonempty : D ≠ []) : G.barren D ≠ [] := by
  obtain ⟨x, mem, greatest⟩ := max_rank rank D nonempty
  have barren : x ∈ G.barren D := mem_barren_iff.mpr ⟨mem, by
    intro path
    rcases rank_of_ancestry increases path with ⟨w, mark, lt⟩ | mark
    · exact (Nat.not_lt_of_ge (greatest w (List.contains_iff_mem.mp
        (Bool.and_eq_true_iff.mp mark).1))) lt
    · simp at mark⟩
  exact List.ne_nil_of_mem barren

def headAt (G : MixedGraph n) (W : List (Fin n)) (v : Fin n) : List (Fin n) :=
  G.barren (G.inducedDistrict W.contains v)

theorem headAt_subset {W : List (Fin n)} {x v : Fin n}
    (member : v ∈ G.headAt W x) : v ∈ W :=
  List.contains_iff_mem.mp (inducedDistrict_inside (mem_barren_iff.mp member).1)

private theorem heads_equal_of_overlap {W : List (Fin n)} {x y v : Fin n}
    (hx : v ∈ G.headAt W x) (hy : v ∈ G.headAt W y) :
    G.headAt W x = G.headAt W y := by
  unfold headAt
  rw [inducedDistrict_eq_of_mem (mem_barren_iff.mp hx).1,
    inducedDistrict_eq_of_mem (mem_barren_iff.mp hy).1]

/-- One copy of each nonempty barren part of an induced district. -/
def headRound (G : MixedGraph n) (W : List (Fin n)) : List (List (Fin n)) :=
  ((W.map (G.headAt W)).filter (!·.isEmpty)).eraseDups

private theorem mem_headRound_iff {W H : List (Fin n)} :
    H ∈ G.headRound W ↔ ∃ x ∈ W, H = G.headAt W x ∧ H ≠ [] := by
  rw [headRound, List.mem_eraseDups, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨x, member, same⟩, nonempty⟩
    exact ⟨x, member, same.symm, by intro empty; simp [empty] at nonempty⟩
  · rintro ⟨x, member, same, nonempty⟩
    exact ⟨⟨x, member, same.symm⟩, by cases H <;> simp_all⟩

/-- Distinct heads in the same round are disjoint. -/
theorem headRound_disjoint {W H K : List (Fin n)}
    (first : H ∈ G.headRound W) (second : K ∈ G.headRound W)
    {v : Fin n} (inH : v ∈ H) (inK : v ∈ K) : H = K := by
  obtain ⟨x, _, rfl, _⟩ := mem_headRound_iff.mp first
  obtain ⟨y, _, rfl, _⟩ := mem_headRound_iff.mp second
  exact heads_equal_of_overlap inH inK

theorem headRound_has_head {rank : Fin n → Nat}
    (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {W : List (Fin n)} (nonempty : W ≠ []) :
    ∃ H ∈ G.headRound W, H ≠ [] := by
  obtain ⟨x, member⟩ := List.exists_mem_of_ne_nil W nonempty
  have start : x ∈ G.inducedDistrict W.contains x :=
    mem_inducedDistrict_self (List.contains_iff_mem.mpr member)
  have present : G.headAt W x ≠ [] :=
    barren_nonempty increases (List.ne_nil_of_mem start)
  exact ⟨_, mem_headRound_iff.mpr ⟨x, member, rfl, present⟩, present⟩

def removeHeads (G : MixedGraph n) (W : List (Fin n)) : List (Fin n) :=
  W.filter fun v => !(G.headRound W).any (·.contains v)

@[simp] theorem mem_removeHeads_iff {W : List (Fin n)} {v : Fin n} :
    v ∈ G.removeHeads W ↔ v ∈ W ∧ ∀ H ∈ G.headRound W, v ∉ H := by
  simp [removeHeads]

theorem headRound_subset {W H : List (Fin n)} {v : Fin n} (first : H ∈ G.headRound W)
    (member : v ∈ H) : v ∈ W := by
  obtain ⟨x, _, rfl, _⟩ := mem_headRound_iff.mp first
  exact headAt_subset member

private theorem removeHeads_length_lt {rank : Fin n → Nat}
    (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {W : List (Fin n)} (nonempty : W ≠ []) : (G.removeHeads W).length < W.length := by
  have sub : (G.removeHeads W).Sublist W := List.filter_sublist
  apply Nat.lt_of_le_of_ne sub.length_le
  intro equal
  obtain ⟨H, inRound, present⟩ := headRound_has_head increases nonempty
  obtain ⟨x, inH⟩ := List.exists_mem_of_ne_nil H present
  have inW := headRound_subset inRound inH
  have left : x ∈ G.removeHeads W := (sub.eq_of_length equal).symm ▸ inW
  exact (mem_removeHeads_iff.mp left).2 H inRound inH

def headRounds (G : MixedGraph n) (W : List (Fin n)) : Nat → List (List (Fin n))
  | 0 => []
  | k + 1 => G.headRound W ++ G.headRounds (G.removeHeads W) k

def headPartition (G : MixedGraph n) (W : List (Fin n)) : List (List (Fin n)) :=
  G.headRounds W W.length

private theorem headRounds_cover {rank : Fin n → Nat}
    (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {fuel : Nat} {W : List (Fin n)} (bound : W.length ≤ fuel)
    (v : Fin n) : (∃ H ∈ G.headRounds W fuel, v ∈ H) ↔ v ∈ W := by
  induction fuel generalizing W with
  | zero =>
    have empty : W = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bound)
    simp [headRounds, empty]
  | succ fuel ih =>
    by_cases empty : W = []
    · subst W
      simp [headRounds, headRound, removeHeads, (ih (by simp : ([] : List (Fin n)).length ≤ fuel))]
    · have nextBound : (G.removeHeads W).length ≤ fuel := by
        have lt := removeHeads_length_lt increases empty
        omega
      simp only [headRounds, List.mem_append]
      constructor
      · rintro ⟨H, here | later, member⟩
        · exact headRound_subset here member
        · exact (mem_removeHeads_iff.mp ((ih nextBound).mp ⟨H, later, member⟩)).1
      · intro member
        classical
        by_cases here : ∃ H ∈ G.headRound W, v ∈ H
        · obtain ⟨H, row, inH⟩ := here
          exact ⟨H, .inl row, inH⟩
        · have next : v ∈ G.removeHeads W :=
            mem_removeHeads_iff.mpr ⟨member, fun H h r => here ⟨H, h, r⟩⟩
          obtain ⟨H, later, inH⟩ := (ih nextBound).mpr next
          exact ⟨H, .inr later, inH⟩

theorem headPartition_cover {rank : Fin n → Nat}
    (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    (W : List (Fin n)) (v : Fin n) : (∃ H ∈ G.headPartition W, v ∈ H) ↔ v ∈ W :=
  headRounds_cover increases (Nat.le_refl _) v

private theorem headRounds_subset {fuel : Nat} {W H : List (Fin n)} {v : Fin n}
    (h : H ∈ G.headRounds W fuel) (member : v ∈ H) : v ∈ W := by
  induction fuel generalizing W with
  | zero => simp [headRounds] at h
  | succ fuel ih =>
    rcases List.mem_append.mp h with here | later
    · exact headRound_subset here member
    · exact (mem_removeHeads_iff.mp (ih later)).1

/-- The first round that supplies a vertex is unique, and its head is unique. -/
theorem headPartition_disjoint {W H K : List (Fin n)} {v : Fin n}
    (first : H ∈ G.headPartition W) (second : K ∈ G.headPartition W)
    (inH : v ∈ H) (inK : v ∈ K) : H = K := by
  have aux (fuel : Nat) (W : List (Fin n))
      (f : H ∈ G.headRounds W fuel) (s : K ∈ G.headRounds W fuel) : H = K := by
    induction fuel generalizing W with
    | zero => simp [headRounds] at f
    | succ fuel ih =>
      rcases List.mem_append.mp f with here | later <;>
        rcases List.mem_append.mp s with there | after
      · exact headRound_disjoint here there inH inK
      · exact ((mem_removeHeads_iff.mp (headRounds_subset after inK)).2 _ here inH).elim
      · exact ((mem_removeHeads_iff.mp (headRounds_subset later inH)).2 _ there inK).elim
      · exact ih _ later after
  exact aux _ _ first second

/-- The conditioning set for a nonempty head is the rest of its ancestral
district and all parents of that district. -/
def headTail (G : MixedGraph n) (H : List (Fin n)) : List (Fin n) :=
  let A := G.ancestorsOf H.contains
  let D := match H with
    | [] => []
    | h :: _ => G.inducedDistrict A.contains h
  (List.finRange n).filter fun v =>
    (D.contains v && !H.contains v) || D.any (fun w => G.edge v false w true)

end
end OpenCausalScience.MixedGraph
