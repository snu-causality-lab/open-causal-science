module
public import OpenCausalScience.Papers.Richardson2009.HeadTail

/-!
# Barrenness under ancestral closure

Richardson (2009), Proposition 1(i)–(iii). In a finite ADMG every vertex
in a set lies above a barren vertex of the set in directed reachability.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n} {rank : Fin n → Nat}

private theorem ancestry_endpoint {S : VertexMask n} {v : Fin n}
    (route : G.AncestorOf S v) :
    ∃ w, S w = true ∧ G.AncestorOf (· == w) v := by
  induction route with
  | conditioned present => exact ⟨_, present, .conditioned (by simp)⟩
  | parent arrow _ ih =>
    obtain ⟨w, present, path⟩ := ih
    exact ⟨w, present, .parent arrow path⟩

private theorem ancestry_bind {S T : VertexMask n} {v : Fin n} (route : G.AncestorOf S v)
    (replace : ∀ w, S w = true → G.AncestorOf T w) : G.AncestorOf T v := by
  induction route with
  | conditioned present => exact replace _ present
  | parent arrow _ ih => exact .parent arrow ih

private theorem ancestry_singleton_transfer {S : VertexMask n} {u v : Fin n}
    (route : G.AncestorOf (· == v) u) (next : G.AncestorOf S v) : G.AncestorOf S u :=
  ancestry_bind route (fun _ present => (beq_iff_eq.mp present).symm ▸ next)

private theorem rank_lt_or_same (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    {u v : Fin n} (route : G.AncestorOf (· == v) u) : rank u < rank v ∨ u = v := by
  induction route with
  | conditioned present => exact .inr (beq_iff_eq.mp present)
  | parent arrow _ ih =>
    exact .inl (ih.elim (Nat.lt_trans (increases _ _ arrow)) (fun eq => eq ▸ increases _ _ arrow))

private theorem self_in_ancestorsOf {S : VertexMask n} {v : Fin n} (present : S v = true) :
    v ∈ G.ancestorsOf S := mem_ancestorsOf_iff.mpr (.conditioned present)

/-- Proposition 1(i), stated by vertex membership. -/
theorem barren_ancestors_iff (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    (W : List (Fin n)) (v : Fin n) :
    v ∈ G.barren (G.ancestorsOf W.contains) ↔ v ∈ G.barren W := by
  classical
  rw [mem_barren_iff, mem_barren_iff]
  constructor
  · rintro ⟨ancestral, stop⟩
    have member : v ∈ W := by
      by_cases member : v ∈ W
      · exact member
      exfalso
      have absent := member
      obtain ⟨w, hw, path⟩ := ancestry_endpoint (mem_ancestorsOf_iff.mp ancestral)
      have diff : w ≠ v := fun eq => absent (eq ▸ List.contains_iff_mem.mp hw)
      apply stop
      exact ancestry_singleton_transfer path (.conditioned (Bool.and_eq_true_iff.mpr
        ⟨List.contains_iff_mem.mpr (self_in_ancestorsOf hw), by simp [diff]⟩))
    exact ⟨member, fun path => stop (ancestry_bind path fun w present =>
      .conditioned (Bool.and_eq_true_iff.mpr
        ⟨List.contains_iff_mem.mpr (self_in_ancestorsOf (Bool.and_eq_true_iff.mp present).1),
          (Bool.and_eq_true_iff.mp present).2⟩))⟩
  · rintro ⟨member, stop⟩
    refine ⟨self_in_ancestorsOf (List.contains_iff_mem.mpr member), ?_⟩
    intro path
    obtain ⟨w, present, vToW⟩ := ancestry_endpoint path
    have different : w ≠ v := by simpa using (Bool.and_eq_true_iff.mp present).2
    obtain ⟨z, hz, wToZ⟩ := ancestry_endpoint
      (mem_ancestorsOf_iff.mp (List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp present).1))
    have vBelowW := (rank_lt_or_same increases vToW).resolve_right (Ne.symm different)
    have zNotV : z ≠ v := by
      intro eq
      subst z
      rcases rank_lt_or_same increases wToZ with wBelowV | same
      · exact (Nat.not_lt_of_ge (Nat.le_of_lt wBelowV)) vBelowW
      · exact different same
    exact stop (ancestry_singleton_transfer vToW
      (ancestry_singleton_transfer wToZ (.conditioned (Bool.and_eq_true_iff.mpr ⟨hz, by simp [zNotV]⟩))))

/-- The ancestral closure of the barren part is the ancestral closure of
the original set. In particular, this gives Proposition 1(ii) for
ancestral sets. -/
theorem ancestors_barren_iff (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    (W : List (Fin n)) (v : Fin n) :
    v ∈ G.ancestorsOf (G.barren W).contains ↔ v ∈ G.ancestorsOf W.contains := by
  rw [mem_ancestorsOf_iff, mem_ancestorsOf_iff]
  constructor
  · intro path
    exact ancestry_bind path (fun w present => .conditioned
      (List.contains_iff_mem.mpr (mem_barren_iff.mp (List.contains_iff_mem.mp present)).1))
  · intro path
    let candidates := W.filter fun w => (G.ancestorsOf (· == w)).contains v
    obtain ⟨w, present, vToW⟩ := ancestry_endpoint path
    have wCandidate : w ∈ candidates := List.mem_filter.mpr
      ⟨List.contains_iff_mem.mp present, List.contains_iff_mem.mpr (mem_ancestorsOf_iff.mpr vToW)⟩
    obtain ⟨b, barrenCandidate⟩ := List.exists_mem_of_ne_nil _ (barren_nonempty increases
      (List.ne_nil_of_mem wCandidate))
    obtain ⟨candidate, noDescendant⟩ := mem_barren_iff.mp barrenCandidate
    have origin := List.mem_filter.mp candidate
    have vToB := mem_ancestorsOf_iff.mp (List.contains_iff_mem.mp origin.2)
    refine ancestry_singleton_transfer vToB (.conditioned (List.contains_iff_mem.mpr
      (mem_barren_iff.mpr ⟨origin.1, ?_⟩)))
    intro descendant
    obtain ⟨d, valid, bToD⟩ := ancestry_endpoint descendant
    have vToD := ancestry_singleton_transfer vToB bToD
    have dCandidate : d ∈ candidates := List.mem_filter.mpr
      ⟨List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp valid).1,
        List.contains_iff_mem.mpr (mem_ancestorsOf_iff.mpr vToD)⟩
    exact noDescendant (ancestry_singleton_transfer bToD (.conditioned (Bool.and_eq_true_iff.mpr
      ⟨List.contains_iff_mem.mpr dCandidate, (Bool.and_eq_true_iff.mp valid).2⟩)))

/-- Proposition 1(iii). -/
theorem barren_of_subset {V W : List (Fin n)} {v : Fin n}
    (subset : ∀ x ∈ V, x ∈ W) (present : v ∈ V) (barren : v ∈ G.barren W) :
    v ∈ G.barren V := by
  refine mem_barren_iff.mpr ⟨present, fun path => (mem_barren_iff.mp barren).2 ?_⟩
  exact ancestry_bind path (fun w valid => .conditioned (Bool.and_eq_true_iff.mpr
    ⟨List.contains_iff_mem.mpr (subset w (List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp valid).1)),
      (Bool.and_eq_true_iff.mp valid).2⟩))

end
end OpenCausalScience.MixedGraph
