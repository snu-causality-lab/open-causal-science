module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDLemma5

/-!
Maier, Marazopoulou and Jensen, Definition 4.3, Definition 4.4 and Appendix C, Lemma C.1.
https://arxiv.org/pdf/1302.4381v3#page=45
Lee and Honavar, AAAI 2016, adopt these schema and terminal-set semantics.
-/

@[expose] public section

namespace RCDPathValidity

open RCDLemma5

/-- Schemas with distinct entity roles, as assumed by RCD-Light. -/
structure Schema (K : Type) where
  entity : K → Prop
  role : K → K → Prop
  many : K → K → Prop
  role_types : ∀ {r e}, role r e → ¬ entity r ∧ entity e
  at_least_two_roles : ∀ r, ¬ entity r → ∃ e f, e ≠ f ∧ role r e ∧ role r f
  finite_roles : ∀ r, ∃ classes : List K, ∀ e, role r e → e ∈ classes

variable {K : Type} {S : Schema K}

def Schema.adj (S : Schema K) (a b : K) : Prop := S.role a b ∨ S.role b a

def Schema.retrace (S : Schema K) (r e : K) : Prop := S.role r e ∧ S.many r e

theorem Schema.symm (S : Schema K) {a b : K} (h : S.adj a b) : S.adj b a := h.symm

/-- A finite typed incidence skeleton with single roles and relationship tuple identity. -/
structure Skeleton (S : Schema K) where
  Item : Type
  kind : Item → K
  present : Item → Prop
  edge : Item → Item → Prop
  finite : ∃ items : List Item, ∀ u, present u → u ∈ items
  symmetric : ∀ {u v}, edge u v → edge v u
  typed : ∀ {u v}, edge u v → S.adj (kind u) (kind v)
  endpoints_present : ∀ {u v}, edge u v → present u ∧ present v
  complete : ∀ r e, present r → S.role (kind r) e → ∃ u, edge r u ∧ kind u = e
  unique_role : ∀ {r u v}, S.role (kind r) (kind u) → kind u = kind v →
    edge r u → edge r v → u = v
  cardinality_one : ∀ {e r s}, S.role (kind r) (kind e) → kind r = kind s →
    ¬ S.many (kind r) (kind e) → edge e r → edge e s → r = s
  tuple_identity : ∀ {r s}, present r → present s → ¬ S.entity (kind r) → kind r = kind s →
    (∀ u, edge r u ↔ edge s u) → r = s

/-- At each step the entire previous frontier history is removed, as in Definition 4.4. -/
def next (g : Skeleton S) (k : K) (seen frontier : g.Item → Prop) (u : g.Item) : Prop :=
  g.kind u = k ∧ (∃ v, frontier v ∧ g.edge v u) ∧ ¬ seen u

def run (g : Skeleton S) : List K → (g.Item → Prop) → (g.Item → Prop) → g.Item → Prop
  | [], _, frontier => frontier
  | k :: ks, seen, frontier =>
      let reach := next g k seen frontier
      run g ks (fun u => seen u ∨ reach u) reach

def Terminal (g : Skeleton S) (w : List K) (base finish : g.Item) : Prop :=
  ∃ k ks, w = k :: ks ∧ g.present base ∧ g.kind base = k ∧
    run g ks (· = base) (· = base) finish

def HasTerminal (S : Schema K) (w : List K) : Prop :=
  ∃ (g : Skeleton S) (base finish : g.Item), Terminal g w base finish

/-- List of traversed edges, with the first item supplied separately. -/
def Chain (e : I → I → Prop) (base : I) : List I → Prop
  | [] => True
  | next :: tail => e base next ∧ Chain e next tail

private theorem trace_of_run (g : Skeleton S) {ks : List K}
    {seen frontier : g.Item → Prop} {finish : g.Item}
    (h : run g ks seen frontier finish) :
    ∃ base trail, frontier base ∧ Chain g.edge base trail ∧
      trail.map g.kind = ks ∧ (base :: trail).getLast? = some finish ∧
      trail.Nodup ∧ (∀ u ∈ trail, ¬ seen u) := by
  induction ks generalizing seen frontier with
  | nil => exact ⟨finish, [], h, trivial, rfl, rfl, by simp, by simp⟩
  | cons k ks ih =>
    have h' : run g ks (fun u => seen u ∨ next g k seen frontier u)
        (next g k seen frontier) finish := h
    obtain ⟨near, trail, hn, walk, types, ends, nd, avoid⟩ := ih h'
    obtain ⟨nearType, ⟨base, prior, edge⟩, notSeen⟩ := hn
    refine ⟨base, near :: trail, prior, ⟨edge, walk⟩, by simp [nearType, types], ?_, ?_, ?_⟩
    · simpa using ends
    · exact List.nodup_cons.mpr ⟨fun mem => avoid near mem (.inr ⟨nearType, ⟨base, prior, edge⟩,
        notSeen⟩), nd⟩
    · intro u mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact notSeen
      · exact fun hist => avoid _ mem (.inl hist)

theorem trace_of_terminal {g : Skeleton S} {w : List K} {base finish : g.Item}
    (h : Terminal g w base finish) :
    ∃ trail, Chain g.edge base trail ∧ (base :: trail).map g.kind = w ∧
      (base :: trail).getLast? = some finish ∧ (base :: trail).Nodup := by
  obtain ⟨k, ks, rfl, _, baseType, hRun⟩ := h
  obtain ⟨_, trail, rfl, chain, kinds, last, distinct, avoid⟩ := trace_of_run g hRun
  exact ⟨trail, chain, by simp [baseType, kinds], last,
    List.nodup_cons.mpr ⟨fun mem => avoid _ mem rfl, distinct⟩⟩

private theorem chain_finish_present {g : Skeleton S} {base finish : g.Item}
    {trail : List g.Item} (start : g.present base) (walk : Chain g.edge base trail)
    (last : (base :: trail).getLast? = some finish) : g.present finish := by
  induction trail generalizing base with
  | nil =>
    have same : base = finish := by simpa using last
    exact same ▸ start
  | cons next tail ih =>
    exact ih (g.endpoints_present walk.1).2 walk.2 (by simpa using last)

/-- Both terminal endpoints are actual items with the beginning and ending
classes of their word. -/
theorem terminal_endpoints {g : Skeleton S} {w : List K} {base finish : g.Item}
    (h : Terminal g w base finish) : g.present base ∧ g.present finish ∧
      w.head? = some (g.kind base) ∧ w.getLast? = some (g.kind finish) := by
  obtain ⟨trail, chain, labels, last, _⟩ := trace_of_terminal h
  obtain ⟨_, _, _, present, _, _⟩ := h
  refine ⟨present, chain_finish_present present chain last, ?_, ?_⟩
  · rw [← labels]
    rfl
  · rw [← labels, List.getLast?_map, last]
    rfl

private theorem run_of_ranked_chain {g : Skeleton S} (rank : g.Item → Nat)
    (boundedEdges : ∀ {u v}, g.edge u v → rank v ≤ rank u + 1)
    {base finish : g.Item} {trail : List g.Item} {seen frontier : g.Item → Prop}
    (walk : Chain g.edge base trail)
    (increases : Chain (fun u v => rank v = rank u + 1) base trail)
    (last : (base :: trail).getLast? = some finish) (baseFrontier : frontier base)
    (priorRanks : ∀ u, seen u → rank u ≤ rank base)
    (frontierSeen : ∀ u, frontier u → seen u) :
    run g (trail.map g.kind) seen frontier finish := by
  induction trail generalizing base seen frontier with
  | nil =>
    have atBase : base = finish := by simpa using last
    exact atBase ▸ baseFrontier
  | cons b trail ih =>
    let reached := next g (g.kind b) seen frontier
    have reaches : reached b :=
      ⟨rfl, ⟨base, baseFrontier, walk.1⟩, fun seenB => by
        have before := priorRanks b seenB
        have one := increases.1
        omega⟩
    have newBound : ∀ u, seen u ∨ reached u → rank u ≤ rank b := by
      intro u reachedU
      have one := increases.1
      rcases reachedU with before | ⟨_, ⟨v, fromFrontier, edge⟩, _⟩
      · have bound := priorRanks u before
        omega
      · have bound := priorRanks v (frontierSeen v fromFrontier)
        have next := boundedEdges edge
        omega
    exact ih walk.2 increases.2 (by simpa using last) reaches newBound (fun _ => Or.inr)

/-- A chain whose distance increases by one at each step survives every
earlier bridge-burning frontier, even when other branches share its types. -/
theorem terminal_of_ranked_chain {g : Skeleton S} (rank : g.Item → Nat)
    (boundedEdges : ∀ {u v}, g.edge u v → rank v ≤ rank u + 1)
    {base finish : g.Item} {trail : List g.Item} (basePresent : g.present base)
    (walk : Chain g.edge base trail)
    (increases : Chain (fun u v => rank v = rank u + 1) base trail)
    (last : (base :: trail).getLast? = some finish) :
    Terminal g ((base :: trail).map g.kind) base finish :=
  ⟨g.kind base, trail.map g.kind, rfl, basePresent, rfl,
    run_of_ranked_chain rank boundedEdges walk increases last rfl
      (fun _ same => by simpa only [same] using Nat.le_refl (rank base)) (fun _ => id)⟩

private theorem local_of_trace {g : Skeleton S} {base : g.Item} {trail : List g.Item}
    (walk : Chain g.edge base trail) (distinct : (base :: trail).Nodup) :
    Local S.adj S.retrace ((base :: trail).map g.kind) := by
  induction trail generalizing base with
  | nil => trivial
  | cons b rest ih =>
    cases rest with
    | nil => exact g.typed walk.1
    | cons c rest =>
      refine ⟨g.typed walk.1, ?_, ih walk.2 (List.nodup_cons.mp distinct).2⟩
      by_cases eq : g.kind base = g.kind c
      · refine Or.inr ?_
        have ne : base ≠ c := fun same => (List.nodup_cons.mp distinct).1 (by simp [same])
        rcases g.typed walk.1 with role | role
        · refine ⟨role, ?_⟩
          exact Classical.byContradiction fun noMany => ne
            (g.cardinality_one role eq noMany (g.symmetric walk.1) walk.2.1)
        · exact (ne (g.unique_role role eq (g.symmetric walk.1) walk.2.1)).elim
      · exact .inl eq

/-- Appendix C, Lemma C.1, necessity, including all participation conditions. -/
theorem local_of_terminal {g : Skeleton S} {w : List K} {base finish : g.Item}
    (h : Terminal g w base finish) : w ≠ [] ∧ Local S.adj S.retrace w := by
  obtain ⟨k, ks, rfl, _, baseType, hRun⟩ := h
  obtain ⟨b, trail, rfl, walk, types, _, nd, avoid⟩ := trace_of_run g hRun
  have distinct : (b :: trail).Nodup := List.nodup_cons.mpr ⟨fun mem => avoid _ mem rfl, nd⟩
  exact ⟨by simp, by simpa [baseType, types] using local_of_trace walk distinct⟩

/-- Bridge burning excludes the canonical item from all non-canonical terminal sets. -/
theorem noncanonical_excludes_base {g : Skeleton S} {w : List K} {base : g.Item}
    (h : Terminal g w base base) : w = [g.kind base] := by
  obtain ⟨k, ks, rfl, _, baseType, hRun⟩ := h
  obtain ⟨b, trail, rfl, _, types, ended, _, avoid⟩ := trace_of_run g hRun
  have nil : trail = [] := by
    cases trail with
    | nil => rfl
    | cons a rest =>
      have ends : (a :: rest).getLast? = some b := by simpa using ended
      obtain ⟨before, same⟩ := List.getLast?_eq_some_iff.mp ends
      exact (avoid _ (by rw [same]; simp) rfl).elim
  simp [nil] at types
  simp [types, baseType]

private theorem local_tail {adj retrace : K → K → Prop} {a : K} {tail : List K}
    (h : Local adj retrace (a :: tail)) : Local adj retrace tail := by
  cases tail with
  | nil => trivial
  | cons b rest =>
    cases rest with
    | nil => trivial
    | cons c rest => exact h.2.2

theorem adj_at {adj retrace : K → K → Prop} {w : List K}
    (h : Local adj retrace w) (i : Nat) (hi : i + 1 < w.length) :
    adj w[i] w[i + 1] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a tail ih =>
    cases i with
    | zero =>
      cases tail with
      | nil => simp at hi
      | cons b rest =>
        cases rest with
        | nil => exact h
        | cons c rest => exact h.1
    | succ i =>
      have hTail : i + 1 < tail.length := by simp at hi; omega
      simp only [List.getElem_cons_succ]
      exact ih (local_tail h) i hTail

theorem turn_at {adj retrace : K → K → Prop} {w : List K}
    (h : Local adj retrace w) (i : Nat) (hi : i + 2 < w.length) :
    w[i] ≠ w[i + 2] ∨ retrace w[i] w[i + 1] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a tail ih =>
    cases i with
    | zero =>
      cases tail with
      | nil => simp at hi
      | cons b rest =>
        cases rest with
        | nil => simp at hi
        | cons c rest => exact h.2.1
    | succ i =>
      have hTail : i + 2 < tail.length := by simp at hi; omega
      simp only [List.getElem_cons_succ]
      exact ih (local_tail h) i hTail

abbrev Position (w : List K) := Fin w.length
abbrev LineItem (w : List K) := Position w ⊕ (Position w × K)

def neighboring {w : List K} (i j : Position w) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

def missing (S : Schema K) (w : List K) (i : Position w) (e : K) : Prop :=
  S.role w[i.val] e ∧ ¬ ∃ j : Position w, neighboring i j ∧ w[j.val] = e

def lineKind (w : List K) : LineItem w → K
  | .inl i => w[i.val]
  | .inr (_, e) => e

def linePresent (S : Schema K) (w : List K) : LineItem w → Prop
  | .inl _ => True
  | .inr (i, e) => missing S w i e

def lineEdge (S : Schema K) (w : List K) : LineItem w → LineItem w → Prop
  | .inl i, .inl j => neighboring i j
  | .inl i, .inr (j, e) => i = j ∧ missing S w j e
  | .inr (j, e), .inl i => i = j ∧ missing S w j e
  | .inr _, .inr _ => False

theorem line_finite (S : Schema K) (w : List K) :
    ∃ items : List (LineItem w), ∀ u, linePresent S w u → u ∈ items := by
  classical
  let roles (j : Position w) := (S.finite_roles w[j.val]).choose
  refine ⟨(List.finRange w.length).map Sum.inl ++
    (List.finRange w.length).flatMap (fun j => (roles j).map (fun e => Sum.inr (j,e))), ?_⟩
  intro u h
  cases u with
  | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  | inr leaf =>
    obtain ⟨i, e⟩ := leaf
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_map.mpr ⟨e, (S.finite_roles w[i.val]).choose_spec e h.1, rfl⟩⟩)

theorem line_symmetric {w : List K} {u v : LineItem w} (h : lineEdge S w u v) :
    lineEdge S w v u := by
  cases u <;> cases v
  · exact h.symm
  · exact h
  · exact h
  · exact h

theorem line_typed {w : List K} (localWord : Local S.adj S.retrace w)
    {u v : LineItem w} (h : lineEdge S w u v) :
    S.adj (lineKind w u) (lineKind w v) := by
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      change neighboring i j at h
      rcases h with next | prev
      · have bound : i.val + 1 < w.length := next ▸ j.isLt
        simpa [lineKind, next] using adj_at localWord i.val bound
      · have bound : j.val + 1 < w.length := prev ▸ i.isLt
        exact S.symm (by simpa [lineKind, prev] using adj_at localWord j.val bound)
    | inr leaf =>
      obtain ⟨j,e⟩ := leaf
      obtain ⟨rfl, hm⟩ := h
      exact Or.inl hm.1
  | inr leaf =>
    obtain ⟨j,e⟩ := leaf
    cases v with
    | inl i =>
      obtain ⟨rfl, hm⟩ := h
      exact Or.inr hm.1
    | inr leaf => exact False.elim h

theorem line_present {w : List K} {u v : LineItem w} (h : lineEdge S w u v) :
    linePresent S w u ∧ linePresent S w v := by
  cases u <;> cases v
  · exact ⟨trivial, trivial⟩
  · rename_i i leaf
    cases leaf
    exact ⟨trivial, h.2⟩
  · rename_i leaf i
    cases leaf
    exact ⟨h.2, trivial⟩
  · exact False.elim h

theorem line_complete {w : List K} (r : LineItem w) (e : K)
    (present : linePresent S w r) (role : S.role (lineKind w r) e) :
    ∃ u, lineEdge S w r u ∧ lineKind w u = e := by
  cases r with
  | inl i =>
    by_cases neighborExists : ∃ j : Position w, neighboring i j ∧ w[j.val] = e
    · obtain ⟨j, n, eq⟩ := neighborExists
      exact ⟨.inl j, n, eq⟩
    · exact ⟨.inr (i,e), ⟨rfl, role, neighborExists⟩, rfl⟩
  | inr leaf =>
    obtain ⟨i, c⟩ := leaf
    exact ((S.role_types role).1 (S.role_types present.1).2).elim

/-- Two distinct neighbors in the line have indices exactly one on either side of the center. -/
private theorem distinct_neighbors {w : List K} {i j k : Position w}
    (ij : neighboring i j) (ik : neighboring i k) (ne : j ≠ k) :
    (j.val + 1 = i.val ∧ i.val + 1 = k.val) ∨ (k.val + 1 = i.val ∧ i.val + 1 = j.val) := by
  unfold neighboring at *
  have neq : j.val ≠ k.val := fun eq => ne (Fin.ext eq)
  omega

private theorem line_two_neighbors_retrace {w : List K} (localWord : Local S.adj S.retrace w)
    {i j k : Position w} (ij : neighboring i j) (ik : neighboring i k) (ne : j ≠ k)
    (same : w[j.val] = w[k.val]) : S.retrace w[j.val] w[i.val] := by
  rcases distinct_neighbors ij ik ne with ⟨ji, ik⟩ | ⟨ki, ij⟩
  · have jk : j.val + 2 = k.val := by omega
    have len : j.val + 2 < w.length := by rw [jk]; exact k.isLt
    have h : w[j.val] ≠ w[k.val] ∨ S.retrace w[j.val] w[i.val] := by
      simpa only [ji, jk] using turn_at localWord j.val len
    exact h.resolve_left (fun neq => neq same)
  · have kj : k.val + 2 = j.val := by omega
    have len : k.val + 2 < w.length := by rw [kj]; exact j.isLt
    have h : w[k.val] ≠ w[j.val] ∨ S.retrace w[k.val] w[i.val] := by
      simpa only [ki, kj] using turn_at localWord k.val len
    exact same.symm ▸ h.resolve_left (fun neq => neq same.symm)

private theorem edge_to_leaf {w : List K} {u : LineItem w} {j : Position w} {e : K}
    (h : lineEdge S w u (.inr (j,e))) : u = .inl j := by
  cases u with
  | inl i => exact congrArg Sum.inl h.1
  | inr leaf => exact False.elim h

theorem line_unique_role {w : List K} (localWord : Local S.adj S.retrace w)
    {r u v : LineItem w} (role : S.role (lineKind w r) (lineKind w u))
    (same : lineKind w u = lineKind w v)
    (ru : lineEdge S w r u) (rv : lineEdge S w r v) : u = v := by
  cases r with
  | inr leaf =>
    obtain ⟨i,e⟩ := leaf
    exact ((S.role_types role).1 (S.role_types (line_present ru).1.1).2).elim
  | inl i =>
    cases u with
    | inl j =>
      cases v with
      | inl k =>
        by_cases eq : j = k
        · exact congrArg Sum.inl eq
        · have repeated := line_two_neighbors_retrace localWord ru rv eq same
          exact ((S.role_types repeated.1).1 (S.role_types role).2).elim
      | inr leaf =>
        obtain ⟨k,e⟩ := leaf
        obtain ⟨rfl, hm⟩ := rv
        exact (hm.2 ⟨j, ru, same⟩).elim
    | inr leaf =>
      obtain ⟨j,e⟩ := leaf
      obtain ⟨rfl, hm⟩ := ru
      cases v with
      | inl k => exact (hm.2 ⟨k, rv, same.symm⟩).elim
      | inr leaf =>
        obtain ⟨k,f⟩ := leaf
        obtain ⟨rfl, _⟩ := rv
        exact congrArg Sum.inr (Prod.ext rfl same)

theorem line_cardinality_one {w : List K} (localWord : Local S.adj S.retrace w)
    {e r s : LineItem w} (role : S.role (lineKind w r) (lineKind w e))
    (same : lineKind w r = lineKind w s) (one : ¬ S.many (lineKind w r) (lineKind w e))
    (er : lineEdge S w e r) (es : lineEdge S w e s) : r = s := by
  cases e with
  | inr leaf =>
    obtain ⟨i,k⟩ := leaf
    exact (edge_to_leaf (line_symmetric er)).trans (edge_to_leaf (line_symmetric es)).symm
  | inl i =>
    cases r with
    | inr leaf =>
      obtain ⟨j,k⟩ := leaf
      exact ((S.role_types role).1 (S.role_types (line_present er).2.1).2).elim
    | inl j =>
      cases s with
      | inr leaf =>
        obtain ⟨k,c⟩ := leaf
        have notEntity : ¬ S.entity (lineKind w (.inr (k,c))) := same ▸ (S.role_types role).1
        exact (notEntity (S.role_types (line_present es).2.1).2).elim
      | inl k =>
        by_cases eq : j = k
        · exact congrArg Sum.inl eq
        · exact (one (line_two_neighbors_retrace localWord er es eq same).2).elim

private theorem shared_core_neighbor {w : List K} {r s : Position w}
    {u : LineItem w} (ne : r ≠ s)
    (edgeR : lineEdge S w (.inl r) u) (edgeS : lineEdge S w (.inl s) u) :
    ∃ i : Position w, u = .inl i ∧ neighboring r i ∧ neighboring s i := by
  cases u with
  | inl i => exact ⟨i, rfl, edgeR, edgeS⟩
  | inr leaf =>
    obtain ⟨i,e⟩ := leaf
    exact (ne (edgeR.1.trans edgeS.1.symm)).elim

theorem line_tuple_identity {w : List K} {r s : LineItem w}
    (presentR : linePresent S w r) (presentS : linePresent S w s)
    (relR : ¬ S.entity (lineKind w r)) (same : lineKind w r = lineKind w s)
    (sameTuple : ∀ u, lineEdge S w r u ↔ lineEdge S w s u) : r = s := by
  cases r with
  | inr leaf =>
    obtain ⟨i,e⟩ := leaf
    exact (relR (S.role_types presentR.1).2).elim
  | inl r =>
    cases s with
    | inr leaf =>
      obtain ⟨i,e⟩ := leaf
      exact (relR (same.symm ▸ (S.role_types presentS.1).2)).elim
    | inl s =>
      apply congrArg Sum.inl
      apply Classical.byContradiction
      intro ne
      obtain ⟨e,f,ef,roleE,roleF⟩ := S.at_least_two_roles _ relR
      obtain ⟨u,edgeU,kindU⟩ := line_complete (.inl r) e presentR roleE
      obtain ⟨v,edgeV,kindV⟩ := line_complete (.inl r) f presentR roleF
      obtain ⟨i,rfl,ri,si⟩ := shared_core_neighbor ne edgeU ((sameTuple u).mp edgeU)
      obtain ⟨j,rfl,rj,sj⟩ := shared_core_neighbor ne edgeV ((sameTuple v).mp edgeV)
      have rs : r.val ≠ s.val := fun eq => ne (Fin.ext eq)
      have ij : i.val ≠ j.val := fun eq => ef (kindU.symm.trans ((Fin.ext eq) ▸ kindV))
      unfold neighboring at ri si rj sj
      omega

/-- Use one fresh item per word position, with fresh leaves completing missing roles. -/
abbrev lineSkeleton (S : Schema K) (w : List K) (h : Local S.adj S.retrace w) :
    Skeleton S where
  Item := LineItem w
  kind := lineKind w
  present := linePresent S w
  edge := lineEdge S w
  finite := line_finite S w
  symmetric := line_symmetric
  typed := line_typed h
  endpoints_present := line_present
  complete := line_complete
  unique_role := line_unique_role h
  cardinality_one := line_cardinality_one h
  tuple_identity := line_tuple_identity

def level {w : List K} : LineItem w → Nat
  | .inl i => i.val
  | .inr (i,_) => i.val + 1

private theorem edge_level {w : List K} {u v : LineItem w} (h : lineEdge S w u v) :
    level v ≤ level u + 1 := by
  cases u <;> cases v
  · change neighboring _ _ at h
    unfold neighboring at h
    simp only [level]
    omega
  · rename_i i leaf
    obtain ⟨j,e⟩ := leaf
    simp [level,h.1]
  · rename_i leaf i
    obtain ⟨j,e⟩ := leaf
    simp only [level, h.1]
    omega
  · exact False.elim h

private theorem traverse_line {w : List K} (hLocal : Local S.adj S.retrace w) {remaining : List K}
    (i : Position w) (hRemaining : remaining = w.drop (i.val + 1))
    (seen frontier : LineItem w → Prop) (reaches : frontier (.inl i))
    (seenBound : ∀ u, seen u → level u ≤ i.val)
    (frontierSeen : ∀ u, frontier u → seen u) :
    run (lineSkeleton S w hLocal) remaining seen frontier
      (.inl ⟨w.length - 1, by have := i.isLt; omega⟩) := by
  induction remaining generalizing i seen frontier with
  | nil =>
    have last : i.val = w.length - 1 := by
      have length := congrArg List.length hRemaining
      simp only [List.length_nil, List.length_drop] at length
      have bound := i.isLt
      omega
    have eq : i = ⟨w.length - 1, by have := i.isLt; omega⟩ := Fin.ext last
    exact eq ▸ reaches
  | cons k ks ih =>
    have indexBound : i.val + 1 < w.length := by
      have length := congrArg List.length hRemaining
      simp only [List.length_cons, List.length_drop] at length
      omega
    let j : Position w := ⟨i.val + 1, indexBound⟩
    have parts : k :: ks = w[j.val] :: w.drop (j.val + 1) := by
      rw [hRemaining, List.drop_eq_getElem_cons indexBound]
    let newFrontier := next (lineSkeleton S w hLocal) k seen frontier
    have reachesNext : newFrontier (.inl j) :=
      ⟨(List.cons.inj parts).1.symm, ⟨.inl i, reaches, Or.inl rfl⟩,
        fun wasSeen => by have h := seenBound (.inl j) wasSeen; change i.val + 1 ≤ i.val at h; omega⟩
    have newBound : ∀ u, seen u ∨ newFrontier u → level u ≤ j.val := by
      intro u h
      rcases h with cameBefore | ⟨_, ⟨v, cameBefore, edge⟩, _⟩
      · exact Nat.le_succ_of_le (seenBound _ cameBefore)
      · exact Nat.le_trans (edge_level edge) (Nat.succ_le_succ (seenBound _ (frontierSeen _ cameBefore)))
    exact ih j (List.cons.inj parts).2 _ _ reachesNext newBound (fun u => Or.inr)

/-- Appendix C, Lemma C.1, sufficiency. The entire selected linear traversal survives
bridge burning, since no position can be reached before its distance from the base. -/
theorem has_terminal_of_local {w : List K} (nonempty : w ≠ []) (h : Local S.adj S.retrace w) :
    HasTerminal S w := by
  cases w with
  | nil => exact (nonempty rfl).elim
  | cons k ks =>
    let w := k :: ks
    let start : Position w := ⟨0, by simp [w]⟩
    let finish : Position w := ⟨w.length - 1, by simp [w]⟩
    refine ⟨lineSkeleton S w h, .inl start, .inl finish, k, ks, rfl, trivial, rfl, ?_⟩
    exact traverse_line h start rfl (· = .inl start) (· = .inl start) rfl
      (by intro u hu; cases hu; exact Nat.le_refl 0) (fun _ same => same)

/-- Maier et al., Appendix C, Lemma C.1, with participation and nonemptiness included. -/
theorem has_terminal_iff {w : List K} : HasTerminal S w ↔ w ≠ [] ∧ Local S.adj S.retrace w := by
  constructor
  · rintro ⟨g, b, f, term⟩
    exact local_of_terminal term
  · rintro ⟨nonempty, valid⟩
    exact has_terminal_of_local nonempty valid

/-- Attributes and undirected dependency candidates after Phase I. -/
structure PhaseOne (S : Schema K) (A : Type) where
  owner : A → K
  dependency : List K → A → A → Prop
  valid_dependency : ∀ {d x y}, dependency d x y → HasTerminal S d
  dependency_endpoints : ∀ {d x y}, dependency d x y →
    d.head? = some (owner y) ∧ d.getLast? = some (owner x)
  reverse_dependency : ∀ {d x y}, dependency d x y → dependency d.reverse y x
  different_attributes : ∀ {d x y}, dependency d x y → x ≠ y

def PhaseOne.toCandidates {A : Type} (M : PhaseOne S A) : Candidates K A where
  adj := S.adj
  retrace := S.retrace
  owner := M.owner
  dependency := M.dependency
  symmetric_adj := S.symm
  valid_dependency dep := (has_terminal_iff.mp (M.valid_dependency dep)).2
  dependency_endpoints := M.dependency_endpoints
  reverse_dependency := M.reverse_dependency
  different_attributes := M.different_attributes

/-- A valid relational variable of the given perspective. -/
def RelationalVariable {A : Type} (M : PhaseOne S A) (base : K) (v : Variable K A) : Prop :=
  HasTerminal S v.1 ∧ v.1.head? = some base ∧ v.1.getLast? = some (M.owner v.2)

/-- Definition 3 applies extend after the terminal-set validity filter. -/
def UnrolledEdge {A : Type} (M : PhaseOne S A) (src dst : Variable K A) : Prop :=
  ∃ d, M.dependency d src.2 dst.2 ∧ Extend (HasTerminal S) dst.1 d src.1

/-- The two incoming edges encode undirected incidences in the reverse-closed graph. -/
def UnshieldedTriple {A : Type} (M : PhaseOne S A) (p q r : Variable K A) : Prop :=
  UnrolledEdge M p q ∧ UnrolledEdge M r q ∧
    p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ ¬ UnrolledEdge M r p ∧ ¬ UnrolledEdge M p r

/-- Two relational variables intersect when the same attribute instance occurs in both terminal sets. -/
def Intersectable (S : Schema K) (p q : Variable K A) : Prop :=
  ∃ (g : Skeleton S) (base finish : g.Item),
    p.2 = q.2 ∧ Terminal g p.1 base finish ∧ Terminal g q.1 base finish

private theorem extend_has_terminal {p q r : List K}
    (h : Extend (Local S.adj S.retrace) p q r) : Extend (HasTerminal S) p q r := by
  refine ⟨has_terminal_of_local ?_ h.1, h.2⟩
  obtain ⟨_, splice⟩ := h
  cases splice
  simp

private theorem unrolled_edge_iff {A : Type} {M : PhaseOne S A} {p q : Variable K A} :
    UnrolledEdge M p q ↔ UnrolledArrow M.toCandidates p q := by
  constructor
  · rintro ⟨d, dep, term, splice⟩
    exact ⟨d, dep, (has_terminal_iff.mp term).2, splice⟩
  · rintro ⟨d, dep, valid, splice⟩
    exact ⟨d, dep, extend_has_terminal ⟨valid, splice⟩⟩

private theorem variable_iff {A : Type} {M : PhaseOne S A} {b : K} {v : Variable K A} :
    RelationalVariable M b v ↔ WellTyped M.toCandidates b v := by
  constructor
  · rintro ⟨valid, head, last⟩
    exact ⟨(has_terminal_iff.mp valid).2, head, last⟩
  · rintro ⟨valid, head, last⟩
    exact ⟨has_terminal_of_local (fun empty => by simp [empty] at head) valid, head, last⟩

private theorem unshielded_iff {A : Type} {M : PhaseOne S A} {p q r : Variable K A} :
    UnshieldedTriple M p q r ↔ Unshielded M.toCandidates p q r := by
  simp only [UnshieldedTriple, Unshielded, unrolled_edge_iff]

/-- A distinct variable cannot intersect a canonical variable at its perspective. -/
theorem canonical_not_intersectable {K A : Type} {S : Schema K} {k : K} {x : A}
    {v : Variable K A} (distinct : ([k],x) ≠ v) : ¬ Intersectable S ([k],x) v := by
  rintro ⟨g, b, f, attr, canonical, other⟩
  obtain ⟨k', trail, eq, _, baseKind, runEq⟩ := canonical
  have types : k = k' ∧ [] = trail := List.cons.inj eq
  obtain ⟨rfl, rfl⟩ := types
  have finishEq : f = b := runEq
  subst f
  exact distinct (Prod.ext (by simpa [baseKind] using (noncanonical_excludes_base other).symm) attr)

/-- AAAI 2016 Lemma 5 in the finite-skeleton bridge-burning semantics. The returned
triple uses the same inducing dependencies and has nonintersectable flanks. -/
theorem representative_unshielded_triple {A : Type} {M : PhaseOne S A}
    {p q r : List K} {x y z : A} (h : UnshieldedTriple M (p,x) (q,y) (r,z)) :
    ∃ d₁ d₂ candidate, M.dependency d₁ x y ∧ M.dependency d₂ z y ∧
      RelationalVariable M (M.owner x) ([M.owner x],x) ∧
      RelationalVariable M (M.owner x) (d₁.reverse,y) ∧
      RelationalVariable M (M.owner x) (candidate,z) ∧
      UnshieldedTriple M ([M.owner x],x) (d₁.reverse,y) (candidate,z) ∧
      ¬ Intersectable S ([M.owner x],x) (candidate,z) ∧
      Extend (HasTerminal S) q d₁ p ∧ Extend (HasTerminal S) q d₂ r ∧
      Extend (HasTerminal S) d₁.reverse d₂ candidate ∧ Splice p candidate r := by
  obtain ⟨d₁, d₂, c, dep1, dep2, ext1, ext2, v1, v2, v3, unshielded, ext3, compatible⟩ :=
    RCDLemma5.representative_unshielded_triple (unshielded_iff.mp h)
  have exactV3 := variable_iff.mpr v3
  have flankDiff : ([M.owner x], x) ≠ (c,z) := by
    obtain ⟨_, _, _, _, distinct, _, _⟩ := unshielded
    exact distinct
  exact ⟨d₁, d₂, c, dep1, dep2, variable_iff.mpr v1, variable_iff.mpr v2, exactV3,
    unshielded_iff.mpr unshielded, canonical_not_intersectable flankDiff,
    extend_has_terminal ext1, extend_has_terminal ext2, extend_has_terminal ext3, compatible⟩

end RCDPathValidity

end
