module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDPathValidity

/-! A finite legal skeleton for three relational words joined at their common pivot. -/

@[expose] public section

namespace RCDThreeArm

open RCDPathValidity
open RCDLemma5 (Local Turn local_split local_reverse)

variable {K : Type} {S : Schema K}

inductive Arm
  | x | y | z
  deriving DecidableEq

inductive Node
  | center
  | ray (arm : Arm) (index : Nat)
  deriving DecidableEq

variable (center : K) (words : Arm → List K)

def classOf : Node → K
  | .center => center
  | .ray a i => (words a)[i]?.getD center

def existsAt : Node → Prop
  | .center => True
  | .ray a i => i < (words a).length

def hinges : Node → Node → Prop
  | .center, .center => False
  | .center, .ray _ i | .ray _ i, .center => i = 0
  | .ray a i, .ray b j => a = b ∧ (i + 1 = j ∨ j + 1 = i)

def adjacent (u v : Node) : Prop := existsAt words u ∧ existsAt words v ∧ hinges u v

private theorem hinges_symm {u v : Node} (edge : hinges u v) : hinges v u := by
  cases u <;> cases v
  · exact edge
  · exact edge
  · exact edge
  · exact ⟨edge.1.symm, edge.2.symm⟩

private theorem adjacent_symm {u v : Node} (edge : adjacent words u v) : adjacent words v u :=
  ⟨edge.2.1, edge.1, hinges_symm edge.2.2⟩

/-- The three incident rays have legal words, and any pair of populated rays can meet
at their common item without violating role multiplicity. -/
structure LegalArms (S : Schema K) : Prop where
  ray_local : ∀ a, Local S.adj S.retrace (center :: words a)
  between : ∀ {a b}, a ≠ b → Turn S.retrace (words a).head? center (words b).head?

private theorem turn_swap {retrace : K → K → Prop} {a b : Option K} {v : K}
    (turn : Turn retrace a v b) : Turn retrace b v a := by
  cases a <;> cases b
  all_goals simp only [Turn] at turn ⊢
  rename_i a b
  rcases turn with ne | repeatAllowed
  · exact .inl (Ne.symm ne)
  · by_cases same : b = a
    · exact .inr (same.symm ▸ repeatAllowed)
    · exact .inl same

/-- The three words in a valid splice give precisely the local legality tests
for the witness's three rays. -/
theorem legal_of_splice (before overlap after : List K) (v : K)
    (q : Local S.adj S.retrace (before ++ v :: overlap.reverse))
    (d : Local S.adj S.retrace (overlap ++ v :: after))
    (r : Local S.adj S.retrace (before ++ v :: after)) :
    LegalArms v (fun | .x => before.reverse | .y => overlap.reverse | .z => after) S := by
  let qSplit := (local_split before overlap.reverse v).mp q
  let dSplit := (local_split overlap after v).mp d
  let rSplit := (local_split before after v).mp r
  have xRay : Local S.adj S.retrace (v :: before.reverse) := by
    simpa using local_reverse S.symm qSplit.1
  have xy : Turn S.retrace before.reverse.head? v overlap.reverse.head? := by
    simpa only [List.head?_reverse] using qSplit.2.2
  have xz : Turn S.retrace before.reverse.head? v after.head? := by
    simpa only [List.head?_reverse] using rSplit.2.2
  have yz : Turn S.retrace overlap.reverse.head? v after.head? := by
    simpa only [List.head?_reverse] using dSplit.2.2
  refine ⟨fun a => ?_, ?_⟩
  · cases a
    · exact xRay
    · exact qSplit.2.1
    · exact rSplit.2.1
  · intro a b ne
    cases a <;> cases b
    · exact (ne rfl).elim
    · exact xy
    · exact xz
    · exact turn_swap xy
    · exact (ne rfl).elim
    · exact yz
    · exact turn_swap xz
    · exact turn_swap yz
    · exact (ne rfl).elim

private theorem class_ray (a : Arm) (i : Nat) (h : i < (words a).length) :
    classOf center words (.ray a i) = (words a)[i] := by
  simp [classOf, List.getElem?_eq_getElem h]

private theorem step_forward (h : LegalArms center words S) (a : Arm) (i : Nat)
    (bound : i + 1 < (words a).length) :
    S.adj (classOf center words (.ray a i)) (classOf center words (.ray a (i+1))) := by
  have prev : i < (words a).length := by omega
  rw [class_ray center words a _ prev, class_ray center words a _ bound]
  have wholeBound : (i+1)+1 < (center :: words a).length := by simp; omega
  simpa only [List.getElem_cons_succ] using adj_at (h.ray_local a) (i+1) wholeBound

private theorem step_center (h : LegalArms center words S) (a : Arm)
    (bound : 0 < (words a).length) : S.adj center (classOf center words (.ray a 0)) := by
  rw [class_ray center words a 0 bound]
  have wholeBound : 0 + 1 < (center :: words a).length := by simp; omega
  simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
    adj_at (h.ray_local a) 0 wholeBound

private theorem adjacent_typed (h : LegalArms center words S) {u v : Node}
    (edge : adjacent words u v) : S.adj (classOf center words u) (classOf center words v) := by
  obtain ⟨inU,inV,step⟩ := edge
  cases u with
  | center =>
    cases v with
    | center => exact step.elim
    | ray a i =>
      change i = 0 at step
      subst i
      exact step_center center words h a inV
  | ray a i =>
    cases v with
    | center =>
      change i = 0 at step
      subst i
      exact S.symm (step_center center words h a inU)
    | ray b j =>
      obtain ⟨rfl, same | same⟩ := step
      · subst j
        exact step_forward center words h a i inV
      · subst i
        exact S.symm (step_forward center words h a j inU)

private theorem window (h : LegalArms center words S) (a : Arm) (i : Nat)
    (bound : i+2 < (center :: words a).length) :
    ¬ (center :: words a)[i] = (center :: words a)[i+2] ∨
      S.retrace (center :: words a)[i] (center :: words a)[i+1] :=
  turn_at (h.ray_local a) i bound

private theorem turn_ray (h : LegalArms center words S) (a : Arm) (i : Nat)
    (bound : i+2 < (words a).length) :
    (classOf center words (.ray a i) ≠ classOf center words (.ray a (i+2))) ∨
      S.retrace (classOf center words (.ray a i)) (classOf center words (.ray a (i+1))) := by
  have b0 : i < (words a).length := by omega
  have b1 : i+1 < (words a).length := by omega
  rw [class_ray center words a _ b0, class_ray center words a _ b1, class_ray center words a _ bound]
  have wholeBound : (i+1)+2 < (center :: words a).length := by simp; omega
  simpa only [List.getElem_cons_succ] using window center words h a (i+1) wholeBound

private theorem turn_at_first (h : LegalArms center words S) (a : Arm)
    (bound : 1 < (words a).length) :
    center ≠ classOf center words (.ray a 1) ∨ S.retrace center (classOf center words (.ray a 0)) := by
  have b0 : 0 < (words a).length := by omega
  rw [class_ray center words a _ b0, class_ray center words a _ bound]
  have wholeBound : 0+2 < (center :: words a).length := by simp; omega
  simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using window center words h a 0 wholeBound

private theorem turn_from_two_edges (h : LegalArms center words S) {u v w : Node}
    (left : adjacent words u v) (right : adjacent words v w) (distinct : u ≠ w)
    (sameClass : classOf center words u = classOf center words w) :
    S.retrace (classOf center words u) (classOf center words v) := by
  obtain ⟨inU,inV,left⟩ := left
  obtain ⟨_,inW,right⟩ := right
  cases v with
  | center =>
    cases u with
    | center => contradiction
    | ray a i =>
      cases w with
      | center => contradiction
      | ray b j =>
        change i = 0 at left
        change j = 0 at right
        subst i
        subst j
        have ab : a ≠ b := fun eq => distinct (congrArg (fun a => Node.ray a 0) eq)
        have headA : (words a).head? = some (classOf center words (.ray a 0)) := by
          cases eq : words a with
          | nil => simp [existsAt, eq] at inU
          | cons k ks => simp [classOf, eq]
        have headB : (words b).head? = some (classOf center words (.ray b 0)) := by
          cases eq : words b with
          | nil => simp [existsAt, eq] at inW
          | cons k ks => simp [classOf, eq]
        have branch := h.between ab
        rw [headA, headB] at branch
        exact branch.resolve_left (fun ne => ne sameClass)
  | ray a j =>
    cases u with
    | center =>
      change j = 0 at left
      subst j
      cases w with
      | center => exact (distinct rfl).elim
      | ray b k =>
        obtain ⟨rfl, hk | hk⟩ := right
        · have kEq : k = 1 := hk.symm
          subst k
          exact (turn_at_first center words h a inW).resolve_left (fun ne => ne sameClass)
        · omega
    | ray b i =>
      obtain ⟨rfl, hij⟩ := left
      cases w with
      | center =>
        change j = 0 at right
        subst j
        rcases hij with bad | hi
        · omega
        · have iEq : i = 1 := hi.symm
          subst i
          rw [sameClass]
          exact (turn_at_first center words h b inU).resolve_left (fun ne => ne sameClass.symm)
      | ray c k =>
        obtain ⟨rfl, hjk⟩ := right
        have notSame : i ≠ k := fun eq => distinct (congrArg (Node.ray b) eq)
        have direction : (j = i+1 ∧ k = i+2) ∨ (j = k+1 ∧ i = k+2) := by omega
        rcases direction with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (turn_ray center words h b i inW).resolve_left (fun ne => ne sameClass)
        · rw [sameClass]
          exact (turn_ray center words h b k inU).resolve_left (fun ne => ne sameClass.symm)

def depth : Node → Nat
  | .center => 0
  | .ray _ i => i + 1

private theorem hinge_depth {u v : Node} (h : hinges u v) :
    depth v = depth u + 1 ∨ depth u = depth v + 1 := by
  cases u <;> cases v
  · exact h.elim
  · exact .inl (by unfold hinges at h; simp [depth, h])
  · exact .inr (by unfold hinges at h; simp [depth, h])
  · exact h.2.elim (fun eq => .inl (by simp [depth]; omega))
      (fun eq => .inr (by simp [depth]; omega))

private theorem hinge_lower_unique {u v w : Node} (hu : hinges v u) (hw : hinges v w)
    (lowerU : depth u < depth v) (lowerW : depth w < depth v) : u = w := by
  cases v with
  | center => cases u <;> simp [depth] at lowerU
  | ray a j =>
    cases u <;> cases w
    · rfl
    · rename_i b k
      rcases hw with ⟨_,hk⟩
      change j = 0 at hu
      simp [depth, hu] at lowerW
    · rename_i b i
      change j = 0 at hw
      simp [depth, hw] at lowerU
    · rename_i b i c k
      obtain ⟨rfl, hi⟩ := hu
      obtain ⟨rfl, hk⟩ := hw
      congr
      simp only [depth] at lowerU lowerW
      omega

private theorem no_square {u v p q : Node} (up : hinges u p) (uq : hinges u q)
    (vp : hinges v p) (vq : hinges v q) (diff : u ≠ v) : p = q := by
  have e1 := hinge_depth up
  have e2 := hinge_depth uq
  have e3 := hinge_depth vp
  have e4 := hinge_depth vq
  have maxNode : (depth p < depth u ∧ depth q < depth u) ∨
      (depth p < depth v ∧ depth q < depth v) ∨
      (depth u < depth p ∧ depth v < depth p) ∨
      (depth u < depth q ∧ depth v < depth q) := by omega
  rcases maxNode with a | a | a | a
  · exact hinge_lower_unique up uq a.1 a.2
  · exact hinge_lower_unique vp vq a.1 a.2
  · exact (diff (hinge_lower_unique (hinges_symm up) (hinges_symm vp) a.1 a.2)).elim
  · exact (diff (hinge_lower_unique (hinges_symm uq) (hinges_symm vq) a.1 a.2)).elim

abbrev Item (K : Type) := Node ⊕ (Node × K)

def itemClass : Item K → K
  | .inl u => classOf center words u
  | .inr (_, k) => k

def unsupplied (u : Node) (e : K) : Prop :=
  existsAt words u ∧ S.role (classOf center words u) e ∧
    ¬ ∃ v, adjacent words u v ∧ classOf center words v = e

def present : Item K → Prop
  | .inl u => existsAt words u
  | .inr (u,e) => unsupplied (S := S) center words u e

def edge : Item K → Item K → Prop
  | .inl u, .inl v => adjacent words u v
  | .inl u, .inr (v,e) | .inr (v,e), .inl u => u = v ∧ unsupplied (S := S) center words v e
  | .inr _, .inr _ => False

theorem edge_symm {u v : Item K} (e : edge (S := S) center words u v) :
    edge (S := S) center words v u := by
  cases u <;> cases v
  · exact adjacent_symm words e
  · exact e
  · exact e
  · exact e

theorem item_present {u v : Item K} (e : edge (S := S) center words u v) :
    present (S := S) center words u ∧ present (S := S) center words v := by
  cases u <;> cases v
  · exact ⟨e.1,e.2.1⟩
  · rename_i u leaf
    obtain ⟨v,k⟩ := leaf
    exact ⟨e.1.symm ▸ e.2.1, e.2⟩
  · rename_i leaf v
    obtain ⟨u,k⟩ := leaf
    exact ⟨e.2,e.1.symm ▸ e.2.1⟩
  · exact e.elim

theorem edge_typed (h : LegalArms center words S) {u v : Item K}
    (e : edge (S := S) center words u v) : S.adj (itemClass center words u) (itemClass center words v) := by
  cases u <;> cases v
  · exact adjacent_typed center words h e
  · rename_i u leaf
    obtain ⟨v,k⟩ := leaf
    obtain ⟨rfl,missing⟩ := e
    exact .inl missing.2.1
  · rename_i leaf v
    obtain ⟨u,k⟩ := leaf
    obtain ⟨rfl,missing⟩ := e
    exact .inr missing.2.1
  · exact e.elim

theorem all_items_finite :
    ∃ items : List (Item K), ∀ u, present (S := S) center words u → u ∈ items := by
  classical
  let nodes := Node.center :: [Arm.x, .y, .z].flatMap
    (fun a => (List.range (words a).length).map (Node.ray a))
  have nodesCover (u : Node) (h : existsAt words u) : u ∈ nodes := by
    cases u with
    | center => simp [nodes]
    | ray a i =>
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨a, by cases a <;> simp, List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩⟩
  let roles (u : Node) := (S.finite_roles (classOf center words u)).choose
  refine ⟨nodes.map Sum.inl ++ nodes.flatMap (fun u => (roles u).map (fun k => Sum.inr (u,k))), ?_⟩
  intro u h
  cases u with
  | inl u => exact List.mem_append_left _ (List.mem_map.mpr ⟨u, nodesCover u h, rfl⟩)
  | inr p =>
    obtain ⟨u,k⟩ := p
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨u,nodesCover u h.1,
      List.mem_map.mpr ⟨k, (S.finite_roles _).choose_spec k h.2.1, rfl⟩⟩)

theorem role_complete (u : Item K) (e : K) (pr : present (S := S) center words u)
    (role : S.role (itemClass center words u) e) :
    ∃ v, edge (S := S) center words u v ∧ itemClass center words v = e := by
  cases u with
  | inl x =>
    by_cases existsThere : ∃ v, adjacent words x v ∧ classOf center words v = e
    · obtain ⟨v,ev,eq⟩ := existsThere
      exact ⟨.inl v,ev,eq⟩
    · exact ⟨.inr (x,e), ⟨rfl,pr,role,existsThere⟩,rfl⟩
  | inr leaf =>
    obtain ⟨x,k⟩ := leaf
    exact ((S.role_types role).1 (S.role_types pr.2.1).2).elim

private theorem is_anchor {u : Item K} {v : Node} {e : K}
    (ed : edge (S := S) center words u (.inr (v,e))) : u = .inl v := by
  cases u with
  | inl u => exact congrArg Sum.inl ed.1
  | inr leaf => exact ed.elim

theorem role_unique (h : LegalArms center words S) {r u v : Item K}
    (role : S.role (itemClass center words r) (itemClass center words u))
    (same : itemClass center words u = itemClass center words v)
    (ru : edge (S := S) center words r u) (rv : edge (S := S) center words r v) : u = v := by
  cases r with
  | inr p =>
    obtain ⟨x,k⟩ := p
    exact ((S.role_types role).1 (S.role_types (item_present center words ru).1.2.1).2).elim
  | inl x =>
    cases u with
    | inl y =>
      cases v with
      | inl z =>
        by_cases sameItem : y = z
        · exact congrArg Sum.inl sameItem
        · have retrace := turn_from_two_edges center words h (adjacent_symm words ru) rv sameItem same
          exact ((S.role_types retrace.1).1 (S.role_types role).2).elim
      | inr leaf =>
        obtain ⟨z,k⟩ := leaf
        obtain ⟨rfl,extra⟩ := rv
        exact (extra.2.2 ⟨y, ru, same⟩).elim
    | inr leaf =>
      obtain ⟨y,k⟩ := leaf
      obtain ⟨rfl,extra⟩ := ru
      cases v with
      | inl z => exact (extra.2.2 ⟨z,rv,same.symm⟩).elim
      | inr leaf =>
        obtain ⟨z,l⟩ := leaf
        obtain ⟨rfl,_⟩ := rv
        exact congrArg Sum.inr (Prod.ext rfl same)

theorem card_one (h : LegalArms center words S) {e r q : Item K}
    (role : S.role (itemClass center words r) (itemClass center words e))
    (same : itemClass center words r = itemClass center words q)
    (one : ¬ S.many (itemClass center words r) (itemClass center words e))
    (er : edge (S := S) center words e r) (eq : edge (S := S) center words e q) : r = q := by
  cases e with
  | inr leaf =>
    obtain ⟨x,k⟩ := leaf
    exact (is_anchor center words (edge_symm center words er)).trans
      (is_anchor center words (edge_symm center words eq)).symm
  | inl x =>
    cases r with
    | inr leaf =>
      obtain ⟨y,k⟩ := leaf
      exact ((S.role_types role).1 (S.role_types (item_present center words er).2.2.1).2).elim
    | inl y =>
      cases q with
      | inr leaf =>
        obtain ⟨z,k⟩ := leaf
        exact ((S.role_types role).1 (same.symm ▸
          (S.role_types (item_present center words eq).2.2.1).2)).elim
      | inl z =>
        by_cases sameItem : y = z
        · exact congrArg Sum.inl sameItem
        · exact (one (turn_from_two_edges center words h (adjacent_symm words er) eq sameItem same).2).elim

private theorem shared_is_core {r s : Node} {u : Item K} (ne : r ≠ s)
    (ru : edge (S := S) center words (.inl r) u) (su : edge (S := S) center words (.inl s) u) :
    ∃ v, u = .inl v ∧ hinges r v ∧ hinges s v := by
  cases u with
  | inl v => exact ⟨v,rfl,ru.2.2,su.2.2⟩
  | inr leaf =>
    obtain ⟨v,k⟩ := leaf
    exact (ne (ru.1.trans su.1.symm)).elim

theorem tuple_identity {r s : Item K}
    (pr : present (S := S) center words r) (ps : present (S := S) center words s)
    (isRel : ¬ S.entity (itemClass center words r))
    (same : itemClass center words r = itemClass center words s)
    (identical : ∀ u, edge (S := S) center words r u ↔ edge (S := S) center words s u) : r = s := by
  cases r with
  | inr leaf =>
    obtain ⟨u,k⟩ := leaf
    exact (isRel (S.role_types pr.2.1).2).elim
  | inl r =>
    cases s with
    | inr leaf =>
      obtain ⟨u,k⟩ := leaf
      exact (isRel (same.symm ▸ (S.role_types ps.2.1).2)).elim
    | inl s =>
      apply congrArg Sum.inl
      apply Classical.byContradiction
      intro ne
      obtain ⟨k,l,kl,rk,rl⟩ := S.at_least_two_roles _ isRel
      obtain ⟨u,ru,ku⟩ := role_complete center words (.inl r) k pr rk
      obtain ⟨v,rv,lv⟩ := role_complete center words (.inl r) l pr rl
      obtain ⟨a,rfl,ra,sa⟩ := shared_is_core center words ne ru ((identical u).mp ru)
      obtain ⟨b,rfl,rb,sb⟩ := shared_is_core center words ne rv ((identical v).mp rv)
      have eq : a = b := no_square ra rb sa sb ne
      exact kl (ku.symm.trans (eq.symm ▸ lv))

/-- Complete each missing entity role with a new leaf. Existing core items retain their edges. -/
def skeleton (h : LegalArms center words S) : Skeleton S where
  Item := Item K
  kind := itemClass center words
  present := present center words
  edge := edge center words
  finite := all_items_finite center words
  symmetric := edge_symm center words
  typed := edge_typed center words h
  endpoints_present := item_present center words
  complete := role_complete center words
  unique_role := role_unique center words h
  cardinality_one := card_one center words h
  tuple_identity := tuple_identity center words

def nodeRank (origin : Arm) : Node → Nat
  | .center => (words origin).length
  | .ray a i => if a = origin then (words origin).length - (i + 1) else (words origin).length + i + 1

def itemRank (origin : Arm) : Item K → Nat
  | .inl u => nodeRank words origin u
  | .inr (u,_) => nodeRank words origin u + 1

private theorem adjacent_rank (origin : Arm) {u v : Node} (e : adjacent words u v) :
    nodeRank words origin v = nodeRank words origin u + 1 ∨
      nodeRank words origin u = nodeRank words origin v + 1 := by
  obtain ⟨pu,pv,step⟩ := e
  cases u with
  | center =>
    cases v with
    | center => exact step.elim
    | ray b j =>
      change j = 0 at step
      subst j
      by_cases same : b = origin
      · subst b
        simp [nodeRank]
        change 0 < (words origin).length at pv
        omega
      · simp [nodeRank, same]
  | ray a i =>
    cases v with
    | center =>
      change i = 0 at step
      subst i
      by_cases same : a = origin
      · subst a
        simp [nodeRank]
        change 0 < (words origin).length at pu
        omega
      · simp [nodeRank, same]
    | ray b j =>
      obtain ⟨rfl, changeIndex⟩ := step
      by_cases same : a = origin
      · subst a
        simp [nodeRank]
        change i < (words origin).length at pu
        change j < (words origin).length at pv
        omega
      · simp only [nodeRank, ite_eq_right same]
        omega

def predecessor (origin : Arm) : Node → Node
  | .center => .ray origin 0
  | .ray a i => if a = origin then .ray a (i+1) else
      match i with
      | 0 => .center
      | j + 1 => .ray a j

private theorem lower_is_predecessor (origin : Arm) {u v : Node} (e : adjacent words v u)
    (lower : nodeRank words origin u < nodeRank words origin v) :
    u = predecessor origin v := by
  obtain ⟨pv,pu,step⟩ := e
  cases v with
  | center =>
    cases u with
    | center => exact step.elim
    | ray a i =>
      change i = 0 at step
      subst i
      by_cases same : a = origin
      · simp [predecessor, same]
      · simp [nodeRank, same] at lower
        omega
  | ray a j =>
    cases u with
    | center =>
      change j = 0 at step
      subst j
      by_cases same : a = origin
      · simp [nodeRank, same] at lower
        omega
      · simp [predecessor, same]
    | ray b i =>
      obtain ⟨rfl, changeIndex⟩ := step
      by_cases same : a = origin
      · subst a
        change i < (words origin).length at pu
        change j < (words origin).length at pv
        simp [nodeRank] at lower
        have eq : i = j+1 := by omega
        simp [predecessor, eq]
      · simp only [nodeRank, ite_eq_right same] at lower
        have eq : j = i+1 := by omega
        simp [predecessor, same, eq]

private theorem edge_rank (origin : Arm) {u v : Item K} (e : edge (S := S) center words u v) :
    itemRank words origin v = itemRank words origin u + 1 ∨
      itemRank words origin u = itemRank words origin v + 1 := by
  cases u <;> cases v
  · exact adjacent_rank words origin e
  · rename_i u leaf
    obtain ⟨v,k⟩ := leaf
    exact .inl (by simp [itemRank,e.1])
  · rename_i leaf v
    obtain ⟨u,k⟩ := leaf
    exact .inr (by simp [itemRank,e.1])
  · exact e.elim

private theorem edge_lower_unique (origin : Arm) {u v w : Item K}
    (vu : edge (S := S) center words v u) (vw : edge (S := S) center words v w)
    (hu : itemRank words origin u < itemRank words origin v)
    (hw : itemRank words origin w < itemRank words origin v) : u = w := by
  cases v with
  | inr p =>
    obtain ⟨v,k⟩ := p
    exact (is_anchor center words (edge_symm center words vu)).trans
      (is_anchor center words (edge_symm center words vw)).symm
  | inl v =>
    cases u with
    | inl u =>
      cases w with
      | inl w => exact congrArg Sum.inl ((lower_is_predecessor words origin vu hu).trans
          (lower_is_predecessor words origin vw hw).symm)
      | inr p =>
        obtain ⟨w,k⟩ := p
        simp [itemRank,vw.1] at hw
        omega
    | inr p =>
      obtain ⟨u,k⟩ := p
      simp [itemRank,vu.1] at hu
      omega

def tip (a : Arm) : Node :=
  match (words a).length with
  | 0 => .center
  | i+1 => .ray a i

private theorem tip_present (a : Arm) : existsAt words (tip words a) := by
  unfold tip
  split
  · trivial
  · rename_i i h
    change i < (words a).length
    omega

private theorem tip_rank (origin to : Arm) (different : origin ≠ to) :
    itemRank words origin (.inl (tip words to)) = (words origin).length + (words to).length := by
  unfold tip
  split
  · rename_i h
    simp [itemRank,nodeRank,h]
  · rename_i i h
    simp [itemRank,nodeRank,Ne.symm different,h,Nat.add_assoc]

private theorem tip_rank_zero (a : Arm) : itemRank words a (.inl (tip words a)) = 0 := by
  unfold tip
  split
  · rename_i h
    simp [itemRank,nodeRank,h]
  · rename_i i h
    simp [itemRank,nodeRank,h]

private theorem chain_snoc_iff {V : Type} {R : V → V → Prop} (base v : V) (trail : List V) :
    Chain R base (trail ++ [v]) ↔ Chain R base trail ∧ R (trail.getLastD base) v := by
  induction trail generalizing base with
  | nil => simp [Chain]
  | cons u rest ih =>
    simp only [List.cons_append, Chain, List.getLastD_cons, ih, and_assoc]

private theorem chain_map {V W : Type} {R : V → V → Prop} {T : W → W → Prop} (f : V → W)
    (valid : ∀ {a b}, R a b → T (f a) (f b)) {base : V} {trail : List V}
    (h : Chain R base trail) : Chain T (f base) (trail.map f) := by
  induction trail generalizing base with
  | nil => trivial
  | cons u rest ih => exact ⟨valid h.1, ih h.2⟩

private theorem getLast_eq {V : Type} (start : V) (trail : List V) :
    (start :: trail).getLast? = some (trail.getLastD start) := by
  induction trail generalizing start with
  | nil => rfl
  | cons u rest ih =>
    rw [List.getLastD_cons]
    exact ih u

private theorem getLastD_append_singleton {V : Type} (fallback x : V) (l : List V) :
    (l ++ [x]).getLastD fallback = x := by
  induction l generalizing fallback with
  | nil => rfl
  | cons a rest ih =>
    rw [List.cons_append, List.getLastD_cons]
    exact ih a

def down (a : Arm) : Nat → List Node
  | 0 => []
  | n+1 => .ray a n :: down a n

private theorem down_length (a : Arm) (n : Nat) : (down a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [down, ih]

private theorem down_map (a : Arm) (n : Nat) (bound : n ≤ (words a).length) :
    (down a n).map (classOf center words) = ((words a).take n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have less : n < (words a).length := by omega
    have old := ih (by omega)
    rw [down, List.map_cons, old, List.take_succ_eq_append_getElem less, List.reverse_append]
    simp only [class_ray center words a n less, List.reverse_singleton, List.singleton_append]

def rayEnd (a : Arm) : Nat → Node
  | 0 => .center
  | i+1 => .ray a i

private theorem down_getLastD (a : Arm) (n : Nat) :
    (down a n).reverse.getLastD .center = rayEnd a n := by
  cases n with
  | zero => rfl
  | succ n => rw [down, List.reverse_cons, getLastD_append_singleton]; rfl

private theorem down_head (a : Arm) (n : Nat) (tail : List Node) :
    (down a n ++ .center :: tail).head? = some (rayEnd a n) := by
  cases n <;> rfl

private theorem step_to_ray (a : Arm) (n : Nat) (bound : n < (words a).length) :
    adjacent words (rayEnd a n) (.ray a n) := by
  cases n with
  | zero => exact ⟨trivial,bound,rfl⟩
  | succ n => exact ⟨by change n < (words a).length; omega, bound, rfl, .inl rfl⟩

private theorem chain_to_ray (a : Arm) (n : Nat) (bound : n ≤ (words a).length) :
    Chain (adjacent words) .center (down a n).reverse := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [down, List.reverse_cons, chain_snoc_iff, down_getLastD]
    exact ⟨ih (by omega), step_to_ray words a n (by omega)⟩

private theorem chain_from_ray (a : Arm) (n : Nat) (bound : n ≤ (words a).length)
    {suffix : List Node} (h : Chain (adjacent words) .center suffix) :
    Chain (adjacent words) (rayEnd a n)
      (down a n ++ .center :: suffix).tail := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have downStep := adjacent_symm words (step_to_ray words a n (by omega))
    have head := down_head a n suffix
    obtain ⟨tail, eqHead⟩ := List.head?_eq_some_iff.mp head
    have tailWalk := ih (by omega)
    rw [eqHead] at tailWalk
    change Chain (adjacent words) (.ray a n) (down a n ++ .center :: suffix)
    rw [eqHead]
    exact ⟨downStep,tailWalk⟩

def route (origin target : Arm) : List Node :=
  down origin (words origin).length ++ .center :: (down target (words target).length).reverse

private theorem route_head (origin target : Arm) :
    (route words origin target).head? = some (tip words origin) := by
  rw [route, down_head]
  rfl

private theorem route_last (origin target : Arm) :
    (route words origin target).getLast? = some (tip words target) := by
  simp only [route, List.getLast?_append, getLast_eq, down_getLastD, Option.some_or]
  rfl

private theorem route_class (origin target : Arm) :
    (route words origin target).map (classOf center words) =
      (words origin).reverse ++ center :: words target := by
  have left := down_map center words origin (words origin).length (Nat.le_refl _)
  have right := down_map center words target (words target).length (Nat.le_refl _)
  rw [route, List.map_append, List.map_cons, List.map_reverse, left, right, List.reverse_reverse]
  simp only [List.take_of_length_le (Nat.le_refl _)]
  rfl

private theorem route_length (origin target : Arm) :
    (route words origin target).length = (words origin).length + (words target).length + 1 := by
  simp only [route, List.length_append, down_length, List.length_cons, List.length_reverse]
  omega

private theorem route_chain (origin target : Arm) :
    Chain (adjacent words) (tip words origin) (route words origin target).tail :=
  by simpa only [route, tip, rayEnd] using
    chain_from_ray words origin _ (Nat.le_refl _) (chain_to_ray words target _ (Nat.le_refl _))

private theorem rank_upper {V : Type} {R : V → V → Prop} (rank : V → Nat)
    (bounded : ∀ {u v}, R u v → rank v ≤ rank u + 1) {base : V} {trail : List V}
    (walk : Chain R base trail) : rank (trail.getLastD base) ≤ rank base + trail.length := by
  induction trail generalizing base with
  | nil => simp
  | cons u rest ih =>
    have bound1 := bounded walk.1
    have bound2 := ih walk.2
    simp only [List.getLastD_cons, List.length_cons]
    omega

private theorem geodesic_increases {V : Type} {R : V → V → Prop} (rank : V → Nat)
    (bounded : ∀ {u v}, R u v → rank v ≤ rank u + 1) {base : V} {trail : List V}
    (walk : Chain R base trail) (goalRank : rank (trail.getLastD base) = rank base + trail.length) :
    Chain (fun a b => rank b = rank a + 1) base trail := by
  induction trail generalizing base with
  | nil => trivial
  | cons u rest ih =>
    have bound1 := bounded walk.1
    have bound2 := rank_upper rank bounded walk.2
    simp only [List.getLastD_cons, List.length_cons] at goalRank
    exact ⟨by omega, ih walk.2 (by omega)⟩

/-- The terminal at the other tip is reached by the whole two-ray path. -/
theorem terminal_between_tips (legal : LegalArms center words S) (a b : Arm) (distinct : a ≠ b) :
    Terminal (skeleton center words legal) ((words a).reverse ++ center :: words b)
      (.inl (tip words a)) (.inl (tip words b)) := by
  obtain ⟨trail, equals⟩ := List.head?_eq_some_iff.mp (route_head words a b)
  let g := skeleton center words legal
  let start : g.Item := .inl (tip words a)
  let finish : g.Item := .inl (tip words b)
  let full : List g.Item := (route words a b).map Sum.inl
  have form : full = start :: trail.map Sum.inl := by
    dsimp [full, start]
    rw [equals]
    rfl
  have walk := route_chain words a b
  rw [equals] at walk
  have edgeWalk : Chain g.edge start (trail.map Sum.inl) :=
    chain_map (W := g.Item) Sum.inl (fun h => h) walk
  have ends : full.getLast? = some finish := by
    change ((route words a b).map (Sum.inl : Node → Item K)).getLast? = _
    rw [List.getLast?_map, route_last]
    rfl
  have labels : full.map g.kind = (words a).reverse ++ center :: words b := by
    change ((route words a b).map (Sum.inl : Node → Item K)).map (itemClass center words) = _
    rw [List.map_map]
    exact route_class center words a b
  have basePresent : g.present start := tip_present words a
  let rank := itemRank words a
  have endOf : (trail.map (Sum.inl : Node → g.Item)).getLastD start = finish := by
    rw [form, getLast_eq] at ends
    exact Option.some.inj ends
  have length : (trail.map (Sum.inl : Node → g.Item)).length = (words a).length + (words b).length := by
    have size := route_length words a b
    rw [equals, List.length_cons] at size
    rw [List.length_map]
    omega
  have dist : rank ((trail.map (Sum.inl : Node → g.Item)).getLastD start) =
      rank start + (trail.map (Sum.inl : Node → g.Item)).length := by
    rw [endOf, length]
    simp only [rank, start, finish, tip_rank_zero, tip_rank words a b distinct, Nat.zero_add]
  have bound {u v : g.Item} (e : g.edge u v) : rank v ≤ rank u + 1 := by
    rcases edge_rank center words a e with f | r <;> dsimp [rank] <;> omega
  rw [form] at labels ends
  rw [← labels]
  exact terminal_of_ranked_chain (g := g) rank bound basePresent edgeWalk
    (geodesic_increases rank (R := g.edge) bound edgeWalk dist) ends

private theorem after_predecessor {V : Type} {E : V → V → Prop} (rank : V → Nat)
    (step : ∀ {u v}, E u v → rank v = rank u + 1 ∨ rank u = rank v + 1)
    (symm : ∀ {u v}, E u v → E v u)
    (uniqueLower : ∀ {u v w}, E v u → E v w → rank u < rank v → rank w < rank v → u = w)
    {previous current : V} {tail : List V} (incoming : E previous current)
    (fromBelow : rank previous < rank current) (walk : Chain E current tail)
    (distinct : (previous :: current :: tail).Nodup) :
    Chain (fun a b => E a b ∧ rank b = rank a + 1) current tail := by
  induction tail generalizing previous current with
  | nil => trivial
  | cons next rest ih =>
    have up : rank next = rank current + 1 := by
      rcases step walk.1 with same | down
      · exact same
      · have eq := uniqueLower (symm incoming) walk.1 fromBelow (by omega)
        exact ((List.nodup_cons.mp distinct).1 (by simp [eq])).elim
    exact ⟨⟨walk.1, up⟩,
      ih walk.1 (by omega) walk.2 (List.nodup_cons.mp distinct).2⟩

private theorem outward_from_zero {V : Type} {E : V → V → Prop} (rank : V → Nat)
    (step : ∀ {u v}, E u v → rank v = rank u + 1 ∨ rank u = rank v + 1)
    (symm : ∀ {u v}, E u v → E v u)
    (uniqueLower : ∀ {u v w}, E v u → E v w → rank u < rank v → rank w < rank v → u = w)
    {base : V} {tail : List V} (zero : rank base = 0) (walk : Chain E base tail)
    (distinct : (base :: tail).Nodup) :
    Chain (fun a b => E a b ∧ rank b = rank a + 1) base tail := by
  cases tail with
  | nil => trivial
  | cons first rest =>
    have up := (step walk.1).resolve_right (by omega)
    exact ⟨⟨walk.1,up⟩, after_predecessor rank step symm uniqueLower walk.1 (by omega) walk.2 distinct⟩

private theorem rank_end {V : Type} {E : V → V → Prop} (rank : V → Nat)
    {base : V} {trail : List V} (walk : Chain (fun a b => E a b ∧ rank b = rank a + 1) base trail) :
    rank (trail.getLastD base) = rank base + trail.length := by
  induction trail generalizing base with
  | nil => simp
  | cons first rest ih =>
    rw [List.getLastD_cons, ih walk.2, walk.1.2, List.length_cons]
    omega

private theorem snoc_nonempty {V : Type} {xs : List V} (ne : xs ≠ []) :
    ∃ left last, xs = left ++ [last] := by
  cases h : xs.getLast? with
  | none => exact (ne (List.getLast?_eq_none_iff.mp h)).elim
  | some a => obtain ⟨b, eq⟩ := List.getLast?_eq_some_iff.mp h; exact ⟨b,a,eq⟩

private theorem ranked_paths_unique {V : Type} {E : V → V → Prop} (rank : V → Nat)
    (symm : ∀ {u v}, E u v → E v u)
    (lowerUnique : ∀ {u v w}, E v u → E v w → rank u < rank v → rank w < rank v → u = w)
    {base : V} {left right : List V} (fuel : Nat) (leftSize : left.length ≤ fuel)
    (leftWalk : Chain (fun a b => E a b ∧ rank b = rank a + 1) base left)
    (rightWalk : Chain (fun a b => E a b ∧ rank b = rank a + 1) base right)
    (endpoints : left.getLastD base = right.getLastD base) : left = right := by
  have lengthEq : left.length = right.length := by
    have e1 := rank_end rank leftWalk
    have e2 := rank_end rank rightWalk
    rw [endpoints, e2] at e1
    omega
  induction fuel generalizing left right with
  | zero =>
    have l : left = [] := List.length_eq_zero_iff.mp (by omega)
    have r : right = [] := List.length_eq_zero_iff.mp (by omega)
    exact l.trans r.symm
  | succ fuel ih =>
    by_cases l : left = []
    · have r : right = [] := List.length_eq_zero_iff.mp (by simpa [l] using lengthEq.symm)
      exact l.trans r.symm
    · obtain ⟨lt,lastL,rfl⟩ := snoc_nonempty l
      have r : right ≠ [] := by intro empty; simp [empty] at lengthEq
      obtain ⟨rt,lastR,rfl⟩ := snoc_nonempty r
      simp only [getLastD_append_singleton] at endpoints
      subst lastR
      obtain ⟨pWalk, endL, stepL⟩ := (chain_snoc_iff _ _ _).mp leftWalk
      obtain ⟨qWalk, endR, stepR⟩ := (chain_snoc_iff _ _ _).mp rightWalk
      have prevEq : lt.getLastD base = rt.getLastD base :=
        lowerUnique (symm endL) (symm endR) (by omega) (by omega)
      have bound : lt.length ≤ fuel := by simpa using leftSize
      rw [ih bound pWalk qWalk prevEq (by simpa using lengthEq)]

/-- At a fixed tip, the path word of any reached item is unique. In particular another
conditioning variable cannot name a selected endpoint by a different word. -/
theorem terminal_word_unique (legal : LegalArms center words S) (a : Arm)
    {u : (skeleton center words legal).Item} {p q : List K}
    (first : Terminal (skeleton center words legal) p (.inl (tip words a)) u)
    (second : Terminal (skeleton center words legal) q (.inl (tip words a)) u) : p = q := by
  obtain ⟨l, walkL, formL, endL, ndL⟩ := trace_of_terminal first
  obtain ⟨r, walkR, formR, endR, ndR⟩ := trace_of_terminal second
  let rank := itemRank words a
  have step {u v : Item K} (e : edge (S := S) center words u v) :
      rank v = rank u + 1 ∨ rank u = rank v + 1 := edge_rank center words a e
  have symm {u v : Item K} (e : edge (S := S) center words u v) := edge_symm center words e
  have lower {u v w : Item K} (vu : edge (S := S) center words v u)
      (vw : edge (S := S) center words v w) (l : rank u < rank v) (r : rank w < rank v) :=
    edge_lower_unique center words a vu vw l r
  have leftRank := outward_from_zero rank step symm lower (tip_rank_zero words a) walkL ndL
  have rightRank := outward_from_zero rank step symm lower (tip_rank_zero words a) walkR ndR
  have eL := getLast_eq (V := (skeleton center words legal).Item) (.inl (tip words a)) l
  have eR := getLast_eq (V := (skeleton center words legal).Item) (.inl (tip words a)) r
  have ends := Option.some.inj (eL.symm.trans (endL.trans (endR.symm.trans eR)))
  have sameTail := ranked_paths_unique rank symm lower l.length (Nat.le_refl _)
    leftRank rightRank ends
  subst r
  exact formL.symm.trans formR

end RCDThreeArm

end
