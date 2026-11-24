module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.PositiveHedgeWitness

/-! # Directed XOR transport on a ranked hedge forest

[Lee and Bareinboim, corrected R-58](https://www.sanghacklee.me/ai-corrected/R58_AI_corrected_2026-10-25.pdf),
Appendix B, proof of Lemma 7: the structural facts (C2)–(C4) and the paragraphs
"The hedge coordinates" and "Observational agreement".

In model one each hedge coordinate is the XOR of its parents in `F` and of its
exogenous input `ξ_v`. `transport g ξ` evaluates these mechanisms in rank order
on an indexed DAG. The local residual `x_v ⊕ ⊕_{p → v} x_p` is a two-sided
inverse, so the transport preserves zero, is XOR-linear and is bijective. When
every vertex has at most one child (C2), the effect of a singleton input has
exactly one vertex without a child in its support. This is the root-parity
hypothesis of `connected_transported_fair_masks_cover`. Model two removes the
reads of `F′` from outside `F′`. Under (C3) and `R ⊆ F′` this gives the
hypothesis of `trimmed_transported_fair_masks_cover`. Private source bits with
the singleton effects give emission coverage, and
`forest_equal_positive_observational_laws` combines these results through
`equal_positive_observational_laws`.

The forest, the side `F′`, the bidirected graphs and the channel lists are
indexed hypotheses here. Constructing them from the original graph `G` is a
separate step, including the coordinates of realized paths, the coin
coordinates and the accumulated noises. So is the post-intervention incidence
used by `target_difference_from_intervention_cut`.
-/

namespace OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.DirectedTransport

@[expose] public section

open HedgeNoise PositiveHedgeWitness
open OpenCausalScience.Papers.LeeEtAl2019.GeneralIdentifiabilityErratum (xorAll)
open OpenCausalScience.Papers.LeeEtAl2019.CorrectedConverse (Bottom Walk)

variable {n : Nat}

private theorem xorAll_map_xor {α : Type} (xs : List α) (f h : α → Bool) :
    xorAll (xs.map fun x => Bool.xor (f x) (h x)) =
      Bool.xor (xorAll (xs.map f)) (xorAll (xs.map h)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, xorAll, ih, Bool.xor_assoc]
    exact congrArg (Bool.xor (f x)) (Bool.xor_left_comm _ _ _)

private theorem xorAll_one_hot {α : Type} [DecidableEq α] (xs : List α) (a : α)
    (unique : xs.Nodup) (value : Bool) :
    xorAll (xs.map fun x => decide (x = a) && value) = (decide (a ∈ xs) && value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨notMem, tailUnique⟩ := List.nodup_cons.mp unique
    by_cases equal : x = a
    · subst x
      simp [xorAll, ih tailUnique, notMem]
    · simp [xorAll, ih tailUnique, equal, Ne.symm equal]

private theorem bool_xor_interchange (a b c d : Bool) :
    Bool.xor (Bool.xor a b) (Bool.xor c d) = Bool.xor (Bool.xor a c) (Bool.xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem atom_bit (v j : Fin n) : (atom v).getLsbD j.val = decide (v = j) := by
  simp only [atom, BitVec.getLsbD_twoPow, v.isLt, decide_true, Bool.true_and, Fin.val_inj]

private theorem ext_bits {a b : BitVec n}
    (same : ∀ j : Fin n, a.getLsbD j.val = b.getLsbD j.val) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  exact same ⟨k, hk⟩

private theorem eq_xor_of_xor_eq {a b c : BitVec n} (h : a ^^^ b = c) : a = c ^^^ b := by
  rw [← h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The mask whose listed coordinates carry the given bits. -/
def gatherBits (bit : Fin n → Bool) : List (Fin n) → BitVec n
  | [] => 0
  | v :: vs => (if bit v then atom v else 0) ^^^ gatherBits bit vs

/-- The mask whose coordinate `v` is `bit v`. -/
def ofBits (bit : Fin n → Bool) : BitVec n := gatherBits bit (List.finRange n)

private theorem select_atom_bit (b : Bool) (v j : Fin n) :
    (if b = true then atom v else 0).getLsbD j.val = (b && decide (v = j)) := by
  cases b
  · simp
  · exact atom_bit v j

private theorem gather_bits_bit (bit : Fin n → Bool) (vs : List (Fin n)) (unique : vs.Nodup)
    (j : Fin n) : (gatherBits bit vs).getLsbD j.val = (decide (j ∈ vs) && bit j) := by
  induction vs with
  | nil => simp [gatherBits]
  | cons v vs ih =>
    obtain ⟨notMem, tailUnique⟩ := List.nodup_cons.mp unique
    simp only [gatherBits, BitVec.getLsbD_xor, select_atom_bit, ih tailUnique, List.mem_cons]
    by_cases same : v = j
    · subst same
      simp [notMem]
    · simp [same, Ne.symm same]

theorem getLsbD_ofBits (bit : Fin n → Bool) (j : Fin n) :
    (ofBits bit).getLsbD j.val = bit j := by
  simpa [ofBits, List.mem_finRange] using
    gather_bits_bit bit (List.finRange n) (List.nodup_finRange n) j

/-! ## The transport on a ranked DAG -/

/-- Parity of the bits of `x` at the predecessors of `v`. -/
def readParity (g : DAG n) (x : BitVec n) (v : Fin n) : Bool :=
  xorAll ((List.finRange n).map fun p => g.edge p v && x.getLsbD p.val)

/-- The directed XOR mechanisms, evaluated in rank order. The output at `v`
is its source bit XOR the outputs of all predecessors of `v`. -/
def output (g : DAG n) (source : BitVec n) (v : Fin n) : Bool :=
  Bool.xor (source.getLsbD v.val)
    (xorAll ((List.finRange n).map fun p =>
      if _h : g.edge p v = true then output g source p else false))
termination_by g.rank v
decreasing_by exact g.edge_increases _ _ _h

/-- All outputs of the directed mechanisms as a coordinate mask. -/
def transport (g : DAG n) (source : BitVec n) : BitVec n := ofBits (output g source)

/-- The local residual: each coordinate XOR the coordinates it reads. -/
def residual (g : DAG n) (x : BitVec n) : BitVec n :=
  ofBits fun v => Bool.xor (x.getLsbD v.val) (readParity g x v)

theorem getLsbD_transport (g : DAG n) (source : BitVec n) (v : Fin n) :
    (transport g source).getLsbD v.val = output g source v :=
  getLsbD_ofBits (output g source) v

theorem getLsbD_residual (g : DAG n) (x : BitVec n) (v : Fin n) :
    (residual g x).getLsbD v.val = Bool.xor (x.getLsbD v.val) (readParity g x v) :=
  getLsbD_ofBits (fun u => Bool.xor (x.getLsbD u.val) (readParity g x u)) v

/-- Each transported coordinate is its source bit XOR the transported
coordinates of its predecessors. -/
theorem output_eq_source_xor_reads (g : DAG n) (source : BitVec n) (v : Fin n) :
    output g source v =
      Bool.xor (source.getLsbD v.val) (readParity g (transport g source) v) := by
  rw [output]
  apply congrArg (Bool.xor (source.getLsbD v.val))
  apply congrArg xorAll
  apply List.map_congr_left
  intro p _
  rw [getLsbD_transport]
  by_cases h : g.edge p v = true
  · rw [dite_eq_left h, h, Bool.true_and]
  · rw [dite_eq_right h, Bool.eq_false_iff.mpr h, Bool.false_and]

/-- The residual is a left inverse of the transport. -/
theorem residual_transport (g : DAG n) (source : BitVec n) :
    residual g (transport g source) = source := by
  apply ext_bits
  intro v
  rw [getLsbD_residual, getLsbD_transport, output_eq_source_xor_reads, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false]

private theorem output_residual (g : DAG n) (x : BitVec n) :
    ∀ k v, g.rank v < k → output g (residual g x) v = x.getLsbD v.val := by
  intro k
  induction k with
  | zero => intro v bound; exact absurd bound (Nat.not_lt_zero _)
  | succ k ih =>
    intro v bound
    have parents : xorAll ((List.finRange n).map fun p =>
        if _h : g.edge p v = true then output g (residual g x) p else false) =
        readParity g x v := by
      apply congrArg xorAll
      apply List.map_congr_left
      intro p _
      by_cases h : g.edge p v = true
      · rw [dite_eq_left h, h, Bool.true_and]
        exact ih p (Nat.lt_of_lt_of_le (g.edge_increases p v h) (Nat.le_of_lt_succ bound))
      · rw [dite_eq_right h, Bool.eq_false_iff.mpr h, Bool.false_and]
    rw [output, parents, getLsbD_residual, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The residual is a right inverse of the transport. -/
theorem transport_residual (g : DAG n) (x : BitVec n) : transport g (residual g x) = x := by
  apply ext_bits
  intro v
  rw [getLsbD_transport]
  exact output_residual g x _ v (Nat.lt_succ_self _)

theorem read_parity_xor (g : DAG n) (a b : BitVec n) (v : Fin n) :
    readParity g (a ^^^ b) v = Bool.xor (readParity g a v) (readParity g b v) := by
  simp only [readParity, BitVec.getLsbD_xor, Bool.and_xor_distrib_left, xorAll_map_xor]

theorem residual_xor (g : DAG n) (a b : BitVec n) :
    residual g (a ^^^ b) = residual g a ^^^ residual g b := by
  apply ext_bits
  intro v
  rw [BitVec.getLsbD_xor, getLsbD_residual, getLsbD_residual, getLsbD_residual,
    BitVec.getLsbD_xor, read_parity_xor]
  exact bool_xor_interchange _ _ _ _

/-- XOR linearity of the transport. -/
theorem transport_xor (g : DAG n) (a b : BitVec n) :
    transport g (a ^^^ b) = transport g a ^^^ transport g b := by
  have h := congrArg (transport g) (residual_xor g (transport g a) (transport g b))
  rw [transport_residual, residual_transport, residual_transport] at h
  exact h.symm

theorem transport_zero (g : DAG n) : transport g 0 = 0 := by
  have h := transport_xor g 0 0
  rw [BitVec.xor_self, BitVec.xor_self] at h
  exact h

theorem transport_surjective (g : DAG n) (out : BitVec n) :
    ∃ source, transport g source = out :=
  ⟨residual g out, transport_residual g out⟩

theorem transport_injective (g : DAG n) {a b : BitVec n}
    (same : transport g a = transport g b) : a = b := by
  rw [← residual_transport g a, same, residual_transport]

/-! ## Forests with unique successors -/

/-- A ranked directed forest: each vertex has at most one child, of larger
rank. This is (C2) in the proof of Lemma 7. -/
structure Forest (n : Nat) where
  child : Fin n → Option (Fin n)
  rank : Fin n → Nat
  ordered : ∀ p c, child p = some c → rank p < rank c

/-- The arrows `p → ch(p)` of the forest as a ranked DAG. -/
def Forest.toDAG (f : Forest n) : DAG n where
  edge p c := decide (f.child p = some c)
  rank := f.rank
  edge_increases p c h := f.ordered p c (of_decide_eq_true h)

theorem Forest.toDAG_edge (f : Forest n) (p c : Fin n) :
    f.toDAG.edge p c = decide (f.child p = some c) := rfl

/-- A vertex without a child. In model one these vertices form `R`. -/
def Forest.isRoot (f : Forest n) (v : Fin n) : Bool := (f.child v).isNone

/-- The descending chain `a, ch(a), ch²(a), …` of a vertex ends at `r`. -/
inductive Forest.Reaches (f : Forest n) : Fin n → Fin n → Prop
  | terminal {r : Fin n} : f.child r = none → Forest.Reaches f r r
  | step {v c r : Fin n} : f.child v = some c → Forest.Reaches f c r → Forest.Reaches f v r

theorem Forest.Reaches.child_eq_none {f : Forest n} {v r : Fin n} (reach : f.Reaches v r) :
    f.child r = none := by
  induction reach with
  | terminal noChild => exact noChild
  | step _ _ ih => exact ih

private theorem rank_le_sum (f : Forest n) (v : Fin n) :
    f.rank v ≤ ((List.finRange n).map f.rank).sum := by
  have member : v ∈ List.finRange n := List.mem_finRange v
  generalize List.finRange n = xs at member ⊢
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp member with same | later
    · subst same
      omega
    · have bound := ih later
      omega

/-- (C2) Every descending chain ends at a vertex without a child. -/
theorem Forest.reaches_terminal (f : Forest n) (v : Fin n) : ∃ r, f.Reaches v r := by
  have climb : ∀ k v, ((List.finRange n).map f.rank).sum - f.rank v < k →
      ∃ r, f.Reaches v r := by
    intro k
    induction k with
    | zero => intro v bound; exact absurd bound (Nat.not_lt_zero _)
    | succ k ih =>
      intro v bound
      cases e : f.child v with
      | none => exact ⟨v, .terminal e⟩
      | some c =>
        have up := f.ordered v c e
        have below := rank_le_sum f c
        obtain ⟨r, reach⟩ := ih c (by omega)
        exact ⟨r, .step e reach⟩
  exact climb _ v (Nat.lt_succ_self _)

theorem read_parity_atom (g : DAG n) (w v : Fin n) :
    readParity g (atom w) v = g.edge w v := by
  unfold readParity
  have pointwise : (List.finRange n).map (fun p => g.edge p v && (atom w).getLsbD p.val) =
      (List.finRange n).map (fun p => decide (p = w) && g.edge w v) := by
    apply List.map_congr_left
    intro p _
    rw [atom_bit]
    by_cases same : p = w
    · subst same
      simp
    · simp [same, Ne.symm same]
  rw [pointwise, xorAll_one_hot _ _ (List.nodup_finRange _)]
  simp

private theorem forest_residual_atom_bit (f : Forest n) (v u : Fin n) :
    (residual f.toDAG (atom v)).getLsbD u.val =
      Bool.xor (decide (v = u)) (decide (f.child v = some u)) := by
  rw [getLsbD_residual, read_parity_atom, atom_bit, Forest.toDAG_edge]

/-- A singleton input at a vertex with child `c` is transported to the vertex
itself together with the transported singleton at `c`. -/
theorem transport_atom_step (f : Forest n) {v c : Fin n} (edge : f.child v = some c) :
    transport f.toDAG (atom v) = atom v ^^^ transport f.toDAG (atom c) := by
  have residualAtom : residual f.toDAG (atom v) = atom v ^^^ atom c := by
    apply ext_bits
    intro u
    rw [forest_residual_atom_bit, edge, BitVec.getLsbD_xor, atom_bit, atom_bit]
    simp
  apply eq_xor_of_xor_eq
  rw [← transport_xor, ← residualAtom, transport_residual]

theorem transport_atom_terminal (f : Forest n) {r : Fin n} (noChild : f.child r = none) :
    transport f.toDAG (atom r) = atom r := by
  have residualAtom : residual f.toDAG (atom r) = atom r := by
    apply ext_bits
    intro u
    rw [forest_residual_atom_bit, noChild, atom_bit]
    simp
  have h := transport_residual f.toDAG (atom r)
  rw [residualAtom] at h
  exact h

/-- At a vertex without a child, a transported singleton is one exactly when
that vertex ends the singleton's descending chain. -/
theorem transport_atom_terminal_bit (f : Forest n) {v r : Fin n} (reach : f.Reaches v r)
    (u : Fin n) (isTerminal : f.child u = none) :
    (transport f.toDAG (atom v)).getLsbD u.val = decide (r = u) := by
  induction reach with
  | terminal noChild => rw [transport_atom_terminal f noChild, atom_bit]
  | @step w c t edge _ ih =>
    have distinct : w ≠ u := by
      intro same
      rw [same, isTerminal] at edge
      cases edge
    rw [transport_atom_step f edge, BitVec.getLsbD_xor, ih, atom_bit, decide_eq_false distinct,
      Bool.false_xor]

/-- (C2) The effect of a singleton input reaches exactly one vertex without a
child, the end of its descending chain. -/
theorem transport_atom_reaches_one_terminal (f : Forest n) (v : Fin n) :
    ∃ r, f.Reaches v r ∧ ∀ u, f.child u = none →
      ((transport f.toDAG (atom v)).getLsbD u.val = true ↔ u = r) := by
  obtain ⟨r, reach⟩ := f.reaches_terminal v
  refine ⟨r, reach, fun u isTerminal => ?_⟩
  rw [transport_atom_terminal_bit f reach u isTerminal]
  exact ⟨fun h => (of_decide_eq_true h).symm, fun h => decide_eq_true h.symm⟩

/-! ## Root parities -/

/-- XOR of the coordinates chosen by `selected`. -/
def selectedValue (selected : Fin n → Bool) (x : BitVec n) : Bool :=
  xorAll ((List.finRange n).map fun v => selected v && x.getLsbD v.val)

theorem selected_value_xor (selected : Fin n → Bool) (a b : BitVec n) :
    selectedValue selected (a ^^^ b) =
      Bool.xor (selectedValue selected a) (selectedValue selected b) := by
  simp only [selectedValue, BitVec.getLsbD_xor, Bool.and_xor_distrib_left, xorAll_map_xor]

theorem selected_value_zero (selected : Fin n → Bool) : selectedValue selected 0 = false := by
  have h := selected_value_xor selected 0 0
  rw [BitVec.xor_self, Bool.xor_self] at h
  exact h

/-- The parity of the coordinates chosen by `selected`, as a linear Boolean map. -/
def selectedParity (selected : Fin n → Bool) : Parity n :=
  ⟨selectedValue selected, selected_value_zero selected, selected_value_xor selected⟩

/-- The root parity `χ_R` of Lemma 7, where `R` is the set of vertices of `F`
without a child. -/
def rootParity (f : Forest n) : Parity n := selectedParity f.isRoot

/-- If only vertices without a child are selected, the selected parity of a
transported singleton is the selection at the end of its chain. -/
theorem selected_parity_transport_atom (f : Forest n) (selected : Fin n → Bool)
    (selectedTerminal : ∀ u, selected u = true → f.child u = none) {v r : Fin n}
    (reach : f.Reaches v r) :
    (selectedParity selected).value (transport f.toDAG (atom v)) = selected r := by
  change xorAll ((List.finRange n).map fun u =>
    selected u && (transport f.toDAG (atom v)).getLsbD u.val) = selected r
  have pointwise : ((List.finRange n).map fun u =>
      selected u && (transport f.toDAG (atom v)).getLsbD u.val) =
      (List.finRange n).map (fun u => decide (u = r) && selected r) := by
    apply List.map_congr_left
    intro u _
    cases h : selected u
    · by_cases same : u = r
      · subst same
        simp [h]
      · simp [same]
    · rw [transport_atom_terminal_bit f reach u (selectedTerminal u h)]
      by_cases same : u = r
      · subst same
        simp [h]
      · simp [same, Ne.symm same]
  rw [pointwise, xorAll_one_hot _ _ (List.nodup_finRange _)]
  simp

/-- Model one: each singleton input reaches exactly one root, so its root
parity is odd. This is `oneRoot` in `connected_transported_fair_masks_cover`. -/
theorem root_parity_transport_atom (f : Forest n) (v : Fin n) :
    (rootParity f).value (transport f.toDAG (atom v)) = true := by
  obtain ⟨r, reach⟩ := f.reaches_terminal v
  have h := selected_parity_transport_atom f f.isRoot
    (fun _ root => Option.isNone_iff_eq_none.mp root) reach
  rw [show f.isRoot r = true from Option.isNone_iff_eq_none.mpr reach.child_eq_none] at h
  exact h

/-! ## Model two's trimmed forest -/

/-- Model two's successor map. A vertex outside `F′` is no longer read by a
child in `F′`. -/
def trimChild (f : Forest n) (inner : Fin n → Bool) (p : Fin n) : Option (Fin n) :=
  match f.child p with
  | none => none
  | some c => if inner c = true ∧ inner p = false then none else some c

theorem trim_child_some {f : Forest n} {inner : Fin n → Bool} {p c : Fin n}
    (h : trimChild f inner p = some c) :
    f.child p = some c ∧ (inner c = true → inner p = true) := by
  unfold trimChild at h
  cases e : f.child p with
  | none => simp [e] at h
  | some d =>
    simp only [e] at h
    by_cases cut : inner d = true ∧ inner p = false
    · rw [ite_eq_left cut] at h
      cases h
    · rw [ite_eq_right cut] at h
      cases h
      refine ⟨rfl, fun ic => ?_⟩
      cases ip : inner p
      · exact (cut ⟨ic, ip⟩).elim
      · rfl

theorem trim_child_of_inner {f : Forest n} {inner : Fin n → Bool} {p c : Fin n}
    (edge : f.child p = some c) (ip : inner p = true) : trimChild f inner p = some c := by
  simp [trimChild, edge, ip]

theorem trim_child_of_root {f : Forest n} {inner : Fin n → Bool} {p : Fin n}
    (root : f.child p = none) : trimChild f inner p = none := by
  simp [trimChild, root]

/-- Model two's forest. The vertices of `F′` read only their parents in `F′`,
and the vertices of `F \ F′` read as in model one. -/
def Forest.trim (f : Forest n) (inner : Fin n → Bool) : Forest n where
  child := trimChild f inner
  rank := f.rank
  ordered p c h := f.ordered p c (trim_child_some h).1

theorem Forest.trim_child (f : Forest n) (inner : Fin n → Bool) (p : Fin n) :
    (f.trim inner).child p = trimChild f inner p := rfl

/-- (C3) and `R ⊆ F′`. In model two the chain of `v` ends at a root of `F`
exactly when `v ∈ F′`. -/
theorem trim_reaches_root (f : Forest n) (inner : Fin n → Bool)
    (closed : ∀ p c, f.child p = some c → inner p = true → inner c = true)
    (rootsInner : ∀ v, f.child v = none → inner v = true) {v r : Fin n}
    (reach : (f.trim inner).Reaches v r) : f.isRoot r = inner v := by
  induction reach with
  | @terminal r noChild =>
    rw [Forest.trim_child] at noChild
    unfold Forest.isRoot
    cases e : f.child r with
    | none => exact (rootsInner r e).symm
    | some d =>
      cases ir : inner r
      · rfl
      · have clash := (trim_child_of_inner (inner := inner) e ir).symm.trans noChild
        cases clash
  | @step w c t edge _ ih =>
    rw [Forest.trim_child] at edge
    obtain ⟨parent, keep⟩ := trim_child_some edge
    rw [ih]
    cases iw : inner w
    · cases ic : inner c
      · rfl
      · have up := keep ic
        rw [iw] at up
        cases up
    · exact closed w c parent iw

/-- Model two: a transported singleton has odd root parity exactly when its
vertex lies in `F′`. This is `reachesRoot` in
`trimmed_transported_fair_masks_cover`. -/
theorem trim_parity_transport_atom (f : Forest n) (inner : Fin n → Bool)
    (closed : ∀ p c, f.child p = some c → inner p = true → inner c = true)
    (rootsInner : ∀ v, f.child v = none → inner v = true) (v : Fin n) :
    (rootParity f).value (transport (f.trim inner).toDAG (atom v)) = inner v := by
  obtain ⟨r, reach⟩ := (f.trim inner).reaches_terminal v
  have h := selected_parity_transport_atom (f.trim inner) f.isRoot
    (fun u root => (Forest.trim_child f inner u).trans
      (trim_child_of_root (Option.isNone_iff_eq_none.mp root))) reach
  rw [trim_reaches_root f inner closed rootsInner reach] at h
  exact h

/-! ## Fair masks of the two models -/

/-- Model one's fair coins cover the kernel of `χ_R`. The transport is the
forest transport. The coin reads are the remaining hypotheses. -/
theorem forest_fair_masks_cover {edges : Nat} (f : Forest n) (g : Bottom n edges)
    (channels : List (Channel n)) (pivot : Fin n)
    (readEdge : ∀ e, Generated channels
      (transport f.toDAG (atom (g.left e) ^^^ atom (g.right e))))
    (connected : ∀ v, Walk g v pivot) :
    ∀ out, (rootParity f).value out = false → Generated channels out :=
  connected_transported_fair_masks_cover g channels (rootParity f) pivot (transport f.toDAG)
    (transport_zero f.toDAG) (transport_xor f.toDAG) (transport_surjective f.toDAG) readEdge
    connected (root_parity_transport_atom f)

/-- Model two's fair coins cover the kernel of the same root parity, using the
trimmed forest transport. -/
theorem trimmed_forest_fair_masks_cover {fullEdges bottomEdges : Nat} (f : Forest n)
    (inner : Fin n → Bool)
    (closed : ∀ p c, f.child p = some c → inner p = true → inner c = true)
    (rootsInner : ∀ v, f.child v = none → inner v = true)
    (full : Bottom n fullEdges) (bottom : Bottom n bottomEdges)
    (channels : List (Channel n)) (pivot : Fin n) (pivotInner : inner pivot = true)
    (bottomRead : ∀ e, Generated channels
      (transport (f.trim inner).toDAG (atom (bottom.left e) ^^^ atom (bottom.right e))))
    (upperRead : ∀ e, inner (full.left e) = false ∨ inner (full.right e) = false →
      Generated channels (transport (f.trim inner).toDAG
        (upperFootprint inner (full.left e) ^^^ upperFootprint inner (full.right e))))
    (fullConnected : ∀ v, Walk full v pivot)
    (bottomConnected : ∀ v, inner v = true → Walk bottom v pivot) :
    ∀ out, (rootParity f).value out = false → Generated channels out :=
  trimmed_transported_fair_masks_cover full bottom channels (rootParity f) pivot inner pivotInner
    (transport (f.trim inner).toDAG) (transport_zero _) (transport_xor _)
    (transport_surjective _) bottomRead upperRead fullConnected bottomConnected
    (trim_parity_transport_atom f inner closed rootsInner)

/-! ## Emission coverage from private source bits -/

/-- Adding channels preserves emission, by skipping the added bits. -/
theorem emits_of_sublist {xs ys : List (Channel n)} (sub : xs.Sublist ys) :
    ∀ mask, Emits xs mask → Emits ys mask := by
  induction sub with
  | slnil => exact fun _ emitted => emitted
  | cons a _ ih => exact fun mask emitted => .skip a (ih mask emitted)
  | cons_cons a _ ih =>
    intro mask emitted
    cases emitted with
    | skip _ rest => exact .skip a (ih _ rest)
    | flip _ rest => exact .flip a (ih _ rest)

private theorem emits_transported_support (transport : BitVec n → BitVec n)
    (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b)) :
    ∀ (vs : List (Fin n)) (privates : List (Channel n)),
      privates.map Channel.effect = vs.map (fun v => transport (atom v)) →
      ∀ mask : BitVec n, (∀ j : Fin n, mask.getLsbD j.val = true → j ∈ vs) →
        Emits privates (transport mask) := by
  intro vs
  induction vs with
  | nil =>
    intro privates effects mask supported
    cases privates with
    | cons _ _ => simp at effects
    | nil =>
      have cleared : mask = 0 := by
        apply ext_bits
        intro j
        cases h : mask.getLsbD j.val
        · simp
        · exact False.elim (List.not_mem_nil (supported j h))
      rw [cleared, zero]
      exact .zero
  | cons v vs ih =>
    intro privates effects mask supported
    cases privates with
    | nil => simp at effects
    | cons ch rest =>
      simp only [List.map_cons, List.cons.injEq] at effects
      obtain ⟨chEffect, restEffects⟩ := effects
      cases bit : mask.getLsbD v.val
      · apply Emits.skip
        apply ih rest restEffects mask
        intro j active
        rcases List.mem_cons.mp (supported j active) with same | later
        · subst same
          rw [bit] at active
          cases active
        · exact later
      · have restored : transport mask = transport (mask ^^^ atom v) ^^^ ch.effect := by
          rw [chEffect, ← linear, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        rw [restored]
        apply Emits.flip
        apply ih rest restEffects
        intro j active
        rw [BitVec.getLsbD_xor, atom_bit] at active
        by_cases same : v = j
        · subst same
          rw [bit, show decide (v = v) = true by simp, Bool.xor_self] at active
          cases active
        · rw [decide_eq_false same, Bool.xor_false] at active
          exact (List.mem_cons.mp (supported j active)).resolve_left (Ne.symm same)

/-- Coordinate coverage. Suppose a sublist of the channels contains one private
bit per coordinate, with effect the transported singleton at that coordinate.
Then every joint value of the coordinates is emitted. -/
theorem emits_of_private_sources (transport : BitVec n → BitVec n) (zero : transport 0 = 0)
    (linear : ∀ a b, transport (a ^^^ b) = (transport a ^^^ transport b))
    (surjective : ∀ out, ∃ mask, transport mask = out)
    (channels privates : List (Channel n)) (present : privates.Sublist channels)
    (effects : privates.map Channel.effect =
      (List.finRange n).map fun v => transport (atom v)) :
    ∀ out, Emits channels out := by
  intro out
  obtain ⟨mask, rfl⟩ := surjective out
  exact emits_of_sublist present _ (emits_transported_support transport zero linear
    (List.finRange n) privates effects mask (fun j _ => List.mem_finRange j))

theorem emits_of_private_transport_sources (g : DAG n) (channels privates : List (Channel n))
    (present : privates.Sublist channels)
    (effects : privates.map Channel.effect =
      (List.finRange n).map fun v => transport g (atom v)) :
    ∀ out, Emits channels out :=
  emits_of_private_sources (transport g) (transport_zero g) (transport_xor g)
    (transport_surjective g) channels privates present effects

/-- Lemma 7, observational agreement and positivity on the indexed hedge
coordinates. The forest transports supply zero, linearity, surjectivity, both
root-parity hypotheses and emission coverage. The other premises are explicit:
(C1) as `fullConnected` and `bottomConnected`, (C3) as `closed`, `R ⊆ F′` as
`rootsInner`, the projected noise weights, the coin reads, positivity of every
channel, and one private bit per coordinate in model one. -/
theorem forest_equal_positive_observational_laws {fullEdges bottomEdges : Nat}
    (f : Forest n) (inner : Fin n → Bool)
    (closed : ∀ p c, f.child p = some c → inner p = true → inner c = true)
    (rootsInner : ∀ v, f.child v = none → inner v = true)
    (full : Bottom n fullEdges) (bottom : Bottom n bottomEdges) (pivot : Fin n)
    (pivotInner : inner pivot = true)
    (fullConnected : ∀ v, Walk full v pivot)
    (bottomConnected : ∀ v, inner v = true → Walk bottom v pivot)
    (first second : List (Channel n)) (shared dropped : List BitWeights)
    (firstProjection : first.map (rootParity f).project = shared ++ dropped)
    (secondProjection : second.map (rootParity f).project = shared ++ [parityWeights dropped])
    (firstRead : ∀ e, Generated first
      (transport f.toDAG (atom (full.left e) ^^^ atom (full.right e))))
    (bottomRead : ∀ e, Generated second
      (transport (f.trim inner).toDAG (atom (bottom.left e) ^^^ atom (bottom.right e))))
    (upperRead : ∀ e, inner (full.left e) = false ∨ inner (full.right e) = false →
      Generated second (transport (f.trim inner).toDAG
        (upperFootprint inner (full.left e) ^^^ upperFootprint inner (full.right e))))
    (weights : ∀ ch ∈ first, ch.Positive)
    (privates : List (Channel n)) (present : privates.Sublist first)
    (effects : privates.map Channel.effect =
      (List.finRange n).map fun v => transport f.toDAG (atom v)) :
    run first 0 = run second 0 ∧ ∀ out, 0 < run first 0 out ∧ 0 < run second 0 out :=
  equal_positive_observational_laws (rootParity f) first second shared dropped
    firstProjection secondProjection
    (forest_fair_masks_cover f full first pivot firstRead fullConnected)
    (trimmed_forest_fair_masks_cover f inner closed rootsInner full bottom second pivot
      pivotInner bottomRead upperRead fullConnected bottomConnected)
    weights (emits_of_private_transport_sources f.toDAG first privates present effects)

end

end OpenCausalScience.Papers.LeeBareinboim2020PartialObservability.DirectedTransport
