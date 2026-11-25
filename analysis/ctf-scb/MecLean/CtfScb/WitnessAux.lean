import MecLean.CtfScb.Defs

set_option linter.unusedSectionVars false

/-!
# The witness model of `thm: ctf-pomis`, "if" (helper for `MecLean.CtfScb.Witness`)

Fix `G`, `y` and a specification `F`, and let `T = An(Y)_{𝒢_F}` (`diagH (G.cutE F) y ∅`).  When
the border of `𝓗_F = 𝒢_F[T]` is empty, `T` is the minimal UC-territory of `𝒢_F`
(`muct_eq_diagH_of_ctfIB` in `Border`).  `ctfPomis_of_muct` takes this as its hypothesis and
builds one model conforming to `𝒢` in which the best assignment of `F` has mean one and every
non-equivalent specification has best mean at most `1/2`.

## The model

Every root of `Mech.ofADMG` is a fair coin.  Every vertex takes values in
`Val n K = Option (Roots n → ZMod K) ⊕ Fin n`: a coordinate tuple `inl (some t)`, the invalid
value `inl none`, or the reserved value `inr w`, designated for the selected inputs of `f_w`.
No mechanism outputs a reserved value (`isRes_respE`).

* A vertex outside `T` records its own roots (`own`): coordinate `l` is the coin `l` when `l` is
  one of its roots.
* A vertex `v ∈ T` checks its inputs (`Chk`): every selected input `(p, v) ∈ F` must carry
  `inr v`, and every unselected input must be a tuple.  On a failure it outputs `inl none`;
  otherwise it outputs the record of its roots plus the coordinates of its unselected parents
  (`comb`).
* The reward is one when the value of `y` is a tuple whose coordinate `l` is `0` or
  `cnt_F(l)` (`Good`).  Here `cnt G F T E l v` counts the directed paths of `𝒢_F` that start at a
  vertex reading root `l`, continue inside `T`, use no edge of `E` and end at `v`, and
  `cnt_F = cnt G F T ∅`.

## The argument

* The designated values `cstar` (every selected input of `f_w` receives `inr w`) pass every
  check, and coordinate `l` of every vertex `w` is `[coin l] · cnt_F(l, w)` (`respE_cstar`).
  The designated assignment has mean one (`muE_cstar`).
* Under any specification `F'` with values `c'`, which vertices output tuples does not depend on
  the coins (`isTup_respE`), and coordinate `l` of a tuple is a constant plus
  `[coin l] · cnt_{F'}(l)` (`coord_respE`).
* If `F'` selects an edge of `𝓗_F`, the live/non-live split of `ScbMec.LB18.exists_split`, with
  edges in place of intervened vertices (`exists_split`), gives a root `l` shared by some `a ↔ b`
  in `T` with `0 < cnt_{F'}(l, y) < cnt_F(l, y)` (`key_coord`).  Flipping coin `l` moves
  coordinate `l` of `y` by `cnt_{F'}(l, y)`, so at most one of the two states is rewarded
  (`LB18.zmod_aux`), and every assignment of `F'` has mean at most `1/2` (`muE_le_half`, by
  `LB18.E_le_half`).
* If `F'` selects no edge of `𝓗_F` and is not equivalent to `F`, it leaves some selected input
  `(p, v) ∈ F` with `v ∈ T` unselected (`relevant_eq_of_noEdge`).  Then `f_v` receives a natural
  value, outputs `inl none`, and `inl none` reaches `y` along `𝓗_F` (`respE_none_start`,
  `respE_none_reach`): every assignment of `F'` has mean `0` (`muE_le_half_none`).
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

namespace CtfWit

/-! ## Values -/

/-- The values of every vertex: a coordinate tuple `inl (some t)`, the invalid value `inl none`,
or the reserved value `inr w` designated for the selected inputs of `f_w`. -/
abbrev Val (n K : ℕ) : Type := Option (Roots n → ZMod K) ⊕ Fin n

/-- The default value is the invalid value (core Lean declares no `Inhabited` instance for sums). -/
instance (n K : ℕ) : Inhabited (Val n K) := ⟨Sum.inl none⟩

/-- The coordinates of a tuple; zero for the other values. -/
def coords {K : ℕ} : Val n K → Roots n → ZMod K
  | Sum.inl (some t) => t
  | Sum.inl none => 0
  | Sum.inr _ => 0

/-- `x` is a coordinate tuple. -/
def isTup {K : ℕ} : Val n K → Bool
  | Sum.inl (some _) => true
  | Sum.inl none => false
  | Sum.inr _ => false

/-- `x` is the value reserved for the selected inputs of `f_v`. -/
def isRes {K : ℕ} (v : Fin n) : Val n K → Bool
  | Sum.inl _ => false
  | Sum.inr w => decide (w = v)

theorem coords_tup {K : ℕ} (t : Roots n → ZMod K) (l : Roots n) :
    coords (Sum.inl (some t) : Val n K) l = t l := rfl

theorem isRes_inr {K : ℕ} (v : Fin n) : isRes v (Sum.inr v : Val n K) = true := by
  simp [isRes]

/-- The coin `b` as an element of `ZMod K`. -/
def coin (K : ℕ) (b : Bool) : ZMod K := if b = true then 1 else 0

theorem coin_true (K : ℕ) : coin K true = 1 := by simp [coin]

theorem coin_false (K : ℕ) : coin K false = 0 := by simp [coin]

/-! ## The mechanisms -/

/-- The record of the roots of `v`: coordinate `l` is the coin `l` when `l` is a root of `v`. -/
def own (G : ADMG n) (K : ℕ) (v : Fin n) (u : Roots n → Bool) (l : Roots n) : ZMod K :=
  if l ∈ rootScope G v then coin K (u l) else 0

theorem own_eq (G : ADMG n) (K : ℕ) (v : Fin n) (u : Roots n → Bool) (l : Roots n) :
    own G K v u l = coin K (u l) * ((if l ∈ rootScope G v then 1 else 0 : ℕ) : ZMod K) := by
  unfold own
  by_cases hl : l ∈ rootScope G v
  · rw [ite_eq_left hl, ite_eq_left hl, Nat.cast_one, mul_one]
  · rw [ite_eq_right hl, ite_eq_right hl, Nat.cast_zero, mul_zero]

/-- The record of the roots of `v` at the coins `u` is its record at `u0`, with coin `l` equal to
`false`, plus `[coin l]` times the indicator of `l` being a root of `v`. -/
theorem own_coord (G : ADMG n) (K : ℕ) (v : Fin n) (u u0 : Roots n → Bool) (l : Roots n)
    (hu0 : u0 l = false) :
    own G K v u l = own G K v u0 l +
      coin K (u l) * ((if l ∈ rootScope G v then 1 else 0 : ℕ) : ZMod K) := by
  rw [own_eq G K v u l, own_eq G K v u0 l, hu0, coin_false, zero_mul, zero_add]

/-- The unselected parents of `v`. -/
def par (G : ADMG n) (F : EdgeSet n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => G.dir p v = true ∧ (p, v) ∉ F)

theorem mem_par {G : ADMG n} {F : EdgeSet n} {v p : Fin n} :
    p ∈ par G F v ↔ G.dir p v = true ∧ (p, v) ∉ F := by
  unfold par
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The input checks of `f_v` on the parent values `z`: every selected input carries the
reserved value `inr v`, and every unselected input is a tuple. -/
def Chk (G : ADMG n) (F : EdgeSet n) (K : ℕ) (v : Fin n) (z : Fin n → Val n K) : Prop :=
  ∀ p, G.dir p v = true → ((p, v) ∈ F → isRes v (z p) = true) ∧
    ((p, v) ∉ F → isTup (z p) = true)

instance (G : ADMG n) (F : EdgeSet n) (K : ℕ) (v : Fin n) (z : Fin n → Val n K) :
    Decidable (Chk G F K v z) := by
  unfold Chk; infer_instance

/-- The output of `f_v`, `v ∈ T`, when its checks pass: the record of its roots plus the
coordinates of its unselected parents. -/
def comb (G : ADMG n) (F : EdgeSet n) (K : ℕ) (v : Fin n) (z : Fin n → Val n K)
    (u : Roots n → Bool) (l : Roots n) : ZMod K :=
  own G K v u l + ∑ p ∈ par G F v, coords (z p) l

/-- The mechanism of `v`. -/
def fw (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) (v : Fin n)
    (z : Fin n → Val n K) (u : Roots n → Bool) : Val n K :=
  if v ∈ T then (if Chk G F K v z then Sum.inl (some (comb G F K v z u)) else Sum.inl none)
  else Sum.inl (some (own G K v u))

theorem fw_not_mem {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ} {v : Fin n}
    (hv : v ∉ T) (z : Fin n → Val n K) (u : Roots n → Bool) :
    fw G F T K v z u = Sum.inl (some (own G K v u)) := by
  unfold fw
  rw [ite_eq_right hv]

theorem fw_chk {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ} {v : Fin n}
    (hv : v ∈ T) {z : Fin n → Val n K} (hc : Chk G F K v z) (u : Roots n → Bool) :
    fw G F T K v z u = Sum.inl (some (comb G F K v z u)) := by
  unfold fw
  rw [ite_eq_left hv, ite_eq_left hc]

theorem fw_not_chk {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ} {v : Fin n}
    (hv : v ∈ T) {z : Fin n → Val n K} (hc : ¬ Chk G F K v z) (u : Roots n → Bool) :
    fw G F T K v z u = Sum.inl none := by
  unfold fw
  rw [ite_eq_left hv, ite_eq_right hc]

/-- No mechanism outputs a reserved value. -/
theorem isRes_fw {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ} (v w : Fin n)
    (z : Fin n → Val n K) (u : Roots n → Bool) : isRes v (fw G F T K w z u) = false := by
  unfold fw
  split_ifs <;> rfl

theorem chk_congr {G : ADMG n} {F : EdgeSet n} {K : ℕ} {v : Fin n} {z z' : Fin n → Val n K}
    (h : ∀ p, G.dir p v = true → isRes v (z p) = isRes v (z' p) ∧ isTup (z p) = isTup (z' p)) :
    Chk G F K v z ↔ Chk G F K v z' := by
  unfold Chk
  refine forall_congr' (fun p => imp_congr_right (fun hp => ?_))
  rw [(h p hp).1, (h p hp).2]

/-- Whether `f_w` outputs a tuple depends on its inputs only through its checks. -/
theorem isTup_fw_congr {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ} {w : Fin n}
    {z z' : Fin n → Val n K} {u u' : Roots n → Bool} (hc : Chk G F K w z ↔ Chk G F K w z') :
    isTup (fw G F T K w z u) = isTup (fw G F T K w z' u') := by
  by_cases hwT : w ∈ T
  · by_cases h1 : Chk G F K w z
    · rw [fw_chk hwT h1, fw_chk hwT (hc.mp h1)]
      rfl
    · rw [fw_not_chk hwT h1, fw_not_chk hwT (fun h2 => h1 (hc.mpr h2))]
  · rw [fw_not_mem hwT, fw_not_mem hwT]
    rfl

theorem fw_pa (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) (i : Fin n)
    (x x' : Fin n → Val n K) (u : Roots n → Bool)
    (h : ∀ j, G.dir j i = true → x j = x' j) : fw G F T K i x u = fw G F T K i x' u := by
  have hc : Chk G F K i x ↔ Chk G F K i x' :=
    chk_congr (fun p hp => by rw [h p hp]; exact ⟨rfl, rfl⟩)
  have hs : comb G F K i x u = comb G F K i x' u := by
    funext l
    have hl : ∀ p ∈ par G F i, coords (x p) l = coords (x' p) l :=
      fun p hp => by rw [h p (mem_par.mp hp).1]
    unfold comb
    rw [Finset.sum_congr rfl hl]
  by_cases hT : i ∈ T
  · by_cases h1 : Chk G F K i x
    · rw [fw_chk hT h1, fw_chk hT (hc.mp h1), hs]
    · rw [fw_not_chk hT h1, fw_not_chk hT (fun h2 => h1 (hc.mpr h2))]
  · rw [fw_not_mem hT, fw_not_mem hT]

theorem fw_ex (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) (i : Fin n)
    (x : Fin n → Val n K) (u u' : Roots n → Bool)
    (h : ∀ l ∈ rootScope G i, u l = u' l) : fw G F T K i x u = fw G F T K i x u' := by
  have ho : own G K i u = own G K i u' := by
    funext l
    unfold own
    by_cases hl : l ∈ rootScope G i
    · rw [ite_eq_left hl, ite_eq_left hl, h l hl]
    · rw [ite_eq_right hl, ite_eq_right hl]
  have hc : comb G F K i x u = comb G F K i x u' := by
    funext l
    unfold comb
    rw [show own G K i u l = own G K i u' l from congrFun ho l]
  unfold fw
  rw [ho, hc]

/-- The mechanisms of the witness; its causal diagram is `G`. -/
def mech (G : ADMG n) (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) :
    Mech n (fun _ => Val n K) (Roots n) (fun _ => Bool) :=
  Mech.ofADMG G hG (fw G F T K) (fw_pa G F T K) (fw_ex G F T K)

/-- The witness SCM: every root is a fair coin. -/
noncomputable def wscm (G : ADMG n) (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) :
    SCM n (fun _ => Val n K) (Roots n) (fun _ => Bool) where
  toMech := mech G hG F T K
  p _ _ := 1 / 2
  p_nonneg _ _ := by norm_num
  p_sum _ := by norm_num [Fintype.sum_bool]

/-- The witness model. -/
noncomputable def wmodel (G : ADMG n) (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ)
    [NeZero K] : Model n where
  X := fun _ => Val n K
  L := Roots n
  U := fun _ => Bool
  scm := wscm G hG F T K

theorem wconf {G : ADMG n} (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ)
    [NeZero K] : ConfDiag G (wmodel G hG F T K) := by
  show (mech G hG F T K).diag = G
  exact Mech.ofADMG_diag G hG _ _ _


/-! ## Path counts -/

/-- One step of the path count `cnt`. -/
def cntF (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (E : EdgeSet n) (l : Roots n)
    (v : Fin n) (z : Fin n → ℕ) : ℕ :=
  (if l ∈ rootScope G v then 1 else 0) +
    if v ∈ T then ∑ p ∈ par G F v, (if (p, v) ∈ E then 0 else z p) else 0

/-- `cnt G F T E l v`: the number of directed paths of `𝒢_F` that start at a vertex reading root
`l`, continue inside `T`, use no edge of `E` and end at `v`.  Under a specification `F'`, coin `l`
moves coordinate `l` of a tuple at `v` by `cnt G F T F' l v` (`coord_respE`). -/
def cnt (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (E : EdgeSet n) (l : Roots n) :
    Fin n → ℕ :=
  sol (X := fun _ => ℕ) (cntF G F T E l)

theorem cnt_spec {G : ADMG n} (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (E : EdgeSet n)
    (l : Roots n) (v : Fin n) : cnt G F T E l v = cntF G F T E l v (cnt G F T E l) := by
  unfold cnt
  refine sol_spec (X := fun _ => ℕ) (topRank G) (fun i => ?_) v
  intro z z' h
  have hs : ∑ p ∈ par G F i, (if (p, i) ∈ E then 0 else z p) =
      ∑ p ∈ par G F i, (if (p, i) ∈ E then 0 else z' p) :=
    Finset.sum_congr rfl (fun p hp => by rw [h p (topRank_lt hG (mem_par.mp hp).1)])
  unfold cntF
  rw [hs]

theorem cnt_eq {G : ADMG n} (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (E : EdgeSet n)
    (l : Roots n) (v : Fin n) :
    cnt G F T E l v = (if l ∈ rootScope G v then 1 else 0) +
      if v ∈ T then ∑ p ∈ par G F v, (if (p, v) ∈ E then 0 else cnt G F T E l p) else 0 :=
  cnt_spec hG F T E l v

theorem cnt_eq0 {G : ADMG n} (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n)) (l : Roots n)
    (v : Fin n) :
    cnt G F T ∅ l v = (if l ∈ rootScope G v then 1 else 0) +
      if v ∈ T then ∑ p ∈ par G F v, cnt G F T ∅ l p else 0 := by
  rw [cnt_eq hG F T ∅ l v]
  have hs : ∑ p ∈ par G F v, (if (p, v) ∈ (∅ : EdgeSet n) then 0 else cnt G F T ∅ l p) =
      ∑ p ∈ par G F v, cnt G F T ∅ l p :=
    Finset.sum_congr rfl (fun p _ => ite_eq_right (Finset.notMem_empty _))
  rw [hs]

theorem one_le_cnt {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {v : Fin n} (hl : l ∈ rootScope G v) :
    1 ≤ cnt G F T E l v := by
  rw [cnt_eq hG F T E l v, ite_eq_left hl]
  omega

/-- Removing edges removes paths. -/
theorem cnt_le_cnt0 {G : ADMG n} (hG : G.WF) (F : EdgeSet n) (T : Finset (Fin n))
    (E : EdgeSet n) (l : Roots n) (v : Fin n) : cnt G F T E l v ≤ cnt G F T ∅ l v := by
  refine rank_induction (topRank G) (P := fun v => cnt G F T E l v ≤ cnt G F T ∅ l v)
    (fun v ih => ?_) v
  have ih' : ∀ j, topRank G j < topRank G v → cnt G F T E l j ≤ cnt G F T ∅ l j := ih
  show cnt G F T E l v ≤ cnt G F T ∅ l v
  rw [cnt_eq hG F T E l v, cnt_eq0 hG F T l v]
  have hs : (if v ∈ T then ∑ p ∈ par G F v, (if (p, v) ∈ E then 0 else cnt G F T E l p)
      else 0) ≤ (if v ∈ T then ∑ p ∈ par G F v, cnt G F T ∅ l p else 0) := by
    by_cases hvT : v ∈ T
    · rw [ite_eq_left hvT, ite_eq_left hvT]
      refine Finset.sum_le_sum (fun p hp => ?_)
      by_cases hpE : (p, v) ∈ E
      · rw [ite_eq_left hpE]
        exact Nat.zero_le _
      · rw [ite_eq_right hpE]
        exact ih' p (topRank_lt hG (mem_par.mp hp).1)
    · simp [hvT]
  omega

/-- The count grows along an edge of `𝒢_F` into `T` that is not in `E`. -/
theorem cnt_le_child {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {p w : Fin n} (hwT : w ∈ T) (hp : p ∈ par G F w)
    (hpE : (p, w) ∉ E) : cnt G F T E l p ≤ cnt G F T E l w := by
  have h1 : (if (p, w) ∈ E then 0 else cnt G F T E l p) ≤
      ∑ q ∈ par G F w, (if (q, w) ∈ E then 0 else cnt G F T E l q) :=
    Finset.single_le_sum (f := fun q => if (q, w) ∈ E then 0 else cnt G F T E l q)
      (fun q _ => Nat.zero_le _) hp
  rw [ite_eq_right hpE] at h1
  rw [cnt_eq hG F T E l w, ite_eq_left hwT]
  omega

/-- The count grows along a directed path of `𝒢_F` into `T` with no edge in `E`. -/
theorem cnt_le_reach {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {R : Fin n → Fin n → Bool}
    (hR : ∀ b c, R b c = true → G.dir b c = true ∧ (b, c) ∉ F ∧ (b, c) ∉ E)
    (hTpar : ∀ p v, v ∈ T → G.dir p v = true → (p, v) ∉ F → p ∈ T)
    {D : Finset (Fin n)} {a w : Fin n} (h : Reach R D a w) (hw : w ∈ T) :
    cnt G F T E l a ≤ cnt G F T E l w := by
  revert hw
  induction h with
  | refl => exact fun _ => le_rfl
  | @tail b c _ hbc ih =>
    intro hcT
    obtain ⟨h1, h2, h3⟩ := hR b c hbc.1
    exact le_trans (ih (hTpar b c hcT h1 h2)) (cnt_le_child hG hcT (mem_par.mpr ⟨h1, h2⟩) h3)

/-- A strict decrease of one summand of `cnt` at `w ∈ T` decreases the count at `w`. -/
theorem cnt_lt_of_term {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {p w : Fin n} (hwT : w ∈ T) (hp : p ∈ par G F w)
    (hlt : (if (p, w) ∈ E then 0 else cnt G F T E l p) < cnt G F T ∅ l p) :
    cnt G F T E l w < cnt G F T ∅ l w := by
  have hle : ∀ q ∈ par G F w, (if (q, w) ∈ E then 0 else cnt G F T E l q) ≤
      cnt G F T ∅ l q := by
    intro q _
    by_cases hqE : (q, w) ∈ E
    · rw [ite_eq_left hqE]
      exact Nat.zero_le _
    · rw [ite_eq_right hqE]
      exact cnt_le_cnt0 hG F T E l q
  have hs : ∑ q ∈ par G F w, (if (q, w) ∈ E then 0 else cnt G F T E l q) <
      ∑ q ∈ par G F w, cnt G F T ∅ l q :=
    Finset.sum_lt_sum hle ⟨p, hp, hlt⟩
  rw [cnt_eq hG F T E l w, cnt_eq0 hG F T l w, ite_eq_left hwT, ite_eq_left hwT]
  omega

theorem cnt_lt_child {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {p w : Fin n} (hwT : w ∈ T) (hp : p ∈ par G F w)
    (hlt : cnt G F T E l p < cnt G F T ∅ l p) : cnt G F T E l w < cnt G F T ∅ l w := by
  refine cnt_lt_of_term hG hwT hp ?_
  by_cases hpE : (p, w) ∈ E
  · rw [ite_eq_left hpE]
    omega
  · rw [ite_eq_right hpE]
    exact hlt

/-- Cutting an edge `p → w` with `0 < cnt_F(l, p)` decreases the count at `w`. -/
theorem cnt_lt_cut {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {p w : Fin n} (hwT : w ∈ T) (hp : p ∈ par G F w)
    (hpE : (p, w) ∈ E) (hpos : 0 < cnt G F T ∅ l p) : cnt G F T E l w < cnt G F T ∅ l w := by
  refine cnt_lt_of_term hG hwT hp ?_
  rw [ite_eq_left hpE]
  exact hpos

/-- A strict decrease passes along a directed path of `𝒢_F` into `T`. -/
theorem cnt_lt_reach {G : ADMG n} (hG : G.WF) {F : EdgeSet n} {T : Finset (Fin n)}
    {E : EdgeSet n} {l : Roots n} {R : Fin n → Fin n → Bool}
    (hR : ∀ b c, R b c = true → G.dir b c = true ∧ (b, c) ∉ F)
    (hTpar : ∀ p v, v ∈ T → G.dir p v = true → (p, v) ∉ F → p ∈ T)
    {D : Finset (Fin n)} {a w : Fin n} (h : Reach R D a w) (hw : w ∈ T)
    (hlt : cnt G F T E l a < cnt G F T ∅ l a) : cnt G F T E l w < cnt G F T ∅ l w := by
  revert hw
  induction h with
  | refl => exact fun _ => hlt
  | @tail b c _ hbc ih =>
    intro hcT
    obtain ⟨h1, h2⟩ := hR b c hbc.1
    exact cnt_lt_child hG hcT (mem_par.mpr ⟨h1, h2⟩) (ih (hTpar b c hcT h1 h2))

/-! ## Responses -/

/-- The value received by `f_w` at its argument `j` under the specification `F'` with values `c'`,
when the vertices take the values `x`. -/
def inp {K : ℕ} (F' : EdgeSet n) (c' : Fin n → Fin n → Val n K) (x : Fin n → Val n K)
    (w j : Fin n) : Val n K :=
  if (j, w) ∈ F' then c' w j else x j

theorem inp_of_mem {K : ℕ} {F' : EdgeSet n} {c' : Fin n → Fin n → Val n K}
    {x : Fin n → Val n K} {w j : Fin n} (h : (j, w) ∈ F') : inp F' c' x w j = c' w j :=
  ite_eq_left h

theorem inp_of_not_mem {K : ℕ} {F' : EdgeSet n} {c' : Fin n → Fin n → Val n K}
    {x : Fin n → Val n K} {w j : Fin n} (h : (j, w) ∉ F') : inp F' c' x w j = x j :=
  ite_eq_right h

/-- The designated values: every selected input of `f_w` receives the reserved value `inr w`. -/
def cstar (n K : ℕ) : Fin n → Fin n → Val n K := fun w _ => Sum.inr w

section Response

variable {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ}

theorem respE_eq (hG : G.WF) (F' : EdgeSet n) (c' : Fin n → Fin n → Val n K)
    (u : Roots n → Bool) (w : Fin n) :
    (mech G hG F T K).respE F' c' u w =
      fw G F T K w (inp F' c' ((mech G hG F T K).respE F' c' u) w) u :=
  (mech G hG F T K).respE_spec F' c' u w

theorem isRes_respE (hG : G.WF) (F' : EdgeSet n) (c' : Fin n → Fin n → Val n K)
    (u : Roots n → Bool) (w v : Fin n) :
    isRes v ((mech G hG F T K).respE F' c' u w) = false := by
  rw [respE_eq hG F' c' u w]
  exact isRes_fw v w _ u

/-- Which vertices output tuples does not depend on the coins. -/
theorem isTup_respE (hG : G.WF) (F' : EdgeSet n) (c' : Fin n → Fin n → Val n K)
    (u u' : Roots n → Bool) (w : Fin n) :
    isTup ((mech G hG F T K).respE F' c' u w) = isTup ((mech G hG F T K).respE F' c' u' w) := by
  refine rank_induction (topRank G) (P := fun w => isTup ((mech G hG F T K).respE F' c' u w) =
    isTup ((mech G hG F T K).respE F' c' u' w)) (fun w ih => ?_) w
  have ih' : ∀ j, topRank G j < topRank G w → isTup ((mech G hG F T K).respE F' c' u j) =
      isTup ((mech G hG F T K).respE F' c' u' j) := ih
  show isTup ((mech G hG F T K).respE F' c' u w) = isTup ((mech G hG F T K).respE F' c' u' w)
  rw [respE_eq hG F' c' u w, respE_eq hG F' c' u' w]
  have hc : Chk G F K w (inp F' c' ((mech G hG F T K).respE F' c' u) w) ↔
      Chk G F K w (inp F' c' ((mech G hG F T K).respE F' c' u') w) := by
    refine chk_congr (fun p hp => ?_)
    by_cases hpF' : (p, w) ∈ F'
    · rw [inp_of_mem hpF', inp_of_mem hpF']
      exact ⟨rfl, rfl⟩
    · rw [inp_of_not_mem hpF', inp_of_not_mem hpF', isRes_respE hG F' c' u p w,
        isRes_respE hG F' c' u' p w]
      exact ⟨rfl, ih' p (topRank_lt hG hp)⟩
  exact isTup_fw_congr hc

/-- At a tuple, coordinate `l` is its value with every coin `false`, plus `[coin l]` times the
path count `cnt_{F'}(l)`. -/
theorem coord_respE (hG : G.WF) (F' : EdgeSet n) (c' : Fin n → Fin n → Val n K)
    (u : Roots n → Bool) (l : Roots n) (w : Fin n)
    (hw : isTup ((mech G hG F T K).respE F' c' u w) = true) :
    coords ((mech G hG F T K).respE F' c' u w) l =
      coords ((mech G hG F T K).respE F' c' (fun _ => false) w) l +
        coin K (u l) * ((cnt G F T F' l w : ℕ) : ZMod K) := by
  revert hw
  refine rank_induction (topRank G) (P := fun w =>
    isTup ((mech G hG F T K).respE F' c' u w) = true →
      coords ((mech G hG F T K).respE F' c' u w) l =
        coords ((mech G hG F T K).respE F' c' (fun _ => false) w) l +
          coin K (u l) * ((cnt G F T F' l w : ℕ) : ZMod K)) (fun w ih => ?_) w
  have ih' : ∀ j, topRank G j < topRank G w →
      isTup ((mech G hG F T K).respE F' c' u j) = true →
      coords ((mech G hG F T K).respE F' c' u j) l =
        coords ((mech G hG F T K).respE F' c' (fun _ => false) j) l +
          coin K (u l) * ((cnt G F T F' l j : ℕ) : ZMod K) := ih
  intro hw
  have hw0 : isTup ((mech G hG F T K).respE F' c' (fun _ => false) w) = true := by
    rw [isTup_respE hG F' c' (fun _ => false) u w]
    exact hw
  rw [respE_eq hG F' c' u w] at hw ⊢
  rw [respE_eq hG F' c' (fun _ => false) w] at hw0 ⊢
  by_cases hwT : w ∈ T
  · have hc : Chk G F K w (inp F' c' ((mech G hG F T K).respE F' c' u) w) := by
      by_contra hc
      rw [fw_not_chk hwT hc] at hw
      exact Bool.false_ne_true hw
    have hc0 : Chk G F K w (inp F' c' ((mech G hG F T K).respE F' c' (fun _ => false)) w) := by
      by_contra hc0
      rw [fw_not_chk hwT hc0] at hw0
      exact Bool.false_ne_true hw0
    have hs : ∑ p ∈ par G F w, coords (inp F' c' ((mech G hG F T K).respE F' c' u) w p) l =
        ∑ p ∈ par G F w,
          (coords (inp F' c' ((mech G hG F T K).respE F' c' (fun _ => false)) w p) l +
            coin K (u l) * ((if (p, w) ∈ F' then 0 else cnt G F T F' l p : ℕ) : ZMod K)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨hp1, hp2⟩ := mem_par.mp hp
      by_cases hpF' : (p, w) ∈ F'
      · rw [inp_of_mem hpF', inp_of_mem hpF', ite_eq_left hpF', Nat.cast_zero, mul_zero,
          add_zero]
      · have ht : isTup ((mech G hG F T K).respE F' c' u p) = true := by
          have h := (hc p hp1).2 hp2
          rwa [inp_of_not_mem hpF'] at h
        rw [inp_of_not_mem hpF', inp_of_not_mem hpF', ite_eq_right hpF']
        exact ih' p (topRank_lt hG hp1) ht
    rw [fw_chk hwT hc, fw_chk hwT hc0, coords_tup, coords_tup, comb, comb,
      own_coord G K w u (fun _ => false) l rfl, hs, Finset.sum_add_distrib, ← Finset.mul_sum,
      cnt_eq hG F T F' l w, ite_eq_left hwT, Nat.cast_add, Nat.cast_sum]
    ring
  · rw [fw_not_mem hwT, fw_not_mem hwT, coords_tup, coords_tup,
      own_coord G K w u (fun _ => false) l rfl, cnt_eq hG F T F' l w, ite_eq_right hwT, add_zero]

/-- Under the designated values every check passes, and coordinate `l` of every vertex `w` is
`[coin l] · cnt_F(l, w)`. -/
theorem respE_cstar (hG : G.WF) (u : Roots n → Bool) (w : Fin n) :
    (mech G hG F T K).respE F (cstar n K) u w =
      Sum.inl (some (fun l => coin K (u l) * ((cnt G F T ∅ l w : ℕ) : ZMod K))) := by
  refine rank_induction (topRank G) (P := fun w => (mech G hG F T K).respE F (cstar n K) u w =
      Sum.inl (some (fun l => coin K (u l) * ((cnt G F T ∅ l w : ℕ) : ZMod K))))
    (fun w ih => ?_) w
  have ih' : ∀ j, topRank G j < topRank G w → (mech G hG F T K).respE F (cstar n K) u j =
      Sum.inl (some (fun l => coin K (u l) * ((cnt G F T ∅ l j : ℕ) : ZMod K))) := ih
  show (mech G hG F T K).respE F (cstar n K) u w =
      Sum.inl (some (fun l => coin K (u l) * ((cnt G F T ∅ l w : ℕ) : ZMod K)))
  rw [respE_eq hG F (cstar n K) u w]
  by_cases hwT : w ∈ T
  · have hc : Chk G F K w (inp F (cstar n K) ((mech G hG F T K).respE F (cstar n K) u) w) := by
      intro p hp
      refine ⟨fun hpF => ?_, fun hpF => ?_⟩
      · rw [inp_of_mem hpF]
        exact isRes_inr w
      · rw [inp_of_not_mem hpF, ih' p (topRank_lt hG hp)]
        rfl
    have hcomb : comb G F K w (inp F (cstar n K) ((mech G hG F T K).respE F (cstar n K) u) w) u =
        fun l => coin K (u l) * ((cnt G F T ∅ l w : ℕ) : ZMod K) := by
      funext l
      have hs : ∑ p ∈ par G F w,
          coords (inp F (cstar n K) ((mech G hG F T K).respE F (cstar n K) u) w p) l =
          ∑ p ∈ par G F w, coin K (u l) * ((cnt G F T ∅ l p : ℕ) : ZMod K) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        obtain ⟨hp1, hp2⟩ := mem_par.mp hp
        rw [inp_of_not_mem hp2, ih' p (topRank_lt hG hp1), coords_tup]
      rw [comb, own_eq, hs, ← Finset.mul_sum, cnt_eq0 hG F T l w, ite_eq_left hwT, Nat.cast_add,
        Nat.cast_sum]
      ring
    rw [fw_chk hwT hc, hcomb]
  · have hown : own G K w u = fun l => coin K (u l) * ((cnt G F T ∅ l w : ℕ) : ZMod K) := by
      funext l
      rw [own_eq, cnt_eq0 hG F T l w, ite_eq_right hwT, add_zero]
    rw [fw_not_mem hwT, hown]

/-- A selected input `(p₀, v₀) ∈ F` with `v₀ ∈ T` that `F'` leaves unselected makes `f_{v₀}`
output `inl none`. -/
theorem respE_none_start (hG : G.WF) {F' : EdgeSet n} {c' : Fin n → Fin n → Val n K}
    {u : Roots n → Bool} {p₀ v₀ : Fin n} (hv₀T : v₀ ∈ T) (hp₀F : (p₀, v₀) ∈ F)
    (hp₀d : G.dir p₀ v₀ = true) (hp₀F' : (p₀, v₀) ∉ F') :
    (mech G hG F T K).respE F' c' u v₀ = Sum.inl none := by
  rw [respE_eq hG F' c' u v₀]
  refine fw_not_chk hv₀T (fun hc => ?_) u
  have h := (hc p₀ hp₀d).1 hp₀F
  rw [inp_of_not_mem hp₀F', isRes_respE hG F' c' u p₀ v₀] at h
  exact Bool.false_ne_true h

/-- `inl none` propagates along the edges of `𝒢_F` into `T` that `F'` leaves unselected. -/
theorem respE_none_reach (hG : G.WF) {F' : EdgeSet n} {c' : Fin n → Fin n → Val n K}
    {u : Roots n → Bool} {R : Fin n → Fin n → Bool}
    (hR : ∀ b c, R b c = true → G.dir b c = true ∧ (b, c) ∉ F ∧ (b, c) ∉ F')
    (hTpar : ∀ p v, v ∈ T → G.dir p v = true → (p, v) ∉ F → p ∈ T)
    {D : Finset (Fin n)} {a w : Fin n} (h : Reach R D a w) (hw : w ∈ T)
    (ha : (mech G hG F T K).respE F' c' u a = Sum.inl none) :
    (mech G hG F T K).respE F' c' u w = Sum.inl none := by
  revert hw
  induction h with
  | refl => exact fun _ => ha
  | @tail b c _ hbc ih =>
    intro hcT
    obtain ⟨h1, h2, h3⟩ := hR b c hbc.1
    have hb : (mech G hG F T K).respE F' c' u b = Sum.inl none := ih (hTpar b c hcT h1 h2)
    rw [respE_eq hG F' c' u c]
    refine fw_not_chk hcT (fun hc => ?_) u
    have hcb := (hc b h1).2 h2
    rw [inp_of_not_mem h3, hb] at hcb
    exact Bool.false_ne_true hcb

end Response

/-! ## The reward -/

/-- The value of `y` is a tuple whose coordinate `l` is `0` or `cnt_F(l, y)`. -/
def Good (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) (y : Fin n) (x : Val n K) :
    Prop :=
  isTup x = true ∧ ∀ l, coords x l = 0 ∨ coords x l = ((cnt G F T ∅ l y : ℕ) : ZMod K)

open Classical in
/-- The witness reward: one on the values of `Good`, zero elsewhere. -/
noncomputable def reward (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) (K : ℕ) (y : Fin n)
    (x : Val n K) : ℝ :=
  if Good G F T K y x then 1 else 0

/-- Two values that differ by `d` at one coordinate cannot both lie in `{0, m}` modulo `K` when
`0 < d`, `d ≠ m` and `d + m < K` (`LB18.zmod_aux` with `B = 0`). -/
theorem zmod0 {K d m : ℕ} (hd : 0 < d) (hdm : d ≠ m) (hK : d + m < K) {C : ZMod K}
    (h1 : C = 0 ∨ C = (m : ZMod K)) (h2 : C + d = 0 ∨ C + d = (m : ZMod K)) : False :=
  LB18.zmod_aux (B := 0) (C := C) hd hdm hK (by rwa [zero_add]) (by rwa [zero_add])

section Means

variable {G : ADMG n} {F : EdgeSet n} {T : Finset (Fin n)} {K : ℕ}

theorem reward_one {y : Fin n} {x : Val n K} (h : Good G F T K y x) : reward G F T K y x = 1 := by
  unfold reward
  exact ite_eq_left h

theorem reward_none {y : Fin n} : reward G F T K y (Sum.inl none : Val n K) = 0 := by
  unfold reward
  refine ite_eq_right (fun h => ?_)
  obtain ⟨h1, -⟩ := h
  exact Bool.false_ne_true h1

theorem reward_pair {y : Fin n} {x x' : Val n K} (h : ¬ (Good G F T K y x ∧ Good G F T K y x')) :
    reward G F T K y x + reward G F T K y x' ≤ 1 := by
  have hle : ∀ v, reward G F T K y v ≤ 1 := fun v => by
    unfold reward
    split_ifs <;> norm_num
  have hz : ∀ v, ¬ Good G F T K y v → reward G F T K y v = 0 := fun v hv => by
    unfold reward
    exact ite_eq_right hv
  by_cases ha : Good G F T K y x
  · have hb : ¬ Good G F T K y x' := fun hb => h ⟨ha, hb⟩
    rw [hz x' hb]
    linarith [hle x]
  · rw [hz x ha]
    linarith [hle x']

theorem good_cstar {y : Fin n} (u : Roots n → Bool) :
    Good G F T K y (Sum.inl (some (fun l => coin K (u l) * ((cnt G F T ∅ l y : ℕ) : ZMod K)))) := by
  refine ⟨rfl, fun l => ?_⟩
  show coin K (u l) * ((cnt G F T ∅ l y : ℕ) : ZMod K) = 0 ∨
    coin K (u l) * ((cnt G F T ∅ l y : ℕ) : ZMod K) = ((cnt G F T ∅ l y : ℕ) : ZMod K)
  cases u l with
  | true =>
    right
    rw [coin_true, one_mul]
  | false =>
    left
    rw [coin_false, zero_mul]

/-- The designated assignment has mean one. -/
theorem muE_cstar (hG : G.WF) [NeZero K] (y : Fin n) :
    (wmodel G hG F T K).muE y (reward G F T K y) F (cstar n K) = 1 := by
  show (wscm G hG F T K).E
    (fun u => reward G F T K y ((mech G hG F T K).respE F (cstar n K) u y)) = 1
  exact LB18.E_eq_one (wscm G hG F T K) (fun u =>
    (congrArg (reward G F T K y) (respE_cstar hG u y)).trans (reward_one (good_cstar u)))

/-- If coin `l` moves coordinate `l` of `y` by `cnt_{F'}(l, y)`, with
`0 < cnt_{F'}(l, y) < cnt_F(l, y)`, then at most one of two units that differ only in coin `l` is
rewarded. -/
theorem pair_le (hG : G.WF) {y : Fin n} {F' : EdgeSet n} {c' : Fin n → Fin n → Val n K}
    {l : Roots n} (hd : 0 < cnt G F T F' l y) (hlt : cnt G F T F' l y < cnt G F T ∅ l y)
    (hK : cnt G F T F' l y + cnt G F T ∅ l y < K) (u : Roots n → Bool) :
    reward G F T K y ((mech G hG F T K).respE F' c' u y) +
      reward G F T K y ((mech G hG F T K).respE F' c' (Function.update u l (!u l)) y) ≤ 1 := by
  apply reward_pair
  rintro ⟨⟨ht, hg⟩, ⟨-, hg'⟩⟩
  have ht' : isTup ((mech G hG F T K).respE F' c' (Function.update u l (!u l)) y) = true := by
    rw [isTup_respE hG F' c' (Function.update u l (!u l)) u y]
    exact ht
  have e1 := coord_respE hG F' c' u l y ht
  have e2 := coord_respE hG F' c' (Function.update u l (!u l)) l y ht'
  rw [Function.update_self] at e2
  have h1 := hg l
  have h2 := hg' l
  rw [e1] at h1
  rw [e2] at h2
  have hdm : cnt G F T F' l y ≠ cnt G F T ∅ l y := Nat.ne_of_lt hlt
  cases hu : u l with
  | true =>
    rw [hu, coin_true, one_mul] at h1
    rw [hu, Bool.not_true, coin_false, zero_mul, add_zero] at h2
    exact zmod0 hd hdm hK h2 h1
  | false =>
    rw [hu, coin_false, zero_mul, add_zero] at h1
    rw [hu, Bool.not_false, coin_true, one_mul] at h2
    exact zmod0 hd hdm hK h1 h2

/-- A specification with a root `l` such that `0 < cnt_{F'}(l, y) < cnt_F(l, y)` has mean at most
`1/2` under every assignment. -/
theorem muE_le_half (hG : G.WF) [NeZero K] {y : Fin n} {F' : EdgeSet n} {l : Roots n}
    (hd : 0 < cnt G F T F' l y) (hlt : cnt G F T F' l y < cnt G F T ∅ l y)
    (hK : cnt G F T F' l y + cnt G F T ∅ l y < K) (c' : Fin n → Fin n → Val n K) :
    (wmodel G hG F T K).muE y (reward G F T K y) F' c' ≤ 1 / 2 := by
  show (wscm G hG F T K).E
    (fun u => reward G F T K y ((mech G hG F T K).respE F' c' u y)) ≤ 1 / 2
  exact LB18.E_le_half (wscm G hG F T K) (fun _ _ => rfl) l (fun u => pair_le hG hd hlt hK u)

theorem pair_none (hG : G.WF) {y : Fin n} {F' : EdgeSet n} {c' : Fin n → Fin n → Val n K}
    (hnone : ∀ u, (mech G hG F T K).respE F' c' u y = Sum.inl none) (l₀ : Roots n)
    (u : Roots n → Bool) :
    reward G F T K y ((mech G hG F T K).respE F' c' u y) +
      reward G F T K y ((mech G hG F T K).respE F' c' (Function.update u l₀ (!u l₀)) y) ≤ 1 := by
  rw [hnone u, hnone (Function.update u l₀ (!u l₀)), reward_none]
  norm_num

/-- An assignment under which `y` is always invalid has mean `0`. -/
theorem muE_le_half_none (hG : G.WF) [NeZero K] {y : Fin n} {F' : EdgeSet n}
    {c' : Fin n → Fin n → Val n K}
    (hnone : ∀ u, (mech G hG F T K).respE F' c' u y = Sum.inl none) :
    (wmodel G hG F T K).muE y (reward G F T K y) F' c' ≤ 1 / 2 := by
  show (wscm G hG F T K).E
    (fun u => reward G F T K y ((mech G hG F T K).respE F' c' u y)) ≤ 1 / 2
  exact LB18.E_le_half (wscm G hG F T K) (fun _ _ => rfl) (Sum.inl y)
    (fun u => pair_none hG hnone (Sum.inl y) u)

end Means

/-! ## Graph facts -/

theorem mem_T {G' : ADMG n} {y v : Fin n} : v ∈ diagH G' y ∅ ↔ Reach G'.dir ∅ v y := by
  unfold diagH
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2.2, fun h => ⟨Finset.mem_univ v, Finset.notMem_empty v, h⟩⟩

/-- A directed path of `G'` from `a` to a vertex `w` that reaches `y` uses no edge of `E` when no
edge of `E` lies on a directed path from `a` to `y`. -/
theorem reach_cut_of {G' : ADMG n} {E : EdgeSet n} {y a : Fin n}
    (hE : ∀ b c, Reach G'.dir ∅ a b → G'.dir b c = true → Reach G'.dir ∅ c y → (b, c) ∉ E)
    {w : Fin n} (h : Reach G'.dir ∅ a w) (hwy : Reach G'.dir ∅ w y) :
    Reach (G'.cutE E).dir ∅ a w := by
  revert hwy
  induction h with
  | refl => exact fun _ => Reach.refl _
  | @tail b c hab hbc ih =>
    intro hcy
    exact Reach.tail (ih (Reach.head hbc.1 hbc.2 hcy))
      (ADMG.cutE_dir.mpr ⟨hbc.1, hE b c hab hbc.1 hcy⟩) hbc.2

theorem cutcut_dir {G : ADMG n} {F F' : EdgeSet n} (b c : Fin n)
    (h : ((G.cutE F).cutE F').dir b c = true) :
    G.dir b c = true ∧ (b, c) ∉ F ∧ (b, c) ∉ F' := by
  obtain ⟨h1, h2⟩ := ADMG.cutE_dir.mp h
  obtain ⟨h3, h4⟩ := ADMG.cutE_dir.mp h1
  exact ⟨h3, h4, h2⟩

/-- A specification `F'` that selects no edge of `𝓗_F` and every selected input of `F` into `T`
has the pruned specification of `F`. -/
theorem relevant_eq_of_noEdge {G : ADMG n} {y : Fin n} {F F' : EdgeSet n} {T : Finset (Fin n)}
    (hTdef : T = diagH (G.cutE F) y ∅)
    (h1 : ∀ a b, (a, b) ∈ F' → G.dir a b = true → (a, b) ∉ F → a ∈ T → b ∈ T → False)
    (h2 : ∀ p v, (p, v) ∈ F → G.dir p v = true → v ∈ T → (p, v) ∈ F') :
    relevant G y F' = relevant G y F := by
  have hreachT : ∀ v, v ∈ T ↔ Reach (G.cutE F).dir ∅ v y := fun v => by
    rw [hTdef]
    exact mem_T
  have hTpar : ∀ p v, v ∈ T → G.dir p v = true → (p, v) ∉ F → p ∈ T := fun p v hv hpv hpF =>
    (hreachT p).mpr (Reach.head (ADMG.cutE_dir.mpr ⟨hpv, hpF⟩) (Finset.notMem_empty v)
      ((hreachT v).mp hv))
  have hH : diagH (G.cutE F') y ∅ = T := by
    ext v
    rw [mem_T]
    constructor
    · intro h
      unfold Reach at h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact (hreachT y).mpr (Reach.refl y)
      | @head a c hac _ ih =>
        obtain ⟨had, haF'⟩ := ADMG.cutE_dir.mp hac.1
        exact hTpar a c ih had (fun haF => haF' (h2 a c haF had ih))
    · intro h
      have key : ∀ x, Reach (G.cutE F).dir ∅ x y → Reach (G.cutE F').dir ∅ x y := by
        intro x hx
        unfold Reach at hx
        induction hx using Relation.ReflTransGen.head_induction_on with
        | refl => exact Reach.refl y
        | @head a c hac hcy ih =>
          obtain ⟨had, haF⟩ := ADMG.cutE_dir.mp hac.1
          refine Reach.head (ADMG.cutE_dir.mpr ⟨had, fun haF' => ?_⟩) (Finset.notMem_empty c) ih
          exact h1 a c haF' had haF
            ((hreachT a).mpr (Reach.head hac.1 (Finset.notMem_empty c) hcy)) ((hreachT c).mpr hcy)
      exact key v ((hreachT v).mp h)
  ext ⟨p, v⟩
  unfold relevant
  rw [Finset.mem_filter, Finset.mem_filter, hH, ← hTdef]
  constructor
  · rintro ⟨hpF', hpv, hvT⟩
    refine ⟨?_, hpv, hvT⟩
    by_contra hpF
    exact h1 p v hpF' hpv hpF (hTpar p v hvT hpv hpF) hvT
  · rintro ⟨hpF, hpv, hvT⟩
    exact ⟨h2 p v hpF hpv hvT, hpv, hvT⟩

/-- The live/non-live split (`ScbMec.LB18.exists_split` with selected edges in place of intervened
vertices).  Let `F'` select an edge `a₀ → b₀` of `𝓗_F`, and call `v ∈ T` live if no directed path of
`𝒢_F` from `v` to `y` uses an edge of `F'`.  The live vertices contain `y` and are closed under
directed edges inside `T`; `a₀` is not live, so by minimality of `T` some `a ↔ b` inside `T` joins
a live `a` to a vertex `b` that is not live. -/
theorem exists_split {G : ADMG n} (hG : G.WF) {y : Fin n} {F F' : EdgeSet n}
    {T : Finset (Fin n)} (hTdef : T = diagH (G.cutE F) y ∅) (hT : DiagMUCT (G.cutE F) y ∅ T)
    {a₀ b₀ : Fin n} (h₀ : (a₀, b₀) ∈ F') (hd₀ : G.dir a₀ b₀ = true) (hF₀ : (a₀, b₀) ∉ F)
    (ha₀ : a₀ ∈ T) (hb₀ : b₀ ∈ T) :
    ∃ a ∈ T, ∃ b ∈ T, G.bi a b = true ∧
      (∀ s s', (s, s') ∈ F' → (G.cutE F).dir s s' = true →
        ¬ (Reach (G.cutE F).dir ∅ a s ∧ Reach (G.cutE F).dir ∅ s' y)) ∧
      ∃ s s', (s, s') ∈ F' ∧ (G.cutE F).dir s s' = true ∧
        Reach (G.cutE F).dir ∅ b s ∧ Reach (G.cutE F).dir ∅ s' y := by
  classical
  have hreachT : ∀ v, v ∈ T ↔ Reach (G.cutE F).dir ∅ v y := fun v => by
    rw [hTdef]
    exact mem_T
  by_contra hcon
  obtain ⟨Lv, hmem⟩ : ∃ Lv : Finset (Fin n), ∀ v, v ∈ Lv ↔ v ∈ T ∧
      ∀ s s', (s, s') ∈ F' → (G.cutE F).dir s s' = true →
        ¬ (Reach (G.cutE F).dir ∅ v s ∧ Reach (G.cutE F).dir ∅ s' y) :=
    ⟨T.filter (fun v => ∀ s s', (s, s') ∈ F' → (G.cutE F).dir s s' = true →
        ¬ (Reach (G.cutE F).dir ∅ v s ∧ Reach (G.cutE F).dir ∅ s' y)),
      fun v => Finset.mem_filter⟩
  have hsub : Lv ⊆ T := fun v hv => ((hmem v).mp hv).1
  have hUCT : DiagUCT (G.cutE F) y ∅ Lv := by
    refine ⟨fun v hv => ?_, (hmem y).mpr ⟨(hreachT y).mpr (Reach.refl y),
      fun s s' _ hss' hs => ?_⟩, fun t ht w hw htw => ?_, fun t ht w hw htw => ?_⟩
    · rw [← hTdef]
      exact hsub hv
    · exact hG.acyclic (ADMG.cutE_dir.mp hss').1
        (Reach.mono_rel (fun x z _ hxz => (ADMG.cutE_dir.mp hxz).1) (Reach.trans hs.2 hs.1))
    · have hwT : w ∈ T := by
        rw [hTdef]
        exact hw
      exact (hmem w).mpr ⟨hwT, fun s s' hF' hss' hs => ((hmem t).mp ht).2 s s' hF' hss'
        ⟨Reach.head htw (Finset.notMem_empty w) hs.1, hs.2⟩⟩
    · have hwT : w ∈ T := by
        rw [hTdef]
        exact hw
      exact (hmem w).mpr ⟨hwT, fun s s' hF' hss' hs =>
        hcon ⟨t, hsub ht, w, hwT, htw, ((hmem t).mp ht).2, s, s', hF', hss', hs⟩⟩
  have hne : Lv ≠ T := by
    intro h
    have ha₀L : a₀ ∈ Lv := by
      rw [h]
      exact ha₀
    exact ((hmem a₀).mp ha₀L).2 a₀ b₀ h₀ (ADMG.cutE_dir.mpr ⟨hd₀, hF₀⟩)
      ⟨Reach.refl a₀, (hreachT b₀).mp hb₀⟩
  exact hT.2 Lv (Finset.mem_powerset.mpr hsub) hne hUCT

/-- If `F'` selects an edge of `𝓗_F`, some root `l` has `0 < cnt_{F'}(l, y) < cnt_F(l, y)`: the
root of the bidirected edge `a ↔ b` of `exists_split`. -/
theorem key_coord {G : ADMG n} (hG : G.WF) {y : Fin n} {F F' : EdgeSet n} {T : Finset (Fin n)}
    (hTdef : T = diagH (G.cutE F) y ∅) (hT : DiagMUCT (G.cutE F) y ∅ T)
    {a₀ b₀ : Fin n} (h₀ : (a₀, b₀) ∈ F') (hd₀ : G.dir a₀ b₀ = true) (hF₀ : (a₀, b₀) ∉ F)
    (ha₀ : a₀ ∈ T) (hb₀ : b₀ ∈ T) :
    ∃ l, 0 < cnt G F T F' l y ∧ cnt G F T F' l y < cnt G F T ∅ l y := by
  have hreachT : ∀ v, v ∈ T ↔ Reach (G.cutE F).dir ∅ v y := fun v => by
    rw [hTdef]
    exact mem_T
  have hyT : y ∈ T := (hreachT y).mpr (Reach.refl y)
  have hTpar : ∀ p v, v ∈ T → G.dir p v = true → (p, v) ∉ F → p ∈ T := fun p v hv hpv hpF =>
    (hreachT p).mpr (Reach.head (ADMG.cutE_dir.mpr ⟨hpv, hpF⟩) (Finset.notMem_empty v)
      ((hreachT v).mp hv))
  obtain ⟨a, haT, b, hbT, hab, hlive, s, s', hF', hss', hbs, hs'y⟩ :=
    exists_split hG hTdef hT h₀ hd₀ hF₀ ha₀ hb₀
  refine ⟨Sum.inr (a, b), ?_, ?_⟩
  · have h1 : 1 ≤ cnt G F T F' (Sum.inr (a, b)) a :=
      one_le_cnt hG (mem_rootScope.mpr (Or.inr ⟨a, b, rfl, hab, Or.inl rfl⟩))
    have hpath : Reach ((G.cutE F).cutE F').dir ∅ a y :=
      reach_cut_of (fun b' c hab' hbc hcy hbcF => hlive b' c hbcF hbc ⟨hab', hcy⟩)
        ((hreachT a).mp haT) (Reach.refl y)
    have h2 : cnt G F T F' (Sum.inr (a, b)) a ≤ cnt G F T F' (Sum.inr (a, b)) y :=
      cnt_le_reach hG (R := ((G.cutE F).cutE F').dir) (fun b' c h => cutcut_dir b' c h) hTpar
        hpath hyT
    omega
  · have h1 : 1 ≤ cnt G F T ∅ (Sum.inr (a, b)) b :=
      one_le_cnt hG (mem_rootScope.mpr (Or.inr ⟨a, b, rfl, hab, Or.inr rfl⟩))
    have hsT : s ∈ T := (hreachT s).mpr (Reach.head hss' (Finset.notMem_empty s') hs'y)
    have h2 : cnt G F T ∅ (Sum.inr (a, b)) b ≤ cnt G F T ∅ (Sum.inr (a, b)) s :=
      cnt_le_reach hG (E := ∅) (R := (G.cutE F).dir) (fun b' c h => ⟨(ADMG.cutE_dir.mp h).1,
        (ADMG.cutE_dir.mp h).2, Finset.notMem_empty _⟩) hTpar hbs hsT
    have hs'T : s' ∈ T := (hreachT s').mpr hs'y
    have h3 : cnt G F T F' (Sum.inr (a, b)) s' < cnt G F T ∅ (Sum.inr (a, b)) s' :=
      cnt_lt_cut hG hs'T (mem_par.mpr (ADMG.cutE_dir.mp hss')) hF' (by omega)
    exact cnt_lt_reach hG (R := (G.cutE F).dir) (fun b' c h => ADMG.cutE_dir.mp h) hTpar hs'y hyT
      h3

/-! ## The witness -/

/-- **The witness of `thm: ctf-pomis`, "if"**: when `An(Y)_{𝒢_F}` is the minimal UC-territory of
`𝒢_F`, the witness model makes the best assignment of `F` (mean one) strictly better than every
assignment of every non-equivalent specification (mean at most `1/2`). -/
theorem ctfPomis_of_muct {G : ADMG n} (hG : G.WF) {y : Fin n} {F : EdgeSet n}
    (hT : DiagMUCT (G.cutE F) y ∅ (diagH (G.cutE F) y ∅)) : CtfPOMIS G y F := by
  obtain ⟨T, hTdef⟩ : ∃ T, T = diagH (G.cutE F) y ∅ := ⟨_, rfl⟩
  rw [← hTdef] at hT
  have hreachT : ∀ v, v ∈ T ↔ Reach (G.cutE F).dir ∅ v y := fun v => by
    rw [hTdef]
    exact mem_T
  have hyT : y ∈ T := (hreachT y).mpr (Reach.refl y)
  have hTpar : ∀ p v, v ∈ T → G.dir p v = true → (p, v) ∉ F → p ∈ T := fun p v hv hpv hpF =>
    (hreachT p).mpr (Reach.head (ADMG.cutE_dir.mpr ⟨hpv, hpF⟩) (Finset.notMem_empty v)
      ((hreachT v).mp hv))
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℕ, 0 < K ∧ ∀ l, 2 * cnt G F T ∅ l y < K := by
    refine ⟨2 * (∑ l, cnt G F T ∅ l y) + 1, by omega, fun l => ?_⟩
    have h1 : cnt G F T ∅ l y ≤ ∑ l', cnt G F T ∅ l' y :=
      Finset.single_le_sum (f := fun l' => cnt G F T ∅ l' y) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ l)
    omega
  have : NeZero K := ⟨by omega⟩
  refine ⟨wmodel G hG F T K, reward G F T K y, wconf hG F T K, fun F' hne => ?_⟩
  have hlow : 1 ≤ (wmodel G hG F T K).bestE y (reward G F T K y) F :=
    (muE_cstar (F := F) (T := T) (K := K) hG y).symm.le.trans
      ((wmodel G hG F T K).muE_le_bestE y _ F _)
  have hup : (wmodel G hG F T K).bestE y (reward G F T K y) F' ≤ 1 / 2 := by
    by_cases hcase : ∃ a b, (a, b) ∈ F' ∧ G.dir a b = true ∧ (a, b) ∉ F ∧ a ∈ T ∧ b ∈ T
    · obtain ⟨a₀, b₀, h₀, hd₀, hF₀, ha₀, hb₀⟩ := hcase
      obtain ⟨l, hl0, hl1⟩ := key_coord hG hTdef hT h₀ hd₀ hF₀ ha₀ hb₀
      have hKl : cnt G F T F' l y + cnt G F T ∅ l y < K := by
        have := hK l
        omega
      exact (wmodel G hG F T K).bestE_le (fun c' => muE_le_half hG hl0 hl1 hKl c')
    · have h1 : ∀ a b, (a, b) ∈ F' → G.dir a b = true → (a, b) ∉ F → a ∈ T → b ∈ T → False :=
        fun a b e1 e2 e3 e4 e5 => hcase ⟨a, b, e1, e2, e3, e4, e5⟩
      obtain ⟨p₀, v₀, hp₀F, hp₀d, hv₀T, hp₀F'⟩ :
          ∃ p v, (p, v) ∈ F ∧ G.dir p v = true ∧ v ∈ T ∧ (p, v) ∉ F' := by
        by_contra hcon
        apply hne
        refine relevant_eq_of_noEdge hTdef h1 (fun p v hpF hpv hvT => ?_)
        by_contra hpF'
        exact hcon ⟨p, v, hpF, hpv, hvT, hpF'⟩
      have hpath : Reach ((G.cutE F).cutE F').dir ∅ v₀ y :=
        reach_cut_of (fun b c _ hbc hcy hbcF => h1 b c hbcF (ADMG.cutE_dir.mp hbc).1
          (ADMG.cutE_dir.mp hbc).2 ((hreachT b).mpr (Reach.head hbc (Finset.notMem_empty c) hcy))
          ((hreachT c).mpr hcy)) ((hreachT v₀).mp hv₀T) (Reach.refl y)
      exact (wmodel G hG F T K).bestE_le (fun c' => muE_le_half_none hG (c' := c')
        (fun u => respE_none_reach hG (R := ((G.cutE F).cutE F').dir)
          (fun b c h => cutcut_dir b c h) hTpar hpath hyT
          (respE_none_start hG hv₀T hp₀F hp₀d hp₀F')))
  linarith

end CtfWit

end Mec.CtfScb
