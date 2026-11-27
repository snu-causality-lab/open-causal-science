import OpenCausalScienceAnalysis.Decision.SCB2019Projection
import OpenCausalScienceAnalysis.Decision.SCB2019Witness

/-!
# Restoring a vertex for the corrected 2019 structural causal bandits proposition

A source read by two vertices in the projected model may be routed to the restored
vertex. Each child can then read its original source value through that vertex.
The restored vertex can also relay directed parent values. The construction
uses independent one-point roots for unused edges of the original diagram.

Source: Lee and Bareinboim, revised Proposition 3, September 19, 2026.
https://www.sanghacklee.me/ai-corrected/SCB2019_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScienceAnalysis.Scb2019

open Mec Mec.ScbMec Finset

variable {n : ℕ}

private def readers (m : Model n) (w : Fin n) (l : m.L) : Finset (Fin n) :=
  (univ.filter fun i => l ∈ m.scm.ex i).erase w

private theorem mem_readers {m : Model n} {w : Fin n} {l : m.L} {i : Fin n} :
    i ∈ readers m w l ↔ i ≠ w ∧ l ∈ m.scm.ex i := by
  simp [readers]

private structure SourceRoute (G : ADMG n) (w : Fin n) (projectedReaders : Finset (Fin n))
    where
  attached : Finset (Fin n)
  pairwise : attached.card ≤ 2
  compatible : ∀ i ∈ attached, ∀ j ∈ attached, i ≠ j → G.bi i j = true
  available : ∀ i ∈ projectedReaders, i ∈ attached ∨
    (w ∈ attached ∧ G.dir w i = true)

private theorem pair_compatible {G : ADMG n} (wf : G.WF) {a b : Fin n}
    (edge : G.bi a b = true) :
    ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ j ∈ ({a, b} : Finset (Fin n)),
      i ≠ j → G.bi i j = true := by
  intro i hi j hj distinct
  simp only [mem_insert, mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (distinct rfl).elim
  · exact edge
  · rw [wf.bi_symm]
    exact edge
  · exact (distinct rfl).elim

private theorem source_route_exists {G : ADMG n} (wf : G.WF) (w : Fin n)
    (m : Model n) (graph : ConfDiag (eliminate G w) m) (pairwise : PairwiseRoots m)
    (l : m.L) : Nonempty (SourceRoute G w (readers m w l)) := by
  have atMostTwo : (readers m w l).card ≤ 2 :=
    (Finset.card_le_card (Finset.erase_subset _ _)).trans (pairwise l)
  by_cases atMostOne : (readers m w l).card ≤ 1
  · refine ⟨⟨readers m w l, atMostTwo, ?_, fun _ hit => .inl hit⟩⟩
    intro i hi j hj distinct
    exact (distinct (Finset.card_le_one.mp atMostOne i hi j hj)).elim
  obtain ⟨a, b, distinct, pair⟩ := Finset.card_eq_two.mp (by omega : (readers m w l).card = 2)
  have ha : a ∈ readers m w l := by simp [pair]
  have hb : b ∈ readers m w l := by simp [pair]
  obtain ⟨_, readA⟩ := mem_readers.mp ha
  obtain ⟨_, readB⟩ := mem_readers.mp hb
  have projectedEdge : (eliminate G w).bi a b = true := by
    change m.scm.toMech.diag = eliminate G w at graph
    rw [← graph]
    exact decide_eq_true ⟨distinct, l, Finset.mem_inter.mpr ⟨readA, readB⟩⟩
  have cases := ((bi_eliminate_iff G w a b).mp projectedEdge).2.2.2
  rcases cases with direct | fromA | fromB | both
  · refine ⟨⟨{a, b}, Finset.card_le_two, pair_compatible wf direct, ?_⟩⟩
    intro i hi
    exact .inl (pair ▸ hi)
  · refine ⟨⟨{a, w}, Finset.card_le_two, pair_compatible wf fromA.1, ?_⟩⟩
    intro i hi
    rw [pair] at hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact .inl (by simp)
    · exact .inr ⟨by simp, fromA.2⟩
  · refine ⟨⟨{b, w}, Finset.card_le_two, pair_compatible wf fromB.1, ?_⟩⟩
    intro i hi
    rw [pair] at hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact .inr ⟨by simp, fromB.2⟩
    · exact .inl (by simp)
  · refine ⟨⟨{w}, by simp, ?_, ?_⟩⟩
    · intro i hi j hj distinct
      simp only [mem_singleton] at hi hj
      exact (distinct (hi.trans hj.symm)).elim
    · intro i hi
      rw [pair] at hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact .inr ⟨by simp, both.1⟩
      · exact .inr ⟨by simp, both.2⟩

private abbrev Relayed (m : Model n) := (∀ i, m.X i) × (∀ l, m.U l)

private def RestoredState (m : Model n) (w i : Fin n) : Type :=
  if i = w then Relayed m else m.X i

private theorem restoredState_eq_relayed (m : Model n) (w : Fin n) :
    RestoredState m w w = Relayed m := ite_eq_left rfl

private theorem restoredState_eq_retained (m : Model n) {w i : Fin n} (hi : i ≠ w) :
    RestoredState m w i = m.X i := ite_eq_right hi

@[instance_reducible] private def stateFintype (m : Model n) (w i : Fin n) : Fintype (RestoredState m w i) := by
  unfold RestoredState
  split_ifs <;> infer_instance

private noncomputable def rootDefault (m : Model n) (l : m.L) : m.U l := by
  classical
  apply Classical.choice
  by_contra empty
  let : IsEmpty (m.U l) := ⟨fun u => empty ⟨u⟩⟩
  simpa using m.scm.p_sum l

private def encode (m : Model n) (w : Fin n) (x : ∀ i, m.X i) (buffer : Relayed m) :
    ∀ i, RestoredState m w i :=
  fun i => if isW : i = w then
      cast (congrArg (RestoredState m w) isW.symm) (cast (restoredState_eq_relayed m w).symm buffer)
    else cast (restoredState_eq_retained m isW).symm (x i)

private def decode (m : Model n) (w : Fin n) (x : ∀ i, RestoredState m w i) :
    ∀ i, m.X i :=
  fun i => if isW : i = w then default else cast (restoredState_eq_retained m isW) (x i)

private def relayValue (m : Model n) (w : Fin n) (x : ∀ i, RestoredState m w i) :
    Relayed m :=
  cast (restoredState_eq_relayed m w) (x w)

private theorem decode_encode {m : Model n} {w : Fin n} (v : ∀ i, m.X i)
    (buffer : Relayed m) {i : Fin n} (hi : i ≠ w) :
    decode m w (encode m w v buffer) i = v i := by
  simp [decode, encode, hi]

private theorem relayValue_encode {m : Model n} {w : Fin n} (v : ∀ i, m.X i)
    (buffer : Relayed m) :
    relayValue m w (encode m w v buffer) = buffer := by
  simp [relayValue, encode]

private abbrev RestoredRoots (m : Model n) := m.L ⊕ Roots n

private def RestoredNoise (m : Model n) : RestoredRoots m → Type
  | .inl l => m.U l
  | .inr _ => Unit

@[instance_reducible] private def noiseFintype (m : Model n) : ∀ l : RestoredRoots m, Fintype (RestoredNoise m l)
  | .inl l => m.fU l
  | .inr _ => inferInstanceAs (Fintype Unit)

private abbrev Routes (G : ADMG n) (m : Model n) (w : Fin n) :=
  ∀ l : m.L, SourceRoute G w (readers m w l)

private def rootUsed {G : ADMG n} {m : Model n} {w : Fin n} (routes : Routes G m w)
    (i : Fin n) : RestoredRoots m → Prop
  | .inl l => i ∈ (routes l).attached
  | .inr l => l ∈ rootScope G i

private noncomputable def restoredScope {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (i : Fin n) : Finset (RestoredRoots m) := by
  classical
  exact univ.filter (rootUsed routes i)

private theorem mem_restoredScope {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (i : Fin n) (l : RestoredRoots m) :
    l ∈ restoredScope routes i ↔ rootUsed routes i l := by
  classical
  simp [restoredScope]

private noncomputable def payload {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (x : ∀ i, RestoredState m w i)
    (u : ∀ l, RestoredNoise m l) : Relayed m :=
  (fun j => if G.dir j w = true then decode m w x j else default,
   fun l => if w ∈ (routes l).attached then u (.inl l) else rootDefault m l)

private def parentValues {G : ADMG n} {m : Model n} {w : Fin n}
    (i : Fin n) (x : ∀ j, RestoredState m w j) : ∀ j, m.X j :=
  fun j => if G.dir j i = true then decode m w x j
    else if G.dir w i = true then (relayValue m w x).1 j else default

private noncomputable def sourceValues {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (i : Fin n) (x : ∀ j, RestoredState m w j)
    (u : ∀ l, RestoredNoise m l) : ∀ l, m.U l :=
  fun l => if i ∈ (routes l).attached then u (.inl l)
    else if G.dir w i = true then (relayValue m w x).2 l else rootDefault m l

private noncomputable def mechanism {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (i : Fin n) (x : ∀ j, RestoredState m w j)
    (u : ∀ l, RestoredNoise m l) : RestoredState m w i :=
  if isW : i = w then
    cast (congrArg (RestoredState m w) isW.symm)
      (cast (restoredState_eq_relayed m w).symm (payload routes x u))
  else cast (restoredState_eq_retained m isW).symm
    (m.scm.f i (parentValues (G := G) i x) (sourceValues routes i x u))

private theorem mechanism_dep_parents {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (i : Fin n) (x x' : ∀ j, RestoredState m w j)
    (u : ∀ l, RestoredNoise m l) (same : ∀ j, G.dir j i = true → x j = x' j) :
    mechanism routes i x u = mechanism routes i x' u := by
  by_cases isW : i = w
  · subst i
    simp only [mechanism]
    change cast (restoredState_eq_relayed m w).symm _ =
      cast (restoredState_eq_relayed m w).symm _
    apply congrArg (cast (restoredState_eq_relayed m w).symm)
    apply Prod.ext
    · funext j
      by_cases edge : G.dir j w = true
      · simp [payload, edge, decode, same j edge]
      · simp [payload, edge]
    · rfl
  · have relaySame (edge : G.dir w i = true) :
        relayValue m w x = relayValue m w x' := by
      simp [relayValue, same w edge]
    have parents : parentValues (G := G) i x = parentValues (G := G) i x' := by
      funext j
      by_cases edge : G.dir j i = true
      · simp [parentValues, edge, decode, same j edge]
      · by_cases route : G.dir w i = true
        · simp [parentValues, edge, route, relaySame route]
        · simp [parentValues, edge, route]
    have noise : sourceValues routes i x u = sourceValues routes i x' u := by
      funext l
      by_cases route : G.dir w i = true
      · simp [sourceValues, route, relaySame route]
      · simp [sourceValues, route]
    simp [mechanism, isW, parents, noise]

private theorem mechanism_dep_sources {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (i : Fin n) (x : ∀ j, RestoredState m w j)
    (u u' : ∀ l, RestoredNoise m l)
    (same : ∀ l ∈ restoredScope routes i, u l = u' l) :
    mechanism routes i x u = mechanism routes i x u' := by
  have here (l : m.L) (h : i ∈ (routes l).attached) : u (.inl l) = u' (.inl l) :=
    same (.inl l) ((mem_restoredScope routes i (.inl l)).mpr h)
  by_cases isW : i = w
  · subst i
    simp only [mechanism]
    change cast (restoredState_eq_relayed m w).symm _ =
      cast (restoredState_eq_relayed m w).symm _
    apply congrArg (cast (restoredState_eq_relayed m w).symm)
    apply Prod.ext
    · rfl
    · funext l
      by_cases direct : w ∈ (routes l).attached
      · simp [payload, direct, here l direct]
        rfl
      · simp [payload, direct]
  · have noise : sourceValues routes i x u = sourceValues routes i x u' := by
      funext l
      by_cases direct : i ∈ (routes l).attached
      · simp [sourceValues, direct, here l direct]
        rfl
      · simp [sourceValues, direct]
    simp [mechanism, isW, noise]

private noncomputable def restoredMech {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) :
    Mech n (RestoredState m w) (RestoredRoots m) (RestoredNoise m) where
  pa i := univ.filter (fun j => G.dir j i = true)
  ex := restoredScope routes
  rank := topRank G
  pa_rank := fun h => topRank_lt wf (by simpa using h)
  f := mechanism routes
  f_pa := fun i x x' u same => mechanism_dep_parents routes i x x' u
    (fun j edge => same j (by simp [edge]))
  f_ex := mechanism_dep_sources routes

private theorem restored_diagram {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) : (restoredMech wf routes).diag = G := by
  rw [ADMG.ext_iff']
  constructor
  · funext j i
    simp [Mech.diag, restoredMech]
  · funext i j
    change decide (i ≠ j ∧ (restoredScope routes i ∩ restoredScope routes j).Nonempty) =
      G.bi i j
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨distinct, l, member⟩
      obtain ⟨hi, hj⟩ := Finset.mem_inter.mp member
      have readI := (mem_restoredScope routes i l).mp hi
      have readJ := (mem_restoredScope routes j l).mp hj
      cases l with
      | inl k => exact (routes k).compatible i readI j readJ distinct
      | inr k => exact (rootScope_inter wf distinct).mp ⟨k, Finset.mem_inter.mpr ⟨readI, readJ⟩⟩
    · intro edge
      have distinct : i ≠ j := by
        rintro rfl
        simp [wf.bi_irrefl] at edge
      obtain ⟨k, hk⟩ := (rootScope_inter wf distinct).mpr edge
      obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hk
      exact ⟨distinct, .inr k, Finset.mem_inter.mpr
        ⟨(mem_restoredScope routes i (.inr k)).mpr hi, (mem_restoredScope routes j (.inr k)).mpr hj⟩⟩

private theorem restored_pairwise {G : ADMG n} {m : Model n} {w : Fin n}
    (routes : Routes G m w) (l : RestoredRoots m) :
    (univ.filter fun i => l ∈ restoredScope routes i).card ≤ 2 := by
  cases l with
  | inl l =>
    have eq : univ.filter (fun i => Sum.inl l ∈ restoredScope routes i) =
        (routes l).attached := by
      ext i
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, rootUsed] using
        mem_restoredScope routes i (.inl l)
    rw [eq]
    exact (routes l).pairwise
  | inr l =>
    apply card_le_two_of_rootScope (G := G) (l := l)
    intro i hi
    simp only [Finset.mem_filter] at hi
    exact (mem_restoredScope routes i (.inr l)).mp hi.2

private noncomputable def restoredP (m : Model n) : ∀ l, RestoredNoise m l → ℝ
  | .inl l, u => m.scm.p l u
  | .inr _, _ => 1

private noncomputable def restoredModel {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) : Model n := by
  classical
  let : ∀ i, Fintype (RestoredState m w i) := stateFintype m w
  let : ∀ i, DecidableEq (RestoredState m w i) := fun _ => Classical.typeDecidableEq _
  let : ∀ i, Inhabited (RestoredState m w i) := fun i => ⟨encode m w
    (fun _ => default) ((fun _ => default), rootDefault m) i⟩
  let : ∀ l, Fintype (RestoredNoise m l) := noiseFintype m
  exact {
    X := RestoredState m w
    L := RestoredRoots m
    U := RestoredNoise m
    scm := {
      toMech := restoredMech wf routes
      p := restoredP m
      p_nonneg := fun l u => by
        cases l
        · exact m.scm.p_nonneg _ u
        · exact zero_le_one
      p_sum := fun l => by
        cases l
        · exact m.scm.p_sum _
        · change (∑ _ : Unit, (1 : ℝ)) = 1
          simp
    }
  }

private def restrictNoise (m : Model n) (u : ∀ l, RestoredNoise m l) : ∀ l, m.U l :=
  fun l => u (.inl l)

private def extendNoise (m : Model n) (u : ∀ l, m.U l) : ∀ l, RestoredNoise m l
  | .inl l => u l
  | .inr _ => ()

private def worldEquiv (m : Model n) :
    (∀ l, RestoredNoise m l) ≃ (∀ l, m.U l) where
  toFun := restrictNoise m
  invFun := extendNoise m
  right_inv _ := rfl
  left_inv u := by
    funext l
    cases l
    · rfl
    · exact Subsingleton.elim (α := Unit) _ _

private theorem restored_prob {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) (u : ∀ l, RestoredNoise m l) :
    (restoredModel wf routes).scm.prob u = m.scm.prob (restrictNoise m u) := by
  unfold SCM.prob
  change (∏ l : RestoredRoots m, restoredP m l (u l)) =
    ∏ l : m.L, m.scm.p l (u (.inl l))
  rw [Fintype.prod_sum_type]
  simp [restoredP]

private def rewardCast (m : Model n) {w y : Fin n} (hy : y ≠ w)
    (r : m.X y → ℝ) (v : RestoredState m w y) : ℝ :=
  r (cast (restoredState_eq_retained m hy) v)

private theorem restored_response {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) (graph : ConfDiag (eliminate G w) m)
    {S : Finset (Fin n)} (hw : w ∉ S) (x : ∀ i, RestoredState m w i)
    (u : ∀ l, RestoredNoise m l) {y : Fin n} (hy : y ≠ w) :
    decode m w ((restoredModel wf routes).scm.toMech.resp S x u) y =
      m.scm.toMech.resp S (decode m w x) (restrictNoise m u) y := by
  let old := m.scm.toMech.resp S (decode m w x) (restrictNoise m u)
  let stored : Relayed m :=
    (fun j => if G.dir j w = true then old j else default,
     fun l => if w ∈ (routes l).attached then u (.inl l) else rootDefault m l)
  let extended := encode m w old stored
  have decodeExtended (i : Fin n) (hi : i ≠ w) : decode m w extended i = old i :=
    decode_encode old stored hi
  have storeExtended : relayValue m w extended = stored := relayValue_encode old stored
  have readStored : payload routes extended u = stored := by
    apply Prod.ext
    · funext j
      by_cases edge : G.dir j w = true
      · have hj : j ≠ w := by rintro rfl; simp [wf.dir_irrefl] at edge
        simp [payload, stored, edge, decodeExtended j hj]
      · simp [payload, stored, edge]
    · rfl
  have atParents (i : Fin n) (j : Fin n) (member : j ∈ m.scm.pa i) :
      parentValues (G := G) i extended j = old j := by
    have edge : (eliminate G w).dir j i = true := by
      change m.scm.toMech.diag = eliminate G w at graph
      rw [← graph]
      exact m.scm.toMech.diag_dir.mpr member
    obtain ⟨hj, _, direct | ⟨into, out⟩⟩ := (dir_eliminate_iff G w j i).mp edge
    · simp [parentValues, direct, decodeExtended j hj]
    · by_cases direct : G.dir j i = true
      · simp [parentValues, direct, decodeExtended j hj]
      · simp [parentValues, direct, out, storeExtended, stored, into]
  have atSources (i : Fin n) (hi : i ≠ w) (l : m.L) (member : l ∈ m.scm.ex i) :
      sourceValues routes i extended u l = restrictNoise m u l := by
    by_cases direct : i ∈ (routes l).attached
    · simp [sourceValues, direct, restrictNoise]
      rfl
    · obtain bad | ⟨into, out⟩ := (routes l).available i (mem_readers.mpr ⟨hi, member⟩)
      · exact (direct bad).elim
      · simp [sourceValues, direct, out, storeExtended, stored, into, restrictNoise]
        rfl
  have equilibrium : extended = (restoredModel wf routes).scm.toMech.resp S x u := by
    apply (restoredModel wf routes).scm.toMech.eq_resp
    intro i
    change extended i = if i ∈ S then x i else mechanism routes i extended u
    by_cases isW : i = w
    · subst i
      simp [extended, encode, hw, mechanism, readStored]
    · by_cases manipulated : i ∈ S
      · have response : old i = decode m w x i := m.scm.toMech.resp_of_mem manipulated
        simp [extended, encode, isW, manipulated, response, decode]
      · have response : old i =
            m.scm.f i (parentValues (G := G) i extended) (sourceValues routes i extended u) := by
          calc
            old i = m.scm.f i old (restrictNoise m u) :=
              m.scm.toMech.resp_of_not_mem manipulated
            _ = m.scm.f i (parentValues (G := G) i extended) (restrictNoise m u) :=
              m.scm.f_pa i old _ _ (fun j member => (atParents i j member).symm)
            _ = _ := m.scm.f_ex i _ _ _ (fun l member => (atSources i isW l member).symm)
        simp [extended, encode, isW, manipulated, mechanism, response]
  rw [← equilibrium]
  exact decodeExtended y hy

private theorem restored_mean {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) (graph : ConfDiag (eliminate G w) m)
    {y : Fin n} (hy : y ≠ w) (r : m.X y → ℝ) {S : Finset (Fin n)} (hw : w ∉ S)
    (x : ∀ i, RestoredState m w i) :
    (restoredModel wf routes).mu y (rewardCast m hy r) S x =
      m.mu y r S (decode m w x) := by
  let : ∀ l, Fintype (RestoredNoise m l) := noiseFintype m
  unfold Model.mu SCM.E
  change (∑ u : ∀ l, RestoredNoise m l, (restoredModel wf routes).scm.prob u *
      rewardCast m hy r ((restoredModel wf routes).scm.toMech.resp S x u y)) =
    ∑ u : ∀ l, m.U l, m.scm.prob u * r (m.scm.toMech.resp S (decode m w x) u y)
  apply Fintype.sum_equiv (worldEquiv m)
  intro u
  rw [restored_prob wf routes u]
  have response := restored_response wf routes graph hw x u hy
  simp only [decode, dite_eq_right hy] at response
  simp only [rewardCast, response]
  rfl

private theorem restored_best {G : ADMG n} {m : Model n} {w : Fin n}
    (wf : G.WF) (routes : Routes G m w) (graph : ConfDiag (eliminate G w) m)
    {y : Fin n} (hy : y ≠ w) (r : m.X y → ℝ) {S : Finset (Fin n)} (hw : w ∉ S) :
    (restoredModel wf routes).best y (rewardCast m hy r) S = m.best y r S := by
  apply le_antisymm
  · obtain ⟨x, hx⟩ := (restoredModel wf routes).exists_best y (rewardCast m hy r) S
    change (∀ i, RestoredState m w i) at x
    calc
      _ = (restoredModel wf routes).mu y (rewardCast m hy r) S x := hx.symm
      _ = m.mu y r S (decode m w x) := restored_mean wf routes graph hy r hw x
      _ ≤ _ := m.mu_le_best _ _ _ _
  · obtain ⟨x, hx⟩ := m.exists_best y r S
    let newX := encode m w x ((fun _ => default), rootDefault m)
    have arm : m.mu y r S (decode m w newX) = m.mu y r S x := by
      apply m.mu_congr
      intro u
      have same := m.scm.toMech.resp_congr (S := S) (x := decode m w newX) (x' := x)
        u fun i hi => decode_encode x _ (fun (eq : i = w) => hw (eq ▸ hi))
      exact congrFun same y
    calc
      _ = m.mu y r S x := hx.symm
      _ = m.mu y r S (decode m w newX) := arm.symm
      _ = (restoredModel wf routes).mu y (rewardCast m hy r) S newX :=
        (restored_mean wf routes graph hy r hw newX).symm
      _ ≤ _ := (restoredModel wf routes).mu_le_best _ _ _ _

/-- Restore one eliminated vertex without changing the best reward of any intervention that
does not manipulate it. The single restored model works for all intervention sets. -/
theorem restore_eliminated {G : ADMG n} (wf : G.WF) (w : Fin n) (m : Model n)
    (graph : ConfDiag (eliminate G w) m) (pairwise : PairwiseRoots m)
    (y : Fin n) (hy : y ≠ w) (r : m.X y → ℝ) :
    ∃ (m' : Model n) (r' : m'.X y → ℝ), ConfDiag G m' ∧ PairwiseRoots m' ∧
      ∀ S, w ∉ S → m'.best y r' S = m.best y r S := by
  classical
  let routes : Routes G m w := fun l => Classical.choice (source_route_exists wf w m graph pairwise l)
  refine ⟨restoredModel wf routes, rewardCast m hy r, restored_diagram wf routes,
    restored_pairwise routes, ?_⟩
  intro S hw
  exact restored_best wf routes graph hy r hw

end OpenCausalScienceAnalysis.Scb2019
