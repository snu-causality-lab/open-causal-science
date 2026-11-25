import MecLean.Common.EdgeInt
import MecLean.Scb2018.Recursion
import MecLean.Scb2018.Semantics

set_option linter.unusedSectionVars false

/-!
# Definitions for counterfactual structural causal bandits

An edge specification provides a constant for each selected parent input of a mechanism.
An outer-target action evaluates specified targets using one fixed-input system and substitutes
their values into the natural system. An unnested action gives each target its own setting;
coherence of the shared computations licenses the fixed-input representation.

The model class has finite domains and independent finite exogenous roots. A conforming model
has the given directed and bidirected diagram. Rewards are real-valued functions of the outcome.
The POMIS comparison ranges over all edge specifications with the same diagram.
-/

open Finset

namespace Mec.CtfScb

open Mec Mec.ScbMec Mec.Scb2018

variable {n : ℕ}

/-! ## Optima -/

/-- `μ_{𝐱^⋆}`: the best mean reward over all ordinary
interventions `do(𝐒 = 𝐱)` with `Y ∉ 𝐒`. -/
noncomputable def ordOpt (m : Model n) (y : Fin n) (r : m.X y → ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => y ∉ S)).sup'
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.notMem_empty y⟩⟩
    (fun S => m.best y r S)

/-- `μ_{𝐗_{∗∗}^⋆}`: the best mean reward over the action space, all
parent-input specifications with all values.  Pairs outside the model's diagram fix nothing
(`Mech.respE_filter_pa`), so the supremum may range over all edge sets; realizable nested actions
reduce to specifications by `prop: cover realizable nested counterfactuals`
(`resp_eq_respE_reqEdges`, `UCtf.reward_eq_spec`). -/
noncomputable def ctfOpt (m : Model n) (y : Fin n) (r : m.X y → ℝ) : ℝ :=
  (Finset.univ : Finset (EdgeSet n)).sup' Finset.univ_nonempty (fun F => m.bestE y r F)

/-- `def: ctfscb action space`: a parent-input specification of `𝒢`, each
selected input with its own value.  Realizable under `𝐀^†` because each mechanism is evaluated
once (Raghavan–Bareinboim 2025, Cor. 3.7 with Assumption 3.1).  The statements of this library
range over all `EdgeSet n`; pairs outside `𝒢` are inert. -/
def CtfAction (G : ADMG n) : Type := {F : EdgeSet n // ∀ e ∈ F, G.dir e.1 e.2 = true}

/-! ## Outer-target actions (Section 6.3) -/

/-- Condition 2 of `thm: ctf-mis` for the target `x` of the outer-target
action `(X, F)`: some edge `p → v` of `𝒢` is selected by `F`, so that
`Pa(v)_{𝒢_{𝐗_{∗∗}}} ⊊ Pa(v)_𝒢`, and `v ∈ An(x)_{𝒢_{𝐗_{∗∗}} ∖ (𝐗 ∖ {x})}`: `v ∉ X ∖ {x}` and `v`
has a directed path to `x` in `𝒢_F` whose vertices avoid `X ∖ {x}`.  The path may have
length zero. -/
def Cond2 (G : ADMG n) (X : Finset (Fin n)) (F : EdgeSet n) (x : Fin n) : Prop :=
  ∃ p v : Fin n, (p, v) ∈ F ∧ G.dir p v = true ∧ v ∉ X.erase x ∧
    (G.cutE F).AncAvoid (X.erase x) v x

instance (G : ADMG n) (X : Finset (Fin n)) (F : EdgeSet n) (x : Fin n) :
    Decidable (Cond2 G X F x) := by
  unfold Cond2; infer_instance

/-- `def: ctf mis` for the outer-target action `(X, F)`: `y ∉ X`, and
no proper subset `Z ⊊ X`, keeping the inner computations of its terms, has the same mean
reward for every model conforming to `𝒢`, every reward and every assignment of the selected
inputs. -/
def CtfMIS (G : ADMG n) (y : Fin n) (X : Finset (Fin n)) (F : EdgeSet n) : Prop :=
  y ∉ X ∧ ∀ Z, Z ⊂ X → ∃ (m : Model n) (r : m.X y → ℝ) (c : Fin n → ∀ p, m.X p),
    ConfDiag G m ∧ m.muSet y r Z F c ≠ m.muSet y r X F c

/-- Realizability of the outer-target action `(X, F)`.
The targets are evaluated in the world of `F`, which needs the ancestors of the targets in
`𝒢_F`; the outer system evaluates, with no fixed input, the vertices outside `X` with a directed
path to `y` avoiding `X`.  No mechanism may be required in two versions, so a vertex needed by both
receives no constant. -/
def Realizable (G : ADMG n) (y : Fin n) (X : Finset (Fin n)) (F : EdgeSet n) : Prop :=
  ∀ v : Fin n, v ∉ X → G.AncAvoid X v y → (∃ x ∈ X, (G.cutE F).Anc v x) →
    ∀ p : Fin n, (p, v) ∈ F → G.dir p v = false

instance (G : ADMG n) (y : Fin n) (X : Finset (Fin n)) (F : EdgeSet n) :
    Decidable (Realizable G y X F) := by
  unfold Realizable; infer_instance

/-- The selected inputs required by the targets of `(X, F)`: the edges of `𝒢` in `F` whose
receivers have a directed path of `𝒢_F` to some target ("a required evaluation of `f_V`
receives a constant",, read literally). -/
def reqEdges (G : ADMG n) (X : Finset (Fin n)) (F : EdgeSet n) : EdgeSet n :=
  F.filter (fun e => G.dir e.1 e.2 = true ∧ ∃ x ∈ X, (G.cutE F).Anc e.2 x)

/-- The second step of `ctf-MISify`: visit the targets in the order `ord` and
delete a target still present that fails condition 2 for the current target set; the graph
`𝒢_F` stays fixed. -/
def misifyPass (G : ADMG n) (F : EdgeSet n) : List (Fin n) → Finset (Fin n) → Finset (Fin n)
  | [], X => X
  | x :: ord, X => misifyPass G F ord (if x ∈ X ∧ ¬ Cond2 G X F x then X.erase x else X)

/-- `ctf-MISify(𝒢, Y, 𝐗_{∗∗})` (`alg: ctf-misify`) for the outer-target action
`(X, F)`: keep the targets in `An(Y)_{𝒢_{\overline 𝐗}}`, then make one pass in the
order `ord`. -/
def misify (G : ADMG n) (y : Fin n) (X : Finset (Fin n)) (F : EdgeSet n) (ord : List (Fin n)) :
    Finset (Fin n) :=
  misifyPass G F ord (X.filter (fun x => G.AncAvoid X x y))

/-! ## Unnested counterfactual sets -/

/-- An unnested counterfactual set `𝐗_∗ = {X_{i[𝐰_i]}}_i`: its targets `tgt` and,
for each target `i`, its subscript variables `sub i`.  The subscript values are supplied for each
model separately (`c i j` is the value of `j` in the subscript of `X_i`), since domains vary
across the models of a graphical characterization. -/
structure UCtf (n : ℕ) where
  tgt : Finset (Fin n)
  sub : Fin n → Finset (Fin n)

namespace UCtf

variable (G : ADMG n) (A : UCtf n)

/-- Standing conventions: targets exclude `Y`, and no term is constant after
effectiveness (`X_i ∉ 𝐖_i`). -/
def Std (y : Fin n) : Prop := y ∉ A.tgt ∧ ∀ i ∈ A.tgt, i ∉ A.sub i

/-- The computation of `X_{i[𝐰_i]}`: `An(X_i)_{𝒢_{\overline{𝐖_i}}} ∖ 𝐖_i`, the vertices `T` of its
counterfactual ancestors `T_𝐳`. -/
def comp (i : Fin n) : Finset (Fin n) := diagH G i (A.sub i)

/-- The minimized subscript of `v` in the computation of `X_i`: the variables of
`𝐰_i ∩ An(v)_{𝒢_{\overline{𝐖_i}}}`. -/
def msub (i v : Fin n) : Finset (Fin n) := (A.sub i).filter (fun w => G.AncAvoid (A.sub i) w v)

/-- The minimized subscript of `v` in the reward term `Y_𝐱`: the variables of
`𝐗 ∩ An(v)_{𝒢_{\overline 𝐗}}`. -/
def osub (v : Fin n) : Finset (Fin n) := A.tgt.filter (fun w => G.AncAvoid A.tgt w v)

/-- Two targets' computations use the same minimized subscript variables at every shared
mechanism. -/
def SameVars : Prop :=
  ∀ i ∈ A.tgt, ∀ j ∈ A.tgt, ∀ v, v ∈ A.comp G i → v ∈ A.comp G j →
    A.msub G i v = A.msub G j v

instance : Decidable (A.SameVars G) := by
  unfold SameVars; infer_instance

/-- The targets' computations require every shared mechanism in one version: the same minimized
subscript with the same values. -/
def Consistent {Ω : Fin n → Type} (c : Fin n → ∀ j, Ω j) : Prop :=
  A.SameVars G ∧ ∀ i ∈ A.tgt, ∀ j ∈ A.tgt, ∀ v, v ∈ A.comp G i → v ∈ A.comp G j →
    ∀ w ∈ A.msub G i v, c i w = c j w

/-- The parent-input specification of `𝐗_∗`: the inputs from `𝐖_i` into the
computation of `X_{i[𝐰_i]}`. -/
def specOf : EdgeSet n :=
  Finset.univ.filter (fun e : Fin n × Fin n =>
    ∃ i ∈ A.tgt, e.1 ∈ A.sub i ∧ G.dir e.1 e.2 = true ∧ e.2 ∈ A.comp G i)

/-- The values of `specOf G A`: the input `(p, v)` receives the value of `p` in the subscript of a
target whose computation selects it (all such targets agree under `Consistent`). -/
noncomputable def specVal {Ω : Fin n → Type} [∀ i, Inhabited (Ω i)] (c : Fin n → ∀ j, Ω j) :
    Fin n → ∀ p, Ω p := fun v p =>
  if h : ∃ i ∈ A.tgt, p ∈ A.sub i ∧ G.dir p v = true ∧ v ∈ A.comp G i then
    c (Classical.choose h) p else default

/-- Realizability of the unnested action with subscript values `c`:
the targets' computations agree on shared mechanisms, and the action `(𝐗, specOf G A)` is
`Realizable` (the outer system and the targets' world share no mechanism in two versions). -/
def Realizable (y : Fin n) {Ω : Fin n → Type} (c : Fin n → ∀ j, Ω j) : Prop :=
  A.Consistent G c ∧ Mec.CtfScb.Realizable G y A.tgt (A.specOf G)

/-- The literal test of  on `An(Y_𝐱, 𝐗_∗)`, the criterion of the ICLR's Prop. 1: the targets' computations are `Consistent`, and a vertex needed both by the
reward term `Y_𝐱` and by a target's computation has the empty minimized subscript in both (the
reward term's subscript values are the targets' counterfactuals, never the constants of a
target's subscript). -/
def NoConflict (y : Fin n) {Ω : Fin n → Type} (c : Fin n → ∀ j, Ω j) : Prop :=
  A.Consistent G c ∧ ∀ i ∈ A.tgt, ∀ v, v ∉ A.tgt → G.AncAvoid A.tgt v y → v ∈ A.comp G i →
    A.osub G v = ∅ ∧ A.msub G i v = ∅

/-- The reward `Y_{𝐗_∗}(𝐮)` of the unnested action with subscript values `c`: each target `X_i` receives `X_{i[𝐰_i]}(𝐮)`, evaluated in `𝓜_{𝐰_i}` at the same `𝐮`. -/
def reward {Ω : Fin n → Type} {L : Type} {U : L → Type} [DecidableEq L] [∀ i, Inhabited (Ω i)]
    (M : Mech n Ω L U) (c : Fin n → ∀ j, Ω j) (u : ∀ l, U l) (y : Fin n) : Ω y :=
  M.resp A.tgt (fun i => M.resp (A.sub i) (c i) u i) u y

end UCtf

/-! ## Parent-input specifications (Sections 6.4–6.5) -/

/-- The directed edges of `𝒢[An(Y)_𝒢]`: the inputs the children choices can
select. -/
def hEdges (G : ADMG n) (y : Fin n) : EdgeSet n :=
  Finset.univ.filter (fun e : Fin n × Fin n => G.dir e.1 e.2 = true ∧ G.Anc e.2 y)

/-- The pruned specification: the selected edges of `𝒢` whose receivers remain
ancestors of `y` in `𝒢_F`.  The source of a retained input may itself have left the ancestral
graph. -/
def relevant (G : ADMG n) (y : Fin n) (F : EdgeSet n) : EdgeSet n :=
  F.filter (fun e => G.dir e.1 e.2 = true ∧ e.2 ∈ diagH (G.cutE F) y ∅)

/-- `IB(𝓗_{𝐗_{∗∗}}, Y)` with `𝓗_{𝐗_{∗∗}} = 𝒢_F[An(Y)_{𝒢_F}]`: `diagH (G.cutE F) y ∅` is `An(Y)_{𝒢_F}`, `Alg.muct` its minimal UC-territory and
`diagBorder` the border. -/
def ctfIB (G : ADMG n) (y : Fin n) (F : EdgeSet n) : Finset (Fin n) :=
  Alg.ib (G.cutE F) y ∅

/-- `def: ctf-pomis` for parent-input specifications: some model conforming to
`𝒢`, with some reward, makes the best assignment of `F` strictly better than the best assignment
of every non-equivalent specification.  Equivalence is equality of the pruned specifications. -/
def CtfPOMIS (G : ADMG n) (y : Fin n) (F : EdgeSet n) : Prop :=
  ∃ (m : Model n) (r : m.X y → ℝ), ConfDiag G m ∧
    ∀ F' : EdgeSet n, relevant G y F' ≠ relevant G y F → m.bestE y r F' < m.bestE y r F

/-- Equivalence of specifications: in every model conforming to `𝒢`, every
assignment of either specification has an assignment of the other that gives the same reward on
every unit.  The corresponding assignment may depend on the model. -/
def SpecEquiv (G : ADMG n) (y : Fin n) (F F' : EdgeSet n) : Prop :=
  ∀ m : Model n, ConfDiag G m →
    (∀ c : Fin n → ∀ p, m.X p, ∃ c' : Fin n → ∀ p, m.X p,
      ∀ u : ∀ l, m.U l, m.scm.toMech.respE F c u y = m.scm.toMech.respE F' c' u y) ∧
    (∀ c' : Fin n → ∀ p, m.X p, ∃ c : Fin n → ∀ p, m.X p,
      ∀ u : ∀ l, m.U l, m.scm.toMech.respE F c u y = m.scm.toMech.respE F' c' u y)

/-- The inputs entering `T` from outside along directed edges of `𝒢_F`: the inputs that
`𝐗'_{∗∗}` fixes in the proof of `thm: ctf-pomis`, "only if". -/
def borderEdges (G : ADMG n) (F : EdgeSet n) (T : Finset (Fin n)) : EdgeSet n :=
  Finset.univ.filter (fun e : Fin n × Fin n =>
    (G.cutE F).dir e.1 e.2 = true ∧ e.1 ∉ T ∧ e.2 ∈ T)

/-- The inputs of `f_Y`: every edge of `𝒢` into `y`. -/
def inEdges (G : ADMG n) (y : Fin n) : EdgeSet n :=
  Finset.univ.filter (fun e : Fin n × Fin n => G.dir e.1 e.2 = true ∧ e.2 = y)

/-- The output of `alg: ctf-pomis`: for every children choice, the set of selected
edges `F ⊆ 𝐄(𝒢[An(Y)_𝒢])`, the pruned specification is returned when the
border of `𝒢_F[An(Y)_{𝒢_F}]` is empty, each once. -/
def ctfPOMISs (G : ADMG n) (y : Fin n) : Finset (EdgeSet n) :=
  ((hEdges G y).powerset.filter (fun F => ctfIB G y F = ∅)).image (relevant G y)

/-- The `CTF-MIS` baseline: every pruned selection of inputs of `𝒢[An(Y)_𝒢]`,
without the border test. -/
def ctfMISBaseline (G : ADMG n) (y : Fin n) : Finset (EdgeSet n) :=
  (hEdges G y).powerset.image (relevant G y)

/-- The ordinary POMISs:
`Y ∉ 𝐗` and `IB(𝒢_{\overline 𝐗}, Y) = 𝐗`. -/
def pomisSets (G : ADMG n) (y : Fin n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S : Finset (Fin n) => y ∉ S ∧ Alg.ib G y S = S)

/-- The number of arms of a collection of sets when every element has its own binary value: `∑ 2^{|F|}`. -/
def binArms {α : Type*} (C : Finset (Finset α)) : ℕ := ∑ F ∈ C, 2 ^ F.card

end Mec.CtfScb
