module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.GroundOracle

@[expose] public section

namespace RCDLight.Learning

open OpenCausalScience.ActiveSimplePath RCDPathValidity

variable {K A : Type} {S : Schema K} {m : Model K A}

/-- The length-two ground path transfers either Lemma 2 dependence test
to the relational query when the three variables name their items uniquely. -/
theorem isolated_ground_triple_is_dependent {t : Triple K A}
    {g : Skeleton S} {base : g.Item} {x y z : GroundVertex m g}
    (left : instantiates g base (t.left m) x)
    (mid : instantiates g base t.middle y)
    (right : instantiates g base t.right z)
    (xy : x ≠ y) (yz : y ≠ z) (xz : x ≠ z)
    (first : Adjacent (groundArrow m g) x y)
    (second : Adjacent (groundArrow m g) z y)
    (collider : t.collider m ↔ groundArrow m g x y ∧ groundArrow m g z y)
    (uniqueLeft : ∀ word, Terminal g word base x.item → word = (t.left m).1)
    (uniqueMiddle : ∀ word, Terminal g word base y.item → word = t.middle.1)
    (uniqueRight : ∀ word, Terminal g word base z.item → word = t.right.1)
    {conditions : List (Variable K A)}
    (leftOut : t.left m ∉ conditions) (rightOut : t.right ∉ conditions)
    (active : (t.collider m ∧ t.middle ∈ conditions) ∨
      (¬ t.collider m ∧ t.middle ∉ conditions)) :
    ¬ GroundSeparated m S (t.left m) t.right conditions := by
  let C : GroundVertex m g → Prop := conditionedAt g base conditions
  have conditional {v : Variable K A} {p : GroundVertex m g}
      (inst : instantiates g base v p)
      (single : ∀ word, Terminal g word base p.item → word = v.1) :
      C p ↔ v ∈ conditions := by
    constructor
    · rintro ⟨other, member, attr, word⟩
      have eq : other = v := Prod.ext (single _ word) (attr.symm.trans inst.1)
      exact eq ▸ member
    · intro member
      exact ⟨v, member, inst⟩
  have openMiddle : OpenTurn (groundArrow m g) C z y x := by
    rcases active with ⟨head, member⟩ | ⟨head, member⟩
    · exact .inl ⟨(collider.mp head).symm, .conditioned ((conditional mid uniqueMiddle).mpr member)⟩
    · exact .inr ⟨fun headGround => head (collider.mpr headGround.symm),
        fun selected => member ((conditional mid uniqueMiddle).mp selected)⟩
  have connected : DConnected (groundArrow m g) C z x :=
    ⟨y, [x], .cons second openMiddle (.last first.symm), by
      simp [Ne.symm xz, Ne.symm yz, Ne.symm xy]⟩
  intro separated
  exact (separated g base x z left right
    (fun selected => leftOut ((conditional left uniqueLeft).mp selected))
    (fun selected => rightOut ((conditional right uniqueRight).mp selected))).2 connected

end RCDLight.Learning

end
