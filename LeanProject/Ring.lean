import LeanProject.Structures

namespace Project

class Rig (α : Type u) extends AddMonoid α, AddCommutative α, MulMonoid α where
  left_distrib  : ∀ a b c : α, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c

class Semiring (α : Type u) extends Rig α where
  zero_absorbs : ∀ a : α, a * zero = zero ∧ zero * a = zero

class Ring (α : Type u) extends Semiring α, AddInvertible α

theorem ring_zero_absorbs [Ring α] (a : α) : a * AddIdent.zero = AddIdent.zero ∧ AddIdent.zero * a = AddIdent.zero := by
  constructor
  ·
    obtain ⟨a0i, h_left, h_right⟩ := AddInvertible.inverses (a*AddIdent.zero)
    have h1 :
      a*AddIdent.zero = a*AddIdent.zero + a*AddIdent.zero := by rw [← Rig.left_distrib, (AddIdent.zero_ident _).left]
    symm
    calc
      AddIdent.zero = a*(AddIdent.zero:α)+a0i := by rw [h_left]
      _             = (a*AddIdent.zero+a*AddIdent.zero)+a0i := by rw [← h1]
      _             = a*AddIdent.zero+(a*AddIdent.zero+a0i) := by rw [AddAssociative.add_associative]
      _             = a*AddIdent.zero+AddIdent.zero := by rw [h_left]
      _             = a*AddIdent.zero := by rw [(AddIdent.zero_ident _).right]
  ·
    obtain ⟨a0i, h_left, h_right⟩ := AddInvertible.inverses (AddIdent.zero*a)
    have h1 :
      AddIdent.zero*a = AddIdent.zero*a + AddIdent.zero*a := by rw [← Rig.right_distrib, (AddIdent.zero_ident _).left]
    symm
    calc
      AddIdent.zero = (AddIdent.zero:α)*a+a0i := by rw [h_left]
      _             = (AddIdent.zero*a+AddIdent.zero*a)+a0i := by rw [← h1]
      _             = AddIdent.zero*a+(AddIdent.zero*a+a0i) := by rw [AddAssociative.add_associative]
      _             = AddIdent.zero*a+AddIdent.zero := by rw [h_left]
      _             = AddIdent.zero*a := by rw [(AddIdent.zero_ident _).right]

instance [Ring α] : Semiring α where
  zero_absorbs := ring_zero_absorbs

structure Congruence [Semiring α] (r : Relation α) where
  eq   : Equivalence r
  add_cong : ∀a b c d: α, r a b ∧ r c d -> r (a + c) (b + d)
  mul_cong : ∀a b c d: α, r a b ∧ r c d -> r (a * c) (b * d)

variable {α : Type} [Semiring α]
variable {r : Relation α} (h : Congruence r)

@[instance_reducible]
def quotSemiring : Semiring (Quot r) where
  zero := Quot.mk r AddIdent.zero
  one := Quot.mk r MulIdent.one
  add := Quot.lift (λa =>
    Quot.lift (λb =>
      Quot.mk r (a + b)
    ) (by
      intro b c h1
      apply Quot.sound
      apply h.add_cong a a b c
      constructor
      · apply h.eq.left
      · exact h1
    )
  ) (by
    intro a b h1
    funext x
    induction x using Quot.ind with | mk x =>
    dsimp
    apply Quot.sound
    apply (h.add_cong a b x x)
    constructor
    · exact h1
    · apply h.eq.left
  )
  mul := Quot.lift (λa =>
    Quot.lift (λb =>
      Quot.mk r (a * b)
    ) (by
      intro b c h1
      apply Quot.sound
      apply h.mul_cong a a b c
      constructor
      · apply h.eq.left
      · exact h1
    )
  ) (by
    intro a b h1
    funext x
    induction x using Quot.ind with | mk x =>
    dsimp
    apply Quot.sound
    apply (h.mul_cong a b x x)
    constructor
    · exact h1
    · apply h.eq.left
  )
  add_associative a b c := by
    induction c using Quot.ind with | mk c =>
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [AddAssociative.add_associative]
  zero_ident a := by
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [AddCommutative.commutative]
    rw [p_and_p]
    rw [(AddIdent.zero_ident a).right]
  commutative a b := by
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [AddCommutative.commutative]
  mul_associative a b c := by
    induction c using Quot.ind with | mk c =>
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [MulAssociative.mul_associative]
  one_ident a := by
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [(MulIdent.one_ident a).left]
    rw [(MulIdent.one_ident a).right]
    rw [p_and_p]
  left_distrib a b c := by
    induction c using Quot.ind with | mk c =>
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [Rig.left_distrib]
  right_distrib a b c := by
    induction c using Quot.ind with | mk c =>
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [Rig.right_distrib]
  zero_absorbs a := by
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [(Semiring.zero_absorbs a).left]
    rw [(Semiring.zero_absorbs a).right]
    rw [p_and_p]

end Project
