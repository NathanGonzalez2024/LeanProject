
namespace Project

theorem obvious (P : Prop): P -> P := by
  intro h
  exact h

theorem p_and_p : P ∧ P <-> P := by
  constructor
  · intro p; exact p.left
  · intro p; exact ⟨p, p⟩

def Relation (α : Type u) : Type u := α -> α -> Prop

variable {α : Type u} (r : Relation α)

  def Reflexive : Prop
    := ∀ x : α, r x x

  def Symmetric : Prop
    := ∀ x y : α, r x y -> r y x

  def Transitive : Prop
    := ∀ x y z : α, r x y ∧ r y z -> r x z

  def Equivalence : Prop
    := Reflexive r ∧ Symmetric r ∧ Transitive r

class Eq (α : Type u) where
  eq : Relation α
  eq_equivalent : Equivalence eq

class Functor (f : Type u -> Type u) where
  map : (a -> b) -> f a -> f b

--Add Structures

class AddMagma (α : Type u) where
  add : α -> α -> α

infixl:70 "+" => AddMagma.add

class AddIdent (α : Type u) [AddMagma α] where
  zero : α
  zero_ident : ∀a : α, zero + a = a ∧ a + zero = a

class AddCommutative (α : Type u) [AddMagma α] where
  commutative : ∀ a b : α, a + b = b + a

class AddAssociative (α : Type u) [AddMagma α] where
  add_associative :
    ∀ a b c : α, (a + b) + c = a + (b + c)

class AddInvertible (α : Type u) [AddMagma α] extends AddIdent α where
  inverses : ∀a : α, ∃b : α, a + b = zero ∧ b + a = zero

class AddSemigroup (α : Type u) extends AddMagma α, AddAssociative α where

class AddMonoid (α : Type u) extends AddSemigroup α, AddIdent α

class AddGroup (α : Type u) extends AddMonoid α, AddInvertible α

class AddAbelianGroup (α : Type u) extends AddGroup α, AddCommutative α

--Mul Structures /// USE MACRO

class MulMagma (α : Type u) where
  mul : α -> α -> α

infixl:80 "*" => MulMagma.mul

class MulIdent (α : Type u) [MulMagma α] where
  one : α
  one_ident : ∀a : α, one * a = a ∧ a * one = a

class MulCommutative (α : Type u) [MulMagma α] where
  commutative : ∀ a b : α, a * b = b * a

class MulAssociative (α : Type u) [MulMagma α] where
  mul_associative :
    ∀ a b c : α, (a * b) * c = a * (b * c)

class MulInvertible (α : Type u) [MulMagma α] extends MulIdent α where
  inverses : ∀a : α, ∃b : α, a * b = one

class MulSemigroup (α : Type u) extends MulMagma α, MulAssociative α where

class MulMonoid (α : Type u) extends MulSemigroup α, MulIdent α

class MulGroup (α : Type u) extends MulMonoid α, MulInvertible α

class MulAbelianGroup (α : Type u) extends MulGroup α, MulCommutative α

structure Pair (α : Type u) (β : Type u) where
  fst : α
  snd : β

theorem group_add_left_cancels [AddGroup α] (a : α) : a + b = a + c -> b = c := by
  intro h
  obtain ⟨a1, h_left, h_right⟩ := AddInvertible.inverses a
  calc
    b = AddIdent.zero + b := by rw [(AddIdent.zero_ident b).left]
    _ = (a1 + a) + b      := by rw [h_right]
    _ = a1 + (a + b)      := by rw [AddAssociative.add_associative]
    _ = a1 + (a + c)      := by rw [h]
    _ = (a1 + a) + c      := by rw [AddAssociative.add_associative]
    _ = AddIdent.zero + c := by rw [h_right]
    _ = c                 := by rw [(AddIdent.zero_ident c).left]

end Project
