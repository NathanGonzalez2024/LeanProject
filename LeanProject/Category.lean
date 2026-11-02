import LeanProject.Nat

namespace Project

def Set (α : Type u) := α → Prop

structure SetMorphism { α β : Type } (A : Set α) (B : Set β) where
  f         : α -> β
  restricts : ∀ a : α, B (f a)

structure Category where
  O    : Set N
  A    : Set N
  dom  : SetMorphism A O
  cod  : SetMorphism A O

end Project
