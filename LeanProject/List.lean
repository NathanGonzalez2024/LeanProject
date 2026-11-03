import LeanProject.Nat
import LeanProject.Structures

namespace Project

inductive List (α : Type u) where
  | nil  : List α
  | cons : α -> List α -> List α

def singleton (a : α) := List.cons a List.nil

def get [Inhabited α] : (l : List α) -> (n : N) -> α
  | (List.cons a _), N.zero      => a
  | (List.cons _ l'), (N.succ n) => get l' n
  | List.nil, _                  => panic! "index out of bounds"

def concat : List α -> List α -> List α
  | .cons a l1', l2 => .cons a (concat l1' l2)
  | .nil, l2        => l2

infixl:80 "!" => get
infixl:90 "++" => concat
infixr:100 ":" => List.cons

def foldr : (α -> β -> β) -> β -> List α -> β
| _, b, .nil     => b
| f, b, (a : as) =>  f a (foldr f b as)

def map (f : α -> β) : (List α -> List β) := foldr (λa bs => f a : bs) .nil

instance : Functor List where
  map := map


end Project
