import LeanProject.Nat
import LeanProject.Structures

namespace Project

class Collection (C : Type u -> Type u) where
  concat : C α -> C α -> C α
  get [Inhabited α] : C α -> N -> α
  singleton : α -> C α
  cons : α -> C α -> C α

inductive List (α : Type u) where
  | nil  : List α
  | cons : α -> List α -> List α

inductive NonEmptyList (α : Type u) where
  | singleton : α -> NonEmptyList α
  | cons      : α -> NonEmptyList α -> NonEmptyList α

def concat : List α -> List α -> List α
  | .cons a l1', l2 => .cons a (concat l1' l2)
  | .nil, l2        => l2

def singleton (a : α) := List.cons a List.nil

def get [Inhabited α] : (l : List α) -> (n : N) -> α
  | (List.cons a _), N.zero      => a
  | (List.cons _ l'), (N.succ n) => get l' n
  | List.nil, _                  => panic! "index out of bounds"

instance : Collection List where
  concat := concat
  get := get
  singleton := singleton
  cons := .cons

def concat_nonempty : NonEmptyList α -> NonEmptyList α -> NonEmptyList α
  | .cons a l1', l2 => .cons a (concat_nonempty l1' l2)
  | (.singleton a), l2        => .cons a l2

def get_nonempty [Inhabited α] : (l : NonEmptyList α) -> (n : N) -> α
  | (.cons a _), N.zero      => a
  | (.cons _ l'), (N.succ n) => get_nonempty l' n
  | .singleton n, N.zero => n
  | .singleton _, _ => panic! "index out of bounds"

instance : Collection NonEmptyList where
  concat := concat_nonempty
  get := get_nonempty
  singleton := .singleton
  cons := .cons

infixl:80 "!" => get
infixl:90 "++" => Collection.concat
infixr:100 ":" => List.cons
infixr:100 ":" => NonEmptyList.cons


def conc : List (List α) -> List α
  | .nil     => .nil
  | xs : xxs => xs ++ conc xxs

def foldr : (α -> β -> β) -> β -> List α -> β
| _, b, .nil     => b
| f, b, (a : as) =>  f a (foldr f b as)

def foldr_non_empty : (α -> β -> β) -> β -> NonEmptyList α -> β
| f, b, .singleton n => f n b
| f, b, (a : as) => f a (foldr_non_empty f b as)

def foldr_base_fst : (α -> β -> β) -> (α -> β) -> NonEmptyList α -> β
  | _, p, .singleton n => p n
  | f, p, (n : ns) => f n (foldr_base_fst f p ns)

def map (f : α -> β) : (List α -> List β) := foldr (λa bs => f a : bs) .nil
def concatMap (f : α -> List β) : List α -> List β := conc ∘ map f
def app : List (α -> β) -> List α -> List β
  | List.nil, _ => List.nil
  | f : fs, l => map f l ++ app fs l

def map_nonempty : (α -> β) -> (NonEmptyList α -> NonEmptyList β)
  | f, .singleton a => .singleton (f a)
  | f, a : as => f a : map_nonempty f as
def app_nonempty : NonEmptyList (α -> β) -> NonEmptyList α -> NonEmptyList β
  | .singleton f, as => map_nonempty f as
  | f : fs, as       => map_nonempty f as ++ app_nonempty fs as

instance : Applicative List where
  map := map
  app := app

instance : Applicative NonEmptyList where
  map := map_nonempty
  app := app_nonempty

theorem cons_cancels (n m : α) (l1 l2 : List α) : n : l1 = m : l2 -> n = m := by
  intro h
  injection h with h_right h_left


end Project
