import LeanProject.Structures
import LeanProject.List
import LeanProject.Ring
import LeanProject.Nat
import Lean

namespace Project

inductive Expr where
  | var (a : N)
  | op (e1 : Expr) (e2 : Expr)
deriving Inhabited, BEq

def Env (α : Type u) := List α

theorem cons_cancels (n m : α) (l1 l2 : List α) : n : l1 = m : l2 -> n = m := by
  intro h
  injection h with h_right h_left

def nat_convert : Nat -> N
| 0          => N.zero
| Nat.succ m => N.succ (nat_convert m)

variable {α : Type u} [Inhabited α] (op : α -> α -> α)
variable (assoc : ∀ a b c : α, op a (op b c) = op (op a b) c)
variable (comm : ∀ a b : α, op a b = op b a)

def eval : Env α -> Expr -> α
  | e, .var a    => e ! a
  | e, .op e1 e2 => op (eval e e1) (eval e e2)

def flatten : Expr -> List N
  | .var a    => singleton a
  | .op e1 e2 => flatten e1 ++ flatten e2

def unflatten : List N -> Expr
  | .nil     => .var .zero
  | n : .nil => .var n
  | n : ls   => .op (unflatten ls) (.var n)

def insert : N -> List N -> List N
  | n, .nil   => singleton n
  | n, x : ls => if n ≤ x then n : x : ls else x : insert n ls

def sort : List N -> List N := foldr insert .nil

theorem concat_not_nil {α : Type u} (l1 : List α) (l2 : List α) (h : l2 ≠ List.nil) : l1 ++ l2 ≠ .nil := by
  induction l1 with
  | nil => rw [concat]; exact h
  | cons x l ih =>
    rw [concat]
    intro h1
    contradiction

theorem flatten_not_nil (e : Expr) : flatten e ≠ .nil := by
  induction e with
  | var n            => dsimp [flatten, singleton]; intro h; contradiction
  | op e1 e2 ih1 ih2 =>
    dsimp [flatten]
    apply concat_not_nil
    exact ih2

include comm assoc in
theorem unflatten_splits (env : Env α) (l1 l2 : List N) (h1 : l1 ≠ .nil) (h2 : l2 ≠ .nil) :
    eval op env (unflatten (l1 ++ l2)) = eval op env (.op (unflatten l1) (unflatten l2)) := by
  induction l1 with
  | nil => nomatch h1
  | cons x l1' ih =>
    dsimp [concat]
    rw [unflatten]
    by_cases h_l1 : l1' = .nil
    rw [h_l1]
    rw [unflatten]
    rw [concat]
    dsimp [eval]
    rw [comm]
    have h : eval op env (unflatten (l1'++l2)) = eval op env ((unflatten l1').op (unflatten l2)) := ih h_l1
    dsimp [eval]
    rw [h]
    rw [unflatten]
    dsimp [eval]
    rw [comm]
    rw [assoc]
    rw [comm (env ! x)]
    exact h_l1
    apply concat_not_nil
    exact h2

include comm assoc in
theorem eval_unflatten_flatten (env : Env α) (e : Expr) :
    eval op env (unflatten (flatten e)) = eval op env e := by
  induction e with
  | var m =>
    dsimp [flatten, singleton, unflatten]
  | op e1 e2 ih1 ih2 =>
    dsimp [flatten]
    rw [unflatten_splits op assoc comm env (flatten e1) (flatten e2) (flatten_not_nil e1) (flatten_not_nil e2)]
    rw [eval, ih1, ih2, eval]

include comm assoc in
theorem eval_eq_of_flatten_eq (env : Env α) (e1 e2 : Expr)
    (h : flatten e1 = flatten e2) : eval op env e1 = eval op env e2 := by
  rw [← eval_unflatten_flatten op assoc comm env e1]
  rw [h]
  rw [eval_unflatten_flatten op assoc comm env e2]

theorem insert_not_nil (n : N) (l : List N)
    : insert n l ≠ .nil := by
  induction l with
  | nil =>
    rw [insert, singleton]
    intro h; contradiction
  | cons m l' =>
    rw [insert]
    by_cases h_leq : n≤m
    rw[ite_eq_left]
    intro h; contradiction
    exact h_leq
    rw [ite_eq_right]
    intro h
    contradiction
    exact h_leq

theorem sort_not_nil (l : List N) (h : l ≠ .nil) : sort l ≠ .nil := by
  induction l with
  | nil          => nomatch h
  | cons x l' ih =>
    rw [sort, foldr]
    apply insert_not_nil

include comm assoc in
theorem insert_preserves_equality (env : Env α) (l : List N) (n : N)
    : eval op env (unflatten (n : l)) = eval op env (unflatten (insert n l)) := by
  induction l with
  | nil          => dsimp [sort, foldr, insert, singleton]
  | cons m l' ih =>
    rw [insert]
    by_cases h_leq : n≤m
    rw [ite_eq_left]
    exact h_leq
    rw [ite_eq_right]
    dsimp [unflatten]
    rw [eval, eval]
    have h_nl' : insert n l' ≠ .nil := insert_not_nil n l'
    symm
    rw [unflatten]
    rw [eval, eval, ← ih]
    by_cases h_l' : l' = .nil
    rw [h_l']
    rw [unflatten, unflatten, eval, eval, comm]
    rw [unflatten, unflatten, eval, eval, eval, eval]
    rw [← assoc, comm (env ! n), assoc]
    exact h_l'
    exact h_l'
    exact h_nl'
    exact h_leq

include comm assoc in
theorem sort_preserves_equality (env : Env α) (l : List N)
    (h : l ≠ .nil) : eval op env (unflatten l) = eval op env (unflatten (sort l)) := by
  induction l with
  | nil       => nomatch h
  | cons x l' ih =>
    rw [sort, foldr]
    rw [← insert_preserves_equality]
    change eval op env (unflatten (x:l')) = eval op env (unflatten (x:sort l'))
    by_cases h_l' : l' = .nil
    rw [h_l', unflatten, sort, foldr, unflatten]
    have ih' : eval op env (unflatten l') = eval op env (unflatten (sort l')) := ih h_l'
    rw [unflatten, unflatten]
    dsimp [eval]
    rw [ih']
    apply sort_not_nil
    exact h_l'
    exact h_l'
    exact assoc
    exact comm

include comm assoc in
theorem eval_eq_sort (env : Env α) (e1 e2 : Expr) (h : sort (flatten e1) = sort (flatten e2))
    : eval op env e1 = eval op env e2 := by
  rw [← eval_unflatten_flatten op assoc comm]
  rw [sort_preserves_equality op assoc comm]
  rw [h]
  rw [← sort_preserves_equality op assoc comm]
  rw [eval_unflatten_flatten op assoc comm]
  apply flatten_not_nil
  apply flatten_not_nil

open Lean Meta Elab Tactic

end Project
