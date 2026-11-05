import LeanProject.Structures
import LeanProject.List
import LeanProject.Ring
import LeanProject.Nat
import Lean

namespace Project

inductive RExpr where
  | var (a : N)
  | add (e1 : RExpr) (e2 : RExpr)
  | mul (e1 : RExpr) (e2 : RExpr)
deriving Inhabited, BEq

def Env (α : Type u) := List α

def add_normal_form : RExpr -> NonEmptyList (NonEmptyList N)
| .var n => .singleton (.singleton n)
| .add e1 e2 => add_normal_form e1 ++ add_normal_form e2
| .mul e1 e2 => concat_nonempty <$> add_normal_form e1 <*> add_normal_form e2

def term_order : NonEmptyList N -> NonEmptyList N -> Bool
| .singleton n, m:_          => n≤m
| .singleton n, .singleton m => n≤m
| n:_, .singleton m          => not (m≤n)
| n:ns, m:ms                 => (n≤m) || (n==m && term_order ns ms)

instance (a b : NonEmptyList N) : Decidable (term_order a b) := inferInstance

def insert : NonEmptyList N -> NonEmptyList (NonEmptyList N) -> NonEmptyList (NonEmptyList N)
| ns, mms@(.singleton ms) => if term_order ns ms then ns : mms else ms : .singleton ns
| ns, ms : mms            => if term_order ns ms then ns : ms : mms else ms : insert ns mms

def sort : NonEmptyList (NonEmptyList N) -> NonEmptyList (NonEmptyList N) := foldr_base_fst insert .singleton
def canf := sort ∘ add_normal_form

def restore_term : NonEmptyList N -> RExpr := foldr_base_fst (λn e => RExpr.mul (RExpr.var n) e) RExpr.var
def restore : NonEmptyList (NonEmptyList N) -> RExpr := foldr_base_fst (λns e => RExpr.add (restore_term ns) e) restore_term

variable {α : Type u} [Rig α] [Inhabited α]

def eval : Env α -> RExpr -> α
  | e, .var a    => e ! a
  | e, .add e1 e2 => (eval e e1) + (eval e e2)
  | e, .mul e1 e2 => (eval e e1) * (eval e e2)

/- Deprecated work with normal lists
theorem insert_not_nil (ns : (List N)) (l : List (List N))
    : insert ns l ≠ .nil := by
  induction l with
  | nil =>
    rw [insert, singleton]
    intro h; contradiction
  | cons m l' =>
    rw [insert]
    by_cases h_leq : term_order ns m
    rw[ite_eq_left]
    intro h; contradiction
    exact h_leq
    rw [ite_eq_right]
    intro h
    contradiction
    exact h_leq

theorem sort_not_nil (l : List (List N)) (h : l ≠ .nil) : sort l ≠ .nil := by
  induction l with
  | nil          => nomatch h
  | cons x l' ih =>
    rw [sort, foldr]
    apply insert_not_nil

theorem concat_not_nil {α : Type u} (l1 : List α) (l2 : List α) (h : l2 ≠ List.nil) : l1 ++ l2 ≠ .nil := by
  induction l1 with
  | nil => rw [concat]; exact h
  | cons x l ih =>
    rw [concat]
    intro h1
    contradiction

theorem concat_not_nil_left {α : Type u} (l1 : List α) (l2 : List α) (h : l1 ≠ List.nil) : l1 ++ l2 ≠ .nil := by
  induction l1 with
  | nil => nomatch h
  | cons x l ih =>
    rw [concat]
    intro h1
    contradiction

theorem anf_not_nil (e : RExpr) : add_normal_form e ≠ .nil := by
  induction e with
  | var n             => dsimp [add_normal_form, singleton]; intro h; contradiction
  | add e1 e2 _ ih    => dsimp [add_normal_form]; apply concat_not_nil; apply ih
  | mul e1 e2 ih1 ih2 =>
    dsimp [add_normal_form]
    cases h : (add_normal_form e1) with
    | nil            => nomatch ih1 h
    | cons ns nns =>
      change ¬((map concat (ns:nns))<*>add_normal_form e2) = List.nil
      dsimp [map, foldr]
      change ¬(app (concat ns:(concat<$>nns)) (add_normal_form e2)) = List.nil
      dsimp [app]
      apply concat_not_nil_left
      cases h1 : (add_normal_form e2) with
      | nil => nomatch ih2 h1
      | cons ms mms => dsimp [map, foldr]; intro h; contradiction


theorem canf_not_nil (e : RExpr) : canf e ≠ .nil := by
  induction e with
  | var n            => dsimp [canf, singleton]; intro h; contradiction
  | add e1 e2 ih1 ih2 =>
    dsimp [canf, add_normal_form]
    apply sort_not_nil
    apply concat_not_nil
    apply anf_not_nil
  | mul e1 e2 ih1 ih2 =>
    dsimp [canf, add_normal_form]
    apply sort_not_nil
    cases h : (add_normal_form e1) with
    | nil =>
      have h' : add_normal_form e1 ≠ .nil := anf_not_nil e1
      nomatch h' h
    | cons ns nns =>
      change ¬((map concat (ns:nns))<*>add_normal_form e2) = List.nil
      dsimp [map, foldr]
      change ¬(app (concat ns:(concat<$>nns)) (add_normal_form e2)) = List.nil
      dsimp [app]
      apply concat_not_nil_left
      cases h1 : (add_normal_form e2) with
      | nil =>
        have h' : add_normal_form e2 ≠ .nil := anf_not_nil e2
        nomatch h' h1
      | cons ms mms => dsimp [map, foldr]; intro h; contradiction

include comm assoc in
theorem unflatten_splits (env : Env α) (l1 l2 : List N) (h1 : l1 ≠ .nil) (h2 : l2 ≠ .nil) :
    eval add env (unflatten (l1 ++ l2)) = eval add env (.add (unflatten l1) (unflatten l2)) := by
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
    have h : eval add env (unflatten (l1'++l2)) = eval add env ((unflatten l1').add (unflatten l2)) := ih h_l1
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
theorem eval_unflatten_flatten (env : Env α) (e : RExpr) :
    eval add env (unflatten (flatten e)) = eval add env e := by
  induction e with
  | var m =>
    dsimp [flatten, singleton, unflatten]
  | add e1 e2 ih1 ih2 =>
    dsimp [flatten]
    rw [unflatten_splits add assoc comm env (flatten e1) (flatten e2) (flatten_not_nil e1) (flatten_not_nil e2)]
    rw [eval, ih1, ih2, eval]

include comm assoc in
theorem eval_eq_of_flatten_eq (env : Env α) (e1 e2 : RExpr)
    (h : flatten e1 = flatten e2) : eval add env e1 = eval add env e2 := by
  rw [← eval_unflatten_flatten add assoc comm env e1]
  rw [h]
  rw [eval_unflatten_flatten add assoc comm env e2]

include comm assoc in
theorem insert_preserves_equality (env : Env α) (l : List N) (n : N)
    : eval add env (unflatten (n : l)) = eval add env (unflatten (insert n l)) := by
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
    (h : l ≠ .nil) : eval add env (unflatten l) = eval add env (unflatten (sort l)) := by
  induction l with
  | nil       => nomatch h
  | cons x l' ih =>
    rw [sort, foldr]
    rw [← insert_preserves_equality]
    change eval add env (unflatten (x:l')) = eval add env (unflatten (x:sort l'))
    by_cases h_l' : l' = .nil
    rw [h_l', unflatten, sort, foldr, unflatten]
    have ih' : eval add env (unflatten l') = eval add env (unflatten (sort l')) := ih h_l'
    rw [unflatten, unflatten]
    dsimp [eval]
    rw [ih']
    apply sort_not_nil
    exact h_l'
    exact h_l'
    exact assoc
    exact comm

include comm assoc in
theorem eval_eq_sort (env : Env α) (e1 e2 : RExpr) (h : sort (flatten e1) = sort (flatten e2))
    : eval add env e1 = eval add env e2 := by
  rw [← eval_unflatten_flatten add assoc comm]
  rw [sort_preserves_equality add assoc comm]
  rw [h]
  rw [← sort_preserves_equality add assoc comm]
  rw [eval_unflatten_flatten add assoc comm]
  apply flatten_not_nil
  apply flatten_not_nil

open Lean Meta Elab Tactic
-/

end Project
