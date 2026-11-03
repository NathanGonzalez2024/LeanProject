import LeanProject.Structures
import LeanProject.Ring

namespace Project

inductive N : Type
  | zero : N
  | succ : N -> N
  deriving BEq, Inhabited

def recurse : (N -> N) -> N -> N -> N -> N
| _, base, _, N.zero   => base
| f, base, m, N.succ n => f (recurse f base m n)

def add : N -> N -> N := λm => recurse (N.succ) m          m
def mul : N -> N -> N := λm => recurse (add m) N.zero      m
def exp : N -> N -> N := λm => recurse (mul m) N.zero.succ m

theorem succ_cancels (a b : N) : N.succ a = N.succ b -> a = b := by
  intro h
  injection h

theorem zero_add (a : N) : add N.zero a = a := by
  induction a with
  | zero      =>
    dsimp [add]
    dsimp [recurse]
  | succ n ih =>
    dsimp [add]
    dsimp [recurse]
    dsimp [add] at ih
    rw [ih]

theorem add_zero (a : N) : add a N.zero = a := by
  dsimp [add]
  dsimp [recurse]

theorem succ_add (a b : N) : add (N.succ a) b = N.succ (add a b) := by
  induction b with
  | zero =>
    dsimp [add]
    dsimp [recurse]
  | succ n ih =>
    dsimp [add]
    dsimp [add] at ih
    dsimp [recurse]
    rw [ih]

theorem add_right_cancels (a b c : N) : add a c = add b c -> a = b := by
  induction c with
  | zero =>
    dsimp [add]
    intro h; exact h
  | succ n ih =>
    dsimp [add]
    intro h
    have h_now : add a n = add b n := by
      apply succ_cancels
      exact h
    rw [ih]
    exact h_now

instance : AddMonoid N where
  add := add
  add_associative a b c := by
    induction c with
    | zero      =>
      dsimp [add]
      dsimp [recurse]
    | succ n ih =>
      dsimp [add]
      dsimp [recurse]
      dsimp [add] at ih
      rw [ih]
  zero := N.zero
  zero_ident a := by
    constructor
    · apply zero_add
    · dsimp [add, recurse]


instance : AddCommutative N where
  commutative a b := by
    dsimp [AddMagma.add]
    induction b with
    | zero      =>
      dsimp [add, recurse]
      rw [← add]
      rw [zero_add a]
    | succ n ih =>
      dsimp [add, recurse]
      rw [← add, ← add]
      rw [succ_add]
      rw [ih]

theorem add_mul_left_distribute (a b c : N) : mul a (add b c) = add (mul a b) (mul a c) := by
  dsimp [mul, add, recurse]
  induction c with
  | zero       => dsimp [recurse]
  | succ c' ih =>
    dsimp [recurse]
    rw [ih]
    rw [← add, ← add, ← mul]
    change a + (mul a b + mul a c') = mul a b + (a + mul a c')
    rw [← AddAssociative.add_associative]
    rw [AddCommutative.commutative a]
    rw [AddAssociative.add_associative]

instance : MulMonoid N where
  one := N.zero.succ
  mul := mul

  one_ident a := by
    dsimp [mul, add, recurse]
    induction a with
    | zero =>
      dsimp [recurse]
      constructor
      · rfl
      · rfl
    | succ n ih =>
      dsimp [recurse]
      constructor
      {
        rw [ih.left]
        rw [← add]
        change N.zero.succ + n = n.succ
        rw [AddCommutative.commutative]
        change add n N.zero.succ = n.succ
        rw [add]
        dsimp [recurse]
      }
      · rfl

  mul_associative a b c := by
    dsimp [mul, add, recurse]
    induction c with
    | zero =>
      dsimp [recurse]
    | succ c' ih =>
      dsimp [recurse]
      rw [ih]
      rw [← add, ← add, ← add, ← mul, ← mul]
      rw [← add, ← add, ← add, ← mul, ← mul, ← mul] at ih
      rw [add_mul_left_distribute]

theorem mul_add_left (a b : N) : add a (mul b a) = mul b.succ a := by
  induction a with
  | zero =>
    dsimp [add, mul, recurse]
  | succ a' ih =>
    dsimp [add, mul, recurse]
    rw [← add, ← add, ← add, ← mul, ← mul]
    rw [← ih]
    change a'.succ + (b + mul b a') = b.succ + (a' + mul b a')
    rw [← AddAssociative.add_associative]
    rw [AddCommutative.commutative a'.succ]
    rw [← AddAssociative.add_associative]
    rw [AddCommutative.commutative b.succ]
    change (add b a'.succ) + mul b a' = (add a' b.succ) + mul b a'
    dsimp [add, mul, recurse]
    rw [← add, ← add, ← mul]
    change (b + a').succ + mul b a' = (a' + b).succ + mul b a'
    rw [AddCommutative.commutative b]

theorem mul_mult_zero_right (a : N) : mul a N.zero = N.zero := by
  dsimp [mul, recurse]

theorem mul_mult_zero_left (a : N) : mul a N.zero = N.zero := by
  dsimp [mul, recurse]

instance : MulCommutative N where
  commutative a b := by
    change mul a b = mul b a
    induction b with
    | zero =>
      dsimp [mul, recurse]
      induction a with
      | zero => dsimp [recurse]
      | succ a' ih =>
        dsimp [recurse]
        rw [← ih]
        dsimp [add, recurse]
    | succ b' ih =>
      dsimp [mul, add, recurse]
      rw [mul, mul, add, add] at ih
      rw [ih]
      rw [← add, ← add, ← mul, ← mul] at ih
      rw [← add, ← add, ← add, ← mul, ← mul]
      apply mul_add_left

instance : Semiring N where
  left_distrib := add_mul_left_distribute
  right_distrib a b c := by
    rw [MulCommutative.commutative, MulCommutative.commutative a, MulCommutative.commutative b]
    apply add_mul_left_distribute
  zero_absorbs a := by
    constructor
    {
      change mul a N.zero = N.zero
      dsimp [mul, recurse]
    }
    {
      change mul N.zero a = N.zero
      dsimp [mul, recurse]
      induction a with
      | zero => dsimp [recurse]
      | succ a' ih =>
        dsimp [add, recurse]
        dsimp [add, recurse] at ih
        rw [ih]
        dsimp [recurse]
    }

def leq_n : Relation N
  | .zero,         _ => True
  | _, .zero         => False
  | .succ n, .succ m => leq_n n m

infixl:20 "≤" => leq_n

instance leq_n_decidable : (n m : N) -> Decidable (n ≤ m)
  | .zero, _         => isTrue True.intro
  | .succ _, .zero   => isFalse (fun h => h)
  | .succ n, .succ m =>
    match leq_n_decidable n m with
    | isTrue h  => isTrue h
    | isFalse h => isFalse h

def Sequence {α : Type} := N -> α

end Project
