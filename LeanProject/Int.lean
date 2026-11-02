import LeanProject.Structures
import LeanProject.Nat

namespace Project

def intEquivalence : Relation (Pair N N)
| p1, p2 => p1.fst + p2.snd = p2.fst + p1.snd

theorem intEquivalence_reflexive : Reflexive intEquivalence := by
  intro x
  rw [intEquivalence]

theorem intEquivalence_symmetric : Symmetric intEquivalence := by
  intro x y
  rw [intEquivalence]
  rw [intEquivalence]
  intro h
  exact h.symm

theorem intEquivalence_transitive : Transitive intEquivalence := by
  rw [Transitive]
  intro x y z
  rw [intEquivalence]
  rw [intEquivalence]
  rw [intEquivalence]
  intro h
  have h_combined : ((x.fst + z.snd) + y.snd) + y.fst = ((x.snd + z.fst) + y.snd) + y.fst := by
    calc
      ((x.fst + z.snd) + y.snd) + y.fst = (x.fst + (z.snd + y.snd)) + y.fst := by rw [AddAssociative.add_associative x.fst]
      _                                 = (x.fst + (y.snd + z.snd)) + y.fst := by rw [AddCommutative.commutative z.snd]
      _                                 = ((x.fst + y.snd) + z.snd) + y.fst := by rw [← AddAssociative.add_associative x.fst]
      _                                 = (x.fst + y.snd) + (z.snd + y.fst) := by rw [AddAssociative.add_associative]
      _                                 = (x.fst + y.snd) + (y.fst + z.snd) := by rw [AddCommutative.commutative z.snd]
      _                                 = (y.fst + x.snd) + (y.fst + z.snd) := by rw [h.left]
      _                                 = (y.fst + x.snd) + (z.fst + y.snd) := by rw [h.right]
      _                                 = (x.snd + y.fst) + (z.fst + y.snd) := by rw [AddCommutative.commutative y.fst]
      _                                 = x.snd + (y.fst + (z.fst + y.snd)) := by rw [AddAssociative.add_associative]
      _                                 = x.snd + ((y.fst + z.fst) + y.snd) := by rw [AddAssociative.add_associative y.fst]
      _                                 = x.snd + ((z.fst + y.fst) + y.snd) := by rw [AddCommutative.commutative y.fst]
      _                                 = x.snd + (z.fst + (y.fst + y.snd)) := by rw [AddAssociative.add_associative z.fst]
      _                                 = x.snd + (z.fst + (y.snd + y.fst)) := by rw [AddCommutative.commutative y.fst]
      _                                 = ((x.snd + z.fst) + y.snd) + y.fst := by rw [AddAssociative.add_associative, AddAssociative.add_associative]

  replace h_combined := add_right_cancels _ _ _ h_combined
  replace h_combined := add_right_cancels _ _ _ h_combined
  rw [AddCommutative.commutative x.snd] at h_combined
  exact h_combined

theorem intEquivalence_equivalence : Equivalence intEquivalence := by
  rw [Equivalence]
  exact ⟨intEquivalence_reflexive, intEquivalence_symmetric, intEquivalence_transitive⟩

def Z := Quot intEquivalence

theorem int_add_well_defined :∀a b c : Pair N N, intEquivalence b c
  -> Quot.mk intEquivalence { fst := a.fst+b.fst, snd := a.snd+b.snd } = Quot.mk intEquivalence { fst := a.fst+c.fst, snd := a.snd+c.snd } := by
    intro a b c h
    dsimp [intEquivalence] at h
    apply Quot.sound
    dsimp [intEquivalence]
    rw [AddAssociative.add_associative]
    rw [AddCommutative.commutative a.snd]
    rw [← AddAssociative.add_associative b.fst]
    rw [h]
    rw [AddAssociative.add_associative]
    rw [AddAssociative.add_associative]
    rw [AddCommutative.commutative b.snd]

instance : AddAbelianGroup Z where
  zero := Quot.mk intEquivalence {fst := N.zero, snd := N.zero}

  add := Quot.lift (λa =>
    Quot.lift (λb =>
      Quot.mk intEquivalence {fst := a.fst + b.fst, snd := a.snd + b.snd}
    ) (by
      intro b c h
      apply int_add_well_defined
      exact h
    )
  ) (by
    intro a b h
    funext x
    induction x using Quot.ind
    case mk x =>
      dsimp
      rw [AddCommutative.commutative a.fst, AddCommutative.commutative a.snd]
      rw [AddCommutative.commutative b.fst, AddCommutative.commutative b.snd]
      apply int_add_well_defined
      exact h
  )

  zero_ident a := by
    constructor
    {
      dsimp
      induction a using Quot.ind with | mk a =>
      dsimp
      rw [AddCommutative.commutative]
      rw [← AddCommutative.commutative a.snd]
      change Quot.mk intEquivalence { fst := add a.fst N.zero, snd := add a.snd N.zero } = Quot.mk intEquivalence a
      dsimp [add, recurse]
    }
    {
      induction a using Quot.ind with | mk a =>
      dsimp
      have h_fst : a.fst + N.zero = a.fst := (AddIdent.zero_ident a.fst).right
      have h_snd : a.snd + N.zero = a.snd := (AddIdent.zero_ident a.snd).right
      rw [h_fst]
      rw [h_snd]
    }

  add_associative a b c := by
    induction c using Quot.ind with | mk c =>
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    rw [AddAssociative.add_associative]
    rw [AddAssociative.add_associative a.snd]

  inverses a := by
    induction a using Quot.ind with | mk a =>
    refine ⟨Quot.mk intEquivalence {fst := a.snd, snd := a.fst}, ?_⟩
    dsimp
    constructor
    ·
      apply Quot.sound
      rw [intEquivalence]
      dsimp
      rw [AddCommutative.commutative a.snd]
      rw [AddCommutative.commutative N.zero]
    ·
      apply Quot.sound
      rw [intEquivalence]
      dsimp
      rw [AddCommutative.commutative a.snd]
      rw [AddCommutative.commutative N.zero]

  commutative a b := by
    induction a using Quot.ind with | mk a =>
    induction b using Quot.ind with | mk b =>
    dsimp
    rw [AddCommutative.commutative]
    rw [AddCommutative.commutative b.snd]

theorem int_mul_well_defined :∀a b c : Pair N N, intEquivalence b c
  -> Quot.mk intEquivalence { fst := a.fst * b.fst + a.snd * b.snd, snd := a.fst * b.snd + a.snd * b.fst }
   = Quot.mk intEquivalence { fst := a.fst * c.fst + a.snd * c.snd, snd := a.fst * c.snd + a.snd * c.fst } := by
    intro a b c h
    dsimp [intEquivalence] at h
    apply Quot.sound
    dsimp [intEquivalence]
    rw [AddAssociative.add_associative]
    rw [← AddAssociative.add_associative (a.snd*b.snd)]
    rw [AddCommutative.commutative (a.snd*b.snd)]
    rw [AddAssociative.add_associative (a.fst*c.snd)]
    rw [← AddAssociative.add_associative]
    change add (mul a.fst b.fst) (mul a.fst c.snd) + add (mul a.snd b.snd) (mul a.snd c.fst) = _
    rw [← add_mul_left_distribute]
    rw [← add_mul_left_distribute]
    change a.fst * (b.fst + c.snd) + a.snd * (b.snd + c.fst) = _
    rw [AddCommutative.commutative b.snd]
    rw [h]
    rw [MulCommutative.commutative, MulCommutative.commutative a.snd]
    rw [← Rig.left_distrib]
    rw [AddAssociative.add_associative (a.fst*c.fst)]
    rw [AddCommutative.commutative (a.snd*c.snd)]
    rw [← AddAssociative.add_associative (a.fst*c.fst)]
    rw [← AddAssociative.add_associative (a.fst*c.fst)]
    rw [AddAssociative.add_associative (a.fst*c.fst+a.fst*b.snd)]
    rw [← Rig.left_distrib a.fst]
    rw [← Rig.left_distrib a.snd]
    rw [AddCommutative.commutative b.fst]
    rw [← h]
    rw [AddCommutative.commutative c.snd]
    rw [← Rig.right_distrib a.fst]
    rw [MulCommutative.commutative (a.fst+a.snd)]

instance : MulMonoid Z where
  mul := Quot.lift (λa : Pair N N =>
    Quot.lift (λb : Pair N N =>
      Quot.mk intEquivalence {fst := a.fst * b.fst + a.snd * b.snd, snd := a.fst * b.snd + a.snd * b.fst}
    ) (by
      intro a b h
      apply int_mul_well_defined
      exact h
    )
  ) (by
    intro a b h
    funext x
    induction x using Quot.ind with | mk x =>
    dsimp
    rw [MulCommutative.commutative a.fst]
    rw [MulCommutative.commutative a.snd]
    rw [MulCommutative.commutative a.fst]
    rw [MulCommutative.commutative a.snd]
    rw [MulCommutative.commutative b.fst]
    rw [MulCommutative.commutative b.snd]
    rw [MulCommutative.commutative b.fst]
    rw [MulCommutative.commutative b.snd]
    rw [AddCommutative.commutative (x.snd*a.fst)]
    rw [AddCommutative.commutative (x.snd*b.fst)]
    apply int_mul_well_defined
    exact h
  )

  mul_associative a b c:= by
    induction c using Quot.ind with | mk c =>
    induction b using Quot.ind with | mk b =>
    induction a using Quot.ind with | mk a =>
    dsimp
    have h (c1 c2 : N): (a.fst*b.fst+a.snd*b.snd)*c1+(a.fst*b.snd+a.snd*b.fst)*c2 = a.fst*(b.fst*c1+b.snd*c2)+a.snd*(b.fst*c2+b.snd*c1) := by
      calc
        (a.fst*b.fst+a.snd*b.snd)*c1+(a.fst*b.snd+a.snd*b.fst)*c2
          = (((a.fst*b.fst)*c1)+((a.snd*b.snd)*c1))+(a.fst*b.snd+a.snd*b.fst)*c2         := by rw[Rig.right_distrib]
        _ = (a.fst*b.fst)*c1+(((a.snd*b.snd)*c1)+(a.fst*b.snd+a.snd*b.fst)*c2)           := by rw[AddAssociative.add_associative]
        _ = (a.fst*b.fst)*c1+((a.fst*b.snd+a.snd*b.fst)*c2+((a.snd*b.snd)*c1))           := by rw[AddCommutative.commutative ((a.snd*b.snd)*c1)]
        _ = (a.fst*b.fst)*c1+(((a.fst*b.snd)*c2+(a.snd*b.fst)*c2)+((a.snd*b.snd)*c1)) := by rw[Rig.right_distrib]
        _ = ((a.fst*b.fst)*c1+((a.fst*b.snd)*c2+(a.snd*b.fst)*c2))+((a.snd*b.snd)*c1) := by rw[AddAssociative.add_associative ((a.fst*b.fst)*c1)]
        _ = (((a.fst*b.fst)*c1+(a.fst*b.snd)*c2)+(a.snd*b.fst)*c2)+((a.snd*b.snd)*c1) := by rw[← AddAssociative.add_associative ((a.fst*b.fst)*c1)]
        _ = ((a.fst*(b.fst*c1)+a.fst*(b.snd*c2))+(a.snd*b.fst)*c2)+((a.snd*b.snd)*c1) := by rw[← MulAssociative.mul_associative a.fst, ← MulAssociative.mul_associative a.fst]
        _ = ((a.fst*(b.fst*c1+b.snd*c2))+(a.snd*b.fst)*c2)+((a.snd*b.snd)*c1)         := by rw[← Rig.left_distrib]
        _ = (a.fst*(b.fst*c1+b.snd*c2))+((a.snd*b.fst)*c2+((a.snd*b.snd)*c1))         := by rw[AddAssociative.add_associative]
        _ = (a.fst*(b.fst*c1+b.snd*c2))+(a.snd*(b.fst*c2)+(a.snd*(b.snd*c1)))         := by rw[← MulAssociative.mul_associative a.snd, ← MulAssociative.mul_associative a.snd]
        _ = (a.fst*(b.fst*c1+b.snd*c2))+(a.snd*(b.fst*c2+b.snd*c1))                   := by rw[← Rig.left_distrib]
    rw [h]
    rw [h]

  one := Quot.mk intEquivalence { fst := N.zero.succ, snd := N.zero }

  one_ident a := by
    induction a using Quot.ind with | mk a =>
    dsimp
    change
      Quot.mk intEquivalence { fst := N.zero.succ*a.fst+AddIdent.zero*a.snd, snd := N.zero.succ*a.snd+AddIdent.zero*a.fst } =
      Quot.mk intEquivalence a ∧
      Quot.mk intEquivalence { fst := a.fst*N.zero.succ+a.snd*AddIdent.zero, snd := a.fst*AddIdent.zero+a.snd*N.zero.succ } =
      Quot.mk intEquivalence a
    rw [(Semiring.zero_absorbs _).right]
    rw [(Semiring.zero_absorbs _).right]
    rw [(Semiring.zero_absorbs _).left]
    rw [(Semiring.zero_absorbs _).left]
    rw [(AddIdent.zero_ident _).left]
    rw [(AddIdent.zero_ident _).right]
    rw [(AddIdent.zero_ident _).right]
    rw [(AddIdent.zero_ident _).right]
    rw [MulCommutative.commutative]
    rw [MulCommutative.commutative N.zero.succ]
    rw [p_and_p]
    apply Quot.sound
    rw [intEquivalence]
    dsimp
    change mul a.fst N.zero.succ+a.snd = a.fst+mul a.snd N.zero.succ
    dsimp [mul, add, recurse]

instance : MulCommutative Z where
  commutative a b := by
    induction a using Quot.ind with | mk a =>
    induction b using Quot.ind with | mk b =>
    dsimp [MulMagma.mul]
    change
    Quot.mk intEquivalence
      { fst := a.fst * b.fst + a.snd * b.snd, snd := a.fst * b.snd + a.snd * b.fst }
    = Quot.mk intEquivalence
      { fst := b.fst * a.fst + b.snd * a.snd, snd := b.fst * a.snd + b.snd * a.fst }
    rw [MulCommutative.commutative]
    rw [MulCommutative.commutative a.snd]
    rw [MulCommutative.commutative a.fst]
    rw [MulCommutative.commutative a.snd]
    rw [AddCommutative.commutative (b.fst*a.snd)]


theorem int_left_distrib (a b c : Z) : a*(b+c) = a*b + a*c := by
    induction a using Quot.ind with | mk a =>
    induction b using Quot.ind with | mk b =>
    induction c using Quot.ind with | mk c =>
    dsimp [AddMagma.add, MulMagma.mul]
    change
      Quot.mk intEquivalence
        { fst := (a.fst * (b.fst + c.fst)) + (a.snd * (b.snd + c.snd)), snd := (a.fst * (b.snd + c.snd)) + (a.snd * (b.fst + c.fst)) }
      = Quot.mk intEquivalence
        { fst := ((a.fst * b.fst) + (a.snd * b.snd)) + ((a.fst * c.fst) + (a.snd * c.snd)), snd := ((a.fst * b.snd) + (a.snd * b.fst)) + ((a.fst * c.snd) + (a.snd * c.fst)) }
    rw [Rig.left_distrib]
    rw [Rig.left_distrib]
    rw [Rig.left_distrib]
    rw [Rig.left_distrib]
    rw [AddAssociative.add_associative]
    rw [AddAssociative.add_associative]
    rw [← AddAssociative.add_associative (a.fst*c.fst)]
    rw [← AddAssociative.add_associative (a.fst*c.snd)]
    rw [AddCommutative.commutative (a.fst*c.fst)]
    rw [AddCommutative.commutative (a.fst*c.snd)]
    rw [← AddAssociative.add_associative]
    rw [← AddAssociative.add_associative]
    rw [← AddAssociative.add_associative]
    rw [← AddAssociative.add_associative]
    rw [AddAssociative.add_associative (a.fst*b.fst+a.snd*b.snd)]
    rw [AddAssociative.add_associative (a.fst*b.snd+a.snd*b.fst)]

theorem int_right_distrib (a b c : Z) : (a+b)*c = a*c + b*c := by
  rw [MulCommutative.commutative]
  rw [int_left_distrib]
  rw [MulCommutative.commutative]
  rw [MulCommutative.commutative c]

instance : Ring Z where
  left_distrib := int_left_distrib
  right_distrib := int_right_distrib
  zero_absorbs a := by
    constructor
    ·
      obtain ⟨a0i, h_left, h_right⟩ := AddInvertible.inverses (a*AddIdent.zero)
      have h1 :
        a*AddIdent.zero = a*AddIdent.zero + a*AddIdent.zero := by rw [← int_left_distrib, (AddIdent.zero_ident _).left]
      symm
      calc
        AddIdent.zero = a*(AddIdent.zero:Z)+a0i := by rw [h_left]
        _             = (a*AddIdent.zero+a*AddIdent.zero)+a0i := by rw [← h1]
        _             = a*AddIdent.zero+(a*AddIdent.zero+a0i) := by rw [AddAssociative.add_associative]
        _             = a*AddIdent.zero+AddIdent.zero := by rw [h_left]
        _             = a*AddIdent.zero := by rw [(AddIdent.zero_ident _).right]
    ·
      obtain ⟨a0i, h_left, h_right⟩ := AddInvertible.inverses (AddIdent.zero*a)
      have h1 :
        AddIdent.zero*a = AddIdent.zero*a + AddIdent.zero*a := by rw [← int_right_distrib, (AddIdent.zero_ident _).left]
      symm
      calc
        AddIdent.zero = (AddIdent.zero:Z)*a+a0i := by rw [h_left]
        _             = (AddIdent.zero*a+AddIdent.zero*a)+a0i := by rw [← h1]
        _             = AddIdent.zero*a+(AddIdent.zero*a+a0i) := by rw [AddAssociative.add_associative]
        _             = AddIdent.zero*a+AddIdent.zero := by rw [h_left]
        _             = AddIdent.zero*a := by rw [(AddIdent.zero_ident _).right]









end Project
