import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End

/-!
# The Cartwright--Steger integral skew Laurent ring

After the substitution `1 + y = z^d`, the integral cyclic order at the
building place is the skew Laurent ring
`F_(q^d){z, z⁻¹}`, with relation `z c = Frobenius(c) z`.  This module
constructs that noncommutative ring from the arithmetic Frobenius action.
It does not replace the skew multiplication by an ordinary commutative
Laurent-polynomial multiplication.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Integer powers of Frobenius as ring automorphisms of the constant
extension. -/
noncomputable def constantFrobeniusZRingAction
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →* RingAut (ConstantExtension P r) :=
  zpowersHom _ (constantFrobenius P r).toRingEquiv

/-- The coefficient action used by the skew Laurent multiplication. -/
noncomputable instance constantFrobeniusZSMul
    (P : BasePrime) (r : Rank) :
    SMul (Multiplicative ℤ) (ConstantExtension P r) :=
  ⟨fun n c => constantFrobeniusZRingAction P r n c⟩

/-- Frobenius powers act by semiring automorphisms, so the skew convolution
is an associative ring multiplication. -/
noncomputable instance constantFrobeniusZMulSemiringAction
    (P : BasePrime) (r : Rank) :
    MulSemiringAction (Multiplicative ℤ) (ConstantExtension P r) where
  one_smul c := by
    change constantFrobeniusZRingAction P r 1 c = c
    rw [map_one]
    rfl
  mul_smul n m c := by
    change constantFrobeniusZRingAction P r (n * m) c =
      constantFrobeniusZRingAction P r n
        (constantFrobeniusZRingAction P r m c)
    rw [map_mul]
    rfl
  smul_zero n := map_zero (constantFrobeniusZRingAction P r n)
  smul_add n := map_add (constantFrobeniusZRingAction P r n)
  smul_one n := map_one (constantFrobeniusZRingAction P r n)
  smul_mul n := map_mul (constantFrobeniusZRingAction P r n)

/-- The actual skew Laurent coefficient ring
`F_(q^d){z, z⁻¹}` from LSV05b Proposition 4.8. -/
abbrev CartwrightStegerSkewLaurentRing
    (P : BasePrime) (r : Rank) :=
  SkewMonoidAlgebra (ConstantExtension P r) (Multiplicative ℤ)

/-- The degree-one action is exactly arithmetic Frobenius. -/
theorem one_action_eq_frobenius
    (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    Multiplicative.ofAdd (1 : ℤ) • c = constantFrobenius P r c := by
  change constantFrobeniusZRingAction P r (Multiplicative.ofAdd 1) c = _
  rw [constantFrobeniusZRingAction, zpowersHom_apply]
  simp

/-- Every nonzero constant times an integral power of `z` is an actual unit
of the skew Laurent ring.  Its inverse includes the required inverse
Frobenius twist. -/
noncomputable def skewLaurentMonomialUnit
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    (CartwrightStegerSkewLaurentRing P r)ˣ where
  val := SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
    (c : ConstantExtension P r)
  inv := SkewMonoidAlgebra.single (Multiplicative.ofAdd (-n))
    (Multiplicative.ofAdd (-n) •
      (c⁻¹ : ConstantExtension P r))
  val_inv := by
    rw [SkewMonoidAlgebra.single_mul_single]
    simp
  inv_val := by
    rw [SkewMonoidAlgebra.single_mul_single]
    rw [← smul_mul']
    simp

@[simp] theorem skewLaurentMonomialUnit_val
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    (skewLaurentMonomialUnit P r c n :
      CartwrightStegerSkewLaurentRing P r) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
        (c : ConstantExtension P r) := rfl

/-- The defining skew relation `z c = Frobenius(c) z`, proved from the
constructed multiplication and action. -/
theorem skewLaurent_z_mul_constant
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 *
        SkewMonoidAlgebra.single 1 c =
      SkewMonoidAlgebra.single 1 (constantFrobenius P r c) *
        SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 := by
  rw [SkewMonoidAlgebra.single_mul_single,
    SkewMonoidAlgebra.single_mul_single]
  simp [one_action_eq_frobenius]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
