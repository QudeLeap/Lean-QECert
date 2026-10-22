import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Frobenius of a prime-field algebra

Construct the actual p-power endomorphism even when the algebra is trivial.
Finite-type prime-field algebras have finite Frobenius: integrality follows
from X^p-C(x), and the Frobenius composite with the base map is the base map.
This is internal ring theory for genuine arithmetic scheme fibres.
-/

namespace QEC.Coding.AlgebraicGeometry.PrimeFrobenius
noncomputable section
variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra (ZMod p) R]

private lemma power_add (x y : R) : (x + y)^p = x^p + y^p := by
  classical
  rcases subsingleton_or_nontrivial R with h | h
  · have := h
    exact Subsingleton.elim _ _
  · have := h
    let : CharP R p :=
      charP_of_injective_ringHom (algebraMap (ZMod p) R).injective p
    simpa only [frobenius_def] using (frobenius R p).map_add x y

def primeAlgebraFrobenius : R →+* R where
  toFun x := x^p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' := power_add p R

lemma primeAlgebraFrobenius_constant (a : ZMod p) :
    primeAlgebraFrobenius p R (algebraMap (ZMod p) R a) = algebraMap (ZMod p) R a := by
  change (algebraMap (ZMod p) R a)^p = algebraMap (ZMod p) R a
  rw [← map_pow, ZMod.pow_card]

lemma primeAlgebraFrobenius_comp_base :
    (primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R) = algebraMap (ZMod p) R := by
  ext a
  exact primeAlgebraFrobenius_constant p R a

lemma primeAlgebraFrobenius_integral : (primeAlgebraFrobenius p R).IsIntegral := by
  intro x
  refine ⟨Polynomial.X^p - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x (Fact.out : p.Prime).ne_zero, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  change x^p - x^p = 0
  exact sub_self _

lemma primeAlgebraFrobenius_finite [Algebra.FiniteType (ZMod p) R] :
    (primeAlgebraFrobenius p R).Finite := by
  have hb : (algebraMap (ZMod p) R).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hc : ((primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R)).FiniteType := by
    rw [primeAlgebraFrobenius_comp_base]
    exact hb
  exact RingHom.finite_iff_isIntegral_and_finiteType.mpr
    ⟨primeAlgebraFrobenius_integral p R, RingHom.FiniteType.of_comp_finiteType hc⟩

end
end QEC.Coding.AlgebraicGeometry.PrimeFrobenius
