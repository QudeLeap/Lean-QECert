import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Basic
import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace
import QEC.Coding.AlgebraicGeometry.Places.InverseAffinePlace

namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport

open scoped LaurentPolynomial Polynomial RatFunc WithZero

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

/-- The actual X-adic global place of the rational base field. -/
noncomputable def xAdicPlace (k : Type*) [Field k] [Finite k] :
    GlobalPlace k (RatFunc k) where
  valuation := (Polynomial.idealX k).valuation (RatFunc k)
  normalized := (Polynomial.idealX k).valuation_surjective (RatFunc k)

/-- The direct Laurent realization of the rational coordinate. -/
noncomputable def directLaurentToRatFunc (k : Type*) [Field k] :
    LaurentPolynomial k →+* RatFunc k :=
  LaurentPolynomial.eval₂ (algebraMap k (RatFunc k))
    (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

/-- Inverting the Laurent variable after the ordinary polynomial inclusion. -/
noncomputable def inverseLaurentCoordinate (k : Type*) [Field k] :
    k[X] →ₐ[k] LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toAlgHom.comp Polynomial.toLaurentAlg

/-- The polynomial restriction of the concrete rational involution. -/
noncomputable def rationalInvolutionOnPolynomial (k : Type*) [Field k] [Finite k] :
    k[X] →+* RatFunc k :=
  (InverseAffinePlace.rationalInvolution k).toRingHom.comp
    (algebraMap k[X] (RatFunc k))

/-- Laurent evaluation after inversion is exactly the polynomial restriction
of the constructed rational involution. -/
private theorem inverseLaurent_eval_eq_involution (p : k[X]) :
    directLaurentToRatFunc k (inverseLaurentCoordinate k p) =
      InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) p) := by
  change ((directLaurentToRatFunc k).comp
    (inverseLaurentCoordinate k).toRingHom) p =
      rationalInvolutionOnPolynomial k p
  have hhom : (directLaurentToRatFunc k).comp
      (inverseLaurentCoordinate k).toRingHom =
      rationalInvolutionOnPolynomial k := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [directLaurentToRatFunc, inverseLaurentCoordinate,
        rationalInvolutionOnPolynomial,
        show RatFunc.C c = algebraMap k (RatFunc k) c from rfl,
        (InverseAffinePlace.rationalInvolution k).commutes c]
    · simpa [directLaurentToRatFunc, inverseLaurentCoordinate,
        rationalInvolutionOnPolynomial] using
        (InverseAffinePlace.rationalInvolution_X k).symm
  exact DFunLike.congr_fun hhom p

/-- The Laurent reciprocal-polynomial identity specializes to an exact
rational-function formula.  The `X ^ natDegree` denominator is the required
coordinate-inversion correction. -/
private theorem involution_polynomial_eq_reverse_div_X_pow (p : k[X]) :
    InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.reverse /
        RatFunc.X ^ p.natDegree := by
  rw [← inverseLaurent_eval_eq_involution]
  change LaurentPolynomial.eval₂ (algebraMap k (RatFunc k))
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
      ((LaurentPolynomial.invert (R := k)) (Polynomial.toLaurent p)) = _
  apply (eq_div_iff (pow_ne_zero _ RatFunc.X_ne_zero)).mpr
  calc
    directLaurentToRatFunc k
        ((LaurentPolynomial.invert (R := k)) (Polynomial.toLaurent p)) *
        RatFunc.X ^ p.natDegree =
        directLaurentToRatFunc k
          ((LaurentPolynomial.invert (R := k)) (Polynomial.toLaurent p) *
            LaurentPolynomial.T p.natDegree) := by
      rw [map_mul]
      simp [directLaurentToRatFunc]
    _ = directLaurentToRatFunc k (Polynomial.toLaurent p.reverse) := by
      rw [LaurentPolynomial.toLaurent_reverse]
    _ = algebraMap k[X] (RatFunc k) p.reverse := by
      simp only [directLaurentToRatFunc, LaurentPolynomial.eval₂_toLaurent]
      rw [← Polynomial.aeval_def]
      exact RatFunc.aeval_X_left_eq_algebraMap p.reverse

/-- The X-adic order of a nonzero polynomial is its exact trailing degree.
This is the normalized-factor calculation at the concrete base prime `(X)`.
It uses the principal ideal count, `rootMultiplicity_eq_natTrailingDegree'`,
and `Polynomial.idealX_span`; no finite extension is involved. -/
private theorem xAdic_order_polynomial (p : k[X]) (hp : p ≠ 0) :
    GlobalPlace.order (xAdicPlace k)
      (algebraMap k[X] (RatFunc k) p) = (p.natTrailingDegree : Int) := by
  classical
  letI : StrongNormalizationMonoid k := UniqueFactorizationMonoid.strongNormalizationMonoid
  unfold xAdicPlace GlobalPlace.order
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg]
  · rw [WithZero.log_exp]
    simp only [neg_neg]
    congr 1
    rw [Ideal.count_associates_factors_eq
      (by simpa [Ideal.zero_eq_bot] using hp)
      (Polynomial.idealX k).isPrime (Polynomial.idealX k).ne_bot]
    rw [Polynomial.idealX_span,
      Ideal.count_span_normalizedFactors_eq_of_normUnit hp
        Polynomial.normUnit_X Polynomial.prime_X]
    rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree',
      Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
    have hX : (Polynomial.X - Polynomial.C (0 : k) : k[X]) = Polynomial.X := by
      simp
    rw [hX]
    symm
    simpa only [← Polynomial.X_eq_normalize] using
      (UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
        Polynomial.irreducible_X hp)
  · exact hp

/-- The reciprocal-polynomial formula has the expected sign: at the X-adic
place it contributes minus the original polynomial degree. -/
private theorem xAdic_order_involution_polynomial (p : k[X]) (hp : p ≠ 0) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) p)) = -(p.natDegree : Int) := by
  have hX : GlobalPlace.order (xAdicPlace k) RatFunc.X = 1 := by
    simpa using
      (xAdic_order_polynomial k (Polynomial.X : k[X]) (by simp))
  have hXpow (n : ℕ) :
      GlobalPlace.order (xAdicPlace k) (RatFunc.X ^ n) = (n : Int) := by
    induction n with
    | zero => simp [GlobalPlace.order]
    | succ n hn =>
        rw [pow_succ,
          GlobalPlace.order_mul _ (pow_ne_zero _ RatFunc.X_ne_zero) RatFunc.X_ne_zero,
          hn, hX]
        push_cast
        ring
  rw [involution_polynomial_eq_reverse_div_X_pow,
    div_eq_mul_inv, GlobalPlace.order_mul]
  · rw [xAdic_order_polynomial]
    · rw [GlobalPlace.order_inv]
      rw [hXpow, Polynomial.natTrailingDegree_reverse]
      ring
    · exact (Polynomial.reverse_eq_zero.not).mpr hp
  · exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr
      ((Polynomial.reverse_eq_zero.not).mpr hp)
  · exact inv_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero)

omit [Finite k] in
/-- The involution is self-inverse.  Fraction-ring extensionality reduces this
to the variable, where the two reciprocal operations cancel. -/
private theorem rationalInvolution_involutive (h : RatFunc k) :
    InverseAffinePlace.rationalInvolution k
      (InverseAffinePlace.rationalInvolution k h) = h := by
  let e := InverseAffinePlace.rationalInvolution k
  have hhom : e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
      RingHom.id (RatFunc k) := by
    apply IsFractionRing.ringHom_ext (A := k[X])
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa only [RingHom.comp_apply, RingHom.id_apply, map_add] using
          congrArg₂ (· + ·) hp hq
    | monomial n a =>
        have hC' : e (e (RatFunc.C a)) = RatFunc.C a := by
          change e (e (algebraMap k (RatFunc k) a)) = algebraMap k (RatFunc k) a
          rw [e.commutes, e.commutes]
        have hC : e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) =
            (algebraMap k[X] (RatFunc k)) (Polynomial.C a) := by
          simpa [← RatFunc.algebraMap_eq_C] using hC'
        have hX' : e (e RatFunc.X) = RatFunc.X := by
          rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
            InverseAffinePlace.rationalInvolution_X, inv_inv]
        have hX : e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) =
            (algebraMap k[X] (RatFunc k)) Polynomial.X := by
          simpa using hX'
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [RingHom.comp_apply, RingHom.id_apply, map_mul, map_pow]
        change e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) *
            e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) ^ n =
          (algebraMap k[X] (RatFunc k)) (Polynomial.C a) *
            (algebraMap k[X] (RatFunc k)) Polynomial.X ^ n
        rw [hC, hX]
  change (e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom) h = h
  rw [hhom]
  rfl

/-- The order transport for an arbitrary nonzero rational function.  A
fraction-ring induction applies the reciprocal-polynomial formula to its
actual numerator and denominator, then subtracts their X-adic orders. -/
private theorem xAdic_order_involution_eq_neg_intDegree
    (h : RatFunc k) (hh : h ≠ 0) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k h) = -h.intDegree := by
  induction h using RatFunc.induction_on with
  | f p q hq =>
      have hpq : algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) q ≠ 0 := by
        simpa [RatFunc.mk_eq_div] using hh
      have hp : p ≠ 0 := by
        intro hp
        apply hpq
        simp [hp]
      have hqmap : algebraMap k[X] (RatFunc k) q ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hq
      have hpmap : algebraMap k[X] (RatFunc k) p ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hp
      rw [map_div₀, div_eq_mul_inv, GlobalPlace.order_mul]
      · rw [GlobalPlace.order_inv,
          xAdic_order_involution_polynomial k p hp,
          xAdic_order_involution_polynomial k q hq]
        rw [RatFunc.intDegree_div]
        · rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
          ring
        · exact hpmap
        · exact hqmap
      · exact (map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hpmap
      · exact inv_ne_zero
          ((map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hqmap)

/-- The concrete `(X)`-adic order after inversion is the original
rational-infinity order.  This is the exact reusable base-place transport
needed by the inverse-fibre normalized-factor calculation. -/
theorem xAdic_order_rationalInvolution_eq_rationalInfinity_order
    (h : RatFunc k) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k h) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k) h := by
  by_cases hh : h = 0
  · simp [hh, xAdicPlace, GlobalPlace.order]
  classical
  rw [xAdic_order_involution_eq_neg_intDegree k h hh]
  unfold GlobalPlace.rationalInfinity GlobalPlace.order
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero (F := k) hh,
    WithZero.log_exp]

omit [Finite k] in
/-- Norm functoriality for the transported rational-coordinate algebra.  The
map equation is proved on all fractions from the involutivity above; it is
not an extra condition on a caller. -/
private theorem rationalInvolution_norm_transport (f : F) :
    letI : Algebra k⟮X⟯ F :=
      InverseAffinePlace.transportedRationalAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) k F
    InverseAffinePlace.rationalInvolution k
      (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f) =
        Algebra.norm k⟮X⟯ f := by
  letI : Algebra k⟮X⟯ F :=
    InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
  exact @Algebra.norm_eq_of_ringEquiv k⟮X⟯ k⟮X⟯ F _ _ _ oldRationalAlgebra
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F)
    (InverseAffinePlace.rationalInvolution k) (by
      ext h
      change InverseAffinePlace.transportedRationalMap
          (oldRationalAlgebra := oldRationalAlgebra) k F
          (InverseAffinePlace.rationalInvolution k h) =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) h
      change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (InverseAffinePlace.rationalInvolution k
            (InverseAffinePlace.rationalInvolution k h)) =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) h
      rw [rationalInvolution_involutive]) f

/-- The exact bridge consumed by the final inverse-fibre local calculation.
After the local normalized-factor proof identifies the finite fibre degree
with the X-adic order of the transported norm, this theorem changes only the
base coordinate and yields the original rational-infinity order. -/
theorem transported_norm_xAdic_to_original_infinity (f : F) :
    letI : Algebra k⟮X⟯ F :=
      InverseAffinePlace.transportedRationalAlgebra k F
    GlobalPlace.order (xAdicPlace k) (Algebra.norm k⟮X⟯ f) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k)
        (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra k F
  rw [← rationalInvolution_norm_transport
    (oldRationalAlgebra := oldRationalAlgebra) k F]
  exact xAdic_order_rationalInvolution_eq_rationalInfinity_order k
    (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra f)

end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
