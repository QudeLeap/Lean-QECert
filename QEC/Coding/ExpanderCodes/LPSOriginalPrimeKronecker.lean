import QEC.Coding.ExpanderCodes.LPSOriginalPrimeCuspCorrespondence

/-!
# Kronecker reduction of the original prime modular polynomial

For every prime p, the same monic integer polynomial for j(tau) and j(p*tau)
reduces to (Y-X^p)(Y^p-X). The theorem is Milne, Modular Functions and Modular
Forms, Theorem 6.1, pp. 82-84. The faithful actual pole evaluation descends the
cusp-series identity to the polynomial ring. No good-reduction or spectral
claim is inferred from this internal result.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

def lpsOriginalModPrimeJPolynomialEval (p : ℕ) [Fact p.Prime] :
    Polynomial (ZMod p) →+* lpsOriginalCuspSeriesRing (ZMod p) :=
  Polynomial.eval₂RingHom
    ((algebraMap (PowerSeries (ZMod p)) (lpsOriginalCuspSeriesRing (ZMod p))).comp PowerSeries.C)
    (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)

lemma lpsOriginalModPrimeJPolynomialEval_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalModPrimeJPolynomialEval p) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hF : PowerSeries.constantCoeff
      (PowerSeries.expand p (Fact.out : p.Prime).ne_zero
        (lpsOriginalCuspJNumerator (ZMod p)))=1 := by
    rw [PowerSeries.constantCoeff_expand]
    exact lpsOriginalJZSeries_mod_constant p
  apply (lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
    (PowerSeries.expand p (Fact.out : p.Prime).ne_zero (lpsOriginalCuspJNumerator (ZMod p)))
    hF p (Fact.out : p.Prime).pos P).mp
  simpa only [lpsOriginalModPrimeJPolynomialEval,Polynomial.coe_eval₂RingHom,
    lpsOriginalCuspJWidth] using hP

lemma lpsOriginalModPrimeJPolynomialEval_integerCoeff (p : ℕ) [Fact p.Prime] :
    (lpsOriginalModPrimeJPolynomialEval p).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))=
      lpsOriginalModPrimeCoefficientEval p := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalModPrimeJPolynomialEval,lpsOriginalModPrimeCoefficientEval]
  · simp [lpsOriginalModPrimeJPolynomialEval,lpsOriginalModPrimeCoefficientEval]

lemma lpsOriginalModPrimeJPolynomialEval_X (p : ℕ) [Fact p.Prime] :
    lpsOriginalModPrimeJPolynomialEval p Polynomial.X=
      lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero := by
  simp [lpsOriginalModPrimeJPolynomialEval]

lemma lpsOriginalPrimeIntegerPolynomial_Kronecker (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))=
      (Polynomial.X-Polynomial.C ((Polynomial.X : Polynomial (ZMod p))^p)) *
        (Polynomial.X^p-Polynomial.C (Polynomial.X : Polynomial (ZMod p))) := by
  apply Polynomial.map_injective (lpsOriginalModPrimeJPolynomialEval p)
    (lpsOriginalModPrimeJPolynomialEval_injective p)
  rw [Polynomial.map_map,lpsOriginalModPrimeJPolynomialEval_integerCoeff]
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    Polynomial.map_pow,map_pow,lpsOriginalModPrimeJPolynomialEval_X]
  simpa only [map_pow] using lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization p

end
end QEC.Coding.TannerLiftedProduct
