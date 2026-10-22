import QEC.Coding.ExpanderCodes.LPSOriginalRationalHeckePullback
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerAffineModel
import QEC.Coding.ExpanderCodes.LPSOriginalPrimeKronecker
import QEC.Coding.ExpanderCodes.LPSOriginalIntegralFricke
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerLevelMorphism

/-!
Internal/API transport of the original prime modular relation to the same
normalized integer model. The actual analytic j_N and j_Np satisfy Φ_p; the
injective ambient embedding transports that equation into the product-level
integral closure. Every characteristic-p domain image then satisfies the two
Frobenius root alternatives, using the genuine prime Kronecker congruence.

This is a derived prerequisite on the original modular-curve route motivated
by pinned PK22 main.tex ex:Xpq484–486 and th:qLDPC231–238. It does not prove
scheme-cycle equality, both normalized component degrees/multiplicities,
uniform smooth good reduction, a Weil bound, principal full-level spectra or
the arbitrary-finite-field/every-rate explicit asymptotically good qLDPC theorem.
The exact public node and source-backed statement remain unchanged and unproved.
-/
namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

def lpsOriginalJNHolomorphicEvalZ (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* LPSOriginalHolomorphicRing :=
  Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicRing)
    (lpsOriginalJNHolomorphic N hN)

lemma lpsOriginalPrimeIntegerPolynomial_productLevelRoot
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p hp).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJDilated N hN τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)))
      (lpsOriginalJDilated (N*p) (Nat.mul_pos hN hp) τ) = 0 := by
  have h := lpsOriginalIntegerPolynomial_root p hp (lpsE2AffineMatrix N hN 0 • τ)
  simpa only [lpsOriginalJDilated,lpsOriginalDilation_product,Nat.mul_comm] using h

lemma lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNHolomorphicEvalZ N hN)
      (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp)) = 0 := by
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp (lpsOriginalJNHolomorphicEvalZ N hN) =
      (Polynomial.evalRingHom (lpsOriginalJDilated N hN τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : Polynomial.C z = (z : Polynomial ℤ) := by
        simp
      rw [hz, map_intCast, map_intCast]
    · simp [lpsOriginalJNHolomorphicEvalZ,e,lpsOriginalJNHolomorphic]
  have he := Polynomial.hom_eval₂ (lpsOriginalIntegerPolynomial p hp)
    (lpsOriginalJNHolomorphicEvalZ N hN) e
    (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp))
  rw [hc] at he
  exact he.trans (lpsOriginalPrimeIntegerPolynomial_productLevelRoot N p hN hp τ)

def lpsOriginalJNIntegerFractionEval (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* LPSOriginalHolomorphicFractionField :=
  (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
    (lpsOriginalJNHolomorphicEvalZ N hN)

lemma lpsOriginalJNIntegerFractionEval_X (N : ℕ) (hN : 0 < N) :
    lpsOriginalJNIntegerFractionEval N hN Polynomial.X =
      lpsOriginalJNInFractionField N hN := by
  simp only [lpsOriginalJNIntegerFractionEval, RingHom.comp_apply,
    lpsOriginalJNHolomorphicEvalZ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    lpsOriginalJNInFractionField]

lemma lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNIntegerFractionEval N hN)
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0 := by
  have he := Polynomial.hom_eval₂ (lpsOriginalIntegerPolynomial p hp)
    (lpsOriginalJNHolomorphicEvalZ N hN)
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp))
  change (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    ((lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNHolomorphicEvalZ N hN)
      (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp))) = _ at he
  rw [lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot,map_zero] at he
  exact he.symm

lemma lpsOriginalPrimeKronecker_afterCoefficientMap
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (f : Polynomial (ZMod p) →+* A) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (f.comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      (Polynomial.X - Polynomial.C ((f Polynomial.X)^p)) *
        (Polynomial.X^p - Polynomial.C (f Polynomial.X)) := by
  rw [← Polynomial.map_map,lpsOriginalPrimeIntegerPolynomial_Kronecker]
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    Polynomial.map_pow,map_pow]

lemma lpsOriginalPrimeKronecker_eval
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Algebra (ZMod p) A]
    (j y : A) :
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))).eval₂
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) A) j) y =
      (y-j^p)*(y^p-j) := by
  rw [lpsOriginalPrimeIntegerPolynomial_Kronecker]
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_sub,Polynomial.eval₂_X,
    Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.coe_eval₂RingHom]

lemma lpsOriginalPrimeKronecker_root_iff
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] (j y : A) :
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))).eval₂
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) A) j) y = 0 ↔
      y=j^p ∨ y^p=j := by
  rw [lpsOriginalPrimeKronecker_eval,mul_eq_zero,sub_eq_zero,sub_eq_zero]

/-- The actual integral generator, rather than a new formal indeterminate. -/
def lpsOriginalIntegerNormalJN (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact lpsOriginalIntegerAffineToNormal N hN
    (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))

lemma lpsOriginalIntegerNormalJN_coe (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    (lpsOriginalIntegerNormalJN N hN).val.val =
      lpsOriginalJNInFractionField N hN := by
  exact lpsOriginalIntegerAffineToNormal_root N hN

/-- The actual normalized chart embeds in the original holomorphic fraction field. -/
def lpsOriginalIntegerNormalToHolomorphic (N : ℕ) (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN →+* LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact
    { toFun x := x.val.val
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma lpsOriginalIntegerNormalToHolomorphic_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalIntegerNormalToHolomorphic N hN) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact h

lemma lpsOriginalIntegerNormalToHolomorphic_JN
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalToHolomorphic N hN (lpsOriginalIntegerNormalJN N hN) =
      lpsOriginalJNInFractionField N hN := by
  exact lpsOriginalIntegerNormalJN_coe N hN

lemma lpsOriginalIntegerNormalToHolomorphic_frickeCoefficient
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalToHolomorphic N hN).comp
      (lpsOriginalIntegerFrickeCoefficientMap N hN) =
      lpsOriginalJNIntegerFractionEval N hN := by
  apply Polynomial.ringHom_ext
  · intro z
    have hz : Polynomial.C z = (z : Polynomial ℤ) := by
      simp
    rw [hz, map_intCast, map_intCast]
  · simp only [RingHom.comp_apply, lpsOriginalIntegerFrickeCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      lpsOriginalJNIntegerFractionEval, lpsOriginalJNHolomorphicEvalZ]
    exact lpsOriginalIntegerNormalJN_coe N hN

/-- The actual lower-level j_N coefficient map pulled into the product chart. -/
def lpsOriginalIntegerProductLevelCoefficientMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    Polynomial ℤ →+* lpsOriginalIntegerNormalZeroChart (N*p) (Nat.mul_pos hN hp) :=
  (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)).comp
      (lpsOriginalIntegerFrickeCoefficientMap N hN)

lemma lpsOriginalIntegerProductLevelCoefficientMap_X
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp Polynomial.X =
      lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
        (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
        (lpsOriginalIntegerNormalJN N hN) := by
  simp only [lpsOriginalIntegerProductLevelCoefficientMap, RingHom.comp_apply,
    lpsOriginalIntegerFrickeCoefficientMap,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

lemma lpsOriginalIntegerProductLevelCoefficientMap_holomorphic
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerNormalToHolomorphic (N*p) (Nat.mul_pos hN hp)).comp
      (lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp) =
      lpsOriginalJNIntegerFractionEval N hN := by
  apply Polynomial.ringHom_ext
  · intro z
    have hz : Polynomial.C z = (z : Polynomial ℤ) := by
      simp
    rw [hz, map_intCast, map_intCast]
  · rw [RingHom.comp_apply, lpsOriginalIntegerProductLevelCoefficientMap_X,
      lpsOriginalJNIntegerFractionEval_X]
    change (((lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
        (lpsOriginalIntegerNormalJN N hN)).val.val)) =
      lpsOriginalJNInFractionField N hN
    exact (lpsOriginalIntegerNormalZeroLevelPullback_coe N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
        (lpsOriginalIntegerNormalJN N hN)).trans
      (lpsOriginalIntegerNormalJN_coe N hN)

/-- The literal prime modular equation holds inside the same normalized
original integral chart at product level. -/
lemma lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂
      (lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp)
      (lpsOriginalIntegerNormalJN (N*p) (Nat.mul_pos hN hp)) = 0 := by
  apply lpsOriginalIntegerNormalToHolomorphic_injective (N*p) (Nat.mul_pos hN hp)
  rw [map_zero, Polynomial.hom_eval₂,
    lpsOriginalIntegerProductLevelCoefficientMap_holomorphic,
    lpsOriginalIntegerNormalToHolomorphic_JN,
    lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot]

/-- Reduction of any literal prime modular root in a characteristic-p domain
has the two genuine Frobenius alternatives. -/
lemma lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] (j y : A) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom A) j) y = 0 ↔
      y = j^p ∨ y^p = j := by
  have hc : (Polynomial.eval₂RingHom (algebraMap (ZMod p) A) j).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) =
      Polynomial.eval₂RingHom (Int.castRingHom A) j := by
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp
  rw [← hc, ← Polynomial.eval₂_map]
  exact lpsOriginalPrimeKronecker_root_iff p A j y

/-- Every actual characteristic-p domain image of the normalized original
product-level chart satisfies one of the two Frobenius relations. This is a
pointwise residue identity; it does not assert a scheme cycle equality. -/
lemma lpsOriginalPrimeIntegerPolynomial_productLevelResidueRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (h4N : 4 ∣ N) (hN : 0 < N)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (q : lpsOriginalIntegerNormalZeroChart (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos) →+* A) :
    let j := q (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
        (lpsOriginalIntegerNormalJN N hN))
    let y := q (lpsOriginalIntegerNormalJN (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    y = j^p ∨ y^p = j := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  let j := q (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
      (lpsOriginalIntegerNormalJN N hN))
  let y := q (lpsOriginalIntegerNormalJN (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos))
  let f := lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN (Fact.out : p.Prime).pos
  have hc : q.comp f = Polynomial.eval₂RingHom (Int.castRingHom A) j := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : Polynomial.C z = (z : Polynomial ℤ) := by
        simp
      rw [hz, map_intCast, map_intCast]
    · simp [f, j, lpsOriginalIntegerProductLevelCoefficientMap, lpsOriginalIntegerFrickeCoefficientMap, lpsOriginalIntegerNormalJN]
  have h := Polynomial.hom_eval₂
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos) f q
    (lpsOriginalIntegerNormalJN (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos))
  rw [lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot,
    map_zero, hc] at h
  exact (lpsOriginalPrimeIntegerPolynomial_charPRoot_iff p A j y).mp h.symm

end
end QEC.Coding.TannerLiftedProduct
