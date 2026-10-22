import QEC.Coding.ExpanderCodes.LPSOriginalPrimeIntegralHeckeRelation
import QEC.Coding.ExpanderCodes.LPSOriginalGaussSpecialFiber

/-! # The actual integral and Gauss dual modular equation

Transport the already proved rational Fricke-swapped relation through the actual
integer normalization and the actual good-prime Gauss normalization comparison.
The literal integral coordinates are identified in the same generated function
field. The monic dual relation also transfers transcendence over a field.

These are derived internal prerequisites for PK22's LPS input (registered source
`ex:Xpq`) and ultimately `pk-good-qldpc`; they do not establish its main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalIntegerNormalBaseCoefficientMap
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact (lpsOriginalIntegerAffineToNormal N hN).toRingHom.comp
    (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN))

def lpsOriginalIntegerNormalJ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN :=
  lpsOriginalIntegerNormalBaseCoefficientMap N hN Polynomial.X

lemma lpsOriginalIntegerNormalBaseCoefficientMap_holomorphic
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalToHolomorphic N hN).comp
      (lpsOriginalIntegerNormalBaseCoefficientMap N hN) =
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  apply RingHom.ext
  intro f
  change ((lpsOriginalIntegerAffineToGenerated N hN
    (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) f)) :
      LPSOriginalHolomorphicFractionField) = _
  rw [lpsOriginalIntegerAffineToGenerated_base]
  change lpsOriginalJFractionEmbeddingQ (lpsOriginalIntegerBaseFractionMap f) = _
  rw [lpsOriginalIntegerBaseFractionMap, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  rfl

lemma lpsOriginalIntegerNormalJ_generated
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalJ N hN).val = lpsOriginalRationalJElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  change lpsOriginalIntegerAffineToGenerated N hN
    (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) Polynomial.X) = _
  rw [lpsOriginalIntegerAffineToGenerated_base,
    lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ]

lemma lpsOriginalIntegerNormalJ_coe
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalToHolomorphic N hN (lpsOriginalIntegerNormalJ N hN) =
      lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  change (lpsOriginalIntegerNormalJ N hN).val.val = _
  rw [lpsOriginalIntegerNormalJ_generated,lpsOriginalRationalJElement_coe]

lemma lpsOriginalIntegerNormalJN_generated
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalJN N hN).val = lpsOriginalRationalJNElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  rfl

lemma lpsOriginalIntegerPolynomial_normalDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (lpsOriginalIntegerFrickeCoefficientMap N hN)
      (lpsOriginalIntegerNormalJ N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let f := (integralClosure (Polynomial ℤ)
    (lpsOriginalGeneratedFunctionFieldQ N hN)).val.toRingHom
  have hc : f.comp (lpsOriginalIntegerFrickeCoefficientMap N hN) =
      Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJNElement N hN) := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : Polynomial.C z = (z : Polynomial ℤ) := by simp
      rw [hz,map_intCast,map_intCast]
    · simp only [RingHom.comp_apply,lpsOriginalIntegerFrickeCoefficientMap,
        Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
      rfl
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext h
  apply hf
  rw [Polynomial.hom_eval₂,map_zero,hc]
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJNElement N hN))
    (lpsOriginalIntegerNormalJ N hN).val = 0
  rw [lpsOriginalIntegerNormalJ_generated]
  exact lpsOriginalIntegerPolynomial_frickeSwappedRoot N hN

/-- transport the proved dual equation through any actual normalization map. -/
lemma lpsOriginalIntegerPolynomial_normalDualRoot_image
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (K : Type*) [CommRing K]
    (f : lpsOriginalIntegerNormalZeroChart N hN →+* K) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom K)
        (f (lpsOriginalIntegerNormalJN N hN)))
      (f (lpsOriginalIntegerNormalJ N hN)) = 0 := by
  have h := congrArg f (lpsOriginalIntegerPolynomial_normalDualRoot N hN)
  have hc : f.comp (lpsOriginalIntegerFrickeCoefficientMap N hN) =
      Polynomial.eval₂RingHom (Int.castRingHom K)
        (f (lpsOriginalIntegerNormalJN N hN)) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [lpsOriginalIntegerFrickeCoefficientMap]
    · simp [lpsOriginalIntegerFrickeCoefficientMap,lpsOriginalIntegerNormalJN]
  rw [Polynomial.hom_eval₂,map_zero,hc] at h
  exact h

/-- the existing good-prime normalization comparison gives the actual map. -/
def lpsOriginalIntegerNormalZeroToGaussAffineOrder
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroChart N hN →+* LPSOriginalGaussAffineOrder N hN p := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  exact (lpsOriginalGaussNormalizationEquiv N hN p hpN).symm.toRingHom.comp
    (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p)

lemma lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN
      (lpsOriginalIntegerNormalJN N hN) =
      AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let e := lpsOriginalGaussNormalizationEquiv N hN p hpN
  apply e.injective
  change e (e.symm ((lpsOriginalIntegerNormalZeroToGaussNormalization N hN p)
    (lpsOriginalIntegerNormalJN N hN))) = e _
  erw [e.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  change (lpsOriginalIntegerNormalJN N hN).val.val =
    (e (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val
  rw [lpsOriginalIntegerNormalJN_generated,lpsOriginalRationalJNElement_coe,
    lpsOriginalGaussNormalizationEquiv_root]

lemma lpsOriginalIntegerNormalZeroToGaussAffineOrder_J
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN
      (lpsOriginalIntegerNormalJ N hN) =
      AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let e := lpsOriginalGaussNormalizationEquiv N hN p hpN
  apply e.injective
  change e (e.symm ((lpsOriginalIntegerNormalZeroToGaussNormalization N hN p)
    (lpsOriginalIntegerNormalJ N hN))) = e (algebraMap _ _ _)
  erw [e.apply_symm_apply,e.commutes]
  apply Subtype.ext
  change (lpsOriginalIntegerNormalJ N hN).val =
    lpsOriginalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)
  rw [lpsOriginalIntegerNormalJ_generated,lpsOriginalGaussBaseToGeneratedField_base,
    lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ]

lemma lpsOriginalIntegerPolynomial_gaussDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = 0 := by
  have h := lpsOriginalIntegerPolynomial_normalDualRoot_image N hN
    (LPSOriginalGaussAffineOrder N hN p)
    (lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN)
  rw [lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN,
    lpsOriginalIntegerNormalZeroToGaussAffineOrder_J] at h
  exact h

/-- a monic dual relation transfers transcendence. -/
lemma lpsOriginalDualMonicRelation_transcendental
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    (P : Polynomial (Polynomial F)) (hP : P.Monic)
    (x y : K)
    (hroot : P.eval₂ (Polynomial.eval₂RingHom (algebraMap F K) y) x = 0)
    (hx : Transcendental F x) : Transcendental F y := by
  intro hy
  let E := Algebra.adjoin F ({y} : Set K)
  let : Module.Finite F E := Algebra.finite_adjoin_simple_of_isIntegral hy.isIntegral
  let ys : E := ⟨y,Algebra.subset_adjoin (by simp)⟩
  let c : Polynomial F →+* E := Polynomial.eval₂RingHom (algebraMap F E) ys
  have hc : (algebraMap E K).comp c = Polynomial.eval₂RingHom (algebraMap F K) y := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [c,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
      change algebraMap E K (algebraMap F E a) = algebraMap F K a
      exact (IsScalarTower.algebraMap_apply F E K a).symm
    · simp only [c,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
      change (ys : K) = y
      rfl
  have hxi : IsIntegral E x := by
    refine ⟨P.map c,hP.map c,?_⟩
    change (P.map c).eval₂ (algebraMap E K) x = 0
    rw [Polynomial.eval₂_map,hc]
    exact hroot
  exact hx (isIntegral_trans (R := F) x hxi).isAlgebraic


end
end QEC.Coding.TannerLiftedProduct
