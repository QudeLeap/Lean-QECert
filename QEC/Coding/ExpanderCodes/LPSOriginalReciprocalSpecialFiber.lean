import QEC.Coding.ExpanderCodes.LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Reduced original reciprocal special fiber

The SAME original infinity chart in Q(j,j_N), whose integer polynomial
coordinate is 1/j, has radical ideal (p) and reduced quotient by p when p does
not divide the positive level. Polynomial reversal constructs an involution
of the Gauss base localization. Its actual fraction-field diagram identifies
the reciprocal base map, transports integrality, and lets the proved
prime-multiple descent return a genuine divisor witness from the original
Gauss normalization to the literal original infinity chart. No automorphism
of the whole generated field or original reducedness hypothesis is supplied.

This internal arithmetic prerequisite supports the original LPS route in
pinned PK22 main.tex ex:Xpq, lines 484–486, and th:qLDPC, lines 231–238. Whole
special-fiber scheme reducedness, normal or smooth fibers, global good
reduction, spectral bounds and the full explicit quantum family remain
unproved.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section

lemma C_dvd_reverse_iff {R : Type*} [CommSemiring R]
    (a : R) (f : Polynomial R) : Polynomial.C a ∣ f.reverse ↔ Polynomial.C a ∣ f := by
  rw [Polynomial.C_dvd_iff_dvd_coeff,Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have hi := h (Polynomial.revAt f.natDegree i)
    simpa only [Polynomial.coeff_reverse,Polynomial.revAt_invol] using hi
  · intro h i
    rw [Polynomial.coeff_reverse]
    exact h _

lemma integralElem_comp_iff_of_involutive
    {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K) (t : R →+* R)
    (ht : Function.Involutive t) (y : K) :
    (f.comp t).IsIntegralElem y ↔ f.IsIntegralElem y := by
  have heq : (f.comp t).comp t = f := by
    ext x
    exact congrArg f (ht x)
  constructor
  · exact fun h => h.of_comp
  · intro h
    have h' : ((f.comp t).comp t).IsIntegralElem y := heq.symm ▸ h
    exact h'.of_comp

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime

lemma lpsOriginalGaussX_isUnit (p : ℕ) [Fact p.Prime] :
    IsUnit (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) := by
  apply IsLocalization.map_units (M := (lpsOriginalGaussPrime p).primeCompl)
    (LPSOriginalGaussBase p) ⟨Polynomial.X,?_⟩
  change ¬ lpsOriginalGaussCoefficientReduction p Polynomial.X = 0
  simp [lpsOriginalGaussCoefficientReduction]

def lpsOriginalGaussReciprocalPolynomialMap (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* LPSOriginalGaussBase p :=
  Polynomial.eval₂RingHom
    ((algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)).comp Polynomial.C)
    (↑(lpsOriginalGaussX_isUnit p).unit⁻¹)

lemma lpsOriginalGaussReciprocalPolynomialMap_units
    (p : ℕ) [Fact p.Prime] (s : (lpsOriginalGaussPrime p).primeCompl) :
    IsUnit (lpsOriginalGaussReciprocalPolynomialMap p s) := by
  let G := LPSOriginalGaussBase p
  let u : Gˣ := (lpsOriginalGaussX_isUnit p).unit
  let i : ℤ →+* G := (algebraMap (Polynomial ℤ) G).comp Polynomial.C
  have hr : (s : Polynomial ℤ).reverse ∈ (lpsOriginalGaussPrime p).primeCompl := by
    intro h
    apply s.property
    have hd : Polynomial.C (p : ℤ) ∣ (s : Polynomial ℤ).reverse := by
      exact Ideal.mem_span_singleton.mp ((le_of_eq (lpsOriginalGaussPrime_eq_span p)) h)
    exact (le_of_eq (lpsOriginalGaussPrime_eq_span p).symm)
      (Ideal.mem_span_singleton.mpr
        ((QEC.Coding.AlgebraicGeometry.C_dvd_reverse_iff _ _).mp hd))
  have hmap : (s : Polynomial ℤ).reverse.eval₂ i (↑u : G) =
      algebraMap (Polynomial ℤ) G (s : Polynomial ℤ).reverse := by
    rw [show (↑u : G) = algebraMap (Polynomial ℤ) G Polynomial.X from
      (lpsOriginalGaussX_isUnit p).unit_spec]
    have h := Polynomial.hom_eval₂ (s : Polynomial ℤ).reverse Polynomial.C
      (algebraMap (Polynomial ℤ) G) Polynomial.X
    simpa only [Polynomial.eval₂_C_X] using h.symm
  have hrev := Polynomial.eval₂_reverse_mul_pow i (↑u⁻¹ : G) (s : Polynomial ℤ)
  have heq : lpsOriginalGaussReciprocalPolynomialMap p s =
      algebraMap (Polynomial ℤ) G (s : Polynomial ℤ).reverse * (↑u⁻¹ : G)^
        (s : Polynomial ℤ).natDegree := by
    change Polynomial.eval₂ i (↑u⁻¹ : G) (s : Polynomial ℤ) = _
    simpa only [invOf_units,inv_inv,hmap] using hrev.symm
  rw [heq]
  exact (IsLocalization.map_units G ⟨_,hr⟩).mul ((u⁻¹).isUnit.pow _)

def lpsOriginalGaussInversion (p : ℕ) [Fact p.Prime] :
    LPSOriginalGaussBase p →+* LPSOriginalGaussBase p :=
  IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl)
    (S := LPSOriginalGaussBase p)
    (g := lpsOriginalGaussReciprocalPolynomialMap p)
    (lpsOriginalGaussReciprocalPolynomialMap_units p)

lemma lpsOriginalGaussInversion_polynomial (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) :
    lpsOriginalGaussInversion p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
        lpsOriginalGaussReciprocalPolynomialMap p f := by
  simp [lpsOriginalGaussInversion]

lemma lpsOriginalGaussInversion_fractionDiagram (p : ℕ) [Fact p.Prime] :
    (lpsOriginalGaussBaseFractionMap p).comp (lpsOriginalGaussInversion p) =
      lpsOriginalJFractionInversion.comp (lpsOriginalGaussBaseFractionMap p) := by
  apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp [RingHom.comp_apply,lpsOriginalGaussInversion_polynomial,
      lpsOriginalGaussReciprocalPolynomialMap,map_units_inv,
      IsUnit.unit_spec,lpsOriginalGaussBaseFractionMap_base,
      lpsOriginalJFractionInversion_X]

lemma lpsOriginalGaussInversion_involutive (p : ℕ) [Fact p.Prime] :
    Function.Involutive (lpsOriginalGaussInversion p) := by
  intro x
  apply lpsOriginalGaussBaseFractionMap_injective p
  have h := RingHom.congr_fun (lpsOriginalGaussInversion_fractionDiagram p)
  change ∀ z, lpsOriginalGaussBaseFractionMap p (lpsOriginalGaussInversion p z) =
    lpsOriginalJFractionInversion (lpsOriginalGaussBaseFractionMap p z) at h
  rw [h (lpsOriginalGaussInversion p x),h x,
    lpsOriginalJFractionInversion_involutive]

lemma lpsOriginalGaussBaseToGeneratedField_fractionDiagram
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGaussBaseToGeneratedField N hN p =
      (algebraMap (FractionRing (Polynomial ℚ))
        (lpsOriginalGeneratedFunctionFieldQ N hN)).comp (lpsOriginalGaussBaseFractionMap p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
  apply RingHom.ext
  intro f
  change lpsOriginalGaussBaseToGeneratedField N hN p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) = _
  rw [lpsOriginalGaussBaseToGeneratedField_base]
  change algebraMap (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalIntegerBaseFractionMap f) = _
  change algebraMap (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalIntegerBaseFractionMap f) =
    algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGaussBaseFractionMap p (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f))
  rw [lpsOriginalGaussBaseFractionMap_base]
  rfl

def lpsOriginalReciprocalGaussBaseToGeneratedField
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalGaussBase p →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalGaussBaseToGeneratedField N hN p).comp (lpsOriginalGaussInversion p)

lemma lpsOriginalReciprocalGaussBaseToGeneratedField_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalReciprocalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN f := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalReciprocalGaussBaseToGeneratedField,
    lpsOriginalGaussBaseToGeneratedField_fractionDiagram]
  have h := RingHom.congr_fun (lpsOriginalGaussInversion_fractionDiagram p)
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)
  change lpsOriginalGaussBaseFractionMap p (lpsOriginalGaussInversion p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)) =
    lpsOriginalJFractionInversion (lpsOriginalGaussBaseFractionMap p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)) at h
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalGaussBaseFractionMap p (lpsOriginalGaussInversion p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f))) = _
  rw [h,lpsOriginalGaussBaseFractionMap_base]
  rfl

lemma lpsOriginalReciprocalGaussBase_scalarTower
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
    IsScalarTower (Polynomial ℤ) (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro f
  exact (lpsOriginalReciprocalGaussBaseToGeneratedField_base N hN p f).symm

lemma lpsOriginalGaussIntegral_reciprocalIntegral_iff
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (y : lpsOriginalGeneratedFunctionFieldQ N hN) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).IsIntegralElem y ↔
      (lpsOriginalGaussBaseToGeneratedField N hN p).IsIntegralElem y := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact QEC.Coding.AlgebraicGeometry.integralElem_comp_iff_of_involutive
    (lpsOriginalGaussBaseToGeneratedField N hN p) (lpsOriginalGaussInversion p)
    (lpsOriginalGaussInversion_involutive p) y

attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring

lemma lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
    ∀ y : lpsOriginalGeneratedFunctionFieldQ N hN,
      IsIntegral (Polynomial ℤ) ((p : lpsOriginalGeneratedFunctionFieldQ N hN)*y) →
      IsIntegral (LPSOriginalGaussBase p) y → IsIntegral (Polynomial ℤ) y := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let instRK := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let instGK := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
  let R := Polynomial ℤ
  let G := LPSOriginalGaussBase p
  let K : Type := lpsOriginalGeneratedFunctionFieldQ N hN
  let J := FractionRing R
  let : SMul R K := instRK.toSMul
  let : SMul G K := instGK.toSMul
  let : IsScalarTower R G K := lpsOriginalReciprocalGaussBase_scalarTower N hN p
  let : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    ((algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      lpsOriginalIntegerReciprocalBaseFractionMap_injective)
  let instJK : Algebra J K := FractionRing.liftAlgebra R K
  let : SMul J K := instJK.toSMul
  let : IsScalarTower R J K := FractionRing.isScalarTower_liftAlgebra R K
  let : IsScalarTower G J K := .of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply RingHom.ext
    intro f
    change algebraMap G K (algebraMap R G f) =
      algebraMap J K (algebraMap G J (algebraMap R G f))
    rw [← IsScalarTower.algebraMap_apply R G K,
      ← IsScalarTower.algebraMap_apply R G J,
      ← IsScalarTower.algebraMap_apply R J K])
  let : FaithfulSMul G K := (faithfulSMul_iff_algebraMap_injective G K).mpr (by
    rw [IsScalarTower.algebraMap_eq G J K]
    exact (algebraMap J K).injective.comp (IsFractionRing.injective G J))
  let : IsIntegrallyClosed G :=
    isIntegrallyClosed_of_isLocalization G (lpsOriginalGaussPrime p).primeCompl
      (lpsOriginalGaussPrime p).primeCompl_le_nonZeroDivisors
  change ∀ y : K, IsIntegral R ((p : K)*y) → IsIntegral G y → IsIntegral R y
  intro y hR hG
  have ha : Prime (Polynomial.C (p : ℤ)) := Polynomial.prime_C_iff.mpr
    (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime)))
  apply QEC.Coding.AlgebraicGeometry.integral_of_prime_multiple_and_localizedIntegral
    (lpsOriginalGaussPrime p) J K (Polynomial.C (p : ℤ))
    (lpsOriginalGaussPrime_eq_span p) ha y
  · simpa only [Polynomial.C_eq_natCast,map_natCast] using hR
  · exact hG

def lpsOriginalIntegerNormalInfinityToGaussNormalization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  exact { toFun := fun x => ⟨x.val,by
            apply (lpsOriginalGaussIntegral_reciprocalIntegral_iff N hN p x.val).mp
            let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
            let := lpsOriginalReciprocalGaussBase_scalarTower N hN p
            exact x.property.tower_top⟩
          map_one' := rfl
          map_mul' _ _ := rfl
          map_zero' := rfl
          map_add' _ _ := rfl }

lemma lpsOriginalNormalInfinity_primeIdeal_radical
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    (Ideal.span {(p : integralClosure (Polynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN))}).IsRadical := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let R := Polynomial ℤ
  let G := LPSOriginalGaussBase p
  let K : Type := lpsOriginalGeneratedFunctionFieldQ N hN
  let C : Type := integralClosure R K
  let D : Type := integralClosure G K
  let instCCommRing : CommRing C := inferInstance
  let : Ring C := instCCommRing.toRing
  let : CommSemiring C := instCCommRing.toCommSemiring
  let : Semiring C := instCCommRing.toCommSemiring.toSemiring
  let instRC : Algebra R C := (integralClosure R K).algebra
  let : SMul R C := instRC.toSMul
  let instDCommRing : CommRing D := gaussFiberNormalizationCommRing N hN p
  let : Ring D := instDCommRing.toRing
  let : CommSemiring D := instDCommRing.toCommSemiring
  let : Semiring D := instDCommRing.toCommSemiring.toSemiring
  let instGD : Algebra G D := (integralClosure G K).algebra
  let : SMul G D := instGD.toSMul
  let F : C →+* D := lpsOriginalIntegerNormalInfinityToGaussNormalization N hN p
  let Jp : Ideal D := Ideal.span {(p : D)}
  have hmax : IsLocalRing.maximalIdeal G = Ideal.span {(p : G)} := by
    calc
      IsLocalRing.maximalIdeal G =
          (lpsOriginalGaussPrime p).map (algebraMap R G) :=
        (Localization.AtPrime.map_eq_maximalIdeal (I := lpsOriginalGaussPrime p)).symm
      _ = (Ideal.span {Polynomial.C (p : ℤ)}).map (algebraMap R G) :=
        congrArg (Ideal.map (algebraMap R G)) (lpsOriginalGaussPrime_eq_span p)
      _ = Ideal.span {(p : G)} := by
        rw [Ideal.map_span,Set.image_singleton]
        simp only [map_natCast]
  have hJ : Jp = (IsLocalRing.maximalIdeal G).map (algebraMap G D) := by
    rw [hmax,Ideal.map_span,Set.image_singleton,map_natCast]
  have hred : IsReduced (D ⧸
      (IsLocalRing.maximalIdeal G).map (algebraMap G D)) :=
    lpsOriginalNormalization_gaussSpecialFiber_reduced N hN p hpN
  have hradD : ((IsLocalRing.maximalIdeal G).map (algebraMap G D)).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced _).mpr hred
  have hrad : Jp.IsRadical := hJ.symm ▸ hradD
  change (Ideal.span {(p : C)}).IsRadical
  intro x hx
  obtain ⟨n,hxn⟩ := hx
  have hxD : F x ∈ Jp := by
    apply hrad
    refine ⟨n,?_⟩
    have hmap := Ideal.mem_map_of_mem F hxn
    simpa only [Ideal.map_span,Set.image_singleton,map_natCast,map_pow] using hmap
  obtain ⟨d,hd⟩ := Ideal.mem_span_singleton.mp hxD
  have heq : (p : K)*d.val = x.val := by
    have h := congrArg (fun z : D => z.val) hd
    exact h.symm
  have hR : IsIntegral R ((p : K)*d.val) := heq.symm ▸ x.property
  have hG : (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).IsIntegralElem d.val :=
    (lpsOriginalGaussIntegral_reciprocalIntegral_iff N hN p d.val).mpr d.property
  have hi : IsIntegral R d.val :=
    lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral N hN p d.val hR hG
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨d.val,hi⟩,?_⟩
  apply Subtype.ext
  exact heq.symm

lemma lpsOriginalNormalInfinity_specialFiber_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    IsReduced (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) ⧸
      Ideal.span {(p : integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))}) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (lpsOriginalNormalInfinity_primeIdeal_radical N hN p hpN)

end
end QEC.Coding.TannerLiftedProduct
