import QEC.Coding.ExpanderCodes.LPSOriginalGaussLocalOrder
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height

/-!
The SAME original Gauss normalization has ramification index one and a nonempty
reduced generic special fiber when the prime does not divide the positive level.
The original integer normal zero chart canonically localizes to this integral
closure inside the original generated function field. Every original height-one
prime containing the rational prime contracts to the coefficient Gauss prime;
that contraction proof needs no coprimality assumption.

Internal arithmetic prerequisite for PK22 main.tex ex:Xpq (lines 484–486) and
th:qLDPC (lines 231–238). Original vertical stalk comparison, global
good reduction, horizontal branch geometry, spectral bounds and the full qLDPC
main theorem remain unproved. #449 stays open and pk-good-qldpc unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal

lemma lpsOriginalGaussAffineOrder_etale
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    Algebra.Etale (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) := by
  let : Module.Free (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).free_adjoinRoot
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  exact Algebra.Etale.of_formallyUnramified_of_flat

lemma lpsOriginalGaussAffineOrder_ramificationIndex_one
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsPrime] :
    q.ramificationIdx (LPSOriginalGaussBase p) = 1 := by
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  let : Algebra.FormallyUnramified (LPSOriginalGaussAffineOrder N hN p)
      (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  let : Algebra.IsUnramifiedAt (LPSOriginalGaussBase p) q :=
    Algebra.FormallyUnramified.comp (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p) (Localization.AtPrime q)
  exact Ideal.ramificationIdx_eq_one q (LPSOriginalGaussBase p)

lemma lpsOriginalGaussAffineOrder_specialFiber_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    IsReduced (LPSOriginalGaussAffineOrder N hN p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))) := by
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact Algebra.FormallyUnramified.isRadical_map_isMaximal (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder N hN p) (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p))

lemma lpsOriginalGaussNormalization_etale
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    Algebra.Etale (LPSOriginalGaussBase p)
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let := lpsOriginalGaussAffineOrder_etale N hN p hpN
  exact Algebra.Etale.of_equiv (lpsOriginalGaussNormalizationEquiv N hN p hpN)

lemma lpsOriginalGaussAffineOrder_specialFiber_nontrivial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Nontrivial (LPSOriginalGaussAffineOrder N hN p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))) := by
  let : Module.Free (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).free_adjoinRoot
  let : Module.Finite (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let := lpsOriginalGaussAffineOrder_domain N hN p
  obtain ⟨q,hq,hqover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := LPSOriginalGaussBase p) (S := LPSOriginalGaussAffineOrder N hN p)
    (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder N hN p))]
      exact bot_le)
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top hq.ne_top
    (Ideal.map_le_of_le_comap (le_of_eq hqover.symm))

def lpsOriginalGaussBaseToGeneratedField
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalGaussBase p →+* lpsOriginalGeneratedFunctionFieldQ N hN :=
  (lpsOriginalGaussAffineToGenerated N hN p).comp
    (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))

lemma lpsOriginalGaussBaseToGeneratedField_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
      lpsOriginalIntegerBaseToGeneratedField N hN f := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change lpsOriginalGaussAffineToGenerated N hN p
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)) = _
  rw [← AdjoinRoot.map_of (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))
    (lpsOriginalIntegerPolynomial N hN) (lpsOriginalGaussPolynomial N hN p) dvd_rfl]
  change lpsOriginalGaussAffineToGenerated N hN p
    (lpsOriginalIntegerAffineToGauss N hN p
      (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) f)) = _
  rw [lpsOriginalGaussAffineToGenerated_base]
  exact lpsOriginalIntegerAffineToGenerated_base N hN f

lemma lpsOriginalGaussBase_scalarTower
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    IsScalarTower (Polynomial ℤ) (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro f
  exact (lpsOriginalGaussBaseToGeneratedField_base N hN p f).symm

def lpsOriginalIntegerNormalZeroToGaussNormalization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let := lpsOriginalGaussBase_scalarTower N hN p
  exact { toFun := fun x => ⟨x.val,x.property.tower_top⟩
          map_one' := rfl
          map_mul' _ _ := rfl
          map_zero' := rfl
          map_add' _ _ := rfl }

lemma lpsOriginalIntegerNormalZeroGauss_localization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    let := (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
        (lpsOriginalGaussPrime p).primeCompl)
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let := lpsOriginalGaussBase_scalarTower N hN p
  let C := integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let D := integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let instCD : Algebra C D :=
    (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d x => by
      change (c.val*d.val)*x=c.val*(d.val*x)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro f
      apply Subtype.ext
      rfl)
  let M := (lpsOriginalGaussPrime p).primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid (lpsOriginalGeneratedFunctionFieldQ N hN) M)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun x hx => by
      obtain ⟨f,hf,rfl⟩ := hx
      apply isUnit_iff_ne_zero.mpr
      intro hz
      have hinj : Function.Injective (lpsOriginalIntegerBaseToGeneratedField N hN) :=
        (algebraMap (FractionRing (Polynomial ℚ))
          (lpsOriginalGeneratedFunctionFieldQ N hN)).injective.comp
          lpsOriginalIntegerBaseFractionMap_injective
      have hf0 : f = 0 := hinj (hz.trans (lpsOriginalIntegerBaseToGeneratedField N hN).map_zero.symm)
      exact hf (hf0 ▸ Ideal.zero_mem _))
  exact IsLocalization.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN) (Rf := LPSOriginalGaussBase p)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) M

section NormalizationFiber
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local instance gaussFiberBaseFieldAlgebra :
    Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
  ((lpsOriginalGaussAffineToGenerated N hN p).comp
    (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
local notation "D" => integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
local instance gaussFiberNormalizationCommRing : CommRing D := inferInstance
local instance gaussFiberNormalizationRing : Ring D := CommRing.toRing
local instance gaussFiberNormalizationSemiring : Semiring D :=
  (gaussFiberNormalizationCommRing N hN p).toCommSemiring.toSemiring
include hN

lemma lpsOriginalNormalization_gaussRamificationIndex_one
    (hpN : ¬ p ∣ N) (q : Ideal D) [q.IsPrime] :
    q.ramificationIdx (LPSOriginalGaussBase p) = 1 := by
  let := lpsOriginalGaussNormalization_etale N hN p hpN
  let : Algebra.IsUnramifiedAt (LPSOriginalGaussBase p) q :=
    (Algebra.formallyUnramified_iff_forall (R := LPSOriginalGaussBase p) (A := D)).mp
      inferInstance ⟨q,inferInstance⟩
  exact Ideal.ramificationIdx_eq_one q (LPSOriginalGaussBase p)

lemma lpsOriginalNormalization_gaussSpecialFiber_reduced (hpN : ¬ p ∣ N) :
    IsReduced (D ⧸ (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) D)) := by
  let := lpsOriginalGaussNormalization_etale N hN p hpN
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact Algebra.FormallyUnramified.isRadical_map_isMaximal (LPSOriginalGaussBase p)
    D (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p))

lemma lpsOriginalNormalization_gaussSpecialFiber_nontrivial (hpN : ¬ p ∣ N) :
    Nontrivial (D ⧸ (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) D)) := by
  let : Module.Free (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).free_adjoinRoot
  let : Module.Finite (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let : Module.Free (LPSOriginalGaussBase p) D :=
    Module.Free.of_equiv (lpsOriginalGaussNormalizationEquiv N hN p hpN).toLinearEquiv
  let : Module.Finite (LPSOriginalGaussBase p) D :=
    Module.Finite.equiv (lpsOriginalGaussNormalizationEquiv N hN p hpN).toLinearEquiv
  obtain ⟨q,hq,hqover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := LPSOriginalGaussBase p) (S := D)
    (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (LPSOriginalGaussBase p) D)]
      exact bot_le)
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top hq.ne_top
    (Ideal.map_le_of_le_comap (le_of_eq hqover.symm))
end NormalizationFiber

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.AlgebraicGeometry

lemma heightOne_primeUnder_eq
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.HasGoingDown R S]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥)
    (q : Ideal S) [q.IsPrime] (hq : q.height = 1) (hle : P ≤ q.under R) :
    q.under R = P := by
  by_contra hn
  have hlt : P < q.under R := lt_of_le_of_ne hle (Ne.symm hn)
  obtain ⟨Q,hQlt,hQprime,hQover⟩ := Ideal.exists_ideal_lt_liesOver_of_lt
    (p := P) (q := q.under R) q hlt
  let : Q.IsPrime := hQprime
  let : Q.LiesOver P := hQover
  have hbot : (⊥ : Ideal S).under R = ⊥ := by
    change RingHom.ker (algebraMap R S) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)
  have hQne : Q ≠ ⊥ := by
    intro hz
    apply hP
    rw [Q.over_def P,hz,hbot]
  have hQheight : 1 ≤ Q.height :=
    Order.one_le_iff_ne_zero.mpr (Q.height_eq_zero_iff_eq_bot.not.mpr hQne)
  have htwo : (2 : ℕ∞) ≤ 1 := calc
    (2 : ℕ∞) = 1 + 1 := rfl
    _ ≤ Q.height + 1 := by simpa only [add_comm] using add_le_add_right hQheight (1 : ℕ∞)
    _ ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime hQlt
    _ = 1 := hq
  norm_num at htwo

end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
local instance verticalPrimeJAlgebra :
    Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
variable (N : ℕ) (hN : 0 < N)
local instance verticalPrimeBaseFieldAlgebra :
    Algebra (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
  (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local instance verticalPrimeNormalCommRing : CommRing C := inferInstance
local instance verticalPrimeNormalRing : Ring C := CommRing.toRing
local instance verticalPrimeNormalSemiring : Semiring C :=
  (verticalPrimeNormalCommRing N hN).toCommSemiring.toSemiring
include hN

lemma lpsOriginalNormalZero_heightOne_verticalUnder
    (p : ℕ) [Fact p.Prime] (q : Ideal C) [q.IsPrime]
    (hq : q.height = 1) (hpq : (p : C) ∈ q) :
    q.under (Polynomial ℤ) = lpsOriginalGaussPrime p := by
  have hiK : Function.Injective (algebraMap (Polynomial ℤ) K) :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      lpsOriginalIntegerBaseFractionMap_injective
  let : FaithfulSMul (Polynomial ℤ) C :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial ℤ) C).mpr (fun f g h => by
      apply hiK
      exact congrArg (fun c : C => c.val) h)
  have hle : lpsOriginalGaussPrime p ≤ q.under (Polynomial ℤ) := by
    rw [lpsOriginalGaussPrime_eq_span,Ideal.span_singleton_le_iff_mem]
    change algebraMap (Polynomial ℤ) C (Polynomial.C (p : ℤ)) ∈ q
    simpa using hpq
  exact QEC.Coding.AlgebraicGeometry.heightOne_primeUnder_eq
    (lpsOriginalGaussPrime p) (lpsOriginalGaussPrime_ne_bot p) q hq hle

end
end QEC.Coding.TannerLiftedProduct
