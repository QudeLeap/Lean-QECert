import QEC.Coding.ExpanderCodes.LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# LPSOriginalIntegerFlatModel

The actual normalized original integer model is flat and surjective over Z,
and locally of finite presentation. Its two integral-closure domains are
Z-torsionfree. Lying-over for their actual faithful integral Z[X] maps gives
surjectivity of the original projective j projection and then of the Z map.

This derived arithmetic prerequisite follows pinned PK22 ex:Xpq,
main.tex:484-486, and supports th:qLDPC, main.tex:231-238. Uniform smooth
reduction away the varying original levels, Hecke/Frobenius/Weil identities,
the LPS spectral bound and the exact quantum family remain unproved. No
flatness or surjectivity conclusion is supplied as an assumption.
-/

open CategoryTheory AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalIntegerNormalZeroChart_intFlat (N : ℕ) (hN : 0 < N) :
    (Int.castRingHom (lpsOriginalIntegerNormalZeroChart N hN)).Flat := by
  let : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hN) :=
    Ring.toIntAlgebra (lpsOriginalIntegerNormalZeroChart N hN)
  rw [← algebraMap_int_eq, RingHom.flat_algebraMap_iff]
  infer_instance

lemma lpsOriginalIntegerNormalInfinityChart_intFlat (N : ℕ) (hN : 0 < N) :
    (Int.castRingHom (lpsOriginalIntegerNormalInfinityChart N hN)).Flat := by
  let : Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hN) :=
    Ring.toIntAlgebra (lpsOriginalIntegerNormalInfinityChart N hN)
  rw [← algebraMap_int_eq, RingHom.flat_algebraMap_iff]
  infer_instance

lemma lpsOriginalIntegerNormalGluedToSpecZ_flat (N : ℕ) (hN : 0 < N) :
    Flat (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Flat.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat.{0})
      (Q := @RingHom.Flat.{0, 0})
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat.{0})
    (f := lpsOriginalIntegerNormalGluedToSpecZ N hN)
    (lpsOriginalIntegerNormalSchemeGlueData N hN).openCover).mpr
  intro b
  change Flat (lpsOriginalIntegerNormalGluedChartMap N hN b ≫
    lpsOriginalIntegerNormalGluedToSpecZ N hN)
  cases b with
  | false =>
    have hm := lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalIntegerNormalZeroChart N hN)
      (lpsOriginalIntegerNormalGluedChartMap N hN false ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (Spec.map (CommRingCat.ofHom (Int.castRingHom (lpsOriginalIntegerNormalZeroChart N hN))))
    exact hm.symm ▸ Flat.SpecMap_iff.mpr
      (lpsOriginalIntegerNormalZeroChart_intFlat N hN)
  | true =>
    have hm := lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalIntegerNormalInfinityChart N hN)
      (lpsOriginalIntegerNormalGluedChartMap N hN true ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (Spec.map (CommRingCat.ofHom (Int.castRingHom (lpsOriginalIntegerNormalInfinityChart N hN))))
    exact hm.symm ▸ Flat.SpecMap_iff.mpr
      (lpsOriginalIntegerNormalInfinityChart_intFlat N hN)

lemma lpsOriginalIntegerNormalZeroChartToJLine_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalZeroChartToJLine N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalZeroChart N hN)))
  have hinj : Function.Injective (algebraMap (Polynomial ℤ)
      (lpsOriginalIntegerNormalZeroChart N hN)) := by
    intro x y h
    have he := congrArg (fun a : lpsOriginalIntegerNormalZeroChart N hN =>
      (a : lpsOriginalGeneratedFunctionFieldQ N hN)) h
    change lpsOriginalIntegerBaseToGeneratedField N hN x =
      lpsOriginalIntegerBaseToGeneratedField N hN y at he
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerBaseFractionMap x) =
      algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerBaseFractionMap y) at he
    exact lpsOriginalIntegerBaseFractionMap_injective ((algebraMap
      (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).injective he)
  let : FaithfulSMul (Polynomial ℤ) (lpsOriginalIntegerNormalZeroChart N hN) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _

lemma lpsOriginalIntegerNormalInfinityChartToJLine_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalInfinityChartToJLine N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalInfinityChart N hN)))
  have hinj : Function.Injective (algebraMap (Polynomial ℤ)
      (lpsOriginalIntegerNormalInfinityChart N hN)) := by
    intro x y h
    have he := congrArg (fun a : lpsOriginalIntegerNormalInfinityChart N hN =>
      (a : lpsOriginalGeneratedFunctionFieldQ N hN)) h
    change lpsOriginalIntegerReciprocalBaseToGeneratedField N hN x =
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN y at he
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerReciprocalBaseFractionMap x) =
      algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerReciprocalBaseFractionMap y) at he
    exact lpsOriginalIntegerReciprocalBaseFractionMap_injective ((algebraMap
      (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).injective he)
  let : FaithfulSMul (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by
  constructor
  intro x
  obtain ⟨b, y, rfl⟩ := lpsOriginalIntegerProjectiveJChartMap_cover x
  have hs : Surjective (lpsOriginalIntegerNormalChartProjection N hN b) := by
    cases b with
    | false => exact lpsOriginalIntegerNormalZeroChartToJLine_surjective N hN
    | true => exact lpsOriginalIntegerNormalInfinityChartToJLine_surjective N hN
  obtain ⟨z, hz⟩ := Scheme.Hom.surjective (lpsOriginalIntegerNormalChartProjection N hN b) y
  refine ⟨lpsOriginalIntegerNormalGluedChartMap N hN b z, ?_⟩
  have hc := lpsOriginalIntegerNormalGluedToProjectiveJ_chart N hN b
  have hp := lpsOriginalIntegerNormalChartProjection_comp N hN b
  exact congrArg (fun f : lpsOriginalIntegerNormalSchemeChart N hN b ⟶
    lpsOriginalIntegerProjectiveJLine => f z) (hc.trans hp.symm) |>.trans (congrArg _ hz)

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_surjective :
    Surjective lpsOriginalIntegerProjectiveJLineToSpecZ := by
  constructor
  intro y
  refine ⟨lpsOriginalIntegerProjectiveJAffinePoint ℤ false 0 y, ?_⟩
  have h := lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ ℤ false 0
  have hi : Spec.map (CommRingCat.ofHom (Int.castRingHom ℤ)) = 𝟙 (Spec (.of ℤ)) := by
    have hr : Int.castRingHom ℤ = RingHom.id ℤ := Subsingleton.elim _ _
    rw [hr]
    exact Spec.map_id _
  exact congrArg (fun f : Spec (.of ℤ) ⟶ Spec (.of ℤ) => f y) (h.trans hi)

lemma lpsOriginalIntegerNormalGluedToSpecZ_surjective
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_surjective N hN
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_surjective
  change Surjective (lpsOriginalIntegerNormalGluedToProjectiveJ N hN ≫
    lpsOriginalIntegerProjectiveJLineToSpecZ)
  infer_instance

lemma lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    LocallyOfFinitePresentation (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let := lpsOriginalIntegerNormalGluedToSpecZ_proper N hN
  infer_instance


end
end QEC.Coding.TannerLiftedProduct
