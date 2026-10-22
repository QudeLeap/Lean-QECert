import QEC.Coding.AlgebraicGeometry.Towers.SourceSeedSplittingIdeals
import QEC.Coding.AlgebraicGeometry.Towers.SourceNormalClosure

import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Coset.Card
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.AlgebraInstances

/-!
# Complete splitting in the source-recursion Garcia--Stichtenoth normal closures

The literal `z=1` place already splits completely in every actual finite
source-recursion extension.  This file proves that the same place splits completely in the
actual normal closure.  The proof does not enumerate the (potentially much
larger) Galois group.  Instead it contracts conjugate closure primes to the
proved seed fibre, factors that contraction through the cosets of the seed
field's fixing subgroup, and proves the resulting finite map bijective from
the exact seed degree.  Normal-closure generation then forces every
decomposition group to be trivial.

No genus, canonical divisor, coordinate enumeration, or asymptotic statement
is made here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

open scoped Pointwise

private noncomputable local instance (priority := 3000)
    sourceGaloisClosureFieldBaseAlgebraPinned (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisClosureField m) :=
  sourceGaloisClosureFieldAlgebra m

private noncomputable local instance (priority := 3000)
    sourceGaloisClosureFieldBaseSMulPinned (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisClosureFieldBaseAlgebraPinned m).toSMul

private noncomputable local instance (priority := 3000)
    sourceGaloisClosureFieldBaseModulePinned (m : ℕ) :
    Module GaloisBaseField (SourceGaloisClosureField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureFieldBaseAlgebraPinned m)

private noncomputable local instance (priority := 3000)
    sourceGaloisClosureGalFinite (m : ℕ) :
    Finite Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
  Fintype.finite
    (AlgEquiv.fintype GaloisBaseField (SourceGaloisClosureField m))

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureSeedBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceField m) :=
  ((algebraMap GaloisBaseField (SourceField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureSeedBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceField m) :=
  (sourceGaloisClosureSeedBaseValuationRingAlgebra m).toSMul

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureSeedBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceField m) _ _
    (sourceGaloisClosureSeedBaseValuationRingAlgebra m)

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  ((algebraMap GaloisBaseField (SourceGaloisClosureField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  (sourceGaloisClosureBaseValuationRingAlgebra m).toSMul

private noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureBaseValuationRingAlgebra m)

/-- The integral closure of the transported `z=1` DVR in normal-closure
level `m`. -/
abbrev SourceGaloisClosureIntegralClosure (m : ℕ) : Type :=
  integralClosure SourceSeedBaseValuationRing (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisClosureBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField
      (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance sourceGaloisClosureSeedBaseScalarTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField (SourceField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance sourceSeedIntegralClosureFractionTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) (SourceField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance sourceGaloisClosureIntegralClosureFractionTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable def sourceSeedIntegralClosureToClosure (m : ℕ) :
    SourceSeedIntegralClosure m →ₐ[SourceSeedBaseValuationRing]
      SourceGaloisClosureIntegralClosure m :=
  ((sourceGaloisSeedToClosure m).restrictScalars
    SourceSeedBaseValuationRing).mapIntegralClosure

private noncomputable local instance sourceSeedIntegralClosureClosureAlgebra
    (m : ℕ) :
    Algebra (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  (sourceSeedIntegralClosureToClosure m).toRingHom.toAlgebra

private noncomputable local instance (priority := 2000)
    sourceSeedIntegralClosureClosureSMul (m : ℕ) :
    SMul (SourceSeedIntegralClosure m) (SourceGaloisClosureIntegralClosure m) :=
  (sourceSeedIntegralClosureClosureAlgebra m).toSMul

private noncomputable local instance (priority := 2000)
    sourceSeedIntegralClosureClosureModule (m : ℕ) :
    Module (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  @Algebra.toModule (SourceSeedIntegralClosure m)
    (SourceGaloisClosureIntegralClosure m) _ _
      (sourceSeedIntegralClosureClosureAlgebra m)

private theorem sourceSeedIntegralClosureToClosure_coe (m : ℕ)
    (x : SourceSeedIntegralClosure m) :
    ((algebraMap (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) x :
        SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) =
      sourceGaloisSeedToClosure m (x : SourceField m) :=
  rfl

private noncomputable local instance
    sourceGaloisClosureIntegralClosureScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) (SourceGaloisClosureIntegralClosure m) :=
  IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro r
    apply IsIntegralClosure.algebraMap_injective
      (SourceGaloisClosureIntegralClosure m) SourceSeedBaseValuationRing
        (SourceGaloisClosureField m)
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply
      SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m)
        (SourceGaloisClosureField m)]
    change algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m) r =
      ((algebraMap (SourceSeedIntegralClosure m)
        (SourceGaloisClosureIntegralClosure m)
          (algebraMap SourceSeedBaseValuationRing
            (SourceSeedIntegralClosure m) r) :
              SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m)
    rw [sourceSeedIntegralClosureToClosure_coe]
    change algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m) r =
      sourceGaloisSeedToClosure m
        (algebraMap (SourceSeedIntegralClosure m) (SourceField m)
          (algebraMap SourceSeedBaseValuationRing
            (SourceSeedIntegralClosure m) r))
    rw [← IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        (SourceSeedIntegralClosure m) (SourceField m),
      IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        GaloisBaseField (SourceField m),
      (sourceGaloisSeedToClosure m).commutes,
      ← IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        GaloisBaseField (SourceGaloisClosureField m)]

private noncomputable local instance sourceGaloisClosureIntegralOverSeedIntegral
    (m : ℕ) :
    Algebra.IsIntegral (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  Algebra.IsIntegral.tower_top SourceSeedBaseValuationRing

private theorem sourceSeedIntegralClosureToClosure_injective (m : ℕ) :
    Function.Injective (algebraMap (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m)) := by
  intro x y hxy
  apply Subtype.ext
  apply (sourceGaloisSeedToClosure m).injective
  calc
    sourceGaloisSeedToClosure m (x : SourceField m) =
        ((algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) x :
            SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) :=
      (sourceSeedIntegralClosureToClosure_coe m x).symm
    _ = ((algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) y :
            SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) :=
      congrArg (fun z : SourceGaloisClosureIntegralClosure m =>
        (z : SourceGaloisClosureField m)) hxy
    _ = sourceGaloisSeedToClosure m (y : SourceField m) :=
      sourceSeedIntegralClosureToClosure_coe m y

private noncomputable local instance sourceGaloisClosureIntegralOverSeedTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (sourceSeedIntegralClosureToClosure_injective m)

private noncomputable local instance sourceGaloisClosureIntegralClosureTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureField m) := by
    apply Module.IsTorsionFree.comap
      (R := SourceSeedBaseValuationRing)
      (S := SourceGaloisClosureField m)
      (M := SourceGaloisClosureField m)
      (algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m))
    · intro r hr
      have hinjective : Function.Injective
          (algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m)) :=
        (algebraMap GaloisBaseField (SourceGaloisClosureField m)).injective.comp
          (ValuationSubring.subtype_injective
            sourceSeedFixedBaseOnePlace.valuationRing)
      exact IsRegular.of_ne_zero fun hzero =>
        hr.ne_zero (hinjective (by simpa only [map_zero] using hzero))
    · intro r x
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisClosureIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
      (SourceGaloisClosureIntegralClosure m)

private noncomputable local instance
    sourceGaloisClosureIntegralClosureIsFractionRing (m : ℕ) :
    IsFractionRing (SourceGaloisClosureIntegralClosure m)
      (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension
    GaloisBaseField (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisClosureIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisClosureIntegralClosureAction
    (m : ℕ) :
    MulSemiringAction
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (SourceGaloisClosureIntegralClosure m) :=
  IsIntegralClosure.MulSemiringAction SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
      (SourceGaloisClosureIntegralClosure m)

private noncomputable local instance (priority := 3000)
    sourceGaloisClosureIntegralClosureSMul (m : ℕ) :
    SMul Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (SourceGaloisClosureIntegralClosure m) :=
  (sourceGaloisClosureIntegralClosureAction m).toDistribMulAction.toMulAction.toSMul

private noncomputable local instance (priority := 3000)
    sourceGaloisClosureIntegralClosureIdealAction (m : ℕ) :
    MulSemiringAction
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (Ideal (SourceGaloisClosureIntegralClosure m)) :=
  Ideal.pointwiseMulSemiringAction

private noncomputable local instance (priority := 4000)
    sourceGaloisClosureIntegralClosureIdealMulAction (m : ℕ) :
    MulAction
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (Ideal (SourceGaloisClosureIntegralClosure m)) :=
  (sourceGaloisClosureIntegralClosureIdealAction m).toDistribMulAction.toMulAction

private noncomputable local instance
    sourceGaloisClosureIntegralClosureActionCommutesWithBase (m : ℕ) :
    SMulCommClass
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m) where
  smul_comm g r x := by
    apply IsIntegralClosure.algebraMap_injective
      (SourceGaloisClosureIntegralClosure m) SourceSeedBaseValuationRing
        (SourceGaloisClosureField m)
    calc
      algebraMap (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)
          (g • (r • x)) =
          g (algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) (r • x)) :=
        algebraMap_galRestrict_apply
          SourceSeedBaseValuationRing g (r • x)
      _ = g (algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m) r *
          algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) x) := by
        rw [Algebra.smul_def, map_mul,
          IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
            (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)]
      _ = algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m) r *
          g (algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) x) := by
        rw [map_mul]
        congr 1
        exact g.commutes (r : GaloisBaseField)
      _ = algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m) r *
          algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) (g • x) := by
        congr 1
        exact (algebraMap_galRestrict_apply
          SourceSeedBaseValuationRing g x).symm
      _ = algebraMap (SourceGaloisClosureIntegralClosure m)
          (SourceGaloisClosureField m) (r • (g • x)) := by
        rw [Algebra.smul_def, map_mul,
          IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
            (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)]

private noncomputable local instance sourceGaloisClosureIntegralClosureIsGaloisGroup
    (m : ℕ) :
    IsGaloisGroup
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m) :=
  IsGaloisGroup.of_isFractionRing
    Gal((SourceGaloisClosureField m) / GaloisBaseField)
    SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m)
    GaloisBaseField (SourceGaloisClosureField m)

private abbrev sourceSeedClosureFieldRange (m : ℕ) :
    IntermediateField GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisSeedToClosure m).fieldRange

private noncomputable local instance (priority := 3000)
    sourceSeedClosureFieldRangeAlgebra (m : ℕ) :
    Algebra GaloisBaseField (sourceSeedClosureFieldRange m) :=
  IntermediateField.algebra' (sourceSeedClosureFieldRange m)

private noncomputable local instance (priority := 3000)
    sourceSeedClosureFieldRangeSMul (m : ℕ) :
    SMul GaloisBaseField (sourceSeedClosureFieldRange m) :=
  (sourceSeedClosureFieldRangeAlgebra m).toSMul

private noncomputable local instance (priority := 3000)
    sourceSeedClosureFieldRangeModule (m : ℕ) :
    Module GaloisBaseField (sourceSeedClosureFieldRange m) :=
  @Algebra.toModule GaloisBaseField (sourceSeedClosureFieldRange m) _ _
    (sourceSeedClosureFieldRangeAlgebra m)

private abbrev sourceSeedClosureFixingSubgroup (m : ℕ) :
    Subgroup Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
  (sourceSeedClosureFieldRange m).fixingSubgroup

private theorem sourceSeedClosureFixingSubgroup_smul_algebraMap (m : ℕ)
    (h : sourceSeedClosureFixingSubgroup m)
    (b : SourceSeedIntegralClosure m) :
    (h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
        algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) b =
      algebraMap (SourceSeedIntegralClosure m)
        (SourceGaloisClosureIntegralClosure m) b := by
  apply IsIntegralClosure.algebraMap_injective
    (SourceGaloisClosureIntegralClosure m) SourceSeedBaseValuationRing
      (SourceGaloisClosureField m)
  have hcoe : algebraMap (SourceGaloisClosureIntegralClosure m)
      (SourceGaloisClosureField m)
        (algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) b) =
      sourceGaloisSeedToClosure m (b : SourceField m) := by
    change ((algebraMap (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) b :
        SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) = _
    exact sourceSeedIntegralClosureToClosure_coe m b
  calc
    algebraMap (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)
        ((h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
          algebraMap (SourceSeedIntegralClosure m)
            (SourceGaloisClosureIntegralClosure m) b) =
        (h : Gal((SourceGaloisClosureField m) / GaloisBaseField))
          (algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m)
              (algebraMap (SourceSeedIntegralClosure m)
                (SourceGaloisClosureIntegralClosure m) b)) :=
      algebraMap_galRestrict_apply SourceSeedBaseValuationRing
        (h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) _
    _ = (h : Gal((SourceGaloisClosureField m) / GaloisBaseField))
        (sourceGaloisSeedToClosure m (b : SourceField m)) := by rw [hcoe]
    _ = sourceGaloisSeedToClosure m (b : SourceField m) :=
      h.2 ⟨sourceGaloisSeedToClosure m (b : SourceField m), ⟨(b : SourceField m), rfl⟩⟩
    _ = algebraMap (SourceGaloisClosureIntegralClosure m)
        (SourceGaloisClosureField m)
          (algebraMap (SourceSeedIntegralClosure m)
            (SourceGaloisClosureIntegralClosure m) b) := hcoe.symm

private theorem sourceSeedClosureFixingSubgroup_contraction_eq (m : ℕ)
    (P : Ideal (SourceGaloisClosureIntegralClosure m))
    (h : sourceSeedClosureFixingSubgroup m) :
    (((h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) • P).under
        (SourceSeedIntegralClosure m)) =
      P.under (SourceSeedIntegralClosure m) := by
  ext b
  have hfix :
      ((h : Gal((SourceGaloisClosureField m) / GaloisBaseField))⁻¹) •
          algebraMap (SourceSeedIntegralClosure m)
            (SourceGaloisClosureIntegralClosure m) b =
        algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) b := by
    simpa only [Subgroup.coe_inv] using
      (sourceSeedClosureFixingSubgroup_smul_algebraMap m h⁻¹ b)
  rw [Ideal.mem_under, Ideal.mem_under,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, hfix]

private noncomputable def sourceGaloisClosureConjugateContraction (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    (g : Gal((SourceGaloisClosureField m) / GaloisBaseField)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m) := by
  let p : Ideal SourceSeedBaseValuationRing :=
    IsLocalRing.maximalIdeal SourceSeedBaseValuationRing
  let Q : Ideal (SourceGaloisClosureIntegralClosure m) := g⁻¹ • P.1
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : Q.LiesOver p := by
    dsimp only [Q]
    exact Ideal.LiesOver.smul
      (A := SourceSeedBaseValuationRing) (P := P.1) (g := g⁻¹)
  letI : (Q.under (SourceSeedIntegralClosure m)).LiesOver p :=
    Ideal.under_liesOver_of_liesOver (SourceSeedIntegralClosure m) Q p
  exact Ideal.primesOver.mk p (Q.under (SourceSeedIntegralClosure m))

private theorem sourceGaloisClosureConjugateContraction_eq_of_leftRel (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    (x y : Gal((SourceGaloisClosureField m) / GaloisBaseField))
    (hxy : QuotientGroup.leftRel (sourceSeedClosureFixingSubgroup m) x y) :
    sourceGaloisClosureConjugateContraction m P x =
      sourceGaloisClosureConjugateContraction m P y := by
  let h : sourceSeedClosureFixingSubgroup m :=
    ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp hxy⟩
  have hy : y = x * (h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) := by
    simp only [h, mul_inv_cancel_left]
  apply Subtype.ext
  change (x⁻¹ • P.1).under (SourceSeedIntegralClosure m) =
    (y⁻¹ • P.1).under (SourceSeedIntegralClosure m)
  calc
    (x⁻¹ • P.1).under (SourceSeedIntegralClosure m) =
        (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
            Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
          (x⁻¹ • P.1)).under (SourceSeedIntegralClosure m) :=
      (sourceSeedClosureFixingSubgroup_contraction_eq m
        (x⁻¹ • P.1) h⁻¹).symm
    _ = (y⁻¹ • P.1).under (SourceSeedIntegralClosure m) := by
      have hginv :
          (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
              Gal((SourceGaloisClosureField m) / GaloisBaseField)) * x⁻¹) = y⁻¹ := by
        rw [hy, mul_inv_rev]
        rfl
      have haction :
          (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
              Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
            (x⁻¹ • P.1)) = y⁻¹ • P.1 := by
        rw [← hginv]
        ext z
        simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
          mul_inv_rev]
        let a : Gal((SourceGaloisClosureField m) / GaloisBaseField) := x⁻¹⁻¹
        let b : Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
          (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
            Gal((SourceGaloisClosureField m) / GaloisBaseField))⁻¹)
        change a • (b • z) ∈ P.1 ↔ (a * b) • z ∈ P.1
        have hz : a • (b • z) = (a * b) • z :=
          ((sourceGaloisClosureIntegralClosureAction m).toDistribMulAction.toMulAction
            |>.mul_smul a b z).symm
        rw [hz]
      exact congrArg
        (fun I : Ideal (SourceGaloisClosureIntegralClosure m) =>
          I.under (SourceSeedIntegralClosure m)) haction

private noncomputable def sourceGaloisClosureCosetContraction (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
        sourceSeedClosureFixingSubgroup m) →
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m) :=
  Quotient.lift (sourceGaloisClosureConjugateContraction m P)
    (sourceGaloisClosureConjugateContraction_eq_of_leftRel m P)

private theorem sourceGaloisClosureCosetContraction_surjective (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    Function.Surjective (sourceGaloisClosureCosetContraction m P) := by
  let p : Ideal SourceSeedBaseValuationRing :=
    IsLocalRing.maximalIdeal SourceSeedBaseValuationRing
  intro Q
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver p := Q.2.2
  letI : FaithfulSMul (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (sourceSeedIntegralClosureToClosure_injective m)
  obtain ⟨R⟩ := Q.1.nonempty_primesOver
    (S := SourceGaloisClosureIntegralClosure m)
  letI : R.1.IsPrime := R.2.1
  letI : R.1.LiesOver Q.1 := R.2.2
  letI : R.1.LiesOver p := Ideal.LiesOver.trans R.1 Q.1 p
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    p P.1 R.1 Gal((SourceGaloisClosureField m) / GaloisBaseField)
  refine ⟨Quotient.mk'' g⁻¹, ?_⟩
  change sourceGaloisClosureConjugateContraction m P g⁻¹ = Q
  apply Subtype.ext
  change ((g⁻¹)⁻¹ • P.1).under (SourceSeedIntegralClosure m) = Q.1
  rw [inv_inv, hg]
  exact R.2.2.over.symm

private theorem sourceGaloisClosureCoset_card (m : ℕ) :
    Nat.card (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
      sourceSeedClosureFixingSubgroup m) = 240 * 16 ^ m := by
  letI : Module GaloisBaseField
      (LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap) :=
    SMulMemClass.toModule
      (LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap)
  let rangeLinearEquiv : sourceSeedClosureFieldRange m ≃ₗ[GaloisBaseField]
      LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap :=
    { toFun := fun x : sourceSeedClosureFieldRange m =>
        (⟨x.1, x.2⟩ : LinearMap.range
          (sourceGaloisSeedToClosure m).toLinearMap)
      invFun := fun x : LinearMap.range
          (sourceGaloisSeedToClosure m).toLinearMap =>
        (⟨x.1, x.2⟩ : sourceSeedClosureFieldRange m)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  calc
    Nat.card (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
        sourceSeedClosureFixingSubgroup m) =
        (sourceSeedClosureFixingSubgroup m).index :=
      (sourceSeedClosureFixingSubgroup m).index_eq_card.symm
    _ = Module.finrank GaloisBaseField (sourceSeedClosureFieldRange m) :=
      (IntermediateField.finrank_eq_fixingSubgroup_index
        (SourceGaloisClosureField m) (sourceSeedClosureFieldRange m)).symm
    _ = Module.finrank GaloisBaseField
        (LinearMap.range (sourceGaloisSeedToClosure m).toLinearMap) :=
      rangeLinearEquiv.finrank_eq
    _ = Module.finrank GaloisBaseField (SourceField m) :=
      LinearMap.finrank_range_of_inj (sourceGaloisSeedToClosure m).injective
    _ = 240 * 16 ^ m := sourceSeed_fixedBase_finrank m

private theorem sourceGaloisClosureCosetContraction_bijective (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    Function.Bijective (sourceGaloisClosureCosetContraction m P) := by
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨sourceGaloisClosureCosetContraction_surjective m P, ?_⟩
  calc
    Nat.card (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
        sourceSeedClosureFixingSubgroup m) = 240 * 16 ^ m :=
      sourceGaloisClosureCoset_card m
    _ = ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m)).ncard :=
      (sourceSeed_primesOver_ncard m).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
          (SourceSeedIntegralClosure m)) :=
      (Nat.card_coe_set_eq _).symm

private theorem sourceGaloisClosurePrime_stabilizer_le_fixingSubgroup (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    MulAction.stabilizer
        Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1 ≤
      sourceSeedClosureFixingSubgroup m := by
  intro d hd
  have hmap :
      sourceGaloisClosureCosetContraction m P (Quotient.mk'' d⁻¹) =
        sourceGaloisClosureCosetContraction m P (Quotient.mk'' 1) := by
    apply Subtype.ext
    change ((d⁻¹)⁻¹ • P.1).under (SourceSeedIntegralClosure m) =
      ((1 : Gal((SourceGaloisClosureField m) / GaloisBaseField))⁻¹ • P.1).under
        (SourceSeedIntegralClosure m)
    rw [inv_inv, inv_one, one_smul, MulAction.mem_stabilizer_iff.mp hd]
  have hquot := (sourceGaloisClosureCosetContraction_bijective m P).1 hmap
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hquot)
  simpa using hrel

private theorem sourceGaloisClosurePrime_stabilizer_conj_mem_fixingSubgroup
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    {d : Gal((SourceGaloisClosureField m) / GaloisBaseField)}
    (hd : d ∈ MulAction.stabilizer
      Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1)
    (g : Gal((SourceGaloisClosureField m) / GaloisBaseField)) :
    g⁻¹ * d * g ∈ sourceSeedClosureFixingSubgroup m := by
  let Q : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m) :=
    ⟨g⁻¹ • P.1, P.2.1.smul g⁻¹, P.2.2.smul g⁻¹⟩
  apply sourceGaloisClosurePrime_stabilizer_le_fixingSubgroup m Q
  rw [MulAction.mem_stabilizer_iff]
  change (g⁻¹ * d * g) • (g⁻¹ • P.1) = g⁻¹ • P.1
  simp only [mul_smul, smul_inv_smul,
    MulAction.mem_stabilizer_iff.mp hd]

private theorem sourceGaloisClosurePrime_stabilizer_fixes_seedEmbedding
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    {d : Gal((SourceGaloisClosureField m) / GaloisBaseField)}
    (hd : d ∈ MulAction.stabilizer
      Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (x : SourceField m) :
    d (f x) = f x := by
  let g : Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
    AlgEquiv.ofBijective (f.liftNormal (SourceGaloisClosureField m))
      (AlgHom.normal_bijective GaloisBaseField
        (SourceGaloisClosureField m) (SourceGaloisClosureField m)
          (f.liftNormal (SourceGaloisClosureField m)))
  have hg : g (sourceGaloisSeedToClosure m x) = f x := by
    change (f.liftNormal (SourceGaloisClosureField m))
        (algebraMap (SourceField m) (SourceGaloisClosureField m) x) =
      algebraMap (SourceGaloisClosureField m) (SourceGaloisClosureField m) (f x)
    exact AlgHom.liftNormal_commutes f (SourceGaloisClosureField m) x
  have hconj :=
    sourceGaloisClosurePrime_stabilizer_conj_mem_fixingSubgroup m P hd g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hconj
  have hseed := hconj (sourceGaloisSeedToClosure m x) ⟨x, rfl⟩
  have happlied := congrArg (fun z : SourceGaloisClosureField m => g z) hseed
  simpa only [AlgEquiv.mul_apply, AlgEquiv.aut_inv,
    AlgEquiv.apply_symm_apply, hg] using happlied

private theorem sourceGaloisClosurePrime_stabilizer_eq_bot (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    MulAction.stabilizer
        Gal((SourceGaloisClosureField m) / GaloisBaseField) P.1 = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro d hd
  have hnormalTop :
      IntermediateField.normalClosure GaloisBaseField (SourceField m)
          (SourceGaloisClosureField m) = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure GaloisBaseField (SourceField m)
        (SourceGaloisClosureField m))).2
  have hle :
      IntermediateField.normalClosure GaloisBaseField (SourceField m)
          (SourceGaloisClosureField m) ≤
        FixedBy.intermediateField GaloisBaseField (SourceGaloisClosureField m) d := by
    rw [normalClosure_le_iff]
    intro f z hz
    rw [FixedBy.intermediateField_mem_iff]
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hz
    exact sourceGaloisClosurePrime_stabilizer_fixes_seedEmbedding m P hd f x
  apply AlgEquiv.ext
  intro z
  have hz : z ∈ FixedBy.intermediateField GaloisBaseField
      (SourceGaloisClosureField m) d := by
    apply hle
    rw [hnormalTop]
    exact IntermediateField.mem_top
  rw [FixedBy.intermediateField_mem_iff] at hz
  exact hz

/-- The prime fibre above the literal `z=1` place has cardinality equal to
the full normal-closure degree. -/
theorem sourceGaloisClosure_primesOver_ncard_eq_finrank (m : ℕ) :
    ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)).ncard =
        Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / GaloisBaseField)
  letI : p.IsPrime := inferInstance
  letI : FaithfulSMul O C :=
    (faithfulSMul_iff_algebraMap_injective O C).2 (by
      intro a b hab
      apply ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing
      apply (algebraMap GaloisBaseField (SourceGaloisClosureField m)).injective
      exact congrArg (fun z : C => (z : SourceGaloisClosureField m)) hab)
  obtain ⟨P⟩ := (inferInstance : Nonempty (p.primesOver C))
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  have horbit : MulAction.orbit G P.1 = p.primesOver C :=
    Algebra.IsInvariant.orbit_eq_primesOver O C G p P.1
  calc
    (p.primesOver C).ncard = (MulAction.orbit G P.1).ncard :=
      congrArg Set.ncard horbit.symm
    _ = (MulAction.stabilizer G P.1).index :=
      (MulAction.index_stabilizer G P.1).symm
    _ = (⊥ : Subgroup G).index := by
      rw [sourceGaloisClosurePrime_stabilizer_eq_bot m P]
    _ = Nat.card G := Subgroup.index_bot
    _ = Module.finrank GaloisBaseField (SourceGaloisClosureField m) :=
      IsGalois.card_aut_eq_finrank GaloisBaseField (SourceGaloisClosureField m)

private theorem sourceGaloisClosure_ramificationIdxIn_mul_inertiaDegIn_eq_one
    (m : ℕ) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdxIn
          (SourceGaloisClosureIntegralClosure m) *
        (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDegIn
          (SourceGaloisClosureIntegralClosure m) = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / GaloisBaseField)
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O C := by
    change Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m)
    exact sourceGaloisClosureIntegralClosureTorsionFree m
  letI : Module.Finite O C := by
    change Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m)
    exact sourceGaloisClosureIntegralClosureFinite m
  have hfundamental :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      p C G
  rw [sourceGaloisClosure_primesOver_ncard_eq_finrank m,
    IsGalois.card_aut_eq_finrank GaloisBaseField (SourceGaloisClosureField m)]
      at hfundamental
  have hcancel :
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) *
          (p.ramificationIdxIn C * p.inertiaDegIn C) =
        Module.finrank GaloisBaseField (SourceGaloisClosureField m) * 1 := by
    simpa only [Nat.mul_one] using hfundamental
  have hproductIn : p.ramificationIdxIn C * p.inertiaDegIn C = 1 :=
    Nat.mul_left_cancel
      (lt_of_lt_of_le (by positivity) (sourceGaloisClosureField_finrank_lower_bound m))
      hcancel
  exact hproductIn

private theorem sourceGaloisClosure_ramificationIdx_mul_inertiaDeg_eq_one
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx' P.1 *
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg' P.1 = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / GaloisBaseField)
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  letI : p.IsMaximal := inferInstance
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  have hP0 : P.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp0 P.2
  letI : P.1.IsMaximal := P.2.1.isMaximal hP0
  have hproductIn : p.ramificationIdxIn C * p.inertiaDegIn C = 1 :=
    sourceGaloisClosure_ramificationIdxIn_mul_inertiaDegIn_eq_one m
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P.1 G,
    Ideal.inertiaDegIn_eq_inertiaDeg p P.1 G] at hproductIn
  change p.ramificationIdx' P.1 * p.inertiaDeg' P.1 = 1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p P.1 hp0,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  exact hproductIn

/-- Every prime above the literal `z=1` place has ramification index one in
the normal closure. -/
theorem sourceGaloisClosure_ramificationIdx_eq_one (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  exact ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).inertiaDeg' P.1,
    (sourceGaloisClosure_ramificationIdx_mul_inertiaDeg_eq_one m P).symm⟩

/-- Every prime above the literal `z=1` place has inertia degree one in the
normal closure. -/
theorem sourceGaloisClosure_inertiaDeg_eq_one (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).ramificationIdx' P.1, ?_⟩
  calc
    1 = (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).ramificationIdx' P.1 *
        (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).inertiaDeg' P.1 :=
      (sourceGaloisClosure_ramificationIdx_mul_inertiaDeg_eq_one m P).symm
    _ = (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).inertiaDeg' P.1 *
        (IsLocalRing.maximalIdeal
          SourceSeedBaseValuationRing).ramificationIdx' P.1 := Nat.mul_comm _ _

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
