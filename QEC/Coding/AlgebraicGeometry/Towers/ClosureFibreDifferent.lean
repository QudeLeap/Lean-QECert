import QEC.Coding.AlgebraicGeometry.Towers.ClosureDifferent
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWGlobalPlaces

/-!
# The two literal w-fibre different formulas

These are consequences of the proved all-prime normal-closure theorem on
the existing zero/infinity integral carriers and actual prime fibres.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree

variable (m : ℕ)

local instance fibreDifferent_baseAlgebra (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Algebra P.valuationRing (sourceClosureWBase m) :=
  inferInstanceAs (Algebra P.valuationRing (SourceGaloisWClosureField m))

local instance fibreDifferent_baseFraction (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsFractionRing P.valuationRing (sourceClosureWBase m) :=
  inferInstanceAs (IsFractionRing P.valuationRing (SourceGaloisWClosureField m))

local instance fibreDifferent_baseFaithful (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    FaithfulSMul P.valuationRing (sourceClosureWBase m) := by
  apply (faithfulSMul_iff_algebraMap_injective P.valuationRing (sourceClosureWBase m)).mpr
  exact ValuationSubring.subtype_injective P.valuationRing

local instance fibreDifferent_baseDVR (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsDiscreteValuationRing P.valuationRing := P.valuationRing_isDiscreteValuationRing

local instance fibreDifferent_ambientAlgebra (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Algebra P.valuationRing (SourceGaloisClosureField m) :=
  ((algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).comp
    (algebraMap P.valuationRing (sourceClosureWBase m))).toAlgebra

local instance fibreDifferent_baseTower (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsScalarTower P.valuationRing (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance fibreDifferent_ambientTorsionFree (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module.IsTorsionFree P.valuationRing (SourceGaloisClosureField m) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  change Function.Injective ((algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).comp
    (algebraMap P.valuationRing (sourceClosureWBase m)))
  exact (algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).injective.comp
    (ValuationSubring.subtype_injective P.valuationRing)

/-- The actual different ideal for a supplied place of the literal `k(w)`
base. It is formed on its ordinary integral closure, with no formula stored. -/
def sourceClosurePlaceDifferentIdeal (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Ideal (integralClosure P.valuationRing (SourceGaloisClosureField m)) :=
  differentIdeal P.valuationRing (integralClosure P.valuationRing (SourceGaloisClosureField m))

set_option maxHeartbeats 1000000 in
/-- The different at every genuine zero-fibre prime is `2(α-1)`, where
`α` is the already constructed common Galois ramification index. -/
theorem sourceClosureWZeroDifferentMultiplicity (P : SourceGaloisWZeroPrime m) :
    multiplicity P.1 (sourceClosurePlaceDifferentIdeal m (sourceGaloisWClosureZeroPlace m)) =
      2 * (sourceGaloisWZeroRamificationIndex m - 1) := by
  let A := (sourceGaloisWClosureZeroPlace m).valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWZeroUpperHeightOne m P
  letI : Algebra A (sourceClosureWBase m) := fibreDifferent_baseAlgebra m (sourceGaloisWClosureZeroPlace m)
  letI : IsFractionRing A (sourceClosureWBase m) := fibreDifferent_baseFraction m (sourceGaloisWClosureZeroPlace m)
  letI : IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    fibreDifferent_baseTower m (sourceGaloisWClosureZeroPlace m)
  have h := sourceClosureW_integralModel_weakDifferent m A Q
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hp] at h
  rw [sourceGaloisWZeroRamificationIndex_eq_prime m P]
  exact h

set_option maxHeartbeats 1000000 in
/-- The different at every genuine infinity-fibre prime is `2(β-1)`, with
the existing common Galois ramification index `β`. -/
theorem sourceClosureWInfinityDifferentMultiplicity (P : SourceGaloisWInfinityPrime m) :
    multiplicity P.1 (sourceClosurePlaceDifferentIdeal m (sourceGaloisWClosureInfinityPlace m)) =
      2 * (sourceGaloisWInfinityRamificationIndex m - 1) := by
  let A := (sourceGaloisWClosureInfinityPlace m).valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWInfinityUpperHeightOne m P
  letI : Algebra A (sourceClosureWBase m) := fibreDifferent_baseAlgebra m (sourceGaloisWClosureInfinityPlace m)
  letI : IsFractionRing A (sourceClosureWBase m) := fibreDifferent_baseFraction m (sourceGaloisWClosureInfinityPlace m)
  letI : IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    fibreDifferent_baseTower m (sourceGaloisWClosureInfinityPlace m)
  have h := sourceClosureW_integralModel_weakDifferent m A Q
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hp] at h
  rw [sourceGaloisWInfinityRamificationIndex_eq_prime m P]
  exact h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
