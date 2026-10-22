import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisSelectedPlaces
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWClosurePlaces

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.AlgebraInstances

/-!
# The zero and infinity fibres over the source F256(w)

For each normal-closure level, this file forms the integral closure of the
actual valuation rings at zero and infinity of the embedded field `F256(w)`.
It then defines the genuine upper-prime fibres and their common Galois
ramification and inertia indices.

The fundamental identities below count these actual fibres with their
ramification and residue-degree weights.  No value of either ramification
index, no different, divisor, genus, or canonical differential is asserted
here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private abbrev SourceGaloisWPlaceValuationRing (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) : Type :=
  P.valuationRing

private noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingBaseModule (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWClosureField m) :=
  @Algebra.toModule (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) _ _
      (inferInstance : Algebra (SourceGaloisWPlaceValuationRing m P)
        (SourceGaloisWClosureField m))

private noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingBaseFaithfulSMul (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    FaithfulSMul (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWClosureField m) :=
  (faithfulSMul_iff_algebraMap_injective
    (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWClosureField m)).2
      (ValuationSubring.subtype_injective P.valuationRing)

private noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureAlgebra (m : ℕ) :
    Algebra (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  (SourceGaloisWClosureField m).val.toRingHom.toAlgebra

private noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureSMul (m : ℕ) :
    SMul (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  (sourceGaloisWClosureFieldClosureAlgebra m).toSMul

private noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureModule (m : ℕ) :
    Module (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  @Algebra.toModule (SourceGaloisWClosureField m) (SourceGaloisClosureField m) _ _
    (sourceGaloisWClosureFieldClosureAlgebra m)

private noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureFree (m : ℕ) :
    Module.Free (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  Module.Free.of_divisionRing (SourceGaloisWClosureField m) (SourceGaloisClosureField m)

private noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldBaseFree (m : ℕ) :
    Module.Free GaloisBaseField (SourceGaloisWClosureField m) :=
  Module.Free.of_divisionRing GaloisBaseField (SourceGaloisWClosureField m)

private noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureFaithfulSMul (m : ℕ) :
    FaithfulSMul (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  (faithfulSMul_iff_algebraMap_injective
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)).2
      (SourceGaloisWClosureField m).val.injective

private noncomputable local instance sourceGaloisWClosureFieldClosureScalarTower
    (m : ℕ) :
    IsScalarTower GaloisBaseField (SourceGaloisWClosureField m)
      (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance
    sourceGaloisWClosureFieldClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree (SourceGaloisWClosureField m)
      (SourceGaloisClosureField m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (SourceGaloisWClosureField m).val.injective

private noncomputable local instance
    sourceGaloisWClosureFieldClosureFiniteDimensional (m : ℕ) :
    FiniteDimensional (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  FiniteDimensional.right GaloisBaseField (SourceGaloisWClosureField m)
    (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisWClosureFieldClosureIsGalois
    (m : ℕ) :
    IsGalois (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  IsGalois.tower_top_of_isGalois GaloisBaseField
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)

private noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingClosureAlgebra (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Algebra (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m) :=
  ((algebraMap (SourceGaloisWClosureField m) (SourceGaloisClosureField m)).comp
    (algebraMap (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWClosureField m))).toAlgebra

private noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingClosureSMul (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    SMul (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m) :=
  (sourceGaloisWPlaceValuationRingClosureAlgebra m P).toSMul

private noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingClosureModule (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m) :=
  @Algebra.toModule (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisClosureField m) _ _
      (sourceGaloisWPlaceValuationRingClosureAlgebra m P)

private abbrev SourceGaloisWPlaceIntegralClosure (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) : Type :=
  integralClosure (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisWPlaceBaseScalarTower (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsScalarTower (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance
    sourceGaloisWPlaceIntegralClosureFractionTower (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsScalarTower (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance sourceGaloisWRelativeGalFinite (m : ℕ) :
    Finite Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m)) :=
  Fintype.finite
    (AlgEquiv.fintype (SourceGaloisWClosureField m) (SourceGaloisClosureField m))

private noncomputable local instance sourceGaloisWPlaceIntegralClosureTorsionFree
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module.IsTorsionFree (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) := by
  letI : Module.IsTorsionFree (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisClosureField m) :=
    Module.IsTorsionFree.trans_faithfulSMul
      (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWClosureField m)
        (SourceGaloisClosureField m)
  exact IsIntegralClosure.isTorsionFree
    (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisWPlaceIntegralClosureFaithfulSMul
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    FaithfulSMul (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    intro a b hab
    apply ValuationSubring.subtype_injective P.valuationRing
    apply (SourceGaloisWClosureField m).val.injective
    exact congrArg (fun z : SourceGaloisWPlaceIntegralClosure m P =>
      (z : SourceGaloisClosureField m)) hab)

private noncomputable local instance sourceGaloisWPlaceIntegralClosureFinite
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module.Finite (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) := by
  letI : IsDiscreteValuationRing (SourceGaloisWPlaceValuationRing m P) :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
      (SourceGaloisWPlaceIntegralClosure m P)

private noncomputable local instance
    sourceGaloisWPlaceIntegralClosureIsFractionRing (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsFractionRing (SourceGaloisWPlaceIntegralClosure m P)
      (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisWPlaceIntegralClosureIsDedekind
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsDedekindDomain (SourceGaloisWPlaceIntegralClosure m P) := by
  letI : IsDiscreteValuationRing (SourceGaloisWPlaceValuationRing m P) :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)

private noncomputable local instance sourceGaloisWPlaceIntegralClosureAction
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    MulSemiringAction
      Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
      (SourceGaloisWPlaceIntegralClosure m P) :=
  IsIntegralClosure.MulSemiringAction (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
      (SourceGaloisWPlaceIntegralClosure m P)

private noncomputable local instance sourceGaloisWPlaceIntegralClosureIsGaloisGroup
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsGaloisGroup
      Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
      (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) :=
  IsGaloisGroup.of_isFractionRing
    Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
    (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWPlaceIntegralClosure m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)

/-- The integral closure of the actual zero-place valuation ring of
`F256(w)` in normal-closure level `m`. -/
abbrev SourceGaloisWZeroIntegralClosure (m : ℕ) : Type :=
  SourceGaloisWPlaceIntegralClosure m (sourceGaloisWClosureZeroPlace m)

/-- The integral closure of the actual infinity-place valuation ring of
`F256(w)` in normal-closure level `m`. -/
abbrev SourceGaloisWInfinityIntegralClosure (m : ℕ) : Type :=
  SourceGaloisWPlaceIntegralClosure m (sourceGaloisWClosureInfinityPlace m)

/-- The genuine prime fibre over the zero place of `F256(w)`. -/
abbrev SourceGaloisWZeroPrime (m : ℕ) :
    Set (Ideal (SourceGaloisWZeroIntegralClosure m)) :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureZeroPlace m).valuationRing).primesOver
      (SourceGaloisWZeroIntegralClosure m)

/-- The genuine prime fibre over the infinity place of `F256(w)`. -/
abbrev SourceGaloisWInfinityPrime (m : ℕ) :
    Set (Ideal (SourceGaloisWInfinityIntegralClosure m)) :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureInfinityPlace m).valuationRing).primesOver
      (SourceGaloisWInfinityIntegralClosure m)

/-- The zero-place upper-prime fibre is nonempty. -/
theorem sourceGaloisWZeroPrime_nonempty (m : ℕ) :
    Nonempty (SourceGaloisWZeroPrime m) := by
  let O := (sourceGaloisWClosureZeroPlace m).valuationRing
  let C := SourceGaloisWZeroIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  letI : p.IsPrime := inferInstance
  letI : Algebra.IsIntegral O C := integralClosure.AlgebraIsIntegral
  letI : Module.IsTorsionFree O C := by
    exact sourceGaloisWPlaceIntegralClosureTorsionFree m
      (sourceGaloisWClosureZeroPlace m)
  exact Ideal.nonempty_primesOver p

/-- The infinity-place upper-prime fibre is nonempty. -/
theorem sourceGaloisWInfinityPrime_nonempty (m : ℕ) :
    Nonempty (SourceGaloisWInfinityPrime m) := by
  let O := (sourceGaloisWClosureInfinityPlace m).valuationRing
  let C := SourceGaloisWInfinityIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  letI : p.IsPrime := inferInstance
  letI : Algebra.IsIntegral O C := integralClosure.AlgebraIsIntegral
  letI : Module.IsTorsionFree O C := by
    exact sourceGaloisWPlaceIntegralClosureTorsionFree m
      (sourceGaloisWClosureInfinityPlace m)
  exact Ideal.nonempty_primesOver p

/-- The genuine zero-place upper-prime fibre is finite. -/
theorem sourceGaloisWZeroPrime_finite (m : ℕ) :
    Set.Finite (SourceGaloisWZeroPrime m) := by
  exact IsDedekindDomain.primesOver_finite
    (IsLocalRing.maximalIdeal
      (sourceGaloisWClosureZeroPlace m).valuationRing)
    (SourceGaloisWZeroIntegralClosure m)

/-- The genuine infinity-place upper-prime fibre is finite. -/
theorem sourceGaloisWInfinityPrime_finite (m : ℕ) :
    Set.Finite (SourceGaloisWInfinityPrime m) := by
  exact IsDedekindDomain.primesOver_finite
    (IsLocalRing.maximalIdeal
      (sourceGaloisWClosureInfinityPlace m).valuationRing)
    (SourceGaloisWInfinityIntegralClosure m)

/-- The common Galois ramification index above the zero place. -/
noncomputable def sourceGaloisWZeroRamificationIndex (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureZeroPlace m).valuationRing).ramificationIdxIn
      (SourceGaloisWZeroIntegralClosure m)

/-- The common Galois ramification index above the infinity place. -/
noncomputable def sourceGaloisWInfinityRamificationIndex (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureInfinityPlace m).valuationRing).ramificationIdxIn
      (SourceGaloisWInfinityIntegralClosure m)

/-- The common zero-fibre ramification index is the ramification index of
each genuine upper prime in that fibre. -/
theorem sourceGaloisWZeroRamificationIndex_eq_prime (m : ℕ)
    (P : SourceGaloisWZeroPrime m) :
    sourceGaloisWZeroRamificationIndex m =
      (IsLocalRing.maximalIdeal
        (sourceGaloisWClosureZeroPlace m).valuationRing).ramificationIdx' P.1 := by
  let O := (sourceGaloisWClosureZeroPlace m).valuationRing
  let C := SourceGaloisWZeroIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureZeroPlace m).valuationRing_isDiscreteValuationRing
  letI : p.IsPrime := inferInstance
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  change p.ramificationIdxIn C = p.ramificationIdx' P.1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p P.1
    (IsDiscreteValuationRing.not_a_field O)]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p P.1 G

/-- The common infinity-fibre ramification index is the ramification index of
each genuine upper prime in that fibre. -/
theorem sourceGaloisWInfinityRamificationIndex_eq_prime (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    sourceGaloisWInfinityRamificationIndex m =
      (IsLocalRing.maximalIdeal
        (sourceGaloisWClosureInfinityPlace m).valuationRing).ramificationIdx' P.1 := by
  let O := (sourceGaloisWClosureInfinityPlace m).valuationRing
  let C := SourceGaloisWInfinityIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureInfinityPlace m).valuationRing_isDiscreteValuationRing
  letI : p.IsPrime := inferInstance
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  change p.ramificationIdxIn C = p.ramificationIdx' P.1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p P.1
    (IsDiscreteValuationRing.not_a_field O)]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p P.1 G

/-- The common Galois inertia degree above the zero place. -/
noncomputable def sourceGaloisWZeroInertiaDegree (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureZeroPlace m).valuationRing).inertiaDegIn
      (SourceGaloisWZeroIntegralClosure m)

/-- The common Galois inertia degree above the infinity place. -/
noncomputable def sourceGaloisWInfinityInertiaDegree (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureInfinityPlace m).valuationRing).inertiaDegIn
      (SourceGaloisWInfinityIntegralClosure m)

/-- The actual relative degree of the normal closure over its embedded
`F256(w)` subfield, pinned to the tower's chosen algebra structure. -/
noncomputable def sourceGaloisWRelativeDegree (m : ℕ) : ℕ :=
  Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m)

/-- The common ramification index above the zero place is positive. -/
theorem sourceGaloisWZeroRamificationIndex_pos (m : ℕ) :
    0 < sourceGaloisWZeroRamificationIndex m := by
  let O := (sourceGaloisWClosureZeroPlace m).valuationRing
  let C := SourceGaloisWZeroIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureZeroPlace m).valuationRing_isDiscreteValuationRing
  change 0 < p.ramificationIdxIn C
  exact Nat.pos_of_ne_zero (Ideal.ramificationIdxIn_ne_zero G)

/-- The common ramification index above the infinity place is positive. -/
theorem sourceGaloisWInfinityRamificationIndex_pos (m : ℕ) :
    0 < sourceGaloisWInfinityRamificationIndex m := by
  let O := (sourceGaloisWClosureInfinityPlace m).valuationRing
  let C := SourceGaloisWInfinityIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureInfinityPlace m).valuationRing_isDiscreteValuationRing
  change 0 < p.ramificationIdxIn C
  exact Nat.pos_of_ne_zero (Ideal.ramificationIdxIn_ne_zero G)

private theorem sourceGaloisWPlace_fundamental_identity (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Set.ncard
        ((IsLocalRing.maximalIdeal P.valuationRing).primesOver
          (SourceGaloisWPlaceIntegralClosure m P)) *
        ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdxIn
            (SourceGaloisWPlaceIntegralClosure m P) *
          (IsLocalRing.maximalIdeal P.valuationRing).inertiaDegIn
            (SourceGaloisWPlaceIntegralClosure m P)) =
      Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) := by
  let O := P.valuationRing
  let C := SourceGaloisWPlaceIntegralClosure m P
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let G := Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  calc
    Set.ncard (p.primesOver C) *
        (p.ramificationIdxIn C * p.inertiaDegIn C) = Nat.card G :=
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p C G
    _ = Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
      IsGalois.card_aut_eq_finrank (SourceGaloisWClosureField m)
        (SourceGaloisClosureField m)

/-- The Galois fundamental identity for the actual zero-place fibre. -/
theorem sourceGaloisWZero_fundamental_identity (m : ℕ) :
    Set.ncard (SourceGaloisWZeroPrime m) *
        (sourceGaloisWZeroRamificationIndex m *
          sourceGaloisWZeroInertiaDegree m) =
      Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) := by
  exact sourceGaloisWPlace_fundamental_identity m (sourceGaloisWClosureZeroPlace m)

/-- The Galois fundamental identity for the actual infinity-place fibre. -/
theorem sourceGaloisWInfinity_fundamental_identity (m : ℕ) :
    Set.ncard (SourceGaloisWInfinityPrime m) *
        (sourceGaloisWInfinityRamificationIndex m *
          sourceGaloisWInfinityInertiaDegree m) =
      Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) := by
  exact sourceGaloisWPlace_fundamental_identity m (sourceGaloisWClosureInfinityPlace m)

/-- The zero-fibre fundamental identity in terms of the pinned relative
degree. -/
theorem sourceGaloisWZero_fundamental_identity_relativeDegree (m : ℕ) :
    Set.ncard (SourceGaloisWZeroPrime m) *
        (sourceGaloisWZeroRamificationIndex m *
          sourceGaloisWZeroInertiaDegree m) =
      sourceGaloisWRelativeDegree m := by
  change Set.ncard (SourceGaloisWZeroPrime m) *
      (sourceGaloisWZeroRamificationIndex m *
        sourceGaloisWZeroInertiaDegree m) =
    Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
  exact sourceGaloisWZero_fundamental_identity m

/-- The infinity-fibre fundamental identity in terms of the pinned relative
degree. -/
theorem sourceGaloisWInfinity_fundamental_identity_relativeDegree (m : ℕ) :
    Set.ncard (SourceGaloisWInfinityPrime m) *
        (sourceGaloisWInfinityRamificationIndex m *
          sourceGaloisWInfinityInertiaDegree m) =
      sourceGaloisWRelativeDegree m := by
  change Set.ncard (SourceGaloisWInfinityPrime m) *
      (sourceGaloisWInfinityRamificationIndex m *
        sourceGaloisWInfinityInertiaDegree m) =
    Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
  exact sourceGaloisWInfinity_fundamental_identity m

/-- The relative degree over `F256(w)`, multiplied by the degree fifteen of
`F256(w) / F256(z)`, is the actual selected length. -/
theorem sourceGaloisWClosureField_relfinrank_mul_fifteen (m : ℕ) :
    15 * Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) =
      sourceGaloisClosureSelectedLength m := by
  calc
    15 * Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) =
        Module.finrank GaloisBaseField (SourceGaloisWClosureField m) *
          Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) := by
      rw [sourceGaloisWClosureField_finrank]
    _ = Module.finrank GaloisBaseField (SourceGaloisClosureField m) :=
      Module.finrank_mul_finrank GaloisBaseField (SourceGaloisWClosureField m)
        (SourceGaloisClosureField m)
    _ = sourceGaloisClosureSelectedLength m := rfl

/-- The pinned relative degree multiplied by the degree fifteen of
`F256(w) / F256(z)` is the actual selected length. -/
theorem sourceGaloisWRelativeDegree_mul_fifteen (m : ℕ) :
    15 * sourceGaloisWRelativeDegree m = sourceGaloisClosureSelectedLength m := by
  change 15 * Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m) =
    sourceGaloisClosureSelectedLength m
  exact sourceGaloisWClosureField_relfinrank_mul_fifteen m

/-- The zero fibre has the actual selected length after applying its
degree-fifteen base weight. -/
theorem sourceGaloisWZero_weighted_fibre_identity (m : ℕ) :
    15 * (Set.ncard (SourceGaloisWZeroPrime m) *
        (sourceGaloisWZeroRamificationIndex m *
          sourceGaloisWZeroInertiaDegree m)) =
      sourceGaloisClosureSelectedLength m := by
  rw [sourceGaloisWZero_fundamental_identity]
  exact sourceGaloisWClosureField_relfinrank_mul_fifteen m

/-- The infinity fibre has the actual selected length after applying its
degree-fifteen base weight. -/
theorem sourceGaloisWInfinity_weighted_fibre_identity (m : ℕ) :
    15 * (Set.ncard (SourceGaloisWInfinityPrime m) *
        (sourceGaloisWInfinityRamificationIndex m *
          sourceGaloisWInfinityInertiaDegree m)) =
      sourceGaloisClosureSelectedLength m := by
  rw [sourceGaloisWInfinity_fundamental_identity]
  exact sourceGaloisWClosureField_relfinrank_mul_fifteen m

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
