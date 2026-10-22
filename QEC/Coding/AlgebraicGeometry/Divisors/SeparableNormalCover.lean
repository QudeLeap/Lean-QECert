import QEC.Coding.AlgebraicGeometry.Places.AffinePlaceDegree
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.RamificationInertia.Inertia

namespace QEC.Coding.AlgebraicGeometry.SeparableNormalCover

open scoped Polynomial RatFunc

noncomputable section

attribute [local instance] FractionRing.liftAlgebra in
private theorem relNorm_eq_pow_of_galois_integral_cover
    {R S : Type*} (T : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsDedekindDomain R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsDedekindDomain S] [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [IsDedekindDomain T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Module.Finite S T] [Module.IsTorsionFree S T] [Module.Finite R T]
    [Module.IsTorsionFree R T] [Algebra.IsIntegral S T]
    [IsGalois (FractionRing R) (FractionRing T)]
    [IsGalois (FractionRing S) (FractionRing T)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  obtain ⟨Q, hQmax, hQover⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := T) P
  letI : Q.IsMaximal := hQmax
  letI : Q.LiesOver P := hQover
  letI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have hQp : Ideal.relNorm R Q = p ^ p.inertiaDeg' Q := by
    simpa only [Ideal.inertiaDeg'_eq_inertiaDeg] using
      Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have hQP : Ideal.relNorm S Q = P ^ P.inertiaDeg' Q := by
    simpa only [Ideal.inertiaDeg'_eq_inertiaDeg] using
      Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P
  rw [← Ideal.relNorm_relNorm R S, hQP, map_pow] at hQp
  rwa [Ideal.inertiaDeg_algebra_tower p P Q, pow_mul, pow_left_inj] at hQp
  exact Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg'_pos P Q)

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

abbrev directRingOfIntegers : Type _ := _root_.FunctionField.ringOfIntegers k F

local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing B

local instance : Module.IsTorsionFree R B :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

local instance : Module.Finite R B := AffinePlace.finite_ringOfIntegers k F

noncomputable local instance : Algebra K L := FractionRing.liftAlgebra _ _

/-- The direct fraction-field extension is the supplied separable
function-field extension transported through the two fraction-ring
equivalences. -/
theorem fractionRing_isSeparable : Algebra.IsSeparable K L := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv R k⟮X⟯).symm.toRingEquiv
    (FractionRing.algEquiv B F).symm.toRingEquiv ?_
  ext x
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R k⟮X⟯).symm
    (FractionRing.algEquiv B F).symm x

local instance : Algebra.IsSeparable K L := fractionRing_isSeparable k F

/-- The absolute separable closure is a genuine Galois ambient field for the
finite separable extension `L / K`. -/
local notation3 "M" => SeparableClosure K

/-- A fixed K-embedding of the actual fraction field `L` into its absolute
separable closure. -/
noncomputable def directSeparableEmbedding : L →ₐ[K] M :=
  (IsSepClosed.lift : L →ₐ[K] M)

local instance : Algebra L M := (directSeparableEmbedding k F).toRingHom.toAlgebra

local instance : IsScalarTower K L M :=
  IsScalarTower.of_algebraMap_eq' (directSeparableEmbedding k F).comp_algebraMap.symm

/-- The finite normal closure of `L / K` inside the absolute separable
closure of `K`. -/
local notation3 "E" => IntermediateField.normalClosure K L M

local instance : FiniteDimensional K E := normalClosure.is_finiteDimensional K L M

local instance : IsGalois K E := IsGalois.normalClosure K L M

local instance : Algebra B E := ((algebraMap L E).comp (algebraMap B L)).toAlgebra

local instance : IsScalarTower B L E := IsScalarTower.of_algebraMap_eq' rfl

/-- The integral closure of the direct affine chart in the actual finite
normal field. -/
local notation3 "T" => integralClosure B E

local instance : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra

local instance : IsIntegralClosure T B E := integralClosure.isIntegralClosure B E

local instance : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

local instance : IsScalarTower R B E := IsScalarTower.to₁₂₄ R B L E

local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R B T E

local instance : FaithfulSMul B E :=
  (faithfulSMul_iff_algebraMap_injective B E).mpr <|
    (FaithfulSMul.algebraMap_injective L E).comp
      (FaithfulSMul.algebraMap_injective B L)

local instance : FaithfulSMul B T :=
  (faithfulSMul_iff_algebraMap_injective B T).mpr <| by
    intro x y h
    apply FaithfulSMul.algebraMap_injective B E
    simpa using congrArg (fun z : T => (z : E)) h

local instance : Module.IsTorsionFree B E :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective B E)

local instance : Module.IsTorsionFree B T :=
  Subalgebra.instIsTorsionFree (integralClosure B E)

local instance : Module.IsTorsionFree R T :=
  Module.IsTorsionFree.trans_faithfulSMul R B T

local instance : FaithfulSMul R T :=
  (faithfulSMul_iff_algebraMap_injective R T).mpr <|
    (FaithfulSMul.algebraMap_injective B T).comp
      (FaithfulSMul.algebraMap_injective R B)

local instance : FiniteDimensional L E := FiniteDimensional.right K L E

local instance : IsFractionRing T E :=
  integralClosure.isFractionRing_of_finite_extension L E

local instance : IsIntegrallyClosed T :=
  integralClosure.isIntegrallyClosedOfFiniteExtension L

local instance : Algebra.IsSeparable L E :=
  Algebra.isSeparable_tower_top_of_isSeparable K L E

local instance : Algebra.IsIntegral B T :=
  IsIntegralClosure.isIntegral_algebra B (A := T) E

local instance : Module.Finite B T := IsIntegralClosure.finite B L E T

local instance : Module.Finite R T := Module.Finite.trans B T

local instance : IsDedekindDomain T := integralClosure.isDedekindDomain B L E

/-- The fraction field of the constructed cover is Galois over the actual
fraction field of `k[X]`. -/
noncomputable local instance : Algebra T (FractionRing T) := OreLocalization.instAlgebra

noncomputable local instance : Algebra K (FractionRing T) :=
  FractionRing.liftAlgebra R (FractionRing T)

theorem directCover_fractionRing_isGalois : IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext x
  simpa using @IsFractionRing.algEquiv_commutes R inferInstance T inferInstance inferInstance
    K (FractionRing R) inferInstance inferInstance inferInstance inferInstance inferInstance
    E (FractionRing T) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm x

local instance : IsGalois K (FractionRing T) := directCover_fractionRing_isGalois k F

noncomputable local instance directBFracAlgebra : Algebra B (FractionRing T) :=
  OreLocalization.instAlgebra
local instance : SMul B (FractionRing T) := (directBFracAlgebra k F).toSMul
local instance : FaithfulSMul B (FractionRing T) :=
  (faithfulSMul_iff_algebraMap_injective B (FractionRing T)).mpr
    ((IsFractionRing.injective T (FractionRing T)).comp
      (FaithfulSMul.algebraMap_injective B T))
noncomputable local instance : Algebra L (FractionRing T) :=
  FractionRing.liftAlgebra B (FractionRing T)

/-- The direct prime relative-norm formula now follows from the constructed
finite integral Galois cover, without adding a separate structural premise. -/
theorem direct_relNorm_eq_pow
    (P : Ideal B) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  letI : IsGalois L (FractionRing T) :=
    IsGalois.tower_top_of_isGalois K L (FractionRing T)
  exact relNorm_eq_pow_of_galois_integral_cover T P p

end

end QEC.Coding.AlgebraicGeometry.SeparableNormalCover
