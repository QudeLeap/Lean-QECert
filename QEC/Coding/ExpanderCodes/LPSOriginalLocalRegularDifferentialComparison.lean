import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationLocalRings
import QEC.Coding.ExpanderCodes.LPSOriginalGenericDifferentialComparison
import QEC.Coding.AlgebraicGeometry.Places.LocalMeromorphicDifferential

/-!
# Original local regular differential comparison

On the actual original Gamma0(N) filled curve and the SAME C(j,jN) field,
compare the real local Kähler image with the analytic no-pole coefficient
condition at every filled point. Derive every DVR and one-dimensionality
prerequisite from the original normalization and function-field proofs.

This is derived internal closure for parent #449 and PK22 ex:Xpq (pinned
main.tex 484–486). It does not prove a complex-algebra equivalence for the
glued stalk, native whole-covector coefficient compatibility, global point
coverage/GAGA, good reduction, Frobenius/Weil bounds, or the arbitrary-field
explicit quantum family. No public node changes status here.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance : Algebra ℂ G := (germComplexConstants a).toAlgebra

/-- The original C(j,jN) local germ map preserves literal complex constants. -/
def lpsOriginalFieldToLocalComplexAlgHom : K →ₐ[ℂ] G where
  toRingHom := lpsOriginalFieldToLocal N hN hpos x
  commutes' c := by
    change lpsOriginalFieldToLocal N hN hpos x (algebraMap ℂ K c) =
      germComplexConstants a c
    rw [lpsOriginalFieldToLocal_constant N hN hpos x c]
    rfl

local instance : Algebra K G := (lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).toAlgebra
local instance : SMul K G := Algebra.toSMul (R := K) (A := G)
local instance : Module K G := Algebra.toModule (R := K) (A := G)
local instance : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance : SMul V K := Algebra.toSMul (R := V) (A := K)
local instance : Module V K := Algebra.toModule (R := V) (A := K)
local instance : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance : IsScalarTower ℂ K G :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).commutes c).symm
local instance : IsDiscreteValuationRing V :=
  lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x

local instance : IsDiscreteValuationRing
    (Valuation.valuationSubring (AddValuation.toValuation
      (AddValuation.comap (algebraMap K G) (meromorphicOrderValuation a)))) := by
  change IsDiscreteValuationRing V
  exact lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x

/-- Differentiate genuine universal differentials of the SAME original function field locally. -/
abbrev lpsOriginalFieldLocalDifferentialMap : KaehlerDifferential ℂ K →ₗ[K] G :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap K a

/-- Every original universal df has its actual differentiated chart germ coefficient. -/
lemma lpsOriginalFieldLocalDifferentialMap_D (f : K) :
    lpsOriginalFieldLocalDifferentialMap N hpos hN x (KaehlerDifferential.D ℂ K f) =
      germDerivative a (lpsOriginalFieldToLocal N hN hpos x f) :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap_D K a f

/-- The real regular-function differential lattice of the original meromorphic-order valuation ring. -/
abbrev lpsOriginalLocalDifferentialLattice : Submodule V (KaehlerDifferential ℂ K) :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice K a

/-- The original regular-function differential lattice equals the no-pole coefficient condition. -/
lemma lpsOriginalLocalDifferentialLattice_iff_noPole (ω : KaehlerDifferential ℂ K) :
    ω ∈ lpsOriginalLocalDifferentialLattice N hpos hN x ↔
      0 ≤ meromorphicOrderValuation a (lpsOriginalFieldLocalDifferentialMap N hpos hN x ω) := by
  change ω ∈ QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice K a ↔
    0 ≤ meromorphicOrderValuation a
      (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap K a ω)
  rw [QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice_eq_analyticRegular
    K a (lpsOriginalGenericKaehlerCoefficientEquiv N hpos)]
  rfl

/-- The original local valuation ring contains the unchanged literal complex constants. -/
abbrev lpsOriginalComplexConstantsToMeromorphicValuationRing : ℂ →+* V :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.complexConstantsToValuationRing K a

local instance : Algebra ℂ V := (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- The original real local Kähler image equals analytic no-pole coefficients, with all prerequisites proved. -/
lemma lpsOriginalLocalKaehlerRange_iff_noPole (ω : KaehlerDifferential ℂ K) :
    ω ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap V).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a (lpsOriginalFieldLocalDifferentialMap N hpos hN x ω) :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localKaehlerRange_iff_noPole
    K a (lpsOriginalGenericKaehlerCoefficientEquiv N hpos) ω

end
end QEC.Coding.TannerLiftedProduct
