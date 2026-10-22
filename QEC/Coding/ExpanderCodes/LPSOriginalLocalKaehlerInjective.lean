import QEC.Coding.ExpanderCodes.LPSOriginalLocalKaehlerFiniteness
import QEC.Coding.AlgebraicGeometry.Places.MeromorphicValuationDifferentials

/-!
# Injective original point-local differentials

Every actual filled point has an essentially finite-type valuation ring. Actual residue evaluation, Nakayama and the genuine positive-order parameter derivative prove injection into the SAME C(j,j_N) differential space.

Derived internal PK22 ex:Xpq machinery, pinned main.tex484–486, for parent #449.
This proves actual differential injection and compatible affine preimages.
Genuine global differential sheaf/gluing/GAGA, good reduction, Hecke/Frobenius/Weil
and the exact arbitrary-finite-field public quantum family remain outstanding.
No public node changes status.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalLocalKaehlerInjectiveDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance LPSOriginalLocalKaehlerInjectiveDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary004 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerInjectiveDictionary005 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerInjectiveDictionary006 : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerInjectiveDictionary007 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerInjectiveDictionary008 : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalLocalKaehlerInjectiveDictionary009 : Algebra ℂ G := (germComplexConstants a).toAlgebra

local instance LPSOriginalLocalKaehlerInjectiveDictionary010 : Algebra K G := (lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary011 : SMul K G := Algebra.toSMul (R := K) (A := G)
local instance LPSOriginalLocalKaehlerInjectiveDictionary012 : Module K G := Algebra.toModule (R := K) (A := G)
local instance LPSOriginalLocalKaehlerInjectiveDictionary013 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary014 : SMul V K := Algebra.toSMul (R := V) (A := K)
local instance LPSOriginalLocalKaehlerInjectiveDictionary015 : Module V K := Algebra.toModule (R := V) (A := K)
local instance LPSOriginalLocalKaehlerInjectiveDictionary016 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerInjectiveDictionary017 : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerInjectiveDictionary018 : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerInjectiveDictionary019 : IsScalarTower ℂ K G :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).commutes c).symm
local instance LPSOriginalLocalKaehlerInjectiveDictionary020 : IsDiscreteValuationRing V :=
  lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x

local instance LPSOriginalLocalKaehlerInjectiveDictionary021 : IsDiscreteValuationRing
    (Valuation.valuationSubring (AddValuation.toValuation
      (AddValuation.comap (algebraMap K G) (meromorphicOrderValuation a)))) := by
  change IsDiscreteValuationRing V
  exact lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x

local instance LPSOriginalLocalKaehlerInjectiveDictionary022 : Algebra ℂ V := (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary023 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl


/-- Every actual filled-point valuation ring is essentially finite type, using the real interior and cusp chart cover. -/
lemma lpsOriginalMeromorphicValuationRing_essFiniteType :
    Algebra.EssFiniteType ℂ V := by
  cases x with
  | inl y =>
      exact lpsOriginalZeroValuation_essFiniteType N hpos hN (Sum.inl y)
        (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN y)
  | inr c =>
      exact lpsOriginalInfinityValuation_essFiniteType N hpos hN (Sum.inr c)
        (lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c)

/-- Prove the actual local differential map injective at every original filled point, with finite type, residue and DVR data derived. -/
lemma lpsOriginalLocalKaehler_map_injective :
    Function.Injective (KaehlerDifferential.map ℂ ℂ V K) := by
  let : Algebra ℂ
      (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationRing K a) :=
    (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.complexConstantsToValuationRing K a).toAlgebra
  let : Algebra.EssFiniteType ℂ
      (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationRing K a) := by
    change Algebra.EssFiniteType ℂ V
    exact lpsOriginalMeromorphicValuationRing_essFiniteType N hpos hN x
  exact QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationKaehler_map_injective K a
end
end QEC.Coding.TannerLiftedProduct
