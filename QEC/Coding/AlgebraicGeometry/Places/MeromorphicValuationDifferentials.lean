import QEC.Coding.AlgebraicGeometry.Differentials.LocalKaehlerCyclic
import QEC.Coding.AlgebraicGeometry.Places.LocalMeromorphicDifferential
import QEC.Coding.AlgebraicGeometry.Places.AnalyticGermEvaluation

/-!
# Residues and meromorphic valuation differentials

Construct actual analytic residue evaluation, identify its kernel by local order, and derive local differential injection from the genuine DVR parameter and essential finite type.

Derived internal PK22 ex:Xpq machinery, pinned main.tex484–486, for parent #449.
This proves actual differential injection and compatible affine preimages.
Genuine global differential sheaf/gluing/GAGA, good reduction, Hecke/Frobenius/Weil
and the exact arbitrary-finite-field public quantum family remain outstanding.
No public node changes status.
-/

namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
local instance MeromorphicValuationDifferentialsDictionary001 : Algebra ℂ (MeromorphicGermRing a) := (germComplexConstants a).toAlgebra
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
local instance MeromorphicValuationDifferentialsDictionary002 : Algebra ℂ V := (complexConstantsToValuationRing K a).toAlgebra
local instance MeromorphicValuationDifferentialsDictionary003 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl

/-- Embed actual valuation-ring elements into genuine no-pole meromorphic germs while retaining their ambient values. -/
def localValuationToMeromorphicInteger : V →+*
    (AddValuation.toValuation (meromorphicOrderValuation a)).integer := by
  let f := (algebraMap K (MeromorphicGermRing a)).comp (ValuationSubring.subtype V)
  refine f.codRestrict _ ?_
  intro t
  exact t.property

/-- Construct the actual complex-algebra residue map from analytic representative evaluation. -/
def localValuationResidueEvaluation : V →ₐ[ℂ] ℂ where
  toRingHom := (meromorphicNoPoleEvaluation a).comp (localValuationToMeromorphicInteger K a)
  commutes' c := by
    apply meromorphicNoPoleEvaluation_rep _ _ (fun _ => c) analyticAt_const
    change ((algebraMap K (MeromorphicGermRing a)) (algebraMap ℂ K c)).val = _
    rw [← IsScalarTower.algebraMap_apply ℂ K (MeromorphicGermRing a) c]
    rfl

/-- The actual residue evaluation kernel is the valuation-ring maximal ideal, by positive local order. -/
lemma localValuationResidueEvaluation_ker :
    RingHom.ker (localValuationResidueEvaluation K a) = IsLocalRing.maximalIdeal V := by
  ext t
  rw [RingHom.mem_ker, (AddValuation.toValuation (localFieldOrder K a)).mem_maximalIdeal_iff]
  change meromorphicNoPoleEvaluation a (localValuationToMeromorphicInteger K a t) = 0 ↔
    0 < meromorphicOrderValuation a (algebraMap K (MeromorphicGermRing a) t.val)
  exact meromorphicNoPoleEvaluation_eq_zero_iff_order_pos a _
end
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential


namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
local instance MeromorphicValuationDifferentialsDictionary004 : Algebra ℂ (MeromorphicGermRing a) := (germComplexConstants a).toAlgebra
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
local instance MeromorphicValuationDifferentialsDictionary005 : Algebra ℂ V := (complexConstantsToValuationRing K a).toAlgebra
local instance MeromorphicValuationDifferentialsDictionary006 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance MeromorphicValuationDifferentialsDictionary007 : SMul V K := Algebra.toSMul
local instance MeromorphicValuationDifferentialsDictionary008 : Module V K := Algebra.toModule
local instance MeromorphicValuationDifferentialsDictionary009 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
local instance MeromorphicValuationDifferentialsDictionary010 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    simp only [Algebra.smul_def]
    ring
local instance MeromorphicValuationDifferentialsDictionary011 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance MeromorphicValuationDifferentialsDictionary012 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
/-- Actual residue evaluation and a genuine positive-order DVR parameter prove local differential injection for an essentially finite-type valuation ring. -/
lemma localValuationKaehler_map_injective
    [IsDiscreteValuationRing V] [Algebra.EssFiniteType ℂ V] :
    Function.Injective (KaehlerDifferential.map ℂ ℂ V K) := by
  obtain ⟨pi,m,hpi,hm,he⟩ := exists_uniformizer_order (localFieldOrder K a)
  exact QEC.Coding.AlgebraicGeometry.localKaehler_map_injective_of_splitResidue ℂ V K
    (localValuationResidueEvaluation K a) (localValuationResidueEvaluation_ker K a) pi
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi)
    (fun _ _ h => Subtype.ext h)
    (uniformizerDifferential_ne_zero K a pi m hm he)
end
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
