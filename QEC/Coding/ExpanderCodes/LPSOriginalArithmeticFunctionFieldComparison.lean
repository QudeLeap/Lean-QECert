import QEC.Coding.ExpanderCodes.LPSOriginalCompactMeromorphicFunctionField
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerModelFunctionField
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace


/-!
# Generic arithmetic and analytic function-field comparison

The original integer normal glued scheme already has the actual generic stalk
function field Q(j,j_N). The preceding analytic proof identifies C(j,j_N) with
all meromorphic germs on the same original filled compact curve. This module
constructs their scalar extension comparison over the same faithful j maps.

The tensor map is defined from actual rational coefficient inclusion and the
original j_N. A genuine j_N power basis proves surjectivity. Independently
proved exact rational and complex coset degrees, together with base-change
finrank, prove injectivity without a linear-disjointness assumption. Tensoring
the genuine generic-stalk equivalence gives the arithmetic comparison.

This is an internal part of the original modular-equation route behind pinned
PK22 ex:Xpq/th:qLDPC and Milne, Modular Functions and Modular Forms, Theorem6.1.
It proves a generic function-field comparison. A global base-changed scheme
comparison, algebraic/analytic differential comparison, uniform good reduction,
geometric Frobenius/Weil bound and the exact public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

/-- Localize faithful rational coefficient inclusion into the complex rational function field. -/
def lpsOriginalJBaseQToC :
    FractionRing (Polynomial ℚ) →+* FractionRing (Polynomial ℂ) :=
  IsFractionRing.lift
    (g := (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ)))
    ((IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      (Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective))

/-- The localized scalar map preserves literal polynomial coefficient inclusion. -/
lemma lpsOriginalJBaseQToC_polynomial (P : Polynomial ℚ) :
    lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P) =
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))
        (P.map (algebraMap ℚ ℂ)) :=
  IsFractionRing.lift_algebraMap _ P

/-- The scalar extension followed by actual complex j evaluation is actual rational j evaluation. -/
lemma lpsOriginalJBaseQToC_actualEmbedding :
    lpsOriginalJFractionEmbedding.comp lpsOriginalJBaseQToC =
      lpsOriginalJFractionEmbeddingQ := by
  apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
  intro P
  change lpsOriginalJFractionEmbedding
    (lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)) =
      lpsOriginalJFractionEmbeddingQ
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)
  rw [lpsOriginalJBaseQToC_polynomial,lpsOriginalJFractionEmbedding_polynomial,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  rfl

/-- The two actual j realizations form a genuine scalar tower. -/
lemma lpsOriginalJBaseQToC_actualTower :
    letI := lpsOriginalJBaseQToC.toAlgebra
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IsScalarTower (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ))
      LPSOriginalHolomorphicFractionField := by
  let := lpsOriginalJBaseQToC.toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    lpsOriginalJBaseQToC_actualEmbedding.symm

/-- The same original rational generated field lies in the complex generated field. -/
lemma lpsOriginalGeneratedFunctionFieldQ_mem_complex (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ x ∈ lpsOriginalGeneratedFunctionFieldQ N hN,
      x ∈ lpsOriginalGeneratedFunctionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalJBaseQToC.toAlgebra
  let := lpsOriginalJBaseQToC_actualTower
  have hle : lpsOriginalGeneratedFunctionFieldQ N hN ≤
      (lpsOriginalGeneratedFunctionField N hN).restrictScalars
        (FractionRing (Polynomial ℚ)) := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    exact IntermediateField.subset_adjoin (FractionRing (Polynomial ℂ))
      {lpsOriginalJNInFractionField N hN} hx
  exact hle


section ScalarExtension
local instance : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower

/-- Include the actual Q(j,j_N) in the actual C(j,j_N) over the faithful rational j base. -/
def lpsOriginalGeneratedQToComplex (N : ℕ) (hN : 0 < N) :
    lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[FractionRing (Polynomial ℚ)]
      lpsOriginalGeneratedFunctionField N hN := by
  change lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[FractionRing (Polynomial ℚ)]
    (lpsOriginalGeneratedFunctionField N hN).restrictScalars (FractionRing (Polynomial ℚ))
  exact IntermediateField.inclusion (lpsOriginalGeneratedFunctionFieldQ_mem_complex N hN)

/-- The inclusion preserves each literal holomorphic-fraction value. -/
lemma lpsOriginalGeneratedQToComplex_apply (N : ℕ) (hN : 0 < N)
    (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    (lpsOriginalGeneratedQToComplex N hN x).val = x.val := rfl

/-- Construct the original generated-field scalar extension map by the tensor universal property. -/
def lpsOriginalRationalComplexTensorMap (N : ℕ) (hN : 0 < N) :
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      (lpsOriginalGeneratedFunctionFieldQ N hN) →ₐ[FractionRing (Polynomial ℂ)]
        lpsOriginalGeneratedFunctionField N hN :=
  (AlgHom.liftEquiv (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ))
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalGeneratedFunctionField N hN))
      (lpsOriginalGeneratedQToComplex N hN)

/-- The tensor map sends a pure tensor to the actual scalar multiple of its rational inclusion. -/
lemma lpsOriginalRationalComplexTensorMap_tmul (N : ℕ) (hN : 0 < N)
    (r : FractionRing (Polynomial ℂ)) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    lpsOriginalRationalComplexTensorMap N hN (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
      r • lpsOriginalGeneratedQToComplex N hN x := rfl

/-- The actual complex j_N power basis proves that the constructed tensor map is onto. -/
lemma lpsOriginalRationalComplexTensorMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Surjective (lpsOriginalRationalComplexTensorMap N hN) := by
  let pb := IntermediateField.adjoin.powerBasis
    (lpsOriginalJNInFractionField_integral N hN)
  let αQ : lpsOriginalGeneratedFunctionFieldQ N hN :=
    ⟨lpsOriginalJNInFractionField N hN,
      IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
        {lpsOriginalJNInFractionField N hN} (Set.mem_singleton _)⟩
  have hα : lpsOriginalRationalComplexTensorMap N hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ) = pb.gen := by
    rw [lpsOriginalRationalComplexTensorMap_tmul,one_smul]
    apply Subtype.ext
    rfl
  intro x
  obtain ⟨P,hP⟩ := pb.exists_eq_aeval' x
  refine ⟨Polynomial.aeval
    ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ) P,?_⟩
  rw [←Polynomial.aeval_algHom_apply,hα]
  exact hP.symm

/-- True base-change finrank and the two independently proved exact degrees give equal dimensions. -/
lemma lpsOriginalRationalComplexTensorMap_finrank
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Module.finrank (FractionRing (Polynomial ℂ))
      ((FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
        (lpsOriginalGeneratedFunctionFieldQ N hN)) =
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN) := by
  let : Module.Free (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace _ _)
  rw [Module.finrank_baseChange,lpsOriginalGeneratedFunctionFieldQ_finrank_eq,
    lpsOriginalGeneratedFunctionField_finrank_eq]

/-- Surjectivity and actual equal finite dimensions prove the tensor map faithful. -/
lemma lpsOriginalRationalComplexTensorMap_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Injective (lpsOriginalRationalComplexTensorMap N hN) := by
  let := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  let := lpsOriginalGeneratedFunctionField_finiteDimensional N hN
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (lpsOriginalRationalComplexTensorMap_finrank N hN)).mpr
      (lpsOriginalRationalComplexTensorMap_surjective N hN)

/-- The genuine rational-to-complex generated-field scalar extension equivalence. -/
def lpsOriginalRationalComplexTensorEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      (lpsOriginalGeneratedFunctionFieldQ N hN) ≃ₐ[FractionRing (Polynomial ℂ)]
        lpsOriginalGeneratedFunctionField N hN :=
  AlgEquiv.ofBijective (lpsOriginalRationalComplexTensorMap N hN)
    ⟨lpsOriginalRationalComplexTensorMap_injective N hN,
      lpsOriginalRationalComplexTensorMap_surjective N hN⟩


/-- Extend the rational original field to ALL actual compact meromorphic germs over the same C(j). -/
def lpsOriginalRationalCompactMeromorphicTensorEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      (lpsOriginalGeneratedFunctionFieldQ N hpos) ≃ₐ[FractionRing (Polynomial ℂ)]
        LPSOriginalCompactMeromorphicGermRing N hN := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  exact (lpsOriginalRationalComplexTensorEquiv N hpos).trans
    (lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN)

/-- The full compact-field comparison preserves the actual pure-tensor values. -/
lemma lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (r : FractionRing (Polynomial ℂ)) (x : lpsOriginalGeneratedFunctionFieldQ N hpos) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
        r • lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
          (lpsOriginalGeneratedQToComplex N hpos x) := by
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  change lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
    (lpsOriginalRationalComplexTensorMap N hpos
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x)) = _
  rw [lpsOriginalRationalComplexTensorMap_tmul,map_smul]

/-- The tensor of the same original j_N is the genuine global germ of filled j_N. -/
lemma lpsOriginalRationalCompactMeromorphicTensorEquiv_jN
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    let αQ : lpsOriginalGeneratedFunctionFieldQ N hpos :=
      ⟨lpsOriginalJNInFractionField N hpos,
        IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
          {lpsOriginalJNInFractionField N hpos} (Set.mem_singleton _)⟩
    (lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ)).val =
      (lpsOriginalFilledJDilated N hpos :
        Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) := by
  let := lpsOriginalFilledTopology N
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  dsimp only
  let αQ : lpsOriginalGeneratedFunctionFieldQ N hpos :=
    ⟨lpsOriginalJNInFractionField N hpos,
      IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
        {lpsOriginalJNInFractionField N hpos} (Set.mem_singleton _)⟩
  let F : LPSOriginalFilledMeromorphicFunctionRing N hN :=
    ⟨lpsOriginalFilledJDilated N hpos,lpsOriginalFilledChartMeromorphic_jN N hpos hN⟩
  have he : lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ) =
        (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F := by
    rw [lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul,one_smul]
    apply (lpsOriginalCompactRestrictedMeromorphicEquiv N hN).injective
    change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
        (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN
          (lpsOriginalGeneratedQToComplex N hpos αQ))) =
      lpsOriginalCompactToRestrictedMeromorphic N hN
        ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F)
    rw [RingEquiv.apply_symm_apply,lpsOriginalCompactToRestrictedMeromorphic_apply]
    apply Subtype.ext
    change lpsOriginalHolomorphicFractionToMeromorphicGerm
      (lpsOriginalJNInFractionField N hpos) =
      (lpsOriginalFilledMeromorphicRestriction N hN
        (lpsOriginalFilledJDilated N hpos)
        (lpsOriginalFilledChartMeromorphic_jN N hpos hN)).val
    rw [lpsOriginalJNInFractionField,
      lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
    exact (lpsOriginalFilledMeromorphicRestriction_jN N hpos hN).symm
  exact congrArg Subtype.val he


/-- Embed the same rational j base in the actual normal glued scheme generic stalk. -/
def lpsOriginalIntegerNormalGenericJFractionEmbedding
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    FractionRing (Polynomial ℚ) →+*
      (lpsOriginalIntegerNormalGluedScheme N hpos).functionField := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  exact (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hpos).symm.toRingHom.comp
    (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hpos))

/-- The genuine generic-stalk equivalence preserves the actual rational j base. -/
def lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    (lpsOriginalIntegerNormalGluedScheme N hpos).functionField ≃ₐ[FractionRing (Polynomial ℚ)]
      lpsOriginalGeneratedFunctionFieldQ N hpos := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  let := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
  let e := lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hpos
  refine { e with commutes' := ?_ }
  intro r
  exact e.apply_symm_apply _

/-- The actual integer normal generic field extends to the ENTIRE original compact meromorphic field. -/
def lpsOriginalIntegerNormalGenericCompactTensorEquiv
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    (FractionRing (Polynomial ℂ)) ⊗[FractionRing (Polynomial ℚ)]
      ((lpsOriginalIntegerNormalGluedScheme N hpos).functionField) ≃ₐ[FractionRing (Polynomial ℂ)]
        LPSOriginalCompactMeromorphicGermRing N hN := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  let := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : FractionRing (Polynomial ℂ) ≃ₐ[FractionRing (Polynomial ℂ)]
    FractionRing (Polynomial ℂ))
    (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos)).trans
      (lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN)

/-- The arithmetic tensor comparison preserves the genuine generic-stalk function values. -/
lemma lpsOriginalIntegerNormalGenericCompactTensorEquiv_tmul
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ (r : FractionRing (Polynomial ℂ))
      (x : (lpsOriginalIntegerNormalGluedScheme N hpos).functionField),
    lpsOriginalIntegerNormalGenericCompactTensorEquiv N hpos hN
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
      r • lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
        (lpsOriginalGeneratedQToComplex N hpos
          (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos x)) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hpos
  let := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
  let := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
  intro r x
  change lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
    ((Algebra.TensorProduct.congr
      (AlgEquiv.refl : FractionRing (Polynomial ℂ) ≃ₐ[FractionRing (Polynomial ℂ)]
        FractionRing (Polynomial ℂ))
      (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos))
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x)) = _
  simp only [Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom]
  exact lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul N hpos hN r _


end ScalarExtension

end
end QEC.Coding.TannerLiftedProduct
