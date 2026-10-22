import QEC.Coding.CodeReduction.DistanceBalancing.Dimension
import QEC.Coding.ChainComplex.Homotopy
import QEC.Coding.CSS.Subsystem

/-!
# Subsystem logical projections through EKZ distance balancing

The ordinary EKZ distance theorems are insufficient for a source subsystem
code: a nontrivial full homology class may be gauge.  This module keeps the
source logical projections visible on every EKZ slice and proves the two
dressed-distance estimates directly for those projected slices.
-/

namespace QEC.Coding.DistanceBalancingSubsystem

open QEC.Coding
open QEC.Coding.DistanceBalancing
open scoped TensorProduct

universe u v

variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Nonempty classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable {LogicalZ LogicalX : Type v}
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]

variable (SD : SubsystemCSSData xZero xOne xTwo LogicalZ LogicalX)
variable (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
  Word (ZMod 2) classicalCheck)

noncomputable abbrev productData :=
  DistanceBalancing.Data.ofComplexes SD.complex Y

noncomputable def sourceToOriginal : ThreeTermChainMap
    (sourceChainComplex (productData SD Y)) SD.complex where
  map0 := LinearMap.id
  map1 := LinearMap.id
  map2 := LinearMap.id
  commutes_boundary1 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]
  commutes_boundary2 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]

noncomputable def originalToSource : ThreeTermChainMap SD.complex
    (sourceChainComplex (productData SD Y)) where
  map0 := LinearMap.id
  map1 := LinearMap.id
  map2 := LinearMap.id
  commutes_boundary1 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]
  commutes_boundary2 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]

noncomputable def sourceHomologyProjection :
    (sourceChainComplex (productData SD Y)).middleHomology →ₗ[ZMod 2]
      LogicalZ :=
  SD.homologyProjection.comp (sourceToOriginal SD Y).inducedMiddleHomology

noncomputable def sourceCohomologyProjection :
    (sourceChainComplex (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      LogicalX :=
  SD.cohomologyProjection.comp
    (originalToSource SD Y).inducedMiddleCohomology

theorem sourceHomologyProjection_surjective :
    Function.Surjective (sourceHomologyProjection SD Y) := by
  intro z
  obtain ⟨h, rfl⟩ := SD.homologyProjection_surjective z
  obtain ⟨c, rfl⟩ :=
    SD.complex.middleBoundaryInCycles.mkQ_surjective h
  refine ⟨(sourceChainComplex (productData SD Y)).middleBoundaryInCycles.mkQ
    ⟨c.1, by simpa [productData] using c.2⟩, ?_⟩
  rw [sourceHomologyProjection, LinearMap.comp_apply,
    ThreeTermChainMap.inducedMiddleHomology_mk]
  congr 2

theorem sourceCohomologyProjection_surjective :
    Function.Surjective (sourceCohomologyProjection SD Y) := by
  intro x
  obtain ⟨h, rfl⟩ := SD.cohomologyProjection_surjective x
  obtain ⟨c, rfl⟩ :=
    SD.complex.middleCoboundaryInCocycles.mkQ_surjective h
  refine ⟨(sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
    ⟨c.1, by simpa [productData] using c.2⟩, ?_⟩
  rw [sourceCohomologyProjection, LinearMap.comp_apply,
    ThreeTermChainMap.inducedMiddleCohomology_mk]
  congr 2
  apply Subtype.ext
  simp [ThreeTermChainMap.mapMiddleCocycle, originalToSource,
    wordLinearMapTranspose_id]

/-- Selected source logical quotient tensored with the classical kernel. -/
noncomputable def sourceLogicalTensorProjection :
    (sourceChainComplex (productData SD Y)).middleHomology ⊗[ZMod 2]
        ClassicalKernel (productData SD Y) →ₗ[ZMod 2]
      LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) :=
  TensorProduct.map (sourceHomologyProjection SD Y) LinearMap.id

/-- Selected Z-logical slices as a linear map on product homology. -/
noncomputable def selectedHomologySliceMap :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleHomology →ₗ[ZMod 2]
      classicalBit → LogicalZ where
  toFun h := fun a => sourceHomologyProjection SD Y
    (homologySliceMap (productData SD Y) h a)
  map_add' h₁ h₂ := by
    funext a
    simp
  map_smul' c h := by
    funext a
    simp

/-- Canonical tensor-to-slices inclusion for the selected Z logical space. -/
noncomputable def kernelTensorToZLogicalSlices :
    LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) →ₗ[ZMod 2]
      classicalBit → LogicalZ :=
  (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      LogicalZ classicalBit).toLinearMap.comp
    ((ClassicalKernel (productData SD Y)).subtype.lTensor LogicalZ)

@[simp]
theorem kernelTensorToZLogicalSlices_tmul
    (z : LogicalZ) (w : ClassicalKernel (productData SD Y)) :
    kernelTensorToZLogicalSlices SD Y (z ⊗ₜ[ZMod 2] w) =
      fun a => w.1 a • z := by
  ext a
  simp [kernelTensorToZLogicalSlices,
    TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

theorem kernelTensorToZLogicalSlices_injective :
    Function.Injective (kernelTensorToZLogicalSlices SD Y) := by
  apply Function.Injective.comp
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      LogicalZ classicalBit).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (ClassicalKernel (productData SD Y)).subtype
    (ClassicalKernel (productData SD Y)).injective_subtype

noncomputable def kernelTensorZLogicalRetraction :
    (classicalBit → LogicalZ) →ₗ[ZMod 2]
      LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) :=
  (kernelTensorToZLogicalSlices SD Y).leftInverse

theorem kernelTensorZLogicalRetraction_apply
    (t : LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y)) :
    kernelTensorZLogicalRetraction SD Y
        (kernelTensorToZLogicalSlices SD Y t) = t := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr
      (kernelTensorToZLogicalSlices_injective SD Y)) t

theorem selectedHomologySliceMap_comp_tensorHomologyMap :
    (selectedHomologySliceMap SD Y).comp
        (tensorHomologyMap (productData SD Y)) =
      (kernelTensorToZLogicalSlices SD Y).comp
        (sourceLogicalTensorProjection SD Y) := by
  apply TensorProduct.ext'
  intro h w
  ext a
  change sourceHomologyProjection SD Y
      (homologySliceMap (productData SD Y)
        (tensorHomologyMap (productData SD Y) (h ⊗ₜ[ZMod 2] w)) a) =
    kernelTensorToZLogicalSlices SD Y
      (TensorProduct.map (sourceHomologyProjection SD Y) LinearMap.id
        (h ⊗ₜ[ZMod 2] w)) a
  rw [TensorProduct.map_tmul, kernelTensorToZLogicalSlices_tmul]
  rw [homologySliceMap_tensorHomologyMap_tmul, map_smul]
  rfl

/-- Natural selected Z-logical projection on the distance-balanced product. -/
noncomputable def productHomologyProjection :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleHomology →ₗ[ZMod 2]
      LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) :=
  (kernelTensorZLogicalRetraction SD Y).comp
    (selectedHomologySliceMap SD Y)

theorem productHomologyProjection_tensorHomologyMap
    (t : (sourceChainComplex (productData SD Y)).middleHomology ⊗[ZMod 2]
      ClassicalKernel (productData SD Y)) :
    productHomologyProjection SD Y
        (tensorHomologyMap (productData SD Y) t) =
      sourceLogicalTensorProjection SD Y t := by
  rw [productHomologyProjection, LinearMap.comp_apply]
  have hSlices := LinearMap.congr_fun
    (selectedHomologySliceMap_comp_tensorHomologyMap SD Y) t
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hSlices
  rw [hSlices, kernelTensorZLogicalRetraction_apply]

theorem productHomologyProjection_surjective :
    Function.Surjective (productHomologyProjection SD Y) := by
  intro z
  have hTensor : Function.Surjective (sourceLogicalTensorProjection SD Y) := by
    apply TensorProduct.map_surjective
    · exact sourceHomologyProjection_surjective SD Y
    · intro w
      exact ⟨w, rfl⟩
  obtain ⟨t, rfl⟩ := hTensor z
  exact ⟨tensorHomologyMap (productData SD Y) t,
    productHomologyProjection_tensorHomologyMap SD Y t⟩

/-- The family of selected source-Z logical slices of a product cycle. -/
noncomputable def selectedHomologySlices
    (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier) :
    classicalBit → LogicalZ :=
  fun a => sourceHomologyProjection SD Y
    (sourceHomologySlice (productData SD Y) z hz a)

/-- Dressed Z-distance for the natural product projection.  Nontriviality is
tested only after every source slice is sent to the selected source logical
sector, so gauge classes do not count as logical operators. -/
def ProductDressedZDistanceAtLeast (d : Nat) : Prop :=
  ∀ (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier),
    selectedHomologySlices SD Y z hz ≠ 0 → d ≤ HammingWeight z

/-- The selected source-X logical classes of the kernel-projected source
cochains used in the EKZ cohomological proof. -/
noncomputable def selectedCohomologySlices
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier) :
    classicalBit → LogicalX :=
  fun a => sourceCohomologyProjection SD Y
    ((sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
      ⟨projectedSourceCochain (productData SD Y) S x a, by
        simpa [productData] using
          projectedSourceCochain_mem_middleCocycleCode
            (productData SD Y) S hS x hx a⟩)

/-- Dressed X-distance for the natural kernel-projected cohomology slices. -/
def ProductDressedXDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (d : Nat) : Prop :=
  ∀ (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier),
    selectedCohomologySlices SD Y S hS x hx ≠ 0 →
      d ≤ HammingWeight x

theorem exists_ne_zero_coordinate
    {i M : Type*} [Nonempty i] [Zero M]
    (f : i → M) (hf : f ≠ 0) : ∃ i, f i ≠ 0 := by
  by_contra h
  apply hf
  funext i
  exact not_ne_iff.mp ((not_exists.mp h) i)

/-- The source dressed-Z bound controls the weighted support of every scalar
functional applied after the selected logical projection. -/
theorem mul_hammingWeight_selectedFunctional_le
    {d : Nat}
    (hSource : SD.DressedZDistanceAtLeast d)
    (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier)
    (phi : Module.Dual (ZMod 2) LogicalZ) :
    d * HammingWeight
        (classicalWordOfHomologyFunctional (productData SD Y) z hz
          (phi.comp (sourceHomologyProjection SD Y))) ≤
      HammingWeight z := by
  rw [DistanceBalancing.HammingWeight_eq_sum_indicator, Finset.mul_sum]
  apply (Finset.sum_le_sum fun a _ha => ?_).trans
    (DistanceBalancing.sum_HammingWeight_xOneBitSlice_le z)
  by_cases ha : classicalWordOfHomologyFunctional
      (productData SD Y) z hz
        (phi.comp (sourceHomologyProjection SD Y)) a ≠ 0
  · rw [if_pos ha, mul_one]
    apply hSource (xOneBitSlice z a)
      (by
        simpa [productData] using
          xOneBitSlice_mem_middleCycleCode (productData SD Y) z hz a)
    intro hProjected
    apply ha
    change phi (sourceHomologyProjection SD Y
      (sourceHomologySlice (productData SD Y) z hz a)) = 0
    rw [sourceHomologyProjection, LinearMap.comp_apply, sourceHomologySlice,
      ThreeTermChainMap.inducedMiddleHomology_mk, sourceCycleSlice]
    change phi (SD.homologyProjection
      (SD.complex.middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice z a, _⟩)) = 0
    rw [hProjected, map_zero]
  · rw [if_neg ha, mul_zero]
    exact Nat.zero_le _

/-- EKZ homological distance multiplication for the selected subsystem
sector.  This is the dressed analogue of
`DistanceBalancing.middleHomologyDistanceAtLeast_mul`. -/
theorem productDressedZDistanceAtLeast_mul
    {dSource dClassical : Nat}
    (hSource : SD.DressedZDistanceAtLeast dSource)
    (hClassical : ClassicalDistanceAtLeast
      (productData SD Y).classicalBoundary dClassical) :
    ProductDressedZDistanceAtLeast SD Y (dClassical * dSource) := by
  intro z hz hSelected
  obtain ⟨a, ha⟩ := exists_ne_zero_coordinate
    (selectedHomologySlices SD Y z hz) hSelected
  obtain ⟨phi, hphi⟩ :=
    Module.Projective.exists_dual_eq_one (ZMod 2) ha
  let psi : Module.Dual (ZMod 2)
      (sourceChainComplex (productData SD Y)).middleHomology :=
    phi.comp (sourceHomologyProjection SD Y)
  let w := classicalWordOfHomologyFunctional (productData SD Y) z hz psi
  have hwKernel : Matrix.toLin' (productData SD Y).classicalBoundary w = 0 :=
    classicalWordOfHomologyFunctional_mem_kernel
      (productData SD Y) z hz psi
  have hwNonzero : w ≠ 0 := by
    intro hw
    have hAt := congrFun hw a
    change phi (selectedHomologySlices SD Y z hz a) = 0 at hAt
    rw [hphi] at hAt
    exact one_ne_zero hAt
  have hwBound : dSource * HammingWeight w ≤ HammingWeight z := by
    exact mul_hammingWeight_selectedFunctional_le SD Y hSource z hz phi
  exact distance_product_le_of_detectingClassicalWord
    (productData SD Y) hClassical w hwKernel hwNonzero hwBound

/-- EKZ cohomological distance preservation for the selected subsystem
sector.  A nonzero projected product class exposes an actual nonzero selected
source cohomology slice, to which the source dressed bound applies. -/
theorem productDressedXDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    {d : Nat}
    (hSource : SD.DressedXDistanceAtLeast d) :
    ProductDressedXDistanceAtLeast SD Y S hS d := by
  intro x hx hSelected
  obtain ⟨a, ha⟩ := exists_ne_zero_coordinate
    (selectedCohomologySlices SD Y S hS x hx) hSelected
  have ha' : SD.cohomologyProjection
      (SD.complex.middleCoboundaryInCocycles.mkQ
        ⟨projectedSourceCochain (productData SD Y) S x a, by
          simpa [productData] using
            projectedSourceCochain_mem_middleCocycleCode
              (productData SD Y) S hS x hx a⟩) ≠ 0 := by
    intro hZero
    apply ha
    change SD.cohomologyProjection
      ((originalToSource SD Y).inducedMiddleCohomology
        ((sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
          ⟨projectedSourceCochain (productData SD Y) S x a, _⟩)) = 0
    rw [ThreeTermChainMap.inducedMiddleCohomology_mk]
    convert hZero using 1
    congr 2
    apply Subtype.ext
    simp [ThreeTermChainMap.mapMiddleCocycle, originalToSource,
      wordLinearMapTranspose_id]
  have hLower := hSource
    (projectedSourceCochain (productData SD Y) S x a)
    (by
      simpa [productData] using
        projectedSourceCochain_mem_middleCocycleCode
          (productData SD Y) S hS x hx a)
    ha'
  have hUpper : HammingWeight
      (projectedSourceCochain (productData SD Y) S x a) ≤
      HammingWeight x := by
    exact (HammingWeight_sourceCochainContraction_le x
      (classicalKernelProjectionWord (productData SD Y) S a)).trans
        (sum_HammingWeight_xOneBitSlice_le_product x)
  exact hLower.trans hUpper

end QEC.Coding.DistanceBalancingSubsystem
