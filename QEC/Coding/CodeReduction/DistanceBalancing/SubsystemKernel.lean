import QEC.Coding.CodeReduction.DistanceBalancing.SubsystemDimension

/-!
# Distance balancing with a non-surjective classical boundary

The homological half of the EKZ product only uses the kernel and distance of
the classical boundary.  For subsystem codes, the cohomological logical
sector can likewise be selected without a right inverse: contract a product
cocycle against every classical kernel word and gauge out the complementary
cokernel summands.  The two selected logical spaces are then
`LogicalZ ⊗ ker Y` and `LogicalX ⊗ (ker Y)ᵛ`.
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

noncomputable abbrev ClassicalKernelDual :=
  Module.Dual (ZMod 2) (ClassicalKernel (productData SD Y))

/-- Contraction against one classical kernel word, as a linear map on raw
product cochains. -/
noncomputable def kernelCochainContractionLinear
    (w : ClassicalKernel (productData SD Y)) :
    Word (ZMod 2)
        (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck) →ₗ[ZMod 2]
      Word (ZMod 2) xOne where
  toFun x := sourceCochainContraction x w.1
  map_add' x y := by
    ext x1
    simp [sourceCochainContraction, xOneBitSlice, Finset.sum_add_distrib,
      mul_add]
  map_smul' c x := by
    ext x1
    simp [sourceCochainContraction, xOneBitSlice, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm]

theorem sourceCochainContraction_smul_kernel
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : ZMod 2) (w : Word (ZMod 2) classicalBit) :
    sourceCochainContraction x (c • w) =
      c • sourceCochainContraction x w := by
  ext x1
  simp only [sourceCochainContraction, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Kernel contraction sends product cocycles to source cocycles. -/
noncomputable def kernelCocycleContractionMap
    (w : ClassicalKernel (productData SD Y)) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      (sourceChainComplex
        (productData SD Y)).middleCocycleCode.carrier where
  toFun x := ⟨sourceCochainContraction x.1 w.1,
    sourceCochainContraction_mem_middleCocycleCode
      (productData SD Y) x.1 x.2 w.1 (LinearMap.mem_ker.mp w.2)⟩
  map_add' x y := by
    apply Subtype.ext
    exact (kernelCochainContractionLinear SD Y w).map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (kernelCochainContractionLinear SD Y w).map_smul c x.1

/-- A selected source logical-X class obtained by kernel contraction. -/
noncomputable def selectedKernelCohomologyClass
    (w : ClassicalKernel (productData SD Y)) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2] LogicalX :=
  (sourceCohomologyProjection SD Y).comp
    ((sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ.comp
        (kernelCocycleContractionMap SD Y w))

/-- All kernel-contracted logical-X classes, linear in the kernel word. -/
noncomputable def selectedKernelCohomologyCycleMap :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      ClassicalKernel (productData SD Y) →ₗ[ZMod 2] LogicalX where
  toFun x :=
    { toFun := fun w => selectedKernelCohomologyClass SD Y w x
      map_add' := by
        intro w₁ w₂
        have hcontraction :
            kernelCocycleContractionMap SD Y (w₁ + w₂) x =
              kernelCocycleContractionMap SD Y w₁ x +
                kernelCocycleContractionMap SD Y w₂ x := by
          apply Subtype.ext
          exact sourceCochainContraction_add x.1 w₁.1 w₂.1
        simp only [selectedKernelCohomologyClass, LinearMap.comp_apply]
        rw [hcontraction, map_add, map_add]
      map_smul' := by
        intro c w
        have hcontraction :
            kernelCocycleContractionMap SD Y (c • w) x =
              c • kernelCocycleContractionMap SD Y w x := by
          apply Subtype.ext
          exact sourceCochainContraction_smul_kernel x.1 c w.1
        simp only [selectedKernelCohomologyClass, LinearMap.comp_apply]
        rw [hcontraction, map_smul, map_smul]
        rfl }
  map_add' x y := by
    apply LinearMap.ext
    intro w
    exact (selectedKernelCohomologyClass SD Y w).map_add x y
  map_smul' c x := by
    apply LinearMap.ext
    intro w
    exact (selectedKernelCohomologyClass SD Y w).map_smul c x

/-- Contracting a product coboundary against a kernel word gives a source
coboundary. -/
theorem kernelCochainContraction_mem_firstCoboundary_of_productCoboundary
    (w : ClassicalKernel (productData SD Y))
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).firstCoboundaryCheckCode.carrier) :
    sourceCochainContraction x w.1 ∈
      (sourceChainComplex
        (productData SD Y)).firstCoboundaryCheckCode.carrier := by
  rcases ((DistanceBalancing.chainComplex
    (productData SD Y)).mem_firstCoboundaryCheckCode_iff x).mp hx with ⟨u, rfl⟩
  apply ((sourceChainComplex
    (productData SD Y)).mem_firstCoboundaryCheckCode_iff _).mpr
  refine ⟨sourceZeroCochainContraction u w.1, ?_⟩
  exact (sourceCochainContraction_transpose_boundary1 SD Y u w.1
    (LinearMap.mem_ker.mp w.2)).symm

theorem middleCoboundary_le_ker_selectedKernelCohomologyCycleMap :
    (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles ≤
      LinearMap.ker (selectedKernelCohomologyCycleMap SD Y) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro w
  change selectedKernelCohomologyClass SD Y w x = 0
  rw [selectedKernelCohomologyClass, LinearMap.comp_apply,
    LinearMap.comp_apply]
  let p := kernelCocycleContractionMap SD Y w x
  have hp : p ∈ (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles :=
    kernelCochainContraction_mem_firstCoboundary_of_productCoboundary
      SD Y w x.1 hx
  have hzero : (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ p = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles).mpr hp
  rw [hzero, map_zero]

/-- Selected product cohomology projection with no full-row-rank hypothesis
on the classical boundary. -/
noncomputable def kernelCohomologyProjection :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      ClassicalKernel (productData SD Y) →ₗ[ZMod 2] LogicalX :=
  (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles.liftQ
    (selectedKernelCohomologyCycleMap SD Y)
    (middleCoboundary_le_ker_selectedKernelCohomologyCycleMap SD Y)

@[simp]
theorem kernelCohomologyProjection_mk
    (x : (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier) :
    kernelCohomologyProjection SD Y
        ((DistanceBalancing.chainComplex
          (productData SD Y)).middleCoboundaryInCocycles.mkQ x) =
      selectedKernelCohomologyCycleMap SD Y x := rfl

/-- A nonzero selected kernel-contracted logical class exposes a source
dressed-X representative of no larger weight. -/
theorem kernelCohomologyProjection_dressedXDistanceAtLeast
    {d : Nat} (hSource : SD.DressedXDistanceAtLeast d)
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier)
    (hLogical : kernelCohomologyProjection SD Y
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ ⟨x, hx⟩) ≠ 0) :
    d ≤ HammingWeight x := by
  rw [kernelCohomologyProjection_mk] at hLogical
  have hexists : ∃ w : ClassicalKernel (productData SD Y),
      selectedKernelCohomologyCycleMap SD Y ⟨x, hx⟩ w ≠ 0 := by
    by_contra h
    apply hLogical
    apply LinearMap.ext
    intro w
    exact not_ne_iff.mp ((not_exists.mp h) w)
  obtain ⟨w, hw⟩ := hexists
  have hLower := hSource
    (sourceCochainContraction x w.1)
    (by
      simpa [productData] using
        sourceCochainContraction_mem_middleCocycleCode
          (productData SD Y) x hx w.1 (LinearMap.mem_ker.mp w.2))
    (by
      intro hzero
      apply hw
      change sourceCohomologyProjection SD Y
          ((sourceChainComplex
            (productData SD Y)).middleCoboundaryInCocycles.mkQ
              (kernelCocycleContractionMap SD Y w ⟨x, hx⟩)) = 0
      rw [sourceCohomologyProjection, LinearMap.comp_apply,
        ThreeTermChainMap.inducedMiddleCohomology_mk]
      convert hzero using 1
      congr 2
      apply Subtype.ext
      change wordLinearMapTranspose LinearMap.id
        (sourceCochainContraction x w.1) = sourceCochainContraction x w.1
      exact LinearMap.congr_fun wordLinearMapTranspose_id _)
  exact hLower.trans
    ((HammingWeight_sourceCochainContraction_le x w.1).trans
      (sum_HammingWeight_xOneBitSlice_le_product x))

/-! ## Surjectivity and the full subsystem package -/

/-- Linear retraction from ambient classical words onto the kernel. -/
noncomputable def classicalKernelRetraction :
    Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      ClassicalKernel (productData SD Y) :=
  (ClassicalKernel (productData SD Y)).subtype.leftInverse

@[simp]
theorem classicalKernelRetraction_apply
    (w : ClassicalKernel (productData SD Y)) :
    classicalKernelRetraction SD Y w.1 = w := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr
      (ClassicalKernel (productData SD Y)).injective_subtype) w

/-- A linear source-cohomology representative for each selected logical-X
class. -/
noncomputable def sourceLogicalCohomologySection :
    LogicalX →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology :=
  Classical.choose
    ((sourceCohomologyProjection SD Y).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (sourceCohomologyProjection_surjective SD Y)))

@[simp]
theorem sourceLogicalCohomologySection_spec (x : LogicalX) :
    sourceCohomologyProjection SD Y
      (sourceLogicalCohomologySection SD Y x) = x := by
  have hRight := Classical.choose_spec
    ((sourceCohomologyProjection SD Y).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (sourceCohomologyProjection_surjective SD Y)))
  exact LinearMap.congr_fun hRight x

/-- Place an arbitrary linear family of source cohomology classes in the
first block of the product cochain space. -/
noncomputable def cohomologyFamilyCochain
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology) :
    Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Sum.elim
    (fun p => (sourceCocycleSection SD Y (g (Pi.single p.2 1))).1 p.1)
    (fun _ => 0)

theorem xOneBitSlice_cohomologyFamilyCochain
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology)
    (a : classicalBit) :
    xOneBitSlice (cohomologyFamilyCochain SD Y g) a =
      (sourceCocycleSection SD Y (g (Pi.single a 1))).1 := by
  rfl

theorem cohomologyFamilyCochain_mem_middleCocycleCode
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology) :
    cohomologyFamilyCochain SD Y g ∈
      (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier := by
  rw [(DistanceBalancing.chainComplex
    (productData SD Y)).mem_middleCocycleCode_iff]
  ext p
  rcases p with ⟨x2, a⟩
  change wordLinearMapTranspose (DistanceBalancing.boundary2
    (productData SD Y)) (cohomologyFamilyCochain SD Y g) (x2, a) = 0
  rw [DistanceBalancing.transpose_boundary2_apply]
  have hCocycle := (sourceCocycleSection SD Y (g (Pi.single a 1))).2
  have hAt := congrFun
    (((sourceChainComplex
      (productData SD Y)).mem_middleCocycleCode_iff _).mp hCocycle) x2
  simp only [Pi.zero_apply] at hAt
  change wordLinearMapTranspose
    (Matrix.toLin' (productData SD Y).xBoundary2)
      (sourceCocycleSection SD Y (g (Pi.single a 1))).1 x2 = 0 at hAt
  rw [wordLinearMapTranspose_toLin'_apply] at hAt
  simp only [xOneBitSlice_cohomologyFamilyCochain,
    cohomologyFamilyCochain, xTwoCheckSlice, Sum.elim_inr, mul_zero,
    Finset.sum_const_zero, add_zero]
  simp only [mul_comm] at hAt
  exact hAt

/-- Kernel contraction of a realized cohomology family recovers the family
value on that kernel word. -/
theorem cohomologyClass_sourceCochainContraction_family
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalKernel (productData SD Y)) :
    (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ
        ⟨sourceCochainContraction (cohomologyFamilyCochain SD Y g) w.1,
          sourceCochainContraction_mem_middleCocycleCode
            (productData SD Y) (cohomologyFamilyCochain SD Y g)
            (cohomologyFamilyCochain_mem_middleCocycleCode SD Y g)
            w.1 (LinearMap.mem_ker.mp w.2)⟩ = g w.1 := by
  rw [← sourceCocycleSection_spec SD Y (g w.1)]
  congr 1
  apply Subtype.ext
  ext x1
  simp only [sourceCochainContraction, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, xOneBitSlice_cohomologyFamilyCochain]
  have hw : (∑ a : classicalBit, w.1 a • Pi.single a 1) = w.1 := by
    calc
      (∑ a : classicalBit, w.1 a • Pi.single a 1) =
          ∑ a : classicalBit, Pi.single a (w.1 a) := by
        apply Finset.sum_congr rfl
        intro a _
        ext a'
        simp [Pi.single_apply, smul_eq_mul]
      _ = w.1 := Finset.univ_sum_single w.1
  calc
    (∑ a : classicalBit,
        w.1 a * (sourceCocycleSection SD Y (g (Pi.single a 1))).1 x1) =
      (∑ a : classicalBit,
        w.1 a • sourceCocycleSection SD Y (g (Pi.single a 1))).1 x1 := by
        change (∑ a : classicalBit,
          w.1 a * (sourceCocycleSection SD Y (g (Pi.single a 1))).1 x1) =
            (Submodule.subtype _
              (∑ a : classicalBit,
                w.1 a • sourceCocycleSection SD Y (g (Pi.single a 1)))) x1
        rw [map_sum]
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro a _
        rfl
    _ = (sourceCocycleSection SD Y
        (g (∑ a : classicalBit, w.1 a • Pi.single a 1))).1 x1 := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    _ = (sourceCocycleSection SD Y (g w.1)).1 x1 := by rw [hw]

/-- Every linear map from the classical kernel to the selected source
logical-X sector is realized by an actual product cohomology class. -/
theorem kernelCohomologyProjection_surjective :
    Function.Surjective (kernelCohomologyProjection SD Y) := by
  intro f
  let g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology :=
    (sourceLogicalCohomologySection SD Y).comp
      (f.comp (classicalKernelRetraction SD Y))
  let c : (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier :=
    ⟨cohomologyFamilyCochain SD Y g,
      cohomologyFamilyCochain_mem_middleCocycleCode SD Y g⟩
  refine ⟨(DistanceBalancing.chainComplex
    (productData SD Y)).middleCoboundaryInCocycles.mkQ c, ?_⟩
  rw [kernelCohomologyProjection_mk]
  apply LinearMap.ext
  intro w
  change sourceCohomologyProjection SD Y
      ((sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ
          (kernelCocycleContractionMap SD Y w c)) = f w
  rw [show (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ
        (kernelCocycleContractionMap SD Y w c) = g w.1 by
    exact cohomologyClass_sourceCochainContraction_family SD Y g w]
  change sourceCohomologyProjection SD Y
    (sourceLogicalCohomologySection SD Y
      (f (classicalKernelRetraction SD Y w.1))) = f w
  rw [sourceLogicalCohomologySection_spec, classicalKernelRetraction_apply]

theorem finrank_classicalKernelDual :
    Module.finrank (ZMod 2) (ClassicalKernelDual SD Y) =
      Module.finrank (ZMod 2) (ClassicalKernel (productData SD Y)) := by
  exact Subspace.dual_finrank_eq

/-- The distance-balanced subsystem selected only by the classical kernel.

Unlike `balancedSubsystemData`, this package does not require a right inverse
for the classical boundary.  Any extra classical cokernel classes are placed
in the cohomological gauge sector rather than silently assumed away. -/
noncomputable def balancedKernelSubsystemData :
    SubsystemCSSData
      (DistanceBalancing.C0Index xZero xOne classicalBit classicalCheck)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck)
      (DistanceBalancing.C2Index xTwo classicalBit)
      (LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y))
      (ClassicalKernel (productData SD Y) →ₗ[ZMod 2] LogicalX) where
  complex := DistanceBalancing.chainComplex (productData SD Y)
  homologyProjection := productHomologyProjection SD Y
  cohomologyProjection := kernelCohomologyProjection SD Y
  homologyProjection_surjective := productHomologyProjection_surjective SD Y
  cohomologyProjection_surjective := kernelCohomologyProjection_surjective SD Y
  logical_finrank_eq := by
    rw [Module.finrank_tensorProduct, Module.finrank_linearMap,
      SD.logical_finrank_eq, Nat.mul_comm]

theorem balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
    {dSource dClassical : Nat}
    (hSource : SD.DressedZDistanceAtLeast dSource)
    (hClassical : ClassicalDistanceAtLeast
      (productData SD Y).classicalBoundary dClassical) :
    (balancedKernelSubsystemData SD Y).DressedZDistanceAtLeast
      (dClassical * dSource) := by
  intro z hz hLogical
  apply productDressedZDistanceAtLeast_mul SD Y hSource hClassical z hz
  intro hSlices
  apply hLogical
  change productHomologyProjection SD Y
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0
  rw [productHomologyProjection, LinearMap.comp_apply]
  have hMap : selectedHomologySliceMap SD Y
      ((DistanceBalancing.chainComplex
        (productData SD Y)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0 := by
    funext a
    change sourceHomologyProjection SD Y
        (sourceHomologySlice (productData SD Y) z hz a) = 0
    exact congrFun hSlices a
  rw [hMap, map_zero]

theorem balancedKernelSubsystemData_dressedXDistanceAtLeast
    {d : Nat} (hSource : SD.DressedXDistanceAtLeast d) :
    (balancedKernelSubsystemData SD Y).DressedXDistanceAtLeast d := by
  intro x hx hLogical
  exact kernelCohomologyProjection_dressedXDistanceAtLeast
    SD Y hSource x hx hLogical

theorem balancedKernelSubsystemData_logicalQubits :
    (balancedKernelSubsystemData SD Y).logicalQubits =
      SD.logicalQubits *
        Module.finrank (ZMod 2) (ClassicalKernel (productData SD Y)) := by
  simp [balancedKernelSubsystemData, SubsystemCSSData.logicalQubits,
    Module.finrank_tensorProduct]


end QEC.Coding.DistanceBalancingSubsystem
