import QEC.Coding.CodeReduction.DistanceBalancing.Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Logical dimension of the EKZ distance-balancing product

The product homology contains the tensor product of source middle homology
with the kernel of the classical boundary.  This file constructs that map and
proves it injective, giving the multiplicative logical-dimension bound used by
the HHO20 family theorem.
-/

namespace QEC.Coding.DistanceBalancing

universe u

open scoped TensorProduct

variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

abbrev ClassicalKernel := LinearMap.ker (Matrix.toLin' D.classicalBoundary)

/-- A linear choice of source-cycle representative for each source homology
class. -/
noncomputable def sourceCycleSection :
    (sourceChainComplex D).middleHomology →ₗ[ZMod 2]
      (sourceChainComplex D).middleCycleCode.carrier :=
  Classical.choose
    ((sourceChainComplex D).middleBoundaryInCycles.mkQ
      |>.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (Submodule.mkQ_surjective
            (sourceChainComplex D).middleBoundaryInCycles)))

theorem sourceCycleSection_spec
    (h : (sourceChainComplex D).middleHomology) :
    (sourceChainComplex D).middleBoundaryInCycles.mkQ
        (sourceCycleSection D h) = h := by
  have hRight := Classical.choose_spec
    ((sourceChainComplex D).middleBoundaryInCycles.mkQ
      |>.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (Submodule.mkQ_surjective
            (sourceChainComplex D).middleBoundaryInCycles)))
  exact LinearMap.congr_fun hRight h

/-- The pure tensor of a source homology class and a classical kernel word,
written in the first block of the EKZ middle chain group. -/
noncomputable def pureTensorWord
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Sum.elim
    (fun p => (sourceCycleSection D h).1 p.1 * w.1 p.2)
    (fun _ => 0)

theorem pureTensorWord_mem_middleCycleCode
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    pureTensorWord D h w ∈ (chainComplex D).middleCycleCode.carrier := by
  rw [(chainComplex D).mem_middleCycleCode_iff]
  ext q
  cases q with
  | inl q =>
      rcases q with ⟨x0, a⟩
      simp only [Pi.zero_apply]
      change boundary1 D (pureTensorWord D h w) (Sum.inl (x0, a)) = 0
      rw [boundary1_apply_inl]
      have hCycle := (sourceCycleSection D h).2
      have hZero := ((sourceChainComplex D).mem_middleCycleCode_iff
        (sourceCycleSection D h).1).mp hCycle
      change Matrix.toLin' D.xBoundary1 (sourceCycleSection D h).1 = 0 at hZero
      have hAt := congrFun hZero x0
      change
        (∑ x1 : xOne,
          D.xBoundary1 x0 x1 * (sourceCycleSection D h).1 x1) = 0 at hAt
      have hAt' :
          (∑ x1 : xOne,
            D.xBoundary1 x0 x1 * (sourceCycleSection D h).1 x1) = 0 := by
        exact hAt
      simp only [xOneBitSlice, pureTensorWord, Sum.elim_inl]
      calc
        (∑ x1 : xOne,
            D.xBoundary1 x0 x1 *
              ((sourceCycleSection D h).1 x1 * w.1 a)) =
            (∑ x1 : xOne,
              D.xBoundary1 x0 x1 * (sourceCycleSection D h).1 x1) *
                w.1 a := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro x1 _
                  rw [mul_assoc]
        _ = 0 := by rw [hAt', zero_mul]
  | inr q =>
      rcases q with ⟨x1, b⟩
      simp only [Pi.zero_apply]
      change boundary1 D (pureTensorWord D h w) (Sum.inr (x1, b)) = 0
      rw [boundary1_apply_inr]
      have hKernel := LinearMap.mem_ker.mp w.2
      have hAt := congrFun hKernel b
      change
        (∑ a : classicalBit, D.classicalBoundary b a * w.1 a) = 0 at hAt
      have hAt' :
          (∑ a : classicalBit, D.classicalBoundary b a * w.1 a) = 0 := by
        exact hAt
      simp only [pureTensorWord, xOneBitSlice, Sum.elim_inl,
        xTwoCheckSlice, Sum.elim_inr, mul_zero, Finset.sum_const_zero,
        add_zero]
      calc
        (∑ a : classicalBit,
            D.classicalBoundary b a *
              ((sourceCycleSection D h).1 x1 * w.1 a)) =
            (sourceCycleSection D h).1 x1 *
              (∑ a : classicalBit, D.classicalBoundary b a * w.1 a) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                ring
        _ = 0 := by rw [hAt', mul_zero]

/-- The pure tensor word, packaged as a product cycle. -/
noncomputable def pureTensorCycle
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    (chainComplex D).middleCycleCode.carrier :=
  ⟨pureTensorWord D h w, pureTensorWord_mem_middleCycleCode D h w⟩

/-- Bilinear pure-tensor cycle construction. -/
noncomputable def pureTensorCycleBilinear :
    (sourceChainComplex D).middleHomology →ₗ[ZMod 2]
      ClassicalKernel D →ₗ[ZMod 2]
        (chainComplex D).middleCycleCode.carrier where
  toFun h :=
    { toFun := pureTensorCycle D h
      map_add' := by
        intro w₁ w₂
        apply Subtype.ext
        ext q
        cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring
      map_smul' := by
        intro c w
        apply Subtype.ext
        ext q
        cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring }
  map_add' := by
    intro h₁ h₂
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext q
    cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring
  map_smul' := by
    intro c h
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext q
    cases q <;> simp [pureTensorCycle, pureTensorWord] <;> ring

/-- Linear extension from the tensor product into product cycles. -/
noncomputable def tensorCycleMap :
    (sourceChainComplex D).middleHomology ⊗[ZMod 2] ClassicalKernel D →ₗ[ZMod 2]
      (chainComplex D).middleCycleCode.carrier :=
  TensorProduct.lift (pureTensorCycleBilinear D)

@[simp]
theorem tensorCycleMap_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    tensorCycleMap D (h ⊗ₜ[ZMod 2] w) = pureTensorCycle D h w := by
  rfl

/-- The induced tensor-product subspace inside product homology. -/
noncomputable def tensorHomologyMap :
    (sourceChainComplex D).middleHomology ⊗[ZMod 2] ClassicalKernel D →ₗ[ZMod 2]
      (chainComplex D).middleHomology :=
  (chainComplex D).middleBoundaryInCycles.mkQ.comp (tensorCycleMap D)

@[simp]
theorem tensorHomologyMap_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    tensorHomologyMap D (h ⊗ₜ[ZMod 2] w) =
      (chainComplex D).middleBoundaryInCycles.mkQ
        (pureTensorCycle D h w) := by
  rfl

/-- Send a product cycle to its family of source homology slices. -/
noncomputable def cycleToHomologySlices :
    (chainComplex D).middleCycleCode.carrier →ₗ[ZMod 2]
      classicalBit → (sourceChainComplex D).middleHomology where
  toFun z := fun a =>
    (sourceChainComplex D).middleBoundaryInCycles.mkQ
      ⟨xOneBitSlice z.1 a, xOneBitSlice_mem_middleCycleCode D z.1 z.2 a⟩
  map_add' z₁ z₂ := by
    funext a
    change (sourceChainComplex D).middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice (z₁.1 + z₂.1) a, _⟩ =
      (sourceChainComplex D).middleBoundaryInCycles.mkQ
          ⟨xOneBitSlice z₁.1 a, _⟩ +
        (sourceChainComplex D).middleBoundaryInCycles.mkQ
          ⟨xOneBitSlice z₂.1 a, _⟩
    rw [← (sourceChainComplex D).middleBoundaryInCycles.mkQ.map_add]
    congr 1
  map_smul' c z := by
    funext a
    change (sourceChainComplex D).middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice (c • z.1) a, _⟩ =
      c • (sourceChainComplex D).middleBoundaryInCycles.mkQ
        ⟨xOneBitSlice z.1 a, _⟩
    rw [← (sourceChainComplex D).middleBoundaryInCycles.mkQ.map_smul]
    congr 1

/-- Product boundaries have trivial source homology in every slice. -/
theorem middleBoundaryInCycles_le_ker_cycleToHomologySlices :
    (chainComplex D).middleBoundaryInCycles ≤
      LinearMap.ker (cycleToHomologySlices D) := by
  intro z hz
  apply LinearMap.mem_ker.mpr
  funext a
  apply (Submodule.Quotient.mk_eq_zero
    (sourceChainComplex D).middleBoundaryInCycles).mpr
  change xOneBitSlice z.1 a ∈
    (sourceChainComplex D).middleBoundaryCode.carrier
  rcases ((chainComplex D).mem_middleBoundaryCode_iff z.1).mp hz with
    ⟨c, hc⟩
  apply ((sourceChainComplex D).mem_middleBoundaryCode_iff _).mpr
  refine ⟨xTwoBitSlice c a, ?_⟩
  ext x1
  change
    (∑ x2 : xTwo, D.xBoundary2 x1 x2 * xTwoBitSlice c a x2) =
      z.1 (Sum.inl (x1, a))
  calc
    _ = boundary2 D c (Sum.inl (x1, a)) :=
      (boundary2_apply_inl D c x1 a).symm
    _ = z.1 (Sum.inl (x1, a)) := congrFun hc _

/-- The slice map descends from product cycles to product homology. -/
noncomputable def homologySliceMap :
    (chainComplex D).middleHomology →ₗ[ZMod 2]
      classicalBit → (sourceChainComplex D).middleHomology :=
  (chainComplex D).middleBoundaryInCycles.liftQ
    (cycleToHomologySlices D)
    (middleBoundaryInCycles_le_ker_cycleToHomologySlices D)

@[simp]
theorem homologySliceMap_mk
    (z : (chainComplex D).middleCycleCode.carrier) :
    homologySliceMap D
        ((chainComplex D).middleBoundaryInCycles.mkQ z) =
      cycleToHomologySlices D z := by
  rfl

/-- On pure tensors, homology slices are scalar multiplication by the
classical kernel coordinates. -/
theorem homologySliceMap_tensorHomologyMap_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    homologySliceMap D (tensorHomologyMap D (h ⊗ₜ[ZMod 2] w)) =
      fun a => w.1 a • h := by
  ext a
  change (sourceChainComplex D).middleBoundaryInCycles.mkQ
      ⟨fun x1 => (sourceCycleSection D h).1 x1 * w.1 a, _⟩ =
    w.1 a • h
  calc
    _ = (sourceChainComplex D).middleBoundaryInCycles.mkQ
        (w.1 a • sourceCycleSection D h) := by
      congr 1
      apply Subtype.ext
      ext x1
      simp [smul_eq_mul, mul_comm]
    _ = w.1 a •
        (sourceChainComplex D).middleBoundaryInCycles.mkQ
          (sourceCycleSection D h) :=
      (sourceChainComplex D).middleBoundaryInCycles.mkQ.map_smul _ _
    _ = w.1 a • h := by rw [sourceCycleSection_spec D h]

/-- The canonical inclusion of a source-homology/classical-kernel tensor
into the family of source-homology slices. -/
noncomputable def kernelTensorToSlices :
    (sourceChainComplex D).middleHomology ⊗[ZMod 2] ClassicalKernel D →ₗ[ZMod 2]
      classicalBit → (sourceChainComplex D).middleHomology :=
  (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      (sourceChainComplex D).middleHomology classicalBit).toLinearMap.comp
    ((ClassicalKernel D).subtype.lTensor
      (sourceChainComplex D).middleHomology)

@[simp]
theorem kernelTensorToSlices_tmul
    (h : (sourceChainComplex D).middleHomology)
    (w : ClassicalKernel D) :
    kernelTensorToSlices D (h ⊗ₜ[ZMod 2] w) = fun a ↦ w.1 a • h := by
  ext a
  simp [kernelTensorToSlices, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

/-- The canonical tensor-to-slices map is injective. -/
theorem kernelTensorToSlices_injective :
    Function.Injective (kernelTensorToSlices D) := by
  apply Function.Injective.comp
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      (sourceChainComplex D).middleHomology classicalBit).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (ClassicalKernel D).subtype (ClassicalKernel D).injective_subtype

/-- Slicing the constructed product-homology class gives the canonical
tensor-to-slices inclusion. -/
theorem homologySliceMap_comp_tensorHomologyMap :
    (homologySliceMap D).comp (tensorHomologyMap D) =
      kernelTensorToSlices D := by
  apply TensorProduct.ext'
  intro h w
  rw [LinearMap.comp_apply,
    homologySliceMap_tensorHomologyMap_tmul D h w,
    kernelTensorToSlices_tmul D h w]

/-- The EKZ product contains the tensor product of source homology with the
classical kernel. -/
theorem tensorHomologyMap_injective :
    Function.Injective (tensorHomologyMap D) := by
  intro x y hxy
  apply kernelTensorToSlices_injective D
  rw [← homologySliceMap_comp_tensorHomologyMap D]
  exact congrArg (homologySliceMap D) hxy

/-- Multiplicative lower bound on the number of logical qubits in the EKZ
distance-balancing product. -/
theorem finrank_middleHomology_mul_finrank_classicalKernel_le :
    Module.finrank (ZMod 2) (sourceChainComplex D).middleHomology *
        Module.finrank (ZMod 2) (ClassicalKernel D) ≤
      Module.finrank (ZMod 2) (chainComplex D).middleHomology := by
  rw [← Module.finrank_tensorProduct]
  exact LinearMap.finrank_le_finrank_of_injective
    (tensorHomologyMap_injective D)

end QEC.Coding.DistanceBalancing
