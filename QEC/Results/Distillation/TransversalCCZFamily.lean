import QEC.Distillation.MultiplicativeQuditProtocol.BinaryFamily

/-!
# Good binary transversal-CCZ family

Final theorem assembly over the reusable Distillation methods.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter

/--
The source-backed binary CSS family, with two-sided linear bounds, actual
quantum distance, disjoint inverse-permuted triples of positive density,
and full tensor-encoding CCZ intertwining [Ngu24, Main result and Step 3].

All families and operators in the statement are the concrete constructions
above; no family, distance, gate action, or parameter conclusion is assumed.
-/
theorem transversal_ccz_good_code :
    Tendsto binaryLength atTop atTop ∧
    ∀ i : Nat,
      binaryLength i = 512 * (f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i) ∧
      binaryLength i = Fintype.card ((f256SourceInput i).PivotComplement × Fin 512) ∧
      f256MultiplicationLogicalCount i = f256GarciaStichtenothLength i / 10 ∧
      (binaryEncodedCode i).code = (binaryCSSCode i).stabilizer.code ∧
      (binaryCSSCode i).stabilizer.code.dimension = 2 ^ f256MultiplicationLogicalCount i ∧
      QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i) ∧
      (¬ QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i + 1)) ∧
      (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤ binaryDistance i ∧
      ((binaryLength i : ℚ) / 10240 ≤ f256MultiplicationLogicalCount i ∧
        (f256MultiplicationLogicalCount i : ℚ) ≤ binaryLength i) ∧
      ((binaryLength i : ℚ) / 5120 ≤ binaryDistance i ∧ (binaryDistance i : ℚ) ≤ binaryLength i) ∧
      (binaryLength i : ℚ) / 512 ≤ (binarySelectedSites (f256SourceInput i).PivotComplement).card ∧
      (∀ x, (binaryTripleSupport (f256SourceInput i).PivotComplement x).card = 3) ∧
      (∀ x y, x ≠ y → Disjoint
        (binaryTripleSupport (f256SourceInput i).PivotComplement x)
        (binaryTripleSupport (f256SourceInput i).PivotComplement y)) ∧
      (binaryPhysicalFactorization (J := (f256SourceInput i).PivotComplement)).factorCount =
        (binarySelectedSites (f256SourceInput i).PivotComplement).card ∧
      (∀ phi : Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)),
        binaryEncodingIsometry i phi =
          mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement
            (selfDualIsometry (f256SourceInput i).PivotComplement
              ((f256SourceInput i).encodingLinearMap
                (logicalIsometry (Fin (f256MultiplicationLogicalCount i)) phi)))) ∧
      ∀ psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i)),
        binaryPhysicalCCZ
            (taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
              ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi) =
          taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
            ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap
              (binaryLogicalCCZ psi) := by
  refine ⟨binaryLength_tendsto_atTop, fun i => ?_⟩
  exact ⟨rfl, binaryLength_eq_card i, rfl, binaryEncodedCode_code_eq_cssCode i, binaryCSSCode_dimension i,
    (binaryCSSCode_distance i).1, (binaryCSSCode_distance i).2,
    binaryDistance_source_lower i, binaryLogicalCount_bounds i, binaryDistance_bounds i,
    binaryFamily_selected_density i, binaryTripleSupport_card _,
    fun _ _ h => binaryTripleSupport_disjoint _ h, binaryFamily_factorCount i,
    binaryEncodingIsometry_selfDual_apply i,
    binaryFamily_tensor_intertwining i⟩

end QEC.Distillation.Ngu24Binary
