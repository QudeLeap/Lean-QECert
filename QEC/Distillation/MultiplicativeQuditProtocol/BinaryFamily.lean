import QEC.Distillation.MultiplicativeQuditProtocol.BinaryParameters
import QEC.Distillation.MultiplicativeQuditProtocol.BinarySelfDual
import QEC.Distillation.MultiplicativeQuditProtocol.BinaryCubicBridge
import QEC.Distillation.MultiplicativeQuditProtocol.BinaryTensorEncoding

/-!
# The concrete Ngu24 binary CSS family with disjoint transversal CCZ

The fixed source-permitted instantiation uses `m = 8`, RMFE width one and
MFE length 512. The code is the actual binary CSS common-fixed carrier, its
distance is the attained semantic distance, and its encoding is the actual
RMFE/qudit/self-dual/MFE construction. The physical operator is the finite
product on the selected inverse-permuted triples. The final all-state
equation uses the literal tensor cube of the one-block encoder.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter

/-- Specialization of the full source intertwining to the actual tower family. -/
theorem binaryFamily_tagged_intertwining (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryPhysicalCCZ (binaryTaggedEncodingLinearMap i psi) =
      binaryTaggedEncodingLinearMap i (binaryLogicalCCZ psi) := by
  have h := sourceBinaryTaggedEncoding_intertwining (f256SourceInput i) psi
  change binaryPhysicalCCZ (binaryTaggedEncodingLinearMap i psi) =
    binaryTaggedEncodingLinearMap i _ at h
  refine h.trans (congrArg (binaryTaggedEncodingLinearMap i) ?_)
  ext label
  simp only [binaryLogicalCCZ, Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_apply,
    Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude,
    Ngu24MultiplicativeCCZ.taggedCubicPhaseExponent, LinearMap.id_apply]

/-- The family equation through the literal tensor cube, for every logical state. -/
theorem binaryFamily_tensor_intertwining (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryPhysicalCCZ
        (taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
          ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi) =
      taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
        ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap
          (binaryLogicalCCZ psi) := by
  rw [← binaryTaggedEncodingIsometry_eq_tensorCube,
    ← binaryTaggedEncodingIsometry_eq_tensorCube]
  exact binaryFamily_tagged_intertwining i psi

/-- The distance is an attained quantum distance on the actual CSS carrier. -/
theorem binaryCSSCode_distance (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i) ∧
      ¬ QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i + 1) := by
  rw [← binaryEncodedCode_code_eq_cssCode]
  exact ⟨binaryDistance_detects i, binaryDistance_fails_succ i⟩

/-- The fixed selected-triple fraction uses the entire physical length of one block. -/
theorem binaryFamily_selected_density (i : Nat) :
    (binaryLength i : ℚ) / 512 ≤ (binarySelectedSites (f256SourceInput i).PivotComplement).card := by
  rw [binaryLength_eq_card]
  exact binarySelectedSites_global_density _

/-- The factor count of the actual physical product equals the number of selected triples. -/
theorem binaryFamily_factorCount (i : Nat) :
    (binaryPhysicalFactorization (J := (f256SourceInput i).PivotComplement)).factorCount =
      (binarySelectedSites (f256SourceInput i).PivotComplement).card := by
  simp only [binaryPhysicalFactorization, Fintype.card_coe]

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
