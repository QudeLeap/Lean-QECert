import QEC.Distillation.MultiplicativeQuditProtocol.BinaryDistance
import QEC.Semantics.ErrorCorrection.FiniteMeasurementDistance

/-!
# The concrete binary family parameters

The distance is the attained semantic minimum, not the qudit lower bound
renamed. The actual encoder gives two orthogonal code states, ensuring finite
distance. All source bounds, both sides of linear rate/distance estimates,
and divergence are proved for the fixed family of [Ngu24, Main result].
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
open scoped BigOperators Topology

local instance {A : Type} [Fintype A] : Fintype (Word F256 A) := Fintype.ofFinite _

def binaryLength (i : Nat) : Nat := 512 * f256QuditLength i

def binaryDistance (i : Nat) : Nat :=
  QuditSubsystem.finiteMeasurementDistance
    (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2) (binaryEncodedCode i).code

theorem binaryLength_eq_card (i : Nat) :
    binaryLength i = Fintype.card ((f256SourceInput i).PivotComplement × Fin 512) := by
  simp only [binaryLength, f256QuditLength_eq_card, Fintype.card_prod, Fintype.card_fin]
  omega

theorem binaryEncodedCode_not_full_noInformation (i : Nat) :
    ¬ QuditSubsystem.NoInformationOn (binaryEncodedCode i).code
      (QuditSubsystem.fullRegion (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2)) := by
  have hK : 0 < f256MultiplicationLogicalCount i := by
    have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
    unfold f256MultiplicationLogicalCount
    omega
  let a : Qubit.Bitstring (Fin (f256MultiplicationLogicalCount i)) := fun _ => 0
  let b : Qubit.Bitstring (Fin (f256MultiplicationLogicalCount i)) := fun _ => 1
  let B := EuclideanSpace.basisFun (Qubit.Bitstring (Fin (f256MultiplicationLogicalCount i))) Complex
  have hab : a ≠ b := by
    intro heq
    have ht := congrFun heq ⟨0, hK⟩
    change (0 : Fin 2) = 1 at ht
    exact (by decide : (0 : Fin 2) ≠ 1) ht
  apply QuditSubsystem.not_noInformationOn_fullRegion
    (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2)
    (binaryEncodedCode i).code (by intro _; exact Nat.zero_lt_two)
    (binaryEncodingIsometry i (B a)) (binaryEncodingIsometry i (B b))
    ⟨B a, rfl⟩ ⟨B b, rfl⟩
  · rw [(binaryEncodingIsometry i).inner_map_map]
    simpa using (orthonormal_iff_ite.mp B.orthonormal) a a
  · rw [(binaryEncodingIsometry i).inner_map_map]
    simpa using (orthonormal_iff_ite.mp B.orthonormal) b b
  · rw [(binaryEncodingIsometry i).inner_map_map]
    exact B.orthonormal.inner_eq_zero hab

theorem binaryDistance_detects (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (binaryDistance i) :=
  QuditSubsystem.finiteMeasurementDistance_detects _ _

theorem binaryDistance_fails_succ (i : Nat) :
    ¬ QuditSubsystem.BPTMeasurementDistance (binaryEncodedCode i).code (binaryDistance i + 1) :=
  QuditSubsystem.finiteMeasurementDistance_fails_succ _ _
    (binaryEncodedCode_not_full_noInformation i)

theorem binaryDistance_source_integer_lower (i : Nat) :
    f256QuditDistanceBound i ≤ binaryDistance i :=
  QuditSubsystem.le_finiteMeasurementDistance _ _ (binaryEncodedCode_not_full_noInformation i)
    (binaryEncodedCode_measurementDistance i)

theorem binaryDistance_le_length (i : Nat) : binaryDistance i ≤ binaryLength i := by
  rw [binaryLength_eq_card]
  exact QuditSubsystem.finiteMeasurementDistance_le_card _ _
    (binaryEncodedCode_not_full_noInformation i)

theorem binaryDistance_source_lower (i : Nat) :
    (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤
      binaryDistance i := by
  have h : (f256QuditDistanceBound i : ℚ) ≤ binaryDistance i := by
    exact_mod_cast binaryDistance_source_integer_lower i
  exact (f256QuditDistanceBound_source_lower i).trans h

theorem binaryLength_tendsto_atTop : Tendsto binaryLength atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 f256QuditLength_tendsto_atTop) b] with i hi
  unfold binaryLength
  omega

theorem binaryLogicalCount_bounds (i : Nat) :
    (binaryLength i : ℚ) / 10240 ≤ f256MultiplicationLogicalCount i ∧
      (f256MultiplicationLogicalCount i : ℚ) ≤ binaryLength i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  have hnat : binaryLength i ≤ 10240 * f256MultiplicationLogicalCount i ∧
      f256MultiplicationLogicalCount i ≤ binaryLength i := by
    unfold binaryLength f256QuditLength f256MultiplicationLogicalCount
    omega
  have hlow : (binaryLength i : ℚ) ≤ 10240 * f256MultiplicationLogicalCount i := by
    exact_mod_cast hnat.1
  refine ⟨by linarith, ?_⟩
  exact_mod_cast hnat.2

theorem binaryDistance_bounds (i : Nat) :
    (binaryLength i : ℚ) / 5120 ≤ binaryDistance i ∧
      (binaryDistance i : ℚ) ≤ binaryLength i := by
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  have hnat : binaryLength i ≤ 5120 * f256QuditDistanceBound i := by
    unfold binaryLength f256QuditLength f256QuditDistanceBound f256MultiplicationLogicalCount
    omega
  have hd := binaryDistance_source_integer_lower i
  have hlow : (binaryLength i : ℚ) ≤ 5120 * binaryDistance i := by
    exact_mod_cast hnat.trans (Nat.mul_le_mul_left 5120 hd)
  refine ⟨by linarith, ?_⟩
  exact_mod_cast binaryDistance_le_length i

end QEC.Distillation.Ngu24Binary
