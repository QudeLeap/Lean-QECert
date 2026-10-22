import QEC.Coding.AlgebraicGeometry.Codes.NormalClosureInterpolation
import QEC.Distillation.MultiplicativeQuditProtocol.NormalClosureInput
import QEC.Distillation.MultiplicativeQuditProtocol.CosetDetectability
import QEC.Semantics.ErrorCorrection.FiniteAlphabetLocality
import QEC.Semantics.ErrorCorrection.QuditNoInformation

/-!
# Semantic local-error detection for the concrete normal-closure family

The actual punctured AG distance separates complementary coset labels.
Riemann--Roch on the shortened divisor supplies local kernel surjectivity.
These two proved facts establish detectability for arbitrary tensor-local
operators on fewer than `ceil(n/5)-K` retained qudits.
-/

noncomputable section

namespace QEC.Distillation.Ngu24MultiplicativeCSS

open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- The concrete shortened kernel can prescribe arbitrary values in a small region. -/
theorem f256SourceInput_kernel_restrict_surjective (i : ℕ)
    (S : Finset (f256SourceInput i).PivotComplement)
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    Function.Surjective (fun h : (f256SourceInput i).H0 =>
      fun j : S => (f256SourceInput i).puncture h.val.val j.val) := by
  intro values
  obtain ⟨x, hx⟩ := f256ShortenedMultiplicationCode_restrict_surjective i S hS values
  have hmem : x.val ∈ (f256SourceInput i).shortenedCode := by
    rw [f256SourceInput_shortenedCode_eq]
    exact x.property
  obtain ⟨h, hh, hword⟩ := hmem
  refine ⟨⟨h, hh⟩, ?_⟩
  change (fun j : S => (f256SourceInput i).puncture h.val j.val) = values
  rw [show (f256SourceInput i).puncture h.val = x.val from hword]
  exact hx

/-- Every physical coset summand lies in the actual punctured evaluation code. -/
theorem f256SourceInput_cosetLabel_mem_punctured (i : ℕ)
    (u : Fin (f256MultiplicationLogicalCount i) → F256) (h : (f256SourceInput i).H0) :
    (f256SourceInput i).shortenedCosetLabel u h ∈
      (f256PuncturedMultiplicationCode i).carrier := by
  rw [← f256SourceInput_puncturedCode_eq]
  exact ⟨(f256SourceInput i).systematicLogicalWord u + h.val.val,
    (f256SourceInput i).code.carrier.add_mem
      ((f256SourceInput i).systematicLogicalWord_mem_code u) h.val.property, rfl⟩

/-- Small-region erasure cannot identify two different physical coset summands. -/
theorem f256SourceInput_complement_separates (i : ℕ)
    (S : Finset (f256SourceInput i).PivotComplement)
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i)
    (u v : Fin (f256MultiplicationLogicalCount i) → F256)
    (h k : (f256SourceInput i).H0)
    (hsame : ∀ j, j ∉ S → (f256SourceInput i).shortenedCosetLabel u h j =
      (f256SourceInput i).shortenedCosetLabel v k j) :
    u = v ∧ h = k := by
  classical
  let x : Word F256 (F256MultiplicationRetained i) :=
    (f256SourceInput i).shortenedCosetLabel u h -
    (f256SourceInput i).shortenedCosetLabel v k
  have hx : x ∈ (f256PuncturedMultiplicationCode i).carrier :=
    (f256PuncturedMultiplicationCode i).carrier.sub_mem
      (f256SourceInput_cosetLabel_mem_punctured i u h)
      (f256SourceInput_cosetLabel_mem_punctured i v k)
  have hw : HammingWeight x ≤ S.card := by
    apply Finset.card_le_card
    intro j hj
    have hjx : x j ≠ 0 := (Finset.mem_filter.mp hj).2
    by_contra hjS
    exact hjx (sub_eq_zero.mpr (hsame j hjS))
  have hxzero : x = 0 := by
    by_contra hxzero
    have hd := (f256PuncturedMultiplicationCode_distance_lower i).trans
      (HypergraphProduct.finitePredicateMinimum_le_of (weight := HammingWeight)
        ⟨hx, hxzero⟩)
    have hd' : (f256GarciaStichtenothLength i + 3) / 4 -
        f256MultiplicationLogicalCount i ≤ HammingWeight x := WithTop.coe_le_coe.mp hd
    omega
  have hlabel := sub_eq_zero.mp hxzero
  have huv := (f256SourceInput i).shortenedCosetLabel_eq_implies_logical_eq u v h k hlabel
  refine ⟨huv, ?_⟩
  subst v
  exact (f256SourceInput i).shortenedCosetLabel_injective u hlabel

local instance {J : Type} [Fintype J] : Fintype (Word F256 J) := Fintype.ofFinite _

/-- Every actual tensor-local operator on fewer than `ceil(n/5)-K` qudits
is detectable on the concrete quantum code's full carrier. -/
theorem f256SourceInput_detectable_localOperator (i : ℕ)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement => Fintype.card F256))
    (hS : S.selected.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i)
    (E : Operator S.selectedSystem) :
    DetectableOn (f256SourceInput i).quantumCode (FiniteAlphabet.localOperator S E) := by
  apply (f256SourceInput i).detectableOn_of_coset_locality
    (FiniteAlphabet.localOperator S E) S.selected
    (f256SourceInput_complement_separates i S.selected hS)
    (f256SourceInput_kernel_restrict_surjective i S.selected hS)
  · intro x y hxy
    exact FiniteAlphabet.localOperator_basis_inner_eq_zero S E x y hxy
  · intro x y hxy
    exact FiniteAlphabet.localOperator_basis_diagonal_eq S E x y hxy

/-- The concrete family satisfies the standard finite-qudit measurement-distance
predicate after the explicit coordinatewise computational-basis relabelling. -/
theorem f256SourceInput_measurementDistance (i : ℕ) :
    QuditSubsystem.BPTMeasurementDistance
      ((f256SourceInput i).quantumCode.transport
        (FiniteAlphabet.registerUnitary F256 (f256SourceInput i).PivotComplement))
      ((f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i) := by
  intro S hS E _hE
  apply (QuditSubsystem.scalarCompression_iff_detectableOn _ _).mpr
  apply FiniteAlphabet.detectableOn_transport_of_localOperator
  apply f256SourceInput_detectable_localOperator i S
  simpa only [QuditSubsystem.SelectedCoordinates, Fintype.card_coe] using hS

end QEC.Distillation.Ngu24MultiplicativeCSS
