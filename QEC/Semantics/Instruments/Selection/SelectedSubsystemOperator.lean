import QEC.Semantics.Instruments.Selection.SelectedSubsystem
import QEC.Semantics.ErrorCorrection.QuditSubsystem
/-!
# Matrix-unit action of tensor-power selected-subsystem channels

The actual tensor-power selector is a composition of three concrete physical
maps: flatten the recursive carrier, partially trace the selector complement,
and reindex the retained coordinates.  This module records that composition
on computational rank-one matrix units.
-/

universe u v

namespace QEC
namespace Semantics

open Classical
open scoped TensorProduct

noncomputable section

namespace FiniteInstrument

/-- The retained output bitstring obtained by flattening a tensor-power basis
history, restricting it to the actual selected coordinate image, and applying
the requested-slot reindexing. -/
noncomputable def tensorPowerSelectedOutputBitstring
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    Qubit.Bitstring (Fin required × ι) :=
  tensorPowerSelectedBitstringEquiv accepts attempts observedHistory required
    hrequired ι
      ((tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).splitBitstring
          (tensorPowerQubitBitstringEquiv ι attempts basisHistory)).1

/-- The complementary bitstring discarded by the actual selected-subsystem
partial trace. -/
noncomputable def tensorPowerSelectedComplementBitstring
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).ComplementCoordinates :=
  ((tensorPowerSelectedSubsystem accepts attempts observedHistory required
      hrequired ι).splitBitstring
        (tensorPowerQubitBitstringEquiv ι attempts basisHistory)).2

/-- The recursive input basis history is exactly equivalent to its retained
requested-slot bitstring together with the complementary bitstring discarded
by the physical selector channel. -/
noncomputable def tensorPowerSelectedHistoryBitstringEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    tensorPowerHistory (Qubit.Bitstring ι) attempts ≃
      Qubit.Bitstring (Fin required × ι) ×
        Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates :=
  (tensorPowerQubitBitstringEquiv ι attempts).trans
    ((tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).bitstringFactorization.trans
      (Equiv.prodCongr
        (tensorPowerSelectedBitstringEquiv accepts attempts observedHistory required
          hrequired ι)
        (Equiv.refl _)))

/-- The retained component of the full selected/complement history equivalence
is the previously exposed requested-slot bitstring. -/
@[simp] theorem tensorPowerSelectedHistoryBitstringEquiv_apply_fst
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    (tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι basisHistory).1 =
        tensorPowerSelectedOutputBitstring accepts attempts observedHistory required
          hrequired ι basisHistory := by
  rfl

/-- The discarded component of the full selected/complement history
equivalence is the previously exposed complement bitstring. -/
@[simp] theorem tensorPowerSelectedHistoryBitstringEquiv_apply_snd
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (basisHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    (tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι basisHistory).2 =
        tensorPowerSelectedComplementBitstring accepts attempts observedHistory required
          hrequired ι basisHistory := by
  rfl

/-- Rebuilding an input history from a selected/complement pair recovers its
selected requested-slot label exactly. -/
@[simp] theorem tensorPowerSelectedOutputBitstring_equiv_symm
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).ComplementCoordinates) :
    tensorPowerSelectedOutputBitstring accepts attempts observedHistory required
        hrequired ι
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
          required hrequired ι).symm (selected, complement)) = selected := by
  rw [← tensorPowerSelectedHistoryBitstringEquiv_apply_fst]
  simp

/-- Rebuilding an input history from a selected/complement pair recovers its
discarded complement label exactly. -/
@[simp] theorem tensorPowerSelectedComplementBitstring_equiv_symm
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Qubit.Bitstring (Fin required × ι))
    (complement : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts observedHistory required
        hrequired ι).ComplementCoordinates) :
    tensorPowerSelectedComplementBitstring accepts attempts observedHistory required
        hrequired ι
        ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
          required hrequired ι).symm (selected, complement)) = complement := by
  rw [← tensorPowerSelectedHistoryBitstringEquiv_apply_snd]
  simp

/-- On a computational matrix unit, the actual selected-subsystem channel
retains the reindexed selected matrix unit and multiplies it by the exact
inner product of the discarded complementary basis vectors. -/
theorem tensorPowerSelectedPartialTraceChannel_rankOne_basis
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (left right : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
        required hrequired ι
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
            attempts left)
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
            attempts right)).toLinearMap =
      (inner Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory
                required hrequired ι).ComplementCoordinates)
            Complex
            (tensorPowerSelectedComplementBitstring accepts attempts
              observedHistory required hrequired ι right))
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory
                required hrequired ι).ComplementCoordinates)
            Complex
            (tensorPowerSelectedComplementBitstring accepts attempts
              observedHistory required hrequired ι left))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι left))
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι right))).toLinearMap := by
  simp only [tensorPowerSelectedPartialTraceChannel,
    QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    tensorPowerQubitRegisterTransport_apply_basis,
    tensorPowerQubitRegisterTransport_apply_basis]
  simp only [FiniteSubsystem.selectedPartialTraceFromRegister,
    FiniteSubsystem.selectedPartialTrace, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    FiniteSubsystem.registerFactorization_apply_basis,
    FiniteSubsystem.registerFactorization_apply_basis]
  change
    (tensorPowerSelectedRegisterReindex accepts attempts observedHistory required
      hrequired ι).conjOperator
      (partialTraceRightRaw
        (tensorPowerSelectedSubsystem accepts attempts observedHistory required
          hrequired ι).selectedSystem
        (tensorPowerSelectedSubsystem accepts attempts observedHistory required
          hrequired ι).complementSystem
        (InnerProductSpace.rankOne Complex
          (_ ⊗ₜ[Complex] _) (_ ⊗ₜ[Complex] _)).toLinearMap) = _
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  change
    (tensorPowerSelectedRegisterReindex accepts attempts observedHistory required
      hrequired ι).conjOperatorLinearMap (_ • _) = _
  rw [map_smul, UnitaryTransport.conjOperatorLinearMap_apply,
    QuditSubsystem.conjOperator_rankOne,
    tensorPowerSelectedRegisterReindex_apply_basis,
    tensorPowerSelectedRegisterReindex_apply_basis]
  rfl

/-- Expand the actual selected-subsystem output in requested-slot matrix
units.  The only surviving coherence factor is the exact inner product of the
discarded complementary computational basis vectors. -/
theorem tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)) :
    tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
        required hrequired ι A =
      ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
        ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          (inner Complex
              (tensorPowerBasis
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
                attempts left)
              (A
                (tensorPowerBasis
                  (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
                  attempts right)) *
            inner Complex
              (EuclideanSpace.basisFun
                (Qubit.Bitstring
                  (tensorPowerSelectedSubsystem accepts attempts observedHistory
                    required hrequired ι).ComplementCoordinates)
                Complex
                (tensorPowerSelectedComplementBitstring accepts attempts
                  observedHistory required hrequired ι right))
              (EuclideanSpace.basisFun
                (Qubit.Bitstring
                  (tensorPowerSelectedSubsystem accepts attempts observedHistory
                    required hrequired ι).ComplementCoordinates)
                Complex
                (tensorPowerSelectedComplementBitstring accepts attempts
                  observedHistory required hrequired ι left))) •
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
                (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
                  required hrequired ι left))
              (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
                (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
                  required hrequired ι right))).toLinearMap := by
  let inputBasis :=
    tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
  have hExpand :
      A = ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
        ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          inner Complex (inputBasis left) (A (inputBasis right)) •
            (InnerProductSpace.rankOne Complex
              (inputBasis left) (inputBasis right)).toLinearMap := by
    calc
      A = ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          (InnerProductSpace.rankOne Complex
            (A (inputBasis right)) (inputBasis right)).toLinearMap :=
        QuditSubsystem.operator_eq_sum_rankOne_basis _ inputBasis A
      _ = ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
            inner Complex (inputBasis left) (A (inputBasis right)) •
              (InnerProductSpace.rankOne Complex
                (inputBasis left) (inputBasis right)).toLinearMap := by
        apply Finset.sum_congr rfl
        intro right _
        ext vector
        simp only [LinearMap.sum_apply, LinearMap.smul_apply]
        change
          inner Complex (inputBasis right) vector • A (inputBasis right) =
            ∑ left,
              inner Complex (inputBasis left) (A (inputBasis right)) •
                (inner Complex (inputBasis right) vector • inputBasis left)
        calc
          inner Complex (inputBasis right) vector • A (inputBasis right) =
              inner Complex (inputBasis right) vector •
                ∑ left,
                  inner Complex (inputBasis left) (A (inputBasis right)) •
                    inputBasis left := by
            rw [inputBasis.sum_repr']
          _ = ∑ left,
              inner Complex (inputBasis left) (A (inputBasis right)) •
                (inner Complex (inputBasis right) vector • inputBasis left) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro left _
            simp [smul_smul, mul_comm]
  conv_lhs => rw [hExpand]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro right _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro left _
  rw [map_smul,
    tensorPowerSelectedPartialTraceChannel_rankOne_basis]
  simp only [smul_smul]
  rfl

/-- A requested-slot matrix entry of the selected output is the sum of input
matrix entries with the same literal discarded-complement label. -/
theorem tensorPowerSelectedPartialTraceChannel_matrixEntry
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι A
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        inner Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
              required hrequired ι).symm (left, complement)))
          (A
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
              ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
                required hrequired ι).symm (right, complement)))) := by
  rw [tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion]
  simp only [LinearMap.sum_apply]
  rw [inner_sum]
  simp_rw [inner_sum]
  have hRankOne (outputLeft outputRight : Qubit.Bitstring (Fin required × ι)) :
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
          outputLeft)
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
          outputRight)).toLinearMap
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            right) =
        inner Complex
            (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
              outputRight)
            (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
              right) •
          EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            outputLeft := by
    rfl
  simp only [LinearMap.smul_apply, inner_smul_right]
  simp_rw [hRankOne]
  simp only [inner_smul_right]
  let inputBasis :=
    tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
  let outputBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
  let complementBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts observedHistory required
          hrequired ι).ComplementCoordinates)
      Complex
  let splitEquiv :=
    tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι
  let entryTerm := fun
      (rightHistory leftHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) =>
    inner Complex (inputBasis leftHistory) (A (inputBasis rightHistory)) *
      inner Complex
        (complementBasis
          (tensorPowerSelectedComplementBitstring accepts attempts observedHistory
            required hrequired ι rightHistory))
        (complementBasis
          (tensorPowerSelectedComplementBitstring accepts attempts observedHistory
            required hrequired ι leftHistory)) *
      (inner Complex
          (outputBasis
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι rightHistory))
          (outputBasis right) *
        inner Complex (outputBasis left)
          (outputBasis
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι leftHistory)))
  change
    (∑ rightHistory, ∑ leftHistory, entryTerm rightHistory leftHistory) =
      ∑ complement,
        inner Complex (inputBasis (splitEquiv.symm (left, complement)))
          (A (inputBasis (splitEquiv.symm (right, complement))))
  have hReindex :
      (∑ rightHistory, ∑ leftHistory, entryTerm rightHistory leftHistory) =
        ∑ rightPair : Qubit.Bitstring (Fin required × ι) ×
            Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory required
                hrequired ι).ComplementCoordinates,
          ∑ leftPair : Qubit.Bitstring (Fin required × ι) ×
              Qubit.Bitstring
                (tensorPowerSelectedSubsystem accepts attempts observedHistory required
                  hrequired ι).ComplementCoordinates,
            entryTerm (splitEquiv.symm rightPair) (splitEquiv.symm leftPair) := by
    apply Fintype.sum_equiv splitEquiv
    intro rightHistory
    apply Fintype.sum_equiv splitEquiv
    intro leftHistory
    simp
  rw [hReindex]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [entryTerm, splitEquiv,
    tensorPowerSelectedOutputBitstring_equiv_symm,
    tensorPowerSelectedComplementBitstring_equiv_symm]
  simp_rw [complementBasis.inner_eq_ite, outputBasis.inner_eq_ite]
  simp

end FiniteInstrument

end
end Semantics
end QEC
