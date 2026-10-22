import QEC.Semantics.Instruments.TensorPower.BranchOperator
import QEC.Semantics.Channels.Instrument
/-!
# Tensor-power channels on product densities

A homogeneous tensor power of one complete channel maps a genuine recursive
product input to the recursive product of the one-factor channel output.  The
identity is derived from the chosen finite Kraus representation and the
existing tensor branch factorization; it is not an independence assumption on
an arbitrary input density.
-/

universe u v

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

open scoped TensorProduct

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]

/-- A recursive history with one possible visible outcome is the canonical
constant history. -/
theorem tensorPowerHistory_punit_eq :
    ∀ (attempts : Nat) (history : tensorPowerHistory PUnit attempts),
      history = tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit) := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      exact PUnit.ext _ _
  | succ attempts ih =>
      rintro ⟨head, tail⟩
      cases head
      change (PUnit.unit, tail) =
        (PUnit.unit, tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit))
      rw [ih tail]

/-- If the sole visible outcome of every factor is `PUnit`, its recursive
branch product is exactly the recursive product of the complete one-factor
channel output. -/
theorem tensorPowerBranchOperatorProduct_punit_eq_productInput
    {κ : Type v} [Fintype κ]
    (I : FiniteInstrument κ PUnit H K) (hI : I.kraus.Complete)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator) :
    ∀ attempts : Nat,
      tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts
          (tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit)) =
        (tensorPowerProductInput
          ((I.kraus.toQuantumChannel hI).mapDensity rho)
          sigmaUnit attempts).toOperator := by
  intro attempts
  induction attempts with
  | zero =>
      simp [tensorPowerBranchOperatorProduct, tensorPowerProductInput, hunit]
  | succ attempts ih =>
      simp only [tensorPowerHistoryOf, tensorPowerBranchOperatorProduct,
        tensorPowerProductInput, DensityOperator.tensorDensity_toOperator]
      rw [ih]
      congr 1
      rw [← I.sum_branchOperator_eq_mapDensity_toOperator hI rho,
        Fintype.sum_unique]

/-- The actual channel obtained from a homogeneous tensor power maps a
recursive product density factorwise. -/
theorem quantumChannelTensorPower_mapDensity_productInput
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    ((((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
          ((channel.toFiniteInstrument).tensorPower_complete
            channel.toFiniteInstrument_complete attempts)).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts)).toOperator =
      (tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts).toOperator := by
  let I := channel.toFiniteInstrument
  let history : tensorPowerHistory PUnit attempts :=
    tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit)
  have hbranch :
      (I.tensorPower attempts).branchOperator history
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
        tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history :=
    branchOperator_tensorPower_productInput I rho rhoUnit attempts history
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteKrausFamily.toQuantumChannel_apply,
    ← (I.tensorPower attempts).sum_branchOperator_eq_inducedMap]
  rw [Fintype.sum_eq_single history]
  · rw [hbranch]
    have hproduct := tensorPowerBranchOperatorProduct_punit_eq_productInput I
      channel.toFiniteInstrument_complete rho rhoUnit sigmaUnit hunit attempts
    have hmap :
        (I.kraus.toQuantumChannel channel.toFiniteInstrument_complete).mapDensity rho =
          channel.mapDensity rho := by
      apply DensityOperator.ext_toOperator
      exact LinearMap.congr_fun channel.toFiniteInstrument_inducedMap_eq rho.toOperator
    rw [tensorPowerHistory_punit_eq attempts history]
    rw [hmap] at hproduct
    exact hproduct
  · intro other hne
    exact False.elim (hne (tensorPowerHistory_punit_eq attempts other))

/-- Density-operator form of
`quantumChannelTensorPower_mapDensity_productInput`. -/
theorem quantumChannelTensorPower_mapDensity_productInput_eq
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    (((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
          ((channel.toFiniteInstrument).tensorPower_complete
            channel.toFiniteInstrument_complete attempts)).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts) =
      tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts := by
  apply DensityOperator.ext_toOperator
  exact quantumChannelTensorPower_mapDensity_productInput
    channel rho rhoUnit sigmaUnit hunit attempts

end FiniteInstrument

end
end Semantics
end QEC
