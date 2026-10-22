import QEC.Coding.Stabilizer.HermitianPauli
import QEC.Semantics.Instruments.Core
/-!
# Honest binary stabilizer measurement

A signed Hermitian binary Pauli is an involutive observable. This module
constructs its two literal spectral projectors

`P_λ = (1 / 2) • (1 + λ • S)`

and packages those projectors as a complete two-outcome Kraus family and
selective finite instrument. Every probability and conditional-state law is
then specialized from the generic finite-instrument API.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PauliSymplectic

open Semantics
open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The visible `+1` and `-1` outcomes of a stabilizer measurement. -/
inductive StabilizerOutcome
  | positive
  | negative
deriving DecidableEq

instance : Fintype StabilizerOutcome where
  elems := {.positive, .negative}
  complete outcome := by cases outcome <;> simp

namespace StabilizerOutcome

/-- The exact complex eigenvalue represented by a measurement outcome. -/
def sign : StabilizerOutcome → Complex
  | .positive => 1
  | .negative => -1

/-- The other spectral outcome. -/
def opposite : StabilizerOutcome → StabilizerOutcome
  | .positive => .negative
  | .negative => .positive

@[simp]
theorem sign_opposite (outcome : StabilizerOutcome) :
    outcome.opposite.sign = -outcome.sign := by
  cases outcome <;> norm_num [opposite, sign]

@[simp]
theorem opposite_opposite (outcome : StabilizerOutcome) :
    outcome.opposite.opposite = outcome := by
  cases outcome <;> rfl

@[simp]
theorem sign_mul_self (outcome : StabilizerOutcome) :
    outcome.sign * outcome.sign = 1 := by
  cases outcome <;> norm_num [sign]

end StabilizerOutcome

/-- The spectral projector `(I + λ S) / 2` for one signed Hermitian Pauli. -/
def stabilizerProjector (P : Binary ι) (outcome : StabilizerOutcome) :
    Operator (Qubit.QubitRegister ι) :=
  (1 / 2 : Complex) •
    (1 + outcome.sign • toHermitianQubitOperator P)

/-- Every binary stabilizer outcome projector is self-adjoint. -/
theorem stabilizerProjector_adjoint
    (P : Binary ι) (outcome : StabilizerOutcome) :
    LinearMap.adjoint (stabilizerProjector P outcome) =
      stabilizerProjector P outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold stabilizerProjector
  apply LinearMap.IsSymmetric.smul
  · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) =
      (2 : Complex)⁻¹ := by
        rw [map_inv₀]
        have htwo : starRingEnd Complex (2 : Complex) = 2 :=
          map_natCast (starRingEnd Complex) 2
        rw [htwo]
    simpa only [one_div] using hreal
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · apply LinearMap.IsSymmetric.smul
      · cases outcome <;> simp [StabilizerOutcome.sign]
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact adjoint_toHermitianQubitOperator_eq_self P

/-- Every binary stabilizer outcome projector is idempotent. -/
theorem stabilizerProjector_idempotent
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome * stabilizerProjector P outcome =
      stabilizerProjector P outcome := by
  cases outcome <;>
    simp only [stabilizerProjector, StabilizerOutcome.sign,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      toHermitianQubitOperator_square] <;>
    module

/-- Opposite spectral projectors are orthogonal in the displayed order. -/
theorem stabilizerProjector_mul_opposite
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome *
        stabilizerProjector P outcome.opposite = 0 := by
  cases outcome <;>
    simp only [stabilizerProjector, StabilizerOutcome.sign,
      StabilizerOutcome.opposite, smul_mul_assoc, mul_smul_comm,
      mul_add, add_mul, one_mul, mul_one,
      toHermitianQubitOperator_square] <;>
    module

/-- Opposite spectral projectors are orthogonal in the reverse order. -/
theorem opposite_stabilizerProjector_mul
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome.opposite *
        stabilizerProjector P outcome = 0 := by
  simpa using stabilizerProjector_mul_opposite P outcome.opposite

/-- The two opposite spectral projectors resolve the identity. -/
theorem stabilizerProjector_add_opposite
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome +
        stabilizerProjector P outcome.opposite = 1 := by
  cases outcome <;>
    simp only [stabilizerProjector, StabilizerOutcome.sign,
      StabilizerOutcome.opposite] <;>
    module

/-- Projector fixed points are exactly the corresponding signed eigenspace. -/
theorem stabilizerProjector_fixed_iff
    (P : Binary ι) (outcome : StabilizerOutcome)
    (ψ : Qubit.QubitRegister ι) :
    stabilizerProjector P outcome ψ = ψ ↔
      toHermitianQubitOperator P ψ = outcome.sign • ψ := by
  cases outcome with
  | positive =>
      constructor
      · intro h
        have htwo := congrArg (fun x => (2 : Complex) • x) h
        simp [stabilizerProjector, StabilizerOutcome.sign, smul_add,
          smul_smul] at htwo
        have heigen : toHermitianQubitOperator P ψ = ψ :=
          add_left_cancel (a := ψ) (by simpa [two_smul] using htwo)
        simpa [StabilizerOutcome.sign] using heigen
      · intro h
        simp [stabilizerProjector, StabilizerOutcome.sign, h, smul_add]
        module
  | negative =>
      constructor
      · intro h
        have htwo := congrArg (fun x => (2 : Complex) • x) h
        simp [stabilizerProjector, StabilizerOutcome.sign, smul_add,
          smul_smul] at htwo
        have hnegative :
            -(toHermitianQubitOperator P ψ) = ψ :=
          add_left_cancel (a := ψ) (by simpa [two_smul] using htwo)
        have heigen : toHermitianQubitOperator P ψ = -ψ := by
          simpa only [neg_neg] using
            congrArg (fun x : Qubit.QubitRegister ι => -x) hnegative
        simpa [StabilizerOutcome.sign] using heigen
      · intro h
        simp [stabilizerProjector, StabilizerOutcome.sign, h, smul_add]
        module

/-- A vector in one eigenspace is annihilated by the opposite projector. -/
theorem stabilizerProjector_opposite_apply_of_fixed
    (P : Binary ι) (outcome : StabilizerOutcome)
    (ψ : Qubit.QubitRegister ι)
    (hfixed : stabilizerProjector P outcome ψ = ψ) :
    stabilizerProjector P outcome.opposite ψ = 0 := by
  have heigen :=
    (stabilizerProjector_fixed_iff P outcome ψ).1 hfixed
  cases outcome <;>
    simp [stabilizerProjector, StabilizerOutcome.sign,
      StabilizerOutcome.opposite, heigen, smul_add]

/-- Changing the stored global Pauli sign visibly swaps the two outcomes. -/
theorem stabilizerProjector_binarySign_mul
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector (binaryMul (binarySign (1 : ZMod 2)) P) outcome =
      stabilizerProjector P outcome.opposite := by
  rw [stabilizerProjector, stabilizerProjector,
    toHermitianQubitOperator_binarySign_mul]
  simp only [binaryPhaseScalar_one, smul_smul]
  cases outcome <;>
    simp [StabilizerOutcome.sign, StabilizerOutcome.opposite]

/-- The two spectral projectors as a concrete same-space Kraus family. -/
def stabilizerKrausFamily (P : Binary ι) :
    FiniteKrausFamily StabilizerOutcome
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  operator := stabilizerProjector P

@[simp]
theorem stabilizerKrausFamily_operator
    (P : Binary ι) (outcome : StabilizerOutcome) :
    (stabilizerKrausFamily P).operator outcome =
      stabilizerProjector P outcome :=
  rfl

/-- Orthogonal resolution of the identity gives Kraus completeness. -/
theorem stabilizerKrausFamily_complete (P : Binary ι) :
    (stabilizerKrausFamily P).Complete := by
  classical
  unfold FiniteKrausFamily.Complete
  simp only [stabilizerKrausFamily_operator, stabilizerProjector_adjoint]
  change
    (∑ outcome : StabilizerOutcome,
      stabilizerProjector P outcome * stabilizerProjector P outcome) = 1
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide]
  simpa [stabilizerProjector_idempotent, StabilizerOutcome.opposite] using
    stabilizerProjector_add_opposite P .positive

/-- The complete binary stabilizer measurement with visible outcome labels. -/
def stabilizerInstrument (P : Binary ι) :
    FiniteInstrument StabilizerOutcome StabilizerOutcome
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  kraus := stabilizerKrausFamily P
  observe := fun outcome => outcome

@[simp]
theorem stabilizerInstrument_kraus (P : Binary ι) :
    (stabilizerInstrument P).kraus = stabilizerKrausFamily P :=
  rfl

@[simp]
theorem stabilizerInstrument_observe
    (P : Binary ι) (outcome : StabilizerOutcome) :
    (stabilizerInstrument P).observe outcome = outcome :=
  rfl

/-- A selective branch is literal nondestructive compression `P_λ ρ P_λ`. -/
theorem stabilizerInstrument_branchOperator
    (P : Binary ι) (outcome : StabilizerOutcome)
    (A : Operator (Qubit.QubitRegister ι)) :
    (stabilizerInstrument P).branchOperator outcome A =
      stabilizerProjector P outcome * A *
        stabilizerProjector P outcome := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  simp only [stabilizerInstrument_observe, stabilizerInstrument_kraus,
    stabilizerKrausFamily_operator, stabilizerProjector_adjoint]
  simp only [eq_comm]
  simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Binary stabilizer Born weights are nonnegative. -/
theorem stabilizerBornWeight_nonneg
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    0 ≤ (stabilizerInstrument P).bornWeight outcome rho :=
  (stabilizerInstrument P).bornWeight_nonneg outcome rho

/-- The two binary stabilizer Born weights sum to one. -/
theorem sum_stabilizerBornWeight_eq_one
    (P : Binary ι)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    ∑ outcome : StabilizerOutcome,
        (stabilizerInstrument P).bornWeight outcome rho = 1 :=
  (stabilizerInstrument P).sum_bornWeight_eq_one
    (stabilizerKrausFamily_complete P) rho

/-- A zero stabilizer Born weight leaves an explicit zero raw branch. -/
theorem stabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hzero : (stabilizerInstrument P).bornWeight outcome rho = 0) :
    (stabilizerInstrument P).branchOperator outcome rho.toOperator = 0 :=
  (stabilizerInstrument P).branchOperator_eq_zero_of_bornWeight_eq_zero
    outcome rho hzero

/-- The normalized state of a strictly positive stabilizer branch. -/
def stabilizerConditionalDensity
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (stabilizerInstrument P).bornWeight outcome rho) :
    DensityOperator (Qubit.QubitRegister ι) :=
  (stabilizerInstrument P).conditionalDensity outcome rho hpos

@[simp]
theorem stabilizerConditionalDensity_toOperator
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (stabilizerInstrument P).bornWeight outcome rho) :
    (stabilizerConditionalDensity P outcome rho hpos).toOperator =
      (((stabilizerInstrument P).bornWeight outcome rho : Complex)⁻¹) •
        (stabilizerProjector P outcome * rho.toOperator *
          stabilizerProjector P outcome) := by
  rw [stabilizerConditionalDensity,
    FiniteInstrument.conditionalDensity_toOperator,
    stabilizerInstrument_branchOperator]

/--
Positive-mass conditional branches reconstruct the unconditioned complete
stabilizer channel; zero-mass outcomes are omitted only through the generic
proved zero-branch law.
-/
theorem sum_positive_stabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
    (P : Binary ι)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    (∑ outcome : {outcome : StabilizerOutcome //
        0 < (stabilizerInstrument P).bornWeight outcome rho},
      ((stabilizerInstrument P).bornWeight outcome.1 rho : Complex) •
        (stabilizerConditionalDensity P outcome.1 rho outcome.2).toOperator) =
      (((stabilizerKrausFamily P).toQuantumChannel
        (stabilizerKrausFamily_complete P)).mapDensity rho).toOperator := by
  simpa [stabilizerConditionalDensity] using
    FiniteInstrument.sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
      (stabilizerInstrument P) (stabilizerKrausFamily_complete P) rho

end PauliSymplectic
end Coding
end QEC
