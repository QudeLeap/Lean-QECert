import QEC.Coding.QuditQubitConversion.ResourceCircuit
import QEC.Distillation.Core.FiniteDecodedTrace
import QEC.Distillation.Core.FiniteInstrumentBinaryRun
import QEC.Distillation.PrimeQuditProtocol.MagicResource
import QEC.Distillation.Core.MagicStateProtocol
import QEC.Distillation.Universality.OneQubitClifford
import QEC.Distillation.Core.Overhead
import QEC.Distillation.ConstantOverheadProtocol.AlgebraicGeometryFamily
import QEC.Semantics.Entropy.Convexity
import QEC.Semantics.Instruments.Sequential.Composition
import QEC.Semantics.Instruments.Registers.ProductDensity
import QEC.Semantics.Instruments.Registers.Marginal
import QEC.Semantics.ErrorCorrection.QuditSubsystem
import QEC.Semantics.Channels.Instrument
/-!
# WHY24 one-round local-stochastic distillation

This module implements the finite physical layer in WHY24, `main.tex:903-1478`.
It keeps the correlated preparation as a joint register density, derives the
CCZ-basis stochastic-error law by an actual finite twirl, constructs the AG
decoder used by the proved F1024 code family, and assembles the deterministic
active-correction round.  Threshold and asymptotic constant-overhead arguments
remain in the terminal child.
-/

noncomputable section

namespace QEC.Distillation.Why24OneRoundProtocol

open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder

attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype

local instance instWhy24OneRoundClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Exact finite correlated preparation model -/

/-- The `C n = 70 n` physical CCZ preparation locations in one WHY24 round. -/
abbrev Why24CCZFaultLocation (r : Nat) : Type :=
  Fin (70 * f1024Why24OddLength r)

/-- Three physical qubits for every prepared CCZ resource. -/
abbrev Why24CCZPhysicalQubit (Location : Type) : Type := Location × Fin 3

/-- The flattened joint qubit register on which correlated faults act. -/
abbrev Why24CCZRegister (Location : Type) [Fintype Location] : Type :=
  Qubit.QubitRegister (Why24CCZPhysicalQubit Location)

/-- The qubit subsystem consisting of all three qubits at the faulty CCZ
locations.  A Kraus operator supported here may correlate all faulty
locations, but is the identity on every nonfaulty location. -/
def why24FaultSubsystem {Location : Type} [Fintype Location]
    [DecidableEq Location] (fault : Finset Location) :
    QuditSubsystem (fun _ : Why24CCZPhysicalQubit Location => 2) where
  selected := fault.product Finset.univ

@[simp]
theorem why24FaultSubsystem_selected {Location : Type} [Fintype Location]
    [DecidableEq Location] (fault : Finset Location) :
    (why24FaultSubsystem fault).selected = fault.product Finset.univ :=
  rfl

/-- One arbitrary correlated CPTP fault operation, represented by its actual
finite Kraus family.  Every Kraus branch is supported on the displayed fault
set; there is no product or IID requirement within that set. -/
structure Why24CCZFaultOperation (Location : Type) [Fintype Location]
    [DecidableEq Location] (fault : Finset Location) where
  krausCount : Nat
  kraus : FiniteKrausFamily (Fin krausCount)
    (Why24CCZRegister Location) (Why24CCZRegister Location)
  complete : kraus.Complete
  supported : forall index,
    (why24FaultSubsystem fault).OperatorSupportedOnRegister
      (kraus.operator index)

namespace Why24CCZFaultOperation

variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {fault : Finset Location}

/-- The actual CPTP map induced by a supported correlated Kraus family. -/
noncomputable def channel
    (operation : Why24CCZFaultOperation Location fault) :
    QuantumChannel (Why24CCZRegister Location) (Why24CCZRegister Location) :=
  operation.kraus.toQuantumChannel operation.complete

@[simp]
theorem channel_apply
    (operation : Why24CCZFaultOperation Location fault)
    (A : Operator (Why24CCZRegister Location)) :
    operation.channel A = operation.kraus.inducedMap A :=
  rfl

end Why24CCZFaultOperation

/-- A finite local-stochastic preparation law.  It samples a fault set, then
runs an arbitrary correlated CPTP operation supported on precisely those
locations.  The tail inequality is required for every subset and uses the
individual site rates before passing to the uniform physical rate. -/
structure Why24LocalStochasticPreparation (Location : Type)
    [Fintype Location] [DecidableEq Location]
    (ideal : DensityOperator (Why24CCZRegister Location)) where
  faultMass : Finset Location -> Real
  faultMass_nonneg : forall fault, 0 <= faultMass fault
  faultMass_sum : (∑ fault : Finset Location, faultMass fault) = 1
  siteRate : Location -> Real
  siteRate_nonneg : forall location, 0 <= siteRate location
  siteRate_le_one : forall location, siteRate location <= 1
  rate : Real
  rate_nonneg : 0 <= rate
  rate_le_one : rate <= 1
  siteRate_le_rate : forall location, siteRate location <= rate
  faultOperation : (fault : Finset Location) ->
    Why24CCZFaultOperation Location fault
  tail_bound : forall sites : Finset Location,
    (∑ fault : Finset Location,
      if sites ⊆ fault then faultMass fault else 0) <=
        ∏ location ∈ sites, siteRate location

namespace Why24LocalStochasticPreparation

variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {ideal : DensityOperator (Why24CCZRegister Location)}

/-- The branch density after the supported correlated fault map. -/
noncomputable def branchDensity
    (preparation : Why24LocalStochasticPreparation Location ideal)
    (fault : Finset Location) : DensityOperator (Why24CCZRegister Location) :=
  (preparation.faultOperation fault).channel.mapDensity ideal

/-- The literal convex mixture over random fault sets and supported CPTP maps. -/
noncomputable def why24LocalStochasticPreparedDensity
    (preparation : Why24LocalStochasticPreparation Location ideal) :
    DensityOperator (Why24CCZRegister Location) :=
  DensityOperator.convexCombination Finset.univ preparation.faultMass
    preparation.branchDensity
    (by intro fault _; exact preparation.faultMass_nonneg fault)
    (by simpa using preparation.faultMass_sum)

@[simp]
theorem why24LocalStochasticPreparedDensity_toOperator
    (preparation : Why24LocalStochasticPreparation Location ideal) :
    preparation.why24LocalStochasticPreparedDensity.toOperator =
      ∑ fault : Finset Location,
        (preparation.faultMass fault : Complex) •
          (preparation.branchDensity fault).toOperator := by
  simp [why24LocalStochasticPreparedDensity,
    DensityOperator.convexCombinationOperator]

private theorem siteRate_product_le_rate_pow
    (preparation : Why24LocalStochasticPreparation Location ideal)
    (sites : Finset Location) :
    (∏ location ∈ sites, preparation.siteRate location) <=
      preparation.rate ^ sites.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod
    (fun location _ => preparation.siteRate_nonneg location)
    (fun location _ => preparation.siteRate_le_rate location)

/-- The per-location tail law implies the usual uniform local-stochastic
bound at the physical rate, without replacing the correlated preparation by
an IID distribution. -/
theorem why24LocalStochastic_tail_maxRate
    (preparation : Why24LocalStochasticPreparation Location ideal)
    (sites : Finset Location) :
    (∑ fault : Finset Location,
      if sites ⊆ fault then preparation.faultMass fault else 0) <=
        preparation.rate ^ sites.card :=
  (preparation.tail_bound sites).trans
    (preparation.siteRate_product_le_rate_pow sites)

end Why24LocalStochasticPreparation

/-! ## Exact adaptor to the shared local-stochastic input API -/

/-- The canonical density on the one-dimensional tensor unit used to form the
literal finite product of ideal CCZ resources. -/
noncomputable def why24CCZTensorUnitDensity :
    DensityOperator
      (FiniteInstrument.tensorPowerCarrier Why24CCZSpace 0) :=
  DensityOperator.pureDensity
    (FiniteInstrument.tensorPowerBasis
      (stdOrthonormalBasis Complex Why24CCZSpace) 0 PUnit.unit) (by
        erw [OrthonormalBasis.norm_eq_one]
        norm_num)

/-- The ideal joint register is the actual tensor product of `count` copies of
the concrete CCZ resource from the literal Appendix-A circuit. -/
noncomputable def why24IdealCCZRegisterDensity (count : Nat) :
    DensityOperator (Why24CCZRegister (Fin count)) :=
  FiniteInstrument.tensorPowerRegisterProductDensity (Fin 3)
    why24CCZMagicStateDensity why24CCZTensorUnitDensity count

/-- The three physical qubits belonging to one displayed CCZ preparation
location. -/
noncomputable def why24CCZSiteSubsystem (count : Nat) (site : Fin count) :
    QuditSubsystem (fun _ : Why24CCZPhysicalQubit (Fin count) => 2) :=
  why24FaultSubsystem ({site} : Finset (Fin count))

private def why24CCZSiteCoordinate (count : Nat) (site : Fin count)
    (qubit : Fin 3) : (why24CCZSiteSubsystem count site).SelectedCoordinates :=
  ⟨(site, qubit), by simp [why24CCZSiteSubsystem, why24FaultSubsystem]⟩

/-- Relabel the selected singleton CCZ block by its original three qubits. -/
private def why24CCZSiteLabelEquiv (count : Nat) (site : Fin count) :
    Qudit.Label (why24CCZSiteSubsystem count site).selectedDimensions ≃
      Qubit.Bitstring (Fin 3) where
  toFun label qubit := label (why24CCZSiteCoordinate count site qubit)
  invFun bits coordinate := bits coordinate.1.2
  left_inv label := by
    funext coordinate
    rcases coordinate with ⟨⟨location, qubit⟩, hselected⟩
    have hlocation : location = site := by
      simpa [why24CCZSiteSubsystem, why24FaultSubsystem] using
        (Finset.mem_product.mp hselected).1
    subst location
    rfl
  right_inv bits := by
    funext qubit
    rfl

/-- The selected three-qubit factor transported back to the concrete CCZ
carrier used by the shared distillation interface. -/
private noncomputable def why24CCZSiteTransport (count : Nat)
    (site : Fin count) :
    UnitaryTransport (why24CCZSiteSubsystem count site).selectedSystem
      Why24CCZSpace := by
  let sourceBasis := EuclideanSpace.basisFun
    (Qudit.Label (why24CCZSiteSubsystem count site).selectedDimensions) Complex
  let targetBasis := EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex
  let U := sourceBasis.equiv targetBasis (why24CCZSiteLabelEquiv count site)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The actual one-site marginal of the same correlated joint preparation. -/
noncomputable def why24LocalStochasticSiteMarginal {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count))
    (site : Fin count) : DensityOperator Why24CCZSpace :=
  (why24CCZSiteTransport count site).conjDensity
    ((why24CCZSiteSubsystem count site).selectedPartialTraceFromRegister.mapDensity
      preparation.why24LocalStochasticPreparedDensity)

/-- The shared resource family consists exactly of singleton marginals of the
actual correlated preparation; it is not an IID replacement for the joint
state. -/
noncomputable def why24LocalStochasticResourceInputs {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) :
    ResourceInput count Why24CCZSpace :=
  fun site => why24LocalStochasticSiteMarginal preparation site

/-- Exact adaptor from the finite correlated preparation law to the common
local-stochastic input-error interface.  Its admissibility proposition pins
the shared inputs to the real singleton marginals of this very preparation. -/
noncomputable def why24LocalStochasticInputErrorModel {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) :
    LocalStochasticInputErrorModel count Why24CCZSpace where
  rate := preparation.rate
  rate_nonneg := preparation.rate_nonneg
  rate_le_one := preparation.rate_le_one
  admissible actualRate inputs :=
    actualRate = preparation.rate ∧
      inputs = why24LocalStochasticResourceInputs preparation

/-- The actual singleton marginals are permitted by the shared constructor
with precisely the preparation's uniform local-stochastic rate. -/
theorem why24LocalStochasticInputErrorModel_permits {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) :
    InputErrorModel.Permits
      (InputErrorModel.localStochastic
        (why24LocalStochasticInputErrorModel preparation))
      (why24LocalStochasticResourceInputs preparation) :=
  ⟨rfl, rfl⟩

/-! ## Physical CCZ stabilizer twirl -/

open QEC.Distillation.OneQubitMagic

/-- The one-qubit X basis obtained from the concrete Hadamard transport. -/
private noncomputable def why24OneQubitXBasis :
    OrthonormalBasis (Fin 2) Complex Qubit.QubitSpace :=
  (EuclideanSpace.basisFun (Fin 2) Complex).map
    hadamardTransport.toLinearIsometryEquiv

/-- Flatten three actual one-qubit tensor factors into the source CCZ register. -/
private noncomputable def why24ThreeQubitTensorRegisterTransport :
    UnitaryTransport
      (FiniteInstrument.tensorPowerCarrier Qubit.QubitSpace 3)
      Why24CCZSpace := by
  let sourceBasis := FiniteInstrument.tensorPowerBasis
    (EuclideanSpace.basisFun (Fin 2) Complex) 3
  let targetBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex
  let U := sourceBasis.equiv targetBasis
    (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The three-qubit product X basis on the concrete flattened register. -/
private noncomputable def why24ThreeQubitXBasis :
    OrthonormalBasis (Qubit.Bitstring (Fin 3)) Complex Why24CCZSpace :=
  ((FiniteInstrument.tensorPowerBasis why24OneQubitXBasis 3).map
    why24ThreeQubitTensorRegisterTransport.toLinearIsometryEquiv).reindex
      (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3)

/-- The literal diagonal CCZ phase operator on the retained three qubits. -/
private noncomputable def why24CCZPhaseOperator : Operator Why24CCZSpace where
  toFun psi := WithLp.toLp 2 fun bits =>
    PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * psi bits
  map_add' left right := by
    ext bits
    simp [mul_add]
  map_smul' scalar psi := by
    ext bits
    simp [smul_eq_mul, mul_left_comm]

@[simp] private theorem why24CCZPhaseOperator_apply
    (psi : Why24CCZSpace) (bits : Qubit.Bitstring (Fin 3)) :
    why24CCZPhaseOperator psi bits =
      PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * psi bits :=
  rfl

private theorem why24BinaryPhaseScalar_mul_self (phase : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar phase *
        PauliSymplectic.binaryPhaseScalar phase = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hself : phase + phase = 0 := by
    fin_cases phase <;> decide
  rw [hself, PauliSymplectic.binaryPhaseScalar_zero]

private theorem why24CCZPhaseOperator_square :
    why24CCZPhaseOperator * why24CCZPhaseOperator = 1 := by
  ext psi bits
  simp only [Module.End.mul_apply, why24CCZPhaseOperator_apply,
    Module.End.one_apply, ← mul_assoc, why24BinaryPhaseScalar_mul_self, one_mul]

/-- The literal CCZ phase as a self-inverse linear equivalence. -/
private noncomputable def why24CCZPhaseLinearEquiv :
    Why24CCZSpace ≃ₗ[Complex] Why24CCZSpace :=
  LinearEquiv.mk why24CCZPhaseOperator why24CCZPhaseOperator
    (fun psi => by
      have h := LinearMap.congr_fun why24CCZPhaseOperator_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun why24CCZPhaseOperator_square psi
      simpa [Module.End.mul_apply] using h)

@[simp] private theorem why24CCZPhaseLinearEquiv_apply
    (psi : Why24CCZSpace) :
    why24CCZPhaseLinearEquiv psi = why24CCZPhaseOperator psi :=
  rfl

/-- The Appendix-A CCZ phase is a unitary physical transport. -/
private noncomputable def why24CCZPhaseTransport :
    UnitaryTransport Why24CCZSpace Why24CCZSpace where
  toLinearEquiv := why24CCZPhaseLinearEquiv
  map_inner := by
    intro left right
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro bits _
    simp only [why24CCZPhaseLinearEquiv_apply,
      why24CCZPhaseOperator_apply, RCLike.inner_apply, map_mul]
    have hstar :
        starRingEnd Complex
            (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits)) =
          PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) :=
      PauliSymplectic.binaryPhaseScalar_star _
    rw [hstar]
    calc
      (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * right bits) *
          (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
            star (left bits)) =
          (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
              PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits)) *
            (right bits * star (left bits)) := by ring
      _ = right bits * star (left bits) := by
        rw [why24BinaryPhaseScalar_mul_self, one_mul]

/-- The CCZ magic basis is obtained by applying the literal CCZ phase to the
three-qubit product X basis.  Its labels are exactly physical Z-error words. -/
noncomputable def why24CCZMagicBasis :
    OrthonormalBasis (Qubit.Bitstring (Fin 3)) Complex Why24CCZSpace :=
  why24ThreeQubitXBasis.map why24CCZPhaseTransport.toLinearIsometryEquiv

/-- The normalized CCZ magic-basis ket carrying one stochastic Z-error word. -/
noncomputable def why24CCZMagicBasisKet
    (error : Qubit.Bitstring (Fin 3)) : Why24CCZSpace :=
  why24CCZMagicBasis error

private theorem why24OneQubitXBasis_zero_apply (bit : Fin 2) :
    why24OneQubitXBasis 0 bit = (Real.sqrt 2 : Complex)⁻¹ := by
  change hadamardOperator
      (EuclideanSpace.basisFun (Fin 2) Complex 0) bit = _
  fin_cases bit <;> simp

private theorem why24TensorPowerOneQubitBasis_inner_eq_prod
    (leftBasis rightBasis :
      OrthonormalBasis (Fin 2) Complex Qubit.QubitSpace) :
    forall (count : Nat)
      (left right : FiniteInstrument.tensorPowerHistory (Fin 2) count),
      inner Complex
          (FiniteInstrument.tensorPowerBasis leftBasis count left)
          (FiniteInstrument.tensorPowerBasis rightBasis count right) =
        ∏ site : Fin count,
          inner Complex
            (leftBasis (FiniteInstrument.tensorPowerHistoryAt
              (Fin 2) count left site))
            (rightBasis (FiniteInstrument.tensorPowerHistoryAt
              (Fin 2) count right site)) := by
  intro count
  induction count with
  | zero =>
      intro left right
      cases left
      cases right
      rw [FiniteInstrument.tensorPowerBasis_zero_apply,
        FiniteInstrument.tensorPowerBasis_zero_apply]
      rw [inner_self_eq_norm_sq_to_K,
        (EuclideanSpace.basisFun
          (ULift (Fin 1)) Complex).norm_eq_one]
      simp
  | succ count ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [FiniteInstrument.tensorPowerBasis_succ_apply,
        FiniteInstrument.tensorPowerBasis_succ_apply,
        TensorProduct.inner_tmul, Fin.prod_univ_succ]
      simp only [FiniteInstrument.tensorPowerHistoryAt,
        Fin.cases_zero, Fin.cases_succ]
      rw [ih leftTail rightTail]

set_option maxRecDepth 4096 in
private theorem why24ThreeQubitXBasis_zero_apply
    (bits : Qubit.Bitstring (Fin 3)) :
    why24ThreeQubitXBasis 0 bits =
      ((Real.sqrt 2 : Complex)⁻¹) ^ 3 := by
  let computationalHistory :=
    (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3).symm bits
  let zeroHistory :=
    (FiniteInstrument.tensorPowerHistoryEquiv (Fin 2) 3).symm
      (0 : Qubit.Bitstring (Fin 3))
  have hinner := why24ThreeQubitTensorRegisterTransport.map_inner
    (FiniteInstrument.tensorPowerBasis
      (EuclideanSpace.basisFun (Fin 2) Complex) 3 computationalHistory)
    (FiniteInstrument.tensorPowerBasis
      why24OneQubitXBasis 3 zeroHistory)
  have hcomputational :
      why24ThreeQubitTensorRegisterTransport
          (FiniteInstrument.tensorPowerBasis
            (EuclideanSpace.basisFun (Fin 2) Complex)
            3 computationalHistory) =
        EuclideanSpace.basisFun
          (Qubit.Bitstring (Fin 3)) Complex bits := by
    dsimp [why24ThreeQubitTensorRegisterTransport]
    rw [OrthonormalBasis.equiv_apply_basis]
    exact congrArg
      (EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex)
      ((FiniteInstrument.tensorPowerHistoryEquiv
        (Fin 2) 3).apply_symm_apply bits)
  have hzero :
      why24ThreeQubitTensorRegisterTransport
          (FiniteInstrument.tensorPowerBasis
            why24OneQubitXBasis 3 zeroHistory) =
        why24ThreeQubitXBasis 0 := by
    rw [why24ThreeQubitXBasis, OrthonormalBasis.reindex_apply]
    rfl
  rw [hcomputational, hzero, EuclideanSpace.basisFun_inner] at hinner
  rw [why24TensorPowerOneQubitBasis_inner_eq_prod] at hinner
  have hcomputationalAt (site : Fin 3) :
      FiniteInstrument.tensorPowerHistoryAt
          (Fin 2) 3 computationalHistory site = bits site := by
    exact congrFun
      ((FiniteInstrument.tensorPowerHistoryEquiv
        (Fin 2) 3).apply_symm_apply bits) site
  have hzeroAt (site : Fin 3) :
      FiniteInstrument.tensorPowerHistoryAt
          (Fin 2) 3 zeroHistory site = 0 := by
    exact congrFun
      ((FiniteInstrument.tensorPowerHistoryEquiv
        (Fin 2) 3).apply_symm_apply
          (0 : Qubit.Bitstring (Fin 3))) site
  simp_rw [hcomputationalAt, hzeroAt,
    EuclideanSpace.basisFun_inner,
    why24OneQubitXBasis_zero_apply] at hinner
  simpa using hinner

private theorem why24CCZMagicBasisKet_zero_apply
    (bits : Qubit.Bitstring (Fin 3)) :
    why24CCZMagicBasisKet 0 bits =
      PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
        ((Real.sqrt 2 : Complex)⁻¹) ^ 3 := by
  change why24CCZPhaseOperator (why24ThreeQubitXBasis 0) bits = _
  rw [why24CCZPhaseOperator_apply, why24ThreeQubitXBasis_zero_apply]

private theorem why24CCZMagicState_apply_in_magic_normalization
    (bits : Qubit.Bitstring (Fin 3)) :
    why24CCZMagicState bits =
      PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
        ((Real.sqrt 2 : Complex)⁻¹) ^ 3 := by
  rw [why24CCZMagicState]
  change (Real.sqrt 128 : Complex) *
      (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
        (Real.sqrt (Fintype.card F1024 : Real) : Complex)⁻¹) = _
  have hsqrtCard :
      Real.sqrt (Fintype.card F1024 : Real) = 32 := by
    rw [f1024_card]
    norm_num
  have hsqrt128 : Real.sqrt (128 : Real) = 8 * Real.sqrt 2 := by
    have hsqrtNonneg := Real.sqrt_nonneg (128 : Real)
    have hsqrtTwoNonneg := Real.sqrt_nonneg (2 : Real)
    have hsqrtSq := Real.sq_sqrt (show (0 : Real) ≤ 128 by norm_num)
    have hsqrtTwoSq := Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)
    nlinarith
  rw [hsqrtCard, hsqrt128]
  have hsqrtTwoNe : (Real.sqrt 2 : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr sqrt_two_pos.ne'
  have hsqrtTwoMul :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  have hsqrtTwoCube :
      (Real.sqrt 2 : Complex) ^ 3 = 2 * (Real.sqrt 2 : Complex) := by
    calc
      (Real.sqrt 2 : Complex) ^ 3 =
          ((Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex)) *
            (Real.sqrt 2 : Complex) := by ring
      _ = 2 * (Real.sqrt 2 : Complex) := by rw [hsqrtTwoMul]
  field_simp [hsqrtTwoNe]
  push_cast
  rw [hsqrtTwoCube]
  calc
    8 * (Real.sqrt 2 : Complex) *
          PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) *
          (2 * (Real.sqrt 2 : Complex)) =
        ((Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex)) *
          (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * 16) := by
      ring
    _ = 2 *
        (PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * 16) := by
      rw [hsqrtTwoMul]
    _ = PauliSymplectic.binaryPhaseScalar (why24CCZPhase bits) * 32 := by
      ring

private theorem why24CCZMagicBasisKet_zero_eq_magicState :
    why24CCZMagicBasisKet 0 = why24CCZMagicState := by
  ext bits
  rw [why24CCZMagicBasisKet_zero_apply,
    why24CCZMagicState_apply_in_magic_normalization]

private theorem why24PureDensity_matrixEntry {ι : Type} [Fintype ι]
    (psi : EuclideanSpace Complex ι) (hnorm : ‖psi‖ ^ 2 = 1)
    (left right : ι) :
    inner Complex (EuclideanSpace.basisFun ι Complex left)
        ((DensityOperator.pureDensity psi hnorm).toOperator
          (EuclideanSpace.basisFun ι Complex right)) =
      star (psi right) * psi left := by
  rw [DensityOperator.pureDensity_toOperator]
  change inner Complex (EuclideanSpace.basisFun ι Complex left)
      (inner Complex psi (EuclideanSpace.basisFun ι Complex right) • psi) = _
  rw [inner_smul_right, EuclideanSpace.basisFun_inner,
    ← inner_conj_symm psi (EuclideanSpace.basisFun ι Complex right),
    EuclideanSpace.basisFun_inner]
  rfl

private theorem why24CCZMagicStateDensity_matrixEntry
    (left right : Qubit.Bitstring (Fin 3)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex left)
        (why24CCZMagicStateDensity.toOperator
          (EuclideanSpace.basisFun
            (Qubit.Bitstring (Fin 3)) Complex right)) =
      star (why24CCZMagicState right) * why24CCZMagicState left := by
  rw [why24CCZMagicStateDensity]
  exact why24PureDensity_matrixEntry why24CCZMagicState _ left right

/-- The tensor-power CCZ magic basis on the actual flattened register.  Its
labels retain one three-bit stochastic-Z word for every prepared resource. -/
noncomputable def why24JointCCZMagicBasis (count : Nat) :
    OrthonormalBasis (Fin count -> Qubit.Bitstring (Fin 3)) Complex
      (Why24CCZRegister (Fin count)) :=
  ((FiniteInstrument.tensorPowerBasis why24CCZMagicBasis count).map
      (FiniteInstrument.tensorPowerQubitRegisterTransport
        (Fin 3) count).toLinearIsometryEquiv).reindex
    (FiniteInstrument.tensorPowerHistoryEquiv
      (Qubit.Bitstring (Fin 3)) count)

/-- One normalized joint CCZ magic-basis vector. -/
noncomputable def why24JointCCZMagicBasisKet (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    Why24CCZRegister (Fin count) :=
  why24JointCCZMagicBasis count error

private theorem why24JointCCZMagicBasisKet_norm (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    ‖why24JointCCZMagicBasisKet count error‖ = 1 :=
  (why24JointCCZMagicBasis count).orthonormal.norm_eq_one error

private theorem why24JointCCZMagicBasisKet_normSq (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    ‖why24JointCCZMagicBasisKet count error‖ ^ 2 = 1 := by
  rw [why24JointCCZMagicBasisKet_norm]
  norm_num

/-- Inner products of two recursive CCZ tensor bases factor over their actual
resource coordinates. -/
private theorem why24TensorPowerCCZBasis_inner_eq_prod
    (leftBasis rightBasis :
      OrthonormalBasis (Qubit.Bitstring (Fin 3)) Complex Why24CCZSpace) :
    forall (count : Nat)
      (left right : FiniteInstrument.tensorPowerHistory
        (Qubit.Bitstring (Fin 3)) count),
      inner Complex
          (FiniteInstrument.tensorPowerBasis leftBasis count left)
          (FiniteInstrument.tensorPowerBasis rightBasis count right) =
        ∏ site : Fin count,
          inner Complex
            (leftBasis (FiniteInstrument.tensorPowerHistoryAt
              (Qubit.Bitstring (Fin 3)) count left site))
            (rightBasis (FiniteInstrument.tensorPowerHistoryAt
              (Qubit.Bitstring (Fin 3)) count right site)) := by
  intro count
  induction count with
  | zero =>
      intro left right
      cases left
      cases right
      rw [FiniteInstrument.tensorPowerBasis_zero_apply,
        FiniteInstrument.tensorPowerBasis_zero_apply]
      rw [inner_self_eq_norm_sq_to_K,
        (EuclideanSpace.basisFun
          (ULift (Fin 1)) Complex).norm_eq_one]
      simp
  | succ count ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [FiniteInstrument.tensorPowerBasis_succ_apply,
        FiniteInstrument.tensorPowerBasis_succ_apply,
        TensorProduct.inner_tmul, Fin.prod_univ_succ]
      simp only [FiniteInstrument.tensorPowerHistoryAt,
        Fin.cases_zero, Fin.cases_succ]
      rw [ih leftTail rightTail]

/-- Joint magic-basis amplitudes are the literal products of the one-resource
CCZ magic-basis amplitudes. -/
private theorem why24JointCCZMagicBasisKet_apply (count : Nat)
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (bits : Qubit.Bitstring (Fin count × Fin 3)) :
    why24JointCCZMagicBasisKet count error bits =
      ∏ site : Fin count,
        why24CCZMagicBasisKet (error site)
          (fun qubit => bits (site, qubit)) := by
  let computationalHistory :=
    (FiniteInstrument.tensorPowerQubitBitstringEquiv
      (Fin 3) count).symm bits
  let magicHistory :=
    FiniteInstrument.tensorPowerHistoryOf
      (Qubit.Bitstring (Fin 3)) count error
  have hinner := (FiniteInstrument.tensorPowerQubitRegisterTransport
      (Fin 3) count).map_inner
    (FiniteInstrument.tensorPowerBasis
      (EuclideanSpace.basisFun (Qubit.Bitstring (Fin 3)) Complex)
      count computationalHistory)
    (FiniteInstrument.tensorPowerBasis why24CCZMagicBasis
      count magicHistory)
  rw [FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis] at hinner
  have hcomputational :
      FiniteInstrument.tensorPowerQubitBitstringEquiv
          (Fin 3) count computationalHistory = bits := by
    exact (FiniteInstrument.tensorPowerQubitBitstringEquiv
      (Fin 3) count).apply_symm_apply bits
  have hjoint :
      FiniteInstrument.tensorPowerQubitRegisterTransport (Fin 3) count
          (FiniteInstrument.tensorPowerBasis why24CCZMagicBasis
            count magicHistory) =
        why24JointCCZMagicBasisKet count error := by
    rw [why24JointCCZMagicBasisKet, why24JointCCZMagicBasis,
      OrthonormalBasis.reindex_apply]
    rfl
  rw [hcomputational, hjoint, EuclideanSpace.basisFun_inner] at hinner
  rw [why24TensorPowerCCZBasis_inner_eq_prod] at hinner
  have hcomputationalAt (site : Fin count) :
      FiniteInstrument.tensorPowerHistoryAt
          (Qubit.Bitstring (Fin 3)) count computationalHistory site =
        fun qubit => bits (site, qubit) := by
    funext qubit
    exact FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
      (Fin 3) count bits site qubit
  have hmagicAt (site : Fin count) :
      FiniteInstrument.tensorPowerHistoryAt
          (Qubit.Bitstring (Fin 3)) count magicHistory site = error site := by
    exact congrFun (FiniteInstrument.tensorPowerHistoryAt_of
      (Qubit.Bitstring (Fin 3)) count error) site
  simp_rw [hcomputationalAt, hmagicAt] at hinner
  simpa only [EuclideanSpace.basisFun_inner,
    why24CCZMagicBasisKet] using hinner

private theorem why24IdealCCZRegisterDensity_eq_jointZeroPure (count : Nat) :
    why24IdealCCZRegisterDensity count =
      DensityOperator.pureDensity
        (why24JointCCZMagicBasisKet count 0)
        (why24JointCCZMagicBasisKet_normSq count 0) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun
    (Qubit.Bitstring (Fin count × Fin 3)) Complex
  apply basis.toBasis.ext
  intro right
  apply InnerProductSpace.ext_inner_left_basis basis.toBasis
  intro left
  dsimp [basis]
  rw [why24IdealCCZRegisterDensity,
    FiniteInstrument.tensorPowerRegisterProductDensity_matrixEntry]
  simp_rw [why24CCZMagicStateDensity_matrixEntry]
  rw [inner_smul_right, EuclideanSpace.basisFun_inner,
    ← inner_conj_symm (why24JointCCZMagicBasisKet count 0)
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (Fin count × Fin 3)) Complex right),
    EuclideanSpace.basisFun_inner,
    why24JointCCZMagicBasisKet_apply,
    why24JointCCZMagicBasisKet_apply]
  simp only [Pi.zero_apply]
  rw [why24CCZMagicBasisKet_zero_eq_magicState]
  rw [map_prod, Finset.prod_mul_distrib]
  rfl

private theorem why24IdealCCZRegisterDensity_toOperator (count : Nat) :
    (why24IdealCCZRegisterDensity count).toOperator =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet count 0)
        (why24JointCCZMagicBasisKet count 0)).toLinearMap := by
  rw [why24IdealCCZRegisterDensity_eq_jointZeroPure,
    DensityOperator.pureDensity_toOperator]

/-- The selected tensor factor of a joint magic-basis word at one declared
fault set. -/
private noncomputable def why24FaultSelectedMagicState {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    (why24FaultSubsystem fault).selectedSystem :=
  WithLp.toLp 2 fun selected =>
    ∏ site : ↥fault,
      why24CCZMagicBasisKet (error site) fun qubit =>
        selected ⟨(site, qubit), by
          rw [why24FaultSubsystem_selected]
          exact Finset.mem_product.mpr ⟨site.property, Finset.mem_univ _⟩⟩

/-- The complementary tensor factor of a joint magic-basis word at one
declared fault set. -/
private noncomputable def why24FaultComplementMagicState {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    (why24FaultSubsystem fault).complementSystem :=
  WithLp.toLp 2 fun complement =>
    ∏ site : ↥faultᶜ,
      why24CCZMagicBasisKet (error site) fun qubit =>
        complement ⟨(site, qubit), by
          rw [why24FaultSubsystem_selected]
          intro hselected
          exact (Finset.mem_compl.mp site.property)
            (Finset.mem_product.mp hselected).1⟩

/-- Evaluate the inverse fault/complement coordinate factorization on a pure
tensor. -/
private theorem why24FaultRegisterFactorization_symm_tmul_apply {count : Nat}
    (fault : Finset (Fin count))
    (selectedState : (why24FaultSubsystem fault).selectedSystem)
    (complementState : (why24FaultSubsystem fault).complementSystem)
    (bits : Qubit.Bitstring (Fin count × Fin 3)) :
    (why24FaultSubsystem fault).registerFactorization.symm
        (selectedState ⊗ₜ[Complex] complementState) bits =
      selectedState ((why24FaultSubsystem fault).splitLabel bits).1 *
        complementState ((why24FaultSubsystem fault).splitLabel bits).2 := by
  have hinner := (why24FaultSubsystem fault).registerFactorization.map_inner
    (EuclideanSpace.basisFun
      (Qubit.Bitstring (Fin count × Fin 3)) Complex bits)
    ((why24FaultSubsystem fault).registerFactorization.symm
      (selectedState ⊗ₜ[Complex] complementState))
  simp only [UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.apply_symm_apply] at hinner
  rw [QuditSubsystem.registerFactorization_apply_basis,
    TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

/-- A joint CCZ magic-basis ket factors exactly across every declared fault
set and its physical complement. -/
private theorem why24JointCCZMagicBasisKet_faultFactorization {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    (why24FaultSubsystem fault).registerFactorization
        (why24JointCCZMagicBasisKet count error) =
      why24FaultSelectedMagicState fault error ⊗ₜ[Complex]
        why24FaultComplementMagicState fault error := by
  apply (why24FaultSubsystem fault).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.symm_apply_apply]
  ext bits
  change why24JointCCZMagicBasisKet count error bits =
    (why24FaultSubsystem fault).registerFactorization.symm
      (why24FaultSelectedMagicState fault error ⊗ₜ[Complex]
        why24FaultComplementMagicState fault error) bits
  rw [why24FaultRegisterFactorization_symm_tmul_apply,
    why24JointCCZMagicBasisKet_apply]
  change (∏ site : Fin count,
      why24CCZMagicBasisKet (error site) (fun qubit => bits (site, qubit))) =
    (∏ site : ↥fault,
      why24CCZMagicBasisKet (error site) (fun qubit =>
        ((why24FaultSubsystem fault).splitLabel bits).1
          ⟨(site, qubit), by
            rw [why24FaultSubsystem_selected]
            exact Finset.mem_product.mpr ⟨site.property, Finset.mem_univ _⟩⟩)) *
      ∏ site : ↥faultᶜ,
        why24CCZMagicBasisKet (error site) (fun qubit =>
          ((why24FaultSubsystem fault).splitLabel bits).2
            ⟨(site, qubit), by
              rw [why24FaultSubsystem_selected]
              intro hselected
              exact (Finset.mem_compl.mp site.property)
                (Finset.mem_product.mp hselected).1⟩)
  simp only [QuditSubsystem.splitLabel]
  let amplitude : Fin count -> Complex := fun site =>
    why24CCZMagicBasisKet (error site) (fun qubit => bits (site, qubit))
  change (∏ site, amplitude site) =
    (∏ site : ↥fault, amplitude site) * ∏ site : ↥faultᶜ, amplitude site
  calc
    (∏ site, amplitude site) =
        (∏ site ∈ fault, amplitude site) * ∏ site ∈ faultᶜ, amplitude site :=
      (Finset.prod_mul_prod_compl fault amplitude).symm
    _ = (∏ site : ↥fault, amplitude site) *
          ∏ site : ↥faultᶜ, amplitude site :=
      congrArg₂ (fun x y : Complex => x * y)
        (Finset.prod_coe_sort fault amplitude).symm
        (Finset.prod_coe_sort faultᶜ amplitude).symm

private theorem why24FaultRegisterFactorization_extendLocalToRegister_apply
    {count : Nat} (fault : Finset (Fin count))
    (localOperator : Operator (why24FaultSubsystem fault).selectedSystem)
    (psi : Why24CCZRegister (Fin count)) :
    (why24FaultSubsystem fault).registerFactorization
        ((why24FaultSubsystem fault).extendLocalToRegister localOperator psi) =
      (why24FaultSubsystem fault).extendLocal localOperator
        ((why24FaultSubsystem fault).registerFactorization psi) := by
  simp [QuditSubsystem.extendLocalToRegister,
    UnitaryTransport.conjOperator_apply]

private def why24OutsideFaultError {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    Fin count -> Qubit.Bitstring (Fin 3) :=
  fun site => if site ∈ fault then 0 else error site

private theorem why24OutsideFaultError_ne_zero {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (site : Fin count) (hsite : site ∉ fault)
    (herror : error site ≠ 0) :
    why24OutsideFaultError fault error ≠ 0 := by
  intro hzero
  have hat := congrFun hzero site
  rw [why24OutsideFaultError, if_neg hsite] at hat
  exact herror hat

private theorem why24FaultSelectedMagicState_outside {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    why24FaultSelectedMagicState fault
        (why24OutsideFaultError fault error) =
      why24FaultSelectedMagicState fault 0 := by
  ext selected
  simp [why24FaultSelectedMagicState, why24OutsideFaultError]

private theorem why24FaultComplementMagicState_outside {count : Nat}
    (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3)) :
    why24FaultComplementMagicState fault
        (why24OutsideFaultError fault error) =
      why24FaultComplementMagicState fault error := by
  ext complement
  apply Fintype.prod_congr
  intro site
  rw [why24OutsideFaultError,
    if_neg (Finset.mem_compl.mp site.property)]

private theorem why24FaultComplementMagicState_inner_zero_of_outside
    {count : Nat} (fault : Finset (Fin count))
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (site : Fin count) (hsite : site ∉ fault)
    (herror : error site ≠ 0) :
    inner Complex (why24FaultComplementMagicState fault error)
        (why24FaultComplementMagicState fault 0) = 0 := by
  let outside := why24OutsideFaultError fault error
  have houtside_ne : outside ≠ 0 :=
    why24OutsideFaultError_ne_zero fault error site hsite herror
  have horthogonal :
      inner Complex (why24JointCCZMagicBasisKet count outside)
          (why24JointCCZMagicBasisKet count 0) = 0 := by
    change inner Complex
      ((why24JointCCZMagicBasis count) outside)
      ((why24JointCCZMagicBasis count) 0) = 0
    rw [(why24JointCCZMagicBasis count).inner_eq_ite,
      if_neg houtside_ne]
  have hfactored :=
    (why24FaultSubsystem fault).registerFactorization.map_inner
      (why24JointCCZMagicBasisKet count outside)
      (why24JointCCZMagicBasisKet count 0)
  rw [why24JointCCZMagicBasisKet_faultFactorization,
    why24JointCCZMagicBasisKet_faultFactorization,
    TensorProduct.inner_tmul,
    why24FaultSelectedMagicState_outside,
    why24FaultComplementMagicState_outside,
    horthogonal] at hfactored
  have hzeroFactored := hfactored
  have hzeroSelf :
      inner Complex (why24JointCCZMagicBasisKet count 0)
          (why24JointCCZMagicBasisKet count 0) = 1 := by
    change inner Complex
      ((why24JointCCZMagicBasis count) 0)
      ((why24JointCCZMagicBasis count) 0) = 1
    rw [inner_self_eq_norm_sq_to_K,
      (why24JointCCZMagicBasis count).orthonormal.norm_eq_one]
    norm_num
  have hself :=
    (why24FaultSubsystem fault).registerFactorization.map_inner
      (why24JointCCZMagicBasisKet count 0)
      (why24JointCCZMagicBasisKet count 0)
  rw [why24JointCCZMagicBasisKet_faultFactorization,
    TensorProduct.inner_tmul, hzeroSelf] at hself
  have hselected_ne :
      inner Complex (why24FaultSelectedMagicState fault 0)
          (why24FaultSelectedMagicState fault 0) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hself
    norm_num at hself
  exact (mul_eq_zero.mp hzeroFactored).resolve_left hselected_ne

private theorem why24SupportedOperator_magicAmplitude_eq_zero
    {count : Nat} (fault : Finset (Fin count))
    (operator : Operator (Why24CCZRegister (Fin count)))
    (hsupported :
      (why24FaultSubsystem fault).OperatorSupportedOnRegister operator)
    (error : Fin count -> Qubit.Bitstring (Fin 3))
    (site : Fin count) (hsite : site ∉ fault)
    (herror : error site ≠ 0) :
    inner Complex (why24JointCCZMagicBasisKet count error)
        (operator (why24JointCCZMagicBasisKet count 0)) = 0 := by
  rcases hsupported with ⟨localOperator, rfl⟩
  have hfactored :=
    (why24FaultSubsystem fault).registerFactorization.map_inner
      (why24JointCCZMagicBasisKet count error)
      ((why24FaultSubsystem fault).extendLocalToRegister localOperator
        (why24JointCCZMagicBasisKet count 0))
  rw [why24JointCCZMagicBasisKet_faultFactorization,
    why24FaultRegisterFactorization_extendLocalToRegister_apply,
    why24JointCCZMagicBasisKet_faultFactorization,
    QuditSubsystem.extendLocal_apply_tmul,
    TensorProduct.inner_tmul,
    why24FaultComplementMagicState_inner_zero_of_outside
      fault error site hsite herror,
    mul_zero] at hfactored
  exact hfactored.symm

private theorem why24CCZMagicBasisKet_norm
    (error : Qubit.Bitstring (Fin 3)) :
    ‖why24CCZMagicBasisKet error‖ = 1 :=
  why24CCZMagicBasis.orthonormal.norm_eq_one error

private theorem why24CCZMagicBasisKet_normSq
    (error : Qubit.Bitstring (Fin 3)) :
    ‖why24CCZMagicBasisKet error‖ ^ 2 = 1 := by
  rw [why24CCZMagicBasisKet_norm]
  norm_num

/-- One explicit commuting CCZ stabilizer, displayed spectrally in the actual
magic basis.  Measuring all three generators is the projective twirl below. -/
noncomputable def why24CCZStabilizer (generator : Fin 3) :
    Operator Why24CCZSpace :=
  ∑ error : Qubit.Bitstring (Fin 3),
    PauliSymplectic.binaryPhaseScalar
        ((PauliSymplectic.bitstringWordEquiv (Fin 3) error) generator) •
      (InnerProductSpace.rankOne Complex
        (why24CCZMagicBasisKet error)
        (why24CCZMagicBasisKet error)).toLinearMap

/-- Rank-one projectors for the complete CCZ stabilizer measurement. -/
noncomputable def why24CCZTwirlKraus :
    FiniteKrausFamily (Qubit.Bitstring (Fin 3)) Why24CCZSpace Why24CCZSpace where
  operator error := (InnerProductSpace.rankOne Complex
    (why24CCZMagicBasisKet error)
    (why24CCZMagicBasisKet error)).toLinearMap

/-- The complete projective stabilizer measurement, with its Z-error word as
the observed classical outcome. -/
noncomputable def why24CCZTwirlInstrument :
    FiniteInstrument (Qubit.Bitstring (Fin 3)) (Qubit.Bitstring (Fin 3))
      Why24CCZSpace Why24CCZSpace where
  kraus := why24CCZTwirlKraus
  observe := id

private theorem why24CCZTwirlKraus_adjoint
    (error : Qubit.Bitstring (Fin 3)) :
    LinearMap.adjoint (why24CCZTwirlKraus.operator error) =
      why24CCZTwirlKraus.operator error := by
  simp only [why24CCZTwirlKraus]
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  change ((InnerProductSpace.rankOne Complex
    (why24CCZMagicBasisKet error)
    (why24CCZMagicBasisKet error)).adjoint).toLinearMap = _
  rw [InnerProductSpace.adjoint_rankOne]

/-- The projective magic-basis Kraus family is complete. -/
theorem why24CCZTwirlInstrument_complete :
    why24CCZTwirlInstrument.kraus.Complete := by
  unfold FiniteKrausFamily.Complete
  change (∑ error : Qubit.Bitstring (Fin 3),
    LinearMap.adjoint (why24CCZTwirlKraus.operator error) *
      why24CCZTwirlKraus.operator error) = 1
  calc
    (∑ error : Qubit.Bitstring (Fin 3),
      LinearMap.adjoint (why24CCZTwirlKraus.operator error) *
        why24CCZTwirlKraus.operator error) =
        ∑ error : Qubit.Bitstring (Fin 3),
          why24CCZTwirlKraus.operator error := by
      apply Finset.sum_congr rfl
      intro error _
      let P : Operator Why24CCZSpace := why24CCZTwirlKraus.operator error
      have hP : P.IsSymmetricProjection := by
        simpa [P, why24CCZTwirlKraus] using
          (InnerProductSpace.isSymmetricProjection_rankOne_self
            (𝕜 := Complex) (why24CCZMagicBasisKet_norm error))
      rw [why24CCZTwirlKraus_adjoint]
      change P * P = P
      exact hP.isIdempotentElem.eq
    _ = 1 := by
      have hport := congrArg ContinuousLinearMap.toLinearMap
        (OrthonormalBasis.sum_rankOne_eq_id why24CCZMagicBasis)
      simp [why24CCZTwirlKraus, why24CCZMagicBasisKet] at hport ⊢
      exact hport

/-- The actual CPTP channel obtained by forgetting the stabilizer outcomes. -/
noncomputable def why24CCZTwirlChannel :
    QuantumChannel Why24CCZSpace Why24CCZSpace :=
  why24CCZTwirlInstrument.kraus.toQuantumChannel
    why24CCZTwirlInstrument_complete

/-- The physical probability of one stochastic Z-error word after twirling. -/
noncomputable def why24TwirledZErrorDistribution
    (rho : DensityOperator Why24CCZSpace)
    (error : Qubit.Bitstring (Fin 3)) : Real :=
  (inner Complex (why24CCZMagicBasisKet error)
    (rho.toOperator (why24CCZMagicBasisKet error))).re

theorem why24TwirledZErrorDistribution_nonneg
    (rho : DensityOperator Why24CCZSpace)
    (error : Qubit.Bitstring (Fin 3)) :
    0 ≤ why24TwirledZErrorDistribution rho error := by
  exact rho.positive.re_inner_nonneg_right
    (why24CCZMagicBasisKet error)

theorem why24TwirledZErrorDistribution_sum
    (rho : DensityOperator Why24CCZSpace) :
    ∑ error : Qubit.Bitstring (Fin 3),
      why24TwirledZErrorDistribution rho error = 1 := by
  have htrace := rho.trace_one
  rw [LinearMap.trace_eq_sum_inner rho.toOperator why24CCZMagicBasis] at htrace
  have hre := congrArg Complex.re htrace
  simpa [why24TwirledZErrorDistribution, why24CCZMagicBasisKet,
    Complex.re_sum] using hre

/-- The literal stochastic-Z density induced by the physical stabilizer
measurement of `rho`. -/
noncomputable def why24CCZStochasticZMixture
    (rho : DensityOperator Why24CCZSpace) : DensityOperator Why24CCZSpace :=
  DensityOperator.convexCombination Finset.univ
    (why24TwirledZErrorDistribution rho)
    (fun error => DensityOperator.pureDensity
      (why24CCZMagicBasisKet error) (why24CCZMagicBasisKet_normSq error))
    (by
      intro error _
      exact why24TwirledZErrorDistribution_nonneg rho error)
    (by simpa using why24TwirledZErrorDistribution_sum rho)

private theorem why24RankOne_sandwich
    (u : Why24CCZSpace) (_hu : inner Complex u u = 1)
    (A : Operator Why24CCZSpace) :
    (InnerProductSpace.rankOne Complex u u).toLinearMap *
        (A * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
      (inner Complex u (A u)) •
        (InnerProductSpace.rankOne Complex u u).toLinearMap := by
  ext vector
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply]
  ring

private theorem why24Inner_apply_real_of_positive
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (rho : DensityOperator H) (u : H) :
    ((inner Complex u (rho.toOperator u)).re : Complex) =
      inner Complex u (rho.toOperator u) := by
  have hpositive := (LinearMap.isPositive_iff_complex rho.toOperator).mp
    rho.positive u
  simpa [rho.positive.isSymmetric u u] using hpositive.1

/-- Forgetting the actual stabilizer measurement outcome is exactly the
stochastic mixture of physical Z-error magic-basis states. -/
theorem why24CCZTwirl_eq_stochasticZMixture
    (rho : DensityOperator Why24CCZSpace) :
    why24CCZTwirlChannel.mapDensity rho =
      why24CCZStochasticZMixture rho := by
  apply DensityOperator.ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator, why24CCZTwirlChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum,
    why24CCZStochasticZMixture,
    DensityOperator.convexCombination_toOperator]
  apply Finset.sum_congr rfl
  intro error _
  have hinner : inner Complex (why24CCZMagicBasisKet error)
      (why24CCZMagicBasisKet error) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, why24CCZMagicBasisKet_norm]
    norm_num
  simp only [why24CCZTwirlInstrument]
  rw [why24CCZTwirlKraus_adjoint]
  simp only [why24CCZTwirlKraus, DensityOperator.pureDensity_toOperator]
  change
    (InnerProductSpace.rankOne Complex
        (why24CCZMagicBasisKet error)
        (why24CCZMagicBasisKet error)).toLinearMap *
      (rho.toOperator *
        (InnerProductSpace.rankOne Complex
          (why24CCZMagicBasisKet error)
          (why24CCZMagicBasisKet error)).toLinearMap) = _
  rw [why24RankOne_sandwich _ hinner rho.toOperator]
  rw [← why24Inner_apply_real_of_positive rho
    (why24CCZMagicBasisKet error)]
  rfl

/-- The random support set carrying the twirled stochastic Z errors keeps the
original source fault-set law. -/
noncomputable def why24TwirledZErrorFaultDistribution {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) : Finset (Fin count) → Real :=
  preparation.faultMass

/-- Stabilizer twirling changes coherent faults into stochastic Z-error
branches but does not change the local-stochastic tail of their support set. -/
theorem why24TwirledZError_tail {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) (sites : Finset (Fin count)) :
    (∑ fault : Finset (Fin count),
      if sites ⊆ fault then
        why24TwirledZErrorFaultDistribution preparation fault else 0) ≤
      preparation.rate ^ sites.card :=
  preparation.why24LocalStochastic_tail_maxRate sites

/-! ## The actual AG dual-code decoder -/

-- The source-facing divisors and rational places in #887 use the direct
-- affine constant algebra.  Install that already-exported algebra here so
-- the decoder's Riemann--Roch spaces live on exactly the same place carrier.
@[reducible] noncomputable local instance (priority := 2000)
    why24DecoderDirectConstantAlgebra (height : Nat) :
    Algebra F1024 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorAlgebra height

noncomputable local instance (priority := 2000)
    why24DecoderDirectConstantScalarTower (height : Nat) :
    IsScalarTower F1024 F1024TowerF1 (F1024TowerLevel height) :=
  f1024TowerLevelCoordinateDivisorRationalScalarTower height

/-- WHY24's one-place auxiliary divisor `A₁`, supported at the reserved
`E`-place and having degree `floor (9 g / 8)`. -/
noncomputable def f1024Why24OddDecoderAuxiliaryDivisor (r : Nat) :
    Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2))) :=
  selectedAuxiliaryDegree (oddGenus r) •
    Finsupp.single (f1024Why24OddEPlace r).place (1 : Int)

private theorem why24Decoder_singleRationalPlace_degree (r : Nat)
    (Q : RationalPlace F1024 (F1024TowerLevel (2 * r + 2))) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (Finsupp.single Q.place (1 : Int)) = 1 := by
  simp [Divisor.degree, Divisor.degreeHom,
    RationalPlace.globalResidueDegree_eq_one]

private theorem why24Decoder_divisor_degree_nsmul (r n : Nat)
    (D : Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2)))) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2))) (n • D) =
      (n : Int) *
        Divisor.degree
          (GlobalPlace.residueDegree
            (k := F1024) (F := F1024TowerLevel (2 * r + 2))) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom
      (GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))).map_nsmul n D

/-- The auxiliary divisor has the literal source degree. -/
theorem f1024Why24OddDecoderAuxiliaryDivisor_degree (r : Nat) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderAuxiliaryDivisor r) =
      selectedAuxiliaryDegree (oddGenus r) := by
  rw [f1024Why24OddDecoderAuxiliaryDivisor,
    why24Decoder_divisor_degree_nsmul,
    why24Decoder_singleRationalPlace_degree]
  simp

/-- The auxiliary divisor is disjoint from every actual physical evaluation
place. -/
theorem f1024Why24OddDecoderAuxiliary_disjoint (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddDecoderAuxiliaryDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  have hne : (f1024Why24OddEPlace r).place ≠
      (f1024Why24OddPhysicalRationalPlace r site).place := by
    exact (f1024Why24OddCandidatePlace_ne_EPlace r site.1.1).symm
  simp [f1024Why24OddDecoderAuxiliaryDivisor, hne]

/-- Riemann's lower bound gives more locator unknowns than the source
decoding radius, so every radius-sized error support has a nonzero locator. -/
theorem f1024Why24OddDecoderAuxiliary_dimension_gt_radius (r : Nat) :
    f1024Why24OddDecodingRadius r <
      Module.finrank F1024
        (GlobalPlace.riemannRochSubmodule
          (f1024Why24OddDecoderAuxiliaryDivisor r)) := by
  have hlower := GlobalPlace.riemannRoch_lower_bound
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddDecoderAuxiliaryDivisor r)
  rw [f1024Why24OddDecoderAuxiliaryDivisor_degree,
    f1024TowerLevel_functionFieldGenus_even] at hlower
  simp only [GlobalPlace.riemannRochDimension] at hlower
  have haux : selectedAuxiliaryDegree (oddGenus r) =
      oddGenus r + selectedDecodingRadius (oddGenus r) := by
    simp only [selectedAuxiliaryDegree, selectedDecodingRadius]
    omega
  rw [haux] at hlower
  simp only [f1024Why24OddDecodingRadius, selectedDecodingRadius,
    Nat.cast_add] at hlower ⊢
  omega

/-- The divisor whose Riemann--Roch basis supplies the key-equation rows. -/
noncomputable def f1024Why24OddDecoderComplementDivisor (r : Nat) :
    Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2))) :=
  f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r -
    f1024Why24OddDecoderAuxiliaryDivisor r

private theorem why24DecoderPivotDivisor_apply_physical (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddPivotDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  simpa only [f1024Why24OddPivotDivisor, evaluationDivisor] using
    zeroCoordinateDivisor_apply_eq_zero_of_not_mem
      (f1024Why24OddPivotRationalPlace r) Finset.univ
      (f1024Why24OddPhysicalRationalPlace r site).place (by
        intro logical _ hplace
        apply site.2
        refine ⟨logical, ?_⟩
        apply f1024Why24OddRetainedRationalPlace_injective r
        exact hplace)

private theorem why24DecoderShortenedDivisor_apply_physical (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  change f1024Why24OddADivisor r
        (f1024Why24OddRetainedRationalPlace r site.1).place -
      f1024Why24OddPivotDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0
  rw [f1024Why24OddADivisor_apply_retained,
    why24DecoderPivotDivisor_apply_physical, sub_zero]

private theorem why24DecoderComplementDivisor_apply_physical (r : Nat)
    (site : f1024Why24OddPhysicalSite r) :
    f1024Why24OddDecoderComplementDivisor r
        (f1024Why24OddPhysicalRationalPlace r site).place = 0 := by
  rw [f1024Why24OddDecoderComplementDivisor, Finsupp.sub_apply,
    why24DecoderShortenedDivisor_apply_physical,
    f1024Why24OddDecoderAuxiliary_disjoint]
  simp

private noncomputable instance why24DecoderAuxiliary_finiteDimensional
    (r : Nat) :
    FiniteDimensional F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r)) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2)) _

private noncomputable instance why24DecoderComplement_finiteDimensional
    (r : Nat) :
    FiniteDimensional F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r)) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2)) _

private noncomputable instance why24DecoderShortened_finiteDimensional
    (r : Nat) :
    FiniteDimensional F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (k := F1024) (F := F1024TowerLevel (2 * r + 2)) _

/-- Multiplication by one key-equation row embeds locator unknowns into the
actual shortened Riemann--Roch space. -/
private noncomputable def why24DecoderMultiplyIntoShortened (r : Nat)
    (row : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r) →ₗ[F1024]
      GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) where
  toFun locator := ⟨(locator : F1024TowerLevel (2 * r + 2)) * row,
    by
      have hproduct := GlobalPlace.mul_mem_riemannRochSubmodule_add
        locator.property row.property
      have hdivisor : f1024Why24OddDecoderAuxiliaryDivisor r +
          f1024Why24OddDecoderComplementDivisor r =
        f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r := by
        rw [f1024Why24OddDecoderComplementDivisor]
        abel
      rwa [hdivisor] at hproduct⟩
  map_add' left right := by
    apply Subtype.ext
    simp only [Submodule.coe_add, add_mul]
  map_smul' scalar locator := by
    apply Subtype.ext
    simpa only [Submodule.coe_smul_of_tower, RingHom.id_apply] using
      (smul_mul_assoc scalar
        (locator : F1024TowerLevel (2 * r + 2))
        (row : F1024TowerLevel (2 * r + 2)))

/-- Coordinate-scaled evaluation on the exact shortened divisor. -/
private noncomputable def why24DecoderScaledEvaluationLinearMap (r : Nat) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun function site := f1024Why24OddCoordinateWeight r site.1 *
    agEvaluationLinearMap
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (why24DecoderShortenedDivisor_apply_physical r) function site
  map_add' left right := by
    funext site
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' scalar function := by
    funext site
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    ring

private theorem why24DecoderScaledEvaluation_mem_stabilizer (r : Nat)
    (function : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)) :
    why24DecoderScaledEvaluationLinearMap r function ∈
      (f1024Why24OddWeightedMatrix r).stabilizerCode.carrier := by
  rw [f1024Why24OddStabilizerCode_eq_scaledShortenedAGCode]
  exact ⟨function, rfl⟩

/-- Scaled evaluation, bundled with its proof of membership in the actual
stabilizer code. -/
private noncomputable def why24DecoderScaledEvaluationToStabilizer (r : Nat) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) →ₗ[F1024]
      (f1024Why24OddWeightedMatrix r).stabilizerCode.carrier where
  toFun function := ⟨why24DecoderScaledEvaluationLinearMap r function,
    why24DecoderScaledEvaluation_mem_stabilizer r function⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add (why24DecoderScaledEvaluationLinearMap r) left right
  map_smul' scalar function := by
    apply Subtype.ext
    exact map_smul (why24DecoderScaledEvaluationLinearMap r) scalar function

/-- Pair a physical word with every actual stabilizer-code word. -/
private def why24DecoderRawSyndromePairing (r : Nat) :
    Word F1024 (f1024Why24OddPhysicalSite r) →ₗ[F1024]
      ((f1024Why24OddWeightedMatrix r).stabilizerCode.carrier →ₗ[F1024]
        F1024) where
  toFun error :=
    { toFun := fun codeword => wordPairing error codeword.1
      map_add' := by
        intro left right
        simp only [Submodule.coe_add, map_add]
      map_smul' := by
        intro scalar codeword
        change wordPairing error (scalar • codeword.1) =
          scalar • wordPairing error codeword.1
        exact map_smul (wordPairing error) scalar codeword.1 }
  map_add' left right := by
    ext codeword
    change wordPairing (left + right) codeword.1 =
      wordPairing left codeword.1 + wordPairing right codeword.1
    exact LinearMap.congr_fun (map_add wordPairing left right) codeword.1
  map_smul' scalar error := by
    ext codeword
    change wordPairing (scalar • error) codeword.1 =
      scalar • wordPairing error codeword.1
    exact LinearMap.congr_fun (map_smul wordPairing scalar error) codeword.1

private theorem why24DecoderStabilizerDual_le_pairingKernel (r : Nat) :
    (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier ≤
      LinearMap.ker (why24DecoderRawSyndromePairing r) := by
  intro error herror
  rw [LinearMap.mem_ker]
  ext codeword
  exact (f1024Why24OddWeightedMatrix r).stabilizerCode.orthogonal_of_mem_dual
    herror codeword.2

/-- The syndrome as a genuine linear functional on the actual stabilizer
code.  `liftQ` proves that no quotient representative is chosen. -/
private noncomputable def why24DecoderSyndromePairing (r : Nat) :
    f1024Why24OddZSyndrome r →ₗ[F1024]
      ((f1024Why24OddWeightedMatrix r).stabilizerCode.carrier →ₗ[F1024]
        F1024) :=
  (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier.liftQ
    (why24DecoderRawSyndromePairing r)
    (why24DecoderStabilizerDual_le_pairingKernel r)

/-- Row index of the finite Stichtenoth key-equation matrix. -/
abbrev f1024Why24OddDecoderEquationIndex (r : Nat) : Type :=
  Fin (Module.finrank F1024
    (GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r)))

/-- The actual finite key-equation linear system.  Its columns are locator
coefficients in `L(A₁)`; its rows are the finite basis of
`L(A-D_pivot-A₁)`; every entry is evaluated through the intrinsic syndrome
quotient pairing. -/
noncomputable def f1024Why24OddDecoderLinearSystem (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r) →ₗ[F1024]
      (f1024Why24OddDecoderEquationIndex r → F1024) :=
  LinearMap.pi fun equation =>
    (why24DecoderSyndromePairing r syndrome).comp
      ((why24DecoderScaledEvaluationToStabilizer r).comp
        (why24DecoderMultiplyIntoShortened r
          (Module.finBasis F1024
            (GlobalPlace.riemannRochSubmodule
              (f1024Why24OddDecoderComplementDivisor r)) equation)))

private theorem why24Decoder_evaluationRegularityOfMem (r : Nat)
    (D : Divisor (GlobalPlace F1024 (F1024TowerLevel (2 * r + 2))))
    (hD : forall site : f1024Why24OddPhysicalSite r,
      D (f1024Why24OddPhysicalRationalPlace r site).place = 0)
    (function : GlobalPlace.riemannRochSubmodule D)
    (site : f1024Why24OddPhysicalSite r) :
    GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place
      (function : F1024TowerLevel (2 * r + 2)) := by
  have hbound :=
    (GlobalPlace.mem_riemannRochSubmodule_iff D
      (function : F1024TowerLevel (2 * r + 2))).mp
        function.property (f1024Why24OddPhysicalRationalPlace r site).place
  rw [hD site] at hbound
  simpa [GlobalPlace.RegularAt] using hbound

private theorem why24Decoder_evaluateRegular_mul (r : Nat)
    (site : f1024Why24OddPhysicalSite r)
    (left right : F1024TowerLevel (2 * r + 2))
    (hleft : GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place left)
    (hright : GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place right)
    (hproduct : GlobalPlace.RegularAt
      (f1024Why24OddPhysicalRationalPlace r site).place (left * right)) :
    (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
        (left * right) hproduct =
      (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular left hleft *
        (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular right hright := by
  let xleft : GlobalPlace.valuationRing
      (f1024Why24OddPhysicalRationalPlace r site).place :=
    ⟨left, (GlobalPlace.mem_valuationRing_iff _ left).mpr hleft⟩
  let xright : GlobalPlace.valuationRing
      (f1024Why24OddPhysicalRationalPlace r site).place :=
    ⟨right, (GlobalPlace.mem_valuationRing_iff _ right).mpr hright⟩
  let xproduct : GlobalPlace.valuationRing
      (f1024Why24OddPhysicalRationalPlace r site).place :=
    ⟨left * right, (GlobalPlace.mem_valuationRing_iff _ _).mpr hproduct⟩
  change (f1024Why24OddPhysicalRationalPlace r site).evaluate xproduct =
    (f1024Why24OddPhysicalRationalPlace r site).evaluate xleft *
      (f1024Why24OddPhysicalRationalPlace r site).evaluate xright
  have hmul : xproduct = xleft * xright := by
    rfl
  rw [hmul]
  exact (f1024Why24OddPhysicalRationalPlace r site).evaluate.map_mul _ _

private theorem why24DecoderScaledEvaluation_mul_apply (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (row : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r))
    (site : f1024Why24OddPhysicalSite r) :
    why24DecoderScaledEvaluationLinearMap r
        (why24DecoderMultiplyIntoShortened r row locator) site =
      f1024Why24OddCoordinateWeight r site.1 *
        (agEvaluationLinearMap
            (f1024Why24OddDecoderAuxiliaryDivisor r)
            (f1024Why24OddPhysicalRationalPlace r)
            (f1024Why24OddDecoderAuxiliary_disjoint r) locator site *
          agEvaluationLinearMap
            (f1024Why24OddDecoderComplementDivisor r)
            (f1024Why24OddPhysicalRationalPlace r)
            (why24DecoderComplementDivisor_apply_physical r) row site) := by
  unfold why24DecoderScaledEvaluationLinearMap
  simp only [agEvaluationLinearMap_apply]
  change f1024Why24OddCoordinateWeight r site.1 *
      (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
        ((locator : F1024TowerLevel (2 * r + 2)) * row) _ =
    f1024Why24OddCoordinateWeight r site.1 *
      ((f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
          (locator : F1024TowerLevel (2 * r + 2)) _ *
        (f1024Why24OddPhysicalRationalPlace r site).evaluateRegular
          (row : F1024TowerLevel (2 * r + 2)) _)
  congr 1
  exact why24Decoder_evaluateRegular_mul r site
    (locator : F1024TowerLevel (2 * r + 2))
    (row : F1024TowerLevel (2 * r + 2))
    (why24Decoder_evaluationRegularityOfMem r
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site)
    (why24Decoder_evaluationRegularityOfMem r
      (f1024Why24OddDecoderComplementDivisor r)
      (why24DecoderComplementDivisor_apply_physical r) row site)
    (why24Decoder_evaluationRegularityOfMem r
      (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r)
      (why24DecoderShortenedDivisor_apply_physical r)
      (why24DecoderMultiplyIntoShortened r row locator) site)

/-- Evaluation of an auxiliary locator on the actual error support. -/
private noncomputable def why24DecoderAuxiliarySupportEvaluation (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r) →ₗ[F1024]
      ({site // site ∈ hammingSupport error} → F1024) where
  toFun locator site :=
    agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site.1
  map_add' left right := by
    funext site
    simp only [map_add, Pi.add_apply]
  map_smul' scalar locator := by
    funext site
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

private theorem why24DecoderAuxiliarySupportEvaluation_finrank (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r)) :
    Module.finrank F1024 ({site // site ∈ hammingSupport error} → F1024) =
      HammingWeight error := by
  rw [HammingWeight_eq_card_hammingSupport, Module.finrank_pi]
  simp

private theorem why24DecoderAuxiliarySupportEvaluation_kernel_ne_bot (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    LinearMap.ker (why24DecoderAuxiliarySupportEvaluation r error) ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  rw [why24DecoderAuxiliarySupportEvaluation_finrank]
  exact herror.trans_lt
    (f1024Why24OddDecoderAuxiliary_dimension_gt_radius r)

@[simp]
private theorem why24DecoderSyndromePairing_mk (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (codeword : (f1024Why24OddWeightedMatrix r).stabilizerCode.carrier) :
    why24DecoderSyndromePairing r (f1024Why24OddZSyndromeMap r error)
        codeword = wordPairing error codeword.1 := by
  change (why24DecoderRawSyndromePairing r error) codeword =
    wordPairing error codeword.1
  rfl

private theorem why24DecoderSupportLocator_mem_linearSystem_kernel (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ∈
      LinearMap.ker (why24DecoderAuxiliarySupportEvaluation r error)) :
    locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error)) := by
  rw [LinearMap.mem_ker] at hlocator ⊢
  funext equation
  simp only [f1024Why24OddDecoderLinearSystem, LinearMap.pi_apply,
    LinearMap.comp_apply, why24DecoderSyndromePairing_mk,
    wordPairing_apply]
  apply Finset.sum_eq_zero
  intro site _
  by_cases hsite : site ∈ hammingSupport error
  · have hzero := congrFun hlocator ⟨site, hsite⟩
    change agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 at hzero
    change error site * why24DecoderScaledEvaluationLinearMap r
      (why24DecoderMultiplyIntoShortened r
        (Module.finBasis F1024
          (GlobalPlace.riemannRochSubmodule
            (f1024Why24OddDecoderComplementDivisor r)) equation) locator) site = 0
    rw [why24DecoderScaledEvaluation_mul_apply]
    change error site *
      (f1024Why24OddCoordinateWeight r site.1 *
        (agEvaluationLinearMap
            (f1024Why24OddDecoderAuxiliaryDivisor r)
            (f1024Why24OddPhysicalRationalPlace r)
            (f1024Why24OddDecoderAuxiliary_disjoint r) locator site * _)) = 0
    rw [hzero]
    ring
  · have herrorZero : error site = 0 := by
      simpa [hammingSupport] using hsite
    rw [herrorZero, zero_mul]

private theorem why24DecoderLinearSystem_kernel_ne_bot_of_error (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    LinearMap.ker
        (f1024Why24OddDecoderLinearSystem r
          (f1024Why24OddZSyndromeMap r error)) ≠ ⊥ := by
  have hsupport : LinearMap.ker
      (why24DecoderAuxiliarySupportEvaluation r error) ≠ ⊥ :=
    why24DecoderAuxiliarySupportEvaluation_kernel_ne_bot r error herror
  have hle : LinearMap.ker
      (why24DecoderAuxiliarySupportEvaluation r error) ≤
        LinearMap.ker
          (f1024Why24OddDecoderLinearSystem r
            (f1024Why24OddZSyndromeMap r error)) := by
    intro locator hlocator
    exact why24DecoderSupportLocator_mem_linearSystem_kernel r error
      locator hlocator
  intro hbot
  rw [hbot] at hle
  apply hsupport
  exact le_antisymm hle bot_le

private theorem why24DecoderLinearSystem_kernel_finrank_pos_of_error (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    0 < Module.finrank F1024
      (LinearMap.ker
        (f1024Why24OddDecoderLinearSystem r
          (f1024Why24OddZSyndromeMap r error))) := by
  exact (Submodule.one_le_finrank_iff.mpr
    (why24DecoderLinearSystem_kernel_ne_bot_of_error r error herror))

/-- A deterministic finite-basis locator extracted from the actual
key-equation kernel.  The zero fallback makes the construction total on every
syndrome; radius syndromes prove that the first basis vector exists. -/
private noncomputable def why24DecoderLocator (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r) := by
  letI : Module.Free F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :=
    Module.Free.of_divisionRing F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
  exact if hdimension : 0 < Module.finrank F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) then
    (Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
      ⟨0, hdimension⟩ :
        LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)).1
  else 0

private theorem why24DecoderLocator_mem_kernel (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    why24DecoderLocator r syndrome ∈
      LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome) := by
  letI : Module.Free F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :=
    Module.Free.of_divisionRing F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
  unfold why24DecoderLocator
  split_ifs with hdimension
  · exact (Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
      ⟨0, hdimension⟩).2
  · exact (LinearMap.ker _).zero_mem

private theorem why24DecoderLocator_ne_zero_of_finrank_pos (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (hdimension : 0 < Module.finrank F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))) :
    why24DecoderLocator r syndrome ≠ 0 := by
  letI : Module.Free F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :=
    Module.Free.of_divisionRing F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
  rw [why24DecoderLocator, dif_pos hdimension]
  intro hzero
  have hbasis : Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))
      ⟨0, hdimension⟩ ≠ 0 :=
    (Module.finBasis F1024
      (LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome))).ne_zero
      ⟨0, hdimension⟩
  apply hbasis
  apply Subtype.ext
  exact hzero

private theorem why24DecoderLocator_ne_zero_of_error (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24DecoderLocator r (f1024Why24OddZSyndromeMap r error) ≠ 0 :=
  why24DecoderLocator_ne_zero_of_finrank_pos r _
    (why24DecoderLinearSystem_kernel_finrank_pos_of_error r error herror)

private noncomputable def why24DecoderComplementAGCode (r : Nat) :
    LinearCode F1024 (f1024Why24OddPhysicalSite r) :=
  agEvaluationCode
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderComplementDivisor_apply_physical r)

private theorem why24DecoderOddGenus_subtrahend_le (r : Nat) :
    34 * 32 ^ (r + 1) ≤ 33 * 32 ^ (2 * r + 2) := by
  let q := 32 ^ (r + 1)
  have hpower : 32 ≤ q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  change 34 * q ≤ 33 * 32 ^ (2 * r + 2)
  rw [hbig]
  have hmul : q * 32 ≤ q * q := Nat.mul_le_mul_left q hpower
  nlinarith

private theorem why24DecoderOddGenus_cast (r : Nat) :
    (oddGenus r : Int) =
      33 * (32 : Int) ^ (2 * r + 2) -
        34 * (32 : Int) ^ (r + 1) + 1 := by
  rw [oddGenus, Nat.cast_add,
    Nat.cast_sub (why24DecoderOddGenus_subtrahend_le r)]
  norm_num

private theorem why24DecoderOddGenus_lower_bound (r : Nat) :
    32705 ≤ oddGenus r := by
  let q : Int := (32 : Int) ^ (r + 1)
  have hqNat : 32 ≤ 32 ^ (r + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 32)
      (by omega : 1 ≤ r + 1)
    norm_num at h ⊢
    exact h
  have hq : (32 : Int) ≤ q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hpower : (32 : Int) ^ (2 * r + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
  have hcast := why24DecoderOddGenus_cast r
  have hbound : (32705 : Int) ≤ (oddGenus r : Int) := by
    rw [hcast, hpower]
    nlinarith
  exact_mod_cast hbound

private theorem why24DecoderOddGenus_mod_eight (r : Nat) :
    oddGenus r % 8 = 1 := by
  have hlarge := why24DecoderOddGenus_subtrahend_le r
  have hhigh : 32 ^ (2 * r + 2) % 8 = 0 := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ]
    omega
  have hlow : 32 ^ (r + 1) % 8 = 0 := by
    rw [pow_succ]
    omega
  unfold oddGenus
  omega

private theorem why24DecoderPhysicalRationalPlace_injective (r : Nat) :
    Function.Injective
      (fun site => (f1024Why24OddPhysicalRationalPlace r site).place) := by
  intro left right heq
  apply Subtype.ext
  exact f1024Why24OddRetainedRationalPlace_injective r heq

private theorem why24DecoderComplementDivisor_degree (r : Nat) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderComplementDivisor r) =
      (selectedDivisorDegree (oddGenus r) : Int) -
        selectedLogicalCount (oddGenus r) -
          selectedAuxiliaryDegree (oddGenus r) := by
  rw [f1024Why24OddDecoderComplementDivisor,
    Divisor.degree_sub, Divisor.degree_sub,
    f1024Why24OddADivisor_degree,
    f1024Why24OddPivotDivisor_degree,
    f1024Why24OddDecoderAuxiliaryDivisor_degree]

private theorem why24DecoderComplementDivisor_largeDegree (r : Nat) :
    2 * (GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : Int) - 1 ≤
      Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderComplementDivisor r) := by
  rw [f1024TowerLevel_functionFieldGenus_even,
    why24DecoderComplementDivisor_degree]
  have hmod := why24DecoderOddGenus_mod_eight r
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedAuxiliaryDegree]
  omega

private theorem why24DecoderComplementDivisor_degree_lt_physicalCard
    (r : Nat) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderComplementDivisor r) <
      Fintype.card (f1024Why24OddPhysicalSite r) := by
  rw [why24DecoderComplementDivisor_degree]
  have hlower := (f1024Why24OddLength_bounds r).1
  rw [f1024Why24OddLength] at hlower
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedAuxiliaryDegree, selectedPhysicalLengthLowerBound] at hlower ⊢
  omega

private theorem why24DecoderComplementDesignedDistance (r : Nat) :
    Int.toNat
        (((selectedDivisorDegree (oddGenus r) : Int) -
              selectedLogicalCount (oddGenus r) -
                selectedAuxiliaryDegree (oddGenus r)) + 2 -
          2 * (oddGenus r : Int)) =
      selectedDecodingRadius (oddGenus r) + 2 := by
  have hmod := why24DecoderOddGenus_mod_eight r
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedDivisorDegree, selectedLogicalCount,
    selectedAuxiliaryDegree, selectedDecodingRadius]
  omega

private theorem why24DecoderComplementAGCode_dual_distance_lower_bound
    (r : Nat) :
    (f1024Why24OddDecodingRadius r + 2 : WithTop Nat) ≤
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
        (why24DecoderComplementAGCode r).dual := by
  have h := agEvaluation_dual_distance_lower_bound
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderPhysicalRationalPlace_injective r)
    (why24DecoderComplementDivisor_apply_physical r)
    (why24DecoderComplementDivisor_largeDegree r)
    (why24DecoderComplementDivisor_degree_lt_physicalCard r)
  change (Int.toNat
      (Divisor.degree (GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
          (f1024Why24OddDecoderComplementDivisor r) + 2 -
        2 * (GlobalPlace.functionFieldGenus F1024
          (F1024TowerLevel (2 * r + 2)) : Int)) : WithTop Nat) ≤
    QEC.Coding.HypergraphProduct.extendedMinimumDistance
      (why24DecoderComplementAGCode r).dual at h
  rw [why24DecoderComplementDivisor_degree,
    f1024TowerLevel_functionFieldGenus_even,
    why24DecoderComplementDesignedDistance] at h
  simpa [f1024Why24OddDecodingRadius] using h

private noncomputable def why24DecoderMultiplyLocatorIntoShortened (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r) →ₗ[F1024]
      GlobalPlace.riemannRochSubmodule
        (f1024Why24OddADivisor r - f1024Why24OddPivotDivisor r) where
  toFun row := why24DecoderMultiplyIntoShortened r row locator
  map_add' left right := by
    apply Subtype.ext
    change (locator : F1024TowerLevel (2 * r + 2)) *
        ((left : F1024TowerLevel (2 * r + 2)) + right) =
      (locator : F1024TowerLevel (2 * r + 2)) * left +
        (locator : F1024TowerLevel (2 * r + 2)) * right
    rw [mul_add]
  map_smul' scalar row := by
    apply Subtype.ext
    change (locator : F1024TowerLevel (2 * r + 2)) *
        (algebraMap F1024 (F1024TowerLevel (2 * r + 2)) scalar * row) =
      algebraMap F1024 (F1024TowerLevel (2 * r + 2)) scalar *
        ((locator : F1024TowerLevel (2 * r + 2)) * row)
    ring

private noncomputable def why24DecoderLocatorEquationFunctional (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r) →ₗ[F1024] F1024 :=
  (why24DecoderSyndromePairing r syndrome).comp
    ((why24DecoderScaledEvaluationToStabilizer r).comp
      (why24DecoderMultiplyLocatorIntoShortened r locator))

private theorem why24DecoderLocatorEquationFunctional_eq_zero (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ∈
      LinearMap.ker (f1024Why24OddDecoderLinearSystem r syndrome)) :
    why24DecoderLocatorEquationFunctional r syndrome locator = 0 := by
  rw [LinearMap.mem_ker] at hlocator
  apply (Module.finBasis F1024
    (GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderComplementDivisor r))).ext
  intro equation
  have hcoordinate := congrFun hlocator equation
  simp only [why24DecoderLocatorEquationFunctional,
    why24DecoderMultiplyLocatorIntoShortened,
    f1024Why24OddDecoderLinearSystem, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.zero_apply] at hcoordinate ⊢
  exact hcoordinate

private noncomputable def why24DecoderLocatorProductWord (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    Word F1024 (f1024Why24OddPhysicalSite r) := fun site =>
  error site *
    (f1024Why24OddCoordinateWeight r site.1 *
      agEvaluationLinearMap
        (f1024Why24OddDecoderAuxiliaryDivisor r)
        (f1024Why24OddPhysicalRationalPlace r)
        (f1024Why24OddDecoderAuxiliary_disjoint r) locator site)

private theorem why24DecoderLocatorProductWord_mem_complementDual (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error))) :
    why24DecoderLocatorProductWord r error locator ∈
      (why24DecoderComplementAGCode r).dual.carrier := by
  rw [LinearCode.mem_dual]
  intro word hword
  change word ∈ (agEvaluationLinearMap
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderComplementDivisor_apply_physical r)).range at hword
  rcases hword with ⟨row, rfl⟩
  have hfunctional := LinearMap.congr_fun
    (why24DecoderLocatorEquationFunctional_eq_zero r
      (f1024Why24OddZSyndromeMap r error) locator hlocator) row
  rw [LinearMap.zero_apply] at hfunctional
  change why24DecoderSyndromePairing r
      (f1024Why24OddZSyndromeMap r error)
      (why24DecoderScaledEvaluationToStabilizer r
        (why24DecoderMultiplyIntoShortened r row locator)) = 0 at hfunctional
  rw [why24DecoderSyndromePairing_mk, wordPairing_apply] at hfunctional
  rw [wordPairing_apply]
  calc
    ∑ site, why24DecoderLocatorProductWord r error locator site *
        agEvaluationLinearMap
          (f1024Why24OddDecoderComplementDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (why24DecoderComplementDivisor_apply_physical r) row site =
      ∑ site, error site *
        why24DecoderScaledEvaluationLinearMap r
          (why24DecoderMultiplyIntoShortened r row locator) site := by
            apply Finset.sum_congr rfl
            intro site _
            rw [why24DecoderScaledEvaluation_mul_apply]
            simp only [why24DecoderLocatorProductWord]
            ring
    _ = 0 := hfunctional

private theorem why24DecoderLocatorProductWord_hammingWeight_le (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    HammingWeight (why24DecoderLocatorProductWord r error locator) ≤
      HammingWeight error := by
  rw [HammingWeight_eq_card_hammingSupport,
    HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro site hsite
  have hproduct : why24DecoderLocatorProductWord r error locator site ≠ 0 :=
    (Finset.mem_filter.mp hsite).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ site, ?_⟩
  intro hzero
  apply hproduct
  change error site * _ = 0
  exact mul_eq_zero.mpr (Or.inl hzero)

private theorem why24DecoderLocatorProductWord_eq_zero (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r)
    (hlocator : locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error))) :
    why24DecoderLocatorProductWord r error locator = 0 := by
  classical
  by_contra hnonzero
  have hminimum :
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (why24DecoderComplementAGCode r).dual ≤
        (HammingWeight
          (why24DecoderLocatorProductWord r error locator) : WithTop Nat) := by
    rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
      ⟨why24DecoderLocatorProductWord_mem_complementDual r error locator
        hlocator, hnonzero⟩
  have hlower : f1024Why24OddDecodingRadius r + 2 ≤
      HammingWeight (why24DecoderLocatorProductWord r error locator) := by
    exact_mod_cast
      (why24DecoderComplementAGCode_dual_distance_lower_bound r |>.trans
        hminimum)
  have hupper : HammingWeight
      (why24DecoderLocatorProductWord r error locator) ≤
        f1024Why24OddDecodingRadius r :=
    (why24DecoderLocatorProductWord_hammingWeight_le r error locator).trans
      herror
  omega

private theorem why24DecoderLocatorEvaluation_zero_on_errorSupport (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r)
    (hlocator : locator ∈ LinearMap.ker
      (f1024Why24OddDecoderLinearSystem r
        (f1024Why24OddZSyndromeMap r error)))
    (site : f1024Why24OddPhysicalSite r)
    (hsite : site ∈ hammingSupport error) :
    agEvaluationLinearMap
        (f1024Why24OddDecoderAuxiliaryDivisor r)
        (f1024Why24OddPhysicalRationalPlace r)
        (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 := by
  have hproduct := congrFun
    (why24DecoderLocatorProductWord_eq_zero r error locator herror hlocator)
    site
  change error site *
      (f1024Why24OddCoordinateWeight r site.1 *
        agEvaluationLinearMap
          (f1024Why24OddDecoderAuxiliaryDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddDecoderAuxiliary_disjoint r) locator site) = 0 at hproduct
  have herror_ne : error site ≠ 0 := by
    simpa [hammingSupport] using hsite
  have hweight_ne := f1024Why24OddCoordinateWeight_ne_zero r site.1
  rcases mul_eq_zero.mp hproduct with hzero | hzero
  · exact False.elim (herror_ne hzero)
  · rcases mul_eq_zero.mp hzero with hzero | hzero
    · exact False.elim (hweight_ne hzero)
    · exact hzero

private theorem why24DecoderSelectedLocator_zero_on_errorSupport (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r)
    (site : f1024Why24OddPhysicalSite r)
    (hsite : site ∈ hammingSupport error) :
    agEvaluationLinearMap
        (f1024Why24OddDecoderAuxiliaryDivisor r)
        (f1024Why24OddPhysicalRationalPlace r)
        (f1024Why24OddDecoderAuxiliary_disjoint r)
        (why24DecoderLocator r (f1024Why24OddZSyndromeMap r error)) site = 0 :=
  why24DecoderLocatorEvaluation_zero_on_errorSupport r error _ herror
    (why24DecoderLocator_mem_kernel r
      (f1024Why24OddZSyndromeMap r error)) site hsite

private noncomputable def why24DecoderLocatorZeroSet (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    Finset (f1024Why24OddPhysicalSite r) :=
  Finset.univ.filter fun site =>
    agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0

private theorem why24DecoderLocatorZeroSet_card_le (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (hlocator : locator ≠ 0) :
    (why24DecoderLocatorZeroSet r locator).card ≤
      selectedAuxiliaryDegree (oddGenus r) := by
  let zeroSet := why24DecoderLocatorZeroSet r locator
  have hzeroOn : forall site, site ∈ zeroSet →
      agEvaluationLinearMap
        (f1024Why24OddDecoderAuxiliaryDivisor r)
        (f1024Why24OddPhysicalRationalPlace r)
        (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 := by
    intro site hsite
    exact (Finset.mem_filter.mp hsite).2
  have hmem : (locator : F1024TowerLevel (2 * r + 2)) ∈
      GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r -
          zeroCoordinateDivisor
            (f1024Why24OddPhysicalRationalPlace r) zeroSet) :=
    evaluationZeroOn_mem_riemannRochSubmodule_sub
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (why24DecoderPhysicalRationalPlace_injective r)
      (f1024Why24OddDecoderAuxiliary_disjoint r)
      zeroSet locator hzeroOn
  have hnotNegative : ¬ Divisor.degree
      (GlobalPlace.residueDegree
        (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
      (f1024Why24OddDecoderAuxiliaryDivisor r -
        zeroCoordinateDivisor
          (f1024Why24OddPhysicalRationalPlace r) zeroSet) < 0 := by
    intro hnegative
    have hbot := GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
      F1024 (F1024TowerLevel (2 * r + 2))
      (f1024Why24OddDecoderAuxiliaryDivisor r -
        zeroCoordinateDivisor
          (f1024Why24OddPhysicalRationalPlace r) zeroSet) hnegative
    have hfunctionZero :
        (locator : F1024TowerLevel (2 * r + 2)) = 0 := by
      have hmemBot : (locator : F1024TowerLevel (2 * r + 2)) ∈
          (⊥ : Submodule F1024 (F1024TowerLevel (2 * r + 2))) := by
        rw [← hbot]
        exact hmem
      exact (Submodule.mem_bot F1024).mp hmemBot
    apply hlocator
    apply Subtype.ext
    exact hfunctionZero
  rw [Divisor.degree_sub, f1024Why24OddDecoderAuxiliaryDivisor_degree,
    zeroCoordinateDivisor_degree_eq_card] at hnotNegative
  exact_mod_cast (show (zeroSet.card : Int) ≤
      selectedAuxiliaryDegree (oddGenus r) by omega)

private noncomputable def why24DecoderLocatorProductLinearMap (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r)) :
    Word F1024 (f1024Why24OddPhysicalSite r) →ₗ[F1024]
      Word F1024 (f1024Why24OddPhysicalSite r) where
  toFun error := why24DecoderLocatorProductWord r error locator
  map_add' left right := by
    funext site
    simp only [why24DecoderLocatorProductWord, Pi.add_apply]
    ring
  map_smul' scalar error := by
    funext site
    simp only [why24DecoderLocatorProductWord, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    ring

private noncomputable def why24DecoderRecoverySyndromeMap (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) →ₗ[F1024]
      f1024Why24OddZSyndrome r :=
  ((f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier.mkQ).comp
    (LinearMap.ker (why24DecoderLocatorProductLinearMap r
      (why24DecoderLocator r syndrome))).subtype

private noncomputable def why24DecoderRecoveryCoordinates (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) →ₗ[F1024]
      (Fin (Module.finrank F1024
        (LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome))) →
          F1024) := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  exact (Module.finBasis F1024 (LinearMap.range recovery)).equivFun.toLinearMap.comp
    recovery.rangeRestrict

private theorem why24DecoderRecoveryCoordinates_surjective (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    Function.Surjective (why24DecoderRecoveryCoordinates r syndrome) := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  exact (Module.finBasis F1024
    (LinearMap.range recovery)).equivFun.surjective.comp
      recovery.surjective_rangeRestrict

private noncomputable def why24DecoderRecoveryRangeSection (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome) →ₗ[F1024]
      LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  exact (LinearMap.splittingOfFunOnFintypeSurjective
      (why24DecoderRecoveryCoordinates r syndrome)
      (why24DecoderRecoveryCoordinates_surjective r syndrome)).comp
    (Module.finBasis F1024 (LinearMap.range recovery)).equivFun.toLinearMap

private theorem why24DecoderRecoveryRangeSection_rightInverse (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (value : LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    why24DecoderRecoverySyndromeMap r syndrome
        (why24DecoderRecoveryRangeSection r syndrome value) = value.1 := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  let basis := Module.finBasis F1024 (LinearMap.range recovery)
  have hcoordinates := LinearMap.leftInverse_splittingOfFunOnFintypeSurjective
    (why24DecoderRecoveryCoordinates r syndrome)
    (why24DecoderRecoveryCoordinates_surjective r syndrome)
    (basis.equivFun value)
  have hrange : recovery.rangeRestrict
      (why24DecoderRecoveryRangeSection r syndrome value) = value := by
    apply basis.equivFun.injective
    exact hcoordinates
  exact congrArg Subtype.val hrange

private theorem why24DecoderError_mem_selectedRecoveryKernel (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    error ∈ LinearMap.ker
      (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r (f1024Why24OddZSyndromeMap r error))) := by
  rw [LinearMap.mem_ker]
  exact why24DecoderLocatorProductWord_eq_zero r error _ herror
    (why24DecoderLocator_mem_kernel r
      (f1024Why24OddZSyndromeMap r error))

private theorem why24DecoderRecoveryKernel_hammingWeight_le_zeroSet (r : Nat)
    (locator : GlobalPlace.riemannRochSubmodule
      (f1024Why24OddDecoderAuxiliaryDivisor r))
    (word : Word F1024 (f1024Why24OddPhysicalSite r))
    (hword : word ∈ LinearMap.ker
      (why24DecoderLocatorProductLinearMap r locator)) :
    HammingWeight word ≤ (why24DecoderLocatorZeroSet r locator).card := by
  rw [HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card
  intro site hsite
  have hword_ne : word site ≠ 0 := by
    simpa [hammingSupport] using hsite
  have hproduct := congrFun (LinearMap.mem_ker.mp hword) site
  change word site *
      (f1024Why24OddCoordinateWeight r site.1 *
        agEvaluationLinearMap
          (f1024Why24OddDecoderAuxiliaryDivisor r)
          (f1024Why24OddPhysicalRationalPlace r)
          (f1024Why24OddDecoderAuxiliary_disjoint r) locator site) = 0 at hproduct
  have hevaluation : agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0 := by
    rcases mul_eq_zero.mp hproduct with hzero | hzero
    · exact False.elim (hword_ne hzero)
    · rcases mul_eq_zero.mp hzero with hzero | hzero
      · exact False.elim
          (f1024Why24OddCoordinateWeight_ne_zero r site.1 hzero)
      · exact hzero
  rw [why24DecoderLocatorZeroSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ site, ?_⟩
  change agEvaluationLinearMap
    (f1024Why24OddDecoderAuxiliaryDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (f1024Why24OddDecoderAuxiliary_disjoint r) locator site = 0
  exact hevaluation

/-- The finite AG key-equation decoder.  It first extracts a nonzero locator
from the explicit key-equation matrix, then uses a basis-coordinate Gaussian
section of the locator-constrained syndrome map.  If an arbitrary syndrome is
outside that constrained range it returns the zero word, so the decoder is a
total function on every syndrome. -/
noncomputable def f1024Why24OddAGDualDecoder (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    Word F1024 (f1024Why24OddPhysicalSite r) := by
  classical
  exact if hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome) then
    (why24DecoderRecoveryRangeSection r syndrome ⟨syndrome, hmem⟩).1
  else 0

/-- The decoder always returns a physical word.  On the solvable branch that
word is the literal constrained linear-system solution with the requested
intrinsic syndrome; otherwise the total fallback is zero. -/
theorem f1024Why24OddAGDualDecoder_alwaysReturns (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (∃ recovered : LinearMap.ker
        (why24DecoderLocatorProductLinearMap r
          (why24DecoderLocator r syndrome)),
      f1024Why24OddAGDualDecoder r syndrome = recovered.1 ∧
        f1024Why24OddZSyndromeMap r recovered.1 = syndrome) ∨
      (syndrome ∉ LinearMap.range
        (why24DecoderRecoverySyndromeMap r syndrome) ∧
        f1024Why24OddAGDualDecoder r syndrome = 0) := by
  classical
  by_cases hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)
  · left
    let recovered := why24DecoderRecoveryRangeSection r syndrome
      ⟨syndrome, hmem⟩
    refine ⟨recovered, ?_, ?_⟩
    · rw [f1024Why24OddAGDualDecoder, dif_pos hmem]
    · have hright := why24DecoderRecoveryRangeSection_rightInverse r
        syndrome ⟨syndrome, hmem⟩
      exact hright
  · right
    refine ⟨hmem, ?_⟩
    rw [f1024Why24OddAGDualDecoder, dif_neg hmem]

private theorem why24DecoderError_syndrome_mem_recoveryRange (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    f1024Why24OddZSyndromeMap r error ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r
        (f1024Why24OddZSyndromeMap r error)) := by
  let supported : LinearMap.ker
      (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r (f1024Why24OddZSyndromeMap r error))) :=
    ⟨error, why24DecoderError_mem_selectedRecoveryKernel r error herror⟩
  exact ⟨supported, rfl⟩

private theorem why24Decoder_syndrome_eq_of_mem_recoveryRange (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    f1024Why24OddZSyndromeMap r
        (f1024Why24OddAGDualDecoder r syndrome) = syndrome := by
  classical
  rw [f1024Why24OddAGDualDecoder, dif_pos hmem]
  exact why24DecoderRecoveryRangeSection_rightInverse r syndrome
    ⟨syndrome, hmem⟩

private theorem why24Decoder_mem_recoveryKernel_of_mem_range (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    f1024Why24OddAGDualDecoder r syndrome ∈
      LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) := by
  classical
  rw [f1024Why24OddAGDualDecoder, dif_pos hmem]
  exact (why24DecoderRecoveryRangeSection r syndrome
    ⟨syndrome, hmem⟩).2

private theorem why24DecoderSelectedAuxiliary_add_radius_lt_distance
    (r : Nat) :
    selectedAuxiliaryDegree (oddGenus r) +
        f1024Why24OddDecodingRadius r <
      selectedDistanceLowerBound (oddGenus r) := by
  have hmod := why24DecoderOddGenus_mod_eight r
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [f1024Why24OddDecodingRadius, selectedAuxiliaryDegree,
    selectedDecodingRadius, selectedDistanceLowerBound,
    selectedDivisorDegree, selectedLogicalCount]
  omega

private theorem why24DecoderHammingWeight_neg (r : Nat)
    (word : Word F1024 (f1024Why24OddPhysicalSite r)) :
    HammingWeight (-word) = HammingWeight word := by
  unfold HammingWeight hammingSupport
  congr 1
  ext site
  simp

/-- Every error in the source radius ball is recovered exactly by the actual
finite key-equation decoder. -/
theorem f1024Why24OddAGDualDecoder_correct (r : Nat)
    (error : Word F1024 (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    f1024Why24OddAGDualDecoder r
      (f1024Why24OddZSyndromeMap r error) = error := by
  classical
  let syndrome := f1024Why24OddZSyndromeMap r error
  let decoded := f1024Why24OddAGDualDecoder r syndrome
  have hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome) :=
    why24DecoderError_syndrome_mem_recoveryRange r error herror
  have hdecodedKernel : decoded ∈
      LinearMap.ker (why24DecoderLocatorProductLinearMap r
        (why24DecoderLocator r syndrome)) :=
    why24Decoder_mem_recoveryKernel_of_mem_range r syndrome hmem
  have hlocator_ne : why24DecoderLocator r syndrome ≠ 0 :=
    why24DecoderLocator_ne_zero_of_error r error herror
  have hdecodedWeight : HammingWeight decoded ≤
      selectedAuxiliaryDegree (oddGenus r) :=
    (why24DecoderRecoveryKernel_hammingWeight_le_zeroSet r
      (why24DecoderLocator r syndrome) decoded hdecodedKernel).trans
        (why24DecoderLocatorZeroSet_card_le r _ hlocator_ne)
  have hsyndrome : f1024Why24OddZSyndromeMap r decoded =
      f1024Why24OddZSyndromeMap r error :=
    why24Decoder_syndrome_eq_of_mem_recoveryRange r syndrome hmem
  by_contra hne
  have hdifference_mem : decoded - error ∈
      (f1024Why24OddWeightedMatrix r).stabilizerCode.dual.carrier := by
    change Submodule.Quotient.mk decoded = Submodule.Quotient.mk error at hsyndrome
    rwa [Submodule.Quotient.eq] at hsyndrome
  have hdifference_ne : decoded - error ≠ 0 := sub_ne_zero.mpr hne
  have hminimum :
      QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (f1024Why24OddWeightedMatrix r).stabilizerCode.dual ≤
        (HammingWeight (decoded - error) : WithTop Nat) := by
    rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
    exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
      ⟨hdifference_mem, hdifference_ne⟩
  have hlower : selectedDistanceLowerBound (oddGenus r) ≤
      HammingWeight (decoded - error) := by
    exact_mod_cast
      (f1024Why24OddStabilizerCode_dual_distance_lower_bound r |>.trans
        hminimum)
  have hupper : HammingWeight (decoded - error) ≤
      selectedAuxiliaryDegree (oddGenus r) +
        f1024Why24OddDecodingRadius r := by
    calc
      HammingWeight (decoded - error) =
          HammingWeight (decoded + -error) := by rw [sub_eq_add_neg]
      _ ≤ HammingWeight decoded + HammingWeight (-error) :=
        HammingWeight_add_le decoded (-error)
      _ = HammingWeight decoded + HammingWeight error := by
        rw [why24DecoderHammingWeight_neg]
      _ ≤ selectedAuxiliaryDegree (oddGenus r) +
          f1024Why24OddDecodingRadius r := Nat.add_le_add hdecodedWeight herror
  exact (not_lt_of_ge hlower)
    (hupper.trans_lt
      (why24DecoderSelectedAuxiliary_add_radius_lt_distance r))

private theorem why24DecoderAuxiliaryDivisor_degree_lt_physicalCard
    (r : Nat) :
    Divisor.degree
        (GlobalPlace.residueDegree
          (k := F1024) (F := F1024TowerLevel (2 * r + 2)))
        (f1024Why24OddDecoderAuxiliaryDivisor r) <
      Fintype.card (f1024Why24OddPhysicalSite r) := by
  rw [f1024Why24OddDecoderAuxiliaryDivisor_degree]
  have hlower := (f1024Why24OddLength_bounds r).1
  rw [f1024Why24OddLength] at hlower
  have hlarge := why24DecoderOddGenus_lower_bound r
  simp only [selectedAuxiliaryDegree,
    selectedPhysicalLengthLowerBound] at hlower ⊢
  omega

private theorem why24DecoderAuxiliary_finrank_le_length (r : Nat) :
    Module.finrank F1024
        (GlobalPlace.riemannRochSubmodule
          (f1024Why24OddDecoderAuxiliaryDivisor r)) ≤
      f1024Why24OddLength r := by
  have hinjective := agEvaluation_injective
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddDecoderAuxiliaryDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderPhysicalRationalPlace_injective r)
    (f1024Why24OddDecoderAuxiliary_disjoint r)
    (why24DecoderAuxiliaryDivisor_degree_lt_physicalCard r)
  have hfinrank :=
    (agEvaluationLinearMap
      (f1024Why24OddDecoderAuxiliaryDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (f1024Why24OddDecoderAuxiliary_disjoint r)).finrank_le_finrank_of_injective
        hinjective
  rw [Module.finrank_pi] at hfinrank
  simpa only [f1024Why24OddLength] using hfinrank

private theorem why24DecoderComplement_finrank_le_length (r : Nat) :
    Module.finrank F1024
        (GlobalPlace.riemannRochSubmodule
          (f1024Why24OddDecoderComplementDivisor r)) ≤
      f1024Why24OddLength r := by
  have hinjective := agEvaluation_injective
    (k := F1024) (F := F1024TowerLevel (2 * r + 2))
    (f1024Why24OddDecoderComplementDivisor r)
    (f1024Why24OddPhysicalRationalPlace r)
    (why24DecoderPhysicalRationalPlace_injective r)
    (why24DecoderComplementDivisor_apply_physical r)
    (why24DecoderComplementDivisor_degree_lt_physicalCard r)
  have hfinrank :=
    (agEvaluationLinearMap
      (f1024Why24OddDecoderComplementDivisor r)
      (f1024Why24OddPhysicalRationalPlace r)
      (why24DecoderComplementDivisor_apply_physical r)).finrank_le_finrank_of_injective
        hinjective
  rw [Module.finrank_pi] at hfinrank
  simpa only [f1024Why24OddLength] using hfinrank

/-- Field-operation count of the two finite Gaussian eliminations: locator
columns, key-equation rows, and recovery coordinates are all included in one
cubic matrix dimension. -/
def f1024Why24OddAGDualDecoderArithmeticCost (r : Nat) : Nat :=
  (f1024Why24OddLength r +
    Module.finrank F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderAuxiliaryDivisor r)) +
    Module.finrank F1024
      (GlobalPlace.riemannRochSubmodule
        (f1024Why24OddDecoderComplementDivisor r))) ^ 3

/-- The literal matrix-operation count is cubic in the actual physical block
length. -/
theorem f1024Why24OddAGDualDecoderArithmeticCost_le_cubic (r : Nat) :
    f1024Why24OddAGDualDecoderArithmeticCost r ≤
      (3 * f1024Why24OddLength r) ^ 3 := by
  unfold f1024Why24OddAGDualDecoderArithmeticCost
  apply pow_le_pow_left'
  have haux := why24DecoderAuxiliary_finrank_le_length r
  have hcomp := why24DecoderComplement_finrank_le_length r
  omega

/-! ## Literal Appendix-A resource conversions -/

/-- A Kraus sandwich sends a pure matrix unit to the matrix unit of the
operator images. -/
private theorem why24LinearMap_comp_rankOne_comp_adjoint
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (x y : H) :
    L.comp ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L x) (L y)).toLinearMap := by
  ext z
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

private theorem why24RankOne_smul_self
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (scalar : Complex) (psi : H) :
    (InnerProductSpace.rankOne Complex (scalar • psi)
        (scalar • psi)).toLinearMap =
      (star scalar * scalar) •
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  simp [InnerProductSpace.rankOne_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The literal Appendix gate list is an inner-product-preserving circuit. -/
private theorem why24AppendixCircuit_isUnitary :
    Why24IsUnitary why24AppendixCircuit := by
  intro left right
  have hport := (why24QuditQubitUnitary_conj_isUnitary_iff why24UOneSeven).2
    (why24U_isUnitary (1 : F1024) 7) left right
  simp only [why24AppendixCircuit_apply_eq_why24QubitUOneSeven] at hport ⊢
  exact hport

/-- The one-outcome ideal Appendix-A circuit instrument.  Its sole Kraus
operator is the literal registered `why24AppendixGateList` circuit. -/
noncomputable def why24AppendixCircuitInstrument :
    FiniteInstrument PUnit PUnit Why24QubitSpace Why24QubitSpace where
  kraus :=
    { operator := fun _ => why24AppendixCircuit }
  observe := id

/-- The literal ideal Appendix circuit is a complete one-outcome instrument. -/
theorem why24AppendixCircuitInstrument_complete :
    why24AppendixCircuitInstrument.kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [Fintype.sum_unique, why24AppendixCircuitInstrument]
  apply LinearMap.ext
  intro x
  apply ext_inner_right Complex
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  exact why24AppendixCircuit_isUnitary x y

private theorem why24QubitPlusState_normSq :
    ‖why24QubitPlusState‖ ^ 2 = 1 := by
  rw [why24QubitPlusState_norm]
  norm_num

private theorem why24UOneSevenQubitResource_normSq :
    ‖why24UOneSevenQubitResource‖ ^ 2 = 1 := by
  rw [why24UOneSevenQubitResource_norm]
  norm_num

/-- The normalized ten-qubit plus input to the forward conversion. -/
noncomputable def why24QubitPlusStateDensity :
    DensityOperator Why24QubitSpace :=
  DensityOperator.pureDensity why24QubitPlusState
    why24QubitPlusState_normSq

/-- The normalized ten-qubit `U_1^(7)` resource prepared by the literal
Appendix circuit. -/
noncomputable def why24UOneSevenQubitResourceDensity :
    DensityOperator Why24QubitSpace :=
  DensityOperator.pureDensity why24UOneSevenQubitResource
    why24UOneSevenQubitResource_normSq

/-- The ideal Appendix circuit prepares exactly the concrete `U_1^(7)`
resource on the source plus input. -/
theorem why24AppendixCircuit_ideal :
    (why24AppendixCircuitInstrument.kraus.toQuantumChannel
      why24AppendixCircuitInstrument_complete).mapDensity
        why24QubitPlusStateDensity =
      why24UOneSevenQubitResourceDensity := by
  apply DensityOperator.ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp only [Fintype.sum_unique, why24AppendixCircuitInstrument,
    why24QubitPlusStateDensity, why24UOneSevenQubitResourceDensity,
    DensityOperator.pureDensity_toOperator]
  rw [why24LinearMap_comp_rankOne_comp_adjoint,
    why24AppendixForwardPreparation]

/-! ### Actual seventy-CCZ forward conversion -/

/-- Relabel binary `ZMod 2` register words by their concrete qubit bits. -/
private def why24BinaryRegisterLabelEquiv (Site : Type)
    [Fintype Site] :
    PrimeQuditRegisterLabel 2 Site ≃ Qubit.Bitstring Site where
  toFun label site := (ZMod.finEquiv 2).symm (label site)
  invFun bits site := ZMod.finEquiv 2 (bits site)
  left_inv label := by
    funext site
    exact (ZMod.finEquiv 2).apply_symm_apply (label site)
  right_inv bits := by
    funext site
    exact (ZMod.finEquiv 2).symm_apply_apply (bits site)

/-- The basis-preserving unitary between binary prime-register words and
ordinary qubit-register labels. -/
private noncomputable def why24BinaryRegisterTransport (Site : Type)
    [Fintype Site] [DecidableEq Site] :
    UnitaryTransport (PrimeQuditRegister 2 Site) (Qubit.QubitRegister Site) := by
  let sourceBasis := EuclideanSpace.basisFun
    (PrimeQuditRegisterLabel 2 Site) Complex
  let targetBasis := EuclideanSpace.basisFun (Qubit.Bitstring Site) Complex
  let U := sourceBasis.equiv targetBasis (why24BinaryRegisterLabelEquiv Site)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The seventy literal cubic triples have their source-recorded cardinality. -/
private theorem why24CubicGateTriples_length :
    QEC.Coding.Why24AppendixANF.cubicGateTriples.length = 70 := by
  decide

/-- The literal Appendix cubic triple at one of the seventy resource slots. -/
private def why24AppendixCCZGateAt (gate : Fin 70) :
    Fin 10 × Fin 10 × Fin 10 :=
  QEC.Coding.Why24AppendixANF.cubicGateTriples.get
    ⟨gate.1, by simpa [why24CubicGateTriples_length] using gate.2⟩

/-- Binary data-qubit `Z` word contributed by one measured CCZ error word at
one literal Appendix cubic gate. -/
private def why24AppendixCCZErrorContribution (gate : Fin 70)
    (error : Qubit.Bitstring (Fin 3)) : PrimeQuditRegisterLabel 2 (Fin 10) :=
  fun site =>
    (if (why24AppendixCCZGateAt gate).1 = site then
        ZMod.finEquiv 2 (error 0) else 0) +
      (if (why24AppendixCCZGateAt gate).2.1 = site then
        ZMod.finEquiv 2 (error 1) else 0) +
      (if (why24AppendixCCZGateAt gate).2.2 = site then
        ZMod.finEquiv 2 (error 2) else 0)

/-- The corrected ten-qubit `Z` word produced by the literal seventy CCZ
teleportation branches. -/
def why24CCZToUOneSevenErrorWord
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) : Qubit.Bitstring (Fin 10) :=
  (why24BinaryRegisterLabelEquiv (Fin 10))
    (∑ gate : Fin 70,
      why24AppendixCCZErrorContribution gate (error gate))

/-- The output state after applying the measured/corrected Appendix error word
to the concrete ideal `U_1^(7)` resource. -/
private noncomputable def why24CCZToUOneSevenErrorKet
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) : Why24QubitSpace :=
  why24BinaryRegisterTransport (Fin 10)
    (zWordTransport 2
      ((why24BinaryRegisterLabelEquiv (Fin 10)).symm
        (why24CCZToUOneSevenErrorWord error))
      ((why24BinaryRegisterTransport (Fin 10)).symm
        why24UOneSevenQubitResource))

private theorem why24CCZToUOneSevenErrorKet_norm
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) :
    ‖why24CCZToUOneSevenErrorKet error‖ = 1 := by
  rw [why24CCZToUOneSevenErrorKet]
  calc
    ‖why24BinaryRegisterTransport (Fin 10)
        (zWordTransport 2
          ((why24BinaryRegisterLabelEquiv (Fin 10)).symm
            (why24CCZToUOneSevenErrorWord error))
          ((why24BinaryRegisterTransport (Fin 10)).symm
            why24UOneSevenQubitResource))‖ =
        ‖zWordTransport 2
          ((why24BinaryRegisterLabelEquiv (Fin 10)).symm
            (why24CCZToUOneSevenErrorWord error))
          ((why24BinaryRegisterTransport (Fin 10)).symm
            why24UOneSevenQubitResource)‖ :=
      (why24BinaryRegisterTransport (Fin 10)).toLinearIsometryEquiv.norm_map _
    _ = ‖(why24BinaryRegisterTransport (Fin 10)).symm
          why24UOneSevenQubitResource‖ :=
      (zWordTransport 2 _).toLinearIsometryEquiv.norm_map _
    _ = ‖why24UOneSevenQubitResource‖ :=
      (why24BinaryRegisterTransport
        (Fin 10)).symm.toLinearIsometryEquiv.norm_map _
    _ = 1 := why24UOneSevenQubitResource_norm

private theorem why24CCZToUOneSevenErrorKet_normSq
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) :
    ‖why24CCZToUOneSevenErrorKet error‖ ^ 2 = 1 := by
  rw [why24CCZToUOneSevenErrorKet_norm]
  norm_num

/-- The actual seventy-resource converter: jointly measure the CCZ magic
basis and apply the corresponding corrected Appendix `Z` word. -/
noncomputable def why24CCZToUOneSevenKraus :
    FiniteKrausFamily (Fin 70 -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin 70)) Why24QubitSpace where
  operator error :=
    (InnerProductSpace.rankOne Complex
      (why24CCZToUOneSevenErrorKet error)
      (why24JointCCZMagicBasisKet 70 error)).toLinearMap

private theorem why24CCZToUOneSevenKraus_adjoint_comp
    (error : Fin 70 -> Qubit.Bitstring (Fin 3)) :
    (LinearMap.adjoint (why24CCZToUOneSevenKraus.operator error)).comp
        (why24CCZToUOneSevenKraus.operator error) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet 70 error)
        (why24JointCCZMagicBasisKet 70 error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (why24CCZToUOneSevenErrorKet error)
        (why24JointCCZMagicBasisKet 70 error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet 70 error)
        (why24CCZToUOneSevenErrorKet error)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24CCZToUOneSevenErrorKet error)
      (why24JointCCZMagicBasisKet 70 error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [why24CCZToUOneSevenKraus]
  rw [hadjoint]
  have hnormSq : (↑‖why24CCZToUOneSevenErrorKet error‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact why24CCZToUOneSevenErrorKet_normSq error
  simp [LinearMap.comp_apply, hnormSq]

/-- Completeness of the actual seventy-CCZ converter. -/
theorem why24CCZToUOneSevenInstrument_complete :
    why24CCZToUOneSevenKraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [why24CCZToUOneSevenKraus_adjoint_comp]
  have hport := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id (why24JointCCZMagicBasis 70))
  simp [why24JointCCZMagicBasisKet] at hport ⊢
  exact hport

/-- The actual measured/corrected forward conversion instrument. -/
noncomputable def why24CCZToUOneSevenInstrument :
    FiniteInstrument
      (Fin 70 -> Qubit.Bitstring (Fin 3))
      (Fin 70 -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin 70)) Why24QubitSpace where
  kraus := why24CCZToUOneSevenKraus
  observe := id

private theorem why24CCZToUOneSevenErrorWord_zero :
    why24CCZToUOneSevenErrorWord
        (0 : Fin 70 -> Qubit.Bitstring (Fin 3)) = 0 := by
  funext site
  simp [why24CCZToUOneSevenErrorWord,
    why24BinaryRegisterLabelEquiv,
    why24AppendixCCZErrorContribution]

private theorem why24CCZToUOneSevenErrorKet_zero :
    why24CCZToUOneSevenErrorKet
        (0 : Fin 70 -> Qubit.Bitstring (Fin 3)) =
      why24UOneSevenQubitResource := by
  rw [why24CCZToUOneSevenErrorKet, why24CCZToUOneSevenErrorWord_zero]
  have hzero :
      (why24BinaryRegisterLabelEquiv (Fin 10)).symm
          (0 : Qubit.Bitstring (Fin 10)) = 0 := by
    funext site
    rfl
  rw [hzero]
  have hz (psi : PrimeQuditRegister 2 (Fin 10)) :
      zWordTransport 2 (0 : PrimeQuditRegisterLabel 2 (Fin 10)) psi = psi := by
    ext label
    simp [zWordTransport_apply, registerPhase, registerPairing]
  rw [hz]
  exact (why24BinaryRegisterTransport
    (Fin 10)).toLinearEquiv.apply_symm_apply _

/-- On an ideal joint magic-basis input, the actual seventy-CCZ instrument
prepares the literal Appendix `U_1^(7)` resource. -/
theorem why24CCZToUOneSeven_ideal :
    (why24CCZToUOneSevenInstrument.kraus.toQuantumChannel
      why24CCZToUOneSevenInstrument_complete).mapDensity
        (DensityOperator.pureDensity
          (why24JointCCZMagicBasisKet 70 0)
          (why24JointCCZMagicBasisKet_normSq 70 0)) =
      why24UOneSevenQubitResourceDensity := by
  apply DensityOperator.ext_toOperator
  dsimp only [why24CCZToUOneSevenInstrument]
  rw [QuantumChannel.mapDensity_toOperator,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp only [why24CCZToUOneSevenInstrument,
    DensityOperator.pureDensity_toOperator,
    why24UOneSevenQubitResourceDensity]
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
  rw [Finset.sum_eq_single
    (0 : Fin 70 -> Qubit.Bitstring (Fin 3))]
  · change (InnerProductSpace.rankOne Complex
      (why24CCZToUOneSevenKraus.operator 0
        (why24JointCCZMagicBasisKet 70 0))
      (why24CCZToUOneSevenKraus.operator 0
        (why24JointCCZMagicBasisKet 70 0))).toLinearMap = _
    have hinner : inner Complex
        (why24JointCCZMagicBasisKet 70 0)
        (why24JointCCZMagicBasisKet 70 0) = 1 := by
      rw [inner_self_eq_norm_sq_to_K,
        why24JointCCZMagicBasisKet_norm]
      norm_num
    simp only [why24CCZToUOneSevenKraus,
      InnerProductSpace.toLinearMap_rankOne, LinearMap.smulRight_apply,
      innerₛₗ_apply_apply, hinner, one_smul]
    rw [why24CCZToUOneSevenErrorKet_zero]
  · intro error _ herror
    change (InnerProductSpace.rankOne Complex
      (why24CCZToUOneSevenKraus.operator error
        (why24JointCCZMagicBasisKet 70 0))
      (why24CCZToUOneSevenKraus.operator error
        (why24JointCCZMagicBasisKet 70 0))).toLinearMap = 0
    have hinner : inner Complex
        (why24JointCCZMagicBasisKet 70 error)
        (why24JointCCZMagicBasisKet 70 0) = 0 := by
      change inner Complex
        ((why24JointCCZMagicBasis 70) error)
        ((why24JointCCZMagicBasis 70) 0) = 0
      rw [(why24JointCCZMagicBasis 70).inner_eq_ite]
      exact if_neg herror
    simp only [why24CCZToUOneSevenKraus,
      InnerProductSpace.toLinearMap_rankOne, LinearMap.smulRight_apply,
      innerₛₗ_apply_apply, hinner, zero_smul]
    apply LinearMap.ext
    intro psi
    simp
  · simp

/-- Split the ten-bit Appendix register into its seven measured bits and its
three retained bits. -/
private def why24AppendixReverseSplit
    (bits : Qubit.Bitstring (Fin 10)) :
    Why24AppendixReverseOutcome × Qubit.Bitstring (Fin 3) :=
  (fun site => bits ⟨site.1 + 3, by omega⟩,
    fun site => bits ⟨site.1, by omega⟩)

private theorem why24AppendixReverseRecombine_split
    (bits : Qubit.Bitstring (Fin 10)) :
    why24AppendixReverseRecombine
        (why24AppendixReverseSplit bits).2
        (why24AppendixReverseSplit bits).1 = bits := by
  funext site
  fin_cases site <;> rfl

private theorem why24AppendixReverseSplit_recombine
    (labels : Why24AppendixReverseOutcome × Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseSplit
        (why24AppendixReverseRecombine labels.2 labels.1) = labels := by
  apply Prod.ext
  · funext site
    fin_cases site <;> rfl
  · funext site
    fin_cases site <;> rfl

/-- The literal retained/measured basis split is a bijection of all ten
physical qubit labels. -/
private def why24AppendixReverseLabelEquiv :
    Qubit.Bitstring (Fin 10) ≃
      Why24AppendixReverseOutcome × Qubit.Bitstring (Fin 3) where
  toFun := why24AppendixReverseSplit
  invFun labels := why24AppendixReverseRecombine labels.2 labels.1
  left_inv := why24AppendixReverseRecombine_split
  right_inv := why24AppendixReverseSplit_recombine

/-- One actual reverse-conversion Kraus operator: fix the seven measured
computational bits, retain the other three, and apply #885's literal
outcome-dependent correction phase. -/
private noncomputable def why24AppendixReverseKraus
    (outcome : Why24AppendixReverseOutcome) :
    Why24QubitSpace →ₗ[Complex] Why24CCZSpace where
  toFun psi := WithLp.toLp 2 fun retained =>
    PauliSymplectic.binaryPhaseScalar
        (why24AppendixReverseCorrectionPhase outcome retained) *
      psi (why24AppendixReverseRecombine retained outcome)
  map_add' left right := by
    ext retained
    simp [mul_add]
  map_smul' scalar psi := by
    ext retained
    simp [smul_eq_mul, mul_left_comm]

@[simp] private theorem why24AppendixReverseKraus_apply
    (outcome : Why24AppendixReverseOutcome) (psi : Why24QubitSpace)
    (retained : Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseKraus outcome psi retained =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        psi (why24AppendixReverseRecombine retained outcome) :=
  rfl

private theorem why24AppendixReverseKraus_inner
    (outcome : Why24AppendixReverseOutcome)
    (left right : Why24QubitSpace) :
    inner Complex (why24AppendixReverseKraus outcome left)
        (why24AppendixReverseKraus outcome right) =
      ∑ retained : Qubit.Bitstring (Fin 3),
        inner Complex
          (left (why24AppendixReverseRecombine retained outcome))
          (right (why24AppendixReverseRecombine retained outcome)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro retained _
  simp only [why24AppendixReverseKraus_apply, RCLike.inner_apply, map_mul]
  have hstar :
      starRingEnd Complex
          (PauliSymplectic.binaryPhaseScalar
            (why24AppendixReverseCorrectionPhase outcome retained)) =
        PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) :=
    PauliSymplectic.binaryPhaseScalar_star _
  rw [hstar]
  calc
    (PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        right (why24AppendixReverseRecombine retained outcome)) *
      (PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        star (left (why24AppendixReverseRecombine retained outcome))) =
        (PauliSymplectic.binaryPhaseScalar
            (why24AppendixReverseCorrectionPhase outcome retained) *
          PauliSymplectic.binaryPhaseScalar
            (why24AppendixReverseCorrectionPhase outcome retained)) *
          (right (why24AppendixReverseRecombine retained outcome) *
            star (left
              (why24AppendixReverseRecombine retained outcome))) := by ring
    _ = right (why24AppendixReverseRecombine retained outcome) *
        star (left (why24AppendixReverseRecombine retained outcome)) := by
      rw [why24BinaryPhaseScalar_mul_self, one_mul]

/-- The literal measurement-and-correction reverse instrument, with one Kraus
branch for each of the 128 published Appendix outcomes. -/
noncomputable def why24UOneSevenToCCZInstrument :
    FiniteInstrument Why24AppendixReverseOutcome
      Why24AppendixReverseOutcome Why24QubitSpace Why24CCZSpace where
  kraus :=
    { operator := why24AppendixReverseKraus }
  observe := id

set_option maxRecDepth 4096 in
/-- The 128 computational restrictions form a complete measurement; the
outcome corrections are phase unitaries and do not change completeness. -/
theorem why24UOneSevenToCCZInstrument_complete :
    why24UOneSevenToCCZInstrument.kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  apply LinearMap.ext
  intro input
  apply ext_inner_left Complex
  intro test
  calc
    inner Complex test
        ((∑ outcome : Why24AppendixReverseOutcome,
          (LinearMap.adjoint (why24AppendixReverseKraus outcome)).comp
            (why24AppendixReverseKraus outcome)) input) =
        ∑ outcome : Why24AppendixReverseOutcome,
          inner Complex
            (why24AppendixReverseKraus outcome test)
            (why24AppendixReverseKraus outcome input) := by
              simp only [LinearMap.sum_apply, inner_sum,
                LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    _ = ∑ outcome : Why24AppendixReverseOutcome,
        ∑ retained : Qubit.Bitstring (Fin 3),
          inner Complex
            (test (why24AppendixReverseRecombine retained outcome))
            (input (why24AppendixReverseRecombine retained outcome)) := by
              apply Finset.sum_congr rfl
              intro outcome _
              exact why24AppendixReverseKraus_inner outcome test input
    _ = ∑ labels : Why24AppendixReverseOutcome ×
          Qubit.Bitstring (Fin 3),
        inner Complex
          (test (why24AppendixReverseRecombine labels.2 labels.1))
          (input (why24AppendixReverseRecombine labels.2 labels.1)) := by
            rw [Fintype.sum_prod_type]
    _ = ∑ bits : Qubit.Bitstring (Fin 10),
        inner Complex (test bits) (input bits) := by
      symm
      apply Fintype.sum_equiv why24AppendixReverseLabelEquiv
      intro bits
      change inner Complex (test bits) (input bits) =
        inner Complex
          (test (why24AppendixReverseRecombine
            (why24AppendixReverseSplit bits).2
            (why24AppendixReverseSplit bits).1))
          (input (why24AppendixReverseRecombine
            (why24AppendixReverseSplit bits).2
            (why24AppendixReverseSplit bits).1))
      rw [why24AppendixReverseRecombine_split]
    _ = inner Complex test input := by
      rw [PiLp.inner_apply]

private theorem why24AppendixReverseKraus_resource
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseKraus outcome why24UOneSevenQubitResource =
      why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome) := by
  rfl

private theorem why24AppendixReverseCorrection_normSq
    (outcome : Why24AppendixReverseOutcome) :
    ‖why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome)‖ ^ 2 =
      why24AppendixReverseBornWeight outcome := by
  have hinner :
      inner Complex
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome)) =
        inner Complex (why24AppendixReverseRawBranch outcome)
          (why24AppendixReverseRawBranch outcome) := by
    rw [← why24AppendixReverseKraus_resource,
      why24AppendixReverseKraus_inner, PiLp.inner_apply]
    rfl
  calc
    ‖why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome)‖ ^ 2 =
        Complex.re (inner Complex
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))) :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
    _ = Complex.re (inner Complex
        (why24AppendixReverseRawBranch outcome)
        (why24AppendixReverseRawBranch outcome)) := by rw [hinner]
    _ = ‖why24AppendixReverseRawBranch outcome‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24AppendixReverseRawBranch outcome)).symm
    _ = why24AppendixReverseBornWeight outcome := rfl

private theorem why24UOneSevenToCCZ_branchOperator_ideal
    (outcome : Why24AppendixReverseOutcome) :
    why24UOneSevenToCCZInstrument.branchOperator outcome
        why24UOneSevenQubitResourceDensity.toOperator =
      (InnerProductSpace.rankOne Complex
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))).toLinearMap := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  rw [Finset.sum_eq_single outcome]
  · rw [if_pos (show why24UOneSevenToCCZInstrument.observe outcome = outcome from rfl)]
    change why24AppendixReverseKraus outcome ∘ₗ
      why24UOneSevenQubitResourceDensity.toOperator ∘ₗ
      (why24AppendixReverseKraus outcome).adjoint = _
    rw [why24UOneSevenQubitResourceDensity,
      DensityOperator.pureDensity_toOperator,
      why24LinearMap_comp_rankOne_comp_adjoint,
      why24AppendixReverseKraus_resource]
  · intro other _ hne
    exact if_neg (show why24UOneSevenToCCZInstrument.observe other ≠ outcome from hne)
  · intro hnot
    exact (hnot (Finset.mem_univ outcome)).elim

private theorem why24UOneSevenToCCZ_bornWeight_ideal
    (outcome : Why24AppendixReverseOutcome) :
    why24UOneSevenToCCZInstrument.bornWeight outcome
        why24UOneSevenQubitResourceDensity = (1 / 128 : Real) := by
  rw [FiniteInstrument.bornWeight,
    why24UOneSevenToCCZ_branchOperator_ideal,
    InnerProductSpace.trace_rankOne]
  calc
    Complex.re (inner Complex
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))) =
        ‖why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome)‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))).symm
    _ = why24AppendixReverseBornWeight outcome :=
      why24AppendixReverseCorrection_normSq outcome
    _ = (1 / 128 : Real) :=
      why24AppendixReverseBornWeight_eq_source outcome

set_option maxHeartbeats 800000 in
private theorem why24AppendixReverseConditional_toOperator
    (outcome : Why24AppendixReverseOutcome) :
    (why24AppendixReverseConditional outcome).toOperator =
      ((128 : Real) : Complex) •
        (InnerProductSpace.rankOne Complex
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))
          (why24AppendixReverseCorrection outcome
            (why24AppendixReverseRawBranch outcome))).toLinearMap := by
  change
    (InnerProductSpace.rankOne Complex
      ((Real.sqrt 128 : Complex) •
        why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))
      ((Real.sqrt 128 : Complex) •
        why24AppendixReverseCorrection outcome
          (why24AppendixReverseRawBranch outcome))).toLinearMap = _
  rw [why24RankOne_smul_self]
  have hsqrt : (Real.sqrt 128 : Complex) *
      (Real.sqrt 128 : Complex) = 128 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : Real) ≤ 128)
  have hstar : star (Real.sqrt 128 : Complex) =
      (Real.sqrt 128 : Complex) := by simp
  rw [hstar, hsqrt]
  norm_num

/-- Every actual reverse-conversion outcome has source Born mass `1/128` and
its normalized corrected branch is exactly the concrete CCZ resource. -/
theorem why24UOneSevenToCCZ_ideal
    (outcome : Why24AppendixReverseOutcome) :
    why24UOneSevenToCCZInstrument.bornWeight outcome
        why24UOneSevenQubitResourceDensity = (1 / 128 : Real) ∧
      why24UOneSevenToCCZInstrument.conditionalDensity outcome
          why24UOneSevenQubitResourceDensity (by
            rw [why24UOneSevenToCCZ_bornWeight_ideal]
            norm_num) =
        why24CCZMagicStateDensity := by
  refine ⟨why24UOneSevenToCCZ_bornWeight_ideal outcome, ?_⟩
  apply DensityOperator.ext_toOperator
  rw [FiniteInstrument.conditionalDensity_toOperator,
    why24UOneSevenToCCZ_branchOperator_ideal,
    why24UOneSevenToCCZ_bornWeight_ideal]
  have hsource := congrArg DensityOperator.toOperator
    (why24AppendixReverseConditional_eq_ccz outcome)
  rw [← hsource]
  rw [why24AppendixReverseConditional_toOperator]
  congr 1
  norm_num [Complex.ofReal_inv]

/-- The literal Appendix gate-count tuple debits seventy CCZ resources in the
forward `CCZ -> U_1^(7)` conversion. -/
def why24CCZToUOneSevenInputCount : Nat :=
  why24AppendixGateCounts.2.2

theorem why24CCZToUOneSeven_inputCount_eq_seventy :
    why24CCZToUOneSevenInputCount = 70 := by
  rw [why24CCZToUOneSevenInputCount,
    why24AppendixGateCounts_eq_source]

/-- Each reverse Appendix conversion retains exactly one CCZ resource. -/
def why24UOneSevenToCCZOutputCount : Nat := 1

theorem why24UOneSevenToCCZ_outputCount_eq_one :
    why24UOneSevenToCCZOutputCount = 1 :=
  rfl

/-! ## Physical F1024 Fourier syndrome and active correction -/

/-- The source-selected self-dual binary coordinates, flattened across every
physical F1024 site.  This is the literal register label transport used for
the X-stabilizer measurement. -/
noncomputable def why24OneRoundBinaryLabelEquiv {Site : Type}
    [Fintype Site] :
    Why24Word Site ≃ PrimeQuditRegisterLabel 2 (Site × Fin 10) :=
  (Equiv.piCongrRight
      (fun _ : Site => f1024SelectedCoordinates.toEquiv)).trans
    (Equiv.curry Site (Fin 10) (ZMod 2)).symm

@[simp]
theorem why24OneRoundBinaryLabelEquiv_apply {Site : Type}
    [Fintype Site] (word : Why24Word Site) (site : Site) (bit : Fin 10) :
    why24OneRoundBinaryLabelEquiv word (site, bit) =
      f1024SelectedCoordinates (word site) bit :=
  rfl

/-- The selected binary label transport preserves field-word addition. -/
theorem why24OneRoundBinaryLabelEquiv_add {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    why24OneRoundBinaryLabelEquiv (left + right) =
      why24OneRoundBinaryLabelEquiv left +
        why24OneRoundBinaryLabelEquiv right := by
  funext siteBit
  rcases siteBit with ⟨site, bit⟩
  change f1024SelectedCoordinates ((left + right) site) bit =
    f1024SelectedCoordinates (left site) bit +
      f1024SelectedCoordinates (right site) bit
  rw [Pi.add_apply, map_add, Pi.add_apply]

/-- The source-selected self-dual coordinates identify the binary register
pairing with the actual F1024 trace pairing. -/
theorem why24OneRound_registerPairing_binaryLabelEquiv {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    registerPairing 2
        (why24OneRoundBinaryLabelEquiv left)
        (why24OneRoundBinaryLabelEquiv right) =
      Algebra.trace (ZMod 2) F1024 (wordPairing left right) := by
  unfold registerPairing
  rw [Fintype.sum_prod_type, wordPairing_apply]
  simp_rw [why24OneRoundBinaryLabelEquiv_apply]
  change (∑ site : Site, ∑ bit : Fin 10,
      f1024SelectedCoordinates (left site) bit *
        f1024SelectedCoordinates (right site) bit) =
    Algebra.trace (ZMod 2) F1024
      (∑ site : Site, left site * right site)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro site _
  exact (f1024SelectedCoordinates_trace_pairing
    (left site) (right site)).symm

private theorem why24OneRound_phase_two_one :
    phase 2 (1 : ZMod 2) = (-1 : Complex) := by
  have hsq : phase 2 (1 : ZMod 2) * phase 2 (1 : ZMod 2) = 1 := by
    rw [← phase_add]
    rw [show (1 : ZMod 2) + 1 = 0 by decide, phase_zero]
  have hne : phase 2 (1 : ZMod 2) ≠ 1 := by
    intro hphase
    have hone := (phase_eq_one_iff 2 (1 : ZMod 2)).mp hphase
    norm_num at hone
  have hfactor :
      (phase 2 (1 : ZMod 2) - 1) *
          (phase 2 (1 : ZMod 2) + 1) = 0 := by
    calc
      (phase 2 (1 : ZMod 2) - 1) *
          (phase 2 (1 : ZMod 2) + 1) =
          phase 2 (1 : ZMod 2) * phase 2 (1 : ZMod 2) - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  have hplus : phase 2 (1 : ZMod 2) + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  exact eq_neg_of_add_eq_zero_left hplus

private theorem why24OneRound_phase_two_eq_binaryPhaseScalar
    (value : ZMod 2) :
    phase 2 value = PauliSymplectic.binaryPhaseScalar value := by
  fin_cases value
  · change phase 2 (0 : ZMod 2) =
      PauliSymplectic.binaryPhaseScalar (0 : ZMod 2)
    rw [phase_zero, PauliSymplectic.binaryPhaseScalar_zero]
  · change phase 2 (1 : ZMod 2) =
      PauliSymplectic.binaryPhaseScalar (1 : ZMod 2)
    rw [why24OneRound_phase_two_one,
      PauliSymplectic.binaryPhaseScalar_one]

private theorem why24OneRound_phase_two_tracePhase (value : F1024) :
    phase 2 (Algebra.trace (ZMod 2) F1024 value) = tracePhase value := by
  unfold tracePhase additiveCharacter fieldTrace
  exact why24OneRound_phase_two_eq_binaryPhaseScalar _

/-- The induced computational-basis unitary from an F1024 register to the
actual ten-bits-per-site register. -/
noncomputable def why24OneRoundBinaryBasisIsometry {Site : Type}
    [Fintype Site] :
    ComputationalBasisRegister F1024 Site ≃ₗᵢ[Complex]
      PrimeQuditRegister 2 (Site × Fin 10) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (why24OneRoundBinaryLabelEquiv (Site := Site))

noncomputable def why24OneRoundBinaryTransport {Site : Type}
    [Fintype Site] :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (PrimeQuditRegister 2 (Site × Fin 10)) where
  toLinearEquiv := why24OneRoundBinaryBasisIsometry.toLinearEquiv
  map_inner := why24OneRoundBinaryBasisIsometry.toLinearIsometry.inner_map_map

@[simp] theorem why24OneRoundBinaryTransport_symm_apply {Site : Type}
    [Fintype Site] (psi : PrimeQuditRegister 2 (Site × Fin 10))
    (word : Why24Word Site) :
    (why24OneRoundBinaryTransport (Site := Site)).symm psi word =
      psi (why24OneRoundBinaryLabelEquiv word) := by
  change (why24OneRoundBinaryBasisIsometry
    (Site := Site)).symm psi word = _
  rw [why24OneRoundBinaryBasisIsometry,
    LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- The actual F1024-register character ket, obtained by transporting the
complete binary character basis through the source-selected self-dual basis. -/
noncomputable def why24OneRoundCharacterKet {Site : Type}
    [Fintype Site] (word : Why24Word Site) :
    ComputationalBasisRegister F1024 Site :=
  (why24OneRoundBinaryTransport (Site := Site)).symm
    (characterKet 2 (why24OneRoundBinaryLabelEquiv word))

@[simp]
theorem why24OneRoundCharacterKet_apply {Site : Type}
    [Fintype Site] (word label : Why24Word Site) :
    why24OneRoundCharacterKet word label =
      (Real.sqrt (2 : Real) : Complex)⁻¹ ^ Fintype.card (Site × Fin 10) *
        phase 2 (registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv label)) := by
  rw [why24OneRoundCharacterKet,
    why24OneRoundBinaryTransport_symm_apply, characterKet_apply]
  norm_num

/-- Physical field-X translation acts diagonally on the transported F1024
character basis. -/
theorem why24OneRound_wordXTransport_characterKet {Site : Type}
    [Fintype Site] [DecidableEq Site]
    (shift word : Why24Word Site) :
    wordXTransport shift (why24OneRoundCharacterKet word) =
      phase 2 (registerPairing 2
        (why24OneRoundBinaryLabelEquiv word)
        (why24OneRoundBinaryLabelEquiv shift)) •
          why24OneRoundCharacterKet word := by
  ext label
  simp only [wordXTransport_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, why24OneRoundCharacterKet_apply]
  rw [why24OneRoundBinaryLabelEquiv_add]
  have hpairing : registerPairing 2
      (why24OneRoundBinaryLabelEquiv word)
      (why24OneRoundBinaryLabelEquiv label +
        why24OneRoundBinaryLabelEquiv shift) =
      registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv label) +
        registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv shift) := by
    simp [registerPairing, mul_add, Finset.sum_add_distrib]
  rw [hpairing, phase_add]
  ring

/-- A physical field-Z error translates the source-selected F1024 character
label by that same actual error word. -/
theorem why24OneRound_wordZTransport_characterKet {Site : Type}
    [Fintype Site] [DecidableEq Site]
    (error word : Why24Word Site) :
    wordZTransport error (why24OneRoundCharacterKet word) =
      why24OneRoundCharacterKet (word + error) := by
  ext label
  simp only [wordZTransport_apply, wordZAmplitude,
    why24OneRoundCharacterKet_apply]
  rw [why24OneRoundBinaryLabelEquiv_add]
  have herrorPhase : tracePhase (wordPairing error label) =
      phase 2 (registerPairing 2
        (why24OneRoundBinaryLabelEquiv error)
        (why24OneRoundBinaryLabelEquiv label)) := by
    rw [why24OneRound_registerPairing_binaryLabelEquiv,
      why24OneRound_phase_two_tracePhase]
  rw [herrorPhase]
  have hpairing : registerPairing 2
      (why24OneRoundBinaryLabelEquiv word +
        why24OneRoundBinaryLabelEquiv error)
      (why24OneRoundBinaryLabelEquiv label) =
      registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv label) +
        registerPairing 2
          (why24OneRoundBinaryLabelEquiv error)
          (why24OneRoundBinaryLabelEquiv label) := by
    simp [registerPairing, add_mul, Finset.sum_add_distrib]
  rw [hpairing, phase_add]
  ring

private def why24OneRoundStabilizerAddEquiv
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (shift : R.StabilizerCarrier) :
    R.StabilizerCarrier ≃ R.StabilizerCarrier where
  toFun word := ⟨word.1 + shift.1,
    R.stabilizerCode.carrier.add_mem word.property shift.property⟩
  invFun word := ⟨word.1 - shift.1,
    R.stabilizerCode.carrier.sub_mem word.property shift.property⟩
  left_inv word := by
    apply Subtype.ext
    exact add_sub_cancel_right word.1 shift.1
  right_inv word := by
    apply Subtype.ext
    exact sub_add_cancel word.1 shift.1

private theorem why24OneRound_cosetLabel_add_stabilizer
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (logical : Logical → F1024) (word shift : R.StabilizerCarrier) :
    R.cosetLabel logical
        (why24OneRoundStabilizerAddEquiv R shift word) =
      R.cosetLabel logical word + shift.1 := by
  funext site
  simp [why24OneRoundStabilizerAddEquiv, cosetLabel,
    Pi.add_apply, add_assoc]

/-- Every encoded coset ket is fixed by every actual X-stabilizer word. -/
theorem why24OneRound_wordXTransport_cosetKet
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (shift : R.StabilizerCarrier) (logical : Logical → F1024) :
    wordXTransport shift.1 (R.cosetKet logical) = R.cosetKet logical := by
  unfold cosetKet
  rw [map_smul, map_sum]
  simp_rw [wordXTransport_apply_basis]
  congr 1
  let e : R.StabilizerCarrier ≃ R.StabilizerCarrier :=
    why24OneRoundStabilizerAddEquiv
      (Logical := Logical) (Stabilizer := Stabilizer) (Site := Site) R shift
  let f : R.StabilizerCarrier → ComputationalBasisRegister F1024 Site :=
    fun word => registerBasisKet (R.cosetLabel logical word)
  calc
    (∑ word : R.StabilizerCarrier,
        registerBasisKet (R.cosetLabel logical word + shift.1)) =
        ∑ word : R.StabilizerCarrier, f (e word) := by
      apply Finset.sum_congr rfl
      intro word _
      change registerBasisKet (R.cosetLabel logical word + shift.1) =
        registerBasisKet (R.cosetLabel logical (e word))
      dsimp only [e]
      rw [why24OneRound_cosetLabel_add_stabilizer
        (Logical := Logical) (Stabilizer := Stabilizer) (Site := Site)]
    _ = ∑ word : R.StabilizerCarrier, f word := e.sum_comp f
    _ = ∑ word : R.StabilizerCarrier,
        registerBasisKet (R.cosetLabel logical word) := rfl

/-- The concrete normalized encoder is fixed by every actual X-stabilizer
word, on arbitrary logical amplitudes. -/
theorem why24OneRound_wordXTransport_encoded
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (shift : R.StabilizerCarrier)
    (psi : ComputationalBasisRegister F1024 Logical) :
    wordXTransport shift.1 (R.encodedCode.encode psi) =
      R.encodedCode.encode psi := by
  rw [R.encodedCode_encode_eq_encodingLinearMap]
  unfold WeightedTriorthogonalMatrix.encodingLinearMap
  change wordXTransport shift.1
      (∑ logical : Logical → F1024, psi logical • R.cosetKet logical) =
    ∑ logical : Logical → F1024, psi logical • R.cosetKet logical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro logical _
  rw [map_smul, why24OneRound_wordXTransport_cosetKet]

private theorem why24OneRound_exists_stabilizer_pairing_ne_zero
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (word : Why24Word Site)
    (hword : word ∉ R.stabilizerCode.dual.carrier) :
    ∃ shift : R.StabilizerCarrier,
      registerPairing 2
        (why24OneRoundBinaryLabelEquiv word)
        (why24OneRoundBinaryLabelEquiv shift.1) ≠ 0 := by
  have hnotOrthogonal : ¬ ∀ codeword : Why24Word Site,
      codeword ∈ R.stabilizerCode.carrier →
        wordPairing word codeword = 0 := by
    intro horthogonal
    exact hword ((R.stabilizerCode.mem_dual word).mpr horthogonal)
  rcases not_forall.mp hnotOrthogonal with ⟨codeword, hcodeword⟩
  have hcodeword' : codeword ∈ R.stabilizerCode.carrier ∧
      wordPairing word codeword ≠ 0 := Classical.not_imp.mp hcodeword
  obtain ⟨traceOne, htraceOne⟩ :=
    (Algebra.trace_surjective (ZMod 2) F1024) (1 : ZMod 2)
  let pairing := wordPairing word codeword
  let scalar := traceOne * pairing⁻¹
  let shift : R.StabilizerCarrier :=
    ⟨scalar • codeword,
      R.stabilizerCode.carrier.smul_mem scalar hcodeword'.1⟩
  refine ⟨shift, ?_⟩
  rw [why24OneRound_registerPairing_binaryLabelEquiv]
  have hpairing : wordPairing word shift.1 = traceOne := by
    change wordPairing word (scalar • codeword) = traceOne
    rw [map_smul]
    change scalar * wordPairing word codeword = traceOne
    dsimp only [scalar, pairing]
    rw [mul_assoc, inv_mul_cancel₀ hcodeword'.2, mul_one]
  rw [hpairing, htraceOne]
  exact one_ne_zero

private theorem why24OneRoundCharacterKet_inner_encoded_eq_zero_of_not_mem_dual
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (word : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Logical)
    (hword : word ∉ R.stabilizerCode.dual.carrier) :
    inner Complex (why24OneRoundCharacterKet word)
      (R.encodedCode.encode psi) = 0 := by
  obtain ⟨shift, hpairing⟩ :=
    why24OneRound_exists_stabilizer_pairing_ne_zero R word hword
  have hphase : phase 2 (registerPairing 2
      (why24OneRoundBinaryLabelEquiv word)
      (why24OneRoundBinaryLabelEquiv shift.1)) ≠ 1 := by
    intro hphase
    exact hpairing ((phase_eq_one_iff 2 _).mp hphase)
  have hunit := (wordXTransport shift.1).map_inner
    (R.encodedCode.encode psi) (why24OneRoundCharacterKet word)
  rw [why24OneRound_wordXTransport_encoded,
    why24OneRound_wordXTransport_characterKet] at hunit
  have heigen : phase 2 (registerPairing 2
      (why24OneRoundBinaryLabelEquiv word)
      (why24OneRoundBinaryLabelEquiv shift.1)) *
        inner Complex (R.encodedCode.encode psi)
          (why24OneRoundCharacterKet word) =
      inner Complex (R.encodedCode.encode psi)
        (why24OneRoundCharacterKet word) := by
    simpa only [inner_smul_right] using hunit
  have hzeroRight : inner Complex (R.encodedCode.encode psi)
      (why24OneRoundCharacterKet word) = 0 := by
    apply (mul_eq_zero.mp (show
      (phase 2 (registerPairing 2
          (why24OneRoundBinaryLabelEquiv word)
          (why24OneRoundBinaryLabelEquiv shift.1)) - 1) *
        inner Complex (R.encodedCode.encode psi)
          (why24OneRoundCharacterKet word) = 0 by
      rw [sub_mul, one_mul, heigen, sub_self])).resolve_left
    exact sub_ne_zero.mpr hphase
  calc
    inner Complex (why24OneRoundCharacterKet word)
        (R.encodedCode.encode psi) =
      starRingEnd Complex (inner Complex (R.encodedCode.encode psi)
        (why24OneRoundCharacterKet word)) :=
      (inner_conj_symm (why24OneRoundCharacterKet word)
        (R.encodedCode.encode psi)).symm
    _ = 0 := by rw [hzeroRight, map_zero]

private theorem why24OneRound_wordZTransport_self_inverse {Site : Type}
    [Fintype Site] [DecidableEq Site]
    (error : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Site) :
    wordZTransport error (wordZTransport error psi) = psi := by
  ext label
  simp only [wordZTransport_apply, wordZAmplitude]
  rw [← mul_assoc, tracePhase_square, one_mul]

private theorem why24OneRoundCharacterKet_inner_wordZ_encoded
    {Logical Stabilizer Site : Type} [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site]
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (error word : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Logical) :
    inner Complex (why24OneRoundCharacterKet word)
        (wordZTransport error (R.encodedCode.encode psi)) =
      inner Complex (why24OneRoundCharacterKet (word + error))
        (R.encodedCode.encode psi) := by
  have hunit := (wordZTransport error).map_inner
    (wordZTransport error (why24OneRoundCharacterKet word))
    (R.encodedCode.encode psi)
  rw [why24OneRound_wordZTransport_self_inverse,
    why24OneRound_wordZTransport_characterKet] at hunit
  exact hunit

@[simp]
theorem why24OneRoundZSyndromeMap_add (r : Nat)
    (left right : Why24Word (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndromeMap r (left + right) =
      f1024Why24OddZSyndromeMap r left +
        f1024Why24OddZSyndromeMap r right :=
  rfl

private theorem why24OneRoundZSyndrome_add_self_zero (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    syndrome + syndrome = 0 := by
  have htwo : (2 : F1024) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  calc
    syndrome + syndrome =
        (1 : F1024) • syndrome + (1 : F1024) • syndrome := by simp
    _ = ((1 : F1024) + 1) • syndrome := (add_smul _ _ _).symm
    _ = (2 : F1024) • syndrome := by norm_num
    _ = 0 := by rw [htwo, zero_smul]

private theorem why24OneRoundZSyndromeMap_add_eq_zero_iff (r : Nat)
    (left right : Why24Word (f1024Why24OddPhysicalSite r)) :
    f1024Why24OddZSyndromeMap r (left + right) = 0 ↔
      f1024Why24OddZSyndromeMap r left =
        f1024Why24OddZSyndromeMap r right := by
  rw [why24OneRoundZSyndromeMap_add]
  constructor
  · intro hzero
    have h := congrArg
      (fun syndrome => syndrome + f1024Why24OddZSyndromeMap r right) hzero
    simpa only [add_assoc,
      why24OneRoundZSyndrome_add_self_zero, add_zero, zero_add] using h
  · intro heq
    rw [heq, why24OneRoundZSyndrome_add_self_zero]

private theorem why24OneRoundCharacterKet_inner_wordZ_encoded_eq_zero_of_ne
    (r : Nat)
    (error word : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (hsyndrome : f1024Why24OddZSyndromeMap r word ≠
      f1024Why24OddZSyndromeMap r error) :
    inner Complex (why24OneRoundCharacterKet word)
      (wordZTransport error
        ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) = 0 := by
  rw [why24OneRoundCharacterKet_inner_wordZ_encoded]
  apply why24OneRoundCharacterKet_inner_encoded_eq_zero_of_not_mem_dual
  intro hmem
  apply hsyndrome
  exact (why24OneRoundZSyndromeMap_add_eq_zero_iff r word error).mp
    ((f1024Why24OddZSyndrome_eq_zero_iff r (word + error)).mpr hmem)

/-- The transported F1024 character kets remain orthonormal. -/
theorem why24OneRoundCharacterKet_inner {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    inner Complex (why24OneRoundCharacterKet left)
        (why24OneRoundCharacterKet right) =
      if left = right then 1 else 0 := by
  rw [why24OneRoundCharacterKet, why24OneRoundCharacterKet,
    (why24OneRoundBinaryTransport (Site := Site)).symm.map_inner,
    characterKet_inner]
  simp only [Equiv.apply_eq_iff_eq]

private theorem why24OneRoundCharacterRankOne_transport {Site : Type}
    [Fintype Site] (word : Why24Word Site)
    (psi : ComputationalBasisRegister F1024 Site) :
    why24OneRoundBinaryTransport
        ((InnerProductSpace.rankOne Complex
          (why24OneRoundCharacterKet word)
          (why24OneRoundCharacterKet word)).toLinearMap psi) =
      (InnerProductSpace.rankOne Complex
        (characterKet 2 (why24OneRoundBinaryLabelEquiv word))
        (characterKet 2 (why24OneRoundBinaryLabelEquiv word))).toLinearMap
          (why24OneRoundBinaryTransport psi) := by
  simp only [InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, map_smul,
    why24OneRoundCharacterKet]
  rw [← (why24OneRoundBinaryTransport (Site := Site)).map_inner]
  simp

/-- Summing the transported character rank-one projectors gives the physical
F1024-register identity. -/
theorem why24OneRound_sum_characterRankOne_eq_one {Site : Type}
    [Fintype Site] :
    (∑ word : Why24Word Site,
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCharacterKet word)
        (why24OneRoundCharacterKet word)).toLinearMap) = 1 := by
  apply LinearMap.ext
  intro psi
  apply (why24OneRoundBinaryTransport
    (Site := Site)).toLinearEquiv.injective
  calc
    why24OneRoundBinaryTransport
        ((∑ word : Why24Word Site,
          (InnerProductSpace.rankOne Complex
            (why24OneRoundCharacterKet word)
            (why24OneRoundCharacterKet word)).toLinearMap) psi) =
        ∑ word : Why24Word Site,
          (InnerProductSpace.rankOne Complex
            (characterKet 2 (why24OneRoundBinaryLabelEquiv word))
            (characterKet 2 (why24OneRoundBinaryLabelEquiv word))).toLinearMap
              (why24OneRoundBinaryTransport psi) := by
      simp only [LinearMap.sum_apply, map_sum,
        why24OneRoundCharacterRankOne_transport]
    _ = ∑ word : PrimeQuditRegisterLabel 2 (Site × Fin 10),
        (InnerProductSpace.rankOne Complex
          (characterKet 2 word) (characterKet 2 word)).toLinearMap
            (why24OneRoundBinaryTransport psi) := by
      apply Fintype.sum_equiv
        (why24OneRoundBinaryLabelEquiv (Site := Site))
      intro word
      rfl
    _ = why24OneRoundBinaryTransport psi := by
      rw [← LinearMap.sum_apply, sum_characterKet_rankOne_eq_one]
      rfl
    _ = why24OneRoundBinaryTransport ((1 : Operator
        (ComputationalBasisRegister F1024 Site)) psi) := by rfl

private theorem why24OneRoundCharacterRankOne_mul {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    (InnerProductSpace.rankOne Complex
      (why24OneRoundCharacterKet left)
      (why24OneRoundCharacterKet left)).toLinearMap *
        (InnerProductSpace.rankOne Complex
          (why24OneRoundCharacterKet right)
          (why24OneRoundCharacterKet right)).toLinearMap =
      if left = right then
        (InnerProductSpace.rankOne Complex
          (why24OneRoundCharacterKet right)
          (why24OneRoundCharacterKet right)).toLinearMap
      else 0 := by
  classical
  ext psi
  simp only [Module.End.mul_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  rw [inner_smul_right]
  by_cases hsame : left = right
  · subst left
    rw [why24OneRoundCharacterKet_inner]
    simp
  · rw [why24OneRoundCharacterKet_inner]
    simp [hsame]

/-- The coherent physical X-stabilizer sector projector indexed by the actual
AG quotient syndrome. -/
noncomputable def why24OneRoundSyndromeProjector (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddPhysicalSite r)) :=
  ∑ word : Why24Word (f1024Why24OddPhysicalSite r),
    if f1024Why24OddZSyndromeMap r word = syndrome then
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCharacterKet word)
        (why24OneRoundCharacterKet word)).toLinearMap
    else 0

/-- A syndrome sector keeps exactly the transported character labels in that
quotient class. -/
theorem why24OneRoundSyndromeProjector_apply_characterKet (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (word : Why24Word (f1024Why24OddPhysicalSite r)) :
    why24OneRoundSyndromeProjector r syndrome
        (why24OneRoundCharacterKet word) =
      if f1024Why24OddZSyndromeMap r word = syndrome then
        why24OneRoundCharacterKet word else 0 := by
  classical
  unfold why24OneRoundSyndromeProjector
  simp only [LinearMap.sum_apply]
  by_cases hsector : f1024Why24OddZSyndromeMap r word = syndrome
  · rw [if_pos hsector, Finset.sum_eq_single word]
    · rw [if_pos hsector]
      simp only [InnerProductSpace.toLinearMap_rankOne,
        LinearMap.smulRight_apply, innerₛₗ_apply_apply]
      rw [why24OneRoundCharacterKet_inner]
      simp
    · intro other _ hne
      by_cases hother : f1024Why24OddZSyndromeMap r other = syndrome
      · rw [if_pos hother]
        simp only [InnerProductSpace.toLinearMap_rankOne,
          LinearMap.smulRight_apply, innerₛₗ_apply_apply]
        rw [why24OneRoundCharacterKet_inner]
        simp [hne]
      · simp [hother]
    · simp
  · rw [if_neg hsector]
    apply Finset.sum_eq_zero
    intro other _
    by_cases hother : f1024Why24OddZSyndromeMap r other = syndrome
    · rw [if_pos hother]
      simp only [InnerProductSpace.toLinearMap_rankOne,
        LinearMap.smulRight_apply, innerₛₗ_apply_apply]
      rw [why24OneRoundCharacterKet_inner]
      have hne : other ≠ word := by
        intro heq
        subst other
        exact hsector hother
      simp [hne]
    · simp [hother]

private theorem why24OneRoundSyndromeProjector_apply_wordZ_encoded_eq_zero_of_ne
    (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (syndrome : f1024Why24OddZSyndrome r)
    (hsyndrome : syndrome ≠ f1024Why24OddZSyndromeMap r error) :
    why24OneRoundSyndromeProjector r syndrome
        (wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) = 0 := by
  unfold why24OneRoundSyndromeProjector
  simp only [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro word _
  by_cases hsector : f1024Why24OddZSyndromeMap r word = syndrome
  · rw [if_pos hsector]
    simp only [InnerProductSpace.toLinearMap_rankOne,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply]
    have hword : f1024Why24OddZSyndromeMap r word ≠
        f1024Why24OddZSyndromeMap r error := by
      intro heq
      exact hsyndrome (hsector.symm.trans heq)
    rw [why24OneRoundCharacterKet_inner_wordZ_encoded_eq_zero_of_ne
      r error word psi hword, zero_smul]
  · simp [hsector]

/-- The syndrome projectors partition the full transported Fourier basis. -/
theorem why24OneRound_sum_syndromeProjector_eq_one (r : Nat) :
    ∑ syndrome : f1024Why24OddZSyndrome r,
      why24OneRoundSyndromeProjector r syndrome = 1 := by
  classical
  unfold why24OneRoundSyndromeProjector
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  exact why24OneRound_sum_characterRankOne_eq_one

/-- The actual coherent syndrome measurement places a field-Z-corrupted
encoded state in exactly the quotient sector of that physical error word. -/
theorem why24OneRoundSyndromeProjector_apply_wordZ_encoded
    (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (syndrome : f1024Why24OddZSyndrome r) :
    why24OneRoundSyndromeProjector r syndrome
        (wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) =
      if syndrome = f1024Why24OddZSyndromeMap r error then
        wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)
      else 0 := by
  by_cases hsyndrome : syndrome = f1024Why24OddZSyndromeMap r error
  · subst syndrome
    rw [if_pos rfl]
    calc
      why24OneRoundSyndromeProjector r
          (f1024Why24OddZSyndromeMap r error)
          (wordZTransport error
            ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) =
          (∑ measured : f1024Why24OddZSyndrome r,
            why24OneRoundSyndromeProjector r measured)
            (wordZTransport error
              ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi)) := by
        rw [LinearMap.sum_apply, Finset.sum_eq_single
          (f1024Why24OddZSyndromeMap r error)]
        · intro other _ hother
          exact
            why24OneRoundSyndromeProjector_apply_wordZ_encoded_eq_zero_of_ne
              r error psi other hother
        · simp
      _ = wordZTransport error
          ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi) := by
        rw [why24OneRound_sum_syndromeProjector_eq_one]
        rfl
  · rw [if_neg hsyndrome]
    exact
      why24OneRoundSyndromeProjector_apply_wordZ_encoded_eq_zero_of_ne
        r error psi syndrome hsyndrome

/-- Every coherent syndrome-sector projector is self-adjoint. -/
theorem why24OneRoundSyndromeProjector_adjoint (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    LinearMap.adjoint (why24OneRoundSyndromeProjector r syndrome) =
      why24OneRoundSyndromeProjector r syndrome := by
  classical
  unfold why24OneRoundSyndromeProjector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hsector : f1024Why24OddZSyndromeMap r word = syndrome
  · rw [if_pos hsector, LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24OneRoundCharacterKet word)
      (why24OneRoundCharacterKet word)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  · simp [hsector]

/-- Every coherent syndrome-sector projector is idempotent. -/
theorem why24OneRoundSyndromeProjector_idempotent (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (why24OneRoundSyndromeProjector r syndrome).comp
        (why24OneRoundSyndromeProjector r syndrome) =
      why24OneRoundSyndromeProjector r syndrome := by
  classical
  rw [← Module.End.mul_eq_comp]
  unfold why24OneRoundSyndromeProjector
  rw [Fintype.sum_mul_sum]
  simp_rw [ite_mul, mul_ite, zero_mul, mul_zero,
    why24OneRoundCharacterRankOne_mul]
  apply Finset.sum_congr rfl
  intro left _
  by_cases hsector : f1024Why24OddZSyndromeMap r left = syndrome
  · rw [if_pos hsector, Finset.sum_eq_single left]
    · simp [hsector]
    · intro right _ hne
      have hleftRight : left ≠ right := Ne.symm hne
      simp [hsector, hleftRight]
    · simp
  · simp [hsector]

/-- The actual finite coherent X-stabilizer syndrome instrument. -/
noncomputable def why24OneRoundSyndromeInstrument (r : Nat) :
    FiniteInstrument (f1024Why24OddZSyndrome r)
      (f1024Why24OddZSyndrome r)
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) where
  kraus :=
    { operator := why24OneRoundSyndromeProjector r }
  observe := id

/-- Completeness of the physical syndrome measurement is derived from the
actual transported Fourier projectors. -/
theorem why24OneRoundSyndromeInstrument_complete (r : Nat) :
    (why24OneRoundSyndromeInstrument r).kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [why24OneRoundSyndromeInstrument]
  rw [Finset.sum_congr rfl (fun syndrome _ => by
    rw [why24OneRoundSyndromeProjector_adjoint,
      why24OneRoundSyndromeProjector_idempotent])]
  exact why24OneRound_sum_syndromeProjector_eq_one r

/-- Active field-Z correction selected by the measured syndrome and the
actual AG key-equation decoder.  Characteristic two makes this same transport
the inverse of the decoded error. -/
noncomputable def why24OneRoundCorrection (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    UnitaryTransport
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  wordZTransport (f1024Why24OddAGDualDecoder r syndrome)

/-- Within the proved AG decoding radius, measuring the actual quotient
syndrome and applying its decoded field-Z correction restores the encoded
state exactly. -/
theorem why24OneRoundCorrection_restores_encoded (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r))
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
        (why24OneRoundSyndromeProjector r
          (f1024Why24OddZSyndromeMap r error)
          (wordZTransport error
            ((f1024Why24OddWeightedMatrix r).encodedCode.encode psi))) =
      (f1024Why24OddWeightedMatrix r).encodedCode.encode psi := by
  rw [why24OneRoundSyndromeProjector_apply_wordZ_encoded, if_pos rfl]
  unfold why24OneRoundCorrection
  rw [f1024Why24OddAGDualDecoder_correct r error herror]
  exact why24OneRound_wordZTransport_self_inverse error _

/-- The one-outcome physical correction instrument selected after one
syndrome observation. -/
noncomputable def why24OneRoundCorrectionInstrument (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    FiniteInstrument PUnit PUnit
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) where
  kraus :=
    { operator := fun _ =>
        (why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap }
  observe := id

/-- Every syndrome-selected correction branch is a complete unitary
instrument. -/
theorem why24OneRoundCorrectionInstrument_complete (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (why24OneRoundCorrectionInstrument r syndrome).kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  rw [show (Finset.univ : Finset PUnit) = {PUnit.unit} by
    ext index
    simp]
  rw [Finset.sum_singleton]
  change (LinearMap.adjoint
      (why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap).comp
        (why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap = 1
  rw [(why24OneRoundCorrection r syndrome).adjoint_toLinearMap]
  ext psi
  simp

/-- The deterministic one-round physical instrument: coherently measure the
actual X-stabilizer quotient syndrome, then apply the AG-decoder correction.
Every syndrome is retained; no branch is discarded. -/
noncomputable def why24OneRoundInstrument (r : Nat) :
    FiniteInstrument
      (f1024Why24OddZSyndrome r × PUnit)
      (Sigma (fun _ : f1024Why24OddZSyndrome r => PUnit))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  (why24OneRoundSyndromeInstrument r).bind
    (why24OneRoundCorrectionInstrument r)

/-- Completeness of active correction follows by finite instrument binding,
from the actual syndrome measurement and each unitary decoder correction. -/
theorem why24OneRoundInstrument_complete (r : Nat) :
    (why24OneRoundInstrument r).kraus.Complete := by
  exact (why24OneRoundSyndromeInstrument r).bind_complete
    (why24OneRoundCorrectionInstrument r)
    (why24OneRoundSyndromeInstrument_complete r)
    (why24OneRoundCorrectionInstrument_complete r)

/-! ## Total inverse encoding after active correction -/

/-- The actual WHY24 encoding, viewed as an isometry into the ambient
physical register rather than merely into the code carrier. -/
def why24OneRoundAmbientEncodingIsometry (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) →ₗᵢ[Complex]
      ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  (f1024Why24OddEncodedCode r).code.carrier.subtypeₗᵢ.comp
    (f1024Why24OddEncodedCode r).encoding.toLinearIsometry

@[simp] theorem why24OneRoundAmbientEncodingIsometry_apply (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundAmbientEncodingIsometry r psi =
      ((f1024Why24OddEncodedCode r).encoding psi :
        ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  rfl

/-- Coherent inverse encoding on the actual WHY24 carrier. -/
def why24OneRoundCodeDecoderBranch (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) →ₗ[Complex]
      ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  LinearMap.adjoint (why24OneRoundAmbientEncodingIsometry r).toLinearMap

@[simp] theorem why24OneRoundCodeDecoderBranch_encoded (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundCodeDecoderBranch r
        (why24OneRoundAmbientEncodingIsometry r psi) = psi := by
  change LinearMap.adjoint
      (why24OneRoundAmbientEncodingIsometry r).toLinearMap
      ((why24OneRoundAmbientEncodingIsometry r).toLinearMap psi) = psi
  exact LinearMap.congr_fun
    (why24OneRoundAmbientEncodingIsometry r).adjoint_comp_self' psi

private theorem why24OneRound_adjoint_codeDecoderBranch (r : Nat) :
    LinearMap.adjoint (why24OneRoundCodeDecoderBranch r) =
      (why24OneRoundAmbientEncodingIsometry r).toLinearMap := by
  rw [why24OneRoundCodeDecoderBranch, LinearMap.adjoint_adjoint]

/-- Orthogonal projector onto the actual WHY24 encoded carrier. -/
def why24OneRoundDecoderCodeProjector (r : Nat) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddPhysicalSite r)) :=
  (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
    (why24OneRoundCodeDecoderBranch r)

@[simp] theorem why24OneRoundDecoderCodeProjector_encoded (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundDecoderCodeProjector r
        (why24OneRoundAmbientEncodingIsometry r psi) =
      why24OneRoundAmbientEncodingIsometry r psi := by
  change LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)
      (why24OneRoundCodeDecoderBranch r
        (why24OneRoundAmbientEncodingIsometry r psi)) =
    why24OneRoundAmbientEncodingIsometry r psi
  rw [why24OneRoundCodeDecoderBranch_encoded,
    why24OneRound_adjoint_codeDecoderBranch]
  rfl

private theorem why24OneRoundCodeDecoderBranch_comp_adjoint (r : Nat) :
    (why24OneRoundCodeDecoderBranch r).comp
        (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)) = 1 := by
  rw [why24OneRound_adjoint_codeDecoderBranch,
    why24OneRoundCodeDecoderBranch]
  exact (why24OneRoundAmbientEncodingIsometry r).adjoint_comp_self'

theorem why24OneRoundDecoderCodeProjector_idempotent (r : Nat) :
    (why24OneRoundDecoderCodeProjector r).comp
        (why24OneRoundDecoderCodeProjector r) =
      why24OneRoundDecoderCodeProjector r := by
  rw [why24OneRoundDecoderCodeProjector]
  calc
    ((LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        (why24OneRoundCodeDecoderBranch r)).comp
        ((LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
          (why24OneRoundCodeDecoderBranch r)) =
      (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        (((why24OneRoundCodeDecoderBranch r).comp
          (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r))).comp
            (why24OneRoundCodeDecoderBranch r)) := by
              ext psi
              rfl
    _ = (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        ((1 : Operator (ComputationalBasisRegister F1024
          (f1024Why24OddLogical r))).comp
            (why24OneRoundCodeDecoderBranch r)) := by
      rw [why24OneRoundCodeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint (why24OneRoundCodeDecoderBranch r)).comp
        (why24OneRoundCodeDecoderBranch r) := by
      ext psi
      rfl

theorem why24OneRoundDecoderCodeProjector_adjoint (r : Nat) :
    LinearMap.adjoint (why24OneRoundDecoderCodeProjector r) =
      why24OneRoundDecoderCodeProjector r := by
  simp [why24OneRoundDecoderCodeProjector, LinearMap.adjoint_comp]

/-- Orthogonal complement of the actual WHY24 carrier. -/
def why24OneRoundDecoderComplementProjector (r : Nat) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddPhysicalSite r)) :=
  1 - why24OneRoundDecoderCodeProjector r

private theorem why24OneRoundDecoderComplementProjector_adjoint (r : Nat) :
    LinearMap.adjoint (why24OneRoundDecoderComplementProjector r) =
      why24OneRoundDecoderComplementProjector r := by
  simp [why24OneRoundDecoderComplementProjector,
    why24OneRoundDecoderCodeProjector_adjoint]

private theorem why24OneRoundDecoderComplementProjector_idempotent (r : Nat) :
    (why24OneRoundDecoderComplementProjector r).comp
        (why24OneRoundDecoderComplementProjector r) =
      why24OneRoundDecoderComplementProjector r := by
  ext psi
  have hprojector := LinearMap.congr_fun
    (why24OneRoundDecoderCodeProjector_idempotent r) psi
  simp only [why24OneRoundDecoderComplementProjector,
    LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf

@[simp] private theorem why24OneRoundDecoderComplementProjector_encoded
    (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundDecoderComplementProjector r
        (why24OneRoundAmbientEncodingIsometry r psi) = 0 := by
  simp only [why24OneRoundDecoderComplementProjector,
    LinearMap.sub_apply, Module.End.one_apply]
  rw [why24OneRoundDecoderCodeProjector_encoded]
  abel_nf

/-- Neutral logical state used only to make inverse encoding total off the
actual code carrier. -/
noncomputable def why24OneRoundDecoderFallbackState (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  EuclideanSpace.basisFun
    (Why24Word (f1024Why24OddLogical r)) Complex (fun _ => 0)

private theorem why24OneRoundDecoderFallbackState_normSq (r : Nat) :
    ‖why24OneRoundDecoderFallbackState r‖ ^ 2 = 1 := by
  simp [why24OneRoundDecoderFallbackState]

private noncomputable def why24OneRoundDecoderPhysicalBasis (r : Nat) :=
  stdOrthonormalBasis Complex
    (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))

/-- One finite complement branch erases a projected ambient basis direction
to the fixed normalized fallback. -/
def why24OneRoundComplementDecoderBranch (r : Nat)
    (index : Fin (Module.finrank Complex
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)))) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) →ₗ[Complex]
      ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  (InnerProductSpace.rankOne Complex
    (why24OneRoundDecoderFallbackState r)
    (why24OneRoundDecoderComplementProjector r
      (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap

private theorem why24OneRoundComplementDecoderBranch_adjoint_comp (r : Nat)
    (index : Fin (Module.finrank Complex
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)))) :
    (LinearMap.adjoint (why24OneRoundComplementDecoderBranch r index)).comp
        (why24OneRoundComplementDecoderBranch r index) =
      (InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderFallbackState r)
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundDecoderFallbackState r)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24OneRoundDecoderFallbackState r)
      (why24OneRoundDecoderComplementProjector r
        (why24OneRoundDecoderPhysicalBasis r index))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [why24OneRoundComplementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖why24OneRoundDecoderFallbackState r‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact why24OneRoundDecoderFallbackState_normSq r
  simp [LinearMap.comp_apply, hnormSq]

private theorem why24OneRound_sum_complementDecoderBranch_adjoint_comp
    (r : Nat) :
    ∑ index : Fin (Module.finrank Complex
        (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))),
      (LinearMap.adjoint (why24OneRoundComplementDecoderBranch r index)).comp
        (why24OneRoundComplementDecoderBranch r index) =
      why24OneRoundDecoderComplementProjector r := by
  simp_rw [why24OneRoundComplementDecoderBranch_adjoint_comp]
  calc
    (∑ index,
      (InnerProductSpace.rankOne Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))).toLinearMap) =
      (why24OneRoundDecoderComplementProjector r).comp
        (LinearMap.adjoint (why24OneRoundDecoderComplementProjector r)) := by
      apply LinearMap.ext
      intro psi
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      rw [← (why24OneRoundDecoderPhysicalBasis r).sum_repr'
        (LinearMap.adjoint (why24OneRoundDecoderComplementProjector r) psi)]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro index _
      rw [LinearMap.adjoint_inner_right]
      rfl
    _ = (why24OneRoundDecoderComplementProjector r).comp
        (why24OneRoundDecoderComplementProjector r) := by
      rw [why24OneRoundDecoderComplementProjector_adjoint]
    _ = why24OneRoundDecoderComplementProjector r :=
      why24OneRoundDecoderComplementProjector_idempotent r

/-- Finite Kraus completion of coherent inverse encoding to a total physical
WHY24 decoder. -/
def why24OneRoundDecoderKrausFamily (r : Nat) :
    FiniteKrausFamily
      (Sum Unit (Fin (Module.finrank Complex
        (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)))))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) where
  operator
    | .inl _ => why24OneRoundCodeDecoderBranch r
    | .inr index => why24OneRoundComplementDecoderBranch r index

theorem why24OneRoundDecoderKrausFamily_complete (r : Nat) :
    (why24OneRoundDecoderKrausFamily r).Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, why24OneRoundDecoderCodeProjector r) +
      (∑ index : Fin (Module.finrank Complex
        (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))),
        (LinearMap.adjoint (why24OneRoundComplementDecoderBranch r index)).comp
          (why24OneRoundComplementDecoderBranch r index)) = 1
  rw [Fintype.sum_unique,
    why24OneRound_sum_complementDecoderBranch_adjoint_comp]
  simp [why24OneRoundDecoderComplementProjector]

/-- The actual total CPTP decoder: inverse encoding on the WHY24 carrier and
a finite neutral completion only on its orthogonal complement. -/
noncomputable def why24OneRoundDecoderChannel (r : Nat) :
    QuantumChannel
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  (why24OneRoundDecoderKrausFamily r).toQuantumChannel
    (why24OneRoundDecoderKrausFamily_complete r)

theorem why24OneRoundDecoderChannel_rankOne_encoded (r : Nat)
    (psi : ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :
    why24OneRoundDecoderChannel r
        (InnerProductSpace.rankOne Complex
          (why24OneRoundAmbientEncodingIsometry r psi)
          (why24OneRoundAmbientEncodingIsometry r psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [why24OneRoundDecoderChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum,
    Fintype.sum_sum_type]
  simp only [why24OneRoundDecoderKrausFamily]
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
  rw [Fintype.sum_unique]
  simp only [why24OneRoundCodeDecoderBranch_encoded]
  have hcomplement : ∀ index,
      why24OneRoundComplementDecoderBranch r index
        (why24OneRoundAmbientEncodingIsometry r psi) = 0 := by
    intro index
    have hinner : inner Complex
        (why24OneRoundDecoderComplementProjector r
          (why24OneRoundDecoderPhysicalBasis r index))
        (why24OneRoundAmbientEncodingIsometry r psi) = 0 := by
      rw [← LinearMap.adjoint_inner_right,
        why24OneRoundDecoderComplementProjector_adjoint,
        why24OneRoundDecoderComplementProjector_encoded]
      simp
    change inner Complex
      (why24OneRoundDecoderComplementProjector r
        (why24OneRoundDecoderPhysicalBasis r index))
      (why24OneRoundAmbientEncodingIsometry r psi) •
        why24OneRoundDecoderFallbackState r = 0
    rw [hinner]
    simp
  simp_rw [hcomplement]
  simp

/-- Every detailed one-round branch is accepted.  Outcome records are kept
for the physical syndrome semantics, but never used to discard an output. -/
def why24OneRoundAccepts {r : Nat}
    (_ : Sigma (fun _ : f1024Why24OddZSyndrome r => PUnit)) : Bool :=
  true

/-- The literal Appendix resource count for one physical code block. -/
def why24OneRoundInputCount (r : Nat) : Nat :=
  why24CCZToUOneSevenInputCount * f1024Why24OddLength r

/-- The literal number of retained logical F1024 output coordinates. -/
def why24OneRoundOutputCount (r : Nat) : Nat :=
  f1024Why24OddDimension r

theorem why24OneRoundInputCount_eq (r : Nat) :
    why24OneRoundInputCount r = 70 * f1024Why24OddLength r := by
  rw [why24OneRoundInputCount, why24CCZToUOneSeven_inputCount_eq_seventy]

theorem why24OneRoundOutputCount_eq (r : Nat) :
    why24OneRoundOutputCount r = f1024Why24OddDimension r :=
  rfl

/-! ## Correlated stochastic-Z preparation and the actual finite run -/

/-- Group the seventy source CCZ preparation locations belonging to one
physical F1024 coordinate. -/
def why24OneRoundCCZLocationEquiv (r : Nat) :
    Fin (f1024Why24OddLength r) × Fin 70 ≃
      Fin (why24OneRoundInputCount r) :=
  finProdFinEquiv.trans (finCongr (by
    rw [why24OneRoundInputCount_eq]
    omega))

/-- Canonical finite coordinate of one actual physical AG-code site. -/
noncomputable def why24OneRoundPhysicalSiteEquiv (r : Nat) :
    f1024Why24OddPhysicalSite r ≃ Fin (f1024Why24OddLength r) :=
  Fintype.equivFin _

/-- The normalized logical plus state encoded before the transversal noisy
gate injection. -/
noncomputable def why24OneRoundLogicalPlusKet (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  why24OneRoundCharacterKet
    (0 : Why24Word (f1024Why24OddLogical r))

private theorem why24OneRoundLogicalPlusKet_normSq (r : Nat) :
    ‖why24OneRoundLogicalPlusKet r‖ ^ 2 = 1 := by
  have hinner : inner Complex (why24OneRoundLogicalPlusKet r)
      (why24OneRoundLogicalPlusKet r) = 1 := by
    have h := why24OneRoundCharacterKet_inner
      (Site := f1024Why24OddLogical r)
      (0 : Why24Word (f1024Why24OddLogical r))
      (0 : Why24Word (f1024Why24OddLogical r))
    simp only [if_pos] at h
    convert h using 1
    simp only [why24OneRoundLogicalPlusKet, PiLp.inner_apply]
    apply Finset.sum_congr
    · ext label
      simp
    · intro label _
      rfl
  calc
    ‖why24OneRoundLogicalPlusKet r‖ ^ 2 =
        (inner Complex (why24OneRoundLogicalPlusKet r)
          (why24OneRoundLogicalPlusKet r)).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
        (why24OneRoundLogicalPlusKet r)
    _ = 1 := by rw [hinner]; norm_num

/-- The source logical magic state produced by the exact logical
`U_1^(7)` action. -/
noncomputable def why24OneRoundLogicalIdealKet (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddLogical r) :=
  (f1024Why24OddWeightedMatrix r).logicalUOneSeven
    (why24OneRoundLogicalPlusKet r)

private theorem why24OneRoundLogicalIdealKet_normSq (r : Nat) :
    ‖why24OneRoundLogicalIdealKet r‖ ^ 2 = 1 := by
  change ‖(f1024Why24OddWeightedMatrix r).logicalUOneSeven.toLinearIsometryEquiv
    (why24OneRoundLogicalPlusKet r)‖ ^ 2 = 1
  rw [(f1024Why24OddWeightedMatrix r).logicalUOneSeven.toLinearIsometryEquiv.norm_map]
  exact why24OneRoundLogicalPlusKet_normSq r

/-- The corresponding ideal encoded physical state before syndrome
measurement. -/
noncomputable def why24OneRoundEncodedIdealKet (r : Nat) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  why24OneRoundAmbientEncodingIsometry r
    (why24OneRoundLogicalIdealKet r)

/-- The ideal injected codeword is obtained by applying the actual transversal
`U_1^(7)` gate to the encoded logical plus state. -/
theorem why24OneRoundPhysicalUOneSeven_ideal (r : Nat) :
    f1024Why24OddPhysicalUOneSeven r
        (why24OneRoundAmbientEncodingIsometry r
          (why24OneRoundLogicalPlusKet r)) =
      why24OneRoundEncodedIdealKet r := by
  have hport := f1024Why24OddPhysicalUOneSeven_implements_logicalUOneSeven r
    (why24OneRoundLogicalPlusKet r)
  simp [why24OneRoundEncodedIdealKet, why24OneRoundLogicalIdealKet] at hport ⊢
  exact hport

private theorem why24OneRoundEncodedIdealKet_normSq (r : Nat) :
    ‖why24OneRoundEncodedIdealKet r‖ ^ 2 = 1 := by
  rw [why24OneRoundEncodedIdealKet,
    (why24OneRoundAmbientEncodingIsometry r).norm_map]
  exact why24OneRoundLogicalIdealKet_normSq r

/-- One actual field-Z branch of the noisy transversal injection. -/
noncomputable def why24OneRoundErrorKet (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  wordZTransport error (why24OneRoundEncodedIdealKet r)

private theorem why24OneRoundErrorKet_normSq (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    ‖why24OneRoundErrorKet r error‖ ^ 2 = 1 := by
  change ‖(wordZTransport error).toLinearIsometryEquiv
    (why24OneRoundEncodedIdealKet r)‖ ^ 2 = 1
  rw [(wordZTransport error).toLinearIsometryEquiv.norm_map]
  exact why24OneRoundEncodedIdealKet_normSq r

/-- Pure density of one physical stochastic-Z branch. -/
noncomputable def why24OneRoundErrorDensity (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  DensityOperator.pureDensity (why24OneRoundErrorKet r error)
    (why24OneRoundErrorKet_normSq r error)

/-- Group the actual joint CCZ magic-basis labels through the seventy literal
Appendix cubic gates at every physical F1024 coordinate. -/
def why24OneRoundAppendixErrorWord (r : Nat)
    (error : Fin (why24OneRoundInputCount r) ->
      Qubit.Bitstring (Fin 3)) :
    Why24Word (f1024Why24OddPhysicalSite r) :=
  fun site =>
    why24ComputationalLabelEquiv.symm
      (why24CCZToUOneSevenErrorWord fun gate =>
        error (why24OneRoundCCZLocationEquiv r
          (why24OneRoundPhysicalSiteEquiv r site, gate)))

/-- The actual joint twirl, seventy-to-one corrected conversion, and physical
field-Z injection written as one finite Kraus family.  Each branch consumes a
joint CCZ magic-basis word and emits exactly its encoded Appendix error word. -/
noncomputable def why24OneRoundFrontEndKraus (r : Nat) :
    FiniteKrausFamily
      (Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin (why24OneRoundInputCount r)))
      (ComputationalBasisRegister F1024
        (f1024Why24OddPhysicalSite r)) where
  operator error :=
    (InnerProductSpace.rankOne Complex
      (why24OneRoundErrorKet r (why24OneRoundAppendixErrorWord r error))
      (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)).toLinearMap

private theorem why24OneRoundFrontEndKraus_adjoint_comp (r : Nat)
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3)) :
    (LinearMap.adjoint (why24OneRoundFrontEndKraus r |>.operator error)).comp
        (why24OneRoundFrontEndKraus r |>.operator error) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
        (why24JointCCZMagicBasisKet
          (why24OneRoundInputCount r) error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (why24OneRoundErrorKet r (why24OneRoundAppendixErrorWord r error))
        (why24JointCCZMagicBasisKet
          (why24OneRoundInputCount r) error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
        (why24OneRoundErrorKet r
          (why24OneRoundAppendixErrorWord r error))).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (why24OneRoundErrorKet r (why24OneRoundAppendixErrorWord r error))
      (why24JointCCZMagicBasisKet
        (why24OneRoundInputCount r) error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [why24OneRoundFrontEndKraus]
  rw [hadjoint]
  have hnormSq :
      (↑‖why24OneRoundErrorKet r
        (why24OneRoundAppendixErrorWord r error)‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact why24OneRoundErrorKet_normSq r
      (why24OneRoundAppendixErrorWord r error)
  simp [LinearMap.comp_apply, hnormSq]

/-- Completeness of the actual joint twirl/conversion/injection front end. -/
theorem why24OneRoundFrontEndInstrument_complete (r : Nat) :
    (why24OneRoundFrontEndKraus r).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [why24OneRoundFrontEndKraus_adjoint_comp]
  have hport := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id
      (why24JointCCZMagicBasis (why24OneRoundInputCount r)))
  simp [why24JointCCZMagicBasisKet] at hport ⊢
  exact hport

/-- The measured joint CCZ word is retained as the classical branch record. -/
noncomputable def why24OneRoundFrontEndInstrument (r : Nat) :
    FiniteInstrument
      (Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
      (Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
      (Why24CCZRegister (Fin (why24OneRoundInputCount r)))
      (ComputationalBasisRegister F1024
        (f1024Why24OddPhysicalSite r)) where
  kraus := why24OneRoundFrontEndKraus r
  observe := id

/-- The CPTP joint twirl, corrected Appendix conversion, and field-Z
injection channel consumed by the one-round run. -/
noncomputable def why24OneRoundFrontEndChannel (r : Nat) :
    QuantumChannel
      (Why24CCZRegister (Fin (why24OneRoundInputCount r)))
      (ComputationalBasisRegister F1024
        (f1024Why24OddPhysicalSite r)) :=
  (why24OneRoundFrontEndKraus r).toQuantumChannel
    (why24OneRoundFrontEndInstrument_complete r)

private theorem why24MeasurePrepare_sandwich
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (output : K) (input : H) (A : Operator H) :
    (InnerProductSpace.rankOne Complex output input).toLinearMap.comp
        (A.comp (LinearMap.adjoint
          (InnerProductSpace.rankOne Complex output input).toLinearMap)) =
      (inner Complex input (A input)) •
        (InnerProductSpace.rankOne Complex output output).toLinearMap := by
  have hadjoint :
      LinearMap.adjoint
          (InnerProductSpace.rankOne Complex output input).toLinearMap =
        (InnerProductSpace.rankOne Complex input output).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex output input).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  rw [hadjoint]
  ext vector
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    smul_smul, mul_comm]

private noncomputable def why24OneRoundJointBornWeight (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3)) :
    Real :=
  (inner Complex
    (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
    ((preparation.branchDensity fault).toOperator
      (why24JointCCZMagicBasisKet
        (why24OneRoundInputCount r) error))).re

private theorem why24OneRoundBranchDensity_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    (preparation.branchDensity fault).toOperator =
      ∑ index : Fin (preparation.faultOperation fault).krausCount,
        (InnerProductSpace.rankOne Complex
          ((preparation.faultOperation fault).kraus.operator index
            (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) 0))
          ((preparation.faultOperation fault).kraus.operator index
            (why24JointCCZMagicBasisKet
              (why24OneRoundInputCount r) 0))).toLinearMap := by
  rw [Why24LocalStochasticPreparation.branchDensity,
    QuantumChannel.mapDensity_toOperator,
    Why24CCZFaultOperation.channel,
    FiniteKrausFamily.toQuantumChannel_apply_sum,
    why24IdealCCZRegisterDensity_toOperator]
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]

private theorem why24OneRoundJointBornWeight_nonneg (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3)) :
    0 <= why24OneRoundJointBornWeight r preparation fault error := by
  exact (preparation.branchDensity fault).positive.re_inner_nonneg_right _

private theorem why24OneRoundJointBornWeight_sum (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    (∑ error, why24OneRoundJointBornWeight r preparation fault error) = 1 := by
  have htrace := (preparation.branchDensity fault).trace_one
  rw [LinearMap.trace_eq_sum_inner
    (preparation.branchDensity fault).toOperator
    (why24JointCCZMagicBasis (why24OneRoundInputCount r))] at htrace
  have hre := congrArg Complex.re htrace
  simp [why24OneRoundJointBornWeight, why24JointCCZMagicBasisKet,
    Complex.re_sum] at hre ⊢
  exact hre

private theorem why24OneRoundFrontEnd_branchDensity_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    ((why24OneRoundFrontEndChannel r).mapDensity
      (preparation.branchDensity fault)).toOperator =
      ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
        (why24OneRoundJointBornWeight r preparation fault error : Complex) •
          (why24OneRoundErrorDensity r
            (why24OneRoundAppendixErrorWord r error)).toOperator := by
  rw [QuantumChannel.mapDensity_toOperator,
    why24OneRoundFrontEndChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro error _
  simp only [why24OneRoundFrontEndKraus]
  rw [why24MeasurePrepare_sandwich]
  rw [← why24Inner_apply_real_of_positive
    (preparation.branchDensity fault)
    (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)]
  rfl

private theorem why24OneRoundJointBornWeight_eq_zero_of_outside
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
    (site : Fin (why24OneRoundInputCount r))
    (hsite : site ∉ fault) (herror : error site ≠ 0) :
    why24OneRoundJointBornWeight r preparation fault error = 0 := by
  unfold why24OneRoundJointBornWeight
  have hinner :
      inner Complex
        (why24JointCCZMagicBasisKet (why24OneRoundInputCount r) error)
        ((preparation.branchDensity fault).toOperator
          (why24JointCCZMagicBasisKet
            (why24OneRoundInputCount r) error)) = 0 := by
    rw [why24OneRoundBranchDensity_toOperator,
      LinearMap.sum_apply, inner_sum]
    apply Finset.sum_eq_zero
    intro index _
    have hamplitude := why24SupportedOperator_magicAmplitude_eq_zero
      fault
      ((preparation.faultOperation fault).kraus.operator index)
      ((preparation.faultOperation fault).supported index)
      error site hsite herror
    simp [InnerProductSpace.rankOne_apply, hamplitude]
  rw [hinner]
  rfl

private theorem why24OneRoundAppendixErrorWord_exists_gate
    (r : Nat)
    (error : Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3))
    (site : f1024Why24OddPhysicalSite r)
    (herror : why24OneRoundAppendixErrorWord r error site ≠ 0) :
    ∃ gate : Fin 70,
      error (why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate)) ≠ 0 := by
  by_contra hgate
  have hgateZero : ∀ gate : Fin 70,
      error (why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate)) = 0 := by
    intro gate
    by_contra hne
    exact hgate ⟨gate, hne⟩
  apply herror
  have hzero :
      (fun gate : Fin 70 =>
        error (why24OneRoundCCZLocationEquiv r
          (why24OneRoundPhysicalSiteEquiv r site, gate))) = 0 := by
    funext gate
    exact hgateZero gate
  rw [why24OneRoundAppendixErrorWord, hzero,
    why24CCZToUOneSevenErrorWord_zero]
  apply f1024SelectedCoordinates.injective
  rw [f1024SelectedCoordinates_label_symm]
  change (0 : Fin 10 → ZMod 2) = f1024SelectedCoordinates 0
  exact (map_zero f1024SelectedCoordinates).symm

private noncomputable def why24OneRoundDerivedBranchMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (fieldError : Why24Word (f1024Why24OddPhysicalSite r)) : Real :=
  ∑ jointError :
      Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
    if fieldError = why24OneRoundAppendixErrorWord r jointError then
      preparation.faultMass fault *
        why24OneRoundJointBornWeight r preparation fault jointError
    else 0

private theorem why24OneRoundDerivedBranchMass_nonneg (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (fieldError : Why24Word (f1024Why24OddPhysicalSite r)) :
    0 <= why24OneRoundDerivedBranchMass r preparation fault fieldError := by
  exact Finset.sum_nonneg fun jointError _ => by
    split_ifs
    · exact mul_nonneg (preparation.faultMass_nonneg fault)
        (why24OneRoundJointBornWeight_nonneg r preparation fault jointError)
    · exact le_rfl

private theorem why24OneRoundDerivedBranchMass_sum (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r))) :
    (∑ fieldError,
      why24OneRoundDerivedBranchMass r preparation fault fieldError) =
        preparation.faultMass fault := by
  unfold why24OneRoundDerivedBranchMass
  rw [Finset.sum_comm]
  calc
    (∑ jointError :
        Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
      ∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
        if fieldError = why24OneRoundAppendixErrorWord r jointError then
          preparation.faultMass fault *
            why24OneRoundJointBornWeight r preparation fault jointError
        else 0) =
      ∑ jointError :
          Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
        preparation.faultMass fault *
          why24OneRoundJointBornWeight r preparation fault jointError := by
      apply Finset.sum_congr rfl
      intro jointError _
      rw [Finset.sum_eq_single
        (why24OneRoundAppendixErrorWord r jointError)]
      · rw [if_pos rfl]
      · intro fieldError _ hne
        rw [if_neg hne]
      · simp
    _ = preparation.faultMass fault *
        ∑ jointError :
          Fin (why24OneRoundInputCount r) -> Qubit.Bitstring (Fin 3),
          why24OneRoundJointBornWeight r preparation fault jointError := by
      rw [Finset.mul_sum]
    _ = preparation.faultMass fault := by
      rw [why24OneRoundJointBornWeight_sum, mul_one]

private theorem why24OneRoundDerivedBranchMass_error_supported (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (fieldError : Why24Word (f1024Why24OddPhysicalSite r))
    (hmass : why24OneRoundDerivedBranchMass r preparation fault fieldError ≠ 0)
    (site : f1024Why24OddPhysicalSite r) (herror : fieldError site ≠ 0) :
    ∃ gate : Fin 70,
      why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate) ∈ fault := by
  obtain ⟨jointError, _, hjointMass⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hmass
  have hfield :
      fieldError = why24OneRoundAppendixErrorWord r jointError := by
    by_contra hne
    rw [if_neg hne] at hjointMass
    exact hjointMass rfl
  obtain ⟨gate, hgateError⟩ :=
    why24OneRoundAppendixErrorWord_exists_gate r jointError site
      (hfield ▸ herror)
  refine ⟨gate, ?_⟩
  by_contra hnotmem
  have hbornZero := why24OneRoundJointBornWeight_eq_zero_of_outside
    r preparation fault jointError
      (why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site, gate))
      hnotmem hgateError
  rw [if_pos hfield, hbornZero, mul_zero] at hjointMass
  exact hjointMass rfl

/-- Exact finite stochastic-Z realization after twirling and grouping each
seventy-CCZ Appendix circuit into one physical F1024 coordinate.  Its branch
masses refine the original correlated fault-set law; no independence between
errors or between physical coordinates is assumed. -/
private structure Why24OneRoundTwirledConversionLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) where
  branchMass :
    Finset (Fin (why24OneRoundInputCount r)) →
      Why24Word (f1024Why24OddPhysicalSite r) → Real
  branchMass_nonneg : ∀ fault error, 0 ≤ branchMass fault error
  branchMass_sum : ∀ fault,
    (∑ error, branchMass fault error) = preparation.faultMass fault
  error_supported : ∀ fault error,
    branchMass fault error ≠ 0 →
      ∀ site, error site ≠ 0 →
        ∃ gate : Fin 70,
          why24OneRoundCCZLocationEquiv r
            (why24OneRoundPhysicalSiteEquiv r site, gate) ∈ fault

private noncomputable def why24OneRoundDerivedTwirledConversionLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    Why24OneRoundTwirledConversionLaw r preparation where
  branchMass := why24OneRoundDerivedBranchMass r preparation
  branchMass_nonneg := why24OneRoundDerivedBranchMass_nonneg r preparation
  branchMass_sum := why24OneRoundDerivedBranchMass_sum r preparation
  error_supported :=
    why24OneRoundDerivedBranchMass_error_supported r preparation

namespace Why24OneRoundTwirledConversionLaw

variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}

/-- Total probability of one physical field-Z error word, obtained by
forgetting the correlated source fault-set record. -/
private noncomputable def errorMass
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) : Real :=
  ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
    law.branchMass fault error

private theorem errorMass_nonneg
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    0 ≤ law.errorMass error := by
  exact Finset.sum_nonneg (fun _ _ => law.branchMass_nonneg _ _)

private theorem errorMass_sum
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    ∑ error, law.errorMass error = 1 := by
  simp only [errorMass]
  rw [Finset.sum_comm]
  simp_rw [law.branchMass_sum]
  exact preparation.faultMass_sum

end Why24OneRoundTwirledConversionLaw

/-- The actual correlated physical input to syndrome measurement: the finite
stochastic-Z mixture obtained from the original fault-set law after twirling
and the seventy-to-one Appendix grouping. -/
private noncomputable def why24OneRoundPreparedPhysicalDensityForLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  DensityOperator.convexCombination Finset.univ law.errorMass
    (why24OneRoundErrorDensity r)
    (by intro error _; exact law.errorMass_nonneg error)
    (by simpa using law.errorMass_sum)

private theorem why24OneRoundDerivedMixture_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundPreparedPhysicalDensityForLaw r preparation
      (why24OneRoundDerivedTwirledConversionLaw r preparation)).toOperator =
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
          ((preparation.faultMass fault *
              why24OneRoundJointBornWeight r preparation fault error : Real) :
            Complex) •
            (why24OneRoundErrorDensity r
              (why24OneRoundAppendixErrorWord r error)).toOperator := by
  rw [why24OneRoundPreparedPhysicalDensityForLaw,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  simp only [Why24OneRoundTwirledConversionLaw.errorMass,
    why24OneRoundDerivedTwirledConversionLaw,
    why24OneRoundDerivedBranchMass]
  calc
    (∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
        ((∑ fault : Finset (Fin (why24OneRoundInputCount r)),
          ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
            if fieldError = why24OneRoundAppendixErrorWord r error then
              preparation.faultMass fault *
                why24OneRoundJointBornWeight r preparation fault error
            else 0 : Real) : Complex) •
          (why24OneRoundErrorDensity r fieldError).toOperator) =
      ∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
        ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
          ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
            ((if fieldError = why24OneRoundAppendixErrorWord r error then
                preparation.faultMass fault *
                  why24OneRoundJointBornWeight r preparation fault error
              else 0 : Real) : Complex) •
              (why24OneRoundErrorDensity r fieldError).toOperator := by
        apply Finset.sum_congr rfl
        intro fieldError _
        rw [Complex.ofReal_sum, Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro fault _
        rw [Complex.ofReal_sum, Finset.sum_smul]
    _ = ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
          ∑ fieldError : Why24Word (f1024Why24OddPhysicalSite r),
            ((if fieldError = why24OneRoundAppendixErrorWord r error then
                preparation.faultMass fault *
                  why24OneRoundJointBornWeight r preparation fault error
              else 0 : Real) : Complex) •
              (why24OneRoundErrorDensity r fieldError).toOperator := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro fault _
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro fault _
      apply Finset.sum_congr rfl
      intro error _
      rw [Finset.sum_eq_single (why24OneRoundAppendixErrorWord r error)]
      · rw [if_pos rfl]
      · intro fieldError _ hne
        rw [if_neg hne]
        simp
      · simp

private theorem why24OneRoundFrontEnd_prepared_toOperator (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    ((why24OneRoundFrontEndChannel r).mapDensity
      preparation.why24LocalStochasticPreparedDensity).toOperator =
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ error : Fin (why24OneRoundInputCount r) → Qubit.Bitstring (Fin 3),
          ((preparation.faultMass fault *
              why24OneRoundJointBornWeight r preparation fault error : Real) :
            Complex) •
            (why24OneRoundErrorDensity r
              (why24OneRoundAppendixErrorWord r error)).toOperator := by
  rw [QuantumChannel.mapDensity_toOperator,
    preparation.why24LocalStochasticPreparedDensity_toOperator, map_sum]
  apply Finset.sum_congr rfl
  intro fault _
  rw [map_smul, ← QuantumChannel.mapDensity_toOperator,
    why24OneRoundFrontEnd_branchDensity_toOperator, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro error _
  rw [smul_smul, ← Complex.ofReal_mul]

/-- The actual correlated physical input to syndrome measurement, with its
finite stochastic branch law derived internally from the joint preparation. -/
noncomputable def why24OneRoundPreparedPhysicalDensity (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  why24OneRoundPreparedPhysicalDensityForLaw r preparation
    (why24OneRoundDerivedTwirledConversionLaw r preparation)

/-- The internally derived finite branch law is exactly the output of the
actual joint twirl, corrected seventy-to-one conversion, and field injection
channel on the supplied correlated preparation. -/
theorem why24OneRoundPreparedPhysicalDensity_eq_frontEnd (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24OneRoundPreparedPhysicalDensity r preparation =
      (why24OneRoundFrontEndChannel r).mapDensity
        preparation.why24LocalStochasticPreparedDensity := by
  apply DensityOperator.ext_toOperator
  rw [why24OneRoundPreparedPhysicalDensity,
    why24OneRoundDerivedMixture_toOperator,
    why24OneRoundFrontEnd_prepared_toOperator]

/-- Normalized ideal physical fallback used only away from the uniquely
permitted correlated marginal family at the total shared run interface. -/
noncomputable def why24OneRoundIdealPhysicalDensity (r : Nat) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  why24OneRoundErrorDensity r 0

/-- Shared-run preparation adaptor.  At the actual permitted singleton
marginals it returns the joint correlated preparation's stochastic-Z image;
the off-regime branch only makes the function total. -/
noncomputable def why24CorrelatedPrepareInput (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (inputs : ResourceInput (why24OneRoundInputCount r) Why24CCZSpace) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  if inputs = why24LocalStochasticResourceInputs preparation then
    why24OneRoundPreparedPhysicalDensity r preparation
  else why24OneRoundIdealPhysicalDensity r

theorem why24CorrelatedPrepareInput_actual (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24CorrelatedPrepareInput r preparation
        (why24LocalStochasticResourceInputs preparation) =
      why24OneRoundPreparedPhysicalDensity r preparation := by
  rw [why24CorrelatedPrepareInput, if_pos rfl]

/-- The deterministic active-correction run before coherent inverse
encoding.  Every physical syndrome is accepted. -/
noncomputable def why24OneRoundRunBeforeDecode (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    DistillationRun Why24CCZSpace
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r)) :=
  FiniteInstrument.binaryDistillationRun
    (Resource := Why24CCZSpace)
    (H := ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
    (K := ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
    (why24OneRoundInstrument.{0} r) why24OneRoundAccepts.{0}
    (why24OneRoundInstrument_complete.{0} r)
    (why24OneRoundInputCount r)
    (why24LocalStochasticResourceInputs preparation)
    (why24CorrelatedPrepareInput r preparation)
    (why24OneRoundIdealPhysicalDensity r)

/-- The full finite one-round run, postprocessed by the actual total inverse
encoding channel. -/
noncomputable def why24OneRoundRun (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    DistillationRun Why24CCZSpace
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  (why24OneRoundRunBeforeDecode r preparation).postprocess (why24OneRoundDecoderChannel r)

/-- Because every syndrome branch is actively corrected rather than
discarded, the actual complete run succeeds with probability one. -/
theorem why24OneRoundRun_successProbability_eq_one (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundRun r preparation).successProbability = 1 := by
  rw [why24OneRoundRun, DistillationRun.postprocess_successProbability,
    why24OneRoundRunBeforeDecode,
    FiniteInstrument.binaryDistillationRun_successProbability,
    FiniteInstrument.binaryCoarsen_bornWeight_accepted]
  simpa [why24OneRoundAccepts] using
    (why24OneRoundInstrument r).sum_bornWeight_eq_one
      (why24OneRoundInstrument_complete r)
      (why24CorrelatedPrepareInput r preparation
        (why24LocalStochasticResourceInputs preparation))

/-! ## Finite correlated failure bound -/

/-- The actual total mass of stochastic field-error branches outside the
proved AG decoding radius. -/
private noncomputable def why24OneRoundFailureMassForLaw (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) : Real :=
  ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
    ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
      if f1024Why24OddDecodingRadius r < HammingWeight error then
        law.branchMass fault error
      else 0

private theorem why24OneRoundFailureMass_nonneg (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    0 ≤ why24OneRoundFailureMassForLaw r preparation law := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun error _ => by
    split_ifs
    · exact law.branchMass_nonneg _ error
    · exact le_rfl

private def why24OneRoundFaultFails (r : Nat)
    {preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (fault : Finset (Fin (why24OneRoundInputCount r))) : Prop :=
  ∃ error : Why24Word (f1024Why24OddPhysicalSite r),
    f1024Why24OddDecodingRadius r < HammingWeight error ∧
      law.branchMass fault error ≠ 0

private theorem why24OneRoundFailureMass_le_failingFaultMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    why24OneRoundFailureMassForLaw r preparation law ≤
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        if why24OneRoundFaultFails r law fault then
          preparation.faultMass fault
        else 0 := by
  unfold why24OneRoundFailureMassForLaw
  apply Finset.sum_le_sum
  intro fault _
  by_cases hfails : why24OneRoundFaultFails r law fault
  · rw [if_pos hfails]
    calc
      (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
          if f1024Why24OddDecodingRadius r < HammingWeight error then
            law.branchMass fault error
          else 0) ≤
          ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
            law.branchMass fault error := by
              apply Finset.sum_le_sum
              intro error _
              by_cases herror :
                  f1024Why24OddDecodingRadius r < HammingWeight error
              · rw [if_pos herror]
              · rw [if_neg herror]
                exact law.branchMass_nonneg fault error
      _ = preparation.faultMass fault := law.branchMass_sum fault
  · rw [if_neg hfails]
    have hzero : ∀ error : Why24Word (f1024Why24OddPhysicalSite r),
        (if f1024Why24OddDecodingRadius r < HammingWeight error then
            law.branchMass fault error
          else 0) = 0 := by
      intro error
      by_cases herror :
          f1024Why24OddDecodingRadius r < HammingWeight error
      · rw [if_pos herror]
        by_contra hmass
        exact hfails ⟨error, herror, hmass⟩
      · rw [if_neg herror]
    simp_rw [hzero]
    simp

/-- Source CCZ locations witnessing one selected collection of bad physical
coordinates.  The gate choice is retained explicitly, so counting witnesses
produces the source factor `70^(t+1)` instead of replacing the correlated law
by an IID law. -/
private noncomputable def why24OneRoundWitnessLocations (r : Nat)
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    Finset (Fin (why24OneRoundInputCount r)) :=
  sites.attach.image fun site =>
    why24OneRoundCCZLocationEquiv r
      (why24OneRoundPhysicalSiteEquiv r site.1, gate site)

@[simp]
private theorem why24OneRoundWitnessLocations_card (r : Nat)
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    (why24OneRoundWitnessLocations r sites gate).card = sites.card := by
  unfold why24OneRoundWitnessLocations
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro left _ right _ heq
    apply Subtype.ext
    exact (why24OneRoundPhysicalSiteEquiv r).injective
      (congrArg Prod.fst ((why24OneRoundCCZLocationEquiv r).injective heq))

private theorem why24OneRound_exists_witness_of_faultFails (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation)
    (fault : Finset (Fin (why24OneRoundInputCount r)))
    (hfails : why24OneRoundFaultFails r law fault) :
    ∃ sites ∈ (Finset.univ :
        Finset (f1024Why24OddPhysicalSite r)).powersetCard
          (f1024Why24OddDecodingRadius r + 1),
      ∃ gate : {site // site ∈ sites} → Fin 70,
        why24OneRoundWitnessLocations r sites gate ⊆ fault := by
  rcases hfails with ⟨error, hweight, hmass⟩
  have hcard : f1024Why24OddDecodingRadius r + 1 ≤
      (hammingSupport error).card := by
    rw [← HammingWeight_eq_card_hammingSupport]
    omega
  obtain ⟨sites, hsites, hsitesCard⟩ :=
    Finset.exists_subset_card_eq hcard
  have hsitesPowerset : sites ∈
      (Finset.univ : Finset (f1024Why24OddPhysicalSite r)).powersetCard
        (f1024Why24OddDecodingRadius r + 1) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ sites, hsitesCard⟩
  have hgate : ∀ site : {site // site ∈ sites}, ∃ gate : Fin 70,
      why24OneRoundCCZLocationEquiv r
        (why24OneRoundPhysicalSiteEquiv r site.1, gate) ∈ fault := by
    intro site
    apply law.error_supported fault error hmass site.1
    have hsupport : site.1 ∈ hammingSupport error := hsites site.2
    simpa [hammingSupport] using hsupport
  choose gate hgate using hgate
  refine ⟨sites, hsitesPowerset, gate, ?_⟩
  intro location hlocation
  rw [why24OneRoundWitnessLocations, Finset.mem_image] at hlocation
  rcases hlocation with ⟨site, _hsite, rfl⟩
  exact hgate site

private noncomputable def why24OneRoundWitnessFaultMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) : Real :=
  ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
    if why24OneRoundWitnessLocations r sites gate ⊆ fault then
      preparation.faultMass fault
    else 0

private theorem why24OneRoundWitnessFaultMass_nonneg (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    0 ≤ why24OneRoundWitnessFaultMass r preparation sites gate := by
  exact Finset.sum_nonneg fun fault _ => by
    split_ifs
    · exact preparation.faultMass_nonneg fault
    · exact le_rfl

private theorem why24OneRoundWitnessFaultMass_le (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (sites : Finset (f1024Why24OddPhysicalSite r))
    (gate : {site // site ∈ sites} → Fin 70) :
    why24OneRoundWitnessFaultMass r preparation sites gate ≤
      preparation.rate ^ sites.card := by
  exact preparation.why24LocalStochastic_tail_maxRate
    (why24OneRoundWitnessLocations r sites gate) |>.trans_eq (by simp)

private theorem why24OneRound_failingFaultMass_le_witnessSum (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    (∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        if why24OneRoundFaultFails r law fault then
          preparation.faultMass fault
        else 0) ≤
      ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard
              (f1024Why24OddDecodingRadius r + 1),
        ∑ gate : {site // site ∈ sites} → Fin 70,
          why24OneRoundWitnessFaultMass r preparation sites gate := by
  calc
    (∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        if why24OneRoundFaultFails r law fault then
          preparation.faultMass fault
        else 0) ≤
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        ∑ sites ∈
            (Finset.univ : Finset
              (f1024Why24OddPhysicalSite r)).powersetCard
                (f1024Why24OddDecodingRadius r + 1),
          ∑ gate : {site // site ∈ sites} → Fin 70,
            if why24OneRoundWitnessLocations r sites gate ⊆ fault then
              preparation.faultMass fault
            else 0 := by
      apply Finset.sum_le_sum
      intro fault _
      by_cases hfails : why24OneRoundFaultFails r law fault
      · rw [if_pos hfails]
        obtain ⟨sites, hsites, gate, hsubset⟩ :=
          why24OneRound_exists_witness_of_faultFails r preparation law fault hfails
        have hgateNonneg : ∀ candidate : {site // site ∈ sites} → Fin 70,
            0 ≤ if why24OneRoundWitnessLocations r sites candidate ⊆ fault then
              preparation.faultMass fault
            else 0 := by
          intro candidate
          split_ifs
          · exact preparation.faultMass_nonneg fault
          · exact le_rfl
        have hgateLe : preparation.faultMass fault ≤
            ∑ candidate : {site // site ∈ sites} → Fin 70,
              if why24OneRoundWitnessLocations r sites candidate ⊆ fault then
                preparation.faultMass fault
              else 0 := by
          calc
            preparation.faultMass fault =
                if why24OneRoundWitnessLocations r sites gate ⊆ fault then
                  preparation.faultMass fault
                else 0 := by rw [if_pos hsubset]
            _ ≤ _ := Finset.single_le_sum
              (fun candidate _ => hgateNonneg candidate) (Finset.mem_univ gate)
        have hsiteNonneg : ∀ candidate ∈
            (Finset.univ : Finset
              (f1024Why24OddPhysicalSite r)).powersetCard
                (f1024Why24OddDecodingRadius r + 1),
            0 ≤ ∑ candidateGate : {site // site ∈ candidate} → Fin 70,
              if why24OneRoundWitnessLocations r candidate candidateGate ⊆ fault then
                preparation.faultMass fault
              else 0 := by
          intro candidate _
          exact Finset.sum_nonneg fun candidateGate _ => by
            split_ifs
            · exact preparation.faultMass_nonneg fault
            · exact le_rfl
        have hsiteLe :
            (∑ candidate : {site // site ∈ sites} → Fin 70,
                if why24OneRoundWitnessLocations r sites candidate ⊆ fault then
                  preparation.faultMass fault
                else 0) ≤
              ∑ candidate ∈
                  (Finset.univ : Finset
                    (f1024Why24OddPhysicalSite r)).powersetCard
                      (f1024Why24OddDecodingRadius r + 1),
                ∑ candidateGate : {site // site ∈ candidate} → Fin 70,
                  if why24OneRoundWitnessLocations r candidate candidateGate ⊆ fault then
                    preparation.faultMass fault
                  else 0 :=
          Finset.single_le_sum hsiteNonneg hsites
        exact hgateLe.trans hsiteLe
      · rw [if_neg hfails]
        exact Finset.sum_nonneg fun sites _ =>
          Finset.sum_nonneg fun gate _ => by
            split_ifs
            · exact preparation.faultMass_nonneg fault
            · exact le_rfl
    _ = ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard
              (f1024Why24OddDecodingRadius r + 1),
        ∑ gate : {site // site ∈ sites} → Fin 70,
          why24OneRoundWitnessFaultMass r preparation sites gate := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sites _
      rw [Finset.sum_comm]
      rfl

/-- The correlated failure mass obeys the literal source-scale finite union
bound: choose the `t+1` bad physical coordinates, then one of the seventy
source CCZ locations supporting each coordinate. -/
private theorem why24OneRoundFailureMassForLaw_le (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    why24OneRoundFailureMassForLaw r preparation law ≤
      (Nat.choose (f1024Why24OddLength r)
        (f1024Why24OddDecodingRadius r + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius r + 1) := by
  let k := f1024Why24OddDecodingRadius r + 1
  calc
    why24OneRoundFailureMassForLaw r preparation law ≤
        ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
          if why24OneRoundFaultFails r law fault then
            preparation.faultMass fault
          else 0 :=
      why24OneRoundFailureMass_le_failingFaultMass r preparation law
    _ ≤ ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard k,
        ∑ gate : {site // site ∈ sites} → Fin 70,
          why24OneRoundWitnessFaultMass r preparation sites gate :=
      why24OneRound_failingFaultMass_le_witnessSum r preparation law
    _ ≤ ∑ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard k,
        ∑ _gate : {site // site ∈ sites} → Fin 70,
          preparation.rate ^ k := by
      apply Finset.sum_le_sum
      intro sites hsites
      apply Finset.sum_le_sum
      intro gate _
      have hcard := (Finset.mem_powersetCard.mp hsites).2
      simpa [k, hcard] using
        why24OneRoundWitnessFaultMass_le r preparation sites gate
    _ = (Nat.choose (f1024Why24OddLength r) k : Real) *
          (70 * preparation.rate) ^ k := by
      have hinner : ∀ sites ∈
          (Finset.univ : Finset
            (f1024Why24OddPhysicalSite r)).powersetCard k,
          (∑ _gate : {site // site ∈ sites} → Fin 70,
              preparation.rate ^ k) =
            (70 : Real) ^ k * preparation.rate ^ k := by
        intro sites hsites
        have hcard := (Finset.mem_powersetCard.mp hsites).2
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [Fintype.card_fin, hcard]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul,
        Finset.card_powersetCard, Finset.card_univ,
        show Fintype.card (f1024Why24OddPhysicalSite r) =
            f1024Why24OddLength r by rfl]
      ring

/-- The actual total mass of internally derived physical error branches
outside the proved AG decoding radius. -/
noncomputable def why24OneRoundFailureMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) : Real :=
  why24OneRoundFailureMassForLaw r preparation
    (why24OneRoundDerivedTwirledConversionLaw r preparation)

/-- The derived correlated failure mass obeys the literal source-scale finite
union bound. -/
theorem why24OneRoundFailureMass_le (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24OneRoundFailureMass r preparation ≤
      (Nat.choose (f1024Why24OddLength r)
        (f1024Why24OddDecodingRadius r + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius r + 1) := by
  simpa [why24OneRoundFailureMass] using
    why24OneRoundFailureMassForLaw_le r preparation
      (why24OneRoundDerivedTwirledConversionLaw r preparation)

/-! ## Actual decoded output and trace-distance error -/

/-- The normalized logical target produced by the ideal transversal
`U_1^(7)` branch. -/
noncomputable def why24OneRoundLogicalIdealDensity (r : Nat) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  DensityOperator.pureDensity (why24OneRoundLogicalIdealKet r)
    (why24OneRoundLogicalIdealKet_normSq r)

/-- The physical state after measuring the actual syndrome and applying the
AG decoder's active correction on one stochastic-Z branch. -/
private noncomputable def why24OneRoundCorrectedErrorKet (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r) :=
  why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
    (why24OneRoundSyndromeProjector r
      (f1024Why24OddZSyndromeMap r error)
      (why24OneRoundErrorKet r error))

private theorem why24OneRoundCorrectedErrorKet_eq_encoded_of_weight_le
    (r : Nat) (error : Why24Word (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24OneRoundCorrectedErrorKet r error =
      why24OneRoundEncodedIdealKet r := by
  unfold why24OneRoundCorrectedErrorKet why24OneRoundErrorKet
  exact why24OneRoundCorrection_restores_encoded r error
    (why24OneRoundLogicalIdealKet r) herror

/-- Expanding the real bound syndrome/correction instrument on one pure
stochastic-Z branch leaves the pure actively corrected branch. -/
private theorem why24OneRoundInstrument_inducedMap_errorDensity (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    (why24OneRoundInstrument r).kraus.inducedMap
        (why24OneRoundErrorDensity r error).toOperator =
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCorrectedErrorKet r error)
        (why24OneRoundCorrectedErrorKet r error)).toLinearMap := by
  rw [why24OneRoundErrorDensity, DensityOperator.pureDensity_toOperator]
  rw [why24OneRoundInstrument,
    FiniteInstrument.bind_inducedMap_apply]
  change
    (∑ syndrome : f1024Why24OddZSyndrome r,
      (why24OneRoundCorrectionInstrument r syndrome).kraus.inducedMap
        ((why24OneRoundSyndromeProjector r syndrome).comp
          ((InnerProductSpace.rankOne Complex
            (why24OneRoundErrorKet r error)
            (why24OneRoundErrorKet r error)).toLinearMap.comp
              (LinearMap.adjoint
                (why24OneRoundSyndromeProjector r syndrome))))) = _
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
  simp only [FiniteKrausFamily.inducedMap_apply,
    why24OneRoundCorrectionInstrument, Fintype.sum_unique]
  simp_rw [why24LinearMap_comp_rankOne_comp_adjoint]
  rw [Finset.sum_eq_single (f1024Why24OddZSyndromeMap r error)]
  · change
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
          (why24OneRoundSyndromeProjector r
            (f1024Why24OddZSyndromeMap r error)
            (why24OneRoundErrorKet r error)))
        (why24OneRoundCorrection r (f1024Why24OddZSyndromeMap r error)
          (why24OneRoundSyndromeProjector r
            (f1024Why24OddZSyndromeMap r error)
            (why24OneRoundErrorKet r error)))).toLinearMap = _
    rfl
  · intro syndrome _ hsyndrome
    change
      (InnerProductSpace.rankOne Complex
        (why24OneRoundCorrection r syndrome
          (why24OneRoundSyndromeProjector r syndrome
            (wordZTransport error
              ((f1024Why24OddWeightedMatrix r).encodedCode.encode
                (why24OneRoundLogicalIdealKet r)))))
        (why24OneRoundCorrection r syndrome
          (why24OneRoundSyndromeProjector r syndrome
            (wordZTransport error
              ((f1024Why24OddWeightedMatrix r).encodedCode.encode
                (why24OneRoundLogicalIdealKet r)))))).toLinearMap = 0
    rw [
      why24OneRoundSyndromeProjector_apply_wordZ_encoded,
      if_neg hsyndrome]
    change (InnerProductSpace.rankOne Complex
      ((why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap 0)
      ((why24OneRoundCorrection r syndrome).toLinearEquiv.toLinearMap 0)).toLinearMap = 0
    rw [map_zero]
    apply LinearMap.ext
    intro vector
    simp only [InnerProductSpace.toLinearMap_rankOne,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply, smul_zero,
      LinearMap.zero_apply]
  · simp

/-- The complete one-round physical channel: actual syndrome measurement,
active AG correction, and total inverse encoding. -/
noncomputable def why24OneRoundPhysicalChannel (r : Nat) :
    QuantumChannel
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  QuantumChannel.comp (why24OneRoundDecoderChannel r)
    ((why24OneRoundInstrument.{0} r).kraus.toQuantumChannel
      (why24OneRoundInstrument_complete.{0} r))

/-- The actual decoded density associated with one stochastic field-error
branch of the correlated preparation. -/
noncomputable def why24OneRoundDecodedErrorDensity (r : Nat)
    (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    DensityOperator
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) :=
  (why24OneRoundPhysicalChannel r).mapDensity
    (why24OneRoundErrorDensity r error)

private theorem why24OneRoundDecodedErrorDensity_eq_ideal_of_weight_le
    (r : Nat) (error : Why24Word (f1024Why24OddPhysicalSite r))
    (herror : HammingWeight error ≤ f1024Why24OddDecodingRadius r) :
    why24OneRoundDecodedErrorDensity r error =
      why24OneRoundLogicalIdealDensity r := by
  apply DensityOperator.ext_toOperator
  rw [why24OneRoundDecodedErrorDensity, QuantumChannel.mapDensity_toOperator,
    why24OneRoundPhysicalChannel, QuantumChannel.comp_apply,
    FiniteKrausFamily.toQuantumChannel_apply,
    why24OneRoundInstrument_inducedMap_errorDensity,
    why24OneRoundCorrectedErrorKet_eq_encoded_of_weight_le r error herror,
    why24OneRoundEncodedIdealKet,
    why24OneRoundDecoderChannel_rankOne_encoded,
    why24OneRoundLogicalIdealDensity,
    DensityOperator.pureDensity_toOperator]

/-- The literal complete run output is the finite decoded mixture induced by
the same correlated branch law; this is not an independently prepared output
distribution. -/
private theorem why24OneRoundRun_rawOutput_toOperator_eq_decodedErrorSum
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundRun r preparation).rawOutput.toOperator =
      ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        ((why24OneRoundDerivedTwirledConversionLaw r preparation).errorMass
          error : Complex) •
          (why24OneRoundDecodedErrorDensity r error).toOperator := by
  rw [why24OneRoundRun, DistillationRun.postprocess_rawOutput]
  change why24OneRoundDecoderChannel r
      (((why24OneRoundInstrument r).kraus.toQuantumChannel
        (why24OneRoundInstrument_complete r))
        (why24CorrelatedPrepareInput r preparation
          (why24LocalStochasticResourceInputs preparation)).toOperator) = _
  rw [why24CorrelatedPrepareInput_actual,
    why24OneRoundPreparedPhysicalDensity,
    why24OneRoundPreparedPhysicalDensityForLaw,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  simp only [map_sum, map_smul, why24OneRoundDecodedErrorDensity,
    why24OneRoundPhysicalChannel, QuantumChannel.mapDensity_toOperator,
    QuantumChannel.comp_apply]

private theorem why24OneRoundFailureMass_eq_errorMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    why24OneRoundFailureMassForLaw r preparation law =
      ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        if f1024Why24OddDecodingRadius r < HammingWeight error then
          law.errorMass error
        else 0 := by
  unfold why24OneRoundFailureMassForLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro error _
  change
    (∑ fault : Finset (Fin (why24OneRoundInputCount r)),
      if f1024Why24OddDecodingRadius r < HammingWeight error then
        law.branchMass fault error
      else 0) =
    if f1024Why24OddDecodingRadius r < HammingWeight error then
      ∑ fault : Finset (Fin (why24OneRoundInputCount r)),
        law.branchMass fault error
    else 0
  by_cases herror : f1024Why24OddDecodingRadius r < HammingWeight error
  · simp_rw [if_pos herror]
  · simp_rw [if_neg herror]
    simp

private theorem why24OneRoundDecodedErrorDensity_traceNorm_sub_ideal_le_two
    (r : Nat) (error : Why24Word (f1024Why24OddPhysicalSite r)) :
    traceNorm ((why24OneRoundDecodedErrorDensity r error).toOperator -
      (why24OneRoundLogicalIdealDensity r).toOperator) ≤ 2 := by
  calc
    traceNorm ((why24OneRoundDecodedErrorDensity r error).toOperator -
        (why24OneRoundLogicalIdealDensity r).toOperator) ≤
      traceNorm (why24OneRoundDecodedErrorDensity r error).toOperator +
        traceNorm (-(why24OneRoundLogicalIdealDensity r).toOperator) := by
      simpa [sub_eq_add_neg] using
        traceNorm_add_le
          (why24OneRoundDecodedErrorDensity r error).toOperator
          (-(why24OneRoundLogicalIdealDensity r).toOperator)
    _ = 2 := by
      rw [DensityOperator.traceNorm_eq_one, traceNorm_neg,
        DensityOperator.traceNorm_eq_one]
      norm_num

/-- The centered contribution of exactly those physical field-error branches
outside the proved AG decoding radius. -/
private noncomputable def why24OneRoundDecodedResidual (r : Nat)
    {preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    Operator (ComputationalBasisRegister F1024
      (f1024Why24OddLogical r)) :=
  ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
    if f1024Why24OddDecodingRadius r < HammingWeight error then
      (law.errorMass error : Complex) •
        ((why24OneRoundDecodedErrorDensity r error).toOperator -
          (why24OneRoundLogicalIdealDensity r).toOperator)
    else 0

private theorem why24OneRoundRun_sub_ideal_eq_decodedResidual (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundRun r preparation).rawOutput.toOperator -
        (why24OneRoundLogicalIdealDensity r).toOperator =
      why24OneRoundDecodedResidual r
        (why24OneRoundDerivedTwirledConversionLaw r preparation) := by
  let law := why24OneRoundDerivedTwirledConversionLaw r preparation
  change (why24OneRoundRun r preparation).rawOutput.toOperator -
      (why24OneRoundLogicalIdealDensity r).toOperator =
    why24OneRoundDecodedResidual r law
  rw [why24OneRoundRun_rawOutput_toOperator_eq_decodedErrorSum]
  have hmass :
      (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
          (law.errorMass error : Complex)) = 1 := by
    rw [← Complex.ofReal_sum, law.errorMass_sum]
    exact Complex.ofReal_one
  calc
    (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        (law.errorMass error : Complex) •
          (why24OneRoundDecodedErrorDensity r error).toOperator) -
        (why24OneRoundLogicalIdealDensity r).toOperator =
      (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        (law.errorMass error : Complex) •
          (why24OneRoundDecodedErrorDensity r error).toOperator) -
        (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
          (law.errorMass error : Complex)) •
            (why24OneRoundLogicalIdealDensity r).toOperator := by
      rw [hmass, one_smul]
    _ = ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        ((law.errorMass error : Complex) •
            (why24OneRoundDecodedErrorDensity r error).toOperator -
          (law.errorMass error : Complex) •
            (why24OneRoundLogicalIdealDensity r).toOperator) := by
      rw [Finset.sum_smul, Finset.sum_sub_distrib]
    _ = why24OneRoundDecodedResidual r law := by
      unfold why24OneRoundDecodedResidual
      apply Finset.sum_congr rfl
      intro error _
      by_cases herror : f1024Why24OddDecodingRadius r < HammingWeight error
      · rw [if_pos herror]
        exact (smul_sub (law.errorMass error : Complex)
          (why24OneRoundDecodedErrorDensity r error).toOperator
          (why24OneRoundLogicalIdealDensity r).toOperator).symm
      · rw [if_neg herror,
          why24OneRoundDecodedErrorDensity_eq_ideal_of_weight_le r error
            (Nat.le_of_not_gt herror)]
        simp

private theorem why24OneRoundDecodedResidual_traceNorm_le_two_mul_failureMass
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r)))
    (law : Why24OneRoundTwirledConversionLaw r preparation) :
    traceNorm (why24OneRoundDecodedResidual r law) ≤
      2 * why24OneRoundFailureMassForLaw r preparation law := by
  unfold why24OneRoundDecodedResidual
  calc
    traceNorm (∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        if f1024Why24OddDecodingRadius r < HammingWeight error then
          (law.errorMass error : Complex) •
            ((why24OneRoundDecodedErrorDensity r error).toOperator -
              (why24OneRoundLogicalIdealDensity r).toOperator)
        else 0) ≤
      ∑ error : Why24Word (f1024Why24OddPhysicalSite r),
        if f1024Why24OddDecodingRadius r < HammingWeight error then
          2 * law.errorMass error
        else 0 := by
      simpa using
        (FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
          (Finset.univ : Finset
            (Why24Word (f1024Why24OddPhysicalSite r)))
          law.errorMass
          (fun error =>
            f1024Why24OddDecodingRadius r < HammingWeight error)
          (fun error => (why24OneRoundDecodedErrorDensity r error).toOperator)
          (why24OneRoundLogicalIdealDensity r).toOperator
          law.errorMass_nonneg
          (why24OneRoundDecodedErrorDensity_traceNorm_sub_ideal_le_two r))
    _ = 2 * why24OneRoundFailureMassForLaw r preparation law := by
      rw [why24OneRoundFailureMass_eq_errorMass]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro error _
      simp only [mul_ite, mul_zero]

/-- Half trace distance between the actual complete one-round output and the
logical ideal state. -/
noncomputable def why24OneRoundTraceDistance {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (rho sigma : DensityOperator H) : Real :=
  (2 : Real)⁻¹ * traceNorm (rho.toOperator - sigma.toOperator)

noncomputable def why24OneRoundOutputError (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) : Real :=
  why24OneRoundTraceDistance
    (why24OneRoundRun r preparation).rawOutput
    (why24OneRoundLogicalIdealDensity r)

private theorem why24OneRoundOutputError_le_failureMass (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24OneRoundOutputError r preparation ≤
      why24OneRoundFailureMass r preparation := by
  let law := why24OneRoundDerivedTwirledConversionLaw r preparation
  rw [why24OneRoundOutputError,
    why24OneRoundTraceDistance,
    why24OneRoundRun_sub_ideal_eq_decodedResidual,
    why24OneRoundFailureMass]
  calc
    (2 : Real)⁻¹ * traceNorm (why24OneRoundDecodedResidual r law) ≤
        (2 : Real)⁻¹ *
          (2 * why24OneRoundFailureMassForLaw r preparation law) :=
      mul_le_mul_of_nonneg_left
        (why24OneRoundDecodedResidual_traceNorm_le_two_mul_failureMass
          r preparation law) (by norm_num)
    _ = why24OneRoundFailureMassForLaw r preparation law := by ring

/-- The actual one-round logical output obeys the finite local-stochastic
source bound.  Correlations are retained through the physical branch law;
only the local-stochastic subset tails enter the final union bound. -/
theorem why24OneRoundOutputError_le (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    why24OneRoundOutputError r preparation ≤
      (Nat.choose (f1024Why24OddLength r)
        (f1024Why24OddDecodingRadius r + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius r + 1) :=
  (why24OneRoundOutputError_le_failureMass r preparation).trans
    (why24OneRoundFailureMass_le r preparation)

/-! ## Shared protocol and family-ready terminal interface -/

/-- With success probability one, the accepted conditional density of the
actual active-correction run is its complete channel output. -/
theorem why24OneRoundRun_acceptedOutput_eq_rawOutput (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundRun r preparation).acceptedOutput =
      (why24OneRoundRun r preparation).rawOutput := by
  have hmixture :=
    (why24OneRoundRun r preparation).rawOutput_eq_outcomeMixture
  rw [hmixture]
  apply DensityOperator.ext_toOperator
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    outcomeWeight, branchState,
    why24OneRoundRun_successProbability_eq_one,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]

/-- The shared distillation-protocol object for one concrete F1024 tower
level.  Its noisy inputs are exactly the singleton marginals of the same
correlated joint preparation consumed by `why24CorrelatedPrepareInput`. -/
noncomputable def why24OneRoundMagicStateDistillationProtocol (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    MagicStateDistillationProtocol Why24CCZSpace
      (ComputationalBasisRegister F1024 (f1024Why24OddPhysicalSite r))
      (ComputationalBasisRegister F1024 (f1024Why24OddLogical r)) where
  run := why24OneRoundRun r preparation
  inputErrorModel := InputErrorModel.localStochastic
    (why24LocalStochasticInputErrorModel preparation)
  inputPermitted := why24LocalStochasticInputErrorModel_permits preparation
  behavior := .activeCorrection (QuantumChannel.id _)
  idealOutput := why24OneRoundLogicalIdealDensity r
  outputError := why24OneRoundTraceDistance
  outputError_nonneg := by
    intro rho sigma
    exact mul_nonneg (by norm_num) (traceNorm_nonneg _)

private theorem why24OneRoundMagicStateDistillationProtocol_successfulOutputError
    (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    (why24OneRoundMagicStateDistillationProtocol r preparation).successfulOutputError =
      why24OneRoundOutputError r preparation := by
  rw [MagicStateDistillationProtocol.successfulOutputError,
    why24OneRoundMagicStateDistillationProtocol,
    why24OneRoundOutputError]
  rw [why24OneRoundRun_acceptedOutput_eq_rawOutput]

/-- Complete finite WHY24 one-round handoff.  It exposes the actual shared
protocol, exact resource counts, deterministic success, and the correlated
local-stochastic output bound needed by the terminal asymptotic child. -/
theorem why24_one_round_physical_protocol (r : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount r))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))) :
    let protocol :=
      why24OneRoundMagicStateDistillationProtocol r preparation
    protocol.run = why24OneRoundRun r preparation ∧
      protocol.inputErrorModel = InputErrorModel.localStochastic
        (why24LocalStochasticInputErrorModel preparation) ∧
      protocol.behavior = .activeCorrection (QuantumChannel.id _) ∧
      protocol.run.resourceCount = 70 * f1024Why24OddLength r ∧
      why24OneRoundOutputCount r = f1024Why24OddDimension r ∧
      protocol.run.successProbability = 1 ∧
      protocol.successfulOutputError ≤
        (Nat.choose (f1024Why24OddLength r)
          (f1024Why24OddDecodingRadius r + 1) : Real) *
          (70 * preparation.rate) ^
            (f1024Why24OddDecodingRadius r + 1) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, why24OneRoundOutputCount_eq r,
    why24OneRoundRun_successProbability_eq_one r preparation, ?_⟩
  · exact why24OneRoundInputCount_eq r
  · rw [why24OneRoundMagicStateDistillationProtocol_successfulOutputError]
    exact why24OneRoundOutputError_le r preparation

end QEC.Distillation.Why24OneRoundProtocol
