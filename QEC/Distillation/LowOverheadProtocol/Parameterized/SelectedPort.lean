import QEC.Distillation.LowOverheadProtocol.Parameterized.DecodedErrorBridge
import QEC.Distillation.LowOverheadProtocol.Parameterized.SelectedPortSupport
import QEC.Semantics.Core.Subsystem
/-!
# Parameterized HH18 selected logical port

This module extracts one literal logical coordinate from the accepted decoded
joint output of an arbitrary admissible HH18 block. The extraction is the
CPTP finite partial trace followed by a basis-preserving unitary transport;
it never replaces the joint output with an input-independent state.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

attribute [local instance 100] Fintype.ofFinite

local instance instSelectedPortClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The singleton physical subsystem retaining the nominated actual logical
output coordinate. -/
noncomputable def selectedLogicalPortSubsystem (m w : Nat) (port : LogicalSite m w) :
    FiniteSubsystem (LogicalSite m w) :=
  ⟨{port}⟩

/-- The only coordinate of a selected singleton port. -/
noncomputable def selectedLogicalPortCoordinate (m w : Nat) (port : LogicalSite m w) :
    (selectedLogicalPortSubsystem m w port).SelectedCoordinates :=
  ⟨port, by simp [selectedLogicalPortSubsystem]⟩

theorem selectedLogicalPortCoordinate_eq (m w : Nat) (port : LogicalSite m w)
    (coordinate : (selectedLogicalPortSubsystem m w port).SelectedCoordinates) :
    coordinate = selectedLogicalPortCoordinate m w port := by
  apply Subtype.ext
  have hmem : (coordinate : LogicalSite m w) ∈ ({port} : Finset (LogicalSite m w)) :=
    coordinate.property
  exact Finset.mem_singleton.mp hmem

/-- Computational labels of the selected singleton register are ordinary
one-qubit bit labels. -/
def selectedLogicalPortBitstringEquiv (m w : Nat) (port : LogicalSite m w) :
    Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates ≃ Fin 2 where
  toFun := fun bits => bits (selectedLogicalPortCoordinate m w port)
  invFun := fun bit _ => bit
  left_inv := by
    intro bits
    funext coordinate
    rw [selectedLogicalPortCoordinate_eq m w port coordinate]
  right_inv := by
    intro bit
    rfl

/-- The basis-preserving unitary identification of the selected subsystem
with the canonical one-qubit Hilbert space. -/
noncomputable def selectedLogicalPortTransport (m w : Nat) (port : LogicalSite m w) :
    UnitaryTransport (selectedLogicalPortSubsystem m w port).selectedSystem QubitSpace := by
  let sourceBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates) Complex
  let targetBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let U := sourceBasis.equiv targetBasis (selectedLogicalPortBitstringEquiv m w port)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

@[simp] theorem selectedLogicalPortTransport_apply_basis (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates) :
    selectedLogicalPortTransport m w port
      (EuclideanSpace.basisFun _ Complex bits) =
      EuclideanSpace.basisFun _ Complex
        (selectedLogicalPortBitstringEquiv m w port bits) := by
  dsimp [selectedLogicalPortTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

private def selectedLogicalPortAnchorBitstring (m w : Nat) (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    Qubit.Bitstring (LogicalSite m w) :=
  (selectedLogicalPortSubsystem m w port).recombineBitstring ((fun _ => 0), bits)

noncomputable def selectedLogicalPortComplementIdealState (m w : Nat)
    (port : LogicalSite m w) :
    (selectedLogicalPortSubsystem m w port).complementSystem :=
  WithLp.toLp 2 fun bits =>
    (Real.sqrt 2 : Complex) *
      Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
        (selectedLogicalPortAnchorBitstring m w port bits)

@[simp] theorem selectedLogicalPortComplementIdealState_apply (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    selectedLogicalPortComplementIdealState m w port bits =
      (Real.sqrt 2 : Complex) *
        Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port bits) :=
  rfl

private theorem selectedLogicalPortAnchorBitstring_apply_port (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    selectedLogicalPortAnchorBitstring m w port bits port = 0 := by
  simp [selectedLogicalPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    selectedLogicalPortSubsystem]

private theorem selectedLogicalPortRecombineBitstring_apply_port (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    (selectedLogicalPortSubsystem m w port).recombineBitstring (left, right) port =
      left (selectedLogicalPortCoordinate m w port) := by
  simp only [FiniteSubsystem.recombineBitstring]
  rw [dif_pos (by simp [selectedLogicalPortSubsystem])]
  let coordinate : (selectedLogicalPortSubsystem m w port).SelectedCoordinates :=
    ⟨port, by simp [selectedLogicalPortSubsystem]⟩
  change left coordinate = left (selectedLogicalPortCoordinate m w port)
  rw [selectedLogicalPortCoordinate_eq m w port coordinate]

private theorem selectedLogicalPortRecombineBitstring_apply_ne (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
    (site : LogicalSite m w) (hsite : site ≠ port) :
    (selectedLogicalPortSubsystem m w port).recombineBitstring (left, right) site =
      selectedLogicalPortAnchorBitstring m w port right site := by
  simp [selectedLogicalPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    selectedLogicalPortSubsystem, hsite]

private theorem selectedLogicalPortHammingWeight_recombine (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
      ((selectedLogicalPortSubsystem m w port).recombineBitstring (left, right))) =
      (selectedLogicalPortBitstringEquiv m w port left).val +
        Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port right)) := by
  classical
  generalize hbit : selectedLogicalPortBitstringEquiv m w port left = bit
  fin_cases bit
  · have hleft : left (selectedLogicalPortCoordinate m w port) = 0 := by
      simpa [selectedLogicalPortBitstringEquiv] using hbit
    have heq :
        (selectedLogicalPortSubsystem m w port).recombineBitstring (left, right) =
          selectedLogicalPortAnchorBitstring m w port right := by
      funext site
      by_cases hsite : site = port
      · subst site
        rw [selectedLogicalPortRecombineBitstring_apply_port,
          selectedLogicalPortAnchorBitstring_apply_port, hleft]
      · exact selectedLogicalPortRecombineBitstring_apply_ne m w port left right site hsite
    simp [heq]
  · have hleft : left (selectedLogicalPortCoordinate m w port) = 1 := by
      simpa [selectedLogicalPortBitstringEquiv] using hbit
    have hsupp :
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
          ((selectedLogicalPortSubsystem m w port).recombineBitstring (left, right))) =
          insert port
            (Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
              (selectedLogicalPortAnchorBitstring m w port right))) := by
      ext site
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and,
        Coding.PauliSymplectic.bitstringWordEquiv_apply]
      by_cases hsite : site = port
      · subst site
        norm_num [
          selectedLogicalPortRecombineBitstring_apply_port,
          selectedLogicalPortAnchorBitstring_apply_port, hleft]
        exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
      · have happly :=
          selectedLogicalPortRecombineBitstring_apply_ne m w port left right site hsite
        simp only [happly, hsite, false_or]
    have hnotmem : port ∉
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port right)) := by
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter]
      simp [Coding.PauliSymplectic.bitstringWordEquiv_apply,
        selectedLogicalPortAnchorBitstring_apply_port]
      rfl
    simp only [Coding.HammingWeight, hsupp,
      Finset.card_insert_of_notMem hnotmem]
    omega

private theorem selectedLogicalPortMagicState_recombine_amplitude (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
        ((selectedLogicalPortSubsystem m w port).recombineBitstring (left, right)) =
      aZeroState (selectedLogicalPortBitstringEquiv m w port left) *
        selectedLogicalPortComplementIdealState m w port right := by
  rw [Triorthogonal.BinaryRowFamily.logicalMagicState_apply,
    selectedLogicalPortComplementIdealState_apply,
    Triorthogonal.BinaryRowFamily.logicalMagicState_apply,
    selectedLogicalPortHammingWeight_recombine]
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast OneQubitMagic.sqrt_two_pos.ne'
  generalize hbit : selectedLogicalPortBitstringEquiv m w port left = bit
  fin_cases bit
  all_goals simp [aZeroState, OneQubitMagic.phaseState,
    Triorthogonal.BinaryRowFamily.piDivFourPhase]
  all_goals field_simp [hsqrt_ne]
  all_goals ring

private theorem selectedLogicalPortTransport_symm_apply (m w : Nat)
    (port : LogicalSite m w) (psi : QubitSpace)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates) :
    (selectedLogicalPortTransport m w port).symm psi bits =
      psi (selectedLogicalPortBitstringEquiv m w port bits) := by
  have hinner := (selectedLogicalPortTransport m w port).map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((selectedLogicalPortTransport m w port).symm psi)
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [selectedLogicalPortTransport_apply_basis, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

private theorem selectedLogicalPortRegisterFactorization_symm_tmul_apply (m w : Nat)
    (port : LogicalSite m w)
    (leftState : (selectedLogicalPortSubsystem m w port).selectedSystem)
    (rightState : (selectedLogicalPortSubsystem m w port).complementSystem)
    (bits : Qubit.Bitstring (LogicalSite m w)) :
    (selectedLogicalPortSubsystem m w port).registerFactorization.symm
        (leftState ⊗ₜ[Complex] rightState) bits =
      leftState ((selectedLogicalPortSubsystem m w port).splitBitstring bits).1 *
        rightState ((selectedLogicalPortSubsystem m w port).splitBitstring bits).2 := by
  have hinner := (selectedLogicalPortSubsystem m w port).registerFactorization.map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((selectedLogicalPortSubsystem m w port).registerFactorization.symm
      (leftState ⊗ₜ[Complex] rightState))
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [FiniteSubsystem.registerFactorization_apply_basis, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

private theorem selectedLogicalPortMagicState_factorization (m w : Nat)
    (port : LogicalSite m w) :
    (selectedLogicalPortSubsystem m w port).registerFactorization
        (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)) =
      (selectedLogicalPortTransport m w port).symm aZeroState ⊗ₜ[Complex]
        selectedLogicalPortComplementIdealState m w port := by
  apply (selectedLogicalPortSubsystem m w port).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_apply_apply]
  ext bits
  change Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w) bits =
    (selectedLogicalPortSubsystem m w port).registerFactorization.symm
      ((selectedLogicalPortTransport m w port).symm aZeroState ⊗ₜ[Complex]
        selectedLogicalPortComplementIdealState m w port) bits
  rw [selectedLogicalPortRegisterFactorization_symm_tmul_apply,
    selectedLogicalPortTransport_symm_apply]
  have hsplit :
      (selectedLogicalPortSubsystem m w port).recombineBitstring
          ((selectedLogicalPortSubsystem m w port).splitBitstring bits) = bits := by
    simpa [FiniteSubsystem.bitstringFactorization] using
      (selectedLogicalPortSubsystem m w port).bitstringFactorization.symm_apply_apply bits
  calc
    Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w) bits =
        Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
          ((selectedLogicalPortSubsystem m w port).recombineBitstring
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits)) := by rw [hsplit]
    _ = aZeroState
          (selectedLogicalPortBitstringEquiv m w port
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).1) *
          selectedLogicalPortComplementIdealState m w port
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).2 := by
          exact selectedLogicalPortMagicState_recombine_amplitude m w port
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).1
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).2

private theorem phaseAmplitude_nat_mul (theta : ℝ) (n : Nat) :
    OneQubitMagic.phaseAmplitude (n * theta) =
      OneQubitMagic.phaseAmplitude theta ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, OneQubitMagic.phaseAmplitude_add,
        ih, one_mul, pow_succ]

private theorem logicalTInv_logicalMagicState (m w : Nat) :
    HH18PuncturedReedMuller.logicalTInv w m
      (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)) =
        logicalPlus m w := by
  ext bits
  rw [HH18PuncturedReedMuller.logicalTInv_eq_allSitePhase_neg_pi_div_four,
    Triorthogonal.allSitePhase_apply]
  simp only [Triorthogonal.BinaryRowFamily.logicalMagicState_apply,
    logicalPlus, Triorthogonal.BinaryRowFamily.logicalPlusState_apply,
    Triorthogonal.BinaryRowFamily.piDivFourPhase]
  rw [show -Real.pi / 4 *
      (Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
        (LogicalSite m w) bits) : Real) =
      -(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
        (LogicalSite m w) bits) : Nat) * (Real.pi / 4) by ring]
  have hphase :
      OneQubitMagic.phaseAmplitude
          (-(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) : Nat) * (Real.pi / 4)) *
        OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
          Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) = 1 := by
    rw [← phaseAmplitude_nat_mul]
    rw [← OneQubitMagic.phaseAmplitude_add]
    convert OneQubitMagic.phaseAmplitude_zero using 1
    ring_nf
  calc
    OneQubitMagic.phaseAmplitude
          (-(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) : Nat) * (Real.pi / 4)) *
        (Triorthogonal.BinaryRowFamily.logicalUniformScalar (LogicalSite m w) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
            Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
              (LogicalSite m w) bits)) =
        (OneQubitMagic.phaseAmplitude
          (-(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) : Nat) * (Real.pi / 4)) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
            Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
              (LogicalSite m w) bits)) *
          Triorthogonal.BinaryRowFamily.logicalUniformScalar (LogicalSite m w) := by ring
    _ = Triorthogonal.BinaryRowFamily.logicalUniformScalar (LogicalSite m w) := by
      rw [hphase]
      ring

private theorem idealLogicalTOutputState_eq_logicalMagicState (m w : Nat) :
    idealLogicalTOutputState m w =
      Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w) := by
  apply (HH18PuncturedReedMuller.logicalTInv w m).toLinearEquiv.injective
  change (HH18PuncturedReedMuller.logicalTInv w m).toLinearEquiv
      ((HH18PuncturedReedMuller.logicalTInv w m).toLinearEquiv.symm
        (logicalPlus m w)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (logicalTInv_logicalMagicState m w).symm

private theorem selectedLogicalPortComplementIdealState_inner_self (m w : Nat)
    (port : LogicalSite m w) :
    inner Complex (selectedLogicalPortComplementIdealState m w port)
      (selectedLogicalPortComplementIdealState m w port) = 1 := by
  have hglobal : inner Complex
      (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w))
      (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)) = 1 :=
    Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self (LogicalSite m w)
  have hlocal : inner Complex
      ((selectedLogicalPortTransport m w port).symm aZeroState)
      ((selectedLogicalPortTransport m w port).symm aZeroState) = 1 := by
    calc
      inner Complex ((selectedLogicalPortTransport m w port).symm aZeroState)
          ((selectedLogicalPortTransport m w port).symm aZeroState) =
          inner Complex
            ((selectedLogicalPortTransport m w port)
              ((selectedLogicalPortTransport m w port).symm aZeroState))
            ((selectedLogicalPortTransport m w port)
              ((selectedLogicalPortTransport m w port).symm aZeroState)) :=
            ((selectedLogicalPortTransport m w port).map_inner _ _).symm
      _ = inner Complex aZeroState aZeroState := by
            simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
      _ = 1 := by
            rw [inner_self_eq_norm_sq_to_K, aZeroState_norm]
            norm_num
  have hfactorNorm : inner Complex
      ((selectedLogicalPortSubsystem m w port).registerFactorization
        (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)))
      ((selectedLogicalPortSubsystem m w port).registerFactorization
        (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w))) = 1 := by
    rw [(selectedLogicalPortSubsystem m w port).registerFactorization.map_inner]
    exact hglobal
  rw [selectedLogicalPortMagicState_factorization, TensorProduct.inner_tmul,
    hlocal, one_mul] at hfactorNorm
  exact hfactorNorm

/-- The ideal joint decoded output, physically selected and transported
through its singleton CPTP partial trace. -/
noncomputable def selectedLogicalPortIdealMarginal (m w : Nat)
    (port : LogicalSite m w) : DensityOperator QubitSpace :=
  (selectedLogicalPortTransport m w port).conjDensity
    ((selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
      (idealLogicalTOutput m w))

theorem selectedLogicalPortIdealMarginal_eq_aZeroDensity (m w : Nat)
    (port : LogicalSite m w) :
    selectedLogicalPortIdealMarginal m w port = aZeroDensity := by
  apply DensityOperator.ext_toOperator
  simp only [selectedLogicalPortIdealMarginal, UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, FiniteSubsystem.selectedPartialTrace,
    idealLogicalTOutput, DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [idealLogicalTOutputState_eq_logicalMagicState]
  rw [selectedLogicalPortMagicState_factorization]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [selectedLogicalPortComplementIdealState_inner_self]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact aZeroDensity_rankOne.symm

/-- The actual selected-port density of the accepted decoded joint output. -/
noncomputable def selectedLogicalPortAcceptedDensity {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    DensityOperator (selectedLogicalPortSubsystem m w port).selectedSystem :=
  (selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
    (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput

/-- The actual selected-port accepted output after its concrete unitary
transport to the canonical qubit space. -/
noncomputable def selectedLogicalPortTransportedAcceptedOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    DensityOperator QubitSpace :=
  (selectedLogicalPortTransport m w port).conjDensity
    (selectedLogicalPortAcceptedDensity h hdegree epsilon port)

/-- The literal negative-A Born probability of the actual transported selected
port. -/
noncomputable def selectedLogicalPortRawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) : ℝ :=
  aBasisInstrument.bornWeight .negative
    (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port)

theorem selectedLogicalPortRawError_nonneg {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    0 ≤ selectedLogicalPortRawError h hdegree epsilon port := by
  unfold selectedLogicalPortRawError
  exact aBasisInstrument_weight_nonneg .negative _

theorem selectedLogicalPortRawError_le_one {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon port ≤ 1 := by
  unfold selectedLogicalPortRawError
  have hsum := aBasisInstrument_weight_sum
    (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port)
  have hpositive := aBasisInstrument_weight_nonneg .positive
    (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port)
  linarith

/-- The closed unit-interval parameter obtained from the actual selected-port
negative-A measurement outcome. -/
noncomputable def selectedLogicalPortRawParameter {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) : ErrorParameter where
  rate := selectedLogicalPortRawError h hdegree epsilon port
  rate_nonneg := selectedLogicalPortRawError_nonneg h hdegree epsilon port
  rate_le_one := selectedLogicalPortRawError_le_one h hdegree epsilon port

/-- A-basis dephasing of the literal selected-port accepted output. -/
noncomputable def selectedLogicalPortDephasedOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity
    (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port)

theorem selectedLogicalPortDephasedOutput_eq_diagonalAResource {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortDephasedOutput h hdegree epsilon port =
      diagonalAResource (selectedLogicalPortRawParameter h hdegree epsilon port) := by
  unfold selectedLogicalPortDephasedOutput
  apply OneQubitABasisSupport.aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
  rfl

private noncomputable def selectedLogicalPortTransportedChannel (m w : Nat)
    (port : LogicalSite m w) : QuantumChannel (LogicalRegister m w) QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (selectedLogicalPortTransport m w port))
    (selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister

private theorem selectedLogicalPortTransportedChannel_ideal (m w : Nat)
    (port : LogicalSite m w) :
    selectedLogicalPortTransportedChannel m w port
      (idealLogicalTOutput m w).toOperator = aZeroDensity.toOperator := by
  change (selectedLogicalPortIdealMarginal m w port).toOperator = _
  exact congrArg DensityOperator.toOperator
    (selectedLogicalPortIdealMarginal_eq_aZeroDensity m w port)

theorem selectedLogicalPortTransportedAcceptedOutput_traceDistance_le_outputTrace
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    traceNorm
      ((selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port).toOperator -
        aZeroDensity.toOperator) ≤
      outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) := by
  change traceNorm
      (selectedLogicalPortTransportedChannel m w port
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput.toOperator -
        aZeroDensity.toOperator) ≤ _
  rw [← selectedLogicalPortTransportedChannel_ideal m w port]
  simpa only [outputTraceError] using
    (selectedLogicalPortTransportedChannel m w port).traceNorm_density_sub_le
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w)

theorem selectedLogicalPortRawError_le_outputTrace {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon port ≤
      outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) := by
  unfold selectedLogicalPortRawError
  calc
    aBasisInstrument.bornWeight .negative
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) ≤
        traceNorm
          ((selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port).toOperator -
            aZeroDensity.toOperator) :=
      OneQubitABasisSupport.negativeABornWeight_le_traceDistance_to_aZero _
    _ ≤ outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) :=
      selectedLogicalPortTransportedAcceptedOutput_traceDistance_le_outputTrace
        h hdegree epsilon port

theorem selectedLogicalPortRawError_le_two_mul_acceptedResidual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon port ≤
      2 * acceptedResidualError h hdegree epsilon := by
  calc
    selectedLogicalPortRawError h hdegree epsilon port ≤
        outputTraceError
          (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
          (idealLogicalTOutput m w) :=
      selectedLogicalPortRawError_le_outputTrace h hdegree epsilon port
    _ ≤ 2 * acceptedResidualError h hdegree epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual h hdegree epsilon

end HH18Parameterized
end Distillation
end QEC
