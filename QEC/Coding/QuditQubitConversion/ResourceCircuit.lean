import QEC.Coding.QuditQubitConversion.AppendixANF.Gate.ReversePhase
import QEC.Semantics.Entropy.Purification
/-!
# WHY24 `U₁^(7)` resource states and Appendix-A circuit route

The WHY24 source starts the Appendix-A construction from the normalized
uniform `F1024` qudit state and its selected ten-qubit-basis transport.  This
module records that resource, the literal Appendix gate program, and the
all-outcome reverse conversion which retains sites `0,1,2`.
-/

noncomputable section

namespace QEC.Coding

/-- The uniform amplitude on the source's concrete `F1024` qudit. -/
private noncomputable def why24UniformAmplitude : Complex :=
  (Real.sqrt (Fintype.card F1024 : Real) : Complex)⁻¹

/-- The normalization identity for the concrete uniform `F1024` amplitude. -/
private theorem why24UniformAmplitude_identity :
    starRingEnd Complex why24UniformAmplitude * why24UniformAmplitude *
        (Fintype.card F1024 : Complex) = 1 := by
  have hcard : 0 < Fintype.card F1024 := Fintype.card_pos
  have hsqrtPos : 0 < Real.sqrt (Fintype.card F1024 : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Fintype.card F1024 : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Fintype.card F1024 : Real) : Complex) *
          (Real.sqrt (Fintype.card F1024 : Real) : Complex) =
        (Fintype.card F1024 : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Fintype.card F1024)
  simp only [why24UniformAmplitude, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Fintype.card F1024 : Real) : Complex) =
        (Real.sqrt (Fintype.card F1024 : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]

/-- The normalized uniform qudit state used as the WHY24 `U₁^(7)` input. -/
noncomputable def why24QuditPlusState : Why24QuditSpace :=
  WithLp.toLp 2 fun _ => why24UniformAmplitude

@[simp] theorem why24QuditPlusState_apply (β : F1024) :
    why24QuditPlusState β = why24UniformAmplitude :=
  rfl

private theorem why24QuditPlusState_inner_self :
    inner Complex why24QuditPlusState why24QuditPlusState = 1 := by
  rw [PiLp.inner_apply]
  simp only [why24QuditPlusState_apply, RCLike.inner_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (Fintype.card F1024 : Complex) *
      (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) = 1
  calc
    (Fintype.card F1024 : Complex) *
        (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) =
        starRingEnd Complex why24UniformAmplitude * why24UniformAmplitude *
          (Fintype.card F1024 : Complex) := by ring
    _ = 1 := why24UniformAmplitude_identity

/-- The concrete uniform qudit input has unit norm. -/
theorem why24QuditPlusState_norm : ‖why24QuditPlusState‖ = 1 := by
  have hinner := why24QuditPlusState_inner_self
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖why24QuditPlusState‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg why24QuditPlusState]

/-- The selected ten-qubit-basis transport of the normalized qudit plus state. -/
noncomputable def why24QubitPlusState : Why24QubitSpace :=
  why24QuditQubitUnitary why24QuditPlusState

/-- The selected basis unitary sends the source qudit plus state to its qubit image. -/
theorem why24QuditQubitUnitary_apply_quditPlusState :
    why24QuditQubitUnitary why24QuditPlusState = why24QubitPlusState :=
  rfl

/-- The transported ten-qubit plus state has unit norm. -/
theorem why24QubitPlusState_norm : ‖why24QubitPlusState‖ = 1 := by
  change ‖why24QuditQubitUnitary.toLinearIsometryEquiv why24QuditPlusState‖ = 1
  rw [why24QuditQubitUnitary.toLinearIsometryEquiv.norm_map]
  exact why24QuditPlusState_norm

/-- The source's qudit `U₁^(7)` resource, prepared from the normalized plus state. -/
noncomputable def why24UOneSevenQuditResource : Why24QuditSpace :=
  why24UOneSeven why24QuditPlusState

/-- The qudit resource is literally the source diagonal applied to its plus input. -/
theorem why24UOneSevenQuditResource_eq_apply :
    why24UOneSevenQuditResource = why24UOneSeven why24QuditPlusState :=
  rfl

/-- The source qudit resource has unit norm by the concrete diagonal's unitarity. -/
theorem why24UOneSevenQuditResource_norm : ‖why24UOneSevenQuditResource‖ = 1 := by
  have hinner := why24U_isUnitary (1 : F1024) 7
    why24QuditPlusState why24QuditPlusState
  change inner Complex why24UOneSevenQuditResource why24UOneSevenQuditResource =
    inner Complex why24QuditPlusState why24QuditPlusState at hinner
  rw [why24QuditPlusState_inner_self] at hinner
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖why24UOneSevenQuditResource‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg why24UOneSevenQuditResource]

/-- The selected ten-qubit transport of the source's qudit `U₁^(7)` resource. -/
noncomputable def why24UOneSevenQubitResource : Why24QubitSpace :=
  why24QubitUOneSeven why24QubitPlusState

/-- The qubit resource is literally the transported source diagonal applied to its plus input. -/
theorem why24UOneSevenQubitResource_eq_apply :
    why24UOneSevenQubitResource = why24QubitUOneSeven why24QubitPlusState :=
  rfl

/-- The selected basis unitary transports the qudit resource to the qubit resource. -/
theorem why24QuditQubitUnitary_apply_uOneSevenQuditResource :
    why24QuditQubitUnitary why24UOneSevenQuditResource =
      why24UOneSevenQubitResource := by
  simp only [why24UOneSevenQuditResource, why24UOneSevenQubitResource,
    why24QubitPlusState, why24QubitUOneSeven,
    Semantics.UnitaryTransport.conjOperator_apply,
    LinearEquiv.symm_apply_apply]

/-- The transported ten-qubit resource has unit norm. -/
theorem why24UOneSevenQubitResource_norm : ‖why24UOneSevenQubitResource‖ = 1 := by
  rw [← why24QuditQubitUnitary_apply_uOneSevenQuditResource]
  change ‖why24QuditQubitUnitary.toLinearIsometryEquiv
    why24UOneSevenQuditResource‖ = 1
  rw [why24QuditQubitUnitary.toLinearIsometryEquiv.norm_map]
  exact why24UOneSevenQuditResource_norm

private def why24AppendixGatePhase (gate : Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) : ZMod 2 :=
  let word := PauliSymplectic.bitstringWordEquiv (Fin 10) bits
  match gate with
  | .z site => word site
  | .cz left right => word left * word right
  | .ccz first second third => word first * word second * word third

private noncomputable def why24AppendixGateOperator (gate : Why24AppendixGate) :
    Semantics.Operator Why24QubitSpace where
  toFun ψ := WithLp.toLp 2 fun bits =>
    PauliSymplectic.binaryPhaseScalar (why24AppendixGatePhase gate bits) * ψ bits
  map_add' ψ φ := by
    ext bits
    simp [mul_add]
  map_smul' c ψ := by
    ext bits
    simp [smul_eq_mul, mul_left_comm]

private theorem why24AppendixGateOperator_apply (gate : Why24AppendixGate)
    (ψ : Why24QubitSpace) (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixGateOperator gate ψ bits =
      PauliSymplectic.binaryPhaseScalar (why24AppendixGatePhase gate bits) * ψ bits :=
  rfl

private def why24AppendixPhaseList (gates : List Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) : ZMod 2 :=
  gates.foldr (fun gate phase => why24AppendixGatePhase gate bits + phase) 0

private noncomputable def why24AppendixCircuitOf (gates : List Why24AppendixGate) :
    Semantics.Operator Why24QubitSpace :=
  gates.foldr (fun gate circuit => why24AppendixGateOperator gate * circuit) 1

private theorem why24AppendixCircuitOf_apply (gates : List Why24AppendixGate)
    (ψ : Why24QubitSpace) (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixCircuitOf gates ψ bits =
      PauliSymplectic.binaryPhaseScalar (why24AppendixPhaseList gates bits) * ψ bits := by
  unfold why24AppendixCircuitOf
  induction gates with
  | nil => simp [why24AppendixPhaseList]
  | cons gate gates ih =>
      simp only [List.foldr_cons, Module.End.mul_apply, why24AppendixGateOperator_apply, ih,
        why24AppendixPhaseList]
      rw [← mul_assoc, ← PauliSymplectic.binaryPhaseScalar_add]

/-- The ordered diagonal circuit obtained by composing the literal Appendix-A gates. -/
noncomputable def why24AppendixCircuit : Semantics.Operator Why24QubitSpace :=
  why24AppendixCircuitOf why24AppendixGateList

private theorem why24AppendixCircuit_apply_phase (ψ : Why24QubitSpace)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixCircuit ψ bits =
      PauliSymplectic.binaryPhaseScalar (why24AppendixPhaseList why24AppendixGateList bits) *
        ψ bits := by
  change why24AppendixCircuitOf why24AppendixGateList ψ bits =
    PauliSymplectic.binaryPhaseScalar
      (why24AppendixPhaseList why24AppendixGateList bits) * ψ bits
  exact why24AppendixCircuitOf_apply why24AppendixGateList ψ bits


private theorem why24AppendixGatePhase_eq_word (gate : Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixGatePhase gate bits =
      why24AppendixWordGatePhase gate
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) :=
  rfl

private theorem why24AppendixPhaseList_eq_word (gates : List Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixPhaseList gates bits =
      why24AppendixWordPhaseList gates
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      simp only [why24AppendixPhaseList, why24AppendixWordPhaseList,
        List.foldr_cons, why24AppendixGatePhase_eq_word, ih]

private theorem why24Trace_label_symm_eq_phaseList
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    Algebra.trace (ZMod 2) F1024
        ((why24ComputationalLabelEquiv.symm bits) ^ 7) =
      why24AppendixWordPhaseList why24AppendixGateList
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
  have hlabel : why24ComputationalLabelEquiv.symm bits =
      f1024SelectedCoordinates.symm
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
    calc
      why24ComputationalLabelEquiv.symm bits =
          f1024SelectedCoordinates.symm
            (f1024SelectedCoordinates
              (why24ComputationalLabelEquiv.symm bits)) := by
                rw [f1024SelectedCoordinates_symm_apply]
      _ = f1024SelectedCoordinates.symm
          (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
            rw [f1024SelectedCoordinates_label_symm]
  rw [hlabel]
  exact (why24AppendixWordPhaseList_eq_trace
    (PauliSymplectic.bitstringWordEquiv (Fin 10) bits)).symm

/-- The literal Appendix-A circuit is exactly the selected ten-qubit transport
of `U₁^(7)`. -/
theorem why24AppendixCircuit_apply_eq_why24QubitUOneSeven
    (ψ : Why24QubitSpace) :
    why24AppendixCircuit ψ = why24QubitUOneSeven ψ := by
  ext bits
  rw [why24AppendixCircuit_apply_phase, why24AppendixPhaseList_eq_word,
    ← why24Trace_label_symm_eq_phaseList]
  rw [why24QubitUOneSeven, Semantics.UnitaryTransport.conjOperator_apply]
  change
    PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24ComputationalLabelEquiv.symm bits) ^ 7)) * ψ bits =
      why24QuditQubitBasisIsometry
        (why24UOneSeven (why24QuditQubitBasisIsometry.symm ψ)) bits
  rw [why24QuditQubitBasisIsometry_apply, why24U_apply,
    why24QuditQubitBasisIsometry_symm_apply]
  simp only [Equiv.apply_symm_apply, one_mul]

/-- Applying the literal Appendix-A circuit to the transported plus state
prepares the source resource. -/
theorem why24AppendixForwardPreparation :
    why24AppendixCircuit why24QubitPlusState =
      why24UOneSevenQubitResource := by
  rw [why24UOneSevenQubitResource_eq_apply,
    why24AppendixCircuit_apply_eq_why24QubitUOneSeven]

/-!
## Reverse conversion to one CCZ resource

For one fixed seven-bit measurement outcome, the raw branch is the literal
restriction of the ten-qubit resource amplitudes.  The correction phase from
`Why24AppendixReversePhase` cancels the complete printed gate-list phase and
restores only the retained `CCZ_{0,1,2}` phase.  The norm calculation is over
the eight retained labels, not over the 1024 source words.
-/

private theorem why24QubitPlusState_apply
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24QubitPlusState bits = why24UniformAmplitude := by
  change why24QuditPlusState (why24ComputationalLabelEquiv.symm bits) =
    why24UniformAmplitude
  exact why24QuditPlusState_apply _

private theorem why24UOneSevenQubitResource_apply
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24UOneSevenQubitResource bits =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixWordPhaseList why24AppendixGateList
            (PauliSymplectic.bitstringWordEquiv (Fin 10) bits)) *
        why24UniformAmplitude := by
  rw [← why24AppendixForwardPreparation,
    why24AppendixCircuit_apply_phase, why24AppendixPhaseList_eq_word,
    why24QubitPlusState_apply]

/-- The actual unnormalised three-qubit branch obtained by fixing all seven
measured computational-basis bits. -/
noncomputable def why24AppendixReverseRawBranch
    (outcome : Why24AppendixReverseOutcome) : Why24CCZSpace :=
  WithLp.toLp 2 fun retained =>
    why24UOneSevenQubitResource
      (why24AppendixReverseRecombine retained outcome)

private theorem why24AppendixReverseRawBranch_apply
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseRawBranch outcome retained =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseSourcePhase outcome retained) *
        why24UniformAmplitude := by
  rw [why24AppendixReverseRawBranch,
    why24UOneSevenQubitResource_apply]
  rfl

/-- The actual outcome-dependent diagonal correction on the three retained
qubits.  Its phase is derived from the literal Appendix list. -/
noncomputable def why24AppendixReverseCorrection
    (outcome : Why24AppendixReverseOutcome) :
    Semantics.Operator Why24CCZSpace where
  toFun psi := WithLp.toLp 2 fun retained =>
    PauliSymplectic.binaryPhaseScalar
        (why24AppendixReverseCorrectionPhase outcome retained) *
      psi retained
  map_add' left right := by
    ext retained
    simp [mul_add]
  map_smul' scalar psi := by
    ext retained
    simp [smul_eq_mul, mul_left_comm]

private theorem why24AppendixReverseCorrection_apply
    (outcome : Why24AppendixReverseOutcome) (psi : Why24CCZSpace)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseCorrection outcome psi retained =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        psi retained :=
  rfl

private theorem why24BinaryPhaseScalar_mul_self (phase : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar phase *
        PauliSymplectic.binaryPhaseScalar phase = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add,
    CharTwo.add_self_eq_zero,
    PauliSymplectic.binaryPhaseScalar_zero]

private noncomputable def why24PhaseUniformRetainedBranch
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2) :
    Why24CCZSpace :=
  WithLp.toLp 2 fun retained =>
    PauliSymplectic.binaryPhaseScalar (phase retained) *
      why24UniformAmplitude

private theorem why24PhaseUniformRetainedBranch_apply
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24PhaseUniformRetainedBranch phase retained =
      PauliSymplectic.binaryPhaseScalar (phase retained) *
        why24UniformAmplitude :=
  rfl

private theorem why24PhaseUniformRetainedBranch_inner_self
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2) :
    inner Complex (why24PhaseUniformRetainedBranch phase)
        (why24PhaseUniformRetainedBranch phase) = (1 / 128 : Complex) := by
  rw [PiLp.inner_apply]
  calc
    (∑ retained : Semantics.Qubit.Bitstring (Fin 3),
      inner Complex
        (why24PhaseUniformRetainedBranch phase retained)
        (why24PhaseUniformRetainedBranch phase retained)) =
        ∑ _retained : Semantics.Qubit.Bitstring (Fin 3),
          why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude := by
      apply Finset.sum_congr rfl
      intro retained _
      rw [why24PhaseUniformRetainedBranch_apply]
      simp only [RCLike.inner_apply, map_mul]
      have hstar :
          starRingEnd Complex
              (PauliSymplectic.binaryPhaseScalar (phase retained)) =
            PauliSymplectic.binaryPhaseScalar (phase retained) :=
        PauliSymplectic.binaryPhaseScalar_star _
      rw [hstar]
      calc
        (PauliSymplectic.binaryPhaseScalar (phase retained) *
            why24UniformAmplitude) *
            (PauliSymplectic.binaryPhaseScalar (phase retained) *
              starRingEnd Complex why24UniformAmplitude) =
            (PauliSymplectic.binaryPhaseScalar (phase retained) *
              PauliSymplectic.binaryPhaseScalar (phase retained)) *
                (why24UniformAmplitude *
                  starRingEnd Complex why24UniformAmplitude) := by ring
        _ = why24UniformAmplitude *
            starRingEnd Complex why24UniformAmplitude := by
              rw [why24BinaryPhaseScalar_mul_self, one_mul]
    _ = (1 / 128 : Complex) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard :
          Fintype.card (Semantics.Qubit.Bitstring (Fin 3)) = 8 := by
        rw [Semantics.Qubit.card_bitstring]
        norm_num
      rw [Finset.card_univ, hcard]
      change (8 : Complex) *
          (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) =
        (1 / 128 : Complex)
      have huniform :
          starRingEnd Complex why24UniformAmplitude * why24UniformAmplitude *
              (1024 : Complex) = 1 := by
        simpa only [f1024_card, Nat.cast_ofNat] using
          why24UniformAmplitude_identity
      calc
        (8 : Complex) *
            (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) =
            (starRingEnd Complex why24UniformAmplitude *
              why24UniformAmplitude * (1024 : Complex)) / 128 := by ring
        _ = (1 / 128 : Complex) := by rw [huniform]

private theorem why24PhaseUniformRetainedBranch_normSq
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2) :
    ‖why24PhaseUniformRetainedBranch phase‖ ^ 2 = (1 / 128 : Real) := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    why24PhaseUniformRetainedBranch_inner_self]
  norm_num

private theorem why24AppendixReverseRawBranch_eq_phaseUniform
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseRawBranch outcome =
      why24PhaseUniformRetainedBranch
        (why24AppendixReverseSourcePhase outcome) := by
  ext retained
  rw [why24AppendixReverseRawBranch_apply,
    why24PhaseUniformRetainedBranch_apply]

/-- The Born weight of one actual computational-basis measurement branch. -/
noncomputable def why24AppendixReverseBornWeight
    (outcome : Why24AppendixReverseOutcome) : Real :=
  ‖why24AppendixReverseRawBranch outcome‖ ^ 2

/-- Every one of the 128 source outcomes has Born weight `1/128`. -/
theorem why24AppendixReverseBornWeight_eq_source
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseBornWeight outcome = (1 / 128 : Real) := by
  rw [why24AppendixReverseBornWeight,
    why24AppendixReverseRawBranch_eq_phaseUniform,
    why24PhaseUniformRetainedBranch_normSq]

private theorem why24AppendixReverseCorrectedRawBranch_eq_phaseUniform
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome) =
      why24PhaseUniformRetainedBranch why24CCZPhase := by
  ext retained
  rw [why24AppendixReverseCorrection_apply,
    why24AppendixReverseRawBranch_apply,
    why24PhaseUniformRetainedBranch_apply,
    ← mul_assoc,
    ← PauliSymplectic.binaryPhaseScalar_add,
    why24AppendixReverseCorrectionPhase_add_source]

/-- The normalized three-qubit `CCZ` magic state obtained from the source's
uniform retained branch. -/
noncomputable def why24CCZMagicState : Why24CCZSpace :=
  (Real.sqrt 128 : Complex) •
    why24PhaseUniformRetainedBranch why24CCZPhase

/-- The concrete `CCZ` resource has unit norm. -/
theorem why24CCZMagicState_norm : ‖why24CCZMagicState‖ = 1 := by
  rw [why24CCZMagicState, norm_smul]
  have hsqrtNorm : ‖(Real.sqrt 128 : Complex)‖ = Real.sqrt 128 := by
    simp
  rw [hsqrtNorm]
  have hsqrtSq : (Real.sqrt 128) ^ 2 = (128 : Real) := by
    exact Real.sq_sqrt (by norm_num)
  have hbranch :=
    why24PhaseUniformRetainedBranch_normSq why24CCZPhase
  have hproductSq :
      (Real.sqrt 128 *
        ‖why24PhaseUniformRetainedBranch why24CCZPhase‖) ^ 2 = 1 := by
    rw [mul_pow, hsqrtSq, hbranch]
    norm_num
  have hproductNonneg : 0 ≤ Real.sqrt 128 *
      ‖why24PhaseUniformRetainedBranch why24CCZPhase‖ :=
    mul_nonneg (Real.sqrt_nonneg 128)
      (norm_nonneg (why24PhaseUniformRetainedBranch why24CCZPhase))
  nlinarith

private theorem why24CCZMagicState_normSq :
    ‖why24CCZMagicState‖ ^ 2 = 1 := by
  rw [why24CCZMagicState_norm]
  norm_num

/-- The pure density operator of the concrete retained `CCZ` resource. -/
noncomputable def why24CCZMagicStateDensity :
    Semantics.DensityOperator Why24CCZSpace :=
  Semantics.DensityOperator.pureDensity
    why24CCZMagicState why24CCZMagicState_normSq

private noncomputable def why24AppendixReverseNormalizedBranch
    (outcome : Why24AppendixReverseOutcome) : Why24CCZSpace :=
  (Real.sqrt 128 : Complex) •
    why24AppendixReverseCorrection outcome
      (why24AppendixReverseRawBranch outcome)

private theorem why24AppendixReverseNormalizedBranch_eq_ccz
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseNormalizedBranch outcome =
      why24CCZMagicState := by
  rw [why24AppendixReverseNormalizedBranch,
    why24AppendixReverseCorrectedRawBranch_eq_phaseUniform,
    why24CCZMagicState]

private theorem why24AppendixReverseNormalizedBranch_normSq
    (outcome : Why24AppendixReverseOutcome) :
    ‖why24AppendixReverseNormalizedBranch outcome‖ ^ 2 = 1 := by
  rw [why24AppendixReverseNormalizedBranch_eq_ccz,
    why24CCZMagicState_normSq]

/-- The normalized corrected conditional density for one measurement outcome. -/
noncomputable def why24AppendixReverseConditional
    (outcome : Why24AppendixReverseOutcome) :
    Semantics.DensityOperator Why24CCZSpace :=
  Semantics.DensityOperator.pureDensity
    (why24AppendixReverseNormalizedBranch outcome)
    (why24AppendixReverseNormalizedBranch_normSq outcome)

/-- Every source measurement outcome corrects to the same concrete `CCZ`
resource density. -/
theorem why24AppendixReverseConditional_eq_ccz
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseConditional outcome =
      why24CCZMagicStateDensity := by
  apply Semantics.DensityOperator.ext_toOperator
  simp only [why24AppendixReverseConditional,
    why24CCZMagicStateDensity,
    Semantics.DensityOperator.pureDensity_toOperator,
    why24AppendixReverseNormalizedBranch_eq_ccz]

end QEC.Coding
