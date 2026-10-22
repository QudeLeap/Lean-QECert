import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.PairedDecoderPhase
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.BareLogicalPair
import QEC.Semantics.Channels.Kraus
import QEC.Semantics.Dynamics.ThermalEncoding
import QEC.Semantics.Entropy.MatrixRelative

/-!
# The actual paired-decoder channel and its one-qubit readout

CLBT10, arXiv.02.tex:619–674 defines the observable correction transform and
its CPTP state adjoint; 794–802 and 1046–1123 give the Pauli algebra and logical
factor decoder. Here every correction is the original actual stopped X/Z
correction, at physical level n+2, including the literal C2 base. The complete
syndrome instrument is identified with the decoder of the existing dressed
logical pair on arbitrary complex operators. This is channel algebra, not
protection, zero-run normalization, successful recovery or a storage estimate.
-/
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct

abbrev Register (S : OddScale) (n : Nat) := Qubit.QubitRegister (Physical S (n+2))
abbrev Op (S : OddScale) (n : Nat) := Operator (Register S n)
variable (S : OddScale) (n : Nat)
local instance : Fintype (BDL26TransposedStoppedDecoder.XSyndromeDomain S n) := Fintype.ofFinite _
local instance : Fintype (BDL26TransposedStoppedDecoder.ZSyndromeDomain S n) := Fintype.ofFinite _

/-- Normalized Hermitian realization of the unchanged original paired correction. -/
def correctionOperator (s : Visible S n) : Op S n :=
  toHermitianQubitOperator (correction S n s)

@[simp] theorem correction_adjoint (s : Visible S n) :
    LinearMap.adjoint (correctionOperator S n s) = correctionOperator S n s :=
  adjoint_toHermitianQubitOperator_eq_self _
@[simp] theorem correction_square (s : Visible S n) :
    correctionOperator S n s * correctionOperator S n s = 1 :=
  toHermitianQubitOperator_square _

/-- A separate measurement branch for every original realizable atom. -/
def kraus : FiniteKrausFamily (Visible S n) (Register S n) (Register S n) where
  operator s := correctionOperator S n s * atom S n s

@[simp] theorem kraus_operator (s : Visible S n) :
    (kraus S n).operator s = correctionOperator S n s * atom S n s := rfl

@[simp] theorem kraus_adjoint (s : Visible S n) :
    LinearMap.adjoint ((kraus S n).operator s) = atom S n s * correctionOperator S n s := by
  rw [kraus_operator]
  change LinearMap.adjoint ((correctionOperator S n s).comp (atom S n s)) =
    (atom S n s).comp (correctionOperator S n s)
  rw [LinearMap.adjoint_comp, atom_adjoint S n s, correction_adjoint S n s]

/-- Completeness is proved from the actual unitary corrections and full resolution. -/
theorem kraus_complete : (kraus S n).Complete := by
  change (∑ s : Visible S n,
    LinearMap.adjoint ((kraus S n).operator s) * (kraus S n).operator s) = 1
  calc
    _ = ∑ s : Visible S n, atom S n s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [kraus_adjoint, kraus_operator]
      calc
        _ = atom S n s *
            (correctionOperator S n s * correctionOperator S n s) * atom S n s := by
          simp only [mul_assoc]
        _ = atom S n s := by rw [correction_square, mul_one, atom_square]
    _ = 1 := sum_atom S n

/-- The state transformation, with the original syndrome stored as a Kraus outcome. -/
def channel : QuantumChannel (Register S n) (Register S n) :=
  (kraus S n).toQuantumChannel (kraus_complete S n)

theorem channel_apply (A : Op S n) :
    channel S n A = ∑ s : Visible S n,
      correctionOperator S n s * atom S n s * A * atom S n s * correctionOperator S n s := by
  rw [channel, FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (kraus S n).operator s * (A * LinearMap.adjoint ((kraus S n).operator s)) = _
  rw [kraus_adjoint, kraus_operator]
  simp only [mul_assoc]

/-- Full Heisenberg transform; no truncation to a selected stable set. -/
def heisenberg : Op S n →ₗ[ℂ] Op S n where
  toFun O := ∑ s : Visible S n,
    atom S n s * correctionOperator S n s * O * correctionOperator S n s * atom S n s
  map_add' A B := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by simp [mul_smul_comm, smul_mul_assoc, Finset.smul_sum]

theorem heisenberg_apply (O : Op S n) :
    heisenberg S n O = ∑ s : Visible S n,
      atom S n s * correctionOperator S n s * O * correctionOperator S n s * atom S n s := rfl

@[simp] theorem heisenberg_one : heisenberg S n 1 = 1 := by
  rw [heisenberg_apply]
  have h (s : Visible S n) : atom S n s * correctionOperator S n s * 1 *
      correctionOperator S n s * atom S n s = atom S n s := by
    simp only [mul_one]
    calc
      _ = atom S n s * (correctionOperator S n s * correctionOperator S n s) * atom S n s := by
        noncomm_ring
      _ = atom S n s := by rw [correction_square, mul_one, atom_square]
  simp_rw [h]
  exact sum_atom S n

@[simp] theorem heisenberg_adjoint (O : Op S n) :
    heisenberg S n (LinearMap.adjoint O) = LinearMap.adjoint (heisenberg S n O) := by
  simp only [heisenberg_apply, map_sum, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    atom_adjoint, correction_adjoint]
  simp only [LinearMap.comp_assoc]

private theorem trace_cycle {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H] (A B C : Operator H) :
    LinearMap.trace ℂ H (A * B * C) = LinearMap.trace ℂ H (B * C * A) := by
  simpa only [Module.End.mul_eq_comp, LinearMap.comp_assoc] using
    (LinearMap.trace_comp_cycle (R := ℂ) (M := H) (N := H) (P := H)
      (f := B) (g := A) (h := C))

/-- The constructed state and observable transforms are actual trace adjoints. -/
theorem trace_duality (A O : Op S n) :
    LinearMap.trace ℂ (Register S n) (channel S n A * O) =
      LinearMap.trace ℂ (Register S n) (A * heisenberg S n O) := by
  rw [channel_apply, Finset.sum_mul, map_sum, heisenberg_apply, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [mul_assoc] using
    trace_cycle (correctionOperator S n s * atom S n s) A
      (atom S n s * correctionOperator S n s * O)

/-- Distinct original syndrome coherences are removed by the measurement. -/
theorem channel_cross_sector (s t : Visible S n) (hst : s ≠ t) (A : Op S n) :
    channel S n (atom S n s * A * atom S n t) = 0 := by
  rw [channel_apply]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hus : u = s
  · subst u
    calc
      _ = correctionOperator S n s * (atom S n s * atom S n s) * A *
          (atom S n t * atom S n s) * correctionOperator S n s := by noncomm_ring
      _ = 0 := by rw [atom_square, atom_mul_of_ne S n t s hst.symm]; simp
  · have hu := atom_mul_of_ne S n u s hus
    simp only [mul_assoc]
    rw [← mul_assoc (atom S n u), hu]
    simp

theorem channel_diagonal_sector (s : Visible S n) (A : Op S n) :
    channel S n (atom S n s * A * atom S n s) =
      correctionOperator S n s * atom S n s * A * atom S n s * correctionOperator S n s := by
  rw [channel_apply, Finset.sum_eq_single s]
  · calc
      _ = correctionOperator S n s * (atom S n s * atom S n s) * A *
          (atom S n s * atom S n s) * correctionOperator S n s := by noncomm_ring
      _ = _ := by rw [atom_square]
  · intro u _ hus
    simp only [mul_assoc]
    rw [← mul_assoc (atom S n u), atom_mul_of_ne S n u s hus]
    simp
  · simp

/-- No new correction is allocated to an unrealizable raw-labelled word. -/
def rawBranch (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (A : Op S n) : Op S n :=
  ∑ s : Visible S n,
    if CSSGibbs.realizableEmbedding (zSyndrome S (n+2)) (xSyndrome S (n+2)) s = w then
      correctionOperator S n s * atom S n s * A * atom S n s * correctionOperator S n s
    else 0

theorem rawBranch_unrealizable
    (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (hw : w ∉ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2)))
    (A : Op S n) : rawBranch S n w A = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg]
  intro h
  apply hw
  rw [← h]
  exact Finset.mem_map.mpr ⟨s, Finset.mem_univ _, rfl⟩

theorem channel_raw_sum (A : Op S n) :
    channel S n A = ∑ w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))),
      rawBranch S n w A := by
  rw [channel_apply]
  simp only [rawBranch]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  symm
  rw [Finset.sum_eq_single
    (CSSGibbs.realizableEmbedding (zSyndrome S (n+2)) (xSyndrome S (n+2)) s)]
  · rw [if_pos rfl]
  · intro w _ hw
    exact if_neg (Ne.symm hw)
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private theorem correction_conjugates (s : Visible S n) (L : Binary (Physical S (n+2))) :
    correctionOperator S n s * toHermitianQubitOperator L * correctionOperator S n s =
      StabilizerCode.DecoderDressedLogical.commutationPhase (correction S n s) L •
        toHermitianQubitOperator L := by
  unfold correctionOperator
  rw [toHermitianQubitOperator_mul_eq_commutationPhase_smul]
  rw [smul_mul_assoc, mul_assoc, toHermitianQubitOperator_square, mul_one]

/-- Literal identification with the original full CLBT phase-sum observable. -/
theorem heisenberg_normalizer (L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    heisenberg S n (toHermitianQubitOperator L) = dressed S n L := by
  rw [heisenberg_apply]
  unfold BDL26PairedDecoderPhase.dressed BDL26PairedDecoderPhase.phaseOperator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hc := (normalizer_commute_atom S n L hL s).eq
  calc
    _ = atom S n s * (correctionOperator S n s * toHermitianQubitOperator L *
        correctionOperator S n s) * atom S n s := by simp only [mul_assoc]
    _ = StabilizerCode.DecoderDressedLogical.commutationPhase (correction S n s) L •
        (atom S n s * toHermitianQubitOperator L * atom S n s) := by
      rw [correction_conjugates, mul_smul_comm, smul_mul_assoc]
    _ = StabilizerCode.DecoderDressedLogical.commutationPhase (correction S n s) L •
        (toHermitianQubitOperator L * atom S n s) := by
      apply congrArg (fun T : Op S n =>
        StabilizerCode.DecoderDressedLogical.commutationPhase (correction S n s) L • T)
      calc
        _ = (toHermitianQubitOperator L * atom S n s) * atom S n s :=
          congrArg (fun T : Op S n => T * atom S n s) hc.symm
        _ = toHermitianQubitOperator L * (atom S n s * atom S n s) :=
          mul_assoc _ _ _
        _ = toHermitianQubitOperator L * atom S n s :=
          congrArg (fun T : Op S n => toHermitianQubitOperator L * T) (atom_square S n s)
    _ = _ := by rw [mul_smul_comm]

/-- Complete logical products, without claiming multiplicativity on arbitrary operators. -/
theorem heisenberg_mul_normalizers (L M : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) (hM : (code S n).InBinaryNormalizer M) :
    heisenberg S n (toHermitianQubitOperator L * toHermitianQubitOperator M) =
      dressed S n L * dressed S n M := by
  have hsector (s : Visible S n) :
      heisenberg S n (toHermitianQubitOperator L * toHermitianQubitOperator M) * atom S n s =
        (dressed S n L * dressed S n M) * atom S n s := by
    rw [heisenberg_apply, Finset.sum_mul, Finset.sum_eq_single s]
    · have hcL := normalizer_commute_atom S n L hL s
      have hcM := normalizer_commute_atom S n M hM s
      have hcLM := hcL.mul_left hcM
      have hprod : correctionOperator S n s *
          (toHermitianQubitOperator L * toHermitianQubitOperator M) * correctionOperator S n s =
          (correctionOperator S n s * toHermitianQubitOperator L * correctionOperator S n s) *
          (correctionOperator S n s * toHermitianQubitOperator M * correctionOperator S n s) := by
        symm
        calc
          _ = correctionOperator S n s * toHermitianQubitOperator L *
              (correctionOperator S n s * correctionOperator S n s) *
              toHermitianQubitOperator M * correctionOperator S n s := by noncomm_ring
          _ = _ := by rw [correction_square]; simp [mul_assoc]
      calc
        _ = atom S n s *
            (correctionOperator S n s *
              (toHermitianQubitOperator L * toHermitianQubitOperator M) *
              correctionOperator S n s) * atom S n s := by
          simp only [mul_assoc, atom_square]
        _ = (commutationPhase (correction S n s) L * commutationPhase (correction S n s) M) •
            ((toHermitianQubitOperator L * toHermitianQubitOperator M) * atom S n s) := by
          rw [hprod, correction_conjugates, correction_conjugates, smul_mul_smul_comm,
            mul_smul_comm, smul_mul_assoc, ← hcLM.eq, mul_assoc, atom_square]
        _ = _ := by
          symm
          rw [mul_assoc, dressed_mul_atom, mul_smul_comm, hcM.eq, ← mul_assoc,
            dressed_mul_atom, smul_mul_assoc, smul_smul]
          rw [mul_comm (commutationPhase (correction S n s) M)
            (commutationPhase (correction S n s) L)]
          exact congrArg
            (fun T : Op S n =>
              (commutationPhase (correction S n s) L * commutationPhase (correction S n s) M) • T)
            ((mul_assoc (toHermitianQubitOperator L) (atom S n s) (toHermitianQubitOperator M)).trans
              ((congrArg (fun T : Op S n => toHermitianQubitOperator L * T) hcM.eq.symm).trans
                (mul_assoc (toHermitianQubitOperator L) (toHermitianQubitOperator M) (atom S n s)).symm))
    · intro t _ hts
      simp only [mul_assoc]
      rw [atom_mul_of_ne S n t s hts]
      simp
    · simp
  calc
    _ = heisenberg S n (toHermitianQubitOperator L * toHermitianQubitOperator M) *
        (∑ s : Visible S n, atom S n s) := by rw [sum_atom, mul_one]
    _ = (dressed S n L * dressed S n M) * (∑ s : Visible S n, atom S n s) := by
      simp_rw [Finset.mul_sum, hsector]
    _ = _ := by rw [sum_atom, mul_one]

abbrev bareX : Op S n := BDL26BareLogicalPair.Xbar S (n+2)
abbrev bareZ : Op S n := BDL26BareLogicalPair.Zbar S (n+2)
def bareY : Op S n := Complex.I • (bareX S n * bareZ S n)
abbrev dressedX : Op S n := dressed S n (BDL26BareLogicalPair.logicalX S (n+2))
abbrev dressedZ : Op S n := dressed S n (BDL26BareLogicalPair.logicalZ S (n+2))
def dressedY : Op S n := Complex.I • (dressedX S n * dressedZ S n)

@[simp] theorem heisenberg_X : heisenberg S n (bareX S n) = dressedX S n :=
  heisenberg_normalizer S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
@[simp] theorem heisenberg_Z : heisenberg S n (bareZ S n) = dressedZ S n :=
  heisenberg_normalizer S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
@[simp] theorem heisenberg_Y : heisenberg S n (bareY S n) = dressedY S n := by
  rw [bareY, map_smul, heisenberg_mul_normalizers S n _ _
    (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
    (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))]
  rfl

theorem dressed_anticommute : dressedX S n * dressedZ S n = -(dressedZ S n * dressedX S n) := by
  rw [← heisenberg_mul_normalizers S n _ _
    (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
    (BDL26BareLogicalPair.logicalZ_normalizer S (n+2)),
    BDL26BareLogicalPair.Xbar_Zbar_anticommute, map_neg,
    heisenberg_mul_normalizers S n _ _
      (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
      (BDL26BareLogicalPair.logicalX_normalizer S (n+2))]

/-- Both pair interfaces are derived from the actual operators, never supplied. -/
def barePauliPair : ThermalEncoding.PauliLikePair (Register S n) where
  x := bareX S n
  z := bareZ S n
  x_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact BDL26BareLogicalPair.Xbar_adjoint S (n+2)
  z_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact BDL26BareLogicalPair.Zbar_adjoint S (n+2)
  x_sq := BDL26BareLogicalPair.Xbar_square S (n+2)
  z_sq := BDL26BareLogicalPair.Zbar_square S (n+2)
  anticommute := BDL26BareLogicalPair.Xbar_Zbar_anticommute S (n+2)

def dressedPauliPair : ThermalEncoding.PauliLikePair (Register S n) where
  x := dressedX S n
  z := dressedZ S n
  x_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact dressed_adjoint S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
  z_symmetric := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
    exact dressed_adjoint S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
  x_sq := dressed_square S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
  z_sq := dressed_square S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
  anticommute := dressed_anticommute S n

@[simp] theorem dressedY_adjoint : LinearMap.adjoint (dressedY S n) = dressedY S n := by
  have hx : LinearMap.adjoint (dressedX S n) = dressedX S n :=
    dressed_adjoint S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
  have hz : LinearMap.adjoint (dressedZ S n) = dressedZ S n :=
    dressed_adjoint S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))
  have hm : LinearMap.adjoint (dressedX S n * dressedZ S n) = dressedZ S n * dressedX S n := by
    change LinearMap.adjoint ((dressedX S n).comp (dressedZ S n)) =
      (dressedZ S n).comp (dressedX S n)
    rw [LinearMap.adjoint_comp, hx, hz]
  have hzx : dressedZ S n * dressedX S n = -(dressedX S n * dressedZ S n) :=
    (dressedPauliPair S n).z_x_anticommute
  rw [dressedY, map_smulₛₗ, hm, hzx]
  simp

theorem dressedY_square : dressedY S n * dressedY S n = 1 := by
  have hzx : dressedZ S n * dressedX S n = -(dressedX S n * dressedZ S n) :=
    (dressedPauliPair S n).z_x_anticommute
  have hxx : dressedX S n * dressedX S n = 1 := (dressedPauliPair S n).x_sq
  have hzz : dressedZ S n * dressedZ S n = 1 := (dressedPauliPair S n).z_sq
  rw [dressedY, smul_mul_smul_comm]
  have h : (dressedX S n * dressedZ S n) * (dressedX S n * dressedZ S n) = -1 := by
    calc
      _ = dressedX S n * (dressedZ S n * dressedX S n) * dressedZ S n := by simp only [mul_assoc]
      _ = -1 := by
        rw [hzx]
        calc
          _ = -((dressedX S n * dressedX S n) * (dressedZ S n * dressedZ S n)) := by noncomm_ring
          _ = -1 := by rw [hxx, hzz, one_mul]
  rw [h, Complex.I_mul_I]
  simp

/-- Actual channel readout: measure/correct, then read the existing bare logical factor. -/
def readout : QuantumChannel (Register S n) Qubit.QubitSpace :=
  QuantumChannel.comp (barePauliPair S n).thermalDecoding (channel S n)

/-- The true single-qubit Y convention used by both factor decoders. -/
theorem qubitY_eq : Qubit.pauliY = Complex.I • (Qubit.pauliX * Qubit.pauliZ) := by
  ext v b
  fin_cases b <;> simp [Qubit.pauliY_apply, Qubit.pauliZ_apply, Qubit.zPhase,
    Module.End.mul_apply, Qubit.pauliX_apply] <;> ring

private theorem decoding_trace {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (A : Operator H) (O : Operator Qubit.QubitSpace) :
    LinearMap.trace ℂ Qubit.QubitSpace (P.thermalDecoding A * O) =
      LinearMap.trace ℂ H (A * P.factorization.conjOperator
        (TensorProduct.map O (1 : Operator P.AuxiliarySpace))) := by
  change LinearMap.trace ℂ Qubit.QubitSpace
    (partialTraceRightRaw Qubit.QubitSpace P.AuxiliarySpace
      (P.factorization.symm.conjOperator A) * O) = _
  rw [show LinearMap.trace ℂ Qubit.QubitSpace
      (partialTraceRightRaw Qubit.QubitSpace P.AuxiliarySpace
        (P.factorization.symm.conjOperator A) * O) =
      LinearMap.trace ℂ (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace)
        (P.factorization.symm.conjOperator A * TensorProduct.map O (1 : Operator P.AuxiliarySpace)) by
    exact FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
      (stdOrthonormalBasis ℂ P.AuxiliarySpace) _ _]
  rw [← P.factorization.trace_conjOperator,
    P.factorization.conjOperator_mul, P.factorization.conjOperator_symm_conjOperator]

private theorem pair_decoding_X {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (A : Operator H) :
    LinearMap.trace ℂ Qubit.QubitSpace (P.thermalDecoding A * Qubit.pauliX) =
      LinearMap.trace ℂ H (A * P.x) := by
  rw [decoding_trace]
  exact congrArg (fun T => LinearMap.trace ℂ H (A * T)) P.conj_tensorPauliX
private theorem pair_decoding_Z {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (A : Operator H) :
    LinearMap.trace ℂ Qubit.QubitSpace (P.thermalDecoding A * Qubit.pauliZ) =
      LinearMap.trace ℂ H (A * P.z) := by
  rw [decoding_trace]
  exact congrArg (fun T => LinearMap.trace ℂ H (A * T)) P.conj_tensorPauliZ

private theorem pair_decoding_Y {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (A : Operator H) :
    LinearMap.trace ℂ Qubit.QubitSpace (P.thermalDecoding A * Qubit.pauliY) =
      LinearMap.trace ℂ H (A * (Complex.I • (P.x * P.z))) := by
  rw [decoding_trace, qubitY_eq]
  have hm : TensorProduct.map (Qubit.pauliX * Qubit.pauliZ) (1 : Operator P.AuxiliarySpace) =
      P.tensorPauliX * P.tensorPauliZ := by
    ext q a
    simp [ThermalEncoding.PauliLikePair.tensorPauliX,
      ThermalEncoding.PauliLikePair.tensorPauliZ, Module.End.mul_apply]
  rw [TensorProduct.map_smul_left, hm]
  have hs (c : ℂ) (T : Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace)) :
      P.factorization.conjOperator (c • T) = c • P.factorization.conjOperator T :=
    P.factorization.conjOperatorLinearMap.map_smul c T
  rw [hs, P.factorization.conjOperator_mul, P.conj_tensorPauliX, P.conj_tensorPauliZ]

@[simp] theorem readout_trace_I (A : Op S n) :
    LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * 1) =
      LinearMap.trace ℂ (Register S n) (A * 1) := by
  simp only [mul_one]
  exact (readout S n).trace_map A

theorem readout_trace_X (A : Op S n) :
    LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * Qubit.pauliX) =
      LinearMap.trace ℂ (Register S n) (A * dressedX S n) := by
  change LinearMap.trace ℂ Qubit.QubitSpace
    ((barePauliPair S n).thermalDecoding (channel S n A) * Qubit.pauliX) = _
  rw [pair_decoding_X]
  exact (trace_duality S n A (bareX S n)).trans (by rw [heisenberg_X])

theorem readout_trace_Z (A : Op S n) :
    LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * Qubit.pauliZ) =
      LinearMap.trace ℂ (Register S n) (A * dressedZ S n) := by
  change LinearMap.trace ℂ Qubit.QubitSpace
    ((barePauliPair S n).thermalDecoding (channel S n A) * Qubit.pauliZ) = _
  rw [pair_decoding_Z]
  exact (trace_duality S n A (bareZ S n)).trans (by rw [heisenberg_Z])

theorem readout_trace_Y (A : Op S n) :
    LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * Qubit.pauliY) =
      LinearMap.trace ℂ (Register S n) (A * dressedY S n) := by
  change LinearMap.trace ℂ Qubit.QubitSpace
    ((barePauliPair S n).thermalDecoding (channel S n A) * Qubit.pauliY) = _
  rw [pair_decoding_Y]
  exact (trace_duality S n A (bareY S n)).trans (by rw [heisenberg_Y])

/-- Complete complex Pauli spanning; no Hermitian-input restriction. -/
theorem qubit_pauli_span (A : Operator Qubit.QubitSpace) :
    ∃ a b c d : ℂ, A = a • (1 : Operator Qubit.QubitSpace) + b • Qubit.pauliX +
      c • Qubit.pauliY + d • Qubit.pauliZ := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := Matrix.toEuclideanLin.symm A
  let a := (M 0 0 + M 1 1)/2
  let b := (M 0 1 + M 1 0)/2
  let c := Complex.I*(M 0 1-M 1 0)/2
  let d := (M 0 0-M 1 1)/2
  refine ⟨a,b,c,d,?_⟩
  have hm : M = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + b • Qubit.pauliXMatrix +
      c • Qubit.pauliYMatrix + d • Qubit.pauliZMatrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a,b,c,d,Qubit.pauliXMatrix,Qubit.pauliYMatrix,Qubit.pauliZMatrix,
        Qubit.flipBit,Qubit.zPhase,Matrix.one_apply] <;> ring_nf <;> norm_num <;> ring
  have h := congrArg Matrix.toEuclideanLin hm
  simpa [M,Qubit.pauliX,Qubit.pauliY,Qubit.pauliZ,Module.End.one_eq_id] using h

/-- Four complex moments separate arbitrary qubit operators. -/
theorem qubit_trace_ext (A B : Operator Qubit.QubitSpace)
    (hI : LinearMap.trace ℂ _ (A * 1) = LinearMap.trace ℂ _ (B * 1))
    (hX : LinearMap.trace ℂ _ (A * Qubit.pauliX) = LinearMap.trace ℂ _ (B * Qubit.pauliX))
    (hY : LinearMap.trace ℂ _ (A * Qubit.pauliY) = LinearMap.trace ℂ _ (B * Qubit.pauliY))
    (hZ : LinearMap.trace ℂ _ (A * Qubit.pauliZ) = LinearMap.trace ℂ _ (B * Qubit.pauliZ)) : A = B := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro O
  obtain ⟨a,b,c,d,hO⟩ := qubit_pauli_span O
  have ht (T : Operator Qubit.QubitSpace) :
      LinearMap.trace ℂ _ (O * T) = LinearMap.trace ℂ _ (T * O) := by
    simpa only [mul_one] using trace_cycle O T (1 : Operator Qubit.QubitSpace)
  change LinearMap.trace ℂ _ (O * A) = LinearMap.trace ℂ _ (O * B)
  rw [ht A, ht B, hO]
  simp only [mul_add, mul_smul_comm, map_add, map_smul, hI,hX,hY,hZ]

/-- Equality of complete channels, not merely equality on selected states. -/
theorem readout_eq_dressed_decoder_apply (A : Op S n) :
    readout S n A = (dressedPauliPair S n).thermalDecoding A := by
  apply qubit_trace_ext
  · simp only [mul_one]
    exact ((readout S n).trace_map A).trans
      (((dressedPauliPair S n).thermalDecoding).trace_map A).symm
  · exact (readout_trace_X S n A).trans (pair_decoding_X (dressedPauliPair S n) A).symm
  · exact (readout_trace_Y S n A).trans (pair_decoding_Y (dressedPauliPair S n) A).symm
  · exact (readout_trace_Z S n A).trans (pair_decoding_Z (dressedPauliPair S n) A).symm

theorem readout_eq_dressed_decoder : readout S n = (dressedPauliPair S n).thermalDecoding := by
  cases hR : readout S n
  cases hD : (dressedPauliPair S n).thermalDecoding
  congr 1
  apply LinearMap.ext
  intro A
  simpa only [hR, hD] using readout_eq_dressed_decoder_apply S n A

/-- The actual logical matrix algebra embedded by the derived factorization. -/
def pairEmbedding {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) : Operator Qubit.QubitSpace →ₗ[ℂ] Operator H where
  toFun O := P.factorization.conjOperator (TensorProduct.map O (1 : Operator P.AuxiliarySpace))
  map_add' A B := by
    rw [TensorProduct.map_add_left]
    exact P.factorization.conjOperatorLinearMap.map_add _ _
  map_smul' c A := by
    rw [TensorProduct.map_smul_left]
    exact P.factorization.conjOperatorLinearMap.map_smul _ _

theorem pairEmbedding_mul {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (A B : Operator Qubit.QubitSpace) :
    pairEmbedding P (A * B) = pairEmbedding P A * pairEmbedding P B := by
  change P.factorization.conjOperator _ = P.factorization.conjOperator _ * P.factorization.conjOperator _
  rw [← P.factorization.conjOperator_mul, ← TensorProduct.map_mul]
  simp only [mul_one]

/-- The complete logical-algebra diagram follows from actual channel trace duality. -/
theorem heisenberg_logical_algebra (O : Operator Qubit.QubitSpace) :
    heisenberg S n (pairEmbedding (barePauliPair S n) O) =
      pairEmbedding (dressedPauliPair S n) O := by
  apply Semantics.operator_ext_of_trace_comp_right_eq
  intro A
  change LinearMap.trace ℂ (Register S n)
      (A * heisenberg S n (pairEmbedding (barePauliPair S n) O)) = _
  calc
    _ = LinearMap.trace ℂ (Register S n)
        (channel S n A * pairEmbedding (barePauliPair S n) O) :=
      (trace_duality S n A _).symm
    _ = LinearMap.trace ℂ Qubit.QubitSpace (readout S n A * O) :=
      (decoding_trace (barePauliPair S n) (channel S n A) O).symm
    _ = LinearMap.trace ℂ (Register S n)
        (A * pairEmbedding (dressedPauliPair S n) O) := by
      rw [readout_eq_dressed_decoder_apply]
      exact decoding_trace (dressedPauliPair S n) A O

theorem heisenberg_logical_mul (A B : Operator Qubit.QubitSpace) :
    heisenberg S n (pairEmbedding (barePauliPair S n) A * pairEmbedding (barePauliPair S n) B) =
      heisenberg S n (pairEmbedding (barePauliPair S n) A) *
        heisenberg S n (pairEmbedding (barePauliPair S n) B) := by
  rw [← pairEmbedding_mul, heisenberg_logical_algebra, heisenberg_logical_algebra,
    heisenberg_logical_algebra, pairEmbedding_mul]

theorem readout_encode (sigma : DensityOperator (dressedPauliPair S n).AuxiliarySpace)
    (A : Operator Qubit.QubitSpace) :
    readout S n ((dressedPauliPair S n).thermalEncoding sigma A) = A := by
  rw [readout_eq_dressed_decoder]
  exact (dressedPauliPair S n).thermalDecoding_thermalEncoding sigma A

theorem readout_encode_density (sigma : DensityOperator (dressedPauliPair S n).AuxiliarySpace)
    (rho : DensityOperator Qubit.QubitSpace) :
    (readout S n).mapDensity ((dressedPauliPair S n).thermalEncoding sigma |>.mapDensity rho) = rho := by
  apply DensityOperator.ext_toOperator
  exact readout_encode S n sigma rho.toOperator

/-- Exact finite reference amplification of the complete operator identity. -/
theorem readout_reference (r : Nat) (A : OperatorMatrix r (Register S n)) :
    OperatorMatrix.map (readout S n).toLinearMap A =
      OperatorMatrix.map (dressedPauliPair S n).thermalDecoding.toLinearMap A := by
  rw [readout_eq_dressed_decoder]

/-- All original source-even levels in the existing C2-inclusive domain. -/
theorem source_even_readout (k : Nat) (hk : 1 ≤ k) :
    ∃ n : Nat, n+2 = 2*k ∧ readout S n = (dressedPauliPair S n).thermalDecoding :=
  ⟨2*(k-1), BDL26TransposedStoppedDecoder.source_even_level k hk,
    readout_eq_dressed_decoder S _⟩

end QEC.Coding.BDL26PairedDecoderChannel
end
