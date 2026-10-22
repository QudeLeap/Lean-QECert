import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDefectProtection
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.PairedDecoderGibbs
import QEC.Semantics.Dynamics.ProtectedObservableDecay

/-!
# Fixed actual-channel logical-defect thermal storage

Internal finite consequences of CLBT10 `arXiv.02.tex:778–855,1046–1123` and
BDL26 `paper.tex:1255–1268`. The original paired readout and actual-H thermal
encoder are fixed throughout. The exact whole-history bad mass gives8/48;
32/192 is conditional on two separately supplied sector envelopes, as in
`paper.tex:3818` and the frozen terminal contract. No small-tail, decoder
stability, geometry, asymptotic lifetime or public theorem is proved here.
-/
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct

/-! The generic helpers keep all tensor carriers fixed before actual specialization. -/
section Embedding
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [FiniteQuantumSystem K]

private theorem embedding_one (P : ThermalEncoding.PauliLikePair K) :
    pairEmbedding P 1 = 1 := by
  change P.factorization.conjOperator (TensorProduct.map 1 1) = 1
  have ht : TensorProduct.map (1 : Operator Qubit.QubitSpace)
      (1 : Operator P.AuxiliarySpace) = 1 := by
    ext q a
    simp
  rw [ht, UnitaryTransport.conjOperator_one]

private theorem embedding_X (P : ThermalEncoding.PauliLikePair K) :
    pairEmbedding P Qubit.pauliX = P.x := P.conj_tensorPauliX

private theorem embedding_Z (P : ThermalEncoding.PauliLikePair K) :
    pairEmbedding P Qubit.pauliZ = P.z := P.conj_tensorPauliZ

private theorem embedding_Y (P : ThermalEncoding.PauliLikePair K) :
    pairEmbedding P Qubit.pauliY = Complex.I • (P.x * P.z) := by
  rw [qubitY_eq, map_smul, pairEmbedding_mul, embedding_X, embedding_Z]

private theorem embedding_span (P : ThermalEncoding.PauliLikePair K)
    (A : Operator Qubit.QubitSpace) :
    ∃ a b c d : ℂ, pairEmbedding P A =
      a • (1 : Operator K) + b • P.x + c • (Complex.I • (P.x * P.z)) + d • P.z := by
  obtain ⟨a,b,c,d,hA⟩ := qubit_pauli_span A
  refine ⟨a,b,c,d,?_⟩
  simp only [hA, map_add, map_smul, embedding_one, embedding_X, embedding_Y, embedding_Z]

private theorem commute_scale_right (A B : Operator K) (h : Commute A B) (c : ℂ) :
    Commute A (c • B) := by
  rw [Commute]
  ext x
  simpa [Module.End.mul_apply] using
    congrArg (fun T : Operator K => c • T x) h.eq

private theorem commute_scale_left (A B : Operator K) (h : Commute A B) (c : ℂ) :
    Commute (c • A) B := (commute_scale_right B A h.symm c).symm

private theorem embedding_commute (P : ThermalEncoding.PauliLikePair K)
    (A : Operator Qubit.QubitSpace) (R : Operator K)
    (hx : Commute P.x R) (hz : Commute P.z R) :
    Commute (pairEmbedding P A) R := by
  obtain ⟨a,b,c,d,hA⟩ := embedding_span P A
  rw [hA]
  have hy := commute_scale_left (P.x * P.z) R (hx.mul_left hz) Complex.I
  exact (((commute_scale_left 1 R (Commute.one_left R) a).add_left
    (commute_scale_left P.x R hx b)).add_left
      (commute_scale_left _ R hy c)).add_left (commute_scale_left P.z R hz d)

private theorem embedding_protected {I : Type} [Fintype I]
    (P : ThermalEncoding.PauliLikePair K) (J : I → Operator K) (R : Operator K)
    (hx : JumpProtected J P.x R) (hz : JumpProtected J P.z R)
    (hzR : Commute P.z R) (A : Operator Qubit.QubitSpace) :
    JumpProtected J (pairEmbedding P A) R := by
  obtain ⟨a,b,c,d,hA⟩ := embedding_span P A
  rw [hA]
  have hy := (hx.mul_of_commute_projector hz hzR).smul Complex.I
  exact ((((JumpProtected.one J R).smul a).add (hx.smul b)).add
    (hy.smul c)).add (hz.smul d)

private theorem observable_symmetric_generic (P : ThermalEncoding.PauliLikePair K)
    (eta : DensityOperator Qubit.QubitSpace) : (P.encodedObservable eta).IsSymmetric := by
  unfold ThermalEncoding.PauliLikePair.encodedObservable
  apply (P.factorization.isPositive_conjOperator ?_).isSymmetric
  exact ThermalEncoding.tensorMap_positive ((2 : ℂ) • eta.toOperator)
    (1 : Operator P.AuxiliarySpace)
    (eta.positive.smul_of_nonneg
      (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)) LinearMap.isPositive_one
end Embedding

variable (S : OddScale) (n : Nat)
local instance : Fintype (BDL26TransposedStoppedDecoder.XSyndromeDomain S n) := Fintype.ofFinite _
local instance : Fintype (BDL26TransposedStoppedDecoder.ZSyndromeDomain S n) := Fintype.ofFinite _

abbrev Rate := BDL26CSSDaviesLocality.CouplingIndex S (n+2) →
  BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ
abbrev logical := dressedPauliPair S n
abbrev projector := BDL26LogicalDefectProtection.protectedProjector S n
abbrev reference (beta : ℝ) := gibbs S (n+2) beta
abbrev encoder (beta : ℝ) := BDL26PairedDecoderGibbs.encoding S n beta
abbrev decoder := BDL26PairedDecoderChannel.readout S n
abbrev observable (eta : DensityOperator Qubit.QubitSpace) := (logical S n).encodedObservable eta
abbrev jumps (rate : Rate S n) := BDL26BoundedRateDavies.jump S (n+2) rate

def evolution (rate : Rate S n) (t : ℝ) (ht : 0 ≤ t) :
    QuantumChannel (Register S n) (Register S n) :=
  finiteLindbladEvolutionChannel (hamiltonian S (n+2)) (jumps S n rate)
    (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2)) t ht

/-- The source self-adjoint induced norm of the actual dissipator, excluding H. -/
def g (rate : Rate S n) : ℝ :=
  selfAdjointTraceNormOneToOne (BDL26BoundedRateDavies.dissipator S (n+2) rate)

def mass (beta : ℝ) : ℝ := clbtGibbsTailMass (projector S n) (reference S n beta)
def xMass (beta : ℝ) : ℝ := BDL26TwoSectorBadProjector.pX S (n+2) beta
  (BDL26LogicalDefectProtection.badX S n)
def zMass (beta : ℝ) : ℝ := BDL26TwoSectorBadProjector.pZ S (n+2) beta
  (BDL26LogicalDefectProtection.badZ S n)
def qubits : ℝ := Fintype.card (Physical S (n+2))

def encodedError (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  traceNorm (((evolution S n rate t ht).mapDensity ((encoder S n beta).mapDensity eta)).toOperator -
    ((encoder S n beta).mapDensity eta).toOperator)

def decodedError (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  traceNorm (((decoder S n).mapDensity
    ((evolution S n rate t ht).mapDensity ((encoder S n beta).mapDensity eta))).toOperator - eta.toOperator)

theorem left_inverse (beta : ℝ) (A : Operator Qubit.QubitSpace) :
    decoder S n (encoder S n beta A) = A := BDL26PairedDecoderGibbs.readout_encoding S n beta A

theorem left_inverse_density (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    (decoder S n).mapDensity ((encoder S n beta).mapDensity eta) = eta :=
  BDL26PairedDecoderGibbs.readout_encoding_density S n beta eta

theorem logical_relations :
    (logical S n).x.IsSymmetric ∧ (logical S n).z.IsSymmetric ∧
    (logical S n).x * (logical S n).x = 1 ∧ (logical S n).z * (logical S n).z = 1 ∧
    (logical S n).x * (logical S n).z = -((logical S n).z * (logical S n).x) :=
  ⟨(logical S n).x_symmetric, (logical S n).z_symmetric,
    (logical S n).x_sq, (logical S n).z_sq, (logical S n).anticommute⟩

theorem hamiltonian_X : Commute (hamiltonian S (n+2)) (logical S n).x :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm

theorem hamiltonian_Z : Commute (hamiltonian S (n+2)) (logical S n).z :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))).symm

theorem projector_properties : IsStarProjection (projector S n) ∧
    Commute (projector S n) (hamiltonian S (n+2)) ∧
    Commute (projector S n) (logical S n).x ∧ Commute (projector S n) (logical S n).z :=
  ⟨BDL26LogicalDefectProtection.projector_projection S n,
    (BDL26LogicalDefectProtection.projector_hamiltonian S n).symm,
    (BDL26LogicalDefectProtection.projector_dressed_X S n).symm,
    (BDL26LogicalDefectProtection.projector_dressed_Z S n).symm⟩

theorem physical_XYZ_protected : BDL26LogicalDefectProtection.Protects S n
    (BDL26LogicalDefectProtection.good S n) := BDL26LogicalDefectProtection.actual_XYZ_protected S n

theorem jump_X (rate : Rate S n) : JumpProtected (jumps S n rate) (logical S n).x (projector S n) :=
  BDL26LogicalDefectProtection.actual_jumps_X S n rate

theorem jump_Z (rate : Rate S n) : JumpProtected (jumps S n rate) (logical S n).z (projector S n) :=
  BDL26LogicalDefectProtection.actual_jumps_Z S n rate

theorem observable_eq_embedding (eta : DensityOperator Qubit.QubitSpace) :
    observable S n eta = (2 : ℂ) • pairEmbedding (logical S n) eta.toOperator := by
  change pairEmbedding (logical S n) ((2 : ℂ) • eta.toOperator) = _
  exact map_smul (pairEmbedding (logical S n)) (2 : ℂ) eta.toOperator

theorem observable_norm (eta : DensityOperator Qubit.QubitSpace) :
    operatorNorm (observable S n eta) ≤ 2 := (logical S n).encodedObservable_operatorNorm_le_two eta

theorem observable_symmetric (eta : DensityOperator Qubit.QubitSpace) :
    (observable S n eta).IsSymmetric := observable_symmetric_generic (logical S n) eta

theorem observable_projector (eta : DensityOperator Qubit.QubitSpace) :
    Commute (observable S n eta) (projector S n) :=
  embedding_commute (logical S n) ((2 : ℂ) • eta.toOperator) (projector S n)
    (projector_properties S n).2.2.1.symm (projector_properties S n).2.2.2.symm

theorem observable_hamiltonian (eta : DensityOperator Qubit.QubitSpace) :
    Commute (observable S n eta) (hamiltonian S (n+2)) :=
  embedding_commute (logical S n) ((2 : ℂ) • eta.toOperator) (hamiltonian S (n+2))
    (hamiltonian_X S n).symm (hamiltonian_Z S n).symm

theorem observable_protected (rate : Rate S n) (eta : DensityOperator Qubit.QubitSpace) :
    JumpProtected (jumps S n rate) (observable S n eta) (projector S n) :=
  embedding_protected (logical S n) (jumps S n rate) (projector S n)
    (jump_X S n rate) (jump_Z S n rate) (projector_properties S n).2.2.2.symm
    ((2 : ℂ) • eta.toOperator)

theorem encoder_mul_reference (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encoder S n beta eta.toOperator = observable S n eta * (reference S n beta).toOperator := by
  rw [show reference S n beta = (logical S n).thermalReferenceState
    (BDL26PairedDecoderGibbs.auxiliaryGibbs S n beta) from BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference S n beta]
  exact (logical S n).thermalEncoding_eq_encodedObservable_mul _ eta

theorem encoder_reference_mul (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encoder S n beta eta.toOperator = (reference S n beta).toOperator * observable S n eta := by
  rw [show reference S n beta = (logical S n).thermalReferenceState
    (BDL26PairedDecoderGibbs.auxiliaryGibbs S n beta) from BDL26PairedDecoderGibbs.gibbs_eq_thermal_reference S n beta]
  exact (logical S n).thermalEncoding_eq_mul_encodedObservable _ eta

theorem observable_reference (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    Commute (observable S n eta) (reference S n beta).toOperator :=
  (encoder_mul_reference S n beta eta).symm.trans (encoder_reference_mul S n beta eta)

theorem projector_reference (beta : ℝ) : Commute (projector S n) (reference S n beta).toOperator :=
  (BDL26TwoSectorBadProjector.gibbs_commute S (n+2) beta
    (BDL26LogicalDefectProtection.good S n)).symm

theorem hamiltonian_reference (beta : ℝ) :
    Commute (hamiltonian S (n+2)) (reference S n beta).toOperator := by
  rw [BDL26BoundedRateDavies.actual_gibbs_eq]
  exact Davies.hamiltonianGibbs_commutes _ _ beta

theorem hamiltonian_encoder (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    Commute (hamiltonian S (n+2)) (encoder S n beta eta.toOperator) := by
  rw [encoder_mul_reference]
  exact (observable_hamiltonian S n eta).symm.mul_right (hamiltonian_reference S n beta)

theorem stationary (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega) :
    lindbladDissipator (jumps S n rate) (reference S n beta).toOperator = 0 :=
  BDL26BoundedRateDavies.gibbs_stationary S (n+2) rate beta hn hDB

theorem g_eq_lindblad (rate : Rate S n) : g S n rate = lindbladDissipatorNorm (jumps S n rate) := rfl

theorem g_nonneg (rate : Rate S n) : 0 ≤ g S n rate :=
  selfAdjointTraceNormOneToOne_nonneg _

theorem g_le (rate : Rate S n) (hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax) :
    g S n rate ≤ 6 * qubits S n * hmax :=
  BDL26BoundedRateDavies.dissipator_selfAdjointTraceNorm_le S (n+2) rate hmax hm hn hu

theorem mass_exact (beta : ℝ) :
    mass S n beta = xMass S n beta + zMass S n beta - xMass S n beta * zMass S n beta :=
  BDL26LogicalDefectProtection.tail_exact S n beta

theorem sector_bounds (beta : ℝ) :
    (0 ≤ xMass S n beta ∧ xMass S n beta ≤ 1) ∧ (0 ≤ zMass S n beta ∧ zMass S n beta ≤ 1) :=
  ⟨BDL26TwoSectorBadProjector.pX_bounds S (n+2) beta _,
    BDL26TwoSectorBadProjector.pZ_bounds S (n+2) beta _⟩

theorem mass_bounds (beta : ℝ) : 0 ≤ mass S n beta ∧ mass S n beta ≤ 1 := by
  rw [mass_exact]
  obtain ⟨hx,hz⟩ := sector_bounds S n beta
  constructor
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hz.2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hz.2)]

theorem mass_union (beta : ℝ) : mass S n beta ≤ xMass S n beta + zMass S n beta :=
  BDL26LogicalDefectProtection.tail_union_bound S n beta

/-- The actual encoded density consumes all four-block inputs proved above. -/
theorem generator_bound (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) :
    traceNorm (lindbladDissipator (jumps S n rate) (encoder S n beta eta.toOperator)) ≤
      8 * g S n rate * mass S n beta := by
  rw [encoder_mul_reference, g_eq_lindblad]
  exact clbtFourBlockGeneratorEstimate (jumps S n rate) (observable S n eta)
    (projector S n) (reference S n beta) (observable_protected S n rate eta)
    (observable_symmetric S n eta) (projector_properties S n).1
    (observable_projector S n eta) (observable_reference S n beta eta)
    (projector_reference S n beta) (stationary S n rate beta hn hDB) (observable_norm S n eta)

theorem encoded_nonneg (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ encodedError S n rate beta eta t ht := traceNorm_nonneg _

theorem decoded_nonneg (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ decodedError S n rate beta eta t ht := traceNorm_nonneg _

/-- Full Hamiltonian evolution, rather than a dissipator-only replacement. -/
theorem encoded_bound (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta := by
  have htime := finiteLindbladEvolution_traceNorm_sub_le_time_mul
    (hamiltonian S (n+2)) (jumps S n rate)
    (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2)) (encoder S n beta eta.toOperator)
    ((encoder S n beta).map_isSymmetric eta.positive.isSymmetric)
    (hamiltonian_encoder S n beta eta) t ht
  have hlocal := mul_le_mul_of_nonneg_left (generator_bound S n rate beta hn hDB eta) ht
  calc
    encodedError S n rate beta eta t ht =
        traceNorm (finiteLindbladEvolutionLinearMap (hamiltonian S (n+2)) (jumps S n rate) t
          (encoder S n beta eta.toOperator) - encoder S n beta eta.toOperator) := rfl
    _ ≤ t * traceNorm (lindbladDissipator (jumps S n rate) (encoder S n beta eta.toOperator)) := htime
    _ ≤ t * (8 * g S n rate * mass S n beta) := hlocal
    _ = 8 * t * g S n rate * mass S n beta := by ring

/-- Contract the same physical readout, using its actual left inverse. -/
theorem decoded_le_encoded (rate : Rate S n) (beta : ℝ)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    decodedError S n rate beta eta t ht ≤ encodedError S n rate beta eta t ht := by
  have hc := (decoder S n).traceNorm_density_sub_le
    ((evolution S n rate t ht).mapDensity ((encoder S n beta).mapDensity eta))
    ((encoder S n beta).mapDensity eta)
  have hl : decoder S n ((encoder S n beta).mapDensity eta).toOperator = eta.toOperator := by
    rw [← QuantumChannel.mapDensity_toOperator]
    exact congrArg DensityOperator.toOperator (left_inverse_density S n beta eta)
  rw [hl] at hc
  simpa only [decodedError, encodedError, QuantumChannel.mapDensity_toOperator] using hc

theorem decoded_bound (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    decodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta :=
  (decoded_le_encoded S n rate beta eta t ht).trans (encoded_bound S n rate beta hn hDB eta t ht)

/-- Both errors for every state and nonnegative time, with the source constant8. -/
theorem storage_eight (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta ∧
    decodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta :=
  ⟨encoded_bound S n rate beta hn hDB eta t ht, decoded_bound S n rate beta hn hDB eta t ht⟩

theorem clock_comparison (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (t : ℝ) (ht : 0 ≤ t) :
    8 * t * g S n rate * mass S n beta ≤ 48 * t * qubits S n * hmax * mass S n beta := by
  calc
    _ ≤ 8 * t * (6 * qubits S n * hmax) * mass S n beta :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (g_le S n rate hmax hm hn hu) (by positivity))
        (mass_bounds S n beta).1
    _ = _ := by ring

/-- The clock counts3N physical axes and uses the self-adjoint induced norm. -/
theorem storage_forty_eight (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta ∧
    decodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta := by
  obtain ⟨he,hd⟩ := storage_eight S n rate beta hn hDB eta t ht
  have hc := clock_comparison S n rate beta hmax hm hn hu t ht
  exact ⟨he.trans hc,hd.trans hc⟩

/-- Physical beta and the original strictly positive bounded rate convention. -/
theorem physical_storage (rate : Rate S n) (beta hmax : ℝ) (_hb : 0 < beta) (hm : 0 < hmax)
    (hr : ∀ qa omega, 0 < rate qa omega ∧ rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    (encodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta ∧
     decodedError S n rate beta eta t ht ≤ 8 * t * g S n rate * mass S n beta) ∧
    (encodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta ∧
     decodedError S n rate beta eta t ht ≤ 48 * t * qubits S n * hmax * mass S n beta) :=
  ⟨storage_eight S n rate beta (fun qa w => (hr qa w).1.le) hDB eta t ht,
    storage_forty_eight S n rate beta hmax hm.le (fun qa w => (hr qa w).1.le)
      (fun qa w => (hr qa w).2) hDB eta t ht⟩

theorem window_eight (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (_hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : 8 * t * g S n rate * mass S n beta ≤ delta) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  obtain ⟨he,hh⟩ := storage_eight S n rate beta hn hDB eta t ht
  exact ⟨he.trans hw, hh.trans hw⟩

theorem window_forty_eight (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (_hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : 48 * t * qubits S n * hmax * mass S n beta ≤ delta) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  obtain ⟨he,hh⟩ := storage_forty_eight S n rate beta hmax hm hn hu hDB eta t ht
  exact ⟨he.trans hw, hh.trans hw⟩

/-- Includes g=0 and mu=0 without division or any positivity premise. -/
theorem zero_product_all_time (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hz : g S n rate * mass S n beta = 0)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht = 0 ∧ decodedError S n rate beta eta t ht = 0 := by
  have hw : 8 * t * g S n rate * mass S n beta ≤ 0 := by
    calc
      _ = 8 * t * (g S n rate * mass S n beta) := by ring
      _ = 0 := by rw [hz,mul_zero]
      _ ≤ 0 := le_refl 0
  obtain ⟨he,hd⟩ := window_eight S n rate beta hn hDB eta 0 t (le_refl 0) ht hw
  exact ⟨le_antisymm he (encoded_nonneg S n rate beta eta t ht),
    le_antisymm hd (decoded_nonneg S n rate beta eta t ht)⟩

theorem zero_g_all_time (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hz : g S n rate = 0) (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht = 0 ∧ decodedError S n rate beta eta t ht = 0 :=
  zero_product_all_time S n rate beta hn hDB (by rw [hz,zero_mul]) eta t ht

theorem zero_mass_all_time (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hz : mass S n beta = 0) (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht = 0 ∧ decodedError S n rate beta eta t ht = 0 :=
  zero_product_all_time S n rate beta hn hDB (by rw [hz,mul_zero]) eta t ht

theorem positive_horizon_eight (rate : Rate S n) (beta : ℝ)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hg : 0 < g S n rate) (hm : 0 < mass S n beta)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : t ≤ delta / (8 * g S n rate * mass S n beta)) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  apply window_eight S n rate beta hn hDB eta delta t hd ht
  have h := (le_div_iff₀ (by positivity : 0 < 8 * g S n rate * mass S n beta)).mp hw
  nlinarith

theorem positive_horizon_forty_eight (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hp : 0 < qubits S n * hmax * mass S n beta)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : t ≤ delta / (48 * qubits S n * hmax * mass S n beta)) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  apply window_forty_eight S n rate beta hmax hm hn hu hDB eta delta t hd ht
  have hp' : 0 < 48 * qubits S n * hmax * mass S n beta := by nlinarith
  have h := (le_div_iff₀ hp').mp hw
  nlinarith

/-- Only arithmetic under explicitly separate sector envelopes, not a Peierls proof. -/
theorem sector_envelope (beta q : ℝ) (_hq : 0 ≤ q)
    (hx : xMass S n beta ≤ 2*q) (hz : zMass S n beta ≤ 2*q) : mass S n beta ≤ 4*q := by
  have h := mass_union S n beta
  linarith

theorem conditional_thirty_two (rate : Rate S n) (beta q : ℝ) (hq : 0 ≤ q)
    (hn : ∀ qa omega, 0 ≤ rate qa omega)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hx : xMass S n beta ≤ 2*q) (hz : zMass S n beta ≤ 2*q)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 32 * t * g S n rate * q ∧
    decodedError S n rate beta eta t ht ≤ 32 * t * g S n rate * q := by
  obtain ⟨he,hd⟩ := storage_eight S n rate beta hn hDB eta t ht
  have hg := g_nonneg S n rate
  have hc : 8 * t * g S n rate * mass S n beta ≤ 32 * t * g S n rate * q := by
    calc
      _ ≤ 8 * t * g S n rate * (4*q) :=
        mul_le_mul_of_nonneg_left (sector_envelope S n beta q hq hx hz) (by positivity)
      _ = _ := by ring
  exact ⟨he.trans hc,hd.trans hc⟩

theorem conditional_one_ninety_two (rate : Rate S n) (beta hmax q : ℝ) (hm : 0 ≤ hmax) (hq : 0 ≤ q)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (hx : xMass S n beta ≤ 2*q) (hz : zMass S n beta ≤ 2*q)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * q ∧
    decodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * q := by
  obtain ⟨he,hd⟩ := storage_forty_eight S n rate beta hmax hm hn hu hDB eta t ht
  have hN : 0 ≤ qubits S n := by unfold qubits; positivity
  have hc : 48 * t * qubits S n * hmax * mass S n beta ≤ 192 * t * qubits S n * hmax * q := by
    calc
      _ ≤ 48 * t * qubits S n * hmax * (4*q) :=
        mul_le_mul_of_nonneg_left (sector_envelope S n beta q hq hx hz) (by positivity)
      _ = _ := by ring
  exact ⟨he.trans hc,hd.trans hc⟩

/-- Literal frozen scalar, not a bound on any actual bad-sector probability. -/
def peierlsScale (k : Nat) : ℝ := Real.rpow 2 (-((2^(k-1) : Nat) : ℝ))

theorem peierlsScale_pos (k : Nat) : 0 < peierlsScale k :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem conditional_terminal_bound (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (k : Nat) (hx : xMass S n beta ≤ 2*peierlsScale k) (hz : zMass S n beta ≤ 2*peierlsScale k)
    (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * peierlsScale k ∧
    decodedError S n rate beta eta t ht ≤ 192 * t * qubits S n * hmax * peierlsScale k :=
  conditional_one_ninety_two S n rate beta hmax (peierlsScale k) hm (peierlsScale_pos k).le
    hn hu hDB hx hz eta t ht

/-- Every source-even level uses the same physical beta and rate cap. -/
theorem source_even_storage (rates : ∀ j, Rate S j) (beta hmax : ℝ)
    (hb : 0 < beta) (hm : 0 < hmax)
    (hr : ∀ j qa omega, 0 < rates j qa omega ∧ rates j qa omega ≤ hmax)
    (hDB : ∀ j qa omega, rates j qa (BDL26BoundedRateDavies.oppositeFrequency S (j+2) omega) =
      Real.exp (-beta * omega.val) * rates j qa omega)
    (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j+2 = 2*k ∧ ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
      (encodedError S j (rates j) beta eta t ht ≤ 8*t*g S j (rates j)*mass S j beta ∧
       decodedError S j (rates j) beta eta t ht ≤ 8*t*g S j (rates j)*mass S j beta) ∧
      (encodedError S j (rates j) beta eta t ht ≤ 48*t*qubits S j*hmax*mass S j beta ∧
       decodedError S j (rates j) beta eta t ht ≤ 48*t*qubits S j*hmax*mass S j beta) := by
  refine ⟨2*(k-1), BDL26TransposedStoppedDecoder.source_even_level k hk, ?_⟩
  intro eta t ht
  exact physical_storage S _ (rates _) beta hmax hb hm (hr _) (hDB _) eta t ht


/-- The actual coherent full-gap operator, keeping both copies of every degeneracy. -/
theorem jump_coherent (rate : Rate S n) (q : Physical S (n+2))
    (axis : CSSDaviesLocality.Axis) (omega : BDL26CSSDaviesLocality.Frequency S (n+2)) :
    jumps S n rate ((q,axis),omega) = (Real.sqrt (rate (q,axis) omega) : ℂ) •
      Davies.actualFrequency (hamiltonian S (n+2))
        (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
        (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega.val :=
  BDL26BoundedRateDavies.jump_eq_sqrt_frequency S (n+2) rate q axis omega

theorem frequency_protection (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) (omega : ℝ) :
    (Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * (logical S n).x -
      (logical S n).x * Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * projector S n = 0 ∧
    (Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * (logical S n).z -
      (logical S n).z * Davies.actualFrequency (hamiltonian S (n+2))
      (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * projector S n = 0 :=
  ⟨BDL26LogicalDefectProtection.actual_frequency_X S n q axis omega,
    BDL26LogicalDefectProtection.actual_frequency_Z S n q axis omega⟩

theorem coupling_count : Fintype.card (BDL26CSSDaviesLocality.CouplingIndex S (n+2)) =
    3 * Fintype.card (Physical S (n+2)) := BDL26BoundedRateDavies.couplingIndex_card S (n+2)

/-- Time zero does not require positivity, detailed balance or a nonzero mass. -/
theorem zero_time (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encodedError S n rate beta eta 0 (le_refl 0) = 0 ∧
    decodedError S n rate beta eta 0 (le_refl 0) = 0 := by
  constructor
  · change traceNorm (finiteLindbladEvolutionLinearMap (hamiltonian S (n+2))
      (jumps S n rate) 0 (encoder S n beta eta.toOperator) - encoder S n beta eta.toOperator) = 0
    rw [finiteLindbladEvolutionLinearMap_zero, LinearMap.id_apply, sub_self]
    exact (traceNorm_eq_zero_iff _).2 rfl
  · change traceNorm (decoder S n (finiteLindbladEvolutionLinearMap (hamiltonian S (n+2))
      (jumps S n rate) 0 (encoder S n beta eta.toOperator)) - eta.toOperator) = 0
    rw [finiteLindbladEvolutionLinearMap_zero, LinearMap.id_apply, left_inverse, sub_self]
    exact (traceNorm_eq_zero_iff _).2 rfl

/-- Conditional frozen denominator; the actual sector envelopes remain explicit. -/
theorem conditional_terminal_horizon (rate : Rate S n) (beta hmax : ℝ) (hm : 0 ≤ hmax)
    (hn : ∀ qa omega, 0 ≤ rate qa omega) (hu : ∀ qa omega, rate qa omega ≤ hmax)
    (hDB : ∀ qa omega, rate qa (BDL26BoundedRateDavies.oppositeFrequency S (n+2) omega) =
      Real.exp (-beta * omega.val) * rate qa omega)
    (k : Nat) (hx : xMass S n beta ≤ 2*peierlsScale k) (hz : zMass S n beta ≤ 2*peierlsScale k)
    (hp : 0 < qubits S n * hmax * peierlsScale k)
    (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ) (_hd : 0 ≤ delta) (ht : 0 ≤ t)
    (hw : t ≤ delta / (192 * qubits S n * hmax * peierlsScale k)) :
    encodedError S n rate beta eta t ht ≤ delta ∧ decodedError S n rate beta eta t ht ≤ delta := by
  obtain ⟨he,hh⟩ := conditional_terminal_bound S n rate beta hmax hm hn hu hDB k hx hz eta t ht
  have hp' : 0 < 192 * qubits S n * hmax * peierlsScale k := by nlinarith
  have hw' := (le_div_iff₀ hp').mp hw
  constructor <;> nlinarith


/-- A genuine lower-level nonnegative-rate specialization, not positive bath data. -/
theorem zero_rate_g : g S n (fun _ _ => 0) = 0 := by
  have h := g_le S n (fun _ _ => 0) 0 (le_refl 0)
    (fun _ _ => le_refl 0) (fun _ _ => le_refl 0)
  exact le_antisymm (by simpa using h) (g_nonneg S n _)

theorem zero_rate_all_time (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace)
    (t : ℝ) (ht : 0 ≤ t) :
    encodedError S n (fun _ _ => 0) beta eta t ht = 0 ∧
    decodedError S n (fun _ _ => 0) beta eta t ht = 0 :=
  zero_g_all_time S n (fun _ _ => 0) beta (fun _ _ => le_refl 0)
    (by intro qa omega; simp) (zero_rate_g S n) eta t ht

end QEC.Coding.BDL26LogicalDefectStorage
end
