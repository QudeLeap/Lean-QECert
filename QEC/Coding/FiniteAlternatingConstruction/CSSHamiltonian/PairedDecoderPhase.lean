import QEC.Coding.FiniteAlternatingConstruction.TransposedStoppedDecoder
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.SectorTranslation
import QEC.Coding.Stabilizer.GoodSyndromeProtectedSector

/-!
# Actual paired-decoder phases and conditional operator protection

The phase is summed over the complete realizable carrier of the original labelled
CSS Hamiltonian. Only the final right restriction uses a finite selection. The
conditional inputs are row-boundary witnesses for the internally computed full
paired residual. No stable-set or lifetime conclusion is asserted.

Source reasoning: CLBT10, arXiv.02.tex:619–674,1195–1211,1234–1276;
BDL26, paper.tex:3383–3416, with the approved actual X/Z convention.
-/
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderPhase
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators

variable (S : OddScale) (n : Nat)

/-- The original visible carrier, retaining every labelled row. -/
abbrev Visible := BDL26TwoSectorBadProjector.JointImage S (n + 2)
local instance : Fintype (XSyndromeDomain S n) := Fintype.ofFinite _
local instance : Fintype (ZSyndromeDomain S n) := Fintype.ofFinite _

/-- The actual bare stabilizer code on this same physical register. -/
abbrev code := binaryCSSStabilizerCodeOfParityChecks
  (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) (row_orthogonal S (n + 2))

/-- The decoder's carrier is definitionally the visible carrier. -/
theorem visible_eq_decoder_domains :
    Visible S n = (XSyndromeDomain S n × ZSyndromeDomain S n) := rfl

/-- The original nonzero joint atom on the actual register. -/
abbrev atom (s : Visible S n) : Operator (Qubit.QubitRegister (Physical S (n + 2))) :=
  projector S (n + 2)
    (CSSGibbs.realizableEmbedding (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) s)

/-- X then Z, using the two existing actual stopped decoders. -/
abbrev correction (s : Visible S n) := pairedCorrection S n s.1 s.2

/-- The original full residual, including its stored binary phase. -/
abbrev residual (s : Visible S n) (E : Binary (Physical S (n + 2))) :=
  pairedResidual S n s.1 s.2 E

/-- Translation in the complete realizable carrier. -/
abbrev translation (E : Binary (Physical S (n + 2))) :=
  CSSGibbs.jointTranslation (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) E

theorem translation_coordinates (s : Visible S n) (E : Binary (Physical S (n + 2))) :
    translation S n E s =
      (translateX S n s.1 E.vector.xPart, translateZ S n s.2 E.vector.zPart) := by
  apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem residual_eq (s : Visible S n) (E : Binary (Physical S (n + 2))) :
    residual S n s E = binaryMul (correction S n (translation S n E s))
      (binaryMul E (correction S n s)) := by
  rw [translation_coordinates]
  rfl

/-- Neither the old background nor the post-error Z overlap is discarded. -/
theorem residual_phase (s : Visible S n) (E : Binary (Physical S (n + 2))) :
    (residual S n s E).phase = E.phase +
      (∑ q, xCorrection S n s.1 q * E.vector.zPart q) +
      ∑ q, (E.vector.xPart q + xCorrection S n s.1 q) *
        zCorrection S n (translation S n E s).2 q := by
  rw [translation_coordinates]
  exact pairedResidual_phase S n s.1 s.2 E

/-- Boundary witnesses certify membership up to sign, never exact group membership. -/
theorem residual_inGeneratedGroupUpToSign (s : Visible S n)
    (E : Binary (Physical S (n + 2)))
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    (code S n).InGeneratedGroupUpToSign (residual S n s E) :=
  pairedResidual_inGeneratedGroupUpToSign_of_boundaries S n s.1 s.2 E hx hz

/-- The stored residual sign is harmless for commutation, but remains stored. -/
theorem residual_commutes (s : Visible S n) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) : Commutes (residual S n s E) logical := by
  obtain ⟨g, hg, hv⟩ := residual_inGeneratedGroupUpToSign S n s E hx hz
  exact (commutes_iff_of_binaryUpToSign_left hv).mpr
    ((commutes_comm g logical).mpr (hlogical g hg))

/-- The computed correction sign transports from the two ordinary boundaries. -/
theorem phase_transport (s : Visible S n) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    commutationPhase (correction S n (translation S n E s)) logical =
      commutationPhase E logical * commutationPhase (correction S n s) logical := by
  have hc := residual_commutes S n s E logical hlogical hx hz
  have hr : commutationPhase (residual S n s E) logical = 1 := by
    simp [commutationPhase, show symplecticForm (residual S n s E).vector logical.vector = 0 from hc,
      binaryPhaseScalar]
  rw [residual_eq, commutationPhase_binaryMul_left, commutationPhase_binaryMul_left] at hr
  have hs : (commutationPhase E logical * commutationPhase (correction S n s) logical) *
      (commutationPhase E logical * commutationPhase (correction S n s) logical) = 1 := by
    calc
      _ = (commutationPhase E logical * commutationPhase E logical) *
        (commutationPhase (correction S n s) logical * commutationPhase (correction S n s) logical) := by ring
      _ = 1 := by simp
  calc
    _ = commutationPhase (correction S n (translation S n E s)) logical * 1 := by simp
    _ = commutationPhase (correction S n (translation S n E s)) logical *
      ((commutationPhase E logical * commutationPhase (correction S n s) logical) *
       (commutationPhase E logical * commutationPhase (correction S n s) logical)) := by rw [hs]
    _ = (commutationPhase (correction S n (translation S n E s)) logical *
      (commutationPhase E logical * commutationPhase (correction S n s) logical)) *
      (commutationPhase E logical * commutationPhase (correction S n s) logical) := by ring
    _ = _ := by rw [hr, one_mul]

@[simp] theorem atom_adjoint (s : Visible S n) :
    LinearMap.adjoint (atom S n s) = atom S n s := CSSGibbs.projector_adjoint _ _ _ _

@[simp] theorem atom_square (s : Visible S n) :
    atom S n s * atom S n s = atom S n s := CSSGibbs.projector_square _ _ _ _

theorem atom_mul_of_ne (s t : Visible S n) (h : s ≠ t) :
    atom S n s * atom S n t = 0 := by
  apply CSSGibbs.projector_mul_of_ne
  exact fun he => h ((CSSGibbs.realizableEmbedding _ _).injective he)

theorem sum_atom : (∑ s : Visible S n, atom S n s) = 1 :=
  CSSGibbs.selectedProjector_total _ _ (row_orthogonal S (n + 2))

theorem atom_ne_zero (s : Visible S n) : atom S n s ≠ 0 :=
  BDL26SectorTranslation.atom_ne_zero S (n + 2) s

/-- The full visible phase sum. The finite selected set never appears here. -/
def phaseOperator (logical : Binary (Physical S (n + 2))) :
    Operator (Qubit.QubitRegister (Physical S (n + 2))) :=
  ∑ s : Visible S n, commutationPhase (correction S n s) logical • atom S n s

/-- The actual globally dressed observable. -/
def dressed (logical : Binary (Physical S (n + 2))) :
    Operator (Qubit.QubitRegister (Physical S (n + 2))) :=
  toHermitianQubitOperator logical * phaseOperator S n logical

theorem phaseOperator_mul_atom (logical : Binary (Physical S (n + 2))) (s : Visible S n) :
    phaseOperator S n logical * atom S n s =
      commutationPhase (correction S n s) logical • atom S n s := by
  rw [phaseOperator, Finset.sum_mul, Finset.sum_eq_single s]
  · rw [smul_mul_assoc, atom_square]
  · intro t _ hts
    rw [smul_mul_assoc, atom_mul_of_ne S n t s hts]
    simp
  · simp

theorem atom_mul_phaseOperator (logical : Binary (Physical S (n + 2))) (s : Visible S n) :
    atom S n s * phaseOperator S n logical =
      commutationPhase (correction S n s) logical • atom S n s := by
  rw [phaseOperator, Finset.mul_sum, Finset.sum_eq_single s]
  · rw [mul_smul_comm, atom_square]
  · intro t _ hts
    rw [mul_smul_comm, atom_mul_of_ne S n s t hts.symm]
    simp
  · simp

@[simp] theorem phaseOperator_square (logical : Binary (Physical S (n + 2))) :
    phaseOperator S n logical * phaseOperator S n logical = 1 := by
  change phaseOperator S n logical *
    (∑ s : Visible S n, commutationPhase (correction S n s) logical • atom S n s) = 1
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, phaseOperator_mul_atom, smul_smul,
    commutationPhase_square, one_smul]
  exact sum_atom S n

@[simp] theorem phaseOperator_adjoint (logical : Binary (Physical S (n + 2))) :
    LinearMap.adjoint (phaseOperator S n logical) = phaseOperator S n logical := by
  rw [phaseOperator, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smulₛₗ, atom_adjoint]
  congr 1
  change star (binaryPhaseScalar _) = binaryPhaseScalar _
  exact binaryPhaseScalar_star _

/-- Bare normalizer semantics imply zero syndrome in both original sectors. -/
theorem normalizer_translation (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) (s : Visible S n) :
    translation S n logical s = s := by
  have hk := (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    _ _ (row_orthogonal S (n + 2)) logical).mp hlogical
  have hx : zSyndrome S (n + 2) logical.vector.xPart = 0 := hk.1
  have hz : xSyndrome S (n + 2) logical.vector.zPart = 0 := hk.2
  apply Prod.ext <;> apply Subtype.ext
  · change s.1.val + zSyndrome S (n + 2) logical.vector.xPart = s.1.val
    rw [hx, add_zero]
  · change s.2.val + xSyndrome S (n + 2) logical.vector.zPart = s.2.val
    rw [hz, add_zero]

/-- Exact full-Pauli transport on the original atoms. -/
theorem pauli_mul_atom (E : Binary (Physical S (n + 2))) (s : Visible S n) :
    toHermitianQubitOperator E * atom S n s =
      atom S n (translation S n E s) * toHermitianQubitOperator E :=
  CSSGibbs.pauli_mul_realizable_projector _ _ (row_orthogonal S (n + 2)) E s

theorem normalizer_commute_atom (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) (s : Visible S n) :
    Commute (toHermitianQubitOperator logical) (atom S n s) := by
  show _ * _ = _ * _
  simpa only [normalizer_translation S n logical hlogical s] using pauli_mul_atom S n logical s

theorem normalizer_commute_phaseOperator (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) :
    Commute (toHermitianQubitOperator logical) (phaseOperator S n logical) := by
  unfold phaseOperator
  apply Commute.sum_right
  intro s _
  exact (normalizer_commute_atom S n logical hlogical s).smul_right _

theorem normalizer_commute_hamiltonian (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) :
    Commute (toHermitianQubitOperator logical) (hamiltonian S (n + 2)) := by
  change Commute _ (-∑ j, toQubitOperator (check S (n + 2) j))
  apply Commute.neg_right
  apply Commute.sum_right
  intro j _
  have hg : check S (n + 2) j ∈ (code S n).generatedGroup := by
    rw [← binaryCSSParityCheckGenerators_generate_generatedGroup
      (zSyndrome S (n + 2)) (xSyndrome S (n + 2)) (row_orthogonal S (n + 2))]
    exact GeneratedStabilizer.generator j
  have hc := toHermitianQubitOperator_commute_of_commutes logical (check S (n + 2) j) (hlogical _ hg)
  show toHermitianQubitOperator logical * toQubitOperator (check S (n + 2) j) =
    toQubitOperator (check S (n + 2) j) * toHermitianQubitOperator logical
  simpa only [check_hermitian] using hc

theorem hamiltonian_commute_atom (s : Visible S n) :
    Commute (hamiltonian S (n + 2)) (atom S n s) := by
  change Commute (CSSGibbs.hamiltonian (zSyndrome S (n + 2)) (xSyndrome S (n + 2))) _
  rw [CSSGibbs.hamiltonian_syndrome_resolution _ _ (row_orthogonal S (n + 2))]
  apply Commute.sum_left
  intro t _
  exact (CSSGibbs.projector_commute _ _ (row_orthogonal S (n + 2)) t _).smul_left _

theorem phaseOperator_commute_hamiltonian (logical : Binary (Physical S (n + 2))) :
    Commute (phaseOperator S n logical) (hamiltonian S (n + 2)) := by
  unfold phaseOperator
  apply Commute.sum_left
  intro s _
  exact (hamiltonian_commute_atom S n s).symm.smul_left _

@[simp] theorem dressed_adjoint (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) :
    LinearMap.adjoint (dressed S n logical) = dressed S n logical := by
  rw [dressed, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    ← Module.End.mul_eq_comp, phaseOperator_adjoint,
    adjoint_toHermitianQubitOperator_eq_self]
  exact (normalizer_commute_phaseOperator S n logical hlogical).eq.symm

@[simp] theorem dressed_square (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) : dressed S n logical * dressed S n logical = 1 := by
  unfold dressed
  calc
    _ = (toHermitianQubitOperator logical * toHermitianQubitOperator logical) *
      (phaseOperator S n logical * phaseOperator S n logical) := by
        rw [mul_assoc, ← mul_assoc (phaseOperator S n logical),
          (normalizer_commute_phaseOperator S n logical hlogical).eq.symm]
        simp only [mul_assoc]
    _ = 1 := by rw [toHermitianQubitOperator_square, phaseOperator_square, one_mul]

theorem dressed_commute_hamiltonian (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) :
    Commute (dressed S n logical) (hamiltonian S (n + 2)) :=
  (normalizer_commute_hamiltonian S n logical hlogical).mul_left
    (phaseOperator_commute_hamiltonian S n logical)

theorem dressed_mul_atom (logical : Binary (Physical S (n + 2))) (s : Visible S n) :
    dressed S n logical * atom S n s =
      commutationPhase (correction S n s) logical • (toHermitianQubitOperator logical * atom S n s) := by
  rw [dressed, mul_assoc, phaseOperator_mul_atom, mul_smul_comm]

/-- Direct full-E protection; no product of compressed X/Z commutators is used. -/
theorem protected_atom (s : Visible S n) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    (toHermitianQubitOperator E * dressed S n logical -
      dressed S n logical * toHermitianQubitOperator E) * atom S n s = 0 := by
  have hphase := phase_transport S n s E logical hlogical hx hz
  have hl : (toHermitianQubitOperator E * dressed S n logical) * atom S n s =
      (commutationPhase E logical * commutationPhase (correction S n s) logical) •
        ((toHermitianQubitOperator logical * toHermitianQubitOperator E) * atom S n s) := by
    rw [mul_assoc, dressed_mul_atom, mul_smul_comm, ← mul_assoc,
      toHermitianQubitOperator_mul_eq_commutationPhase_smul,
      smul_mul_assoc, smul_smul]
    congr 1
    exact mul_comm _ _
  have hr : (dressed S n logical * toHermitianQubitOperator E) * atom S n s =
      commutationPhase (correction S n (translation S n E s)) logical •
        ((toHermitianQubitOperator logical * toHermitianQubitOperator E) * atom S n s) := by
    rw [mul_assoc, pauli_mul_atom, ← mul_assoc, dressed_mul_atom, smul_mul_assoc]
    simp only [mul_assoc]
    rw [← pauli_mul_atom S n E s]
  rw [sub_mul, hl, hr, hphase, sub_self]

/-- Only the final right restriction is selected. No selection invariance is needed. -/
theorem protected_selected (A : Finset (Visible S n)) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∀ s ∈ A, ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∀ s ∈ A, ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    (toHermitianQubitOperator E * dressed S n logical - dressed S n logical * toHermitianQubitOperator E) *
      BDL26TwoSectorBadProjector.selected S (n + 2) A = 0 := by
  change _ * (∑ s ∈ A, atom S n s) = 0
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun s hs => protected_atom S n s E logical hlogical (hx s hs) (hz s hs))

theorem protected_empty (E logical : Binary (Physical S (n + 2))) :
    (toHermitianQubitOperator E * dressed S n logical - dressed S n logical * toHermitianQubitOperator E) *
      BDL26TwoSectorBadProjector.selected S (n + 2) ∅ = 0 := by
  simp [BDL26TwoSectorBadProjector.selected, CSSGibbs.selectedProjector]

theorem protected_univ (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∀ s : Visible S n, ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∀ s : Visible S n, ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    Commute (toHermitianQubitOperator E) (dressed S n logical) := by
  have h := protected_selected S n Finset.univ E logical hlogical (fun s _ => hx s) (fun s _ => hz s)
  change (toHermitianQubitOperator E * dressed S n logical -
    dressed S n logical * toHermitianQubitOperator E) *
    CSSGibbs.selectedProjector (zSyndrome S (n + 2)) (xSyndrome S (n + 2))
      (row_orthogonal S (n + 2)) Finset.univ = 0 at h
  rw [CSSGibbs.selectedProjector_total, mul_one] at h
  show toHermitianQubitOperator E * dressed S n logical = dressed S n logical * toHermitianQubitOperator E
  exact sub_eq_zero.mp h

/-- Literal XYZ couplings, on the same Hamiltonian and register. -/
theorem coupling_protected_atom (s : Visible S n) (q : Physical S (n + 2))
    (axis : CSSDaviesLocality.Axis) (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.zPart) :
    (BDL26CSSDaviesLocality.coupling S (n + 2) q axis * dressed S n logical -
      dressed S n logical * BDL26CSSDaviesLocality.coupling S (n + 2) q axis) * atom S n s = 0 :=
  protected_atom S n s (CSSDaviesLocality.singlePauli q axis) logical hlogical hx hz

theorem coupling_protected_selected (A : Finset (Visible S n)) (q : Physical S (n + 2))
    (axis : CSSDaviesLocality.Axis) (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∀ s ∈ A, ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.xPart)
    (hz : ∀ s ∈ A, ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.zPart) :
    (BDL26CSSDaviesLocality.coupling S (n + 2) q axis * dressed S n logical -
      dressed S n logical * BDL26CSSDaviesLocality.coupling S (n + 2) q axis) *
        BDL26TwoSectorBadProjector.selected S (n + 2) A = 0 :=
  protected_selected S n A (CSSDaviesLocality.singlePauli q axis) logical hlogical hx hz

/-- Y translates both sectors, and the operator retains its exact central i. -/
theorem actual_Y (s : Visible S n) (q : Physical S (n + 2)) :
    translation S n (CSSDaviesLocality.singlePauli q .y) s =
      (translateX S n s.1 (Pi.single q 1), translateZ S n s.2 (Pi.single q 1)) ∧
    BDL26CSSDaviesLocality.coupling S (n + 2) q .y =
      Complex.I • (Qubit.localX q * Qubit.localZ q) :=
  ⟨translation_coordinates S n s _, BDL26CSSDaviesLocality.coupling_y S (n + 2) q⟩

/-- A concrete two-sector background; no decoder is chosen by a caller. -/
def singletonBackground (q : Physical S (n + 2)) : Visible S n :=
  (⟨zSyndrome S (n + 2) (Pi.single q 1), ⟨Pi.single q 1, rfl⟩⟩,
   ⟨xSyndrome S (n + 2) (Pi.single q 1), ⟨Pi.single q 1, rfl⟩⟩)

theorem singletonBackground_nonzero (q : Physical S (n + 2)) :
    (singletonBackground S n q).1.val ≠ 0 ∧ (singletonBackground S n q).2.val ≠ 0 :=
  ⟨singleton_zSyndrome_ne_zero S (n + 2) q, singleton_xSyndrome_ne_zero S (n + 2) q⟩

/-- The actual right inverses force both computed corrections to be nonzero. -/
theorem singletonBackground_corrections_nonzero (q : Physical S (n + 2)) :
    xCorrection S n (singletonBackground S n q).1 ≠ 0 ∧
      zCorrection S n (singletonBackground S n q).2 ≠ 0 := by
  constructor
  · intro h
    have he := xCorrection_syndrome S n (singletonBackground S n q).1
    rw [h, map_zero] at he
    exact (singletonBackground_nonzero S n q).1 he.symm
  · intro h
    have he := zCorrection_syndrome S n (singletonBackground S n q).2
    rw [h, map_zero] at he
    exact (singletonBackground_nonzero S n q).2 he.symm

/-- Both Y coordinates are nonzero and overlap at the actual physical site. -/
theorem actual_Y_nonzero_overlap (q : Physical S (n + 2)) :
    (CSSDaviesLocality.singlePauli q .y).vector.xPart ≠ 0 ∧
    (CSSDaviesLocality.singlePauli q .y).vector.zPart ≠ 0 ∧
    (CSSDaviesLocality.singlePauli q .y).vector.xPart q *
      (CSSDaviesLocality.singlePauli q .y).vector.zPart q = 1 := by
  have he : (Pi.single q (1 : ZMod 2) : Word (ZMod 2) (Physical S (n + 2))) ≠ 0 := by
    intro h
    have hq : (1 : ZMod 2) = 0 := by simpa using congrFun h q
    exact one_ne_zero hq
  exact ⟨he, he, by simp [CSSDaviesLocality.singlePauli]⟩

/-- The canonical before-correction overlap is retained without assuming it vanishes. -/
theorem correction_raw_square_phase (s : Visible S n) :
    (binaryMul (correction S n s) (correction S n s)).phase =
      ∑ q, xCorrection S n s.1 q * zCorrection S n s.2 q := by
  simp [correction, pairedCorrection, binaryMul, binaryMulPhase]

/-- A central sign changes no translation coordinate. -/
theorem sign_translation (phase : ZMod 2) (E : Binary (Physical S (n + 2))) :
    translation S n (binaryMul (binarySign phase) E) = translation S n E := by
  apply Equiv.ext
  intro s
  rw [translation_coordinates, translation_coordinates]
  simp [binaryMul, binarySign]

theorem sign_residual_vector (phase : ZMod 2) (s : Visible S n)
    (E : Binary (Physical S (n + 2))) :
    (residual S n s (binaryMul (binarySign phase) E)).vector = (residual S n s E).vector := by
  rw [residual_eq, residual_eq, sign_translation]
  simp [binaryMul, binarySign]

/-- The phase shift is preserved even though the residual vectors agree. -/
theorem sign_residual_phase (phase : ZMod 2) (s : Visible S n)
    (E : Binary (Physical S (n + 2))) :
    (residual S n s (binaryMul (binarySign phase) E)).phase =
      phase + (residual S n s E).phase := by
  rw [residual_phase, residual_phase, sign_translation]
  simp [binaryMul, binaryMulPhase, binarySign, add_assoc]

theorem sign_boundaries (phase : ZMod 2) (s : Visible S n)
    (E : Binary (Physical S (n + 2))) :
    ((∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
        (residual S n s (binaryMul (binarySign phase) E)).vector.xPart) ↔
      ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a = (residual S n s E).vector.xPart) ∧
    ((∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
        (residual S n s (binaryMul (binarySign phase) E)).vector.zPart) ↔
      ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b = (residual S n s E).vector.zPart) := by
  constructor <;> simp only [sign_residual_vector]

theorem sign_commutationPhase (phase : ZMod 2) (E logical : Binary (Physical S (n + 2))) :
    commutationPhase (binaryMul (binarySign phase) E) logical = commutationPhase E logical := by
  simp [commutationPhase, binaryMul, binarySign]

/-- Direct use of the registered signed Hermitian API, not general multiplicativity. -/
theorem sign_one_operator (E : Binary (Physical S (n + 2))) :
    toHermitianQubitOperator (binaryMul (binarySign 1) E) = -toHermitianQubitOperator E := by
  rw [toHermitianQubitOperator_binarySign_mul]
  norm_num [binaryPhaseScalar]

theorem sign_one_protected_atom (s : Visible S n) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    (toHermitianQubitOperator (binaryMul (binarySign 1) E) * dressed S n logical -
      dressed S n logical * toHermitianQubitOperator (binaryMul (binarySign 1) E)) * atom S n s = 0 := by
  rw [sign_one_operator, neg_mul, mul_neg, neg_sub_neg, sub_mul]
  have hp := protected_atom S n s E logical hlogical hx hz
  rw [sub_mul] at hp
  exact sub_eq_zero.mpr (sub_eq_zero.mp hp).symm

/-- Every actual coupling and every actual realizable atom is nonzero. -/
theorem nonvacuous_coupling_atom (q : Physical S (n + 2)) (axis : CSSDaviesLocality.Axis)
    (s : Visible S n) :
    BDL26CSSDaviesLocality.coupling S (n + 2) q axis ≠ 0 ∧ atom S n s ≠ 0 :=
  ⟨BDL26CSSDaviesLocality.coupling_ne_zero S (n + 2) q axis, atom_ne_zero S n s⟩

/-- One all-parity, literal C2-inclusive source-even consumer. -/
theorem source_even_protected_atom (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j + 2 = 2 * k ∧
      ∀ (s : Visible S j) (E logical : Binary (Physical S (j + 2))),
      (code S j).InBinaryNormalizer logical →
      (∃ a, wordLinearMapTranspose (xSyndrome S (j + 2)) a = (residual S j s E).vector.xPart) →
      (∃ b, wordLinearMapTranspose (zSyndrome S (j + 2)) b = (residual S j s E).vector.zPart) →
      (toHermitianQubitOperator E * dressed S j logical - dressed S j logical * toHermitianQubitOperator E) *
        atom S j s = 0 :=
  ⟨2 * (k - 1), source_even_level k hk, fun s E logical hlogical hx hz => protected_atom S _ s E logical hlogical hx hz⟩

/-- An actual paired-correction error taking s to t; raw corrections need not square to one. -/
def bridgeError (s t : Visible S n) : Binary (Physical S (n + 2)) :=
  binaryMul (correction S n t) (correction S n s)

theorem bridgeError_translation (s t : Visible S n) :
    translation S n (bridgeError S n s t) s = t := by
  have hs := pairedCorrection_syndromes S n s.1 s.2
  have ht := pairedCorrection_syndromes S n t.1 t.2
  apply Prod.ext <;> apply Subtype.ext
  · change s.1.val + zSyndrome S (n + 2)
      ((correction S n t).vector.xPart + (correction S n s).vector.xPart) = t.1.val
    rw [map_add, ht.1, hs.1]
    calc
      _ = t.1.val + (s.1.val + s.1.val) := by abel
      _ = t.1.val := by
        funext z
        change t.1.val z + (s.1.val z + s.1.val z) = t.1.val z
        rw [ZModModule.add_self, add_zero]
  · change s.2.val + xSyndrome S (n + 2)
      ((correction S n t).vector.zPart + (correction S n s).vector.zPart) = t.2.val
    rw [map_add, ht.2, hs.2]
    calc
      _ = t.2.val + (s.2.val + s.2.val) := by abel
      _ = t.2.val := by
        funext x
        change t.2.val x + (s.2.val x + s.2.val x) = t.2.val x
        rw [ZModModule.add_self, add_zero]

/-- Both computed residual vectors vanish; the residual sign is still unrestricted. -/
theorem bridgeError_residual_vectors (s t : Visible S n) :
    (residual S n s (bridgeError S n s t)).vector.xPart = 0 ∧
      (residual S n s (bridgeError S n s t)).vector.zPart = 0 := by
  simp only [residual_eq, bridgeError_translation]
  constructor
  · change (correction S n t).vector.xPart +
      ((correction S n t).vector.xPart + (correction S n s).vector.xPart +
        (correction S n s).vector.xPart) = 0
    funext q
    simp only [Pi.add_apply, Pi.zero_apply, add_assoc, ZModModule.add_self, add_zero]
  · change (correction S n t).vector.zPart +
      ((correction S n t).vector.zPart + (correction S n s).vector.zPart +
        (correction S n s).vector.zPart) = 0
    funext q
    simp only [Pi.add_apply, Pi.zero_apply, add_assoc, ZModModule.add_self, add_zero]

theorem bridgeError_boundaries (s t : Visible S n) :
    (∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s (bridgeError S n s t)).vector.xPart) ∧
    (∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s (bridgeError S n s t)).vector.zPart) := by
  obtain ⟨hx, hz⟩ := bridgeError_residual_vectors S n s t
  exact ⟨⟨0, by rw [map_zero, hx]⟩, ⟨0, by rw [map_zero, hz]⟩⟩

/-- Identity bare data are valid and give the complete identity phase. -/
theorem binaryOne_normalizer : (code S n).InBinaryNormalizer binaryOne := by
  intro g _
  exact (commutes_comm binaryOne g).mpr (commutes_binaryOne_right g)

@[simp] theorem phaseOperator_binaryOne : phaseOperator S n binaryOne = 1 := by
  simpa [phaseOperator, commutationPhase, binaryOne, symplecticForm, binaryPhaseScalar]
    using sum_atom S n

@[simp] theorem dressed_binaryOne : dressed S n binaryOne = 1 := by
  rw [dressed, toHermitianQubitOperator_binaryOne, phaseOperator_binaryOne, one_mul]

/-- Truncating the phase to {s} at identity bare data gives only the single atom. -/
theorem truncated_phase_singleton (s : Visible S n) :
    (∑ a ∈ ({s} : Finset (Visible S n)),
      commutationPhase (correction S n a) binaryOne • atom S n a) = atom S n s := by
  simp [commutationPhase, binaryOne, symplecticForm, binaryPhaseScalar]

/-- A nontrivial translation makes the truncated right-restricted commutator nonzero. -/
theorem truncated_not_protected (s t : Visible S n) (hst : s ≠ t) :
    (toHermitianQubitOperator (bridgeError S n s t) * atom S n s -
      atom S n s * toHermitianQubitOperator (bridgeError S n s t)) * atom S n s ≠ 0 := by
  have hcross : (atom S n s * toHermitianQubitOperator (bridgeError S n s t)) * atom S n s = 0 := by
    rw [mul_assoc, pauli_mul_atom, bridgeError_translation, ← mul_assoc,
      atom_mul_of_ne S n s t hst, zero_mul]
  rw [sub_mul, mul_assoc, atom_square, hcross, sub_zero]
  intro hzero
  have hc := congrArg (fun B : Operator (Qubit.QubitRegister (Physical S (n + 2))) =>
    toHermitianQubitOperator (bridgeError S n s t) * B) hzero
  rw [← mul_assoc, toHermitianQubitOperator_square, one_mul, mul_zero] at hc
  exact atom_ne_zero S n s hc

/-- Concrete actual singleton syndrome supplies the required distinct visible sectors. -/
theorem singletonBackground_ne_zero_sector (q : Physical S (n + 2)) :
    (0 : Visible S n) ≠ singletonBackground S n q := by
  intro h
  have hx := congrArg (fun a : Visible S n => a.1.val) h
  exact (singletonBackground_nonzero S n q).1 hx.symm

/-- A fully actual counterexample to truncating the full phase sum before restriction.
The same two zero-witness residual boundary premises protect the full global O. -/
theorem actual_truncated_counterexample (q : Physical S (n + 2)) :
    let s : Visible S n := 0
    let t := singletonBackground S n q
    let E := bridgeError S n s t
    translation S n E s = t ∧
    (∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a = (residual S n s E).vector.xPart) ∧
    (∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b = (residual S n s E).vector.zPart) ∧
    (toHermitianQubitOperator E * dressed S n binaryOne -
      dressed S n binaryOne * toHermitianQubitOperator E) * atom S n s = 0 ∧
    (toHermitianQubitOperator E *
        (∑ a ∈ ({s} : Finset (Visible S n)), commutationPhase (correction S n a) binaryOne • atom S n a) -
      (∑ a ∈ ({s} : Finset (Visible S n)), commutationPhase (correction S n a) binaryOne • atom S n a) *
        toHermitianQubitOperator E) * atom S n s ≠ 0 := by
  dsimp only
  obtain ⟨hx, hz⟩ := bridgeError_boundaries S n 0 (singletonBackground S n q)
  refine ⟨bridgeError_translation S n _ _, hx, hz,
    protected_atom S n _ _ _ (binaryOne_normalizer S n) hx hz, ?_⟩
  simp only [truncated_phase_singleton]
  exact truncated_not_protected S n _ _ (singletonBackground_ne_zero_sector S n q)

end QEC.Coding.BDL26PairedDecoderPhase
end
