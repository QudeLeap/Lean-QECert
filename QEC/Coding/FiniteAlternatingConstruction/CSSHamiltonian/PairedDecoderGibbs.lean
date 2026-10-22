import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.PairedDecoderChannel
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDimension
import QEC.Coding.CSS.GibbsSyndrome.Translation
import QEC.Semantics.Dynamics.Davies.FrequencyLocality

/-!
# The actual paired decoder, its spectrum and its thermal logical factor

CLBT10 `arXiv.02.tex:619–674,899–932,1046–1123` fixes the correction
transform, the source-minus-target frequency convention, and thermal encoding.
BDL26 `paper.tex:3383–3385` fixes the same labelled Hamiltonian and original
X-then-Z correction. The reset and explicit finite spectral/Gibbs identities
below are project-derived internal consequences. They do not prove decoder
stability, correct logical recovery, Gibbs preservation or a memory lifetime.
-/
noncomputable section
namespace QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct

variable (S : OddScale) (n : Nat)
local instance : Fintype (BDL26TransposedStoppedDecoder.XSyndromeDomain S n) := Fintype.ofFinite _
local instance : Fintype (BDL26TransposedStoppedDecoder.ZSyndromeDomain S n) := Fintype.ofFinite _

/-- The actual all-plus code projector, on the unchanged physical register. -/
abbrev groundProjector : Op S n := projector S (n+2) 0
/-- Ground energy counts all labelled checks, including redundant and identity rows. -/
def groundEnergy : ℝ :=
  -((Fintype.card (ZLabel S (n+2)) + Fintype.card (XLabel S (n+2)) : Nat) : ℝ)
/-- Literal energy of an original realizable joint syndrome. -/
def syndromeEnergy (s : Visible S n) : ℝ :=
  CSSGibbs.energy (zSyndrome S (n+2)) (xSyndrome S (n+2))
    (CSSGibbs.realizableEmbedding (zSyndrome S (n+2)) (xSyndrome S (n+2)) s)
/-- The zero pair is in the two actual image carriers. -/
def zeroVisible : Visible S n := (0,0)

@[simp] theorem atom_zero : atom S n (zeroVisible S n) = groundProjector S n := by
  change projector S (n+2) (CSSGibbs.realizableEmbedding _ _ _) = projector S (n+2) 0
  congr 1
  funext j
  cases j <;> rfl

/-- The original computed correction translates its own syndrome to zero. -/
theorem correction_translation_zero (s : Visible S n) :
    translation S n (correction S n s) s = zeroVisible S n := by
  have hs := BDL26TransposedStoppedDecoder.pairedCorrection_syndromes S n s.1 s.2
  apply Prod.ext
  · apply Subtype.ext
    change s.1.val + zSyndrome S (n+2) (correction S n s).vector.xPart = 0
    rw [hs.1]
    funext j
    change s.1.val j + s.1.val j = (0 : ZMod 2)
    exact CharTwo.add_self_eq_zero _
  · apply Subtype.ext
    change s.2.val + xSyndrome S (n+2) (correction S n s).vector.zPart = 0
    rw [hs.2]
    funext j
    change s.2.val j + s.2.val j = (0 : ZMod 2)
    exact CharTwo.add_self_eq_zero _

/-- Hermitian Pauli transport retains the actual sign and actual correction. -/
theorem correction_mul_atom (s : Visible S n) :
    correctionOperator S n s * atom S n s = groundProjector S n * correctionOperator S n s := by
  have h := CSSGibbs.pauli_mul_realizable_projector
    (zSyndrome S (n+2)) (xSyndrome S (n+2)) (row_orthogonal S (n+2))
    (correction S n s) s
  change correctionOperator S n s * atom S n s =
    atom S n (translation S n (correction S n s) s) * correctionOperator S n s at h
  simpa only [correction_translation_zero, atom_zero] using h

/-- Full actual sector reset; no zero-run normalization is used. -/
theorem correction_conjugates_atom (s : Visible S n) :
    correctionOperator S n s * atom S n s * correctionOperator S n s = groundProjector S n := by
  rw [correction_mul_atom, mul_assoc, correction_square, mul_one]

private theorem ground_square : groundProjector S n * groundProjector S n = groundProjector S n :=
  CSSGibbs.projector_square _ _ _ _
private theorem ground_adjoint : LinearMap.adjoint (groundProjector S n) = groundProjector S n :=
  CSSGibbs.projector_adjoint _ _ _ _

private theorem atom_mul_correction (s : Visible S n) :
    atom S n s * correctionOperator S n s = correctionOperator S n s * groundProjector S n := by
  have h := congrArg LinearMap.adjoint (correction_mul_atom S n s)
  simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, atom_adjoint,
    correction_adjoint, ground_adjoint] using h

/-- A complete nonzero visible sector is sent to the actual zero-code projector. -/
theorem channel_atom (s : Visible S n) : channel S n (atom S n s) = groundProjector S n := by
  calc
    channel S n (atom S n s) = channel S n (atom S n s * 1 * atom S n s) := by
      rw [mul_one, atom_square]
    _ = correctionOperator S n s * atom S n s * 1 * atom S n s * correctionOperator S n s :=
      channel_diagonal_sector S n s 1
    _ = correctionOperator S n s * (atom S n s * atom S n s) * correctionOperator S n s := by
      noncomm_ring
    _ = groundProjector S n := by
      rw [atom_square]
      exact correction_conjugates_atom S n s

/-- Raw unreachable labels retain their zero input projector and zero output. -/
theorem channel_raw_projector
    (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2)))) :
    channel S n (projector S (n+2) w) =
      if w ∈ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2))
      then groundProjector S n else 0 := by
  by_cases hw : w ∈ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2))
  · rw [if_pos hw]
    obtain ⟨s, _, hs⟩ := Finset.mem_map.mp hw
    rw [← hs]
    exact channel_atom S n s
  · rw [if_neg hw]
    have hz : projector S (n+2) w = 0 :=
      CSSGibbs.projector_eq_zero_of_not_realizable _ _ (row_orthogonal S (n+2)) w hw
    rw [hz, map_zero]

@[simp] theorem channel_zero : channel S n (0 : Op S n) = 0 := map_zero _

/-- Every complex output, not just density outputs, has left code support. -/
theorem channel_left_support (A : Op S n) :
    groundProjector S n * channel S n A = channel S n A := by
  rw [channel_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hl : groundProjector S n * (correctionOperator S n s * atom S n s) =
      correctionOperator S n s * atom S n s := by
    rw [correction_mul_atom, ← mul_assoc, ground_square]
  calc
    _ = (groundProjector S n * (correctionOperator S n s * atom S n s)) *
        A * (atom S n s * correctionOperator S n s) := by noncomm_ring
    _ = _ := by rw [hl]; noncomm_ring

/-- Every complex output has right code support as well. -/
theorem channel_right_support (A : Op S n) :
    channel S n A * groundProjector S n = channel S n A := by
  rw [channel_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hr : (atom S n s * correctionOperator S n s) * groundProjector S n =
      atom S n s * correctionOperator S n s := by
    rw [atom_mul_correction, mul_assoc, ground_square]
  calc
    _ = (correctionOperator S n s * atom S n s) * A *
        ((atom S n s * correctionOperator S n s) * groundProjector S n) := by noncomm_ring
    _ = _ := by rw [hr]; noncomm_ring

/-- The full syndrome algebra is collapsed with its original complex coefficients. -/
theorem channel_weighted_atoms (a : Visible S n → ℂ) :
    channel S n (∑ s : Visible S n, a s • atom S n s) =
      (∑ s : Visible S n, a s) • groundProjector S n := by
  rw [map_sum]
  simp only [map_smul, channel_atom, Finset.sum_smul]

/-- Literal labelled-check energy, with no rank substitution. -/
theorem syndromeEnergy_eq (s : Visible S n) :
    syndromeEnergy S n s = groundEnergy S n +
      2 * ((HammingWeight s.1.val : ℝ) + HammingWeight s.2.val) := by
  simpa only [syndromeEnergy, CSSGibbs.realizableEmbedding_apply,
    CSSGibbs.energy_joinSyndrome, groundEnergy, Nat.cast_add]

theorem hamiltonian_mul_atom (s : Visible S n) :
    hamiltonian S (n+2) * atom S n s = (syndromeEnergy S n s : ℂ) • atom S n s :=
  CSSGibbs.hamiltonian_mul_projector _ _ (row_orthogonal S (n+2)) _

theorem atom_mul_hamiltonian (s : Visible S n) :
    atom S n s * hamiltonian S (n+2) = (syndromeEnergy S n s : ℂ) • atom S n s := by
  have h := congrArg LinearMap.adjoint (hamiltonian_mul_atom S n s)
  have hh : LinearMap.adjoint (hamiltonian S (n+2)) = hamiltonian S (n+2) :=
    CSSGibbs.hamiltonian_adjoint _ _
  have hl : LinearMap.adjoint (hamiltonian S (n+2) * atom S n s) =
      atom S n s * hamiltonian S (n+2) := by
    change LinearMap.adjoint ((hamiltonian S (n+2)).comp (atom S n s)) =
      (atom S n s).comp (hamiltonian S (n+2))
    rw [LinearMap.adjoint_comp, atom_adjoint, hh]
  have hr : LinearMap.adjoint ((syndromeEnergy S n s : ℂ) • atom S n s) =
      (syndromeEnergy S n s : ℂ) • atom S n s := by
    rw [map_smulₛₗ, atom_adjoint]
    simp
  exact hl.symm.trans (h.trans hr)

/-- Ground energy corresponds to the single zero word, not to energy zero. -/
theorem syndromeEnergy_ground_iff (s : Visible S n) :
    syndromeEnergy S n s = groundEnergy S n ↔ s = zeroVisible S n := by
  rw [syndromeEnergy_eq]
  constructor
  · intro h
    have hp0 : (0 : ℝ) ≤ HammingWeight s.1.val := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ HammingWeight s.2.val := Nat.cast_nonneg _
    have hp : (HammingWeight s.1.val : ℝ) = 0 := by nlinarith
    have hq : (HammingWeight s.2.val : ℝ) = 0 := by nlinarith
    have hp' : s.1.val = 0 := (HammingWeight_eq_zero_iff s.1.val).mp (by exact_mod_cast hp)
    have hq' : s.2.val = 0 := (HammingWeight_eq_zero_iff s.2.val).mp (by exact_mod_cast hq)
    apply Prod.ext <;> apply Subtype.ext
    · exact hp'
    · exact hq'
  · rintro rfl
    simp [zeroVisible, HammingWeight_zero]

/-- Equal energies are grouped as complete original atoms, with all degeneracies. -/
def groupedEnergyProjector (E : ℝ) : Op S n :=
  ∑ s : Visible S n, if syndromeEnergy S n s = E then atom S n s else 0

private theorem energy_projector_mul_atom (E : ℝ) (s : Visible S n) :
    Davies.hamiltonianEnergyProjector (hamiltonian S (n+2))
        (CSSGibbs.hamiltonian_symmetric _ _) E * atom S n s =
      if syndromeEnergy S n s = E then atom S n s else 0 := by
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun T : Op S n => T v) (hamiltonian_mul_atom S n s)
  change hamiltonian S (n+2) (atom S n s v) =
    (syndromeEnergy S n s : ℂ) • atom S n s v at hv
  have hd := Davies.hamiltonian_diagonal (hamiltonian S (n+2))
    (CSSGibbs.hamiltonian_symmetric (zSyndrome S (n+2)) (xSyndrome S (n+2)))
  have hv' :
      (Davies.diagonal
        (Davies.hamiltonianBasis (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _))
        (Davies.hamiltonianEnergies (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)))
        (atom S n s v) = (syndromeEnergy S n s : ℂ) • atom S n s v :=
    (congrArg (fun T : Op S n => T (atom S n s v)) hd).trans hv
  have h := Davies.energyProjector_apply_eigenvector
    (Davies.hamiltonianBasis (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _))
    (Davies.hamiltonianEnergies (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _))
    (atom S n s v) (syndromeEnergy S n s) E hv'
  by_cases he : syndromeEnergy S n s = E
  · rw [if_pos he] at h ⊢
    exact h
  · rw [if_neg he] at h ⊢
    exact h

/-- The canonical same-H spectral projector, for every real energy including absent ones. -/
theorem actual_energy_projector (E : ℝ) :
    Davies.hamiltonianEnergyProjector (hamiltonian S (n+2))
        (CSSGibbs.hamiltonian_symmetric _ _) E = groupedEnergyProjector S n E := by
  calc
    _ = Davies.hamiltonianEnergyProjector (hamiltonian S (n+2))
        (CSSGibbs.hamiltonian_symmetric _ _) E * (∑ s : Visible S n, atom S n s) := by
          rw [sum_atom, mul_one]
    _ = _ := by simp only [Finset.mul_sum, energy_projector_mul_atom, groupedEnergyProjector]

theorem actual_ground_energy_projector :
    Davies.hamiltonianEnergyProjector (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) (groundEnergy S n) = groundProjector S n := by
  rw [actual_energy_projector, groupedEnergyProjector]
  simp only [syndromeEnergy_ground_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, atom_zero]

theorem hamiltonian_mul_ground :
    hamiltonian S (n+2) * groundProjector S n =
      (groundEnergy S n : ℂ) • groundProjector S n := by
  have h := hamiltonian_mul_atom S n (zeroVisible S n)
  rw [atom_zero] at h
  have hz := (syndromeEnergy_ground_iff S n (zeroVisible S n)).mpr rfl
  rwa [hz] at h

theorem ground_mul_hamiltonian :
    groundProjector S n * hamiltonian S (n+2) =
      (groundEnergy S n : ℂ) • groundProjector S n := by
  have h := atom_mul_hamiltonian S n (zeroVisible S n)
  rw [atom_zero] at h
  have hz := (syndromeEnergy_ground_iff S n (zeroVisible S n)).mpr rfl
  rwa [hz] at h

theorem hamiltonian_mul_channel (A : Op S n) :
    hamiltonian S (n+2) * channel S n A = (groundEnergy S n : ℂ) • channel S n A := by
  calc
    _ = hamiltonian S (n+2) * (groundProjector S n * channel S n A) := by rw [channel_left_support]
    _ = _ := by rw [← mul_assoc, hamiltonian_mul_ground, smul_mul_assoc, channel_left_support]

theorem channel_mul_hamiltonian (A : Op S n) :
    channel S n A * hamiltonian S (n+2) = (groundEnergy S n : ℂ) • channel S n A := by
  calc
    _ = (channel S n A * groundProjector S n) * hamiltonian S (n+2) := by rw [channel_right_support]
    _ = _ := by rw [mul_assoc, ground_mul_hamiltonian, mul_smul_comm, channel_right_support]

/-- This uses the input sector energies, not merely the output support. -/
theorem channel_commutator (A : Op S n) :
    channel S n (hamiltonian S (n+2) * A - A * hamiltonian S (n+2)) = 0 := by
  rw [channel_apply]
  apply Finset.sum_eq_zero
  intro s _
  have hl := atom_mul_hamiltonian S n s
  have hr := hamiltonian_mul_atom S n s
  calc
    _ = correctionOperator S n s *
        ((atom S n s * hamiltonian S (n+2)) * A * atom S n s -
          atom S n s * A * (hamiltonian S (n+2) * atom S n s)) * correctionOperator S n s := by
      noncomm_ring
    _ = 0 := by rw [hl, hr, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]; simp

/-- Source-minus-target energy difference E' - E, with the original sign. -/
theorem channel_nonzero_frequency (A : Op S n) (omega : ℝ) (h : omega ≠ 0) :
    channel S n (Davies.actualFrequency (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) A omega) = 0 := by
  let F := Davies.actualFrequency (hamiltonian S (n+2))
    (CSSGibbs.hamiltonian_symmetric _ _) A omega
  have hf := Davies.actualFrequency_energyDifference (hamiltonian S (n+2))
    (CSSGibbs.hamiltonian_symmetric _ _) A omega
  have hc := channel_commutator S n F
  have hz : channel S n (F * hamiltonian S (n+2) - hamiltonian S (n+2) * F) = 0 := by
    rw [show F * hamiltonian S (n+2) - hamiltonian S (n+2) * F =
      -(hamiltonian S (n+2) * F - F * hamiltonian S (n+2)) by abel, map_neg, hc, neg_zero]
  change channel S n (Davies.energyDifference (hamiltonian S (n+2)) F) = 0 at hz
  rw [hf, map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr h)

/-- Complete frequency reconstruction retains exactly the zero-frequency image. -/
theorem channel_zero_frequency (A : Op S n) :
    channel S n (Davies.actualFrequency (hamiltonian S (n+2))
      (CSSGibbs.hamiltonian_symmetric _ _) A 0) = channel S n A := by
  let b := Davies.hamiltonianBasis (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)
  let e := Davies.hamiltonianEnergies (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)
  letI : Nonempty (Fin (Module.finrank ℂ (Register S n))) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  let i : Fin (Module.finrank ℂ (Register S n)) := Classical.choice inferInstance
  let w : Davies.Frequency e := ⟨0, (Davies.mem_frequencies e 0).mpr ⟨i,i,sub_self _⟩⟩
  have hs := congrArg (channel S n) (Davies.sum_frequencyComponent b e A)
  rw [map_sum, Finset.sum_eq_single w] at hs
  · exact hs
  · intro v _ hv
    apply channel_nonzero_frequency
    intro hz
    exact hv (Subtype.ext hz)
  · simp

/-- Actual positive canonical partition, without a supplied expansion. -/
theorem partition_positive (beta : ℝ) : 0 < physicalPartition S (n+2) beta :=
  CSSGibbs.physicalPartition_pos _ _ beta

/-- Complete visible reindexing removes only proved zero raw atoms. -/
theorem thermal_exponential_atoms (beta : ℝ) : thermalExponential S (n+2) beta =
    ∑ s : Visible S n, (Real.exp (-beta * syndromeEnergy S n s) : ℂ) • atom S n s := by
  have hexp : thermalExponential S (n+2) beta =
      ∑ w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))),
        (Real.exp (-beta * CSSGibbs.energy (zSyndrome S (n+2))
          (xSyndrome S (n+2)) w) : ℂ) • projector S (n+2) w :=
    CSSGibbs.thermalExponential_resolution _ _ (row_orthogonal S (n+2)) beta
  rw [hexp]
  have hs := Finset.sum_subset (Finset.subset_univ
    (CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2))))
    (f := fun w => (Real.exp (-beta * CSSGibbs.energy (zSyndrome S (n+2))
      (xSyndrome S (n+2)) w) : ℂ) • projector S (n+2) w)
    (by
      intro w _ hw
      have hz : projector S (n+2) w = 0 :=
        CSSGibbs.projector_eq_zero_of_not_realizable _ _ (row_orthogonal S (n+2)) w hw
      rw [hz, smul_zero])
  rw [← hs]
  simp only [CSSGibbs.realizableSyndromes, Finset.sum_map]
  rfl

/-- Actual rank two supplies the normalization coefficient. -/
theorem partition_visible_sum (beta : ℝ) : physicalPartition S (n+2) beta =
    2 * ∑ s : Visible S n, Real.exp (-beta * syndromeEnergy S n s) := by
  have h := CSSGibbs.physicalPartition_syndrome_sum (zSyndrome S (n+2))
    (xSyndrome S (n+2)) (row_orthogonal S (n+2)) beta
  change physicalPartition S (n+2) beta = multiplicity S (n+2) *
    ∑ s : Visible S n, Real.exp (-beta * syndromeEnergy S n s) at h
  rwa [multiplicity_two] at h

/-- The actual exponential is evaluated before canonical Gibbs normalization. -/
theorem channel_thermal_exponential (beta : ℝ) :
    channel S n (thermalExponential S (n+2) beta) =
      (∑ s : Visible S n, (Real.exp (-beta * syndromeEnergy S n s) : ℂ)) • groundProjector S n := by
  rw [thermal_exponential_atoms, channel_weighted_atoms]

/-- Normalized physical Gibbs image, at every finite real inverse temperature. -/
theorem channel_gibbs (beta : ℝ) :
    channel S n (gibbs S (n+2) beta).toOperator = (2 : ℂ)⁻¹ • groundProjector S n := by
  rw [gibbs_normalized_exp, map_smul, channel_thermal_exponential, smul_smul]
  have hz : (physicalPartition S (n+2) beta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (partition_positive S n beta).ne'
  have hs : (physicalPartition S (n+2) beta : ℂ) =
      2 * (∑ s : Visible S n, (Real.exp (-beta * syndromeEnergy S n s) : ℂ)) := by
    exact_mod_cast partition_visible_sum S n beta
  congr 1
  have hw : (∑ s : Visible S n, (Real.exp (-beta * syndromeEnergy S n s) : ℂ)) =
      (physicalPartition S (n+2) beta : ℂ) / 2 := by
    linear_combination -(1/2 : ℂ) * hs
  rw [hw]
  field_simp [hz]

/-- A derived density, independent of an unproved code-normalization record. -/
def groundDensity : DensityOperator (Register S n) :=
  (channel S n).mapDensity (gibbs S (n+2) 0)

@[simp] theorem groundDensity_toOperator :
    (groundDensity S n).toOperator = (2 : ℂ)⁻¹ • groundProjector S n := channel_gibbs S n 0

theorem channel_gibbs_density (beta : ℝ) :
    (channel S n).mapDensity (gibbs S (n+2) beta) = groundDensity S n := by
  apply DensityOperator.ext_toOperator
  exact (channel_gibbs S n beta).trans (groundDensity_toOperator S n).symm

private theorem pair_auxiliary_nontrivial {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteQuantumSystem V] [Nontrivial V]
    (P : ThermalEncoding.PauliLikePair V) : Nontrivial P.AuxiliarySpace := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have ha : ∃ a : P.AuxiliarySpace, a ≠ 0 := by
    by_contra h
    have hz : ∀ a : P.AuxiliarySpace, a = 0 := by
      intro a
      by_contra hne
      exact h ⟨a,hne⟩
    have ht (w : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) : w = 0 := by
      apply P.qubitAuxCoordinates.injective
      apply Prod.ext <;> simp [hz]
    have he := congrArg P.factorization (ht (P.factorization.symm v))
    exact hv (by simpa using he)
  obtain ⟨a, ha⟩ := ha
  exact { exists_pair_ne := ⟨a,0,ha⟩ }

/-- Auxiliary nontriviality is constructed from the actual derived factorization. -/
theorem auxiliary_nontrivial : Nontrivial (dressedPauliPair S n).AuxiliarySpace :=
  pair_auxiliary_nontrivial _
local instance : Nontrivial (dressedPauliPair S n).AuxiliarySpace := auxiliary_nontrivial S n

private theorem H_commutes_X : Commute (hamiltonian S (n+2)) (dressedPauliPair S n).x :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm
private theorem H_commutes_Z : Commute (hamiltonian S (n+2)) (dressedPauliPair S n).z :=
  (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))).symm

/-- Canonical Gibbs state of the actual restricted Hamiltonian. -/
def auxiliaryGibbs (beta : ℝ) : DensityOperator (dressedPauliPair S n).AuxiliarySpace :=
  (dressedPauliPair S n).auxiliaryGibbsState (hamiltonian S (n+2))
    (H_commutes_Z S n) (CSSGibbs.hamiltonian_symmetric _ _) beta

/-- The physical Gibbs density is the derived dressed thermal reference, for the SAME H. -/
theorem gibbs_eq_thermal_reference (beta : ℝ) :
    gibbs S (n+2) beta = (dressedPauliPair S n).thermalReferenceState (auxiliaryGibbs S n beta) := by
  apply DensityOperator.ext_toOperator
  have h := Davies.hamiltonianGibbs_eq_physicalGibbsState (dressedPauliPair S n)
    (hamiltonian S (n+2)) (CSSGibbs.hamiltonian_symmetric _ _)
    (H_commutes_X S n) (H_commutes_Z S n) beta
  exact h.trans (congrArg DensityOperator.toOperator
    ((dressedPauliPair S n).physicalGibbsState_eq_thermalReferenceState
      (hamiltonian S (n+2)) (H_commutes_Z S n) (CSSGibbs.hamiltonian_symmetric _ _) beta))

/-- Only the canonical actual-H auxiliary Gibbs state is prepared. -/
def encoding (beta : ℝ) : QuantumChannel Qubit.QubitSpace (Register S n) :=
  (dressedPauliPair S n).thermalEncoding (auxiliaryGibbs S n beta)

theorem readout_encoding (beta : ℝ) (A : Operator Qubit.QubitSpace) :
    readout S n (encoding S n beta A) = A :=
  readout_encode S n (auxiliaryGibbs S n beta) A

theorem readout_encoding_density (beta : ℝ) (rho : DensityOperator Qubit.QubitSpace) :
    (readout S n).mapDensity ((encoding S n beta).mapDensity rho) = rho := by
  apply DensityOperator.ext_toOperator
  exact readout_encoding S n beta rho.toOperator

/-- Scalar tensor cancellation is proved with a fixed generic pair, before specializing
its dependent auxiliary carrier to the concrete dressed pair. -/
private theorem pair_encoding_mul_reference {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
    (P : ThermalEncoding.PauliLikePair H) (sigma : DensityOperator P.AuxiliarySpace)
    (A : Operator Qubit.QubitSpace) :
    P.thermalEncoding sigma A = (2 : ℂ) •
      (pairEmbedding P A * (P.thermalReferenceState sigma).toOperator) := by
  let T : Operator (Qubit.QubitSpace ⊗[ℂ] P.AuxiliarySpace) :=
    TensorProduct.map A (1 : Operator P.AuxiliarySpace)
  let B : Operator (Qubit.QubitSpace ⊗[ℂ] P.AuxiliarySpace) :=
    TensorProduct.map ((2 : ℂ)⁻¹ • (1 : Operator Qubit.QubitSpace)) sigma.toOperator
  have hemb : pairEmbedding P A = P.factorization.conjOperator T := rfl
  have ht : (2 : ℂ) • (T * B) = TensorProduct.map A sigma.toOperator := by
    dsimp only [T, B]
    rw [← TensorProduct.map_mul, one_mul, ← TensorProduct.map_smul_left]
    congr 1
    ext v
    simp
  have hscalar : P.factorization.conjOperator ((2 : ℂ) • (T * B)) =
      (2 : ℂ) • P.factorization.conjOperator (T * B) :=
    P.factorization.conjOperatorLinearMap.map_smul (2 : ℂ) (T * B)
  have hproduct : P.factorization.conjOperator (T * B) =
      P.factorization.conjOperator T * P.factorization.conjOperator B :=
    P.factorization.conjOperator_mul T B
  rw [ThermalEncoding.PauliLikePair.thermalEncoding_apply,
    ThermalEncoding.PauliLikePair.thermalReferenceState_toOperator, hemb]
  calc
    _ = P.factorization.conjOperator ((2 : ℂ) • (T * B)) :=
      congrArg P.factorization.conjOperator ht.symm
    _ = (2 : ℂ) • P.factorization.conjOperator (T * B) := hscalar
    _ = _ := congrArg (fun F : Operator H => (2 : ℂ) • F) hproduct

/-- Direct tensor algebra for ALL complex qubit operators, not density-only instantiation. -/
theorem encoding_mul_gibbs (beta : ℝ) (A : Operator Qubit.QubitSpace) :
    encoding S n beta A = (2 : ℂ) •
      (pairEmbedding (dressedPauliPair S n) A * (gibbs S (n+2) beta).toOperator) := by
  rw [gibbs_eq_thermal_reference]
  change (dressedPauliPair S n).thermalEncoding (auxiliaryGibbs S n beta) A = _
  exact pair_encoding_mul_reference (dressedPauliPair S n) (auxiliaryGibbs S n beta) A

theorem encoding_gibbs_mul (beta : ℝ) (A : Operator Qubit.QubitSpace) :
    encoding S n beta A = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * pairEmbedding (dressedPauliPair S n) A) := by
  rw [gibbs_eq_thermal_reference, ThermalEncoding.PauliLikePair.thermalReferenceState_toOperator]
  change (dressedPauliPair S n).thermalEncoding (auxiliaryGibbs S n beta) A = _
  rw [ThermalEncoding.PauliLikePair.thermalEncoding_apply]
  change (dressedPauliPair S n).factorization.conjOperator
      (TensorProduct.map A (auxiliaryGibbs S n beta).toOperator) =
    (2 : ℂ) • ((dressedPauliPair S n).factorization.conjOperator (TensorProduct.map ((2 : ℂ)⁻¹ • (1 : Operator Qubit.QubitSpace)) (auxiliaryGibbs S n beta).toOperator) *
      (dressedPauliPair S n).factorization.conjOperator (TensorProduct.map A (1 : Operator (dressedPauliPair S n).AuxiliarySpace)))
  have ht : (2 : ℂ) • ((TensorProduct.map ((2 : ℂ)⁻¹ • (1 : Operator Qubit.QubitSpace)) (auxiliaryGibbs S n beta).toOperator) * (TensorProduct.map A (1 : Operator (dressedPauliPair S n).AuxiliarySpace))) =
      TensorProduct.map A (auxiliaryGibbs S n beta).toOperator := by
    rw [← TensorProduct.map_mul, mul_one, ← TensorProduct.map_smul_left]
    congr 1
    ext v
    simp
  calc
    _ = (dressedPauliPair S n).factorization.conjOperator
        ((2 : ℂ) • ((TensorProduct.map ((2 : ℂ)⁻¹ • (1 : Operator Qubit.QubitSpace)) (auxiliaryGibbs S n beta).toOperator) * (TensorProduct.map A (1 : Operator (dressedPauliPair S n).AuxiliarySpace)))) :=
      congrArg (dressedPauliPair S n).factorization.conjOperator ht.symm
    _ = (2 : ℂ) • (dressedPauliPair S n).factorization.conjOperator ((TensorProduct.map ((2 : ℂ)⁻¹ • (1 : Operator Qubit.QubitSpace)) (auxiliaryGibbs S n beta).toOperator) * (TensorProduct.map A (1 : Operator (dressedPauliPair S n).AuxiliarySpace))) :=
      (dressedPauliPair S n).factorization.conjOperatorLinearMap.map_smul (2 : ℂ) _
    _ = _ := congrArg (fun T : Op S n => (2 : ℂ) • T)
      ((dressedPauliPair S n).factorization.conjOperator_mul (TensorProduct.map ((2 : ℂ)⁻¹ • (1 : Operator Qubit.QubitSpace)) (auxiliaryGibbs S n beta).toOperator) (TensorProduct.map A (1 : Operator (dressedPauliPair S n).AuxiliarySpace)))

private theorem embedding_one : pairEmbedding (dressedPauliPair S n) 1 = 1 := by
  change (dressedPauliPair S n).factorization.conjOperator (TensorProduct.map 1 1) = 1
  have ht : TensorProduct.map (1 : Operator Qubit.QubitSpace)
      (1 : Operator (dressedPauliPair S n).AuxiliarySpace) = 1 := by
    ext q a
    simp
  rw [ht, UnitaryTransport.conjOperator_one]
private theorem embedding_X : pairEmbedding (dressedPauliPair S n) Qubit.pauliX = dressedX S n :=
  (dressedPauliPair S n).conj_tensorPauliX
private theorem embedding_Z : pairEmbedding (dressedPauliPair S n) Qubit.pauliZ = dressedZ S n :=
  (dressedPauliPair S n).conj_tensorPauliZ
private theorem embedding_Y : pairEmbedding (dressedPauliPair S n) Qubit.pauliY = dressedY S n := by
  rw [qubitY_eq, map_smul, pairEmbedding_mul, embedding_X, embedding_Z]
  rfl

theorem encoding_one (beta : ℝ) :
    encoding S n beta 1 = (2 : ℂ) • (gibbs S (n+2) beta).toOperator := by
  rw [encoding_mul_gibbs, embedding_one, one_mul]

theorem encoding_X (beta : ℝ) :
    encoding S n beta Qubit.pauliX = (2 : ℂ) •
      (dressedX S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_X]
theorem encoding_Y (beta : ℝ) :
    encoding S n beta Qubit.pauliY = (2 : ℂ) •
      (dressedY S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_Y]
theorem encoding_Z (beta : ℝ) :
    encoding S n beta Qubit.pauliZ = (2 : ℂ) •
      (dressedZ S n * (gibbs S (n+2) beta).toOperator) := by
  rw [encoding_mul_gibbs, embedding_Z]
theorem encoding_X_right (beta : ℝ) :
    encoding S n beta Qubit.pauliX = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * dressedX S n) := by
  rw [encoding_gibbs_mul, embedding_X]
theorem encoding_Y_right (beta : ℝ) :
    encoding S n beta Qubit.pauliY = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * dressedY S n) := by
  rw [encoding_gibbs_mul, embedding_Y]
theorem encoding_Z_right (beta : ℝ) :
    encoding S n beta Qubit.pauliZ = (2 : ℂ) •
      ((gibbs S (n+2) beta).toOperator * dressedZ S n) := by
  rw [encoding_gibbs_mul, embedding_Z]

/-- Exact physical Gibbs readout through the unchanged complete channel. -/
theorem readout_gibbs (beta : ℝ) :
    readout S n (gibbs S (n+2) beta).toOperator = ThermalEncoding.PauliLikePair.maximallyMixedQubit.toOperator := by
  have hi := encoding_one S n beta
  have he := congrArg (readout S n) hi
  rw [readout_encoding, map_smul] at he
  change readout S n (gibbs S (n+2) beta).toOperator = (2 : ℂ)⁻¹ • 1
  have h := congrArg (fun T : Operator Qubit.QubitSpace => (2 : ℂ)⁻¹ • T) he
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using h.symm

theorem readout_gibbs_density (beta : ℝ) :
    (readout S n).mapDensity (gibbs S (n+2) beta) = ThermalEncoding.PauliLikePair.maximallyMixedQubit := by
  apply DensityOperator.ext_toOperator
  exact readout_gibbs S n beta

/-- Every source-even physical level is covered, including C2 at k=1. -/
theorem source_even_gibbs (k : Nat) (hk : 1 ≤ k) (beta : ℝ) :
    ∃ n : Nat, n+2 = 2*k ∧
      channel S n (gibbs S (n+2) beta).toOperator = (2 : ℂ)⁻¹ • groundProjector S n ∧
      readout S n (gibbs S (n+2) beta).toOperator = ThermalEncoding.PauliLikePair.maximallyMixedQubit.toOperator :=
  ⟨2*(k-1), BDL26TransposedStoppedDecoder.source_even_level k hk,
    channel_gibbs S _ beta, readout_gibbs S _ beta⟩

end QEC.Coding.BDL26PairedDecoderGibbs
end
