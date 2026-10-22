import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Gibbs
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Incidence
import QEC.Coding.CSS.DaviesLocality

/-!
# Davies tensor support on the actual recursive CSS family

The Hamiltonian retains every Z+X row label, including identity and repeated
rows. CLBT10's incident-check reduction is applied to that full Hamiltonian.
The bound 50 counts physical coordinates; it asserts no Euclidean diameter.
-/

noncomputable section
namespace QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators

variable (S : OddScale) (n : Nat)

/-- The source ordering is Z labels followed by X labels, without deduplication. -/
abbrev Label := Sum (ZLabel S n) (XLabel S n)

theorem row_eq (j : Label S n) :
    CSSDaviesLocality.row (zSyndrome S n) (xSyndrome S n) j = check S n j := rfl

theorem rowOperator_eq (j : Label S n) :
    CSSDaviesLocality.rowOperator (zSyndrome S n) (xSyndrome S n) j =
      toQubitOperator (check S n j) := rfl

theorem rowSupport_eq (j : Label S n) :
    CSSDaviesLocality.rowSupport (zSyndrome S n) (xSyndrome S n) j =
      checkSupport S n j := rfl

theorem incident_eq (q : Physical S n) :
    CSSDaviesLocality.incident (zSyndrome S n) (xSyndrome S n) q =
      incident S n q := rfl

theorem region_eq (q : Physical S n) :
    CSSDaviesLocality.region (zSyndrome S n) (xSyndrome S n) q = region S n q := rfl

/-- The canonical actual physical region, with the existing tensor semantics. -/
def subsystem (q : Physical S n) : FiniteSubsystem (Physical S n) := ⟨region S n q⟩

theorem subsystem_eq (q : Physical S n) :
    CSSDaviesLocality.subsystem (zSyndrome S n) (xSyndrome S n) q =
      subsystem S n q := rfl

theorem hamiltonian_eq :
    CSSDaviesLocality.hamiltonian (zSyndrome S n) (xSyndrome S n) =
      BDL26CSSHamiltonian.hamiltonian S n := rfl

/-- The incident part uses exactly the actual labelled-check incidence. -/
def incidentHamiltonian (q : Physical S n) : Operator (Qubit.QubitRegister (Physical S n)) :=
  -∑ j ∈ incident S n q, toQubitOperator (check S n j)

theorem incidentHamiltonian_eq (q : Physical S n) :
    CSSDaviesLocality.incidentHamiltonian (zSyndrome S n) (xSyndrome S n) q =
      incidentHamiltonian S n q := rfl

/-- Adjoint equality comes from the actual check's Hermitian phase. -/
theorem check_adjoint (j : Label S n) :
    LinearMap.adjoint (toQubitOperator (check S n j)) = toQubitOperator (check S n j) := by
  rw [← check_hermitian S n j, adjoint_toHermitianQubitOperator_eq_self]

theorem checks_commute (j k : Label S n) :
    Commute (toQubitOperator (check S n j)) (toQubitOperator (check S n k)) :=
  CSSDaviesLocality.rows_commute (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n) j k

/-- No caller-provided symmetry or alternative spectral model is used. -/
theorem hamiltonian_symmetric : (BDL26CSSHamiltonian.hamiltonian S n).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp only [BDL26CSSHamiltonian.hamiltonian, map_neg, map_sum, check_adjoint]

theorem incidentHamiltonian_symmetric (q : Physical S n) :
    (incidentHamiltonian S n q).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp only [incidentHamiltonian, map_neg, map_sum, check_adjoint]

/-- Actual physical X, Hermitian Y, and Z couplings on the recursive register. -/
def coupling (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    Operator (Qubit.QubitRegister (Physical S n)) := CSSDaviesLocality.coupling q a

@[simp] theorem coupling_x (q : Physical S n) : coupling S n q .x = Qubit.localX q :=
  CSSDaviesLocality.coupling_x q

@[simp] theorem coupling_y (q : Physical S n) :
    coupling S n q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) :=
  CSSDaviesLocality.coupling_y q

@[simp] theorem coupling_z (q : Physical S n) : coupling S n q .z = Qubit.localZ q :=
  CSSDaviesLocality.coupling_z q

theorem coupling_adjoint (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    LinearMap.adjoint (coupling S n q a) = coupling S n q a :=
  CSSDaviesLocality.coupling_adjoint q a

theorem coupling_square (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    coupling S n q a * coupling S n q a = 1 :=
  toHermitianQubitOperator_square (CSSDaviesLocality.singlePauli q a)

theorem coupling_ne_zero (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    coupling S n q a ≠ 0 := by
  intro h
  have hs := coupling_square S n q a
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

/-- The same literal full-H sector energy, counting all labels with multiplicity. -/
theorem sector_energy (u : Word (ZMod 2) (ZLabel S n))
    (v : Word (ZMod 2) (XLabel S n)) :
    BDL26CSSHamiltonian.hamiltonian S n * projector S n (CSSGibbs.joinSyndrome u v) =
      (((-((Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat) : ℝ) +
        2 * ((HammingWeight u : ℝ) + (HammingWeight v : ℝ))) : ℝ) : ℂ) •
          projector S n (CSSGibbs.joinSyndrome u v) :=
  hamiltonian_sector_energy S n u v

/-- Complementary check terms change no coherent frequency component. -/
theorem frequency_eq_incident (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω =
    actualFrequency (incidentHamiltonian S n q) (incidentHamiltonian_symmetric S n q)
      (coupling S n q a) ω :=
  CSSDaviesLocality.frequency_eq_incident (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n) q a ω

theorem incidentHamiltonian_supported (q : Physical S n) :
    (subsystem S n q).OperatorSupportedOnRegister (incidentHamiltonian S n q) :=
  CSSDaviesLocality.incidentHamiltonian_supported (zSyndrome S n) (xSyndrome S n) q

theorem coupling_supported (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (subsystem S n q).OperatorSupportedOnRegister (coupling S n q a) :=
  CSSDaviesLocality.coupling_supported (zSyndrome S n) (xSyndrome S n) q a

/-- All real frequencies, including those outside the actual Bohr spectrum. -/
theorem frequency_supported (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω) :=
  CSSDaviesLocality.frequency_supported (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n) q a ω

/-- Energy transferred to the bath is the right-energy minus left-energy gap. -/
theorem frequency_energyDifference (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω * BDL26CSSHamiltonian.hamiltonian S n -
      BDL26CSSHamiltonian.hamiltonian S n *
        actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω =
    (ω : ℂ) • actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω :=
  actualFrequency_energyDifference _ _ _ ω

/-- The bath index contains every physical site and all three axes. -/
abbrev CouplingIndex := Physical S n × CSSDaviesLocality.Axis
abbrev Frequency := HamiltonianFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)

theorem jump_eq_sqrt_smul (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
      (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) =
    (Real.sqrt (rate (q,a) ω) : ℂ) •
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val := rfl

/-- Algebraic support needs no positivity or detailed-balance assumption on rates. -/
theorem weightedJump_supported (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) := by
  rw [jump_eq_sqrt_smul]
  exact (subsystem S n q).supported_smul _ (frequency_supported S n q a ω.val)

theorem frequency_supported_card (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω) ∧ (subsystem S n q).selected.card ≤ 50 :=
  ⟨frequency_supported S n q a ω, region_card_le_fifty S n q⟩

theorem weightedJump_supported_card (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
      (subsystem S n q).selected.card ≤ 50 :=
  ⟨weightedJump_supported S n rate q a ω, region_card_le_fifty S n q⟩

/-- Complete coherent reconstruction on the actual full-H spectrum. -/
theorem sum_actualFrequency (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (∑ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val) = coupling S n q a :=
  sum_frequencyComponent _ _ _

/-- A genuine component survives for every actual physical coupling. -/
theorem exists_nonzero_actualFrequency (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    ∃ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : (∑ ω : Frequency S n,
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val) = 0 := Finset.sum_eq_zero (fun ω _ => h ω)
  rw [sum_actualFrequency S n q a] at hz
  exact coupling_ne_zero S n q a hz

end QEC.Coding.BDL26CSSDaviesLocality
