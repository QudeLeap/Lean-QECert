import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.DaviesLocality

/-!
# A bounded-rate Davies bath on the actual recursive CSS family

The couplings are all literal physical X/Y/Z operators. Their norm is derived
from their adjoint and square identities, including the Hermitian Y phase.
CLBT10, `arXiv.02.tex:899-931,969-1022`, supplies detailed balance and the
coupling-count norm bound. The Hamiltonian is exactly BDL26,
`paper.tex:3383`, with all labelled checks retained. Only the dissipator is
bounded here; no Hamiltonian commutator or memory-time conclusion is included.
-/

noncomputable section
namespace QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators

variable (S : OddScale) (n : Nat)

/-- Every actual coupling preserves the physical register inner product. -/
theorem coupling_inner (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (v w : Qubit.QubitRegister (Physical S n)) :
    inner ℂ (coupling S n q a v) (coupling S n q a w) = inner ℂ v w := by
  have hv : coupling S n q a (coupling S n q a v) = v :=
    congrArg (fun T : Operator (Qubit.QubitRegister (Physical S n)) => T v)
      (coupling_square S n q a)
  calc
    _ = inner ℂ (LinearMap.adjoint (coupling S n q a) (coupling S n q a v)) w :=
      (LinearMap.adjoint_inner_left (coupling S n q a) w (coupling S n q a v)).symm
    _ = inner ℂ v w := by rw [coupling_adjoint, hv]

theorem coupling_norm_apply (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (v : Qubit.QubitRegister (Physical S n)) : ‖coupling S n q a v‖ = ‖v‖ :=
  ((LinearMap.norm_map_iff_inner_map_map (𝕜 := ℂ) (coupling S n q a)).mpr
    (coupling_inner S n q a)) v

/-- Exact norm one is proved, never supplied as a bath assumption. -/
theorem coupling_operatorNorm_eq_one (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    operatorNorm (coupling S n q a) = 1 := by
  unfold operatorNorm
  apply ContinuousLinearMap.homothety_norm
  intro v
  simpa only [LinearMap.coe_toContinuousLinearMap', one_mul] using coupling_norm_apply S n q a v

theorem coupling_operatorNorm_le_one (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    operatorNorm (coupling S n q a) ≤ 1 := (coupling_operatorNorm_eq_one S n q a).le

theorem coupling_symmetric (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    (coupling S n q a).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  exact coupling_adjoint S n q a

/-- All three axes remain present, including Y. -/
theorem axis_card : Fintype.card CSSDaviesLocality.Axis = 3 := by decide

theorem couplingIndex_card : Fintype.card (CouplingIndex S n) =
    3 * Fintype.card (Physical S n) := by
  rw [Fintype.card_prod, axis_card, Nat.mul_comm]

/-- Negation is the existing involution on the actual full-H energy gaps. -/
abbrev oppositeFrequency (ω : BDL26CSSDaviesLocality.Frequency S n) :
    BDL26CSSDaviesLocality.Frequency S n :=
  negFrequency (hamiltonianEnergies (BDL26CSSHamiltonian.hamiltonian S n)
    (hamiltonian_symmetric S n)) ω

@[simp] theorem oppositeFrequency_val (ω : BDL26CSSDaviesLocality.Frequency S n) :
    (oppositeFrequency S n ω).val = -ω.val := rfl

@[simp] theorem oppositeFrequency_opposite (ω : BDL26CSSDaviesLocality.Frequency S n) :
    oppositeFrequency S n (oppositeFrequency S n ω) = ω := by
  apply Subtype.ext
  simp only [oppositeFrequency_val, neg_neg]

/-- The original full-H frequency construction with square-root rates. -/
def jump (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    CouplingIndex S n × BDL26CSSDaviesLocality.Frequency S n →
      Operator (Qubit.QubitRegister (Physical S n)) :=
  hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
    (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate

theorem jump_eq_sqrt_frequency
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S n) :
    jump S n rate ((q,a),ω) = (Real.sqrt (rate (q,a) ω) : ℂ) •
      actualFrequency (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω.val := rfl

/-- The actual Davies dissipator, excluding the Hamiltonian commutator. -/
def dissipator (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    Superoperator (Qubit.QubitRegister (Physical S n)) :=
  hamiltonianDissipator (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
    (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate

theorem dissipator_eq_lindblad
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    dissipator S n rate = lindbladDissipator (jump S n rate) := rfl

/-- The physical family Gibbs state uses this same literal Hamiltonian.
The independently proved symmetry witnesses are propositionally irrelevant. -/
theorem actual_gibbs_eq (β : ℝ) :
    (BDL26CSSHamiltonian.gibbs S n β).toOperator =
      (hamiltonianGibbs (BDL26CSSHamiltonian.hamiltonian S n)
        (hamiltonian_symmetric S n) β).toOperator := rfl

/-- Detailed balance fixes the actual family Gibbs state, at the physical β. -/
theorem gibbs_stationary
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) (β : ℝ)
    (hn : ∀ qa ω, 0 ≤ rate qa ω)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S n ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S n rate (BDL26CSSHamiltonian.gibbs S n β).toOperator = 0 := by
  rw [actual_gibbs_eq]
  exact hamiltonianGibbs_stationary (BDL26CSSHamiltonian.hamiltonian S n)
    (hamiltonian_symmetric S n) (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2)
    (fun qa => coupling_symmetric S n qa.1 qa.2) rate β hn hDB

/-- The bound counts three physical couplings per qubit, with no gap multiplier. -/
theorem dissipator_selfAdjointTraceNorm_le
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ qa ω, 0 ≤ rate qa ω) (hu : ∀ qa ω, rate qa ω ≤ hmax) :
    selfAdjointTraceNormOneToOne (dissipator S n rate) ≤
      6 * Fintype.card (Physical S n) * hmax := by
  have h := hamiltonianDissipator_selfAdjointTraceNorm_le
    (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
    (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2)
    (fun qa => coupling_operatorNorm_le_one S n qa.1 qa.2) rate hmax hm hn hu
  calc
    _ ≤ 2 * (Fintype.card (CouplingIndex S n) : ℝ) * hmax := h
    _ = 6 * Fintype.card (Physical S n) * hmax := by
      rw [couplingIndex_card]
      push_cast
      ring

/-- Physical positive bounded detailed-balance rates give both conclusions. -/
theorem bounded_rate_application
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (β hmax : ℝ) (_hβ : 0 ≤ β) (hm : 0 < hmax)
    (hr : ∀ qa ω, 0 < rate qa ω ∧ rate qa ω ≤ hmax)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S n ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S n rate (BDL26CSSHamiltonian.gibbs S n β).toOperator = 0 ∧
      selfAdjointTraceNormOneToOne (dissipator S n rate) ≤
        6 * Fintype.card (Physical S n) * hmax :=
  ⟨gibbs_stationary S n rate β (fun qa ω => (hr qa ω).1.le) hDB,
    dissipator_selfAdjointTraceNorm_le S n rate hmax hm.le
      (fun qa ω => (hr qa ω).1.le) (fun qa ω => (hr qa ω).2)⟩

/-- Source-even prefixes retain the literal physical Hamiltonian and β. -/
theorem even_gibbs_stationary (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ) (β : ℝ)
    (hn : ∀ qa ω, 0 ≤ rate qa ω)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S (2*k) ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S (2*k) rate (BDL26CSSHamiltonian.gibbs S (2*k) β).toOperator = 0 :=
  gibbs_stationary S (2*k) rate β hn hDB

theorem even_dissipator_selfAdjointTraceNorm_le (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ qa ω, 0 ≤ rate qa ω) (hu : ∀ qa ω, rate qa ω ≤ hmax) :
    selfAdjointTraceNormOneToOne (dissipator S (2*k) rate) ≤
      6 * Fintype.card (Physical S (2*k)) * hmax :=
  dissipator_selfAdjointTraceNorm_le S (2*k) rate hmax hm hn hu

theorem even_bounded_rate_application (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hm : 0 < hmax)
    (hr : ∀ qa ω, 0 < rate qa ω ∧ rate qa ω ≤ hmax)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S (2*k) ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S (2*k) rate (BDL26CSSHamiltonian.gibbs S (2*k) β).toOperator = 0 ∧
      selfAdjointTraceNormOneToOne (dissipator S (2*k) rate) ≤
        6 * Fintype.card (Physical S (2*k)) * hmax :=
  bounded_rate_application S (2*k) rate β hmax hβ hm hr hDB

end QEC.Coding.BDL26BoundedRateDavies
