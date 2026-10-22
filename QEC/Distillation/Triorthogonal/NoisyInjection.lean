import QEC.Distillation.Core.MagicStateProtocol
import QEC.Distillation.Triorthogonal.Transversal
import QEC.Coding.Stabilizer.Measurement

/-!
# BH12 noisy magic-state injection

The one-resource A-basis input, the exact ideal-`T`-then-stochastic-`Z`
channel, and its independent finite-register product.  The protocol and
syndrome postselection live in `BH12Protocol`.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace Triorthogonal
namespace BH12NoisyInjection

open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

universe u

/-- An explicit physical error rate in the closed unit interval. -/
structure ErrorParameter where
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_le_one : rate ≤ 1

namespace ErrorParameter

/-- The no-error probability. -/
def cleanWeight (p : ErrorParameter) : ℝ := 1 - p.rate

theorem cleanWeight_nonneg (p : ErrorParameter) : 0 ≤ p.cleanWeight :=
  sub_nonneg.mpr p.rate_le_one

theorem cleanWeight_le_one (p : ErrorParameter) : p.cleanWeight ≤ 1 := by
  dsimp [cleanWeight]
  linarith [p.rate_nonneg]

theorem cleanWeight_add_rate (p : ErrorParameter) :
    p.cleanWeight + p.rate = 1 := by
  simp [cleanWeight]

end ErrorParameter

namespace OneQubit

open Semantics.Qubit
open OneQubitMagic

/-- Pauli `Z` as a linear equivalence, with itself as inverse. -/
def zLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk pauliZ pauliZ
    (fun psi => by
      have h := LinearMap.congr_fun pauliZ_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun pauliZ_square psi
      simpa [Module.End.mul_apply] using h)

@[simp] theorem zLinearEquiv_apply (psi : QubitSpace) :
    zLinearEquiv psi = pauliZ psi :=
  rfl

@[simp] theorem zLinearEquiv_symm_apply (psi : QubitSpace) :
    zLinearEquiv.symm psi = pauliZ psi :=
  rfl

theorem pauliZ_map_inner (psi phi : QubitSpace) :
    inner Complex (pauliZ psi) (pauliZ phi) = inner Complex psi phi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two, pauliZ_apply, RCLike.inner_apply, map_mul]
  ring_nf
  simp

/-- Pauli `Z` packaged as a unitary transport. -/
def zTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := zLinearEquiv
  map_inner := pauliZ_map_inner

/-- The source state `|A₀⟩ = |A⟩`. -/
def aZeroState : QubitSpace :=
  phaseState (Real.pi / 4)

/-- The source state `|A₁⟩ = Z|A₀⟩`. -/
def aOneState : QubitSpace :=
  zTransport aZeroState

@[simp] theorem aOneState_eq_pauliZ :
    aOneState = pauliZ aZeroState :=
  rfl

@[simp] theorem aZeroState_norm : ‖aZeroState‖ = 1 := by
  exact phaseState_norm (Real.pi / 4)

@[simp] theorem aOneState_norm : ‖aOneState‖ = 1 := by
  change ‖zTransport.toLinearIsometryEquiv aZeroState‖ = 1
  rw [zTransport.toLinearIsometryEquiv.norm_map, aZeroState_norm]

/-- The pure density `|A₀⟩⟨A₀|`. -/
def aZeroDensity : DensityOperator QubitSpace :=
  phaseStateDensity (Real.pi / 4)

/-- The pure density `|A₁⟩⟨A₁|`, obtained by actual `Z` conjugation. -/
def aOneDensity : DensityOperator QubitSpace :=
  zTransport.conjDensity aZeroDensity

@[simp] theorem aOneDensity_toOperator :
    aOneDensity.toOperator =
      pauliZ.comp (aZeroDensity.toOperator.comp pauliZ) := by
  rw [aOneDensity, UnitaryTransport.conjDensity_toOperator]
  ext psi
  rfl

/-- The source-exact diagonal noisy A-basis resource. -/
def diagonalAResource (p : ErrorParameter) : DensityOperator QubitSpace :=
  outcomeMixture p.cleanWeight p.cleanWeight_nonneg p.cleanWeight_le_one
    aZeroDensity aOneDensity

@[simp] theorem diagonalAResource_toOperator (p : ErrorParameter) :
    (diagonalAResource p).toOperator =
      p.cleanWeight • aZeroDensity.toOperator +
        p.rate • aOneDensity.toOperator := by
  simp [diagonalAResource, outcomeMixture,
    DensityOperator.convexCombinationOperator, branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide,
    ErrorParameter.cleanWeight]

/-- Compose two same-space unitary transports in circuit order. -/
def composeTransport
    (after before : UnitaryTransport QubitSpace QubitSpace) :
    UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := before.toLinearEquiv.trans after.toLinearEquiv
  map_inner := by
    intro psi phi
    change inner Complex (after (before psi)) (after (before phi)) =
      inner Complex psi phi
    rw [after.map_inner, before.map_inner]

/-- The ideal physical `T` transport. -/
def idealTTransport : UnitaryTransport QubitSpace QubitSpace :=
  phaseShiftTransport (Real.pi / 4)

/-- The computational basis transported to the source A basis by `T H`. -/
def aBasisTransport : UnitaryTransport QubitSpace QubitSpace :=
  composeTransport idealTTransport hadamardTransport

@[simp] theorem aBasisTransport_basis_zero :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 0) =
      aZeroState := by
  ext bit
  fin_cases bit
  all_goals simp [aBasisTransport, composeTransport, idealTTransport,
    hadamardTransport, aZeroState, phaseState]
  all_goals ring

@[simp] theorem aBasisTransport_basis_one :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 1) =
      aOneState := by
  ext bit
  fin_cases bit
  all_goals simp [aBasisTransport, composeTransport, idealTTransport,
    hadamardTransport, aOneState, aZeroState, phaseState, zTransport,
    zLinearEquiv]
  all_goals ring

/-- The Hermitian source observable with eigenbasis `|A₀⟩, |A₁⟩`. -/
def aBasisObservable : Operator QubitSpace :=
  aBasisTransport.conjOperator pauliZ

theorem aBasisObservable_adjoint :
    LinearMap.adjoint aBasisObservable = aBasisObservable := by
  rw [aBasisObservable, UnitaryTransport.conjOperator_adjoint, pauliZ_adjoint]

theorem aBasisObservable_square :
    aBasisObservable * aBasisObservable = 1 := by
  rw [aBasisObservable, ← UnitaryTransport.conjOperator_mul, pauliZ_square]
  exact aBasisTransport.conjOperator_one

@[simp] theorem aBasisObservable_aZeroState :
    aBasisObservable aZeroState = aZeroState := by
  rw [← aBasisTransport_basis_zero]
  have hz : pauliZ (EuclideanSpace.basisFun (Fin 2) Complex 0) =
      EuclideanSpace.basisFun (Fin 2) Complex 0 := by
    ext bit
    fin_cases bit <;> simp
  rw [aBasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hz]

@[simp] theorem aBasisObservable_aOneState :
    aBasisObservable aOneState = -aOneState := by
  rw [← aBasisTransport_basis_one]
  have hz : pauliZ (EuclideanSpace.basisFun (Fin 2) Complex 1) =
      -(EuclideanSpace.basisFun (Fin 2) Complex 1) := by
    ext bit
    fin_cases bit <;> simp
  rw [aBasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hz, map_neg]

/-- The two literal spectral projectors of the source A-basis observable. -/
def aBasisProjector (outcome : StabilizerOutcome) : Operator QubitSpace :=
  (1 / 2 : Complex) •
    (1 + outcome.sign • aBasisObservable)

theorem aBasisProjector_adjoint (outcome : StabilizerOutcome) :
    LinearMap.adjoint (aBasisProjector outcome) = aBasisProjector outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold aBasisProjector
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
        exact aBasisObservable_adjoint

theorem aBasisProjector_idempotent (outcome : StabilizerOutcome) :
    aBasisProjector outcome * aBasisProjector outcome =
      aBasisProjector outcome := by
  cases outcome <;>
    simp only [aBasisProjector, StabilizerOutcome.sign,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      aBasisObservable_square] <;>
    module

theorem aBasisProjector_add :
    aBasisProjector .positive + aBasisProjector .negative = 1 := by
  simp only [aBasisProjector, StabilizerOutcome.sign]
  module

@[simp] theorem aBasisProjector_positive_aZeroState :
    aBasisProjector .positive aZeroState = aZeroState := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    one_smul, aBasisObservable_aZeroState]
  module

@[simp] theorem aBasisProjector_negative_aZeroState :
    aBasisProjector .negative aZeroState = 0 := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    aBasisObservable_aZeroState]
  module

@[simp] theorem aBasisProjector_positive_aOneState :
    aBasisProjector .positive aOneState = 0 := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    one_smul, aBasisObservable_aOneState]
  module

@[simp] theorem aBasisProjector_negative_aOneState :
    aBasisProjector .negative aOneState = aOneState := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    aBasisObservable_aOneState]
  module

@[simp] theorem aBasisProjector_positive_pauliZ_aZeroState :
    aBasisProjector .positive (pauliZ aZeroState) = 0 := by
  rw [← aOneState_eq_pauliZ]
  exact aBasisProjector_positive_aOneState

@[simp] theorem aBasisProjector_negative_pauliZ_aZeroState :
    aBasisProjector .negative (pauliZ aZeroState) = pauliZ aZeroState := by
  rw [← aOneState_eq_pauliZ]
  exact aBasisProjector_negative_aOneState

/-- The projective A-basis measurement with the result forgotten. -/
def aBasisDephasingKrausFamily :
    FiniteKrausFamily StabilizerOutcome QubitSpace QubitSpace where
  operator := aBasisProjector

theorem aBasisDephasingKrausFamily_complete :
    aBasisDephasingKrausFamily.Complete := by
  unfold FiniteKrausFamily.Complete
  simp only [aBasisDephasingKrausFamily, aBasisProjector_adjoint]
  change
    (∑ outcome : StabilizerOutcome,
      aBasisProjector outcome * aBasisProjector outcome) = 1
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide]
  simpa [aBasisProjector_idempotent] using aBasisProjector_add

/-- The actual A-basis dephasing channel. -/
def aBasisDephasing : QuantumChannel QubitSpace QubitSpace :=
  aBasisDephasingKrausFamily.toQuantumChannel
    aBasisDephasingKrausFamily_complete

/-- The same projective measurement with its A-basis outcome retained. -/
def aBasisInstrument :
    FiniteInstrument StabilizerOutcome StabilizerOutcome QubitSpace QubitSpace where
  kraus := aBasisDephasingKrausFamily
  observe := id

theorem aBasisInstrument_complete : aBasisInstrument.kraus.Complete :=
  aBasisDephasingKrausFamily_complete

theorem aBasisInstrument_weight_sum (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight .positive rho +
        aBasisInstrument.bornWeight .negative rho = 1 := by
  have h := aBasisInstrument.sum_bornWeight_eq_one
    aBasisInstrument_complete rho
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide] at h
  simpa using h

theorem aBasisInstrument_weight_nonneg (outcome : StabilizerOutcome)
    (rho : DensityOperator QubitSpace) :
    0 ≤ aBasisInstrument.bornWeight outcome rho :=
  aBasisInstrument.bornWeight_nonneg outcome rho

private theorem aBasis_sandwich_rankOne (outcome : StabilizerOutcome)
    (psi : QubitSpace) :
    (aBasisProjector outcome).comp
        ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
          (LinearMap.adjoint (aBasisProjector outcome))) =
      (InnerProductSpace.rankOne Complex
        (aBasisProjector outcome psi)
        (aBasisProjector outcome psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

theorem aZeroDensity_rankOne :
    aZeroDensity.toOperator =
      (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
  rw [aZeroDensity, phaseStateDensity_toOperator]
  rfl

theorem aOneDensity_rankOne :
    aOneDensity.toOperator =
      (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
  rw [aOneDensity, UnitaryTransport.conjDensity_toOperator,
    aZeroDensity, phaseStateDensity_toOperator]
  apply LinearMap.ext
  intro z
  simp [UnitaryTransport.conjOperator, InnerProductSpace.rankOne_apply]
  change inner Complex aZeroState (zTransport.toLinearEquiv.symm z) •
      zTransport aZeroState =
    inner Complex (zTransport aZeroState) z • zTransport aZeroState
  rw [← zTransport.map_inner]
  simp

private theorem aBasisInstrument_branchOperator_eq_sandwich
    (outcome : StabilizerOutcome) (A : Operator QubitSpace) :
    aBasisInstrument.branchOperator outcome A =
      (aBasisProjector outcome).comp
        (A.comp (LinearMap.adjoint (aBasisProjector outcome))) := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  rw [Fintype.sum_eq_single outcome]
  · simp [aBasisInstrument, aBasisDephasingKrausFamily]
  · intro other hne
    simp [aBasisInstrument, hne]

theorem aBasisInstrument_branch_aZero (outcome : StabilizerOutcome) :
    aBasisInstrument.branchOperator outcome aZeroDensity.toOperator =
      if outcome = .positive then aZeroDensity.toOperator else 0 := by
  rw [aBasisInstrument_branchOperator_eq_sandwich,
    aZeroDensity_rankOne, aBasis_sandwich_rankOne]
  cases outcome
  · simp only [aBasisProjector_positive_aZeroState, if_true]
  · simp only [aBasisProjector_negative_aZeroState]
    apply LinearMap.ext
    intro psi
    change inner Complex (0 : QubitSpace) psi • (0 : QubitSpace) = 0
    exact smul_zero _

private noncomputable def aBasisBranchLinearMap
    (outcome : StabilizerOutcome) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := aBasisInstrument.branchOperator outcome
  map_add' := by
    intro A B
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hobserve : aBasisInstrument.observe index = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply, map_add]
    · simp [hobserve]
  map_smul' := by
    intro scalar A
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hobserve : aBasisInstrument.observe index = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply]
    · simp [hobserve]

theorem aBasisInstrument_branch_aOne (outcome : StabilizerOutcome) :
    aBasisInstrument.branchOperator outcome aOneDensity.toOperator =
      if outcome = .negative then aOneDensity.toOperator else 0 := by
  rw [aBasisInstrument_branchOperator_eq_sandwich,
    aOneDensity_rankOne, aBasis_sandwich_rankOne]
  cases outcome
  · simp only [aBasisProjector_positive_aOneState]
    apply LinearMap.ext
    intro psi
    change inner Complex (0 : QubitSpace) psi • (0 : QubitSpace) = 0
    exact smul_zero _
  · simp only [aBasisProjector_negative_aOneState, if_true]

private theorem aBasisInstrument_aZero_weight (outcome : StabilizerOutcome) :
    aBasisInstrument.bornWeight outcome aZeroDensity =
      if outcome = .positive then 1 else 0 := by
  rw [FiniteInstrument.bornWeight, aBasisInstrument_branch_aZero]
  cases outcome
  · rw [if_pos rfl, aZeroDensity.trace_one]
    norm_num
  · have hne : (StabilizerOutcome.negative : StabilizerOutcome) ≠
        StabilizerOutcome.positive := by decide
    rw [if_neg hne, if_neg hne]
    norm_num

private theorem aBasisInstrument_aOne_weight (outcome : StabilizerOutcome) :
    aBasisInstrument.bornWeight outcome aOneDensity =
      if outcome = .negative then 1 else 0 := by
  rw [FiniteInstrument.bornWeight, aBasisInstrument_branch_aOne]
  cases outcome
  · have hne : (StabilizerOutcome.positive : StabilizerOutcome) ≠
        StabilizerOutcome.negative := by decide
    rw [if_neg hne, if_neg hne]
    norm_num
  · rw [if_pos rfl, aOneDensity.trace_one]
    norm_num

theorem aBasisInstrument_diagonalAResource_weight (p : ErrorParameter)
    (outcome : StabilizerOutcome) :
    aBasisInstrument.bornWeight outcome (diagonalAResource p) =
      if outcome = .positive then p.cleanWeight else p.rate := by
  rw [FiniteInstrument.bornWeight, diagonalAResource_toOperator]
  change Complex.re (LinearMap.trace Complex QubitSpace
    (aBasisBranchLinearMap outcome
      ((p.cleanWeight : Complex) • aZeroDensity.toOperator +
        (p.rate : Complex) • aOneDensity.toOperator))) = _
  rw [map_add, map_smul, map_smul]
  rw [map_add, map_smul, map_smul]
  change Complex.re
    ((p.cleanWeight : Complex) • LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator outcome aZeroDensity.toOperator) +
      (p.rate : Complex) • LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator outcome aOneDensity.toOperator)) = _
  rw [aBasisInstrument.trace_branchOperator_eq_bornWeight outcome aZeroDensity,
    aBasisInstrument.trace_branchOperator_eq_bornWeight outcome aOneDensity]
  rw [aBasisInstrument_aZero_weight, aBasisInstrument_aOne_weight]
  cases outcome <;> simp

/-- Dephasing is exactly the source random-`I/A` twirl. -/
theorem aBasisDephasing_apply (A : Operator QubitSpace) :
    aBasisDephasing A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) := by
  rw [aBasisDephasing, FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp only [aBasisDephasingKrausFamily, aBasisProjector_adjoint]
  change
    (∑ outcome : StabilizerOutcome,
      aBasisProjector outcome * (A * aBasisProjector outcome)) =
        (1 / 2 : Complex) •
          (A + aBasisObservable * (A * aBasisObservable))
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold aBasisProjector
  simp only [StabilizerOutcome.sign]
  simp only [one_smul, smul_mul_assoc, mul_smul_comm, mul_add, add_mul,
    one_mul, mul_one, neg_mul, mul_neg, neg_smul]
  module

/-- Source terminology: the random `I/A` twirl is the proved dephasing channel. -/
def aBasisTwirl : QuantumChannel QubitSpace QubitSpace :=
  aBasisDephasing

theorem aBasisTwirl_eq_dephasing : aBasisTwirl = aBasisDephasing :=
  rfl

theorem aBasisTwirl_apply (A : Operator QubitSpace) :
    aBasisTwirl A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) :=
  aBasisDephasing_apply A

/-- The error branch: ideal `T` followed by physical Pauli `Z`. -/
def zAfterTTransport : UnitaryTransport QubitSpace QubitSpace :=
  composeTransport zTransport idealTTransport

/-- The unscaled unitary selected by a one-site error bit. -/
def injectionBranchTransport (error : Fin 2) :
    UnitaryTransport QubitSpace QubitSpace :=
  if error = 0 then idealTTransport else zAfterTTransport

/-- The Bernoulli probability of one physical error bit. -/
def branchProbability (p : ErrorParameter) (error : Fin 2) : ℝ :=
  if error = 0 then p.cleanWeight else p.rate

theorem branchProbability_nonneg (p : ErrorParameter) (error : Fin 2) :
    0 ≤ branchProbability p error := by
  by_cases h : error = 0
  · simp [branchProbability, h, p.cleanWeight_nonneg]
  · simp [branchProbability, h, p.rate_nonneg]

theorem sum_branchProbability (p : ErrorParameter) :
    ∑ error : Fin 2, branchProbability p error = 1 := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp [branchProbability, p.cleanWeight_add_rate]

/-- The positive Kraus amplitude of one physical error bit. -/
def branchAmplitude (p : ErrorParameter) (error : Fin 2) : Complex :=
  (Real.sqrt (branchProbability p error) : Complex)

theorem branchAmplitude_normSq (p : ErrorParameter) (error : Fin 2) :
    star (branchAmplitude p error) * branchAmplitude p error =
      (branchProbability p error : Complex) := by
  rw [show star (branchAmplitude p error) = branchAmplitude p error by
    apply Complex.ext <;> simp [branchAmplitude]]
  change (Real.sqrt (branchProbability p error) : Complex) *
      (Real.sqrt (branchProbability p error) : Complex) =
    (branchProbability p error : Complex)
  rw [← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : Complex))
    (Real.mul_self_sqrt (branchProbability_nonneg p error))

theorem branchAmplitude_mul_star (p : ErrorParameter) (error : Fin 2) :
    branchAmplitude p error * star (branchAmplitude p error) =
      (branchProbability p error : Complex) := by
  rw [mul_comm, branchAmplitude_normSq]

/-- The two ideal unitary branches before Bernoulli scaling. -/
def injectionUnitaryFamily :
    FiniteKrausFamily (Fin 2) QubitSpace QubitSpace where
  operator error := (injectionBranchTransport error).toLinearEquiv.toLinearMap

theorem injectionUnitaryFamily_adjoint_comp (error : Fin 2) :
    (LinearMap.adjoint (injectionUnitaryFamily.operator error)).comp
        (injectionUnitaryFamily.operator error) = 1 := by
  change (LinearMap.adjoint
      (injectionBranchTransport error).toLinearEquiv.toLinearMap).comp
      (injectionBranchTransport error).toLinearEquiv.toLinearMap = 1
  rw [(injectionBranchTransport error).adjoint_toLinearMap]
  ext psi
  simp

/-- The actual one-resource noisy-`T` Kraus family. -/
def noisyTKrausFamily (p : ErrorParameter) :
    FiniteKrausFamily (Fin 2) QubitSpace QubitSpace :=
  injectionUnitaryFamily.scale (branchAmplitude p)

theorem noisyTKrausFamily_complete (p : ErrorParameter) :
    (noisyTKrausFamily p).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, branchAmplitude_normSq,
    injectionUnitaryFamily_adjoint_comp]
  ext psi site
  simp [branchProbability, ErrorParameter.cleanWeight]
  ring

/-- The actual one-resource noisy-`T` channel. -/
def noisyTChannel (p : ErrorParameter) : QuantumChannel QubitSpace QubitSpace :=
  (noisyTKrausFamily p).toQuantumChannel (noisyTKrausFamily_complete p)

/-- The injection consumes exactly one noisy A-basis resource. -/
def resourceConsumption : Nat := 1

theorem resourceConsumption_eq_one : resourceConsumption = 1 :=
  rfl

/-- Exact ideal-`T`-then-`Z` mixture on every input operator. -/
theorem noisyTChannel_apply (p : ErrorParameter) (A : Operator QubitSpace) :
    noisyTChannel p A =
      (p.cleanWeight : Complex) •
          idealTTransport.conjOperator A +
        (p.rate : Complex) •
          zTransport.conjOperator (idealTTransport.conjOperator A) := by
  rw [noisyTChannel, FiniteKrausFamily.toQuantumChannel_apply_sum]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, noisyTKrausFamily, FiniteKrausFamily.scale_operator]
  rw [show branchAmplitude p 0 • injectionUnitaryFamily.operator 0 =
      branchAmplitude p 0 • idealTTransport.toLinearEquiv.toLinearMap by rfl]
  rw [show branchAmplitude p 1 • injectionUnitaryFamily.operator 1 =
      branchAmplitude p 1 • zAfterTTransport.toLinearEquiv.toLinearMap by rfl]
  have hadjointTransport (amplitude : Complex)
      (U : UnitaryTransport QubitSpace QubitSpace) :
      LinearMap.adjoint (amplitude • U.toLinearEquiv.toLinearMap) =
        star amplitude • LinearMap.adjoint U.toLinearEquiv.toLinearMap := by
    exact map_smulₛₗ
      (LinearMap.adjoint :
        (QubitSpace →ₗ[Complex] QubitSpace) ≃ₗ⋆[Complex]
          (QubitSpace →ₗ[Complex] QubitSpace))
      amplitude U.toLinearEquiv.toLinearMap
  rw [hadjointTransport (branchAmplitude p 0) idealTTransport,
    hadjointTransport (branchAmplitude p 1) zAfterTTransport]
  rw [idealTTransport.adjoint_toLinearMap,
    zAfterTTransport.adjoint_toLinearMap]
  ext psi
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, smul_smul]
  rw [branchAmplitude_normSq p 0, branchAmplitude_normSq p 1]
  simp [UnitaryTransport.conjOperator, zAfterTTransport, composeTransport,
    branchProbability, LinearMap.comp_apply]

@[simp] theorem noisyTChannel_mapDensity_toOperator
    (p : ErrorParameter) (rho : DensityOperator QubitSpace) :
    ((noisyTChannel p).mapDensity rho).toOperator =
      (p.cleanWeight : Complex) •
          idealTTransport.conjOperator rho.toOperator +
        (p.rate : Complex) •
          zTransport.conjOperator
            (idealTTransport.conjOperator rho.toOperator) := by
  exact noisyTChannel_apply p rho.toOperator

end OneQubit

section Register

variable {Index : Type u} [Fintype Index] [DecidableEq Index]

/-- Independent Bernoulli weight of one physical `Z`-error word. -/
def errorWordProbability (p : ErrorParameter)
    (error : Word (ZMod 2) Index) : ℝ :=
  ∏ site, if error site = 0 then p.cleanWeight else p.rate

/-- The independent physical word law is the Bernoulli monomial determined by
the literal Hamming support, rather than a stored weight-enumerator value. -/
theorem errorWordProbability_eq_hammingWeight (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    errorWordProbability p error =
      p.rate ^ HammingWeight error *
        p.cleanWeight ^ (Fintype.card Index - HammingWeight error) := by
  classical
  let support := hammingSupport error
  have hdisjoint : Disjoint support (Finset.univ \ support) := by
    exact Finset.disjoint_sdiff
  have hunion : support ∪ (Finset.univ \ support) = Finset.univ := by
    simp
  have hsupp_card : support.card = HammingWeight error := by
    rfl
  have hcompl_card : (Finset.univ \ support).card =
      Fintype.card Index - HammingWeight error := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ support),
      Finset.card_univ, hsupp_card]
  calc
    errorWordProbability p error =
        (∏ site ∈ support, if error site = 0 then p.cleanWeight else p.rate) *
          (∏ site ∈ Finset.univ \ support,
            if error site = 0 then p.cleanWeight else p.rate) := by
      rw [errorWordProbability, ← Finset.prod_union hdisjoint, hunion]
    _ = (∏ _site ∈ support, p.rate) *
          ∏ _site ∈ Finset.univ \ support, p.cleanWeight := by
      congr 1
      · apply Finset.prod_congr rfl
        intro site hsite
        have hnonzero : error site ≠ 0 := by
          simpa [support, hammingSupport] using hsite
        simp [hnonzero]
      · apply Finset.prod_congr rfl
        intro site hsite
        have hzero : error site = 0 := by
          by_contra hnonzero
          exact (Finset.mem_sdiff.mp hsite).2
            (by simp [support, hammingSupport, hnonzero])
        simp [hzero]
    _ = p.rate ^ HammingWeight error *
          p.cleanWeight ^ (Fintype.card Index - HammingWeight error) := by
      simp [hsupp_card, hcompl_card]

omit [DecidableEq Index] in
theorem errorWordProbability_nonneg (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    0 ≤ errorWordProbability p error := by
  exact Finset.prod_nonneg fun site _ => by
    by_cases h : error site = 0
    · simp [h, p.cleanWeight_nonneg]
    · simp [h, p.rate_nonneg]

/-- The independent word probabilities sum to one. -/
theorem sum_errorWordProbability (p : ErrorParameter) :
    ∑ error : Word (ZMod 2) Index, errorWordProbability p error = 1 := by
  classical
  have h := Finset.sum_prod_piFinset
    (R := ℝ) (ι := Index) (κ := ZMod 2)
    (s := Finset.univ)
    (g := fun _ bit => if bit = 0 then p.cleanWeight else p.rate)
  have hbit :
      ∑ bit : ZMod 2, (if bit = 0 then p.cleanWeight else p.rate) = 1 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simp [p.cleanWeight_add_rate]
  rw [hbit] at h
  simpa [errorWordProbability] using h

/-- The physical branch applies all ideal `T` gates and then the selected `Z` word. -/
def registerBranchOperator (error : Word (ZMod 2) Index) :
    Operator (Qubit.QubitRegister Index) :=
  (toQubitOperator (cssZCheck error)).comp
    (allSiteT (Index := Index)).toLinearEquiv.toLinearMap

theorem registerBranchOperator_adjoint
    (error : Word (ZMod 2) Index) :
    LinearMap.adjoint (registerBranchOperator error) =
      (allSiteT (Index := Index)).toLinearEquiv.symm.toLinearMap.comp
        (toQubitOperator (cssZCheck error)) := by
  rw [registerBranchOperator, LinearMap.adjoint_comp,
    (allSiteT (Index := Index)).adjoint_toLinearMap,
    adjoint_toQubitOperator_eq_binaryDagger]
  simp

theorem registerBranchOperator_adjoint_comp
    (error : Word (ZMod 2) Index) :
    (LinearMap.adjoint (registerBranchOperator error)).comp
        (registerBranchOperator error) = 1 := by
  let T := (allSiteT (Index := Index)).toLinearEquiv.toLinearMap
  let Z := toQubitOperator (cssZCheck error)
  change (LinearMap.adjoint (Z.comp T)).comp (Z.comp T) = 1
  rw [LinearMap.adjoint_comp]
  calc
    ((LinearMap.adjoint T).comp (LinearMap.adjoint Z)).comp (Z.comp T) =
        (LinearMap.adjoint T).comp
          (((LinearMap.adjoint Z).comp Z).comp T) := by
      ext psi
      rfl
    _ = (LinearMap.adjoint T).comp T := by
      rw [show (LinearMap.adjoint Z).comp Z = 1 by
        exact toQubitOperator_adjoint_comp_self (cssZCheck error)]
      ext psi
      rfl
    _ = 1 := by
      dsimp [T]
      rw [(allSiteT (Index := Index)).adjoint_toLinearMap]
      ext psi
      simp

/-- Positive square-root amplitude of an independent physical error word. -/
def errorWordAmplitude (p : ErrorParameter)
    (error : Word (ZMod 2) Index) : Complex :=
  (Real.sqrt (errorWordProbability p error) : Complex)

omit [DecidableEq Index] in
theorem errorWordAmplitude_normSq (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    star (errorWordAmplitude p error) * errorWordAmplitude p error =
      (errorWordProbability p error : Complex) := by
  rw [show star (errorWordAmplitude p error) = errorWordAmplitude p error by
    apply Complex.ext <;> simp [errorWordAmplitude]]
  change (Real.sqrt (errorWordProbability p error) : Complex) *
      (Real.sqrt (errorWordProbability p error) : Complex) =
    (errorWordProbability p error : Complex)
  rw [← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : Complex))
    (Real.mul_self_sqrt (errorWordProbability_nonneg p error))

omit [DecidableEq Index] in
theorem errorWordAmplitude_mul_star (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    errorWordAmplitude p error * star (errorWordAmplitude p error) =
      (errorWordProbability p error : Complex) := by
  rw [mul_comm, errorWordAmplitude_normSq]

/-- Every physical error word as an unscaled unitary Kraus branch. -/
def registerUnitaryFamily :
    FiniteKrausFamily (Word (ZMod 2) Index)
      (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) where
  operator := registerBranchOperator

/-- The genuine independent finite-register noisy-`T` Kraus family. -/
def independentNoisyTKrausFamily (p : ErrorParameter) :
    FiniteKrausFamily (Word (ZMod 2) Index)
      (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  registerUnitaryFamily.scale (errorWordAmplitude p)

theorem independentNoisyTKrausFamily_complete (p : ErrorParameter) :
    (independentNoisyTKrausFamily (Index := Index) p).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
  simp_rw [errorWordAmplitude_normSq, registerUnitaryFamily,
    registerBranchOperator_adjoint_comp]
  rw [← Finset.sum_smul]
  have hsum :
      ∑ error : Word (ZMod 2) Index,
        (errorWordProbability p error : Complex) = 1 := by
    exact_mod_cast sum_errorWordProbability (Index := Index) p
  rw [hsum]
  simp

/-- The actual independent noisy-`T` channel on a finite physical register. -/
def independentNoisyTChannel (p : ErrorParameter) :
    QuantumChannel (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  (independentNoisyTKrausFamily (Index := Index) p).toQuantumChannel
    (independentNoisyTKrausFamily_complete p)

/-- The independent channel has one literal Kraus branch per physical error word. -/
theorem independentNoisyTChannel_apply (p : ErrorParameter)
    (A : Operator (Qubit.QubitRegister Index)) :
    independentNoisyTChannel (Index := Index) p A =
      ∑ error : Word (ZMod 2) Index,
        (errorWordProbability p error : Complex) •
          (toQubitOperator (cssZCheck error)).comp
            ((allSiteT (Index := Index)).conjOperator A |>.comp
              (toQubitOperator (cssZCheck error))) := by
  rw [independentNoisyTChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro error _
  rw [independentNoisyTKrausFamily, FiniteKrausFamily.scale_operator]
  have hadjoint :
      LinearMap.adjoint
          (errorWordAmplitude p error • registerUnitaryFamily.operator error) =
        star (errorWordAmplitude p error) •
          LinearMap.adjoint (registerUnitaryFamily.operator error) := by
    exact map_smulₛₗ
      (LinearMap.adjoint :
        (Qubit.QubitRegister Index →ₗ[Complex] Qubit.QubitRegister Index) ≃ₗ⋆[Complex]
          (Qubit.QubitRegister Index →ₗ[Complex] Qubit.QubitRegister Index))
      (errorWordAmplitude p error) (registerUnitaryFamily.operator error)
  rw [hadjoint]
  rw [show LinearMap.adjoint (registerUnitaryFamily.operator error) =
      (allSiteT (Index := Index)).toLinearEquiv.symm.toLinearMap.comp
        (toQubitOperator (cssZCheck error)) by
    exact registerBranchOperator_adjoint error]
  ext psi
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
  rw [errorWordAmplitude_normSq]
  simp [registerUnitaryFamily, registerBranchOperator,
    UnitaryTransport.conjOperator, LinearMap.comp_apply]

end Register

end BH12NoisyInjection
end Triorthogonal
end Distillation
end QEC
