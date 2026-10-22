import QEC.Semantics.Channels.TraceNorm
import QEC.Semantics.Channels.Kraus
import QEC.Semantics.Dynamics.LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite-dimensional Lindblad evolution

This module constructs a jump-form Lindblad dissipator and Hamiltonian
commutator on the repository's concrete finite operator space.  The evolution
is the Banach-algebra exponential of the transported superoperator; identity,
semigroup, trace, positivity, and differential properties are proved from
that construction rather than stored in a dynamics structure.
-/

universe u v

namespace QEC.Semantics

open scoped BigOperators ComplexOrder

noncomputable section

variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

noncomputable local instance finiteQuantumSystemComplete : CompleteSpace H :=
  FiniteDimensional.complete Complex H

/-- Continuous representatives of finite-dimensional operators. -/
abbrev ContinuousOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] := H →L[Complex] H

/-- The normed algebra in which the superoperator exponential is formed. -/
abbrev ContinuousSuperoperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] :=
  ContinuousOperator H →L[Complex] ContinuousOperator H

/-- Project-facing linear superoperators on finite operators. -/
abbrev Superoperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] :=
  Operator H →ₗ[Complex] Operator H

/-- Left multiplication as a continuous regular representation. -/
noncomputable def continuousLeftRegularRepresentation :
    ContinuousOperator H →+* ContinuousSuperoperator H where
  toFun X := ContinuousLinearMap.mulLeftRight Complex (ContinuousOperator H) X 1
  map_zero' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((0 : ContinuousOperator H) * A * 1) x) = 0
    simp
  map_one' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((1 : ContinuousOperator H) * A * 1) x) = A x
    simp
  map_add' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((X + Y) * A * 1) x) = ((X * A * 1 + Y * A * 1) x)
    simp [add_mul]
  map_mul' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change (((X * Y) * A * 1) x) = (X * (Y * A * 1) * 1) x
    simp [mul_assoc]

/-- Right multiplication, expressed as a representation of the opposite
operator algebra so that composition has the correct order. -/
noncomputable def continuousRightRegularRepresentation :
    (ContinuousOperator H)ᵐᵒᵖ →+* ContinuousSuperoperator H where
  toFun X := ContinuousLinearMap.mulLeftRight Complex (ContinuousOperator H)
    1 (MulOpposite.unop X)
  map_zero' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (0 : ContinuousOperator H)) x) = 0
    simp
  map_one' := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (1 : ContinuousOperator H)) x) = A x
    simp
  map_add' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (MulOpposite.unop X + MulOpposite.unop Y)) x) =
      ((1 * A * MulOpposite.unop X + 1 * A * MulOpposite.unop Y) x)
    simp [mul_add]
  map_mul' X Y := by
    apply ContinuousLinearMap.ext; intro A
    apply ContinuousLinearMap.ext; intro x
    change ((1 * A * (MulOpposite.unop Y * MulOpposite.unop X)) x) =
      (1 * (1 * A * MulOpposite.unop Y) * MulOpposite.unop X) x
    simp [mul_assoc]

@[simp]
theorem continuousLeftRegularRepresentation_apply
    (X A : ContinuousOperator H) :
    continuousLeftRegularRepresentation (H := H) X A = X * A := by
  rfl

@[simp]
theorem continuousRightRegularRepresentation_apply
    (X : (ContinuousOperator H)ᵐᵒᵖ) (A : ContinuousOperator H) :
    continuousRightRegularRepresentation (H := H) X A =
      A * MulOpposite.unop X := by
  rfl

theorem continuous_continuousLeftRegularRepresentation :
    Continuous (continuousLeftRegularRepresentation (H := H)) := by
  exact (continuous_const.clm_apply continuous_id).clm_apply continuous_const

theorem continuous_continuousRightRegularRepresentation :
    Continuous (continuousRightRegularRepresentation (H := H)) := by
  exact (continuous_const.clm_apply continuous_const).clm_apply
    MulOpposite.continuous_unop

theorem exp_continuousLeftRegularRepresentation (X : ContinuousOperator H) :
    NormedSpace.exp (continuousLeftRegularRepresentation (H := H) X) =
      continuousLeftRegularRepresentation (H := H) (NormedSpace.exp X) := by
  exact (NormedSpace.map_exp_of_mem_ball
    (continuousLeftRegularRepresentation (H := H))
    continuous_continuousLeftRegularRepresentation X
    ((NormedSpace.expSeries_radius_eq_top Complex (ContinuousOperator H)).symm ▸
      edist_lt_top _ _)).symm

theorem exp_continuousRightRegularRepresentation (X : ContinuousOperator H) :
    NormedSpace.exp
        (continuousRightRegularRepresentation (H := H) (MulOpposite.op X)) =
      continuousRightRegularRepresentation (H := H)
        (MulOpposite.op (NormedSpace.exp X)) := by
  calc
    NormedSpace.exp
        (continuousRightRegularRepresentation (H := H) (MulOpposite.op X)) =
        continuousRightRegularRepresentation (H := H)
          (NormedSpace.exp (MulOpposite.op X)) :=
      (NormedSpace.map_exp_of_mem_ball
        (continuousRightRegularRepresentation (H := H))
        continuous_continuousRightRegularRepresentation (MulOpposite.op X)
        ((NormedSpace.expSeries_radius_eq_top Complex
          ((ContinuousOperator H)ᵐᵒᵖ)).symm ▸ edist_lt_top _ _)).symm
    _ = continuousRightRegularRepresentation (H := H)
        (MulOpposite.op (NormedSpace.exp X)) := by rw [NormedSpace.exp_op]

theorem commute_continuousRegularRepresentations
    (X Y : ContinuousOperator H) :
    Commute (continuousLeftRegularRepresentation (H := H) X)
      (continuousRightRegularRepresentation (H := H) (MulOpposite.op Y)) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change (X * (A * Y)) x = ((X * A) * Y) x
  simp [mul_assoc]

/-- Adjoint as a real continuous-linear map, used to commute it with real-time integrals. -/
noncomputable def continuousOperatorAdjointReal :
    ContinuousOperator H →L[Real] ContinuousOperator H where
  toFun := ContinuousLinearMap.adjoint
  map_add' A B := by
    exact ContinuousLinearMap.adjoint.map_add A B
  map_smul' r A := by
    change ContinuousLinearMap.adjoint ((r : Complex) • A) =
      (r : Complex) • ContinuousLinearMap.adjoint A
    rw [map_smulₛₗ]
    have hr : (starRingEnd Complex) (r : Complex) = (r : Complex) := by
      apply Complex.ext <;> simp
    rw [hr]
  cont := ContinuousLinearMap.adjoint.continuous

/-- A real continuous-linear map commutes with Bochner interval integration. -/
theorem intervalIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    (L : E →L[Real] F) (f : Real → E) (a b : Real)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ x in a..b, L (f x)) = L (∫ x in a..b, f x) := by
  simp only [intervalIntegral]
  rw [L.integral_comp_comm hf.1, L.integral_comp_comm hf.2]
  rw [map_sub]

/-- One Schrödinger-picture Lindblad jump term. -/
def lindbladJumpTerm (J : Operator H) : Superoperator H where
  toFun A := J * A * LinearMap.adjoint J -
    (2 : Complex)⁻¹ •
      ((LinearMap.adjoint J * J) * A + A * (LinearMap.adjoint J * J))
  map_add' A B := by
    ext x
    simp [mul_add, add_mul]
    module
  map_smul' c A := by
    ext x
    simp
    module

theorem lindbladJumpTerm_apply (J A : Operator H) :
    lindbladJumpTerm J A = J * A * LinearMap.adjoint J -
      (2 : Complex)⁻¹ •
        ((LinearMap.adjoint J * J) * A + A * (LinearMap.adjoint J * J)) :=
  rfl

/-- The finite sum of jump terms. -/
def lindbladDissipator [Fintype ι]
    (J : ι → Operator H) : Superoperator H :=
  ∑ a, lindbladJumpTerm (J a)

theorem lindbladDissipator_apply [Fintype ι]
    (J : ι → Operator H) (A : Operator H) :
    lindbladDissipator J A = ∑ a, lindbladJumpTerm (J a) A := by
  simp [lindbladDissipator]

/-- The completely positive gain part of the jump generator. -/
def lindbladJumpGain [Fintype ι] (J : ι → Operator H) : Superoperator H where
  toFun A := ∑ a, J a * A * LinearMap.adjoint (J a)
  map_add' A B := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext x
    simp
    simp only [Finset.smul_sum]

theorem lindbladJumpGain_apply [Fintype ι]
    (J : ι → Operator H) (A : Operator H) :
    lindbladJumpGain J A = ∑ a, J a * A * LinearMap.adjoint (J a) :=
  rfl

/-- The jump operators regarded as the repository's concrete Kraus family. -/
def lindbladJumpKrausFamily [Fintype ι]
    (J : ι → Operator H) : FiniteKrausFamily ι H H where
  operator := J

theorem lindbladJumpGain_eq_inducedMap [Fintype ι] (J : ι → Operator H) :
    lindbladJumpGain J = (lindbladJumpKrausFamily J).inducedMap := by
  ext A x
  simp [lindbladJumpGain, lindbladJumpKrausFamily,
    FiniteKrausFamily.inducedMap_apply, mul_assoc]

theorem lindbladJumpGain_completelyPositive [Fintype ι] (J : ι → Operator H) :
    CompletelyPositive (lindbladJumpGain J) := by
  rw [lindbladJumpGain_eq_inducedMap]
  exact (lindbladJumpKrausFamily J).inducedMap_completelyPositive

/-- Conjugation by one (not necessarily unitary) operator. -/
def singleKrausMap (V : Operator H) : Superoperator H where
  toFun A := V * A * LinearMap.adjoint V
  map_add' A B := by
    ext x
    simp [mul_add]
  map_smul' c A := by
    ext x
    simp

/-- A single operator as a Kraus family indexed by `Unit`. -/
def singleKrausFamily (V : Operator H) : FiniteKrausFamily Unit H H where
  operator _ := V

theorem singleKrausMap_eq_inducedMap (V : Operator H) :
    singleKrausMap V = (singleKrausFamily V).inducedMap := by
  ext A x
  simp [singleKrausMap, singleKrausFamily,
    FiniteKrausFamily.inducedMap_apply, mul_assoc]

theorem singleKrausMap_completelyPositive (V : Operator H) :
    CompletelyPositive (singleKrausMap V) := by
  rw [singleKrausMap_eq_inducedMap]
  exact (singleKrausFamily V).inducedMap_completelyPositive

namespace CompletelyPositive

variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem add {Φ Ψ : Operator H →ₗ[Complex] Operator K}
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ) :
    CompletelyPositive (Φ + Ψ) := by
  intro n M hM
  constructor
  · intro i j
    simp only [OperatorMatrix.map, LinearMap.add_apply, map_add]
    exact congrArg₂ (· + ·) ((hΦ n M hM).1 i j) ((hΨ n M hM).1 i j)
  · intro x
    have hp := (hΦ n M hM).2 x
    have hq := (hΨ n M hM).2 x
    simpa only [OperatorMatrix.map, LinearMap.add_apply, inner_add_left,
      Complex.add_re, Finset.sum_add_distrib] using add_nonneg hp hq

theorem comp {Φ : Operator H →ₗ[Complex] Operator K}
    {Ψ : Operator K →ₗ[Complex] Operator L}
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ) :
    CompletelyPositive (Ψ.comp Φ) := by
  intro n M hM
  exact hΨ n (OperatorMatrix.map Φ M) (hΦ n M hM)

theorem nonneg_smul (c : Real) (hc : 0 ≤ c)
    {Φ : Operator H →ₗ[Complex] Operator K}
    (hΦ : CompletelyPositive Φ) :
    CompletelyPositive ((c : Complex) • Φ) := by
  intro n M hM
  constructor
  · intro i j
    simp only [OperatorMatrix.map, LinearMap.smul_apply, map_smulₛₗ]
    have hcstar : (starRingEnd Complex) (c : Complex) = (c : Complex) := by
      apply Complex.ext <;> simp
    rw [hcstar]
    exact congrArg ((c : Complex) • ·) ((hΦ n M hM).1 i j)
  · intro x
    have hp := (hΦ n M hM).2 x
    have hnonneg : 0 ≤ c * Complex.re
        (∑ i : Fin n, ∑ j : Fin n, inner Complex (Φ (M i j) (x j)) (x i)) :=
      mul_nonneg hc hp
    simp only [OperatorMatrix.map, LinearMap.smul_apply, inner_smul_left]
    have hcstar : (starRingEnd Complex) (c : Complex) = (c : Complex) := by
      apply Complex.ext <;> simp
    rw [hcstar]
    have heq :
        (∑ i : Fin n, ∑ j : Fin n,
          (c : Complex) * inner Complex (Φ (M i j) (x j)) (x i)) =
        (c : Complex) * (∑ i : Fin n, ∑ j : Fin n,
          inner Complex (Φ (M i j) (x j)) (x i)) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    rw [heq]
    simpa only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hnonneg

theorem zero :
    CompletelyPositive (0 : Operator H →ₗ[Complex] Operator K) := by
  intro n M hM
  constructor
  · intro i j
    simp [OperatorMatrix.map]
  · intro x
    simp [OperatorMatrix.map]

theorem sum_finset {κ : Type*} (s : Finset κ)
    {Φ : κ → Operator H →ₗ[Complex] Operator K}
    (hΦ : ∀ i ∈ s, CompletelyPositive (Φ i)) :
    CompletelyPositive (∑ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (H := H) (K := K))
  | @insert a s ha induction =>
      rw [Finset.sum_insert ha]
      exact add (hΦ a (Finset.mem_insert_self a s))
        (induction fun i hi => hΦ i (Finset.mem_insert_of_mem hi))

theorem sum {κ : Type*} [Fintype κ]
    {Φ : κ → Operator H →ₗ[Complex] Operator K}
    (hΦ : ∀ i, CompletelyPositive (Φ i)) :
    CompletelyPositive (∑ i, Φ i) := by
  classical
  exact sum_finset Finset.univ fun i _hi => hΦ i

end CompletelyPositive

/-- The Hamiltonian contribution `-i[H, ·]`. -/
def hamiltonianCommutator (hamiltonian : Operator H) : Superoperator H where
  toFun A := (-Complex.I) • (hamiltonian * A - A * hamiltonian)
  map_add' A B := by
    ext x
    simp [mul_add, add_mul]
    module
  map_smul' c A := by
    ext x
    simp
    module

theorem hamiltonianCommutator_apply (hamiltonian A : Operator H) :
    hamiltonianCommutator hamiltonian A =
      (-Complex.I) • (hamiltonian * A - A * hamiltonian) :=
  rfl

/-- The full finite Lindblad generator. -/
def finiteLindbladGenerator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) : Superoperator H :=
  hamiltonianCommutator hamiltonian + lindbladDissipator J

/-- The positive loss operator `sum_a J_a† J_a`. -/
def lindbladLossOperator [Fintype ι] (J : ι → Operator H) : Operator H :=
  ∑ a, LinearMap.adjoint (J a) * J a

/-- The effective non-Hermitian Hamiltonian for no-jump evolution. -/
def lindbladEffectiveOperator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) : Operator H :=
  (-Complex.I) • hamiltonian -
    (2 : Complex)⁻¹ • lindbladLossOperator J

/-- The no-jump drift `K A + A K†`. -/
def lindbladNoJumpDrift (K : Operator H) : Superoperator H where
  toFun A := K * A + A * LinearMap.adjoint K
  map_add' A B := by
    ext x
    simp [mul_add, add_mul]
    module
  map_smul' c A := by
    ext x
    simp

theorem lindbladNoJumpDrift_apply (K A : Operator H) :
    lindbladNoJumpDrift K A = K * A + A * LinearMap.adjoint K :=
  rfl

theorem adjoint_lindbladLossOperator [Fintype ι] (J : ι → Operator H) :
    LinearMap.adjoint (lindbladLossOperator J) = lindbladLossOperator J := by
  classical
  rw [lindbladLossOperator, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, ← Module.End.mul_eq_comp]

theorem adjoint_lindbladEffectiveOperator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric) :
    LinearMap.adjoint (lindbladEffectiveOperator hamiltonian J) =
      Complex.I • hamiltonian -
        (2 : Complex)⁻¹ • lindbladLossOperator J := by
  rw [lindbladEffectiveOperator]
  rw [map_sub]
  rw [map_smulₛₗ, map_smulₛₗ]
  rw [hhamiltonian.adjoint_eq, adjoint_lindbladLossOperator]
  have htwo : (starRingEnd Complex) ((2 : Complex)⁻¹) = (2 : Complex)⁻¹ := by
    apply Complex.ext <;> norm_num
  have hI : (starRingEnd Complex) (-Complex.I) = Complex.I := by
    apply Complex.ext <;> norm_num
  rw [hI]
  rw [htwo]

theorem lindbladNoJumpDrift_effective_apply [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric) (A : Operator H) :
    lindbladNoJumpDrift (lindbladEffectiveOperator hamiltonian J) A =
      lindbladEffectiveOperator hamiltonian J * A +
        A * (Complex.I • hamiltonian -
          (2 : Complex)⁻¹ • lindbladLossOperator J) := by
  rw [lindbladNoJumpDrift_apply,
    adjoint_lindbladEffectiveOperator hamiltonian J hhamiltonian]

theorem finiteLindbladGenerator_eq_noJump_add_gain [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric) :
    finiteLindbladGenerator hamiltonian J =
      lindbladNoJumpDrift (lindbladEffectiveOperator hamiltonian J) +
        lindbladJumpGain J := by
  classical
  ext A x
  simp only [finiteLindbladGenerator, LinearMap.add_apply]
  rw [lindbladNoJumpDrift_effective_apply hamiltonian J hhamiltonian]
  simp only [hamiltonianCommutator_apply, lindbladDissipator_apply,
    lindbladJumpTerm_apply, lindbladJumpGain_apply,
    lindbladEffectiveOperator, lindbladLossOperator]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_eq_comp, LinearMap.comp_apply, LinearMap.sum_apply]
  simp only [map_sub, map_smul, map_sum]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_add_distrib]
  module

/-- Adjoint commutes with the Banach-algebra exponential on finite operators. -/
theorem continuousOperator_adjoint_exp (A : ContinuousOperator H) :
    ContinuousLinearMap.adjoint (NormedSpace.exp A) =
      NormedSpace.exp (ContinuousLinearMap.adjoint A) := by
  change star (NormedSpace.exp A) = NormedSpace.exp (star A)
  exact NormedSpace.star_exp A

/-- The nonunitary propagator `exp(t K)` of a no-jump trajectory. -/
noncomputable def lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) : ContinuousOperator H :=
  NormedSpace.exp ((t : Complex) • LinearMap.toContinuousLinearMap K)

/-- Project-facing linear representative of the no-jump propagator. -/
noncomputable def lindbladNoJumpPropagator
    (K : Operator H) (t : Real) : Operator H :=
  (lindbladNoJumpPropagatorContinuous K t).toLinearMap

/-- A no-jump time slice as a single-Kraus completely positive map. -/
noncomputable def lindbladNoJumpEvolutionLinearMap
    (K : Operator H) (t : Real) : Superoperator H :=
  singleKrausMap (lindbladNoJumpPropagator K t)

theorem lindbladNoJumpEvolutionLinearMap_completelyPositive
    (K : Operator H) (t : Real) :
    CompletelyPositive (lindbladNoJumpEvolutionLinearMap K t) :=
  singleKrausMap_completelyPositive (lindbladNoJumpPropagator K t)

@[simp]
theorem lindbladNoJumpPropagatorContinuous_zero (K : Operator H) :
    lindbladNoJumpPropagatorContinuous K 0 = 1 := by
  unfold lindbladNoJumpPropagatorContinuous
  have hz : ((0 : Real) : Complex) • LinearMap.toContinuousLinearMap K = 0 := by
    simp
  rw [hz, NormedSpace.exp_zero]

@[simp]
theorem lindbladNoJumpPropagator_zero (K : Operator H) :
    lindbladNoJumpPropagator K 0 = 1 := by
  unfold lindbladNoJumpPropagator
  rw [lindbladNoJumpPropagatorContinuous_zero]
  rfl

@[simp]
theorem lindbladNoJumpEvolutionLinearMap_zero (K : Operator H) :
    lindbladNoJumpEvolutionLinearMap K 0 = LinearMap.id := by
  ext A x
  simp [lindbladNoJumpEvolutionLinearMap, singleKrausMap,
    lindbladNoJumpPropagator_zero]

theorem hasDerivAt_lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) :
    HasDerivAt (lindbladNoJumpPropagatorContinuous K)
      (lindbladNoJumpPropagatorContinuous K t *
        LinearMap.toContinuousLinearMap K) t := by
  let _ : NormedAlgebra Real (ContinuousOperator H) :=
    NormedAlgebra.restrictScalars Real Complex (ContinuousOperator H)
  change HasDerivAt
    (fun s : Real => NormedSpace.exp (s • LinearMap.toContinuousLinearMap K))
    (NormedSpace.exp (t • LinearMap.toContinuousLinearMap K) *
      LinearMap.toContinuousLinearMap K) t
  exact hasDerivAt_exp_smul_const (LinearMap.toContinuousLinearMap K) t

theorem adjoint_lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) :
    ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) =
      NormedSpace.exp ((t : Complex) •
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) := by
  unfold lindbladNoJumpPropagatorContinuous
  rw [continuousOperator_adjoint_exp]
  rw [map_smulₛₗ]
  have ht : (starRingEnd Complex) (t : Complex) = (t : Complex) := by
    apply Complex.ext <;> simp
  rw [ht]

theorem hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous
    (K : Operator H) (t : Real) :
    HasDerivAt
      (fun s : Real =>
        ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K s))
      (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) *
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t := by
  rw [show (fun s : Real =>
      ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K s)) =
      (fun s : Real => NormedSpace.exp ((s : Complex) •
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) by
    funext s
    exact adjoint_lindbladNoJumpPropagatorContinuous K s]
  let _ : NormedAlgebra Real (ContinuousOperator H) :=
    NormedAlgebra.restrictScalars Real Complex (ContinuousOperator H)
  rw [adjoint_lindbladNoJumpPropagatorContinuous]
  change HasDerivAt
    (fun s : Real => NormedSpace.exp
      (s • ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)))
    (NormedSpace.exp (t • ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) *
      ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t
  exact hasDerivAt_exp_smul_const
    (ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t

/-- The continuous-operator form of a single no-jump trajectory. -/
noncomputable def lindbladNoJumpTrajectoryContinuous
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    ContinuousOperator H :=
  lindbladNoJumpPropagatorContinuous K t * A *
    ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t)

theorem hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    HasDerivAt (lindbladNoJumpTrajectoryContinuous K A)
      (((lindbladNoJumpPropagatorContinuous K t *
          LinearMap.toContinuousLinearMap K) * A) *
          ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) +
        (lindbladNoJumpPropagatorContinuous K t * A) *
          (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t) *
            ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) t := by
  exact ((hasDerivAt_lindbladNoJumpPropagatorContinuous K t).mul_const A).mul
    (hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous K t)

theorem continuousOperator_commute_lindbladNoJumpPropagator
    (K : Operator H) (t : Real) :
    Commute (LinearMap.toContinuousLinearMap K)
      (lindbladNoJumpPropagatorContinuous K t) := by
  unfold lindbladNoJumpPropagatorContinuous
  exact ((Commute.refl (LinearMap.toContinuousLinearMap K)).smul_right
    (t : Complex)).exp_right

theorem hasDerivAt_lindbladNoJumpTrajectoryContinuous
    (K : Operator H) (A : ContinuousOperator H) (t : Real) :
    HasDerivAt (lindbladNoJumpTrajectoryContinuous K A)
      (LinearMap.toContinuousLinearMap K *
          lindbladNoJumpTrajectoryContinuous K A t +
        lindbladNoJumpTrajectoryContinuous K A t *
          ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) t := by
  convert hasDerivAt_lindbladNoJumpTrajectoryContinuous_raw K A t using 1
  rw [(continuousOperator_commute_lindbladNoJumpPropagator K t).eq.symm]
  simp only [lindbladNoJumpTrajectoryContinuous, mul_assoc]

/-- The no-jump trajectory bundled as a continuous superoperator. -/
noncomputable def lindbladNoJumpEvolutionContinuous
    (K : Operator H) (t : Real) : ContinuousSuperoperator H :=
  ContinuousLinearMap.mulLeftRight Complex (ContinuousOperator H)
    (lindbladNoJumpPropagatorContinuous K t)
    (ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t))

@[simp]
theorem lindbladNoJumpEvolutionContinuous_apply
    (K : Operator H) (t : Real) (A : ContinuousOperator H) :
    lindbladNoJumpEvolutionContinuous K t A =
      lindbladNoJumpTrajectoryContinuous K A t :=
  rfl

@[simp]
theorem lindbladNoJumpEvolutionContinuous_zero (K : Operator H) :
    lindbladNoJumpEvolutionContinuous K 0 = 1 := by
  ext A x
  simp [lindbladNoJumpEvolutionContinuous,
    lindbladNoJumpPropagatorContinuous_zero, ContinuousLinearMap.adjoint_one]

theorem continuous_lindbladNoJumpPropagatorContinuous (K : Operator H) :
    Continuous (lindbladNoJumpPropagatorContinuous K) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_lindbladNoJumpPropagatorContinuous K t).continuousAt

theorem continuous_adjoint_lindbladNoJumpPropagatorContinuous (K : Operator H) :
    Continuous (fun t : Real =>
      ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t)) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_adjoint_lindbladNoJumpPropagatorContinuous K t).continuousAt

theorem continuous_lindbladNoJumpEvolutionContinuous (K : Operator H) :
    Continuous (lindbladNoJumpEvolutionContinuous K) := by
  unfold lindbladNoJumpEvolutionContinuous
  exact (continuous_const.clm_apply
    (continuous_lindbladNoJumpPropagatorContinuous K)).clm_apply
      (continuous_adjoint_lindbladNoJumpPropagatorContinuous K)

theorem trace_lindbladJumpTerm (J A : Operator H) :
    LinearMap.trace Complex H (lindbladJumpTerm J A) = 0 := by
  have hcycle :
      LinearMap.trace Complex H (J * A * LinearMap.adjoint J) =
        LinearMap.trace Complex H ((LinearMap.adjoint J * J) * A) := by
    calc
      LinearMap.trace Complex H (J * A * LinearMap.adjoint J) =
          LinearMap.trace Complex H (LinearMap.adjoint J * (J * A)) := by
        exact LinearMap.trace_mul_comm (R := Complex) (M := H)
          (J * A) (LinearMap.adjoint J)
      _ = LinearMap.trace Complex H ((LinearMap.adjoint J * J) * A) := by
        exact congrArg (LinearMap.trace Complex H)
          (mul_assoc (LinearMap.adjoint J) J A).symm
  have hcycle' :
      LinearMap.trace Complex H (A * (LinearMap.adjoint J * J)) =
        LinearMap.trace Complex H ((LinearMap.adjoint J * J) * A) :=
    LinearMap.trace_mul_comm (R := Complex) (M := H)
      A (LinearMap.adjoint J * J)
  unfold lindbladJumpTerm
  dsimp
  rw [map_sub, map_smul, map_add, hcycle, hcycle']
  ring

theorem trace_hamiltonianCommutator (hamiltonian A : Operator H) :
    LinearMap.trace Complex H (hamiltonianCommutator hamiltonian A) = 0 := by
  unfold hamiltonianCommutator
  dsimp
  rw [map_smul, map_sub,
    LinearMap.trace_mul_comm (R := Complex) (M := H) hamiltonian A]
  ring

theorem trace_finiteLindbladGenerator [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H) :
    LinearMap.trace Complex H (finiteLindbladGenerator hamiltonian J A) = 0 := by
  simp [finiteLindbladGenerator, lindbladDissipator,
    trace_hamiltonianCommutator, trace_lindbladJumpTerm]

/-- The trace as a continuous functional on the normed operator model. -/
noncomputable def continuousOperatorTrace : ContinuousOperator H →L[Complex] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.trace Complex H A.toLinearMap
      map_add' := by intro A B; simp
      map_smul' := by intro c A; simp }

noncomputable def asContinuousSuperoperator (L : Superoperator H) :
    ContinuousSuperoperator H :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (L.comp LinearMap.toContinuousLinearMap.symm.toLinearMap))

noncomputable def asOperatorSuperoperator (L : ContinuousSuperoperator H) :
    Superoperator H :=
  LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
    (L.toLinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap)

@[simp]
theorem asContinuousSuperoperator_add (L M : Superoperator H) :
    asContinuousSuperoperator (L + M) =
      asContinuousSuperoperator L + asContinuousSuperoperator M := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem asContinuousSuperoperator_lindbladNoJumpDrift (K : Operator H) :
    asContinuousSuperoperator (lindbladNoJumpDrift K) =
      continuousLeftRegularRepresentation (H := H)
          (LinearMap.toContinuousLinearMap K) +
        continuousRightRegularRepresentation (H := H)
          (MulOpposite.op
            (ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K))) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change
    (LinearMap.toContinuousLinearMap K * A +
      A * ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap K)) x = _
  rfl

@[simp]
theorem asOperatorSuperoperator_one :
    asOperatorSuperoperator (1 : ContinuousSuperoperator H) = LinearMap.id := by
  ext A x
  rfl

@[simp]
theorem asOperatorSuperoperator_mul (L M : ContinuousSuperoperator H) :
    asOperatorSuperoperator (L * M) =
      (asOperatorSuperoperator L).comp (asOperatorSuperoperator M) := by
  ext A x
  rfl

@[simp]
theorem asOperatorSuperoperator_smul (c : Complex)
    (L : ContinuousSuperoperator H) :
    asOperatorSuperoperator (c • L) =
      c • asOperatorSuperoperator L := by
  ext A x
  rfl

@[simp]
theorem asOperatorSuperoperator_asContinuousSuperoperator (L : Superoperator H) :
    asOperatorSuperoperator (asContinuousSuperoperator L) = L := by
  ext A x
  rfl

theorem asOperatorSuperoperator_finset_sum {κ : Type*}
    (s : Finset κ) (f : κ → ContinuousSuperoperator H) :
    asOperatorSuperoperator (∑ i ∈ s, f i) =
      ∑ i ∈ s, asOperatorSuperoperator (f i) := by
  classical
  ext A x
  simp [asOperatorSuperoperator]

theorem asOperatorSuperoperator_lindbladNoJumpEvolutionContinuous
    (K : Operator H) (t : Real) :
    asOperatorSuperoperator (lindbladNoJumpEvolutionContinuous K t) =
      lindbladNoJumpEvolutionLinearMap K t := by
  ext A x
  change
    (lindbladNoJumpPropagatorContinuous K t *
      LinearMap.toContinuousLinearMap A *
      ContinuousLinearMap.adjoint (lindbladNoJumpPropagatorContinuous K t)) x =
    (lindbladNoJumpPropagator K t * A *
      LinearMap.adjoint (lindbladNoJumpPropagator K t)) x
  unfold lindbladNoJumpPropagator
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  rfl

theorem lindbladNoJumpEvolutionContinuous_completelyPositive
    (K : Operator H) (t : Real) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladNoJumpEvolutionContinuous K t)) := by
  rw [asOperatorSuperoperator_lindbladNoJumpEvolutionContinuous]
  exact lindbladNoJumpEvolutionLinearMap_completelyPositive K t

/-- The exponential of the no-jump drift is the explicit one-Kraus
trajectory. -/
theorem exp_asContinuousSuperoperator_lindbladNoJumpDrift
    (K : Operator H) (t : Real) :
    NormedSpace.exp
        ((t : Complex) • asContinuousSuperoperator (lindbladNoJumpDrift K)) =
      lindbladNoJumpEvolutionContinuous K t := by
  let Kc := LinearMap.toContinuousLinearMap K
  let Kadj := ContinuousLinearMap.adjoint Kc
  have hscaled :
      (t : Complex) • asContinuousSuperoperator (lindbladNoJumpDrift K) =
        continuousLeftRegularRepresentation (H := H) ((t : Complex) • Kc) +
          continuousRightRegularRepresentation (H := H)
            (MulOpposite.op ((t : Complex) • Kadj)) := by
    rw [asContinuousSuperoperator_lindbladNoJumpDrift]
    apply ContinuousLinearMap.ext
    intro A
    apply ContinuousLinearMap.ext
    intro x
    simp
    rfl
  rw [hscaled, NormedSpace.exp_add_of_commute_of_mem_ball
    (commute_continuousRegularRepresentations ((t : Complex) • Kc)
      ((t : Complex) • Kadj))
    ((NormedSpace.expSeries_radius_eq_top Complex
      (ContinuousSuperoperator H)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top Complex
      (ContinuousSuperoperator H)).symm ▸ edist_lt_top _ _)]
  rw [exp_continuousLeftRegularRepresentation,
    exp_continuousRightRegularRepresentation]
  apply ContinuousLinearMap.ext
  intro A
  apply ContinuousLinearMap.ext
  intro x
  change
    (NormedSpace.exp ((t : Complex) • Kc) * A *
      NormedSpace.exp ((t : Complex) • Kadj)) x =
      (lindbladNoJumpPropagatorContinuous K t * A *
        ContinuousLinearMap.adjoint
          (lindbladNoJumpPropagatorContinuous K t)) x
  rw [adjoint_lindbladNoJumpPropagatorContinuous]
  rfl

/-- The completely positive jump gain transported to the continuous model. -/
noncomputable def lindbladJumpGainContinuous [Fintype ι]
    (J : ι → Operator H) : ContinuousSuperoperator H :=
  asContinuousSuperoperator (lindbladJumpGain J)

@[simp]
theorem asOperatorSuperoperator_lindbladJumpGainContinuous [Fintype ι]
    (J : ι → Operator H) :
    asOperatorSuperoperator (lindbladJumpGainContinuous J) =
      lindbladJumpGain J := by
  exact asOperatorSuperoperator_asContinuousSuperoperator (lindbladJumpGain J)

/-- One Dyson integrand: free no-jump propagation after one jump. -/
noncomputable def lindbladDysonIntegrandContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H) (t s : Real) :
    ContinuousSuperoperator H :=
  lindbladNoJumpEvolutionContinuous K (t - s) *
    lindbladJumpGainContinuous J * previous s

theorem lindbladDysonIntegrandContinuous_completelyPositive [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H)
    (t s : Real)
    (hprevious : CompletelyPositive (asOperatorSuperoperator (previous s))) :
    CompletelyPositive
      (asOperatorSuperoperator
        (lindbladDysonIntegrandContinuous K J previous t s)) := by
  unfold lindbladDysonIntegrandContinuous
  rw [asOperatorSuperoperator_mul, asOperatorSuperoperator_mul,
    asOperatorSuperoperator_lindbladJumpGainContinuous]
  exact CompletelyPositive.comp hprevious
    (CompletelyPositive.comp (lindbladJumpGain_completelyPositive J)
      (lindbladNoJumpEvolutionContinuous_completelyPositive K (t - s)))

/-- Recursive quantum-trajectory/Dyson terms in continuous superoperator space. -/
noncomputable def lindbladDysonTermContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) :
    Nat → Real → ContinuousSuperoperator H
  | 0, t => lindbladNoJumpEvolutionContinuous K t
  | n + 1, t => ∫ s in (0 : Real)..t,
      lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t s

/-- Finite sum of trajectories with at most `N` jumps. -/
noncomputable def lindbladDysonPartialSumContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (N : Nat) (t : Real) :
    ContinuousSuperoperator H :=
  ∑ n ∈ Finset.range (N + 1), lindbladDysonTermContinuous K J n t

/-- The full quantum-trajectory expansion, once its norm summability is established. -/
noncomputable def lindbladDysonEvolutionContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (t : Real) :
    ContinuousSuperoperator H :=
  ∑' n, lindbladDysonTermContinuous K J n t

theorem continuous_lindbladDysonIntegrandContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (previous : Real → ContinuousSuperoperator H)
    (hprevious : Continuous previous) (t : Real) :
    Continuous (lindbladDysonIntegrandContinuous K J previous t) := by
  unfold lindbladDysonIntegrandContinuous
  exact (((continuous_lindbladNoJumpEvolutionContinuous K).comp
    (continuous_const.sub continuous_id)).mul continuous_const).mul hprevious

theorem continuous_lindbladDysonTermContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (n : Nat) :
    Continuous (lindbladDysonTermContinuous K J n) := by
  induction n with
  | zero => exact continuous_lindbladNoJumpEvolutionContinuous K
  | succ n induction =>
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · change Continuous (fun p : Real × Real =>
          lindbladDysonIntegrandContinuous K J
            (lindbladDysonTermContinuous K J n) p.1 p.2)
        unfold lindbladDysonIntegrandContinuous
        exact (((continuous_lindbladNoJumpEvolutionContinuous K).comp
          (continuous_fst.sub continuous_snd)).mul continuous_const).mul
            (induction.comp continuous_snd)
      · exact continuous_id

theorem intervalIntegrable_lindbladDysonIntegrandContinuous [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (n : Nat) (t : Real) :
    IntervalIntegrable
      (lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t)
      MeasureTheory.volume 0 t :=
  (continuous_lindbladDysonIntegrandContinuous K J
    (lindbladDysonTermContinuous K J n)
    (continuous_lindbladDysonTermContinuous K J n) t).intervalIntegrable 0 t

@[simp]
theorem lindbladDysonTermContinuous_zero [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (t : Real) :
    lindbladDysonTermContinuous K J 0 t =
      lindbladNoJumpEvolutionContinuous K t :=
  rfl

theorem lindbladDysonTermContinuous_zero_completelyPositive [Fintype ι]
    (K : Operator H) (J : ι → Operator H) (t : Real) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonTermContinuous K J 0 t)) := by
  rw [lindbladDysonTermContinuous_zero]
  exact lindbladNoJumpEvolutionContinuous_completelyPositive K t

set_option maxHeartbeats 800000 in
theorem intervalIntegral_preserves_adjoint_blocks
    (f : Real → ContinuousSuperoperator H) (a b : Real)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hab : a ≤ b) (A B : Operator H)
    (hsym : ∀ s ∈ Set.Icc a b, asOperatorSuperoperator (f s) B =
      LinearMap.adjoint (asOperatorSuperoperator (f s) A)) :
    asOperatorSuperoperator (∫ s in a..b, f s) B =
      LinearMap.adjoint (asOperatorSuperoperator (∫ s in a..b, f s) A) := by
  let Ac := LinearMap.toContinuousLinearMap A
  let Bc := LinearMap.toContinuousLinearMap B
  let evalA :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Ac).restrictScalars Real
  let evalB :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Bc).restrictScalars Real
  have hfA : IntervalIntegrable (fun s => f s Ac) MeasureTheory.volume a b :=
    ⟨evalA.integrable_comp hf.1, evalA.integrable_comp hf.2⟩
  have hs (s : Real) (hsab : s ∈ Set.Icc a b) :
      f s Bc = ContinuousLinearMap.adjoint (f s Ac) := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : Operator H => T x) (hsym s hsab)
    rw [LinearMap.adjoint_eq_toCLM_adjoint] at h
    exact h
  have hcontinuous :
      (∫ s in a..b, f s Bc) =
        ContinuousLinearMap.adjoint (∫ s in a..b, f s Ac) := by
    calc
      (∫ s in a..b, f s Bc) =
          (∫ s in a..b, ContinuousLinearMap.adjoint (f s Ac)) := by
            apply intervalIntegral.integral_congr
            intro s hsab
            exact hs s (by simpa [Set.uIcc_of_le hab] using hsab)
      _ = ContinuousLinearMap.adjoint (∫ s in a..b, f s Ac) := by
            exact intervalIntegral_comp_comm continuousOperatorAdjointReal
              (fun s => f s Ac) a b hfA
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  apply congrArg ContinuousLinearMap.toLinearMap
  change (∫ s in a..b, f s) Bc =
    ContinuousLinearMap.adjoint ((∫ s in a..b, f s) Ac)
  change evalB (∫ s in a..b, f s) =
    ContinuousLinearMap.adjoint (evalA (∫ s in a..b, f s))
  rw [← intervalIntegral_comp_comm evalB f a b hf,
    ← intervalIntegral_comp_comm evalA f a b hf]
  exact hcontinuous

set_option maxHeartbeats 800000 in
theorem tsum_preserves_adjoint_blocks
    (f : Nat → ContinuousSuperoperator H) (hf : Summable f)
    (A B : Operator H)
    (hsym : ∀ n, asOperatorSuperoperator (f n) B =
      LinearMap.adjoint (asOperatorSuperoperator (f n) A)) :
    asOperatorSuperoperator (∑' n, f n) B =
      LinearMap.adjoint (asOperatorSuperoperator (∑' n, f n) A) := by
  let Ac := LinearMap.toContinuousLinearMap A
  let Bc := LinearMap.toContinuousLinearMap B
  let evalA :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Ac).restrictScalars Real
  let evalB :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Bc).restrictScalars Real
  have hfA : Summable (fun n => f n Ac) := evalA.summable hf
  have hs (n : Nat) :
      f n Bc = ContinuousLinearMap.adjoint (f n Ac) := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : Operator H => T x) (hsym n)
    rw [LinearMap.adjoint_eq_toCLM_adjoint] at h
    exact h
  have hcontinuous :
      (∑' n, f n Bc) =
        ContinuousLinearMap.adjoint (∑' n, f n Ac) := by
    calc
      (∑' n, f n Bc) =
          (∑' n, ContinuousLinearMap.adjoint (f n Ac)) := by
            congr 1
            funext n
            exact hs n
      _ = ContinuousLinearMap.adjoint (∑' n, f n Ac) := by
            exact (continuousOperatorAdjointReal.map_tsum hfA).symm
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  apply congrArg ContinuousLinearMap.toLinearMap
  change (∑' n, f n) Bc =
    ContinuousLinearMap.adjoint ((∑' n, f n) Ac)
  change evalB (∑' n, f n) =
    ContinuousLinearMap.adjoint (evalA (∑' n, f n))
  rw [evalB.map_tsum hf, evalA.map_tsum hf]
  exact hcontinuous

set_option synthInstance.maxHeartbeats 200000 in
/-- The block quadratic form as a real continuous functional of a superoperator. -/
noncomputable def completelyPositiveQuadraticFunctional (n : Nat)
    (M : OperatorMatrix n H) (x : Fin n → H) :
    ContinuousSuperoperator H →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => Complex.re
        (∑ i : Fin n, ∑ j : Fin n,
          inner Complex (L (LinearMap.toContinuousLinearMap (M i j)) (x j)) (x i))
      map_add' := by
        intro L N
        simp only [ContinuousLinearMap.add_apply, inner_add_left,
          Complex.add_re, Finset.sum_add_distrib]
      map_smul' := by
        intro r L
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
        have heq :
            (∑ i : Fin n, ∑ j : Fin n,
              inner Complex
                (r • (L (LinearMap.toContinuousLinearMap (M i j))) (x j)) (x i)) =
            (r : Complex) * (∑ i : Fin n, ∑ j : Fin n,
              inner Complex
                (L (LinearMap.toContinuousLinearMap (M i j)) (x j)) (x i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          change inner Complex
            ((r : Complex) •
              (L (LinearMap.toContinuousLinearMap (M i j))) (x j)) (x i) = _
          rw [inner_smul_left]
          simp
        rw [heq, Complex.mul_re]
        simp }

theorem completelyPositiveQuadraticFunctional_apply (n : Nat)
    (M : OperatorMatrix n H) (x : Fin n → H)
    (L : ContinuousSuperoperator H) :
    completelyPositiveQuadraticFunctional n M x L =
      Complex.re (∑ i : Fin n, ∑ j : Fin n,
        inner Complex
          (asOperatorSuperoperator L (M i j) (x j)) (x i)) := by
  simp [completelyPositiveQuadraticFunctional, asOperatorSuperoperator]

namespace CompletelyPositive

set_option maxHeartbeats 800000 in
theorem intervalIntegral
    (f : Real → ContinuousSuperoperator H) (a b : Real) (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hcp : ∀ s ∈ Set.Icc a b,
      CompletelyPositive (asOperatorSuperoperator (f s))) :
    CompletelyPositive (asOperatorSuperoperator (∫ s in a..b, f s)) := by
  intro n M hM
  constructor
  · intro i j
    exact intervalIntegral_preserves_adjoint_blocks f a b hf hab (M i j) (M j i)
      (fun s hs => (hcp s hs n M hM).1 i j)
  · intro x
    let q := completelyPositiveQuadraticFunctional n M x
    have hnonneg : 0 ≤ ∫ s in a..b, q (f s) :=
      intervalIntegral.integral_nonneg hab fun s hs => by
        simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using
          (hcp s hs n M hM).2 x
    rw [intervalIntegral_comp_comm q f a b hf] at hnonneg
    simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using hnonneg

set_option maxHeartbeats 800000 in
theorem tsum
    (f : Nat → ContinuousSuperoperator H) (hf : Summable f)
    (hcp : ∀ n, CompletelyPositive (asOperatorSuperoperator (f n))) :
    CompletelyPositive (asOperatorSuperoperator (∑' n, f n)) := by
  intro n M hM
  constructor
  · intro i j
    exact tsum_preserves_adjoint_blocks f hf (M i j) (M j i)
      (fun k => (hcp k n M hM).1 i j)
  · intro x
    let q := completelyPositiveQuadraticFunctional n M x
    have hq : Summable (fun k => q (f k)) := q.summable hf
    have hnonneg : 0 ≤ ∑' k, q (f k) :=
      tsum_nonneg fun k => by
        simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using
          (hcp k n M hM).2 x
    rw [← q.map_tsum hf] at hnonneg
    simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using hnonneg

/-- Complete positivity is closed under operator-norm limits of continuous
superoperators. -/
theorem tendsto
    (f : Nat → ContinuousSuperoperator H) (L : ContinuousSuperoperator H)
    (hf : Filter.Tendsto f Filter.atTop (nhds L))
    (hcp : ∀ n, CompletelyPositive (asOperatorSuperoperator (f n))) :
    CompletelyPositive (asOperatorSuperoperator L) := by
  intro n M hM
  constructor
  · intro i j
    let Ac := LinearMap.toContinuousLinearMap (M i j)
    let Bc := LinearMap.toContinuousLinearMap (M j i)
    let evalA := ContinuousLinearMap.apply Complex (ContinuousOperator H) Ac
    let evalB := ContinuousLinearMap.apply Complex (ContinuousOperator H) Bc
    have hA : Filter.Tendsto (fun k => f k Ac) Filter.atTop (nhds (L Ac)) :=
      evalA.continuous.continuousAt.tendsto.comp hf
    have hB : Filter.Tendsto (fun k => f k Bc) Filter.atTop (nhds (L Bc)) :=
      evalB.continuous.continuousAt.tendsto.comp hf
    have hadj : Filter.Tendsto
        (fun k => ContinuousLinearMap.adjoint (f k Ac)) Filter.atTop
        (nhds (ContinuousLinearMap.adjoint (L Ac))) :=
      continuousOperatorAdjointReal.continuous.continuousAt.tendsto.comp hA
    have hterm (k : Nat) :
        f k Bc = ContinuousLinearMap.adjoint (f k Ac) := by
      have hraw := (hcp k n M hM).1 i j
      simp only [OperatorMatrix.map] at hraw
      apply ContinuousLinearMap.ext
      intro x
      have h := congrArg (fun T : Operator H => T x) hraw
      rw [LinearMap.adjoint_eq_toCLM_adjoint] at h
      exact h
    have hcontinuous : L Bc = ContinuousLinearMap.adjoint (L Ac) :=
      tendsto_nhds_unique hB
        (hadj.congr' (Filter.Eventually.of_forall fun k => (hterm k).symm))
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    apply congrArg ContinuousLinearMap.toLinearMap
    simpa [asOperatorSuperoperator, Ac, Bc, OperatorMatrix.map,
      ← LinearMap.coe_toContinuousLinearMap_symm] using hcontinuous
  · intro x
    let q := completelyPositiveQuadraticFunctional n M x
    have hq : Filter.Tendsto (fun k => q (f k)) Filter.atTop (nhds (q L)) :=
      q.continuous.continuousAt.tendsto.comp hf
    have hevent : ∀ᶠ k in Filter.atTop, 0 ≤ q (f k) :=
      Filter.Eventually.of_forall fun k => by
        simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using
          (hcp k n M hM).2 x
    have hnonneg : 0 ≤ q L := ge_of_tendsto hq hevent
    simpa [q, completelyPositiveQuadraticFunctional_apply, OperatorMatrix.map] using hnonneg

theorem oneContinuousSuperoperator :
    CompletelyPositive
      (asOperatorSuperoperator (1 : ContinuousSuperoperator H)) := by
  rw [asOperatorSuperoperator_one]
  exact (QuantumChannel.id H).completely_positive

theorem powContinuousSuperoperator (L : ContinuousSuperoperator H)
    (hL : CompletelyPositive (asOperatorSuperoperator L)) (n : Nat) :
    CompletelyPositive (asOperatorSuperoperator (L ^ n)) := by
  induction n with
  | zero => simpa using oneContinuousSuperoperator (H := H)
  | succ n ih =>
      rw [pow_succ, asOperatorSuperoperator_mul]
      exact CompletelyPositive.comp hL ih

theorem expContinuousSuperoperator (L : ContinuousSuperoperator H)
    (hL : CompletelyPositive (asOperatorSuperoperator L)) :
    CompletelyPositive (asOperatorSuperoperator (NormedSpace.exp L)) := by
  rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := Complex) L).tsum_eq]
  apply CompletelyPositive.tsum _
    (NormedSpace.expSeries_summable' (𝕂 := Complex) L)
  intro n
  rw [asOperatorSuperoperator_smul]
  simpa using CompletelyPositive.nonneg_smul
    ((Nat.factorial n : Real)⁻¹) (by positivity)
      (powContinuousSuperoperator L hL n)

end CompletelyPositive

theorem lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable
    [Fintype ι] (K : Operator H) (J : ι → Operator H)
    (hintegrable : ∀ n t, IntervalIntegrable
      (lindbladDysonIntegrandContinuous K J
        (lindbladDysonTermContinuous K J n) t)
      MeasureTheory.volume 0 t)
    (n : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonTermContinuous K J n t)) := by
  induction n generalizing t with
  | zero => exact lindbladDysonTermContinuous_zero_completelyPositive K J t
  | succ n induction =>
      change CompletelyPositive
        (asOperatorSuperoperator
          (∫ s in (0 : Real)..t,
            lindbladDysonIntegrandContinuous K J
              (lindbladDysonTermContinuous K J n) t s))
      apply CompletelyPositive.intervalIntegral _ 0 t ht (hintegrable n t)
      intro s hs
      exact lindbladDysonIntegrandContinuous_completelyPositive K J
        (lindbladDysonTermContinuous K J n) t s (induction s hs.1)

theorem lindbladDysonTermContinuous_completelyPositive [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (n : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonTermContinuous K J n t)) :=
  lindbladDysonTermContinuous_completelyPositive_of_intervalIntegrable K J
    (intervalIntegrable_lindbladDysonIntegrandContinuous K J) n t ht

theorem lindbladDysonPartialSumContinuous_completelyPositive [Fintype ι]
    (K : Operator H) (J : ι → Operator H)
    (N : Nat) (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonPartialSumContinuous K J N t)) := by
  rw [lindbladDysonPartialSumContinuous,
    asOperatorSuperoperator_finset_sum]
  exact CompletelyPositive.sum_finset (Finset.range (N + 1))
    (fun n _hn => lindbladDysonTermContinuous_completelyPositive K J n t ht)

theorem lindbladDysonEvolutionContinuous_completelyPositive_of_summable
    [Fintype ι] (K : Operator H) (J : ι → Operator H)
    (t : Real) (ht : 0 ≤ t)
    (hsummable : Summable (fun n => lindbladDysonTermContinuous K J n t)) :
    CompletelyPositive
      (asOperatorSuperoperator (lindbladDysonEvolutionContinuous K J t)) := by
  unfold lindbladDysonEvolutionContinuous
  exact CompletelyPositive.tsum _ hsummable
    (fun n => lindbladDysonTermContinuous_completelyPositive K J n t ht)

/-- The induced trace norm over the source-faithful self-adjoint unit ball. -/
noncomputable def selfAdjointTraceNormOneToOne (L : Superoperator H) : Real :=
  sSup {r : Real | ∃ A : Operator H,
    A.IsSymmetric ∧ traceNorm A ≤ 1 ∧ r = traceNorm (L A)}

noncomputable def lindbladDissipatorNorm [Fintype ι]
    (J : ι → Operator H) : Real :=
  selfAdjointTraceNormOneToOne (lindbladDissipator J)

/-- The complex-time superoperator exponential underlying real-time evolution. -/
noncomputable def finiteLindbladEvolutionContinuous [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (z : Complex) :
    ContinuousSuperoperator H :=
  NormedSpace.exp
    (z • asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J))

/-- Lindblad evolution defined by the finite superoperator exponential. -/
noncomputable def finiteLindbladEvolutionLinearMap [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t : Real) :
    Superoperator H :=
  asOperatorSuperoperator
    (finiteLindbladEvolutionContinuous hamiltonian J (t : Complex))

private theorem finiteLindbladEvolutionLinearMap_completelyPositive_of_nontrivial
    [Fintype ι] [Nontrivial H]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive (finiteLindbladEvolutionLinearMap hamiltonian J t) := by
  let K := lindbladEffectiveOperator hamiltonian J
  let D := asContinuousSuperoperator (lindbladNoJumpDrift K)
  let G := lindbladJumpGainContinuous J
  let X : ContinuousSuperoperator H := (t : Complex) • D
  let Y : ContinuousSuperoperator H := (t : Complex) • G
  have hgenerator :
      asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J) =
        D + G := by
    rw [finiteLindbladGenerator_eq_noJump_add_gain hamiltonian J hhamiltonian,
      asContinuousSuperoperator_add]
    rfl
  have hevolution :
      finiteLindbladEvolutionContinuous hamiltonian J (t : Complex) =
        NormedSpace.exp (X + Y) := by
    unfold finiteLindbladEvolutionContinuous
    rw [hgenerator]
    change NormedSpace.exp ((t : Complex) • (D + G)) = _
    rw [smul_add]
  rw [finiteLindbladEvolutionLinearMap, hevolution]
  apply CompletelyPositive.tendsto
    (fun n : Nat => (lieTrotterStep X Y ((n : Complex)⁻¹)) ^ n)
    (NormedSpace.exp (X + Y)) (tendsto_lieTrotter X Y)
  intro n
  apply CompletelyPositive.powContinuousSuperoperator
  rw [lieTrotterStep, asOperatorSuperoperator_mul]
  apply CompletelyPositive.comp
  · have hscalar :
        ((n : Complex)⁻¹) • Y =
          ((((n : Real)⁻¹ * t : Real) : Complex) • G) := by
      simp [Y, smul_smul]
    apply CompletelyPositive.expContinuousSuperoperator
    rw [hscalar, asOperatorSuperoperator_smul]
    exact CompletelyPositive.nonneg_smul ((n : Real)⁻¹ * t)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) ht) (by
          dsimp [G]
          rw [asOperatorSuperoperator_lindbladJumpGainContinuous]
          exact lindbladJumpGain_completelyPositive J)
  · have hscalar :
        ((n : Complex)⁻¹) • X =
          ((((n : Real)⁻¹ * t : Real) : Complex) • D) := by
      simp [X, smul_smul]
    rw [hscalar, exp_asContinuousSuperoperator_lindbladNoJumpDrift]
    exact lindbladNoJumpEvolutionContinuous_completelyPositive K
      ((n : Real)⁻¹ * t)

/-- Finite-dimensional Lindblad evolution is completely positive for
nonnegative time.  The proof is the no-jump/jump-gain Lie--Trotter
factorization. -/
theorem finiteLindbladEvolutionLinearMap_completelyPositive [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (t : Real) (ht : 0 ≤ t) :
    CompletelyPositive (finiteLindbladEvolutionLinearMap hamiltonian J t) := by
  classical
  by_cases hH : Nontrivial H
  · letI := hH
    exact finiteLindbladEvolutionLinearMap_completelyPositive_of_nontrivial
      hamiltonian J hhamiltonian t ht
  · letI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
    have hzero : finiteLindbladEvolutionLinearMap hamiltonian J t = 0 := by
      apply LinearMap.ext
      intro A
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    rw [hzero]
    exact CompletelyPositive.zero

theorem hasDerivAt_finiteLindbladEvolutionContinuous [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (z : Complex) :
    HasDerivAt (finiteLindbladEvolutionContinuous hamiltonian J)
      (finiteLindbladEvolutionContinuous hamiltonian J z *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z := by
  exact hasDerivAt_exp_smul_const
    (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z

theorem hasDerivAt_finiteLindbladEvolutionReal [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t : Real) :
    HasDerivAt
      (fun s : Real => finiteLindbladEvolutionContinuous hamiltonian J (s : Complex))
      (finiteLindbladEvolutionContinuous hamiltonian J (t : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) t := by
  let _ : NormedAlgebra Real (ContinuousSuperoperator H) :=
    NormedAlgebra.restrictScalars Real Complex (ContinuousSuperoperator H)
  change HasDerivAt
    (fun s : Real => NormedSpace.exp
      (s • asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)))
    (NormedSpace.exp (t • asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) *
      asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) t
  exact hasDerivAt_exp_smul_const
    (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) t

@[simp]
theorem finiteLindbladEvolutionContinuous_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) :
    finiteLindbladEvolutionContinuous hamiltonian J 0 = 1 := by
  unfold finiteLindbladEvolutionContinuous
  have hz : (0 : Complex) •
      asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J) = 0 := by
    ext A x
    simp
  rw [hz, NormedSpace.exp_zero]

theorem finiteLindbladEvolutionContinuous_integral [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (t : Real) :
    (∫ s in (0 : Real)..t,
      finiteLindbladEvolutionContinuous hamiltonian J (s : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) =
      finiteLindbladEvolutionContinuous hamiltonian J (t : Complex) - 1 := by
  have hderiv : ∀ s : Real, HasDerivAt
      (fun r : Real => finiteLindbladEvolutionContinuous hamiltonian J (r : Complex))
      (finiteLindbladEvolutionContinuous hamiltonian J (s : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) s :=
    fun s => hasDerivAt_finiteLindbladEvolutionReal hamiltonian J s
  have hint : IntervalIntegrable
      (fun s : Real => finiteLindbladEvolutionContinuous hamiltonian J (s : Complex) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J))
      MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_finiteLindbladEvolutionReal hamiltonian J s).continuousAt.mul
        continuousAt_const
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs => hderiv s) hint
  have hzeroCast : finiteLindbladEvolutionContinuous hamiltonian J
      ((0 : Real) : Complex) = 1 := by
    change finiteLindbladEvolutionContinuous hamiltonian J (0 : Complex) = 1
    exact finiteLindbladEvolutionContinuous_zero hamiltonian J
  rw [hzeroCast] at hfund
  exact hfund

theorem continuousOperatorTrace_generator_eq_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : ContinuousOperator H) :
    continuousOperatorTrace
      (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J) A) = 0 := by
  change LinearMap.trace Complex H
    (finiteLindbladGenerator hamiltonian J A.toLinearMap) = 0
  exact trace_finiteLindbladGenerator hamiltonian J A.toLinearMap

theorem hasDerivAt_trace_finiteLindbladEvolutionContinuous [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (A : ContinuousOperator H) (z : Complex) :
    HasDerivAt
      (fun w => continuousOperatorTrace
        (finiteLindbladEvolutionContinuous hamiltonian J w A)) 0 z := by
  let E := finiteLindbladEvolutionContinuous hamiltonian J
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  have hE : HasDerivAt E (G * E z) z := by
    exact hasDerivAt_exp_smul_const'
      (asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) z
  have hEA : HasDerivAt (fun w => E w A) ((G * E z) A) z := by
    simpa using hE.clm_apply (hasDerivAt_const z A)
  have htrace := (hasDerivAt_const z continuousOperatorTrace).clm_apply hEA
  have hzero : continuousOperatorTrace ((G * E z) A) = 0 := by
    change continuousOperatorTrace (G (E z A)) = 0
    exact continuousOperatorTrace_generator_eq_zero hamiltonian J (E z A)
  simp only [zero_apply, zero_add, hzero] at htrace
  exact htrace

theorem continuousOperatorTrace_evolution [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (A : ContinuousOperator H) (z : Complex) :
    continuousOperatorTrace
      (finiteLindbladEvolutionContinuous hamiltonian J z A) =
        continuousOperatorTrace A := by
  let f : Complex → Complex := fun w => continuousOperatorTrace
    (finiteLindbladEvolutionContinuous hamiltonian J w A)
  have hf : Differentiable Complex f := fun w =>
    (hasDerivAt_trace_finiteLindbladEvolutionContinuous hamiltonian J A w).differentiableAt
  have hf' : ∀ w, deriv f w = 0 := fun w =>
    (hasDerivAt_trace_finiteLindbladEvolutionContinuous hamiltonian J A w).deriv
  have hconst := is_const_of_deriv_eq_zero hf hf' z 0
  simpa [f] using hconst

theorem finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H)
    (hstationary : finiteLindbladGenerator hamiltonian J A = 0) (z : Complex) :
    finiteLindbladEvolutionContinuous hamiltonian J z
      (LinearMap.toContinuousLinearMap A) = LinearMap.toContinuousLinearMap A := by
  let E := finiteLindbladEvolutionContinuous hamiltonian J
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  let Ac := LinearMap.toContinuousLinearMap A
  have hG : G Ac = 0 := by
    change LinearMap.toContinuousLinearMap
      (finiteLindbladGenerator hamiltonian J A) = 0
    rw [hstationary]
    rfl
  have hderiv : ∀ w : Complex, HasDerivAt (fun z => E z Ac) 0 w := by
    intro w
    have hE : HasDerivAt E (E w * G) w :=
      hasDerivAt_finiteLindbladEvolutionContinuous hamiltonian J w
    have hEA := hE.clm_apply (hasDerivAt_const w Ac)
    have hzero : (E w * G) Ac = 0 := by
      change E w (G Ac) = 0
      rw [hG]
      exact map_zero (E w)
    simp only [map_zero, add_zero, hzero] at hEA
    exact hEA
  have hdiff : Differentiable Complex (fun w => E w Ac) :=
    fun w => (hderiv w).differentiableAt
  have hderiv_zero : ∀ w, deriv (fun z => E z Ac) w = 0 :=
    fun w => (hderiv w).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv_zero z 0
  simpa [E, Ac] using hconst

@[simp]
theorem finiteLindbladEvolutionLinearMap_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) :
    finiteLindbladEvolutionLinearMap hamiltonian J 0 = LinearMap.id := by
  unfold finiteLindbladEvolutionLinearMap
  change asOperatorSuperoperator
    (finiteLindbladEvolutionContinuous hamiltonian J (0 : Complex)) = LinearMap.id
  rw [finiteLindbladEvolutionContinuous_zero, asOperatorSuperoperator_one]

theorem finiteLindbladEvolutionLinearMap_trace [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t : Real)
    (A : Operator H) :
    LinearMap.trace Complex H
      (finiteLindbladEvolutionLinearMap hamiltonian J t A) =
        LinearMap.trace Complex H A := by
  exact continuousOperatorTrace_evolution hamiltonian J
    (LinearMap.toContinuousLinearMap A) (t : Complex)

/-- The nonnegative-time finite Lindblad evolution bundled as a CPTP quantum
channel. -/
noncomputable def finiteLindbladEvolutionChannel [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (t : Real) (ht : 0 ≤ t) : QuantumChannel H H where
  toLinearMap := finiteLindbladEvolutionLinearMap hamiltonian J t
  completely_positive :=
    finiteLindbladEvolutionLinearMap_completelyPositive
      hamiltonian J hhamiltonian t ht
  trace_preserving := finiteLindbladEvolutionLinearMap_trace hamiltonian J t

theorem finiteLindbladEvolutionLinearMap_apply_of_generator_eq_zero [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (A : Operator H)
    (hstationary : finiteLindbladGenerator hamiltonian J A = 0) (t : Real) :
    finiteLindbladEvolutionLinearMap hamiltonian J t A = A := by
  change LinearMap.toContinuousLinearMap.symm
    (finiteLindbladEvolutionContinuous hamiltonian J (t : Complex)
      (LinearMap.toContinuousLinearMap A)) = A
  rw [finiteLindbladEvolutionContinuous_apply_of_generator_eq_zero
    hamiltonian J A hstationary]
  rfl

theorem finiteLindbladEvolutionLinearMap_add [Fintype ι]
    (hamiltonian : Operator H) (J : ι → Operator H) (t s : Real) :
    finiteLindbladEvolutionLinearMap hamiltonian J (t + s) =
      (finiteLindbladEvolutionLinearMap hamiltonian J t).comp
        (finiteLindbladEvolutionLinearMap hamiltonian J s) := by
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  have hsmul : ((t + s : Real) : Complex) • G =
      (t : Complex) • G + (s : Complex) • G := by
    calc
      ((t + s : Real) : Complex) • G =
          ((t : Complex) + (s : Complex)) • G := by rw [Complex.ofReal_add]
      _ = (t : Complex) • G + (s : Complex) • G := by
        ext A x
        simp
        module
  have hcomm : Commute ((t : Complex) • G) ((s : Complex) • G) := by
    rw [Commute]
    ext A x
    simp
    module
  let _ : NormedAlgebra ℚ (ContinuousSuperoperator H) :=
    NormedAlgebra.restrictScalars ℚ Complex (ContinuousSuperoperator H)
  unfold finiteLindbladEvolutionLinearMap finiteLindbladEvolutionContinuous
  change asOperatorSuperoperator (NormedSpace.exp (((t + s : Real) : Complex) • G)) =
    (asOperatorSuperoperator (NormedSpace.exp ((t : Complex) • G))).comp
      (asOperatorSuperoperator (NormedSpace.exp ((s : Complex) • G)))
  rw [hsmul, NormedSpace.exp_add_of_commute hcomm,
    asOperatorSuperoperator_mul]

end

end QEC.Semantics
