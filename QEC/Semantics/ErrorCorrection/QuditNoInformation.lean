import QEC.Semantics.ErrorCorrection.QuditReplacement
import QEC.Semantics.ErrorCorrection.KLRecovery
import QEC.Semantics.ErrorCorrection.CodeSupport
import QEC.Semantics.ErrorCorrection.Detectability
/-!
# Finite-qudit no-information and erasure recovery

This internal module relates the BPT measurement convention for finite qudits
to exact recovery from the concrete coordinate-erasure channel.  It deliberately
does not state a geometric tradeoff or any public theorem lifecycle claim.
-/

noncomputable section

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

/-- A local effect is Hermitian positive and bounded above by the identity. -/
def ValidEffect {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (E : Operator H) : Prop :=
  LinearMap.IsPositive E ∧ LinearMap.IsPositive ((1 : Operator H) - E)

/-- A rank-one projector onto a unit vector is a valid effect. -/
theorem validEffect_rankOne_of_norm_one {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {x : H} (hx : ‖x‖ = 1) :
    ValidEffect (InnerProductSpace.rankOne Complex x x).toLinearMap := by
  let P : Operator H := (InnerProductSpace.rankOne Complex x x).toLinearMap
  have hP : P.IsSymmetricProjection := by
    simpa [P] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hx)
  have hOne : (1 : Operator H).IsSymmetricProjection := by
    constructor
    · exact one_mul _
    · intro y z
      simp
  refine ⟨hP.isPositive, ?_⟩
  exact (hP.sub_of_range_le_range hOne (by
    intro y _
    exact ⟨y, by simp⟩)).isPositive

/-- A matrix unit on a basis diagonal is a valid effect. -/
theorem validEffect_rankOne_basis_diagonal {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H) (i : κ) :
    ValidEffect (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap :=
  validEffect_rankOne_of_norm_one (b.orthonormal.norm_eq_one i)

/- A rank-one operator with squared norm two becomes an effect after halving. -/
set_option maxHeartbeats 800000 in
theorem validEffect_half_rankOne_of_inner_eq_two {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {x : H} (hxx : inner Complex x x = 2) :
    ValidEffect ((2 : Complex)⁻¹ •
      (InnerProductSpace.rankOne Complex x x).toLinearMap) := by
  have hxnorm : (‖x‖ ^ 2 : Complex) = 2 := by
    calc
      (‖x‖ ^ 2 : Complex) = inner Complex x x := (inner_self_eq_norm_sq_to_K x).symm
      _ = 2 := hxx
  let P : Operator H := (2 : Complex)⁻¹ •
    (InnerProductSpace.rankOne Complex x x).toLinearMap
  have hP : P.IsSymmetricProjection := by
    constructor
    · ext x
      simp [P, InnerProductSpace.rankOne_apply]
      rw [hxnorm]
      module
    · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) = (2 : Complex)⁻¹ := by
        rw [map_inv₀]
        have htwo : starRingEnd Complex (2 : Complex) = 2 :=
          map_natCast (starRingEnd Complex) 2
        rw [htwo]
      simpa [P] using
        (InnerProductSpace.isSymmetric_rankOne_self (𝕜 := Complex) x).smul hreal
  have hOne : (1 : Operator H).IsSymmetricProjection := by
    constructor
    · exact one_mul _
    · intro y z
      simp
  refine ⟨hP.isPositive, ?_⟩
  exact (hP.sub_of_range_le_range hOne (by
    intro y _
    exact ⟨y, by simp⟩)).isPositive

/-- The equal-weight projector onto the span of two distinct basis vectors is an effect. -/
theorem validEffect_half_rankOne_add {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    {i j : κ} (hij : i ≠ j) :
    ValidEffect ((2 : Complex)⁻¹ •
      (InnerProductSpace.rankOne Complex (b i + b j) (b i + b j)).toLinearMap) := by
  apply validEffect_half_rankOne_of_inner_eq_two
  have hji0 : inner Complex (b j) (b i) = 0 :=
    b.orthonormal.inner_eq_zero hij.symm
  simp only [inner_add_left, inner_add_right]
  simp [hij, hji0]
  norm_num

/-- The equal-weight projector onto a phase-shifted pair of basis vectors is an effect. -/
theorem validEffect_half_rankOne_add_I_smul {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    {i j : κ} (hij : i ≠ j) :
    ValidEffect ((2 : Complex)⁻¹ •
      (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
        (b i + Complex.I • b j)).toLinearMap) := by
  apply validEffect_half_rankOne_of_inner_eq_two
  have hji0 : inner Complex (b j) (b i) = 0 :=
    b.orthonormal.inner_eq_zero hij.symm
  simp only [inner_add_left, inner_add_right]
  simp [hij, hji0, norm_smul]
  norm_num

/-- Complex polarization expresses an off-diagonal matrix unit using valid-effect directions. -/
theorem rankOne_basis_polarization {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (x y : H) :
    (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + y) (x + y)).toLinearMap +
        Complex.I • ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + Complex.I • y)
            (x + Complex.I • y)).toLinearMap) -
        ((1 + Complex.I) * (2 : Complex)⁻¹) •
          ((InnerProductSpace.rankOne Complex x x).toLinearMap +
            (InnerProductSpace.rankOne Complex y y).toLinearMap) := by
  ext z
  have hIhalf : Complex.I * (2 : Complex)⁻¹ * Complex.I = -(2 : Complex)⁻¹ := by
    calc
      Complex.I * (2 : Complex)⁻¹ * Complex.I = (2 : Complex)⁻¹ *
          (Complex.I * Complex.I) := by ring
      _ = -(2 : Complex)⁻¹ := by rw [Complex.I_mul_I]; ring
  have hIhalf_mul (a : Complex) :
      Complex.I * ((2 : Complex)⁻¹ * (Complex.I * a)) = -(2 : Complex)⁻¹ * a := by
    calc
      Complex.I * ((2 : Complex)⁻¹ * (Complex.I * a)) =
          (Complex.I * (2 : Complex)⁻¹ * Complex.I) * a := by ring
      _ = -(2 : Complex)⁻¹ * a := by rw [hIhalf]
  simp [InnerProductSpace.rankOne_apply, Complex.conj_I]
  simp only [smul_smul]
  rw [hIhalf_mul (inner Complex y z), hIhalf_mul (inner Complex x z),
    hIhalf_mul (Complex.I * inner Complex y z)]
  module

/-- A finite POVM consists of valid effects whose sum is the identity. -/
def FinitePOVM {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {m : Type v} [Fintype m]
    (effects : m → Operator H) : Prop :=
  (∀ i, ValidEffect (effects i)) ∧ ∑ i, effects i = 1

namespace QuditSubsystem

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

/-- The code-projector compression of an operator is a scalar on the code. -/
def ScalarCompression (C : QuantumCode (Qudit.QuditRegister q))
    (A : Operator (Qudit.QuditRegister q)) : Prop :=
  ∃ scalar : Complex,
    C.projector.comp (A.comp C.projector) = scalar • C.projector

/-- Scalar compression for every local operator on the selected subsystem. -/
def AllLocalScalarCompression (C : QuantumCode (Qudit.QuditRegister q))
    (S : QuditSubsystem q) : Prop :=
  ∀ A : Operator S.selectedSystem,
    ScalarCompression C (S.extendLocalToRegister A)

/--
No local valid effect on `S` can distinguish states encoded in `C`: its global
identity extension has scalar compression to the code projector.
-/
def NoInformationOn (C : QuantumCode (Qudit.QuditRegister q))
    (S : QuditSubsystem q) : Prop :=
  ∀ E : Operator S.selectedSystem, ValidEffect E →
    ScalarCompression C (S.extendLocalToRegister E)

/-- Scalar compression is precisely the existing carrier-matrix-element detectability notion. -/
theorem scalarCompression_iff_detectableOn (C : QuantumCode (Qudit.QuditRegister q))
    (A : Operator (Qudit.QuditRegister q)) :
    ScalarCompression C A ↔ DetectableOn C A := by
  simpa only [ScalarCompression, LinearMap.comp_assoc] using
    (detectableOn_iff_projectorEquation C A).symm

/-- Scalar compression is closed under complex linear combinations. -/
theorem ScalarCompression.linearCombination
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A B : Operator (Qudit.QuditRegister q)}
    (hA : ScalarCompression C A) (hB : ScalarCompression C B)
    (a b : Complex) : ScalarCompression C (a • A + b • B) := by
  rcases hA with ⟨alpha, hAlpha⟩
  rcases hB with ⟨beta, hBeta⟩
  refine ⟨a * alpha + b * beta, ?_⟩
  calc
    C.projector.comp ((a • A + b • B).comp C.projector) =
        a • (C.projector.comp (A.comp C.projector)) +
          b • (C.projector.comp (B.comp C.projector)) := by
            ext x
            simp [LinearMap.comp_apply]
    _ = (a * alpha + b * beta) • C.projector := by
      rw [hAlpha, hBeta]
      module

/-- Scalar compression is closed under complex scaling. -/
theorem ScalarCompression.smul
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A : Operator (Qudit.QuditRegister q)}
    (hA : ScalarCompression C A) (a : Complex) : ScalarCompression C (a • A) := by
  rcases hA with ⟨alpha, hAlpha⟩
  refine ⟨a * alpha, ?_⟩
  calc
    C.projector.comp ((a • A).comp C.projector) =
        a • (C.projector.comp (A.comp C.projector)) := by
          ext x
          simp [LinearMap.comp_apply]
    _ = (a * alpha) • C.projector := by rw [hAlpha]; module

/-- A nonzero scalar can be cancelled from a scalar compression. -/
theorem ScalarCompression.of_smul
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A : Operator (Qudit.QuditRegister q)} {a : Complex}
    (ha : a ≠ 0) (hA : ScalarCompression C (a • A)) : ScalarCompression C A := by
  rcases hA with ⟨alpha, hAlpha⟩
  refine ⟨a⁻¹ * alpha, ?_⟩
  calc
    C.projector.comp (A.comp C.projector) =
        (a⁻¹ * a) • (C.projector.comp (A.comp C.projector)) := by
          rw [inv_mul_cancel₀ ha]
          simp
    _ = a⁻¹ • (C.projector.comp ((a • A).comp C.projector)) := by
          ext x
          simp [LinearMap.comp_apply, smul_smul, mul_assoc]
    _ = a⁻¹ • (alpha • C.projector) := by rw [hAlpha]
    _ = (a⁻¹ * alpha) • C.projector := by module

/-- Scalar compression is closed under addition. -/
theorem ScalarCompression.add
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A B : Operator (Qudit.QuditRegister q)}
    (hA : ScalarCompression C A) (hB : ScalarCompression C B) :
    ScalarCompression C (A + B) := by
  simpa using hA.linearCombination hB 1 1

/-- Scalar compression is closed under finite sums. -/
theorem ScalarCompression.sum
    {C : QuantumCode (Qudit.QuditRegister q)} {κ : Type v} [Fintype κ]
    (f : κ → Operator (Qudit.QuditRegister q))
    (h : ∀ i, ScalarCompression C (f i)) : ScalarCompression C (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s his ih =>
      simpa [Finset.sum_insert, his] using (h i).add ih

/-- Scalar compression of the zero operator. -/
theorem scalarCompression_zero (C : QuantumCode (Qudit.QuditRegister q)) :
    ScalarCompression C (0 : Operator (Qudit.QuditRegister q)) :=
  ⟨0, by simp⟩

/-- A scalar compression fixes the trace of the operator against every encoded density. -/
theorem trace_comp_eq_scalar_of_scalarCompression
    {C : QuantumCode (Qudit.QuditRegister q)} {A : Operator (Qudit.QuditRegister q)}
    {alpha : Complex}
    (hCompression : C.projector.comp (A.comp C.projector) = alpha • C.projector)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hRho : DensityOperator.SupportedOn C rho) :
    LinearMap.trace Complex (Qudit.QuditRegister q) (A.comp rho.toOperator) = alpha := by
  have hProjectorRho := DensityOperator.supportedOn_projector_comp_eq_self C rho hRho
  have hRhoProjector := DensityOperator.supportedOn_comp_projector_eq_self C rho hRho
  have hProjectorRhoApply (x : Qudit.QuditRegister q) :
      C.projector (rho.toOperator x) = rho.toOperator x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun T : Operator (Qudit.QuditRegister q) => T x) hProjectorRho
  calc
    LinearMap.trace Complex (Qudit.QuditRegister q) (A.comp rho.toOperator) =
        LinearMap.trace Complex (Qudit.QuditRegister q) (rho.toOperator.comp A) := by
          exact LinearMap.trace_comp_comm' rho.toOperator A
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((rho.toOperator.comp C.projector).comp A) := by rw [hRhoProjector]
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          (C.projector.comp (A.comp rho.toOperator)) := by
            simpa [LinearMap.comp_assoc] using
              (LinearMap.trace_comp_cycle
                (R := Complex) (M := Qudit.QuditRegister q)
                (N := Qudit.QuditRegister q) (P := Qudit.QuditRegister q)
                (f := C.projector) (g := rho.toOperator) (h := A))
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((C.projector.comp (A.comp C.projector)).comp rho.toOperator) := by
            congr 1
            ext x
            simp only [LinearMap.comp_apply]
            rw [hProjectorRhoApply]
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((alpha • C.projector).comp rho.toOperator) := by rw [hCompression]
    _ = alpha := by
      rw [show (alpha • C.projector).comp rho.toOperator =
          alpha • (C.projector.comp rho.toOperator) by
            ext x
            simp [LinearMap.comp_apply]]
      rw [hProjectorRho, map_smul, rho.trace_one]
      simp

/-- The outcome trace of an operator on a normalized pure density is its Rayleigh quotient. -/
theorem trace_comp_pureOfNonzero
    (A : Operator (Qudit.QuditRegister q)) (x : Qudit.QuditRegister q) (hx : x ≠ 0) :
    LinearMap.trace Complex (Qudit.QuditRegister q)
      (A.comp (DensityOperator.pureOfNonzero x hx).toOperator) =
      (inner Complex x x)⁻¹ * inner Complex x (A x) := by
  rw [DensityOperator.pureOfNonzero_toOperator]
  have hComp : A.comp (InnerProductSpace.rankOne Complex x x).toLinearMap =
      (InnerProductSpace.rankOne Complex (A x) x).toLinearMap := by
    ext y
    simp [LinearMap.comp_apply]
  calc
    LinearMap.trace Complex (Qudit.QuditRegister q)
        (A.comp ((inner Complex x x)⁻¹ •
          (InnerProductSpace.rankOne Complex x x).toLinearMap)) =
        LinearMap.trace Complex (Qudit.QuditRegister q)
          ((inner Complex x x)⁻¹ •
            (A.comp (InnerProductSpace.rankOne Complex x x).toLinearMap)) := by
              congr 1
              ext y
              simp [LinearMap.comp_apply]
    _ = (inner Complex x x)⁻¹ * inner Complex x (A x) := by
      rw [map_smul, hComp, InnerProductSpace.trace_rankOne]
      simp [smul_eq_mul]

/-- Constant pure-state expectations on a nonzero code subspace give detectability. -/
theorem detectableOnWithScalar_of_quadratic_expectation
    {C : QuantumCode (Qudit.QuditRegister q)} {A : Operator (Qudit.QuditRegister q)}
    {alpha : Complex}
    (hQuadratic : ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
      inner Complex x (A x) = alpha * inner Complex x x) :
    DetectableOnWithScalar C A alpha := by
  intro x hx y hy
  have hConjugateQuadratic (z : Qudit.QuditRegister q) (hz : z ∈ C.carrier) :
      inner Complex (A z) z = star alpha * inner Complex z z := by
    calc
      inner Complex (A z) z = star (inner Complex z (A z)) := by
        exact (inner_conj_symm (𝕜 := Complex) (A z) z).symm
      _ = star (alpha * inner Complex z z) := by rw [hQuadratic z hz]
      _ = star alpha * inner Complex z z := by simp
  have hAdd : x + y ∈ C.carrier := C.carrier.add_mem hx hy
  have hSub : x - y ∈ C.carrier := C.carrier.sub_mem hx hy
  have hIAdd : x + Complex.I • y ∈ C.carrier := C.carrier.add_mem hx
    (C.carrier.smul_mem Complex.I hy)
  have hISub : x - Complex.I • y ∈ C.carrier := C.carrier.sub_mem hx
    (C.carrier.smul_mem Complex.I hy)
  have hScalarQuadratic (z : Qudit.QuditRegister q) :
      inner Complex (((alpha • (1 : Operator (Qudit.QuditRegister q))) z)) z =
        star alpha * inner Complex z z := by
    simp [mul_comm]
  have hPolarized : inner Complex (A y) x =
      inner Complex (((alpha • (1 : Operator (Qudit.QuditRegister q))) y)) x := by
    rw [inner_map_polarization A x y,
      inner_map_polarization (alpha • (1 : Operator (Qudit.QuditRegister q))) x y]
    rw [hConjugateQuadratic (x + y) hAdd,
      hConjugateQuadratic (x - y) hSub,
      hConjugateQuadratic (x + Complex.I • y) hIAdd,
      hConjugateQuadratic (x - Complex.I • y) hISub,
      hScalarQuadratic (x + y), hScalarQuadratic (x - y),
      hScalarQuadratic (x + Complex.I • y), hScalarQuadratic (x - Complex.I • y)]
  calc
    inner Complex x (A y) = star (inner Complex (A y) x) := by
      exact (inner_conj_symm (𝕜 := Complex) x (A y)).symm
    _ = star (inner Complex (((alpha • (1 : Operator (Qudit.QuditRegister q))) y)) x) := by
      rw [hPolarized]
    _ = alpha * inner Complex x y := by simp [mul_comm]

/-- Identity extension is complex-linear in the local operator. -/
theorem extendLocalToRegister_smul (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (a • A) = a • S.extendLocalToRegister A := by
  unfold extendLocalToRegister extendLocal
  rw [TensorProduct.map_smul_left]
  ext x
  simp [UnitaryTransport.conjOperator]

/-- Identity extension preserves local operator addition. -/
theorem extendLocalToRegister_add (S : QuditSubsystem q)
    (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A + B) =
      S.extendLocalToRegister A + S.extendLocalToRegister B := by
  unfold extendLocalToRegister extendLocal
  rw [TensorProduct.map_add_left]
  ext x
  simp [UnitaryTransport.conjOperator]

/-- Identity extension maps the zero local operator to zero. -/
theorem extendLocalToRegister_zero (S : QuditSubsystem q) :
    S.extendLocalToRegister (0 : Operator S.selectedSystem) = 0 := by
  unfold extendLocalToRegister extendLocal
  rw [TensorProduct.map_zero_left]
  simp [UnitaryTransport.conjOperator]

/-- Identity extension preserves finite sums of local operators. -/
theorem extendLocalToRegister_sum (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocalToRegister (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocalToRegister (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S.extendLocalToRegister_zero]
  | insert i s his ih =>
      calc
        S.extendLocalToRegister (∑ j ∈ insert i s, f j) =
            S.extendLocalToRegister (f i + ∑ j ∈ s, f j) := by
              rw [Finset.sum_insert his]
        _ = S.extendLocalToRegister (f i) +
            S.extendLocalToRegister (∑ j ∈ s, f j) :=
              S.extendLocalToRegister_add (f i) (∑ j ∈ s, f j)
        _ = S.extendLocalToRegister (f i) + ∑ j ∈ s,
            S.extendLocalToRegister (f j) := by rw [ih]
        _ = ∑ j ∈ insert i s, S.extendLocalToRegister (f j) := by
              rw [Finset.sum_insert his]

/-- Expand a finite-dimensional operator in the matrix units of an orthonormal basis. -/
theorem operator_eq_sum_rankOne_matrix_basis {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
      (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
  calc
    A = ∑ i : κ, (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap :=
      operator_eq_sum_rankOne_basis H b A
    _ = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
        (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          ext x
          simp only [LinearMap.sum_apply, LinearMap.smul_apply]
          change inner Complex (b i) x • A (b i) =
            ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j)
          calc
            inner Complex (b i) x • A (b i) = inner Complex (b i) x •
                ∑ j : κ, inner Complex (b j) (A (b i)) • b j := by
                  rw [b.sum_repr']
            _ = ∑ j : κ, inner Complex (b j) (A (b i)) •
                (inner Complex (b i) x • b j) := by
                  rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  simp [smul_smul, mul_comm]

/-- Effect-level no-information gives scalar compression of every local matrix unit. -/
theorem noInformationOn_rankOne_basis
    {C : QuantumCode (Qudit.QuditRegister q)} {S : QuditSubsystem q}
    (hInformation : NoInformationOn C S)
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex S.selectedSystem)
    (i j : κ) :
    ScalarCompression C
      (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) := by
  by_cases hij : i = j
  · subst j
    exact hInformation _ (validEffect_rankOne_basis_diagonal b i)
  · have hPlus : ScalarCompression C
        (S.extendLocalToRegister ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (b i + b j) (b i + b j)).toLinearMap)) :=
        hInformation _ (validEffect_half_rankOne_add b hij)
    have hPhase : ScalarCompression C
        (S.extendLocalToRegister ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
            (b i + Complex.I • b j)).toLinearMap)) :=
        hInformation _ (validEffect_half_rankOne_add_I_smul b hij)
    have hDiagonalI : ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap) :=
      hInformation _ (validEffect_rankOne_basis_diagonal b i)
    have hDiagonalJ : ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap) :=
      hInformation _ (validEffect_rankOne_basis_diagonal b j)
    have hPlus' : ScalarCompression C ((2 : Complex)⁻¹ •
        S.extendLocalToRegister
          (InnerProductSpace.rankOne Complex (b i + b j) (b i + b j)).toLinearMap) := by
      simpa only [S.extendLocalToRegister_smul] using hPlus
    have hPhase' : ScalarCompression C ((2 : Complex)⁻¹ •
        S.extendLocalToRegister
          (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
            (b i + Complex.I • b j)).toLinearMap) := by
      simpa only [S.extendLocalToRegister_smul] using hPhase
    have hPolarized := (hPlus'.add (hPhase'.smul Complex.I)).add
      ((hDiagonalI.add hDiagonalJ).smul (-(1 + Complex.I) * (2 : Complex)⁻¹))
    rw [rankOne_basis_polarization]
    rw [sub_eq_add_neg]
    rw [S.extendLocalToRegister_add, S.extendLocalToRegister_add]
    rw [S.extendLocalToRegister_smul, S.extendLocalToRegister_smul]
    rw [show -(((1 + Complex.I) * (2 : Complex)⁻¹) •
        ((InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
          (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap)) =
        (-(1 + Complex.I) * (2 : Complex)⁻¹) •
          ((InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
            (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap) by module]
    have hDiagonalSum :
        S.extendLocalToRegister
          ((-(1 + Complex.I) * (2 : Complex)⁻¹) •
            ((InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
              (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap)) =
          (-(1 + Complex.I) * (2 : Complex)⁻¹) •
            (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap +
              S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap) := by
      rw [S.extendLocalToRegister_smul]
      rw [S.extendLocalToRegister_add]
    have hPhaseTerm :
        S.extendLocalToRegister ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
            (b i + Complex.I • b j)).toLinearMap) =
          (2 : Complex)⁻¹ • S.extendLocalToRegister
            (InnerProductSpace.rankOne Complex (b i + Complex.I • b j)
              (b i + Complex.I • b j)).toLinearMap :=
      S.extendLocalToRegister_smul _ _
    rw [hPhaseTerm, hDiagonalSum]
    exact hPolarized

/-- Valid-effect no-information is equivalent to scalar compression for all local operators. -/
theorem noInformationOn_iff_allLocalScalarCompression
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S ↔ AllLocalScalarCompression C S := by
  constructor
  · intro hInformation A
    let b := stdOrthonormalBasis Complex S.selectedSystem
    rw [operator_eq_sum_rankOne_matrix_basis b A]
    rw [S.extendLocalToRegister_sum Finset.univ]
    apply ScalarCompression.sum
    intro i
    rw [S.extendLocalToRegister_sum Finset.univ]
    apply ScalarCompression.sum
    intro j
    rw [S.extendLocalToRegister_smul]
    exact (noInformationOn_rankOne_basis hInformation b j i).smul
      (inner Complex (b j) (A (b i)))
  · intro hAll E _
    exact hAll E

/-- Scalar compression of a local matrix-unit basis extends to all local operators. -/
theorem allLocalScalarCompression_of_rankOne_basis
    {C : QuantumCode (Qudit.QuditRegister q)} {S : QuditSubsystem q}
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex S.selectedSystem)
    (hRankOne : ∀ i j : κ,
      ScalarCompression C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap)) :
    AllLocalScalarCompression C S := by
  intro A
  rw [operator_eq_sum_rankOne_matrix_basis b A]
  rw [S.extendLocalToRegister_sum Finset.univ]
  apply ScalarCompression.sum
  intro i
  rw [S.extendLocalToRegister_sum Finset.univ]
  apply ScalarCompression.sum
  intro j
  rw [S.extendLocalToRegister_smul]
  exact (hRankOne j i).smul (inner Complex (b j) (A (b i)))

/--
All normalized finite POVMs on `S` have state-independent outcome traces on
encoded density operators.  The finite-POVM premise contains both effect
validity and the normalization equation.
-/
def FinitePOVMDistributionInvariant (C : QuantumCode (Qudit.QuditRegister q))
    (S : QuditSubsystem q) : Prop :=
  ∀ (m : Type v) (_ : Fintype m) (effects : m → Operator S.selectedSystem),
    FinitePOVM effects →
      ∀ i : m, ∀ rho sigma : DensityOperator (Qudit.QuditRegister q),
        DensityOperator.SupportedOn C rho → DensityOperator.SupportedOn C sigma →
          LinearMap.trace Complex (Qudit.QuditRegister q)
              ((S.extendLocalToRegister (effects i)).comp rho.toOperator) =
            LinearMap.trace Complex (Qudit.QuditRegister q)
              ((S.extendLocalToRegister (effects i)).comp sigma.toOperator)

/-- A nonzero code carrier contains a nonzero ambient code vector. -/
theorem exists_nonzero_codeword
    (C : QuantumCode (Qudit.QuditRegister q)) (hC : C.carrier ≠ ⊥) :
    ∃ x : Qudit.QuditRegister q, x ∈ C.carrier ∧ x ≠ 0 := by
  rcases Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hC) with ⟨x, hx⟩
  exact ⟨x, x.property, fun hzero => hx (Subtype.ext hzero)⟩

/-- No-information makes every valid finite-POVM outcome distribution-independent. -/
theorem noInformationOn_implies_finitePOVMDistributionInvariant
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S → FinitePOVMDistributionInvariant.{u, v} C S := by
  intro hInformation m _ effects hPOVM i rho sigma hRho hSigma
  rcases hInformation (effects i) (hPOVM.1 i) with ⟨alpha, hAlpha⟩
  exact (trace_comp_eq_scalar_of_scalarCompression hAlpha rho hRho).trans
    (trace_comp_eq_scalar_of_scalarCompression hAlpha sigma hSigma).symm

/-- A code with bottom carrier has zero projector and therefore no local information. -/
theorem noInformationOn_of_carrier_eq_bot
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (hC : C.carrier = ⊥) : NoInformationOn C S := by
  intro E _
  refine ⟨0, ?_⟩
  have hProjector : C.projector = 0 := by
    apply LinearMap.ext
    intro x
    have hx := C.projector_mem_carrier x
    rw [hC] at hx
    simpa using hx
  simp [hProjector]

/-- Every operator has scalar compression to a nonzero one-dimensional code carrier. -/
theorem scalarCompression_of_carrier_eq_span_singleton
    (C : QuantumCode (Qudit.QuditRegister q)) (v : Qudit.QuditRegister q)
    (hv : v ≠ 0) (hC : C.carrier = Complex ∙ v)
    (A : Operator (Qudit.QuditRegister q)) : ScalarCompression C A := by
  rw [scalarCompression_iff_detectableOn]
  refine ⟨(inner Complex v (A v)) / inner Complex v v, ?_⟩
  intro x hx y hy
  rw [hC] at hx hy
  rcases (Submodule.mem_span_singleton.mp hx) with ⟨a, ha⟩
  rcases (Submodule.mem_span_singleton.mp hy) with ⟨b, hb⟩
  rw [← ha, ← hb]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  field_simp [inner_self_ne_zero.mpr hv]

/-- A nonzero one-dimensional code reveals no information to any local valid effect. -/
theorem noInformationOn_of_carrier_eq_span_singleton
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (v : Qudit.QuditRegister q) (hv : v ≠ 0) (hC : C.carrier = Complex ∙ v) :
    NoInformationOn C S := by
  intro E _
  exact scalarCompression_of_carrier_eq_span_singleton C v hv hC
    (S.extendLocalToRegister E)

/-- On a nonzero code carrier, finite-POVM distribution invariance gives no-information. -/
theorem finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q)
    (hC : C.carrier ≠ ⊥) :
    FinitePOVMDistributionInvariant.{u, v} C S → NoInformationOn C S := by
  intro hDistribution E hE
  let effects : ULift.{v} Bool → Operator S.selectedSystem :=
    fun b => if b.down then E else 1 - E
  have hPOVM : FinitePOVM effects := by
    constructor
    · intro b
      rcases b with ⟨b⟩
      cases b with
      | false =>
          dsimp [effects]
          refine ⟨hE.2, ?_⟩
          convert hE.1 using 1; module
      | true => simpa [effects] using hE
    · let e : ULift.{v} Bool ≃ Bool := Equiv.ulift
      rw [Fintype.sum_equiv e effects
        (fun b : Bool => if b then E else 1 - E) (by intro b; rfl)]
      rw [Fintype.sum_bool]
      simp
  rcases exists_nonzero_codeword C hC with ⟨r, hrC, hr0⟩
  let A : Operator (Qudit.QuditRegister q) := S.extendLocalToRegister E
  let alpha : Complex := LinearMap.trace Complex (Qudit.QuditRegister q)
    (A.comp (DensityOperator.pureOfNonzero r hr0).toOperator)
  have hQuadratic : ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
      inner Complex x (A x) = alpha * inner Complex x x := by
    intro x hxC
    by_cases hx0 : x = 0
    · subst x
      simp
    · have hInvariant := hDistribution (ULift.{v} Bool) inferInstance effects hPOVM ⟨true⟩
        (DensityOperator.pureOfNonzero x hx0) (DensityOperator.pureOfNonzero r hr0)
        (DensityOperator.pureOfNonzero_supportedOn hx0 hxC)
        (DensityOperator.pureOfNonzero_supportedOn hr0 hrC)
      have hRayleigh : (inner Complex x x)⁻¹ * inner Complex x (A x) = alpha := by
        calc
          (inner Complex x x)⁻¹ * inner Complex x (A x) =
              LinearMap.trace Complex (Qudit.QuditRegister q)
                (A.comp (DensityOperator.pureOfNonzero x hx0).toOperator) := by
                  symm
                  exact trace_comp_pureOfNonzero A x hx0
          _ = LinearMap.trace Complex (Qudit.QuditRegister q)
                (A.comp (DensityOperator.pureOfNonzero r hr0).toOperator) := by
                  simpa [A, effects] using hInvariant
          _ = alpha := rfl
      rw [← hRayleigh]
      field_simp [inner_self_ne_zero.mpr hx0]
  rw [scalarCompression_iff_detectableOn]
  exact ⟨alpha, detectableOnWithScalar_of_quadratic_expectation hQuadratic⟩

/-- Effect-level no-information is equivalent to finite-POVM distribution invariance. -/
theorem noInformationOn_iff_finitePOVMDistributionInvariant
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S ↔ FinitePOVMDistributionInvariant.{u, v} C S := by
  constructor
  · exact noInformationOn_implies_finitePOVMDistributionInvariant C S
  · intro hDistribution
    by_cases hC : C.carrier = ⊥
    · exact noInformationOn_of_carrier_eq_bot C S hC
    · exact finitePOVMDistributionInvariant_implies_noInformationOn_of_nonzero C S hC
        hDistribution

/-- Factorized local extension is complex-linear in the selected operator. -/
theorem extendLocal_smul (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocal (a • A) = a • S.extendLocal A := by
  unfold extendLocal
  rw [TensorProduct.map_smul_left]

/-- Factorized local extension preserves addition. -/
theorem extendLocal_add (S : QuditSubsystem q)
    (A B : Operator S.selectedSystem) :
    S.extendLocal (A + B) = S.extendLocal A + S.extendLocal B := by
  unfold extendLocal
  rw [TensorProduct.map_add_left]

/-- Factorized local extension maps zero to zero. -/
theorem extendLocal_zero (S : QuditSubsystem q) :
    S.extendLocal (0 : Operator S.selectedSystem) = 0 := by
  unfold extendLocal
  rw [TensorProduct.map_zero_left]

/-- Factorized local extension preserves finite sums. -/
theorem extendLocal_sum (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocal (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S.extendLocal_zero]
  | insert i s his ih =>
      rw [Finset.sum_insert his, S.extendLocal_add, ih, Finset.sum_insert his]

/-- Extending the local identity is the factorized identity. -/
theorem extendLocal_one (S : QuditSubsystem q) :
    S.extendLocal (1 : Operator S.selectedSystem) = 1 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k => simp [S.extendLocal_apply_tmul]
  | add x y hx hy => simp [hx, hy]

/- The adjoint preparation branch contracts its selected tensor factor. -/
set_option maxHeartbeats 800000 in
theorem adjoint_prepareFactorizedBranch_apply_tmul (S : QuditSubsystem q)
    (u h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.prepareFactorizedBranch u) (h ⊗ₜ[Complex] k) =
      (inner Complex u h) • k := by
  apply (ext_iff_inner_left Complex).mpr
  intro l
  rw [LinearMap.adjoint_inner_right]
  simp [S.prepareFactorizedBranch_apply, TensorProduct.inner_tmul,
    inner_smul_right]

/-- A preparation branch followed by its adjoint is the corresponding local matrix unit. -/
theorem prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
    (S : QuditSubsystem q) (u v : S.selectedSystem) :
    (S.prepareFactorizedBranch u).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch v)) =
      S.extendLocal (InnerProductSpace.rankOne Complex u v).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      rw [LinearMap.comp_apply, S.adjoint_prepareFactorizedBranch_apply_tmul,
        S.prepareFactorizedBranch_apply, S.extendLocal_apply_tmul]
      simp [InnerProductSpace.rankOne_apply, TensorProduct.smul_tmul']
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

/-- Preparation branches for an orthonormal basis resolve the factorized identity. -/
theorem sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
    (S : QuditSubsystem q) {κ : Type v} [Fintype κ]
    (b : OrthonormalBasis κ Complex S.selectedSystem) :
    ∑ a : κ, (S.prepareFactorizedBranch (b a)).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch (b a))) = 1 := by
  calc
    ∑ a : κ, (S.prepareFactorizedBranch (b a)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch (b a))) =
        ∑ a : κ, S.extendLocal
          (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro a _
            exact S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch (b a) (b a)
    _ = S.extendLocal (∑ a : κ,
        (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) := by
          symm
          simpa using S.extendLocal_sum (Finset.univ : Finset κ)
            (fun a => (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap)
    _ = S.extendLocal 1 := by
          congr 1
          change (∑ a : κ,
            (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) = LinearMap.id
          simpa using congrArg ContinuousLinearMap.toLinearMap
            (OrthonormalBasis.sum_rankOne_eq_id b)
    _ = 1 := S.extendLocal_one

/- The preparation-branch overlap is the selected-vector inner product. -/
set_option maxHeartbeats 800000 in
theorem adjoint_prepareFactorizedBranch_comp_cross (S : QuditSubsystem q)
    (u v : S.selectedSystem) :
    (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
      (S.prepareFactorizedBranch v) =
      (inner Complex u v) • (1 : Operator S.complementSystem) := by
  apply LinearMap.ext
  intro k
  apply (ext_iff_inner_left Complex).mpr
  intro l
  change inner Complex l (LinearMap.adjoint (S.prepareFactorizedBranch u)
    (S.prepareFactorizedBranch v k)) =
      inner Complex l (((inner Complex u v) • (1 : Operator S.complementSystem)) k)
  rw [LinearMap.adjoint_inner_right]
  simp [S.prepareFactorizedBranch_apply, TensorProduct.inner_tmul]

/--
The finite replacement family: erase against a selected orthonormal basis, then
prepare one density-ensemble branch on the selected factor.
-/
noncomputable def replacementFactorizedKraus (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    FiniteKrausFamily
      (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem))
      S.factorizedSystem S.factorizedSystem := by
  let b : OrthonormalBasis (Fin (Module.finrank Complex S.selectedSystem)) Complex S.selectedSystem :=
    stdOrthonormalBasis Complex S.selectedSystem
  exact {
    operator := fun p =>
      (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch (b p.2))) }

@[simp]
theorem replacementFactorizedKraus_operator (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (S.replacementFactorizedKraus rho).operator p =
      (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2))) :=
  rfl

/-- Cross products of replacement branches are selected local matrix units. -/
theorem replacementFactorizedKraus_adjoint_comp (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator p)).comp
      ((S.replacementFactorizedKraus rho).operator r) =
      (inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by
  rw [S.replacementFactorizedKraus_operator, S.replacementFactorizedKraus_operator]
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.adjoint_adjoint]
  calc
    ((S.prepareFactorizedBranch
        ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)))).comp
      ((S.prepareFactorizedBranch (S.densityEnsembleVectors rho r.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) =
        (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
          (((LinearMap.adjoint (S.prepareFactorizedBranch
            (S.densityEnsembleVectors rho p.1))).comp
            (S.prepareFactorizedBranch (S.densityEnsembleVectors rho r.1))).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch
              ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) := by
                rfl
    _ = (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
          (((inner Complex (S.densityEnsembleVectors rho p.1)
            (S.densityEnsembleVectors rho r.1)) • (1 : Operator S.complementSystem)).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch
              ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) := by
                rw [S.adjoint_prepareFactorizedBranch_comp_cross]
    _ = (inner Complex (S.densityEnsembleVectors rho p.1)
          (S.densityEnsembleVectors rho r.1)) •
        ((S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
          (LinearMap.adjoint (S.prepareFactorizedBranch
            ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) := by
              ext x
              simp [LinearMap.comp_apply]
    _ = (inner Complex (S.densityEnsembleVectors rho p.1)
          (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by
              rw [S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch]

/-- The explicit replacement family is complete. -/
theorem replacementFactorizedKraus_complete (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementFactorizedKraus rho).Complete := by
  have hBasisIdentity :
      ∑ a : Fin (Module.finrank Complex S.selectedSystem),
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) a)
          ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap = 1 := by
    calc
      ∑ a : Fin (Module.finrank Complex S.selectedSystem),
          S.extendLocal (InnerProductSpace.rankOne Complex
            ((stdOrthonormalBasis Complex S.selectedSystem) a)
            ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap =
          ∑ a : Fin (Module.finrank Complex S.selectedSystem),
            (S.prepareFactorizedBranch
              ((stdOrthonormalBasis Complex S.selectedSystem) a)).comp
              (LinearMap.adjoint (S.prepareFactorizedBranch
                ((stdOrthonormalBasis Complex S.selectedSystem) a))) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  symm
                  exact S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
                    ((stdOrthonormalBasis Complex S.selectedSystem) a)
                    ((stdOrthonormalBasis Complex S.selectedSystem) a)
      _ = 1 := S.sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
        (stdOrthonormalBasis Complex S.selectedSystem)
  rw [FiniteKrausFamily.Complete, Fintype.sum_prod_type]
  calc
    ∑ i : Fin (S.densityEnsembleSize rho),
        ∑ a : Fin (Module.finrank Complex S.selectedSystem),
          (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator (i, a))).comp
            ((S.replacementFactorizedKraus rho).operator (i, a)) =
        ∑ i : Fin (S.densityEnsembleSize rho),
          ∑ a : Fin (Module.finrank Complex S.selectedSystem),
            (inner Complex (S.densityEnsembleVectors rho i)
              (S.densityEnsembleVectors rho i)) •
              S.extendLocal (InnerProductSpace.rankOne Complex
                ((stdOrthonormalBasis Complex S.selectedSystem) a)
                ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap := by
                  apply Finset.sum_congr rfl
                  intro i _
                  apply Finset.sum_congr rfl
                  intro a _
                  exact S.replacementFactorizedKraus_adjoint_comp rho (i, a) (i, a)
    _ = ∑ i : Fin (S.densityEnsembleSize rho),
          (inner Complex (S.densityEnsembleVectors rho i)
            (S.densityEnsembleVectors rho i)) •
            (∑ a : Fin (Module.finrank Complex S.selectedSystem),
              S.extendLocal (InnerProductSpace.rankOne Complex
                ((stdOrthonormalBasis Complex S.selectedSystem) a)
                ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.smul_sum]
    _ = ∑ i : Fin (S.densityEnsembleSize rho),
          (inner Complex (S.densityEnsembleVectors rho i)
            (S.densityEnsembleVectors rho i)) • (1 : Operator S.factorizedSystem) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [hBasisIdentity]
    _ = 1 := by
      apply LinearMap.ext
      intro x
      calc
        (∑ i : Fin (S.densityEnsembleSize rho),
            (inner Complex (S.densityEnsembleVectors rho i)
              (S.densityEnsembleVectors rho i)) • (1 : Operator S.factorizedSystem)) x =
            (∑ i : Fin (S.densityEnsembleSize rho),
              inner Complex (S.densityEnsembleVectors rho i)
                (S.densityEnsembleVectors rho i)) • x := by
                  simp [Finset.sum_smul]
        _ = x := by rw [S.densityEnsemble_trace_one rho]; simp

/-- A replacement branch selects exactly its matching selected basis component. -/
theorem replacementFactorizedKraus_operator_apply_basis_tmul (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem))
    (a : Fin (Module.finrank Complex S.selectedSystem)) (k : S.complementSystem) :
    (S.replacementFactorizedKraus rho).operator p
      (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k) =
      if p.2 = a then (S.densityEnsembleVectors rho p.1) ⊗ₜ[Complex] k else 0 := by
  rw [S.replacementFactorizedKraus_operator, LinearMap.comp_apply,
    S.adjoint_prepareFactorizedBranch_apply_tmul,
    S.prepareFactorizedBranch_apply]
  by_cases hpa : p.2 = a
  · subst a
    simp
  · rw [(stdOrthonormalBasis Complex S.selectedSystem).orthonormal.inner_eq_zero hpa]
    simp [hpa]

/-- A Kraus sandwich maps a rank-one operator to the rank one of its images. -/
theorem comp_rankOne_comp_adjoint (S : QuditSubsystem q)
    (K : Operator S.factorizedSystem) (x y : S.factorizedSystem) :
    K.comp ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp
      (LinearMap.adjoint K)) =
      (InnerProductSpace.rankOne Complex (K x) (K y)).toLinearMap := by
  ext z
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

/-- The replacement family has the expected action on product-basis matrix units. -/
theorem replacementFactorizedKraus_inducedMap_rankOne_tmul
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (a b : Fin (Module.finrank Complex S.selectedSystem))
    (k l : S.complementSystem) :
    (S.replacementFactorizedKraus rho).inducedMap
      (InnerProductSpace.rankOne Complex
        (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
        (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap =
  if a = b then ∑ i : Fin (S.densityEnsembleSize rho),
        (InnerProductSpace.rankOne Complex
          ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] k)
          ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] l)).toLinearMap else 0 := by
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_prod_type]
  have hExpand :
      (∑ i : Fin (S.densityEnsembleSize rho),
        ∑ r : Fin (Module.finrank Complex S.selectedSystem),
          ((S.replacementFactorizedKraus rho).operator (i, r)).comp
            ((InnerProductSpace.rankOne Complex
              (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
              (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap.comp
                (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator (i, r))))) =
        ∑ i : Fin (S.densityEnsembleSize rho),
          ∑ r : Fin (Module.finrank Complex S.selectedSystem),
            (InnerProductSpace.rankOne Complex
              ((S.replacementFactorizedKraus rho).operator (i, r)
                (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k))
              ((S.replacementFactorizedKraus rho).operator (i, r)
                (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l))).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro r _
          exact S.comp_rankOne_comp_adjoint _ _ _
  rw [hExpand]
  simp_rw [S.replacementFactorizedKraus_operator_apply_basis_tmul]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single a]
    · simp
    · intro r _ hra
      have hne : r ≠ a := fun h => hra h
      rw [if_neg hne, if_neg hne]
      apply LinearMap.ext
      intro z
      change inner Complex (0 : S.factorizedSystem) z • (0 : S.factorizedSystem) = 0
      simp
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  · simp only [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro r _
    by_cases hra : r = a
    · subst r
      rw [if_pos rfl, if_neg hab]
      apply LinearMap.ext
      intro z
      change inner Complex (0 : S.factorizedSystem) z •
        ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] k) = 0
      simp
    · rw [if_neg hra]
      apply LinearMap.ext
      intro z
      change inner Complex
        (if r = b then (S.densityEnsembleVectors rho i) ⊗ₜ[Complex] l else 0) z •
          (0 : S.factorizedSystem) = 0
      simp

/-- The concrete factored erasure channel contracts the selected tensor factor. -/
theorem erasureChannel_rankOne_tmul (S : QuditSubsystem q)
    (h h' : S.selectedSystem) (k k' : S.complementSystem) :
    S.erasureChannel
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by
  simp only [erasureChannel, QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [conjOperator_rankOne S.factorSwap]
  simp only [S.factorSwap_apply_tmul]
  exact partialTraceRightRaw_rankOne_tmul S.complementSystem S.selectedSystem k k' h h'

/-- The explicit replacement family agrees with preparation after concrete factored erasure. -/
theorem replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (a b : Fin (Module.finrank Complex S.selectedSystem))
    (k l : S.complementSystem) :
    (S.replacementFactorizedKraus rho).inducedMap
      (InnerProductSpace.rankOne Complex
        (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
        (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap =
      S.prepareFactorized rho
        (S.erasureChannel
          (InnerProductSpace.rankOne Complex
            (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
            (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap) := by
  by_cases hab : a = b
  · subst b
    rw [S.replacementFactorizedKraus_inducedMap_rankOne_tmul]
    rw [S.erasureChannel_rankOne_tmul]
    simp
    exact (S.prepareFactorized_apply_rankOne rho k l).symm
  · rw [S.replacementFactorizedKraus_inducedMap_rankOne_tmul]
    simp only [if_neg hab]
    rw [S.erasureChannel_rankOne_tmul]
    rw [(stdOrthonormalBasis Complex S.selectedSystem).orthonormal.inner_eq_zero (Ne.symm hab)]
    simp

/-- The raw induced map of the explicit family is preparation after factored erasure. -/
theorem replacementFactorizedKraus_inducedMap_eq_replacement (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementFactorizedKraus rho).inducedMap =
      (QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel).toLinearMap := by
  apply linearMap_ext_of_rankOne_basis
    ((stdOrthonormalBasis Complex S.selectedSystem).tensorProduct
      (stdOrthonormalBasis Complex S.complementSystem))
    (S.replacementFactorizedKraus rho).inducedMap
    (QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel).toLinearMap
  intro x y
  rcases x with ⟨a, k⟩
  rcases y with ⟨b, l⟩
  simp only [OrthonormalBasis.tensorProduct_apply', QuantumChannel.comp_apply]
  exact S.replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement rho a b
    ((stdOrthonormalBasis Complex S.complementSystem) k)
    ((stdOrthonormalBasis Complex S.complementSystem) l)

/-- The complete explicit replacement family packages the factorized replacement channel. -/
theorem replacementFactorizedKraus_toQuantumChannel_eq_replacement (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (hComplete : (S.replacementFactorizedKraus rho).Complete) :
    (S.replacementFactorizedKraus rho).toQuantumChannel hComplete =
      QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel := by
  apply quantumChannel_ext
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  exact S.replacementFactorizedKraus_inducedMap_eq_replacement rho

/-- The explicit replacement family transported back to the global qudit register. -/
noncomputable def replacementKraus (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    FiniteKrausFamily
      (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem))
      (Qudit.QuditRegister q) (Qudit.QuditRegister q) :=
  (S.replacementFactorizedKraus rho).unitaryTransport
    S.registerFactorization.symm S.registerFactorization.symm

/-- The global transported replacement family remains complete. -/
theorem replacementKraus_complete (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementKraus rho).Complete :=
  (S.replacementFactorizedKraus rho).unitaryTransport_complete
    S.registerFactorization.symm S.registerFactorization.symm
    (S.replacementFactorizedKraus_complete rho)

/- Cross products of global replacement branches are concrete global local matrix units. -/
set_option maxHeartbeats 800000 in
theorem replacementKraus_adjoint_comp (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
      ((S.replacementKraus rho).operator r) =
      (inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by
  let U := S.registerFactorization.symm
  have hFactor := S.replacementFactorizedKraus_adjoint_comp rho p r
  apply LinearMap.ext
  intro x
  calc
    ((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
        ((S.replacementKraus rho).operator r)) x =
        U (((LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator p)).comp
          ((S.replacementFactorizedKraus rho).operator r)) (U.symm x)) := by
            simp [replacementKraus, U, FiniteKrausFamily.unitaryTransport,
              LinearMap.comp_apply,
              S.registerFactorization.adjoint_toLinearMap,
              S.registerFactorization.adjoint_symm_toLinearMap]
    _ = U (((inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap) (U.symm x)) := by
            rw [hFactor]
    _ = ((inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap) x := by
            simp [U, extendLocalToRegister, UnitaryTransport.conjOperator]

/- The complete global replacement family induces the concrete replacement-after-erasure channel. -/
set_option maxRecDepth 4096 in
theorem replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (hComplete : (S.replacementKraus rho).Complete) :
    (S.replacementKraus rho).toQuantumChannel hComplete =
      S.replacementAfterErasureWith rho := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  rw [replacementKraus, FiniteKrausFamily.unitaryTransport_inducedMap_apply]
  rw [S.replacementFactorizedKraus_inducedMap_eq_replacement]
  change S.registerFactorization.symm.conjOperator
      ((QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel)
        (S.registerFactorization.conjOperator A)) =
    S.registerFactorization.symm.conjOperator
      (S.prepareFactorized rho
        (S.erasureChannel (S.registerFactorization.conjOperator A)))
  rfl

/-- Local scalar compression supplies the matrix-element KL equations for the explicit replacement family. -/
theorem replacementKraus_matrixElementKL_of_allLocalScalarCompression
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hLocal : AllLocalScalarCompression C S) :
    ∃ scalar :
        (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
          (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
            Complex,
      ∀ p r,
        ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
          ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
            inner Complex ((S.replacementKraus rho).operator p x)
              ((S.replacementKraus rho).operator r y) =
              scalar p r * inner Complex x y := by
  have hProduct (p r :
      Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
      ScalarCompression C
        ((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
          ((S.replacementKraus rho).operator r)) := by
    rw [S.replacementKraus_adjoint_comp rho p r]
    exact (hLocal _).smul _
  choose scalar hScalar using fun p r =>
    (scalarCompression_iff_detectableOn C _).mp (hProduct p r)
  refine ⟨scalar, ?_⟩
  intro p r x hx y hy
  calc
    inner Complex ((S.replacementKraus rho).operator p x)
        ((S.replacementKraus rho).operator r y) =
        inner Complex x
          (((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
            ((S.replacementKraus rho).operator r)) y) := by
              simpa [LinearMap.comp_apply] using
                (LinearMap.adjoint_inner_right (𝕜 := Complex)
                  ((S.replacementKraus rho).operator p) x
                  ((S.replacementKraus rho).operator r y)).symm
    _ = scalar p r * inner Complex x y := hScalar p r x hx y hy

/-- No local information yields a CPTP recovery for any normalized replacement-after-erasure channel. -/
theorem noInformationOn_implies_replacementAfterErasureWith_recovery
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hInformation : NoInformationOn C S) :
    ∃ recovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasureWith rho) recovery := by
  let E := S.replacementKraus rho
  have hComplete : E.Complete := S.replacementKraus_complete rho
  have hKL := S.replacementKraus_matrixElementKL_of_allLocalScalarCompression C rho
    ((S.noInformationOn_iff_allLocalScalarCompression C).mp hInformation)
  rcases (FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
    E C hComplete).mp hKL with ⟨recovery, hRecovery⟩
  refine ⟨recovery, ?_⟩
  intro sigma hSupported
  rw [← S.replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith rho hComplete]
  exact hRecovery sigma hSupported

/-- No local information yields recovery from the concrete coordinate-erasure channel. -/
theorem noInformationOn_implies_erasureRecovery
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (hInformation : NoInformationOn C S) :
    ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  rcases S.noInformationOn_implies_replacementAfterErasureWith_recovery C rho hInformation
    with ⟨replacementRecovery, hReplacement⟩
  exact ⟨QuantumChannel.comp replacementRecovery (S.prepareSelected rho),
    S.replacementRecovery_transfers_to_erasure rho C replacementRecovery hReplacement⟩

/-- A matrix-element KL equation gives scalar compression of the corresponding Kraus product. -/
theorem scalarCompression_of_replacementKraus_matrixElement
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    {scalar :
        (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
          (Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) →
            Complex}
    (hMatrix : ∀ p r,
      ∀ x : Qudit.QuditRegister q, x ∈ C.carrier →
        ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
          inner Complex ((S.replacementKraus rho).operator p x)
            ((S.replacementKraus rho).operator r y) =
            scalar p r * inner Complex x y)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    ScalarCompression C
      ((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
        ((S.replacementKraus rho).operator r)) := by
  rw [scalarCompression_iff_detectableOn]
  refine ⟨scalar p r, ?_⟩
  intro x hx y hy
  calc
    inner Complex x
        (((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
          ((S.replacementKraus rho).operator r)) y) =
        inner Complex ((S.replacementKraus rho).operator p x)
          ((S.replacementKraus rho).operator r y) := by
            simpa [LinearMap.comp_apply] using
              (LinearMap.adjoint_inner_right (𝕜 := Complex)
                ((S.replacementKraus rho).operator p) x
                ((S.replacementKraus rho).operator r y))
    _ = scalar p r * inner Complex x y := hMatrix p r x hx y hy

/-- A normalized finite rank-one ensemble contains a nonzero branch. -/
theorem densityEnsembleVectors_exists_ne_zero (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    ∃ i : Fin (S.densityEnsembleSize rho), S.densityEnsembleVectors rho i ≠ 0 := by
  by_contra h
  push Not at h
  have hSum : ∑ i, inner Complex (S.densityEnsembleVectors rho i)
      (S.densityEnsembleVectors rho i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [h i]
    simp
  have hTrace := S.densityEnsemble_trace_one rho
  rw [hSum] at hTrace
  norm_num at hTrace

/-- A concrete erasure recovery makes every local valid effect information-free on the code. -/
theorem erasureRecovery_implies_noInformationOn
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (rho : DensityOperator S.selectedSystem)
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hRecovery : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    NoInformationOn C S := by
  let E := S.replacementKraus rho
  have hComplete : E.Complete := S.replacementKraus_complete rho
  let replacementRecovery := QuantumChannel.comp recovery S.erasureChannelFromRegister
  have hReplacement : Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho) replacementRecovery :=
    S.erasureRecovery_transfers_to_replacement rho C recovery hRecovery
  have hKrausRecovery :
      ∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
        ∀ sigma : DensityOperator (Qudit.QuditRegister q),
          DensityOperator.SupportedOn C sigma →
            replacementRecovery (E.inducedMap sigma.toOperator) = sigma.toOperator := by
    refine ⟨replacementRecovery, ?_⟩
    intro sigma hSupported
    have hCorrected := hReplacement sigma hSupported
    rw [← S.replacementKraus_toQuantumChannel_eq_replacementAfterErasureWith rho hComplete]
      at hCorrected
    exact hCorrected
  have hMatrix :=
    (FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
      E C hComplete).mpr hKrausRecovery
  rcases hMatrix with ⟨scalar, hMatrix⟩
  rcases S.densityEnsembleVectors_exists_ne_zero rho with ⟨i0, hi0⟩
  apply (S.noInformationOn_iff_allLocalScalarCompression C).mpr
  apply allLocalScalarCompression_of_rankOne_basis
    (C := C) (S := S) (stdOrthonormalBasis Complex S.selectedSystem)
  intro i j
  have hProduct := S.scalarCompression_of_replacementKraus_matrixElement C rho hMatrix
    (i0, i) (i0, j)
  rw [S.replacementKraus_adjoint_comp rho] at hProduct
  exact hProduct.of_smul (inner_self_ne_zero.mpr hi0)

/--
For strictly positive finite local dimensions, local measurement
indistinguishability is exactly correctability of the concrete register erasure
channel.  This is an internal bridge theorem, not a BPT tradeoff statement.
-/
theorem noInformationOn_iff_exists_erasureRecovery
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (hq : ∀ i, 0 < q i) :
    NoInformationOn C S ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery := by
  let rho := S.maximallyMixedSelected hq
  constructor
  · intro hInformation
    exact S.noInformationOn_implies_erasureRecovery C rho hInformation
  · rintro ⟨recovery, hRecovery⟩
    exact S.erasureRecovery_implies_noInformationOn C rho recovery hRecovery

/-- The BPT measurement-distance convention for finite regions. -/
def BPTMeasurementDistance (C : QuantumCode (Qudit.QuditRegister q)) (d : Nat) : Prop :=
  ∀ S : QuditSubsystem q, Fintype.card S.SelectedCoordinates < d → NoInformationOn C S

/-- The direct strict-cardinality consequence of the BPT measurement-distance predicate. -/
theorem BPTMeasurementDistance.noInformationOn_of_card_lt
    {C : QuantumCode (Qudit.QuditRegister q)} {d : Nat}
    (hDistance : BPTMeasurementDistance C d) (S : QuditSubsystem q)
    (hcard : Fintype.card S.SelectedCoordinates < d) :
    NoInformationOn C S :=
  hDistance S hcard

end QuditSubsystem

end Semantics
end QEC
