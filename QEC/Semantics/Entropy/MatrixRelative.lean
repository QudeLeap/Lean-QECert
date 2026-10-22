import QEC.Semantics.Entropy.FiniteDimensional
import QEC.Locality.CorrectableRegions.LocalPauliErasureTransfer
/-!
# Finite-matrix relative entropy foundations

This module develops the finite-dimensional matrix ingredients used by the
generic entropy-subadditivity integration node.  Matrix logarithms are defined
through Mathlib's Hermitian functional calculus; in particular, no
simultaneous-diagonalization hypothesis is made for the two matrices in the
Klein inequality.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder Kronecker TensorProduct

noncomputable section

namespace FiniteMatrixEntropy

/-- Natural-log functional calculus of a finite Hermitian matrix. -/
def logMatrix {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) : Matrix n n Complex :=
  hA.cfc Real.log

/-- Base-two-log functional calculus of a finite Hermitian matrix. -/
def log2Matrix {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) : Matrix n n Complex :=
  hA.cfc (Real.logb 2)

/-- The real trace pairing used for finite matrix relative entropy. -/
def realTrace {n : Type u} [Fintype n] (A : Matrix n n Complex) : Real :=
  Complex.re A.trace

/-- Natural-log finite quantum relative entropy for Hermitian matrices. -/
def relativeEntropy {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) : Real :=
  realTrace (A * (logMatrix A hA - logMatrix B hB))

/-- Base-two finite quantum relative entropy for Hermitian matrices. -/
def relativeEntropy2 {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) : Real :=
  realTrace (A * (log2Matrix A hA - log2Matrix B hB))

@[simp]
theorem logMatrix_apply {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    logMatrix A hA = hA.cfc Real.log :=
  rfl

@[simp]
theorem log2Matrix_apply {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    log2Matrix A hA = hA.cfc (Real.logb 2) :=
  rfl

/-- The scalar Klein inequality in the form used after spectral expansion. -/
theorem scalar_klein_log {a b : Real} (ha : 0 <= a) (hb : 0 < b) :
    a - b <= a * (Real.log a - Real.log b) := by
  by_cases ha0 : a = 0
  · simp [ha0, le_of_lt hb]
  have hkl := InformationTheory.klFun_nonneg (x := a / b)
    (div_nonneg ha (le_of_lt hb))
  have hscaled := mul_nonneg (le_of_lt hb) hkl
  rw [InformationTheory.klFun_apply, Real.log_div ha0 hb.ne'] at hscaled
  field_simp [hb.ne'] at hscaled
  linarith

/-- The scalar Klein inequality is stable under a nonnegative overlap weight. -/
theorem scalar_klein_log_weighted {a b w : Real}
    (ha : 0 <= a) (hb : 0 < b) (hw : 0 <= w) :
    w * (a - b) <= w * (a * (Real.log a - Real.log b)) := by
  exact mul_le_mul_of_nonneg_left (scalar_klein_log ha hb) hw

/-- Squared moduli of the transition amplitudes between two finite eigenbases. -/
def overlapWeight {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (i j : n) : Real :=
  Complex.normSq ((star (U : Matrix n n Complex) * (V : Matrix n n Complex)) i j)

theorem overlapWeight_nonnegative {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (i j : n) :
    0 <= overlapWeight U V i j :=
  Complex.normSq_nonneg _

/-- Each row of a unitary overlap matrix has total squared modulus one. -/
theorem sum_overlapWeight_row {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (i : n) :
    (∑ j, overlapWeight U V i j) = 1 := by
  let W : Matrix.unitaryGroup n Complex := star U * V
  have hW : (W : Matrix n n Complex) * star (W : Matrix n n Complex) = 1 :=
    Unitary.coe_mul_star_self W
  have hdiag := congrFun (congrFun hW i) i
  change (∑ j, overlapWeight U V i j) = 1
  change (∑ j, Complex.normSq (W i j)) = 1
  have hdiag' : ((∑ j, Complex.normSq (W i j) : Real) : Complex) = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Complex.mul_conj] using hdiag
  exact_mod_cast hdiag'

/-- Each column of a unitary overlap matrix has total squared modulus one. -/
theorem sum_overlapWeight_column {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (j : n) :
    (∑ i, overlapWeight U V i j) = 1 := by
  let W : Matrix.unitaryGroup n Complex := star U * V
  have hW := Matrix.UnitaryGroup.star_mul_self W
  have hdiag := congrFun (congrFun hW j) j
  change (∑ i, overlapWeight U V i j) = 1
  change (∑ i, Complex.normSq (W i j)) = 1
  have hdiag' : ((∑ i, Complex.normSq (W i j) : Real) : Complex) = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Complex.normSq_eq_conj_mul_self] using hdiag
  exact_mod_cast hdiag'

/-- Row stochasticity of the eigenbasis overlap preserves a row-indexed sum. -/
theorem sum_overlapWeight_row_scale {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (f : n -> Real) :
    (∑ i, ∑ j, overlapWeight U V i j * f i) = ∑ i, f i := by
  calc
    (∑ i, ∑ j, overlapWeight U V i j * f i) =
        ∑ i, (∑ j, overlapWeight U V i j) * f i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ i, f i := by simp [sum_overlapWeight_row]

/-- Column stochasticity of the eigenbasis overlap preserves a column-indexed sum. -/
theorem sum_overlapWeight_column_scale {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (f : n -> Real) :
    (∑ i, ∑ j, overlapWeight U V i j * f j) = ∑ j, f j := by
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, overlapWeight U V i j * f j) =
        ∑ j, (∑ i, overlapWeight U V i j) * f j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ j, f j := by simp [sum_overlapWeight_column]

/-- The real trace of a finite Hermitian matrix is the sum of its real eigenvalues. -/
theorem realTrace_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    realTrace A = ∑ i, hA.eigenvalues i := by
  unfold realTrace
  rw [hA.trace_eq_sum_eigenvalues]
  simp

/-- A Hermitian functional-calculus trace pairing is its finite spectral sum. -/
theorem trace_mul_cfc_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) (f : Real -> Real) :
    (A * hA.cfc f).trace =
      (∑ i, (hA.eigenvalues i * f (hA.eigenvalues i) : Real) : Complex) := by
  rw [Matrix.IsHermitian.cfc]
  conv_lhs => arg 1; arg 1; rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  calc
    _ = Matrix.trace
        ((hA.eigenvectorUnitary : Matrix n n Complex) *
          (Matrix.diagonal (Function.comp (RCLike.ofReal : Real -> Complex) hA.eigenvalues) *
            ((star (hA.eigenvectorUnitary : Matrix n n Complex) *
              (hA.eigenvectorUnitary : Matrix n n Complex)) *
              (Matrix.diagonal
                (Function.comp (RCLike.ofReal : Real -> Complex)
                  (Function.comp f hA.eigenvalues)) *
                star (hA.eigenvectorUnitary : Matrix n n Complex))))) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        ((hA.eigenvectorUnitary : Matrix n n Complex) *
          (Matrix.diagonal (Function.comp (RCLike.ofReal : Real -> Complex) hA.eigenvalues) *
            (Matrix.diagonal
              (Function.comp (RCLike.ofReal : Real -> Complex)
                (Function.comp f hA.eigenvalues)) *
              star (hA.eigenvectorUnitary : Matrix n n Complex)))) := by
          rw [Unitary.coe_star_mul_self]
          simp
    _ = Matrix.trace
        ((Matrix.diagonal (Function.comp (RCLike.ofReal : Real -> Complex) hA.eigenvalues) *
          (Matrix.diagonal
            (Function.comp (RCLike.ofReal : Real -> Complex)
              (Function.comp f hA.eigenvalues)) *
            star (hA.eigenvectorUnitary : Matrix n n Complex))) *
          (hA.eigenvectorUnitary : Matrix n n Complex)) :=
          Matrix.trace_mul_comm _ _
    _ = _ := by
      simp only [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
      simp

/-- The trace of a Hermitian functional calculus is the spectral sum of the function. -/
theorem trace_cfc_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) (f : Real -> Real) :
    (hA.cfc f).trace = (∑ i, (f (hA.eigenvalues i) : Real) : Complex) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  calc
    _ = (star (hA.eigenvectorUnitary : Matrix n n Complex) *
        ((hA.eigenvectorUnitary : Matrix n n Complex) *
          Matrix.diagonal (Function.comp Complex.ofReal
            (Function.comp f hA.eigenvalues)))).trace := Matrix.trace_mul_comm _ _
    _ = _ := by
      rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
      simp [Matrix.trace, Matrix.diag, Matrix.diagonal, Function.comp_def]

/-- Functional-calculus trace of a real diagonal matrix, stated without choosing an eigenbasis. -/
theorem trace_cfc_diagonal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    (cfc f (Matrix.diagonal fun i => (d i : Complex))).trace =
      (∑ i, (f (d i) : Real) : Complex) := by
  let D : Matrix n n Complex := Matrix.diagonal fun i => (d i : Complex)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  rw [hD.cfc_eq, trace_cfc_eq_sum_eigenvalues]
  have hroots := congrArg (fun roots : Multiset Complex =>
      (roots.map fun z => f z.re).sum) hD.roots_charpoly_eq_eigenvalues
  have hcharpoly : D.charpoly = (Finset.univ : Finset n).prod
      (fun i => Polynomial.X - Polynomial.C (d i : Complex)) := by
    simpa [D] using Matrix.charpoly_diagonal (fun i => (d i : Complex))
  rw [hcharpoly,
    Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hroots
  exact_mod_cast (by
    simpa [Function.comp_def, List.sum_ofFn] using hroots.symm)

/-- A diagonal trace pairing reduces to its coordinatewise functional-calculus sum. -/
theorem trace_mul_cfc_diagonal {n : Type u} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    (Matrix.diagonal (fun i => (d i : Complex)) *
        cfc f (Matrix.diagonal fun i => (d i : Complex))).trace =
      (∑ i, (d i * f (d i) : Real) : Complex) := by
  let D : Matrix n n Complex := Matrix.diagonal fun i => (d i : Complex)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  rw [hD.cfc_eq, trace_mul_cfc_eq_sum_eigenvalues]
  have hroots := congrArg (fun roots : Multiset Complex =>
      (roots.map fun z => z.re * f z.re).sum) hD.roots_charpoly_eq_eigenvalues
  have hcharpoly : D.charpoly = (Finset.univ : Finset n).prod
      (fun i => Polynomial.X - Polynomial.C (d i : Complex)) := by
    simpa [D] using Matrix.charpoly_diagonal (fun i => (d i : Complex))
  rw [hcharpoly,
    Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hroots
  exact_mod_cast (by
    simpa [Function.comp_def, List.sum_ofFn] using hroots.symm)

/-- The trace of `A log A` is its finite spectral sum. -/
theorem trace_mul_logMatrix_eq_sum_eigenvalues {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    (A * logMatrix A hA).trace =
      (∑ i, (hA.eigenvalues i * Real.log (hA.eigenvalues i) : Real) : Complex) := by
  exact trace_mul_cfc_eq_sum_eigenvalues A hA Real.log

/- The mixed trace pairing expands over the two independent Hermitian eigenbases. -/
set_option maxHeartbeats 3000000 in
theorem trace_mul_logMatrix_eq_sum_overlap {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * logMatrix B hB).trace =
      (∑ i, ∑ j,
        (hA.eigenvalues i * overlapWeight hA.eigenvectorUnitary hB.eigenvectorUnitary i j *
          Real.log (hB.eigenvalues j) : Real) : Complex) := by
  let U : Matrix.unitaryGroup n Complex := hA.eigenvectorUnitary
  let V : Matrix.unitaryGroup n Complex := hB.eigenvectorUnitary
  let W : Matrix.unitaryGroup n Complex := star U * V
  have hA_spectral :
      A = Unitary.conjStarAlgAut Complex _ U
        (Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues)) := hA.spectral_theorem
  have hB_log :
      logMatrix B hB = Unitary.conjStarAlgAut Complex _ V
        (Matrix.diagonal
          (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues))) := by
    change hB.cfc Real.log = _
    rfl
  rw [hB_log]
  conv_lhs => arg 1; rw [hA_spectral]
  change
    Matrix.trace
      ((U : Matrix n n Complex) * Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
        star (U : Matrix n n Complex) *
        ((V : Matrix n n Complex) *
          Matrix.diagonal
            (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
          star (V : Matrix n n Complex))) = _
  calc
    _ = Matrix.trace
        ((U : Matrix n n Complex) *
          (Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
            (star (U : Matrix n n Complex) *
              ((V : Matrix n n Complex) *
                (Matrix.diagonal
                  (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
                  star (V : Matrix n n Complex)))))) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace
        ((Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
          (star (U : Matrix n n Complex) *
            ((V : Matrix n n Complex) *
              (Matrix.diagonal
                (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
                star (V : Matrix n n Complex))))) * (U : Matrix n n Complex)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
          ((W : Matrix n n Complex) *
            (Matrix.diagonal
              (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
              star (W : Matrix n n Complex))) ) := by
          congr 1
          simp [W, U, V, Matrix.mul_assoc]
    _ = _ := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Finset.mul_sum,
        overlapWeight, U, V, W, Complex.normSq_eq_conj_mul_self, mul_comm,
        mul_left_comm, mul_assoc]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_comm]

/-- Relative entropy is the scalar Klein expression averaged over eigenbasis overlaps. -/
theorem relativeEntropy_eq_sum_overlap {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relativeEntropy A B hA hB =
      ∑ i, ∑ j,
        overlapWeight hA.eigenvectorUnitary hB.eigenvectorUnitary i j *
          (hA.eigenvalues i *
            (Real.log (hA.eigenvalues i) - Real.log (hB.eigenvalues j))) := by
  unfold relativeEntropy realTrace
  rw [Matrix.mul_sub, Matrix.trace_sub,
    trace_mul_logMatrix_eq_sum_eigenvalues A hA,
    trace_mul_logMatrix_eq_sum_overlap A B hA hB]
  simp only [Complex.sub_re]
  simp_rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [← sum_overlapWeight_row_scale hA.eigenvectorUnitary hB.eigenvectorUnitary
    (fun i => hA.eigenvalues i * Real.log (hA.eigenvalues i))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
Finite noncommutative Klein trace inequality.  `A` and `B` are diagonalized
independently; their interaction is represented by the doubly stochastic
overlap weights between the two eigenbases.
-/
theorem klein_trace_inequality {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.PosSemidef) (hB : B.PosDef) :
    realTrace (A - B) <= relativeEntropy A B hA.isHermitian hB.isHermitian := by
  rw [relativeEntropy_eq_sum_overlap A B hA.isHermitian hB.isHermitian]
  calc
    realTrace (A - B) = realTrace A - realTrace B := by
      simp [realTrace]
    _ = (∑ i, hA.isHermitian.eigenvalues i) - (∑ j, hB.isHermitian.eigenvalues j) := by
      rw [realTrace_eq_sum_eigenvalues A hA.isHermitian,
        realTrace_eq_sum_eigenvalues B hB.isHermitian]
    _ = ∑ i, ∑ j,
        overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
          (hA.isHermitian.eigenvalues i - hB.isHermitian.eigenvalues j) := by
      symm
      calc
        _ =
            (∑ i, ∑ j,
              overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
                hA.isHermitian.eigenvalues i) -
              ∑ i, ∑ j,
                overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
                  hB.isHermitian.eigenvalues j := by
                    simp_rw [mul_sub]
                    calc
                      _ = ∑ i,
                          ((∑ j,
                            overlapWeight hA.isHermitian.eigenvectorUnitary
                              hB.isHermitian.eigenvectorUnitary i j *
                              hA.isHermitian.eigenvalues i) -
                            ∑ j,
                              overlapWeight hA.isHermitian.eigenvectorUnitary
                                hB.isHermitian.eigenvectorUnitary i j *
                                hB.isHermitian.eigenvalues j) := by
                            apply Finset.sum_congr rfl
                            intro i _
                            rw [Finset.sum_sub_distrib]
                      _ = _ := by rw [Finset.sum_sub_distrib]
        _ = _ := by
          rw [sum_overlapWeight_row_scale hA.isHermitian.eigenvectorUnitary
            hB.isHermitian.eigenvectorUnitary hA.isHermitian.eigenvalues,
            sum_overlapWeight_column_scale hA.isHermitian.eigenvectorUnitary
              hB.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvalues]
    _ <= ∑ i, ∑ j,
        overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
          (hA.isHermitian.eigenvalues i *
            (Real.log (hA.isHermitian.eigenvalues i) -
              Real.log (hB.isHermitian.eigenvalues j))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact scalar_klein_log_weighted (hA.eigenvalues_nonneg i) (hB.eigenvalues_pos j)
        (overlapWeight_nonnegative _ _ _ _)

/-- Normalizing factor for epsilon regularization of a finite density matrix. -/
def epsilonRegularizationDenominator {n : Type u} [Fintype n] (epsilon : Real) : Real :=
  1 + epsilon * Fintype.card n

/--
Normalized epsilon regularization.  It is strictly positive for positive
`epsilon` while preserving trace one when the input has trace one.
-/
def epsilonRegularize {n : Type u} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (epsilon : Real) : Matrix n n Complex :=
  ((epsilonRegularizationDenominator (n := n) epsilon)⁻¹ : Real) •
    (B + (epsilon : Real) • (1 : Matrix n n Complex))

theorem epsilonRegularizationDenominator_pos {n : Type u} [Fintype n]
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < epsilonRegularizationDenominator (n := n) epsilon := by
  unfold epsilonRegularizationDenominator
  positivity

/-- Epsilon regularization turns every positive semidefinite finite matrix positive definite. -/
theorem epsilonRegularize_posDef {n : Type u} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    (epsilonRegularize B epsilon).PosDef := by
  unfold epsilonRegularize
  have hidentity : (epsilon • (1 : Matrix n n Complex)).PosDef := by
    exact (Matrix.PosDef.one (n := n)).smul hepsilon
  have hshift : (B + epsilon • (1 : Matrix n n Complex)).PosDef :=
    Matrix.PosDef.posSemidef_add hB hidentity
  exact Matrix.PosDef.smul hshift
    (inv_pos.mpr (epsilonRegularizationDenominator_pos (n := n) hepsilon))

/-- Normalized epsilon regularization preserves the trace-one condition. -/
theorem realTrace_epsilonRegularize {n : Type u} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) (hBtrace : realTrace B = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    realTrace (epsilonRegularize B epsilon) = 1 := by
  have hBtrace' : B.trace = 1 := by
    have hBtraceReal := hBtrace
    rw [realTrace_eq_sum_eigenvalues B hB.isHermitian] at hBtraceReal
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]
    simpa using congrArg Complex.ofReal hBtraceReal
  unfold epsilonRegularize realTrace
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hBtrace']
  have hdenom : 1 + epsilon * Fintype.card n ≠ 0 :=
    ne_of_gt (epsilonRegularizationDenominator_pos (n := n) hepsilon)
  rw [Complex.real_smul, Complex.real_smul]
  simp
  unfold epsilonRegularizationDenominator
  field_simp [hdenom]

/--
Epsilon-regularized relative entropy is nonnegative for arbitrary finite
trace-one positive semidefinite matrices, including singular inputs.
-/
theorem epsilon_regularized_relativeEntropy_nonnegative
    {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAtrace : realTrace A = 1) (hBtrace : realTrace B = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 <= relativeEntropy A (epsilonRegularize B epsilon) hA.isHermitian
      (epsilonRegularize_posDef B hB hepsilon).isHermitian := by
  have hregularizedTrace := realTrace_epsilonRegularize B hB hBtrace hepsilon
  have hKlein := klein_trace_inequality A (epsilonRegularize B epsilon) hA
    (epsilonRegularize_posDef B hB hepsilon)
  have hdifference : realTrace (A - epsilonRegularize B epsilon) = 0 := by
    calc
      realTrace (A - epsilonRegularize B epsilon) =
          realTrace A - realTrace (epsilonRegularize B epsilon) := by
            simp [realTrace]
      _ = 0 := by rw [hAtrace, hregularizedTrace]; norm_num
  rw [hdifference] at hKlein
  exact hKlein

/-
The finite tensor logarithm trace formula.  The proof transports the
functional calculus through the tensor of the two independent spectral
unitaries, then evaluates the resulting diagonal trace.  Thus no common
eigenbasis for `A` and `B` is assumed.
-/
set_option maxHeartbeats 1000000 in
theorem trace_mul_logMatrix_kronecker {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    ((A ⊗ₖ B) *
        logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian).trace =
      (∑ i, ∑ j,
        (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j *
          Real.log (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j) : Real) : Complex) := by
  let U : unitary (Matrix (m × n) (m × n) Complex) :=
    ⟨(hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
        (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex),
      Matrix.kronecker_mem_unitary hA.isHermitian.eigenvectorUnitary.property
        hB.isHermitian.eigenvectorUnitary.property⟩
  let D : Matrix (m × n) (m × n) Complex :=
    Matrix.diagonal fun ij : m × n =>
      ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex)
  let hP : (A ⊗ₖ B).IsHermitian := (hA.kronecker hB).isHermitian
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro ij
    exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  have hfactor : A ⊗ₖ B =
      (U : Matrix (m × n) (m × n) Complex) * D *
        star (U : Matrix (m × n) (m × n) Complex) := by
    rw [hA.isHermitian.spectral_theorem, hB.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    have hstar : star
        ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) =
        star (hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          star (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex) := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
    change
      ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) *
          (Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) ⊗ₖ
            Matrix.diagonal (Complex.ofReal ∘ hB.isHermitian.eigenvalues)) *
          (star (hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
            star (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) =
        ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) *
          Matrix.diagonal (fun ij =>
            ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex)) *
          star ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
            (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex))
    rw [Matrix.diagonal_kronecker_diagonal, hstar]
    simp [Complex.ofReal_mul]
  let phi : Matrix (m × n) (m × n) Complex ≃⋆ₐ[Complex]
      Matrix (m × n) (m × n) Complex :=
    Unitary.conjStarAlgAut Complex _ U
  have hDpos : D.PosDef := by
    change (Matrix.diagonal fun ij : m × n =>
      ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex)).PosDef
    apply Matrix.posDef_diagonal_iff.mpr
    intro ij
    exact_mod_cast mul_pos (hA.eigenvalues_pos ij.1) (hB.eigenvalues_pos ij.2)
  have hlog_cont : ContinuousOn Real.log (spectrum Real D) :=
    Real.continuousOn_log.mono (by
      simpa only [Set.subset_compl_singleton_iff] using
        spectrum.zero_notMem Real hDpos.isUnit)
  have hphi_cont : Continuous phi := by
    change Continuous fun X : Matrix (m × n) (m × n) Complex =>
      (U : Matrix (m × n) (m × n) Complex) * X * star (U : Matrix (m × n) (m × n) Complex)
    fun_prop
  have hphiD : phi D = A ⊗ₖ B := by
    simpa [phi, Unitary.conjStarAlgAut_apply] using hfactor.symm
  have hphiHermitian : (phi D).IsHermitian := by
    rw [hphiD]
    exact hP
  have hmap : phi (cfc Real.log D) = cfc Real.log (phi D) :=
    StarAlgHomClass.map_cfc phi Real.log D hlog_cont hphi_cont hD hphiHermitian
  have hlog : logMatrix (A ⊗ₖ B) hP =
      (U : Matrix (m × n) (m × n) Complex) * cfc Real.log D *
        star (U : Matrix (m × n) (m × n) Complex) := by
    rw [logMatrix_apply, ← hP.cfc_eq]
    calc
      cfc Real.log (A ⊗ₖ B) = cfc Real.log (phi D) := by rw [hphiD]
      _ = phi (cfc Real.log D) := hmap.symm
      _ = _ := rfl
  change ((A ⊗ₖ B) * logMatrix (A ⊗ₖ B) hP).trace = _
  rw [hlog, hfactor]
  have hUleft : (star U : Matrix (m × n) (m × n) Complex) *
      (U : Matrix (m × n) (m × n) Complex) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have hUleft' :
      ((↑(star U) : Matrix (m × n) (m × n) Complex) *
        (↑U : Matrix (m × n) (m × n) Complex)) = (1 : Matrix (m × n) (m × n) Complex) := by
    simpa only [Unitary.coe_star] using hUleft
  calc
    _ = (U * (D * cfc Real.log D) * star U).trace := by
      congr 1
      calc
        U * D * star U * (U * cfc Real.log D * star U) =
            U * (D * ((star U * U) * cfc Real.log D)) * star U := by noncomm_ring
        _ = U * (D * cfc Real.log D) * star U := by
          rw [hUleft']
          simp [Matrix.mul_assoc]
    _ = (star U * (U * (D * cfc Real.log D))).trace :=
      Matrix.trace_mul_comm _ _
    _ = (D * cfc Real.log D).trace := by
      congr 1
      rw [← Matrix.mul_assoc, hUleft', Matrix.one_mul]
    _ = _ := by
      rw [show D = Matrix.diagonal fun ij =>
        ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex) by rfl]
      rw [trace_mul_cfc_diagonal]
      simp [Fintype.sum_prod_type]

/--
Trace-level tensor logarithm rule for strictly positive finite matrices.  This
is the exact finite identity used when the product marginal is regularized.
-/
theorem realTrace_mul_logMatrix_kronecker {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    realTrace ((A ⊗ₖ B) *
        logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian) =
      realTrace (A * logMatrix A hA.isHermitian) * realTrace B +
        realTrace A * realTrace (B * logMatrix B hB.isHermitian) := by
  let hP : (A ⊗ₖ B).IsHermitian := (hA.kronecker hB).isHermitian
  have hproduct :
      realTrace ((A ⊗ₖ B) * logMatrix (A ⊗ₖ B) hP) =
        ∑ i, ∑ j,
          hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j *
            Real.log (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j) := by
    unfold realTrace
    rw [trace_mul_logMatrix_kronecker A B hA hB]
    simp
  have hAlog : realTrace (A * logMatrix A hA.isHermitian) =
      ∑ i, hA.isHermitian.eigenvalues i * Real.log (hA.isHermitian.eigenvalues i) := by
    unfold realTrace
    rw [trace_mul_logMatrix_eq_sum_eigenvalues]
    simp
  have hBlog : realTrace (B * logMatrix B hB.isHermitian) =
      ∑ j, hB.isHermitian.eigenvalues j * Real.log (hB.isHermitian.eigenvalues j) := by
    unfold realTrace
    rw [trace_mul_logMatrix_eq_sum_eigenvalues]
    simp
  have hAtrace : realTrace A = ∑ i, hA.isHermitian.eigenvalues i :=
    realTrace_eq_sum_eigenvalues A hA.isHermitian
  have hBtrace : realTrace B = ∑ j, hB.isHermitian.eigenvalues j :=
    realTrace_eq_sum_eigenvalues B hB.isHermitian
  change realTrace ((A ⊗ₖ B) * logMatrix (A ⊗ₖ B) hP) = _
  rw [hproduct, hAlog, hBlog, hAtrace, hBtrace]
  calc
    _ = ∑ i, ∑ j,
        ((hA.isHermitian.eigenvalues i * Real.log (hA.isHermitian.eigenvalues i)) *
            hB.isHermitian.eigenvalues j +
          hA.isHermitian.eigenvalues i *
            (hB.isHermitian.eigenvalues j * Real.log (hB.isHermitian.eigenvalues j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_mul (hA.eigenvalues_pos i).ne' (hB.eigenvalues_pos j).ne']
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      apply congrArg₂ (fun x y : Real => x + y)
      · rw [Finset.sum_comm]
        calc
          _ = ∑ i, (∑ j, hA.isHermitian.eigenvalues j *
              Real.log (hA.isHermitian.eigenvalues j)) * hB.isHermitian.eigenvalues i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = _ := by rw [Finset.mul_sum]
      · rw [Finset.sum_comm]
        calc
          _ = ∑ i, (∑ j, hA.isHermitian.eigenvalues j) *
              (hB.isHermitian.eigenvalues i * Real.log (hB.isHermitian.eigenvalues i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = _ := by rw [Finset.mul_sum]

/--
The adjoint Kraus sum of the repository's concrete right-compression formula
is extension by the identity on the traced-out factor.
-/
theorem rightCompression_adjoint_sum
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {beta : Type u} [Fintype beta]
    (b : OrthonormalBasis beta Complex K) (X : Operator H) :
    (∑ i : beta,
      (QEC.Locality.tensorRight H K (b i)).comp
        (X.comp (LinearMap.adjoint (QEC.Locality.tensorRight H K (b i))))) =
      TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      calc
        (∑ i : beta,
          (QEC.Locality.tensorRight H K (b i)).comp
            (X.comp (LinearMap.adjoint (QEC.Locality.tensorRight H K (b i)))))
            (h ⊗ₜ[Complex] k) =
            ∑ i : beta,
              ((QEC.Locality.tensorRight H K (b i)).comp
                (X.comp (LinearMap.adjoint (QEC.Locality.tensorRight H K (b i)))))
                (h ⊗ₜ[Complex] k) := by
              simp
        _ =
            ∑ i : beta, X h ⊗ₜ[Complex] (inner Complex (b i) k • b i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [LinearMap.comp_apply, LinearMap.comp_apply,
                QEC.Locality.tensorRight_adjoint_tmul]
              simp [QEC.Locality.tensorRight, TensorProduct.tmul_smul]
        _ = X h ⊗ₜ[Complex] (∑ i : beta, inner Complex (b i) k • b i) := by
              rw [TensorProduct.tmul_sum]
        _ = (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))
              (h ⊗ₜ[Complex] k) := by
              rw [b.sum_repr']
              simp
  | add x y hx hy => simp [map_add, hx, hy]

/--
Concrete right partial-trace pairing for the repository's raw contraction
semantics.  It is the finite adjoint relation used to move a marginal
logarithm back onto the bipartite operator.
-/
theorem partialTraceRightRaw_trace_pairing
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {beta : Type u} [Fintype beta]
    (b : OrthonormalBasis beta Complex K) (A : Operator (CompositeSystem H K))
    (X : Operator H) :
    LinearMap.trace Complex H (((partialTraceRightRaw H K) A).comp X) =
      LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))) := by
  let S : beta -> H →ₗ[Complex] CompositeSystem H K :=
    fun i => QEC.Locality.tensorRight H K (b i)
  let T : beta -> Operator H :=
    fun i => (LinearMap.adjoint (S i)).comp (A.comp (S i))
  have hright : QEC.Locality.rightCompression H K b A = ∑ i, T i := by
    apply LinearMap.ext
    intro z
    simp [QEC.Locality.rightCompression, S, T]
  rw [QEC.Locality.partialTraceRightRaw_eq_rightCompression H K b, hright]
  have hcompose : (∑ i, T i).comp X = ∑ i, (T i).comp X := by
    ext z
    simp [LinearMap.comp_apply]
  rw [hcompose, map_sum]
  calc
    _ = ∑ i, LinearMap.trace Complex (CompositeSystem H K)
        (A.comp ((S i).comp (X.comp (LinearMap.adjoint (S i))))) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [T, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_comm'
          (A.comp ((S i).comp X)) (LinearMap.adjoint (S i)))
    _ = LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (∑ i, (S i).comp (X.comp (LinearMap.adjoint (S i))))) := by
      symm
      have hdistribute :
          A.comp (∑ i, (S i).comp (X.comp (LinearMap.adjoint (S i)))) =
            ∑ i, A.comp ((S i).comp (X.comp (LinearMap.adjoint (S i)))) := by
        ext z
        simp [LinearMap.comp_apply]
      rw [hdistribute, map_sum]
    _ = _ := by
      rw [rightCompression_adjoint_sum b X]

/-- Concrete left partial trace, defined by swapping factors and using the raw right trace. -/
noncomputable def partialTraceLeftRaw (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator K :=
  (partialTraceRightRaw K H).comp
    ((TensorProduct.comm Complex H K).conj.toLinearMap)

/--
Concrete left partial-trace pairing.  Together with
`partialTraceRightRaw_trace_pairing`, this supplies the two factor pairings
needed to move both marginal logarithms into a bipartite trace.
-/
theorem partialTraceLeftRaw_trace_pairing
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator (CompositeSystem H K)) (Y : Operator K) :
    LinearMap.trace Complex K (((partialTraceLeftRaw H K) A).comp Y) =
      LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y)) := by
  let e : CompositeSystem H K ≃ₗ[Complex] CompositeSystem K H :=
    TensorProduct.comm Complex H K
  change LinearMap.trace Complex K
      (((partialTraceRightRaw K H) (e.conj A)).comp Y) = _
  let bH : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex H))) Complex H :=
    (stdOrthonormalBasis Complex H).reindex Equiv.ulift.symm
  rw [partialTraceRightRaw_trace_pairing
    (H := K) (K := H) (bH) (e.conj A) Y]
  have hswap : e.symm.toLinearMap.comp
      ((TensorProduct.map Y (LinearMap.id : H →ₗ[Complex] H)).comp e.toLinearMap) =
        TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul h k => simp [e, LinearMap.comp_apply]
    | add x y hx hy => simp [map_add, hx, hy]
  have hconj : (e.conj A).comp
      (TensorProduct.map Y (LinearMap.id : H →ₗ[Complex] H)) =
        e.conj (A.comp (e.symm.toLinearMap.comp
          ((TensorProduct.map Y (LinearMap.id : H →ₗ[Complex] H)).comp e.toLinearMap))) := by
    simp [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hconj, LinearMap.trace_conj', hswap]

/-- The base-two entropy of #409 is the negative real trace pairing with `log2Matrix`. -/
theorem DensityOperator.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    rho.vonNeumannEntropy =
      -realTrace (rho.spectralMatrix b * log2Matrix (rho.spectralMatrix b)
        (rho.spectralMatrix_isHermitian b)) := by
  let A := rho.spectralMatrix b
  let hA : A.IsHermitian := rho.spectralMatrix_isHermitian b
  rw [DensityOperator.vonNeumannEntropy_eq_basisMatrixSpectrum]
  change
    ((A.charpoly.roots.map Complex.re).map DensityOperator.entropyTerm).sum =
      -Complex.re (Matrix.trace (A * hA.cfc (Real.logb 2)))
  rw [hA.roots_charpoly_eq_eigenvalues]
  rw [trace_mul_cfc_eq_sum_eigenvalues]
  simp [Function.comp_def, List.sum_ofFn]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : hA.eigenvalues i = 0 <;> simp [DensityOperator.entropyTerm, hi]

end FiniteMatrixEntropy

end
end Semantics
end QEC
