import QEC.Semantics.Entropy.MatrixRelative
import QEC.Semantics.Entropy.Purification
import QEC.Semantics.Entropy.QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Finite bipartite entropy subadditivity

This module integrates the finite matrix relative-entropy foundation with the
repository's concrete partial-trace semantics.  The main result is stated for
arbitrary finite bipartite density operators; regularization is used only
inside the proof to handle singular marginals.
-/

universe u v w

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder Kronecker TensorProduct

noncomputable section

namespace FiniteMatrixEntropy

/-- Tensor-product coordinates turn a tensor map into the matrix Kronecker product. -/
theorem toMatrix_tensorMap
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
    {m : Type v} [Fintype m] [DecidableEq m] {n : Type w} [Fintype n] [DecidableEq n]
    (bH : OrthonormalBasis m Complex H) (bK : OrthonormalBasis n Complex K)
    (X : Operator H) (Y : Operator K) :
    (TensorProduct.map X Y).toMatrix (bH.tensorProduct bK).toBasis
      (bH.tensorProduct bK).toBasis =
      X.toMatrix bH.toBasis bH.toBasis ⊗ₖ Y.toMatrix bK.toBasis bK.toBasis := by
  simpa only [OrthonormalBasis.toBasis_tensorProduct] using
    (TensorProduct.toMatrix_map bH.toBasis bK.toBasis bH.toBasis bK.toBasis X Y)

/-- The joint matrix of a positive operator is positive semidefinite in any orthonormal basis. -/
theorem posSemidef_toMatrix_of_isPositive
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A : Operator H) (hA : A.IsPositive) :
    (A.toMatrix b.toBasis b.toBasis).PosSemidef := by
  exact (LinearMap.posSemidef_toMatrix_iff b).mpr hA

/-- Real matrix trace agrees with the trace of the represented finite operator. -/
theorem realTrace_toMatrix
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A : Operator H) :
    realTrace (A.toMatrix b.toBasis b.toBasis) =
      Complex.re (LinearMap.trace Complex H A) := by
  unfold realTrace
  rw [← LinearMap.trace_eq_matrix_trace Complex b.toBasis A]

/-- Matrix coordinates preserve a composition trace pairing. -/
theorem realTrace_toMatrix_mul_toMatrix
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A X : Operator H) :
    realTrace (A.toMatrix b.toBasis b.toBasis * X.toMatrix b.toBasis b.toBasis) =
      Complex.re (LinearMap.trace Complex H (A.comp X)) := by
  rw [← LinearMap.toMatrix_comp]
  exact realTrace_toMatrix b (A.comp X)

/-- Right marginal pairing in tensor-product matrix coordinates. -/
theorem realTrace_joint_mul_kronecker_right
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (X : Operator H) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          (X.toMatrix bH.toBasis bH.toBasis ⊗ₖ (1 : Matrix n n Complex))) =
      realTrace (((partialTraceRightRaw H K) A).toMatrix bH.toBasis bH.toBasis *
        X.toMatrix bH.toBasis bH.toBasis) := by
  have hmap : X.toMatrix bH.toBasis bH.toBasis ⊗ₖ (1 : Matrix n n Complex) =
      (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K)).toMatrix
        (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis := by
    simpa only [LinearMap.toMatrix_id] using
      (toMatrix_tensorMap bH bK X (LinearMap.id : K →ₗ[Complex] K)).symm
  rw [hmap]
  rw [realTrace_toMatrix_mul_toMatrix, realTrace_toMatrix_mul_toMatrix]
  rw [partialTraceRightRaw_trace_pairing bK A X]

/-- Left marginal pairing in tensor-product matrix coordinates. -/
theorem realTrace_joint_mul_kronecker_left
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (Y : Operator K) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          ((1 : Matrix m m Complex) ⊗ₖ Y.toMatrix bK.toBasis bK.toBasis)) =
      realTrace ((partialTraceLeftRaw H K A).toMatrix bK.toBasis bK.toBasis *
        Y.toMatrix bK.toBasis bK.toBasis) := by
  have hmap : (1 : Matrix m m Complex) ⊗ₖ Y.toMatrix bK.toBasis bK.toBasis =
      (TensorProduct.map (LinearMap.id : H →ₗ[Complex] H) Y).toMatrix
        (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis := by
    simpa only [LinearMap.toMatrix_id] using
      (toMatrix_tensorMap bH bK (LinearMap.id : H →ₗ[Complex] H) Y).symm
  rw [hmap]
  rw [realTrace_toMatrix_mul_toMatrix, realTrace_toMatrix_mul_toMatrix]
  rw [partialTraceLeftRaw_trace_pairing A Y]

/-- Right marginal pairing directly for a matrix observable in fixed coordinates. -/
theorem realTrace_joint_mul_kronecker_right_matrix
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (X : Matrix m m Complex) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          (X ⊗ₖ (1 : Matrix n n Complex))) =
      realTrace (((partialTraceRightRaw H K) A).toMatrix bH.toBasis bH.toBasis * X) := by
  let Xop : Operator H := (LinearMap.toMatrix bH.toBasis bH.toBasis).symm X
  simpa [Xop] using realTrace_joint_mul_kronecker_right bH bK A Xop

/-- Left marginal pairing directly for a matrix observable in fixed coordinates. -/
theorem realTrace_joint_mul_kronecker_left_matrix
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] {m n : Type u} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (bH : OrthonormalBasis m Complex H)
    (bK : OrthonormalBasis n Complex K) (A : Operator (CompositeSystem H K))
    (Y : Matrix n n Complex) :
    realTrace
        (A.toMatrix (bH.tensorProduct bK).toBasis (bH.tensorProduct bK).toBasis *
          ((1 : Matrix m m Complex) ⊗ₖ Y)) =
      realTrace ((partialTraceLeftRaw H K A).toMatrix bK.toBasis bK.toBasis * Y) := by
  let Yop : Operator K := (LinearMap.toMatrix bK.toBasis bK.toBasis).symm Y
  simpa [Yop] using realTrace_joint_mul_kronecker_left bH bK A Yop

/-- The diagonal embedding as a continuous star algebra homomorphism. -/
noncomputable def diagonalStarAlgHom {n : Type v} [Fintype n] [DecidableEq n] :
    (n -> Complex) →⋆ₐ[Complex] Matrix n n Complex where
  toAlgHom := Matrix.diagonalAlgHom (n := n) Complex
  map_star' := by
    intro x
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · have hji : j ≠ i := Ne.symm hij
      simp [Matrix.diagonal, hij, hji]

/-- Functional calculus of a real diagonal matrix is pointwise. -/
theorem cfc_diagonal {n : Type v} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    cfc f (Matrix.diagonal fun i => (d i : Complex)) =
      Matrix.diagonal fun i => (f (d i) : Complex) := by
  letI : ContinuousFunctionalCalculus Complex (n -> Complex) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus Real (n -> Complex) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus Complex Complex IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus Real Complex IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let a : n -> Complex := fun i => (d i : Complex)
  let phi : (n -> Complex) →⋆ₐ[Complex] Matrix n n Complex := diagonalStarAlgHom
  have hphi : Continuous phi := by
    change Continuous (fun x : n -> Complex => Matrix.diagonal x)
    exact continuous_id.matrix_diagonal
  have ha : IsSelfAdjoint a := by
    change star a = a
    ext i
    simp [a]
  have hphia : IsSelfAdjoint (phi a) := by
    dsimp [phi, diagonalStarAlgHom, a]
    change (Matrix.diagonal fun i => (d i : Complex)).IsHermitian
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  have hspectrum : (spectrum Real a).Finite := by
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    refine (Set.finite_singleton (d i)).subset ?_
    intro x hx
    have hx' := CFC.spectrum_algebraMap_subset (A := Complex) (d i) hx
    simpa [a] using hx'
  have hcontinuity : ContinuousOn f (spectrum Real a) := hspectrum.continuousOn f
  have hunion : (⋃ i, spectrum Real (a i)).Finite := by
    rw [← Pi.spectrum_eq]
    exact hspectrum
  have hmap := phi.map_cfc f a hcontinuity hphi ha hphia
  calc
    cfc f (Matrix.diagonal fun i => (d i : Complex)) = phi (cfc f a) := by
      simpa [phi, diagonalStarAlgHom, a] using hmap.symm
    _ = phi (fun i => cfc f (a i)) := by
      rw [cfc_map_pi (R := Real) (S := Complex) (A := fun _ : n => Complex)
        (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) f a
        (hf := hunion.continuousOn f) (ha := ha) (ha' := by
        intro i
        change IsSelfAdjoint (a i)
        exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp [a]))]
    _ = Matrix.diagonal fun i => (f (d i) : Complex) := by
      change Matrix.diagonal (fun i => cfc f (a i)) = _
      congr 1
      funext i
      simpa [a] using (cfc_algebraMap (p := IsSelfAdjoint) (A := Complex)
        (R := Real) (d i) f)

/- The finite product logarithm rule for arbitrary positive-definite factors. -/
set_option maxHeartbeats 2000000 in
theorem logMatrix_kronecker_posDef {m : Type v} {n : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian =
      logMatrix A hA.isHermitian ⊗ₖ 1 + 1 ⊗ₖ logMatrix B hB.isHermitian := by
  let UA : Matrix.unitaryGroup m Complex := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup n Complex := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (m × n) Complex :=
    ⟨(UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex),
      Matrix.kronecker_mem_unitary UA.property UB.property⟩
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
    have hstar : star ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) =
        star (UA : Matrix m m Complex) ⊗ₖ star (UB : Matrix n n Complex) := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
    change
      ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) *
          (Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) ⊗ₖ
            Matrix.diagonal (Complex.ofReal ∘ hB.isHermitian.eigenvalues)) *
          (star (UA : Matrix m m Complex) ⊗ₖ star (UB : Matrix n n Complex)) =
        ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) * D *
          star ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex))
    rw [Matrix.diagonal_kronecker_diagonal, hstar]
    simp [D, Complex.ofReal_mul]
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
  have hmiddle : cfc Real.log D =
      Matrix.diagonal (fun i => (Real.log (hA.isHermitian.eigenvalues i) : Complex)) ⊗ₖ 1 +
        1 ⊗ₖ Matrix.diagonal (fun j => (Real.log (hB.isHermitian.eigenvalues j) : Complex)) := by
    rw [show D = Matrix.diagonal fun ij : m × n =>
      ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex) by rfl]
    rw [cfc_diagonal]
    rw [← Matrix.diagonal_one (n := n), ← Matrix.diagonal_one (n := m)]
    rw [Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal]
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    by_cases hi : i = i'
    · subst i'
      by_cases hj : j = j'
      · subst j'
        simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
        rw [Real.log_mul (ne_of_gt (hA.eigenvalues_pos i))
          (ne_of_gt (hB.eigenvalues_pos j))]
        rw [Complex.ofReal_add]
        simp
      · simp [Matrix.diagonal, hj]
    · simp [Matrix.diagonal, hi]
  have hlogA : logMatrix A hA.isHermitian =
      (UA : Matrix m m Complex) *
        Matrix.diagonal (fun i => (Real.log (hA.isHermitian.eigenvalues i) : Complex)) *
        star (UA : Matrix m m Complex) := by
    change hA.isHermitian.cfc Real.log = _
    rfl
  have hlogB : logMatrix B hB.isHermitian =
      (UB : Matrix n n Complex) *
        Matrix.diagonal (fun j => (Real.log (hB.isHermitian.eigenvalues j) : Complex)) *
        star (UB : Matrix n n Complex) := by
    change hB.isHermitian.cfc Real.log = _
    rfl
  have hUA : (UA : Matrix m m Complex) * star (UA : Matrix m m Complex) = 1 :=
    Unitary.coe_mul_star_self UA
  have hUB : (UB : Matrix n n Complex) * star (UB : Matrix n n Complex) = 1 :=
    Unitary.coe_mul_star_self UB
  have hUstar : star ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) =
      star (UA : Matrix m m Complex) ⊗ₖ star (UB : Matrix n n Complex) := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [hlog, hmiddle, hlogA, hlogB]
  simp only [U, Matrix.mul_add, Matrix.add_mul]
  rw [hUstar]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  rw [hUB, hUA]

/-- Epsilon regularization is scalar functional calculus on a Hermitian matrix. -/
theorem epsilonRegularize_eq_cfc {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.IsHermitian) (epsilon : Real) :
    epsilonRegularize B epsilon = hB.cfc (fun x =>
      (1 + epsilon * Fintype.card n)⁻¹ * (x + epsilon)) := by
  unfold epsilonRegularize epsilonRegularizationDenominator
  rw [← hB.cfc_eq]
  change (1 + epsilon * Fintype.card n)⁻¹ • (B + epsilon • 1) =
    cfc (fun x : Real => (1 + epsilon * Fintype.card n)⁻¹ • (x + epsilon)) B
  have hsmul :
      cfc (fun x : Real => (1 + epsilon * Fintype.card n)⁻¹ • (x + epsilon)) B =
        (1 + epsilon * Fintype.card n)⁻¹ • cfc (fun x : Real => x + epsilon) B := by
    exact cfc_smul (p := IsSelfAdjoint) (1 + epsilon * Fintype.card n)⁻¹
      (fun x : Real => x + epsilon) B
  have hadd : cfc (fun x : Real => x + epsilon) B = B + epsilon • 1 := by
    rw [cfc_add_const epsilon (fun x : Real => x) B]
    have hid : cfc (fun x : Real => x) B = B :=
      cfc_id' (p := IsSelfAdjoint) (R := Real) B hB
    rw [hid]
    rw [Algebra.algebraMap_eq_smul_one (A := Matrix n n Complex)]
  rw [hsmul, hadd]

/-- The logarithm of a regularized PSD matrix in the original spectral basis. -/
theorem logMatrix_epsilonRegularize_eq_cfc
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    logMatrix (epsilonRegularize B epsilon)
        (epsilonRegularize_posDef B hB hepsilon).isHermitian =
      hB.isHermitian.cfc (fun x =>
        Real.log ((x + epsilon) / (1 + epsilon * Fintype.card n))) := by
  let f : Real -> Real := fun x =>
    (1 + epsilon * Fintype.card n)⁻¹ * (x + epsilon)
  have hregularized : epsilonRegularize B epsilon = hB.isHermitian.cfc f :=
    epsilonRegularize_eq_cfc B hB.isHermitian epsilon
  have hregularizedCfc : epsilonRegularize B epsilon = cfc f B := by
    rw [hB.isHermitian.cfc_eq]
    exact hregularized
  have hlogContinuous : ContinuousOn Real.log (f '' spectrum Real B) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxnonneg : 0 <= x := by
      obtain ⟨i, rfl⟩ := hB.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
      exact hB.eigenvalues_nonneg i
    have hdenom : 0 < 1 + epsilon * Fintype.card n := by positivity
    have hfx : 0 < f x := by
      dsimp [f]
      exact mul_pos (inv_pos.mpr hdenom) (add_pos_of_nonneg_of_pos hxnonneg hepsilon)
    exact (Real.continuousAt_log (ne_of_gt hfx)).continuousWithinAt
  rw [logMatrix_apply, ← (epsilonRegularize_posDef B hB hepsilon).isHermitian.cfc_eq]
  rw [hregularizedCfc]
  rw [← cfc_comp' (p := IsSelfAdjoint) Real.log f B hlogContinuous
    (ha := hB.isHermitian)]
  rw [hB.isHermitian.cfc_eq]
  congr 2
  funext x
  dsimp [f]
  rw [div_eq_mul_inv]
  congr 1
  ring

/-- Spectral trace formula for the regularized logarithm. -/
theorem realTrace_mul_log_epsilonRegularize
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    realTrace (B * logMatrix (epsilonRegularize B epsilon)
      (epsilonRegularize_posDef B hB hepsilon).isHermitian) =
      ∑ i, hB.isHermitian.eigenvalues i *
        Real.log ((hB.isHermitian.eigenvalues i + epsilon) /
          (1 + epsilon * Fintype.card n)) := by
  rw [logMatrix_epsilonRegularize_eq_cfc B hB hepsilon]
  unfold realTrace
  rw [trace_mul_cfc_eq_sum_eigenvalues]
  simp

/-- Scalar support-aware convergence for the zero-eigenvalue case. -/
theorem tendsto_weighted_log_regularization (d : Nat) (x : Real)
    (hx : 0 <= x) :
    Filter.Tendsto (fun n : Nat =>
      x * Real.log ((x + (1 / ((n : Real) + 1))) /
        (1 + (1 / ((n : Real) + 1)) * d))) Filter.atTop
      (nhds (x * Real.log x)) := by
  let epsilon : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have htends : Filter.Tendsto epsilon Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hxzero : x = 0
  · subst x
    simp
  · have hnum : ContinuousAt (fun e : Real => x + e) 0 :=
      continuousAt_const.add continuousAt_id
    have hdenom : ContinuousAt (fun e : Real => 1 + e * d) 0 :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    have hquotient : ContinuousAt (fun e : Real => (x + e) / (1 + e * d)) 0 :=
      hnum.div hdenom (by norm_num)
    have hlog : ContinuousAt (fun e : Real =>
        Real.log ((x + e) / (1 + e * d))) 0 := by
      have hlog_base : ContinuousAt Real.log
          ((fun e : Real => (x + e) / (1 + e * d)) 0) := by
        simpa using Real.continuousAt_log hxzero
      exact Filter.Tendsto.comp hlog_base hquotient
    have hcontinuous : ContinuousAt (fun e : Real =>
        x * Real.log ((x + e) / (1 + e * d))) 0 :=
      continuousAt_const.mul hlog
    simpa [epsilon, Function.comp_def] using hcontinuous.tendsto.comp htends

/-- Epsilon-to-zero bridge for a possibly singular finite PSD matrix. -/
theorem tendsto_realTrace_mul_log_epsilonRegularize
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) :
    Filter.Tendsto (fun k : Nat =>
      realTrace (B * logMatrix (epsilonRegularize B (1 / ((k : Real) + 1)))
        (epsilonRegularize_posDef B hB (by positivity)).isHermitian)) Filter.atTop
      (nhds (realTrace (B * logMatrix B hB.isHermitian))) := by
  have hsum : Filter.Tendsto (fun k : Nat => ∑ i,
      hB.isHermitian.eigenvalues i *
        Real.log ((hB.isHermitian.eigenvalues i + (1 / ((k : Real) + 1))) /
          (1 + (1 / ((k : Real) + 1)) * Fintype.card n))) Filter.atTop
      (nhds (∑ i, hB.isHermitian.eigenvalues i *
        Real.log (hB.isHermitian.eigenvalues i))) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_weighted_log_regularization (Fintype.card n)
        (hB.isHermitian.eigenvalues i) (hB.eigenvalues_nonneg i))
  have hbase : realTrace (B * logMatrix B hB.isHermitian) =
      ∑ i, hB.isHermitian.eigenvalues i * Real.log (hB.isHermitian.eigenvalues i) := by
    unfold realTrace
    rw [trace_mul_logMatrix_eq_sum_eigenvalues]
    simp
  rw [hbase]
  convert hsum using 1
  funext k
  exact realTrace_mul_log_epsilonRegularize B hB (by positivity)

/-- A Hermitian trace-one matrix has complex trace equal to one. -/
theorem trace_eq_one_of_realTrace_eq_one
    {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) (hBtrace : realTrace B = 1) :
    B.trace = 1 := by
  have hBtraceReal := hBtrace
  rw [realTrace_eq_sum_eigenvalues B hB.isHermitian] at hBtraceReal
  rw [hB.isHermitian.trace_eq_sum_eigenvalues]
  simpa using congrArg Complex.ofReal hBtraceReal

/-- The real trace pairing is additive. -/
theorem realTrace_add {n : Type v} [Fintype n]
    (A B : Matrix n n Complex) :
    realTrace (A + B) = realTrace A + realTrace B := by
  simp [realTrace]

/-- The real trace pairing preserves subtraction. -/
theorem realTrace_sub {n : Type v} [Fintype n]
    (A B : Matrix n n Complex) :
    realTrace (A - B) = realTrace A - realTrace B := by
  simp [realTrace]

/-- Real scalar multiplication commutes with the real trace pairing. -/
theorem realTrace_real_smul {n : Type v} [Fintype n]
    (s : Real) (A : Matrix n n Complex) :
    realTrace (s • A) = s * realTrace A := by
  unfold realTrace
  rw [Matrix.trace_smul]
  change ((s : Complex) * A.trace).re = s * A.trace.re
  rw [Complex.mul_re]
  simp

/-- Base-two matrix logarithm is the positive scalar rescaling of the natural logarithm. -/
theorem log2Matrix_eq_inv_log_two_smul_logMatrix
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    log2Matrix A hA = (Real.log 2)⁻¹ • logMatrix A hA := by
  rw [log2Matrix_apply, logMatrix_apply, ← hA.cfc_eq]
  rw [← hA.cfc_eq Real.log]
  have hcont : ContinuousOn Real.log (spectrum Real A) :=
    Matrix.finite_real_spectrum.continuousOn Real.log
  rw [← cfc_smul (p := IsSelfAdjoint) (Real.log 2)⁻¹ Real.log A hcont]
  congr 1
  funext x
  rw [Real.logb, div_eq_mul_inv]
  ring

/-- Natural and base-two trace logarithms differ by the positive scalar `1 / log 2`. -/
theorem realTrace_mul_log2Matrix_eq_inv_log_two_mul
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) :
    realTrace (A * log2Matrix A hA) =
      (Real.log 2)⁻¹ * realTrace (A * logMatrix A hA) := by
  rw [log2Matrix_eq_inv_log_two_smul_logMatrix]
  rw [Matrix.mul_smul, realTrace_real_smul]

end FiniteMatrixEntropy

namespace DensityOperator

/-- The entropy trace formula in arbitrary finite orthonormal coordinates. -/
theorem vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (rho : DensityOperator H) (b : OrthonormalBasis n Complex H) :
    rho.vonNeumannEntropy =
      -FiniteMatrixEntropy.realTrace
        (rho.toOperator.toMatrix b.toBasis b.toBasis *
          FiniteMatrixEntropy.log2Matrix (rho.toOperator.toMatrix b.toBasis b.toBasis)
            ((LinearMap.isHermitian_toMatrix_iff b).2 rho.positive.isSymmetric)) := by
  let A := rho.toOperator.toMatrix b.toBasis b.toBasis
  let hA : A.IsHermitian := (LinearMap.isHermitian_toMatrix_iff b).2 rho.positive.isSymmetric
  unfold vonNeumannEntropy finiteSpectrum
  rw [← LinearMap.charpoly_toMatrix rho.toOperator b.toBasis]
  change
    ((A.charpoly.roots.map Complex.re).map entropyTerm).sum =
      -Complex.re (Matrix.trace (A * hA.cfc (Real.logb 2)))
  rw [hA.roots_charpoly_eq_eigenvalues]
  rw [FiniteMatrixEntropy.trace_mul_cfc_eq_sum_eigenvalues]
  simp
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : hA.eigenvalues i = 0 <;> simp [entropyTerm, hi]

/-- The left marginal is the raw left partial trace packaged as a density operator. -/
theorem leftMarginal_toOperator_eq_partialTraceLeftRaw
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (rho : DensityOperator (CompositeSystem H K)) :
    (leftMarginal rho).toOperator = FiniteMatrixEntropy.partialTraceLeftRaw H K rho.toOperator := by
  rfl

set_option maxHeartbeats 3000000 in
theorem vonNeumannEntropy_subadditive_bipartite
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (rho : DensityOperator (CompositeSystem H K)) :
    rho.vonNeumannEntropy <=
      (rightMarginal rho).vonNeumannEntropy + (leftMarginal rho).vonNeumannEntropy := by
  let bH : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex H))) Complex H :=
    (stdOrthonormalBasis Complex H).reindex Equiv.ulift.symm
  let bK : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex K))) Complex K :=
    (stdOrthonormalBasis Complex K).reindex Equiv.ulift.symm
  let bHK := bH.tensorProduct bK
  let A := rho.toOperator.toMatrix bHK.toBasis bHK.toBasis
  let B := (rightMarginal rho).toOperator.toMatrix bH.toBasis bH.toBasis
  let C := (leftMarginal rho).toOperator.toMatrix bK.toBasis bK.toBasis
  have hA : A.PosSemidef := by
    dsimp [A]
    exact FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive bHK rho.toOperator rho.positive
  have hB : B.PosSemidef := by
    dsimp [B]
    exact FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive bH
      (rightMarginal rho).toOperator (rightMarginal rho).positive
  have hC : C.PosSemidef := by
    dsimp [C]
    exact FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive bK
      (leftMarginal rho).toOperator (leftMarginal rho).positive
  have hAtrace : FiniteMatrixEntropy.realTrace A = 1 := by
    dsimp [A]
    rw [FiniteMatrixEntropy.realTrace_toMatrix]
    rw [rho.trace_one]
    norm_num
  have hBtrace : FiniteMatrixEntropy.realTrace B = 1 := by
    dsimp [B]
    rw [FiniteMatrixEntropy.realTrace_toMatrix]
    rw [(rightMarginal rho).trace_one]
    norm_num
  have hCtrace : FiniteMatrixEntropy.realTrace C = 1 := by
    dsimp [C]
    rw [FiniteMatrixEntropy.realTrace_toMatrix]
    rw [(leftMarginal rho).trace_one]
    norm_num
  have hregularized (epsilon : Real) (hepsilon : 0 < epsilon) :
      FiniteMatrixEntropy.realTrace
          (B * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            (FiniteMatrixEntropy.epsilonRegularize_posDef B hB hepsilon).isHermitian) +
        FiniteMatrixEntropy.realTrace
          (C * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            (FiniteMatrixEntropy.epsilonRegularize_posDef C hC hepsilon).isHermitian) <=
        FiniteMatrixEntropy.realTrace
          (A * FiniteMatrixEntropy.logMatrix A hA.isHermitian) := by
    have hBe : (FiniteMatrixEntropy.epsilonRegularize B epsilon).PosDef :=
      FiniteMatrixEntropy.epsilonRegularize_posDef B hB hepsilon
    have hCe : (FiniteMatrixEntropy.epsilonRegularize C epsilon).PosDef :=
      FiniteMatrixEntropy.epsilonRegularize_posDef C hC hepsilon
    have hP :
        (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
          FiniteMatrixEntropy.epsilonRegularize C epsilon).PosDef := hBe.kronecker hCe
    have hBeTrace : FiniteMatrixEntropy.realTrace
        (FiniteMatrixEntropy.epsilonRegularize B epsilon) = 1 :=
      FiniteMatrixEntropy.realTrace_epsilonRegularize B hB hBtrace hepsilon
    have hCeTrace : FiniteMatrixEntropy.realTrace
        (FiniteMatrixEntropy.epsilonRegularize C epsilon) = 1 :=
      FiniteMatrixEntropy.realTrace_epsilonRegularize C hC hCtrace hepsilon
    have hBeTraceComplex : (FiniteMatrixEntropy.epsilonRegularize B epsilon).trace = 1 :=
      FiniteMatrixEntropy.trace_eq_one_of_realTrace_eq_one
        (FiniteMatrixEntropy.epsilonRegularize B epsilon) hBe.posSemidef hBeTrace
    have hCeTraceComplex : (FiniteMatrixEntropy.epsilonRegularize C epsilon).trace = 1 :=
      FiniteMatrixEntropy.trace_eq_one_of_realTrace_eq_one
        (FiniteMatrixEntropy.epsilonRegularize C epsilon) hCe.posSemidef hCeTrace
    have hPTrace : FiniteMatrixEntropy.realTrace
        (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
          FiniteMatrixEntropy.epsilonRegularize C epsilon) = 1 := by
      unfold FiniteMatrixEntropy.realTrace
      rw [Matrix.trace_kronecker, hBeTraceComplex, hCeTraceComplex]
      norm_num
    have hBraw : (rightMarginal rho).toOperator =
        partialTraceRightRaw H K rho.toOperator := by
      rfl
    have hCraw : (leftMarginal rho).toOperator =
        FiniteMatrixEntropy.partialTraceLeftRaw H K rho.toOperator :=
      leftMarginal_toOperator_eq_partialTraceLeftRaw rho
    have hright : FiniteMatrixEntropy.realTrace
        (A * (FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
          hBe.isHermitian ⊗ₖ (1 : Matrix _ _ Complex))) =
        FiniteMatrixEntropy.realTrace
          (B * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            hBe.isHermitian) := by
      have hrightRaw :=
        FiniteMatrixEntropy.realTrace_joint_mul_kronecker_right_matrix bH bK rho.toOperator
          (FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            hBe.isHermitian)
      rw [← hBraw] at hrightRaw
      simpa only [A, B] using hrightRaw
    have hleft : FiniteMatrixEntropy.realTrace
        (A * ((1 : Matrix _ _ Complex) ⊗ₖ
          FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            hCe.isHermitian)) =
        FiniteMatrixEntropy.realTrace
          (C * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            hCe.isHermitian) := by
      have hleftRaw :=
        FiniteMatrixEntropy.realTrace_joint_mul_kronecker_left_matrix bH bK rho.toOperator
          (FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            hCe.isHermitian)
      rw [← hCraw] at hleftRaw
      simpa only [A, C] using hleftRaw
    have hcross : FiniteMatrixEntropy.realTrace
        (A * FiniteMatrixEntropy.logMatrix
          (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
            FiniteMatrixEntropy.epsilonRegularize C epsilon) hP.isHermitian) =
        FiniteMatrixEntropy.realTrace
          (B * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            hBe.isHermitian) +
          FiniteMatrixEntropy.realTrace
            (C * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
              hCe.isHermitian) := by
      rw [FiniteMatrixEntropy.logMatrix_kronecker_posDef _ _ hBe hCe, Matrix.mul_add,
        FiniteMatrixEntropy.realTrace_add, hright, hleft]
    have hKlein := FiniteMatrixEntropy.klein_trace_inequality A
      (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
        FiniteMatrixEntropy.epsilonRegularize C epsilon) hA hP
    have hdiff : FiniteMatrixEntropy.realTrace
        (A - (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
          FiniteMatrixEntropy.epsilonRegularize C epsilon)) = 0 := by
      rw [FiniteMatrixEntropy.realTrace_sub, hAtrace, hPTrace]
      norm_num
    rw [hdiff] at hKlein
    unfold FiniteMatrixEntropy.relativeEntropy at hKlein
    rw [Matrix.mul_sub, FiniteMatrixEntropy.realTrace_sub, hcross] at hKlein
    linarith
  have hlimit : Filter.Tendsto (fun k : Nat =>
      FiniteMatrixEntropy.realTrace
        (B * FiniteMatrixEntropy.logMatrix
          (FiniteMatrixEntropy.epsilonRegularize B (1 / ((k : Real) + 1)))
          (FiniteMatrixEntropy.epsilonRegularize_posDef B hB (by positivity)).isHermitian) +
      FiniteMatrixEntropy.realTrace
        (C * FiniteMatrixEntropy.logMatrix
          (FiniteMatrixEntropy.epsilonRegularize C (1 / ((k : Real) + 1)))
          (FiniteMatrixEntropy.epsilonRegularize_posDef C hC (by positivity)).isHermitian))
      Filter.atTop
      (nhds
        (FiniteMatrixEntropy.realTrace (B * FiniteMatrixEntropy.logMatrix B hB.isHermitian) +
          FiniteMatrixEntropy.realTrace (C * FiniteMatrixEntropy.logMatrix C hC.isHermitian))) :=
    (FiniteMatrixEntropy.tendsto_realTrace_mul_log_epsilonRegularize B hB).add
      (FiniteMatrixEntropy.tendsto_realTrace_mul_log_epsilonRegularize C hC)
  have hnatural :
      FiniteMatrixEntropy.realTrace (B * FiniteMatrixEntropy.logMatrix B hB.isHermitian) +
        FiniteMatrixEntropy.realTrace (C * FiniteMatrixEntropy.logMatrix C hC.isHermitian) <=
        FiniteMatrixEntropy.realTrace (A * FiniteMatrixEntropy.logMatrix A hA.isHermitian) := by
    apply le_of_tendsto' hlimit
    intro k
    exact hregularized (1 / ((k : Real) + 1)) (by positivity)
  have hEntropyA : rho.vonNeumannEntropy =
      -((Real.log 2)⁻¹ *
        FiniteMatrixEntropy.realTrace (A * FiniteMatrixEntropy.logMatrix A hA.isHermitian)) := by
    calc
      rho.vonNeumannEntropy =
          -FiniteMatrixEntropy.realTrace
            (A * FiniteMatrixEntropy.log2Matrix A hA.isHermitian) := by
        simpa only [A] using rho.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis bHK
      _ = _ := by rw [FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul]
  have hEntropyB : (rightMarginal rho).vonNeumannEntropy =
      -((Real.log 2)⁻¹ *
        FiniteMatrixEntropy.realTrace (B * FiniteMatrixEntropy.logMatrix B hB.isHermitian)) := by
    calc
      (rightMarginal rho).vonNeumannEntropy =
          -FiniteMatrixEntropy.realTrace
            (B * FiniteMatrixEntropy.log2Matrix B hB.isHermitian) := by
        simpa only [B] using
          (rightMarginal rho).vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis bH
      _ = _ := by rw [FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul]
  have hEntropyC : (leftMarginal rho).vonNeumannEntropy =
      -((Real.log 2)⁻¹ *
        FiniteMatrixEntropy.realTrace (C * FiniteMatrixEntropy.logMatrix C hC.isHermitian)) := by
    calc
      (leftMarginal rho).vonNeumannEntropy =
          -FiniteMatrixEntropy.realTrace
            (C * FiniteMatrixEntropy.log2Matrix C hC.isHermitian) := by
        simpa only [C] using
          (leftMarginal rho).vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis bK
      _ = _ := by rw [FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul]
  have hinv : 0 <= (Real.log 2)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (Real.log_pos (by norm_num)))
  have hscaled := mul_le_mul_of_nonneg_left hnatural hinv
  rw [hEntropyA, hEntropyB, hEntropyC]
  nlinarith

/-- BPT-ready entropy composition with the concrete heterogeneous qudit dimension bound. -/
theorem vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q)
    (rho : DensityOperator (CompositeSystem H S.selectedSystem)) :
    rho.vonNeumannEntropy <= (rightMarginal rho).vonNeumannEntropy +
      ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by
  exact (vonNeumannEntropy_subadditive_bipartite rho).trans
    (add_le_add_right (S.vonNeumannEntropy_le_sum_log_selectedDimensions (leftMarginal rho)) _)

/-- BPT-ready uniform-dimension corollary, available only under an explicit local bound. -/
theorem vonNeumannEntropy_le_rightMarginal_add_card_mul_log_uniformDimension
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι -> Nat} (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) (D : Nat)
    (hD : ∀ i, i ∈ S.selected -> q i <= D)
    (rho : DensityOperator (CompositeSystem H S.selectedSystem)) :
    rho.vonNeumannEntropy <= (rightMarginal rho).vonNeumannEntropy +
      (S.selected.card : Real) * Real.logb 2 (D : Real) := by
  exact (vonNeumannEntropy_le_rightMarginal_add_sum_log_selectedDimensions S rho).trans
    (add_le_add_right
      (S.sum_log_selectedDimensions_le_card_mul_log_uniformDimension hq D hD) _)

end DensityOperator

end
end Semantics
end QEC
