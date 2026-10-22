import QEC.Bounds.BPTDisentangling.NoCloning.ScalarCompression.Transport

/-!
# BPT partial-trace no-cloning closure

Cacheable internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
One-factor scalar compression fixes every code cross term after tracing out
the opposite factor.  This is the local reference-decoupling bridge used by
the two-factor no-cloning closure; it only consumes probes on `N`.
-/
theorem partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hscalar : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y) (hnorm : inner Complex x x = 1) :
    Semantics.partialTraceRightRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • Semantics.partialTraceRightRaw N C
        (InnerProductSpace.rankOne Complex x x).toLinearMap := by
  let b : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex C))) Complex C :=
    (stdOrthonormalBasis Complex C).reindex Equiv.ulift.symm
  apply LinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  let X : Semantics.Operator N := (InnerProductSpace.rankOne Complex v u).toLinearMap
  let E : Semantics.Operator (Semantics.CompositeSystem N C) :=
    TensorProduct.map X (1 : Semantics.Operator C)
  rcases hscalar X with ⟨scalar, hcompression⟩
  have hself : LinearMap.adjoint P = P :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp hP.isSymmetric
  have hmatrix (z w : Semantics.CompositeSystem N C) (hz : P z = z) (hw : P w = w) :
      inner Complex w (E z) = scalar * inner Complex w z := by
    calc
      inner Complex w (E z) = inner Complex (P w) (E (P z)) := by rw [hw, hz]
      _ = inner Complex w (P (E (P z))) := by
        rw [← LinearMap.adjoint_inner_right P w (E (P z)), hself]
      _ = inner Complex w ((P * E * P) z) := by rfl
      _ = inner Complex w ((scalar • P) z) := by
        rw [hcompression]
      _ = scalar * inner Complex w z := by
        rw [LinearMap.smul_apply, hz, inner_smul_right]
  have hscalar_eq : scalar = inner Complex x (E x) := by
    calc
      scalar = scalar * inner Complex x x := by rw [hnorm, mul_one]
      _ = inner Complex x (E x) := (hmatrix x x hx hx).symm
  have htrace_x : LinearMap.trace Complex N
      ((Semantics.partialTraceRightRaw N C
        (InnerProductSpace.rankOne Complex x x).toLinearMap).comp X) =
      inner Complex x (E x) := by
    calc
      LinearMap.trace Complex N
          ((Semantics.partialTraceRightRaw N C
            (InnerProductSpace.rankOne Complex x x).toLinearMap).comp X) =
          LinearMap.trace Complex (Semantics.CompositeSystem N C)
            ((InnerProductSpace.rankOne Complex x x).toLinearMap.comp E) := by
              exact Semantics.FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
                  b (InnerProductSpace.rankOne Complex x x).toLinearMap X
      _ = inner Complex x (E x) :=
        Semantics.QuditSubsystem.trace_rankOne_comp E x x
  calc
    inner Complex u
        (Semantics.partialTraceRightRaw N C
          (InnerProductSpace.rankOne Complex x y).toLinearMap v) =
        LinearMap.trace Complex N
          ((Semantics.partialTraceRightRaw N C
            (InnerProductSpace.rankOne Complex x y).toLinearMap).comp X) := by
              simpa [X] using
                (Semantics.QuditSubsystem.trace_comp_rankOne
                  (Semantics.partialTraceRightRaw N C
                    (InnerProductSpace.rankOne Complex x y).toLinearMap) v u).symm
    _ = LinearMap.trace Complex (Semantics.CompositeSystem N C)
        ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) := by
          exact Semantics.FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
              b (InnerProductSpace.rankOne Complex x y).toLinearMap X
    _ = inner Complex y (E x) :=
      Semantics.QuditSubsystem.trace_rankOne_comp E x y
    _ = scalar * inner Complex y x := hmatrix x y hx hy
    _ = (inner Complex y x) * inner Complex x (E x) := by
      rw [← hscalar_eq]
      ring
    _ = (inner Complex y x) * LinearMap.trace Complex N
        ((Semantics.partialTraceRightRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap).comp X) := by
            rw [htrace_x]
    _ = LinearMap.trace Complex N
        (((inner Complex y x) • Semantics.partialTraceRightRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap).comp X) := by
            simp [LinearMap.smul_comp, smul_eq_mul]
    _ = inner Complex u
        (((inner Complex y x) • Semantics.partialTraceRightRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap) v) := by
            simpa [X] using
              Semantics.QuditSubsystem.trace_comp_rankOne
                ((inner Complex y x) • Semantics.partialTraceRightRaw N C
                  (InnerProductSpace.rankOne Complex x x).toLinearMap) v u

/--
The factor-swapped companion of
`partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression`.
Right-factor scalar compression kills cross terms after tracing out the left
factor, without asserting any scalarity for joint observables.
-/
theorem partialTraceLeftRaw_rankOne_eq_inner_smul_of_right_scalar_compression
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hscalar : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y) (hnorm : inner Complex x x = 1) :
    Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex x x).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  let Y : Semantics.Operator C := (InnerProductSpace.rankOne Complex v u).toLinearMap
  let E : Semantics.Operator (Semantics.CompositeSystem N C) :=
    TensorProduct.map (1 : Semantics.Operator N) Y
  rcases hscalar Y with ⟨scalar, hcompression⟩
  have hself : LinearMap.adjoint P = P :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp hP.isSymmetric
  have hmatrix (z w : Semantics.CompositeSystem N C) (hz : P z = z) (hw : P w = w) :
      inner Complex w (E z) = scalar * inner Complex w z := by
    calc
      inner Complex w (E z) = inner Complex (P w) (E (P z)) := by rw [hw, hz]
      _ = inner Complex w (P (E (P z))) := by
        rw [← LinearMap.adjoint_inner_right P w (E (P z)), hself]
      _ = inner Complex w ((P * E * P) z) := by rfl
      _ = inner Complex w ((scalar • P) z) := by
        rw [hcompression]
      _ = scalar * inner Complex w z := by
        rw [LinearMap.smul_apply, hz, inner_smul_right]
  have hscalar_eq : scalar = inner Complex x (E x) := by
    calc
      scalar = scalar * inner Complex x x := by rw [hnorm, mul_one]
      _ = inner Complex x (E x) := (hmatrix x x hx hx).symm
  have htrace_x : LinearMap.trace Complex C
      ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex x x).toLinearMap).comp Y) =
      inner Complex x (E x) := by
    calc
      LinearMap.trace Complex C
          ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
            (InnerProductSpace.rankOne Complex x x).toLinearMap).comp Y) =
          LinearMap.trace Complex (Semantics.CompositeSystem N C)
            ((InnerProductSpace.rankOne Complex x x).toLinearMap.comp E) := by
              exact Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
                  (InnerProductSpace.rankOne Complex x x).toLinearMap Y
      _ = inner Complex x (E x) :=
        Semantics.QuditSubsystem.trace_rankOne_comp E x x
  calc
    inner Complex u
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x y).toLinearMap v) =
        LinearMap.trace Complex C
          ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
            (InnerProductSpace.rankOne Complex x y).toLinearMap).comp Y) := by
              simpa [Y] using
                (Semantics.QuditSubsystem.trace_comp_rankOne
                  (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
                    (InnerProductSpace.rankOne Complex x y).toLinearMap) v u).symm
    _ = LinearMap.trace Complex (Semantics.CompositeSystem N C)
        ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) := by
          exact Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
              (InnerProductSpace.rankOne Complex x y).toLinearMap Y
    _ = inner Complex y (E x) :=
      Semantics.QuditSubsystem.trace_rankOne_comp E x y
    _ = scalar * inner Complex y x := hmatrix x y hx hy
    _ = (inner Complex y x) * inner Complex x (E x) := by
      rw [← hscalar_eq]
      ring
    _ = (inner Complex y x) * LinearMap.trace Complex C
        ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap).comp Y) := by
            rw [htrace_x]
    _ = LinearMap.trace Complex C
        (((inner Complex y x) • Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap).comp Y) := by
            simp [LinearMap.smul_comp, smul_eq_mul]
    _ = inner Complex u
        (((inner Complex y x) • Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap) v) := by
            simpa [Y] using
              Semantics.QuditSubsystem.trace_comp_rankOne
                ((inner Complex y x) • Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
                  (InnerProductSpace.rankOne Complex x x).toLinearMap) v u

/--
Right-factor scalar compression identifies the diagonal left marginals of any
two normalized vectors fixed by the projection.  This remains a one-factor
statement; no joint-observable scalarity is used.
-/
theorem partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hscalar : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y)
    (hnormx : inner Complex x x = 1) (hnormy : inner Complex y y = 1) :
    Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x x).toLinearMap =
      Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex y y).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  let Y : Semantics.Operator C := (InnerProductSpace.rankOne Complex v u).toLinearMap
  let E : Semantics.Operator (Semantics.CompositeSystem N C) :=
    TensorProduct.map (1 : Semantics.Operator N) Y
  rcases hscalar Y with ⟨scalar, hcompression⟩
  have hself : LinearMap.adjoint P = P :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp hP.isSymmetric
  have hmatrix (z : Semantics.CompositeSystem N C) (hz : P z = z) :
      inner Complex z (E z) = scalar * inner Complex z z := by
    calc
      inner Complex z (E z) = inner Complex (P z) (E (P z)) := by rw [hz]
      _ = inner Complex z (P (E (P z))) := by
        rw [← LinearMap.adjoint_inner_right P z (E (P z)), hself]
      _ = inner Complex z ((P * E * P) z) := by rfl
      _ = inner Complex z ((scalar • P) z) := by rw [hcompression]
      _ = scalar * inner Complex z z := by rw [LinearMap.smul_apply, hz, inner_smul_right]
  have htrace (z : Semantics.CompositeSystem N C) :
      LinearMap.trace Complex C
        ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex z z).toLinearMap).comp Y) =
        inner Complex z (E z) := by
    calc
      LinearMap.trace Complex C
          ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
            (InnerProductSpace.rankOne Complex z z).toLinearMap).comp Y) =
          LinearMap.trace Complex (Semantics.CompositeSystem N C)
            ((InnerProductSpace.rankOne Complex z z).toLinearMap.comp E) := by
              exact Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
                  (InnerProductSpace.rankOne Complex z z).toLinearMap Y
      _ = inner Complex z (E z) :=
        Semantics.QuditSubsystem.trace_rankOne_comp E z z
  calc
    inner Complex u
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap v) =
        LinearMap.trace Complex C
          ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
            (InnerProductSpace.rankOne Complex x x).toLinearMap).comp Y) := by
              simpa [Y] using
                (Semantics.QuditSubsystem.trace_comp_rankOne
                  (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
                    (InnerProductSpace.rankOne Complex x x).toLinearMap) v u).symm
    _ = inner Complex x (E x) := htrace x
    _ = scalar := by rw [hmatrix x hx, hnormx, mul_one]
    _ = inner Complex y (E y) := by rw [hmatrix y hy, hnormy, mul_one]
    _ = LinearMap.trace Complex C
        ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex y y).toLinearMap).comp Y) := (htrace y).symm
    _ = inner Complex u
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex y y).toLinearMap v) := by
            simpa [Y] using
              Semantics.QuditSubsystem.trace_comp_rankOne
                (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
                  (InnerProductSpace.rankOne Complex y y).toLinearMap) v u

/-- The finite cross-Gram operator is the sum of paired rank-one columns. -/
theorem comp_adjoint_eq_sum_rankOne_cross
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (b : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (A B : C →ₗ[Complex] N) :
    A.comp (LinearMap.adjoint B) = ∑ j,
      (InnerProductSpace.rankOne Complex (A (b j)) (B (b j))).toLinearMap := by
  ext z
  change A (LinearMap.adjoint B z) = _
  rw [← b.sum_repr' (LinearMap.adjoint B z)]
  simp only [map_sum, map_smul, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.adjoint_inner_right]
  rfl

/-- The right partial trace of a cross rank-one operator is its cross amplitude Gram operator. -/
theorem partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (b : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (x y : Semantics.CompositeSystem N C) :
    Semantics.partialTraceRightRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (Semantics.DensityOperator.rightAmplitude b x).comp
        (LinearMap.adjoint (Semantics.DensityOperator.rightAmplitude b y)) := by
  conv_lhs =>
    rw [← Semantics.DensityOperator.sum_rightTensorCoefficients_tmul b x,
      ← Semantics.DensityOperator.sum_rightTensorCoefficients_tmul b y]
  rw [Semantics.DensityOperator.rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [comp_adjoint_eq_sum_rankOne_cross b]
  simp [b.inner_eq_ite, Semantics.DensityOperator.rightAmplitude_apply_basis]

/-- The transpose convention for the left raw marginal still identifies the right Gram operators. -/
theorem adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (bN : OrthonormalBasis (Fin (Module.finrank Complex N)) Complex N)
    (bC : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (x y : Semantics.CompositeSystem N C)
    (hnormx : ‖x‖ ^ 2 = 1) (hnormy : ‖y‖ ^ 2 = 1)
    (hraw : Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x x).toLinearMap =
      Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex y y).toLinearMap) :
    (LinearMap.adjoint (Semantics.DensityOperator.rightAmplitude bC x)).comp
        (Semantics.DensityOperator.rightAmplitude bC x) =
      (LinearMap.adjoint (Semantics.DensityOperator.rightAmplitude bC y)).comp
        (Semantics.DensityOperator.rightAmplitude bC y) := by
  have hmatrix := congrArg
    (fun T : Semantics.Operator C => LinearMap.toMatrix bC.toBasis bC.toBasis T) hraw
  have hraw' :
      LinearMap.toMatrix bC.toBasis bC.toBasis
          (Semantics.DensityOperator.leftMarginal
            (Semantics.DensityOperator.pureDensity x hnormx)).toOperator =
        LinearMap.toMatrix bC.toBasis bC.toBasis
          (Semantics.DensityOperator.leftMarginal
            (Semantics.DensityOperator.pureDensity y hnormy)).toOperator := by
    change LinearMap.toMatrix bC.toBasis bC.toBasis
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap) =
      LinearMap.toMatrix bC.toBasis bC.toBasis
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex y y).toLinearMap)
    exact hmatrix
  rw [Semantics.DensityOperator.leftMarginal_pureDensity_toMatrix bN bC x hnormx,
    Semantics.DensityOperator.leftMarginal_pureDensity_toMatrix bN bC y hnormy] at hraw'
  have hcoeff :
      (Semantics.DensityOperator.coefficientMatrix bN bC x).conjTranspose *
          Semantics.DensityOperator.coefficientMatrix bN bC x =
        (Semantics.DensityOperator.coefficientMatrix bN bC y).conjTranspose *
          Semantics.DensityOperator.coefficientMatrix bN bC y := by
    simpa using congrArg Matrix.transpose hraw'
  apply (LinearMap.toMatrix bC.toBasis bC.toBasis).injective
  rw [LinearMap.toMatrix_comp bC.toBasis bN.toBasis bC.toBasis,
    LinearMap.toMatrix_adjoint bC bN,
    LinearMap.toMatrix_comp bC.toBasis bN.toBasis bC.toBasis,
    LinearMap.toMatrix_adjoint bC bN]
  simpa [Semantics.DensityOperator.coefficientMatrix] using hcoeff

/-- A vanishing cross Gram and equal right Gram operators force the first amplitude to vanish. -/
theorem linearMap_eq_zero_of_cross_and_equal_gram
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (A B : C →ₗ[Complex] N)
    (hcross : A.comp (LinearMap.adjoint B) = 0)
    (hgram : (LinearMap.adjoint A).comp A = (LinearMap.adjoint B).comp B) :
    A = 0 := by
  let T : C →ₗ[Complex] C := (LinearMap.adjoint A).comp A
  have hTsq : T.comp T = 0 := by
    calc
      T.comp T = ((LinearMap.adjoint A).comp A).comp
          ((LinearMap.adjoint A).comp A) := rfl
      _ = ((LinearMap.adjoint A).comp A).comp
          ((LinearMap.adjoint B).comp B) := by rw [hgram]
      _ = (LinearMap.adjoint A).comp ((A.comp (LinearMap.adjoint B)).comp B) := by
        simp only [LinearMap.comp_assoc]
      _ = 0 := by rw [hcross]; simp
  have hTself : LinearMap.adjoint T = T := by
    dsimp [T]
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  have hTzero : T = 0 := by
    apply LinearMap.ext
    intro z
    apply (inner_self_eq_zero (𝕜 := Complex)).mp
    calc
      inner Complex (T z) (T z) =
          inner Complex z (LinearMap.adjoint T (T z)) :=
        (LinearMap.adjoint_inner_right T z (T z)).symm
      _ = inner Complex z (T (T z)) := by rw [hTself]
      _ = 0 := by
        have happly := congrArg (fun S : C →ₗ[Complex] C => S z) hTsq
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right] using
          congrArg (inner Complex z) happly
  have hgramzero : (LinearMap.adjoint A).comp A = 0 := by
    exact hTzero
  apply LinearMap.ext
  intro z
  apply (inner_self_eq_zero (𝕜 := Complex)).mp
  calc
    inner Complex (A z) (A z) =
        inner Complex z (LinearMap.adjoint A (A z)) :=
      (LinearMap.adjoint_inner_right A z (A z)).symm
    _ = inner Complex z (((LinearMap.adjoint A).comp A) z) := rfl
    _ = 0 := by rw [hgramzero]; simp

/-- Vanishing finite right amplitude has no hidden tensor component. -/
theorem eq_zero_of_rightAmplitude_eq_zero
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (b : OrthonormalBasis (Fin (Module.finrank Complex C)) Complex C)
    (x : Semantics.CompositeSystem N C)
    (hamp : Semantics.DensityOperator.rightAmplitude b x = 0) :
    x = 0 := by
  rw [← Semantics.DensityOperator.sum_rightTensorCoefficients_tmul b x]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Semantics.DensityOperator.rightAmplitude_apply_basis b x j, hamp]
  simp

theorem exists_orthonormal_pair_fixed_of_one_lt_range_finrank
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection)
    (hdim : 1 < Module.finrank Complex (LinearMap.range P)) :
    ∃ x y : H, P x = x ∧ P y = y ∧
      inner Complex x x = 1 ∧ inner Complex y y = 1 ∧
      ‖x‖ ^ 2 = 1 ∧ ‖y‖ ^ 2 = 1 ∧ inner Complex y x = 0 := by
  classical
  let R := LinearMap.range P
  let b := stdOrthonormalBasis Complex R
  let i0 : Fin (Module.finrank Complex R) :=
    ⟨0, Nat.zero_lt_of_lt (lt_trans Nat.zero_lt_one hdim)⟩
  let i1 : Fin (Module.finrank Complex R) := ⟨1, hdim⟩
  let x : H := (b i0 : R)
  let y : H := (b i1 : R)
  have hi10 : i1 ≠ i0 := by
    simp [i0, i1]
  have hxmem : x ∈ LinearMap.range P := by
    exact (b i0).property
  have hymem : y ∈ LinearMap.range P := by
    exact (b i1).property
  have hx : P x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp hxmem
  have hy : P y = y :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP.isIdempotentElem).mp hymem
  refine ⟨x, y, hx, hy, ?_, ?_, ?_, ?_, ?_⟩
  · change inner Complex (b i0) (b i0) = 1
    simpa only [if_pos] using b.inner_eq_ite i0 i0
  · change inner Complex (b i1) (b i1) = 1
    simpa only [if_pos] using b.inner_eq_ite i1 i1
  · change ‖b i0‖ ^ 2 = 1
    rw [b.norm_eq_one]
    norm_num
  · change ‖b i1‖ ^ 2 = 1
    rw [b.norm_eq_one]
    norm_num
  · change inner Complex (b i1) (b i0) = 0
    simpa only [if_neg hi10] using b.inner_eq_ite i1 i0

/--
Two independent local scalar-compression families on a genuine two-factor
projection force its range to have finite complex dimension at most one.
-/
theorem finrank_range_le_one_of_two_factor_scalar_compressions
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hleft : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (hright : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P) :
    Module.finrank Complex (LinearMap.range P) ≤ 1 := by
  by_contra hle
  have hdim : 1 < Module.finrank Complex (LinearMap.range P) := Nat.lt_of_not_ge hle
  rcases exists_orthonormal_pair_fixed_of_one_lt_range_finrank P hP hdim with
    ⟨x, y, hx, hy, hxx, hyy, hnormx, hnormy, hyx⟩
  let bN := stdOrthonormalBasis Complex N
  let bC := stdOrthonormalBasis Complex C
  let A := Semantics.DensityOperator.rightAmplitude bC x
  let B := Semantics.DensityOperator.rightAmplitude bC y
  have hrawCross : Semantics.partialTraceRightRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap = 0 := by
    calc
      Semantics.partialTraceRightRaw N C
          (InnerProductSpace.rankOne Complex x y).toLinearMap =
          (inner Complex y x) • Semantics.partialTraceRightRaw N C
            (InnerProductSpace.rankOne Complex x x).toLinearMap :=
        partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
          P hP hleft x y hx hy hxx
      _ = 0 := by rw [hyx, zero_smul]
  have hcross : A.comp (LinearMap.adjoint B) = 0 := by
    calc
      A.comp (LinearMap.adjoint B) =
          Semantics.partialTraceRightRaw N C
            (InnerProductSpace.rankOne Complex x y).toLinearMap := by
              symm
              exact partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint bC x y
      _ = 0 := hrawCross
  have hrawDiag := partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
    P hP hright x y hx hy hxx hyy
  have hgram : (LinearMap.adjoint A).comp A = (LinearMap.adjoint B).comp B := by
    simpa [A, B] using adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
      bN bC x y hnormx hnormy hrawDiag
  have hAzero : A = 0 := linearMap_eq_zero_of_cross_and_equal_gram A B hcross hgram
  have hxzero : x = 0 := eq_zero_of_rightAmplitude_eq_zero bC x (by simpa [A] using hAzero)
  have hzero_one : (0 : Complex) = 1 := by simpa [hxzero] using hxx
  norm_num at hzero_one

/-- A nonzero two-factor scalar-compressed projection is rank one. -/
theorem isSymmetricProjection_eq_rankOne_of_ne_zero_of_two_factor_scalar_compressions
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hleft : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (hright : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P) :
    ∃ phi : Semantics.CompositeSystem N C, ‖phi‖ = 1 ∧
      P = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  exact isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one P hP hP0
    (finrank_range_le_one_of_two_factor_scalar_compressions P hP hleft hright)

end BPTCommutingProjectorModel

end Bounds
end QEC
