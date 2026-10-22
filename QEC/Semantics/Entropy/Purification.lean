import QEC.Semantics.Entropy.FiniteDimensional
import QEC.Semantics.ErrorCorrection.QuditSubsystem
/-!
# Finite spectral purifications and entropy identities

This internal module develops the finite-dimensional purification construction
and entropy facts needed by the M4 BPT entropy route.  The construction is
spectral: a density operator is purified by pairing each eigenvector with an
identical reference eigenvector and weighting it by the square root of its
eigenvalue.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder TensorProduct

noncomputable section

namespace DensityOperator

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- The orthonormal eigenbasis used by the canonical finite spectral purification. -/
noncomputable def spectralEigenbasis (rho : DensityOperator H) :
    OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H :=
  rho.positive.isSymmetric.eigenvectorBasis rfl

/-- The explicit spectral purification vector on `H tensor H`. -/
noncomputable def spectralPurificationVector (rho : DensityOperator H) : CompositeSystem H H :=
  ∑ i : Fin (Module.finrank Complex H),
    (Real.sqrt (rho.spectralEigenvalues i) : Complex) •
      (rho.spectralEigenbasis i ⊗ₜ[Complex] rho.spectralEigenbasis i)

/-- The spectral purification vector is normalized by the trace-one spectrum. -/
theorem spectralPurificationVector_normSq (rho : DensityOperator H) :
    ‖rho.spectralPurificationVector‖ ^ 2 = 1 := by
  have hpair (i j : Fin (Module.finrank Complex H)) :
      inner Complex
          ((Real.sqrt (rho.spectralEigenvalues i) : Complex) •
            (rho.spectralEigenbasis i ⊗ₜ[Complex] rho.spectralEigenbasis i))
          ((Real.sqrt (rho.spectralEigenvalues j) : Complex) •
            (rho.spectralEigenbasis j ⊗ₜ[Complex] rho.spectralEigenbasis j)) =
        if i = j then (rho.spectralEigenvalues i : Complex) else 0 := by
    change inner Complex
        (((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) ⊗ₜ[Complex]
          rho.spectralEigenbasis i)
        (((Real.sqrt (rho.spectralEigenvalues j) : Complex) • rho.spectralEigenbasis j) ⊗ₜ[Complex]
          rho.spectralEigenbasis j) = _
    rw [TensorProduct.inner_tmul]
    rw [inner_smul_left, inner_smul_right]
    simp only [rho.spectralEigenbasis.inner_eq_ite]
    split_ifs with hij
    · subst j
      simp only [Complex.conj_ofReal, mul_one]
      exact_mod_cast (show Real.sqrt (rho.spectralEigenvalues i) *
          Real.sqrt (rho.spectralEigenvalues i) = rho.spectralEigenvalues i by
        simpa [pow_two] using Real.sq_sqrt (rho.spectralEigenvalues_nonnegative i))
    · simp
  have hinner :
      inner Complex rho.spectralPurificationVector rho.spectralPurificationVector =
        ∑ i, (rho.spectralEigenvalues i : Complex) := by
    unfold spectralPurificationVector
    rw [sum_inner]
    simp_rw [inner_sum]
    simp_rw [hpair]
    simp
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner, map_sum]
  simpa using rho.spectralEigenvalues_sum_eq_one

/-- The density operator is the sum of its normalized spectral rank-one terms. -/
theorem spectralDecomposition (rho : DensityOperator H) :
    rho.toOperator = ∑ i : Fin (Module.finrank Complex H),
      (InnerProductSpace.rankOne Complex
        ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i)
        ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i)).toLinearMap := by
  ext x
  rw [LinearMap.sum_apply]
  change rho.toOperator x = ∑ i,
    inner Complex ((Real.sqrt (rho.spectralEigenvalues i) : Complex) •
      rho.spectralEigenbasis i) x •
      ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i)
  have hterm (i : Fin (Module.finrank Complex H)) :
      inner Complex ((Real.sqrt (rho.spectralEigenvalues i) : Complex) •
        rho.spectralEigenbasis i) x •
        ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) =
      inner Complex (rho.spectralEigenbasis i) x •
        ((rho.spectralEigenvalues i : Complex) • rho.spectralEigenbasis i) := by
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, smul_smul]
    rw [show
      (Real.sqrt (rho.spectralEigenvalues i) : Complex) *
          inner Complex (rho.spectralEigenbasis i) x *
          (Real.sqrt (rho.spectralEigenvalues i) : Complex) =
        inner Complex (rho.spectralEigenbasis i) x *
          (rho.spectralEigenvalues i : Complex) by
      calc
        (Real.sqrt (rho.spectralEigenvalues i) : Complex) *
            inner Complex (rho.spectralEigenbasis i) x *
            (Real.sqrt (rho.spectralEigenvalues i) : Complex) =
          inner Complex (rho.spectralEigenbasis i) x *
            ((Real.sqrt (rho.spectralEigenvalues i) : Complex) *
              (Real.sqrt (rho.spectralEigenvalues i) : Complex)) := by ring
        _ = inner Complex (rho.spectralEigenbasis i) x *
            (rho.spectralEigenvalues i : Complex) := by
          congr 1
          exact_mod_cast (show Real.sqrt (rho.spectralEigenvalues i) *
              Real.sqrt (rho.spectralEigenvalues i) = rho.spectralEigenvalues i by
            simpa [pow_two] using Real.sq_sqrt (rho.spectralEigenvalues_nonnegative i))]
  calc
    rho.toOperator x = rho.toOperator (∑ i,
        inner Complex (rho.spectralEigenbasis i) x • rho.spectralEigenbasis i) := by
      congr 1
      exact (rho.spectralEigenbasis.sum_repr' x).symm
    _ = ∑ i, inner Complex (rho.spectralEigenbasis i) x •
        rho.toOperator (rho.spectralEigenbasis i) := by
      simp only [map_sum, map_smul]
    _ = ∑ i, inner Complex (rho.spectralEigenbasis i) x •
        ((rho.spectralEigenvalues i : Complex) • rho.spectralEigenbasis i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold spectralEigenbasis spectralEigenvalues
      rw [rho.positive.isSymmetric.apply_eigenvectorBasis]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hterm i).symm

omit [FiniteQuantumSystem H] in
/-- Rank one is additive in each finite vector argument. -/
theorem rankOne_sum_sum {ι : Type*} [Fintype ι] (a b : ι → H) :
    (InnerProductSpace.rankOne Complex (∑ i, a i) (∑ j, b j)).toLinearMap =
      ∑ i, ∑ j, (InnerProductSpace.rankOne Complex (a i) (b j)).toLinearMap := by
  ext x
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.sum_apply]
  change inner Complex (∑ j, b j) x • ∑ i, a i =
    ∑ i, ∑ j, inner Complex (b j) x • a i
  rw [sum_inner, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum]

/-- The rank-one density operator associated with a normalized finite vector. -/
noncomputable def pureDensity (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) : DensityOperator H where
  toOperator := (InnerProductSpace.rankOne Complex psi psi).toLinearMap
  positive := (InnerProductSpace.isPositive_rankOne_self psi).toLinearMap
  trace_one := by
    rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K]
    simpa using congrArg ((↑) : Real → Complex) hpsi

@[simp]
theorem pureDensity_toOperator (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (pureDensity psi hpsi).toOperator =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap :=
  rfl

/-- Density operators are determined by their underlying linear operator. -/
theorem ext_toOperator {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- The canonical rank-one density purification of a finite density operator. -/
noncomputable def spectralPurification (rho : DensityOperator H) :
    DensityOperator (CompositeSystem H H) :=
  pureDensity rho.spectralPurificationVector rho.spectralPurificationVector_normSq

/-- The right partial-trace marginal of a bipartite density operator. -/
noncomputable def rightMarginal {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (omega : DensityOperator (CompositeSystem H K)) : DensityOperator H :=
  partialTraceRightRaw_mapDensity H K omega

/-- The unitary transport which swaps two finite tensor factors. -/
noncomputable def tensorSwap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    UnitaryTransport (CompositeSystem H K) (CompositeSystem K H) := by
  let U := TensorProduct.commIsometry Complex H K
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

@[simp]
theorem tensorSwap_apply_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) (k : K) :
    tensorSwap H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl

/-- The left partial-trace marginal, implemented by a concrete factor swap. -/
noncomputable def leftMarginal {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (omega : DensityOperator (CompositeSystem H K)) : DensityOperator K :=
  rightMarginal ((tensorSwap H K).conjDensity omega)

/-- The finite coefficients of a tensor with respect to a chosen right orthonormal basis. -/
noncomputable def rightTensorCoefficients {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) : Fin (Module.finrank Complex K) →₀ H :=
  TensorProduct.equivFinsuppOfBasisRight b.toBasis psi

/-- The linear coefficient map from the right factor into the left factor of a tensor. -/
noncomputable def rightAmplitude {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) : K →ₗ[Complex] H where
  toFun := fun k => ∑ j, inner Complex (b j) k • rightTensorCoefficients b psi j
  map_add' := by
    intro x y
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [inner_smul_right, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul]

@[simp]
theorem rightAmplitude_apply_basis {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (j : Fin (Module.finrank Complex K)) :
    rightAmplitude b psi (b j) = rightTensorCoefficients b psi j := by
  simp [rightAmplitude, b.inner_eq_ite]

/-- Re-expanding the finite right coefficients reconstructs the original tensor. -/
theorem sum_rightTensorCoefficients_tmul {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    ∑ j, rightTensorCoefficients b psi j ⊗ₜ[Complex] b j = psi := by
  classical
  let a : Fin (Module.finrank Complex K) →₀ H := rightTensorCoefficients b psi
  have hrepr := (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm_apply_apply psi
  change (∑ j, a j ⊗ₜ[Complex] b j) = psi
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hrepr
  rw [← hrepr]
  rw [Finsupp.sum]
  symm
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro j _ hj
    change j ∉ a.support at hj
    have hzero : a j = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hj
    change a j ⊗ₜ[Complex] b j = 0
    simp [hzero]

/-- Swapping a tensor swaps the two factors in its finite right-coefficient expansion. -/
theorem tensorSwap_sum_rightTensorCoefficients {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    tensorSwap H K psi = ∑ j, b j ⊗ₜ[Complex] rightTensorCoefficients b psi j := by
  calc
    tensorSwap H K psi = tensorSwap H K
        (∑ j, rightTensorCoefficients b psi j ⊗ₜ[Complex] b j) :=
      congrArg (tensorSwap H K) (sum_rightTensorCoefficients_tmul b psi).symm
    _ = _ := by simp only [map_sum, tensorSwap_apply_tmul]

/-- A finite Gram operator is the sum of the rank-one columns in an orthonormal basis. -/
theorem comp_adjoint_eq_sum_rankOne {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (A : K →ₗ[Complex] H) :
    A.comp (LinearMap.adjoint A) = ∑ j,
      (InnerProductSpace.rankOne Complex (A (b j)) (A (b j))).toLinearMap := by
  ext x
  change A (LinearMap.adjoint A x) = _
  rw [← b.sum_repr' (LinearMap.adjoint A x)]
  simp only [map_sum, map_smul, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.adjoint_inner_right]
  rfl

/-- The right marginal of a pure tensor density is its finite coefficient Gram operator. -/
theorem rightMarginal_pureDensity_toOperator {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (rightMarginal (pureDensity psi hpsi)).toOperator =
      (rightAmplitude b psi).comp (LinearMap.adjoint (rightAmplitude b psi)) := by
  change partialTraceRightRaw H K
    ((InnerProductSpace.rankOne Complex psi psi).toLinearMap) = _
  conv_lhs => rw [← sum_rightTensorCoefficients_tmul b psi]
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [comp_adjoint_eq_sum_rankOne b]
  simp [b.inner_eq_ite, rightAmplitude_apply_basis]

/-- The left marginal of a pure tensor density, expanded in right tensor coefficients. -/
theorem leftMarginal_pureDensity_toOperator_sum {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (leftMarginal (pureDensity psi hpsi)).toOperator =
      ∑ i, ∑ j,
        (inner Complex (rightTensorCoefficients b psi j) (rightTensorCoefficients b psi i)) •
          (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by
  change partialTraceRightRaw K H
    ((tensorSwap H K).conjOperator
      ((InnerProductSpace.rankOne Complex psi psi).toLinearMap)) = _
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [tensorSwap_sum_rightTensorCoefficients b psi]
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]

omit [FiniteQuantumSystem H] in
/-- Parseval's finite-coordinate identity for an orthonormal basis. -/
theorem inner_eq_sum_reprs
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) (x y : H) :
    inner Complex x y = ∑ i, star (b.repr x i) * b.repr y i := by
  calc
    inner Complex x y = inner Complex (∑ i, b.repr x i • b i) y :=
      congrArg (fun z => inner Complex z y) (b.sum_repr x).symm
    _ = ∑ i, star (b.repr x i) * b.repr y i := by
      rw [sum_inner]
      simp [inner_smul_left, OrthonormalBasis.repr_apply_apply]

/-- The rectangular coefficient matrix of a bipartite vector in chosen orthonormal bases. -/
noncomputable def coefficientMatrix {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    Matrix (Fin (Module.finrank Complex H)) (Fin (Module.finrank Complex K)) Complex :=
  LinearMap.toMatrix bK.toBasis bH.toBasis (rightAmplitude bK psi)

/-- The inner-product matrix entry of a rank-one basis operator. -/
theorem inner_rankOne_basis_apply {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (i j r s : Fin (Module.finrank Complex K)) :
    inner Complex (b r) ((InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap (b s)) =
      (if j = s then if r = i then 1 else 0 else 0) := by
  change inner Complex (b r) (inner Complex (b j) (b s) • b i) = _
  rw [inner_smul_right]
  by_cases hri : r = i
  · subst i
    by_cases hjs : j = s <;> simp [b.inner_eq_ite, hjs]
  · by_cases hjs : j = s <;> simp [b.inner_eq_ite, hri, hjs]

/-- The right marginal matrix is the ordinary left Gram matrix of the tensor coefficients. -/
theorem rightMarginal_pureDensity_toMatrix {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    LinearMap.toMatrix bH.toBasis bH.toBasis
      (rightMarginal (pureDensity psi hpsi)).toOperator =
      coefficientMatrix bH bK psi * (coefficientMatrix bH bK psi).conjTranspose := by
  rw [rightMarginal_pureDensity_toOperator bK psi hpsi]
  rw [LinearMap.toMatrix_comp bH.toBasis bK.toBasis bH.toBasis,
    LinearMap.toMatrix_adjoint bK bH]
  rfl

/-- The left marginal matrix is the transpose of the other finite Gram matrix. -/
theorem leftMarginal_pureDensity_toMatrix {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    LinearMap.toMatrix bK.toBasis bK.toBasis
      (leftMarginal (pureDensity psi hpsi)).toOperator =
      ((coefficientMatrix bH bK psi).conjTranspose * coefficientMatrix bH bK psi).transpose := by
  ext r s
  rw [LinearMap.toMatrix_apply]
  change bK.repr ((leftMarginal (pureDensity psi hpsi)).toOperator (bK s)) r = _
  rw [leftMarginal_pureDensity_toOperator_sum bK psi hpsi]
  rw [OrthonormalBasis.repr_apply_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum]
  simp_rw [inner_smul_right]
  simp_rw [inner_rankOne_basis_apply bK]
  simp [eq_comm]
  rw [inner_eq_sum_reprs bH]
  simp [coefficientMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    LinearMap.toMatrix_apply]

/-- The two pure-state marginals have the same nonzero characteristic roots, with zeros explicit. -/
theorem pureMarginals_balanced_charpoly {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (rightMarginal (pureDensity psi hpsi)).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (leftMarginal (pureDensity psi hpsi)).toOperator.charpoly := by
  let bH := stdOrthonormalBasis Complex H
  let bK := stdOrthonormalBasis Complex K
  let C := coefficientMatrix bH bK psi
  have hright := rightMarginal_pureDensity_toMatrix bH bK psi hpsi
  have hleft := leftMarginal_pureDensity_toMatrix bH bK psi hpsi
  change LinearMap.toMatrix bH.toBasis bH.toBasis
      (rightMarginal (pureDensity psi hpsi)).toOperator = C * C.conjTranspose at hright
  change LinearMap.toMatrix bK.toBasis bK.toBasis
      (leftMarginal (pureDensity psi hpsi)).toOperator =
        (C.conjTranspose * C).transpose at hleft
  calc
    (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (rightMarginal (pureDensity psi hpsi)).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (C * C.conjTranspose).charpoly := by
          congr 1
          rw [← LinearMap.charpoly_toMatrix
            (rightMarginal (pureDensity psi hpsi)).toOperator bH.toBasis, hright]
    _ = (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (C.conjTranspose * C).charpoly := by
          simpa using Matrix.charpoly_mul_comm' C C.conjTranspose
    _ = (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (leftMarginal (pureDensity psi hpsi)).toOperator.charpoly := by
          congr 1
          rw [← LinearMap.charpoly_toMatrix
            (leftMarginal (pureDensity psi hpsi)).toOperator bK.toBasis, hleft,
            Matrix.charpoly_transpose]

/-- Adding any multiplicity of the zero root leaves finite entropy unchanged. -/
theorem vonNeumannEntropy_eq_of_balanced_charpoly {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) (m n : Nat)
    (hcharpoly : (Polynomial.X : Polynomial Complex) ^ m * rho.toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ n * sigma.toOperator.charpoly) :
    rho.vonNeumannEntropy = sigma.vonNeumannEntropy := by
  have hrho : rho.toOperator.charpoly ≠ 0 :=
    (LinearMap.charpoly_monic rho.toOperator).ne_zero
  have hsigma : sigma.toOperator.charpoly ≠ 0 :=
    (LinearMap.charpoly_monic sigma.toOperator).ne_zero
  have hleft : (Polynomial.X : Polynomial Complex) ^ m * rho.toOperator.charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hrho
  have hright : (Polynomial.X : Polynomial Complex) ^ n * sigma.toOperator.charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hsigma
  have hroots := congrArg Polynomial.roots hcharpoly
  rw [Polynomial.roots_mul hleft, Polynomial.roots_mul hright,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  have hsum := congrArg (fun s : Multiset Complex =>
    ((s.map Complex.re).map entropyTerm).sum) hroots
  have hzero (q : Nat) : (q • ({0} : Multiset Real)).sum = 0 := by
    rw [Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_zero]
  unfold vonNeumannEntropy finiteSpectrum
  have hsum' : 0 +
      ((rho.toOperator.charpoly.roots.map Complex.re).map entropyTerm).sum = 0 +
        ((sigma.toOperator.charpoly.roots.map Complex.re).map entropyTerm).sum := by
    simpa [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add, entropyTerm_zero,
      hzero] using hsum
  exact add_left_cancel hsum'

/-- Every finite pure bipartite density has equal base-two entropy on its two marginals. -/
theorem vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy =
      (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
  exact vonNeumannEntropy_eq_of_balanced_charpoly
    (rightMarginal (pureDensity psi hpsi)) (leftMarginal (pureDensity psi hpsi))
    (Module.finrank Complex K) (Module.finrank Complex H)
    (pureMarginals_balanced_charpoly psi hpsi)

/-- The ket map associated with a finite vector. -/
def ket (psi : H) : Complex →ₗ[Complex] H where
  toFun := fun c => c • psi
  map_add' := by
    intro a b
    rw [add_smul]
  map_smul' := by
    intro a b
    change (a * b) • psi = a • (b • psi)
    rw [mul_smul]

/-- The bra map associated with a finite vector. -/
def bra (psi : H) : H →ₗ[Complex] Complex where
  toFun := fun x => inner Complex psi x
  map_add' := by
    intro x y
    rw [inner_add_right]
  map_smul' := by
    intro c x
    rw [inner_smul_right]
    change c * inner Complex psi x = c * inner Complex psi x
    rfl

omit [FiniteQuantumSystem H] in
/-- A normalized ket followed by its bra is the actual rank-one density operator. -/
theorem ket_comp_bra (psi : H) :
    (ket psi).comp (bra psi) = (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  rfl

omit [FiniteQuantumSystem H] in
/-- A normalized bra followed by its ket is the identity on the scalar factor. -/
theorem bra_comp_ket (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (bra psi).comp (ket psi) = 1 := by
  apply LinearMap.ext
  intro c
  change inner Complex psi (c • psi) = c
  have hnorm : (‖psi‖ : Complex) ^ 2 = 1 := by
    exact_mod_cast hpsi
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  calc
    c * (‖psi‖ : Complex) ^ 2 = c * 1 := congrArg (fun z : Complex => c * z) hnorm
    _ = c := mul_one c

/-- The characteristic polynomial of a normalized rank-one density has one root at one. -/
theorem pureDensity_balanced_charpoly (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (Polynomial.X : Polynomial Complex) * (pureDensity psi hpsi).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (Polynomial.X - 1) := by
  let bH := stdOrthonormalBasis Complex H
  let bC : OrthonormalBasis Unit Complex Complex := OrthonormalBasis.singleton Unit Complex
  let A := ket psi
  let B := bra psi
  let C := LinearMap.toMatrix bC.toBasis bH.toBasis A
  let D := LinearMap.toMatrix bH.toBasis bC.toBasis B
  have hCD : (C * D).charpoly = (pureDensity psi hpsi).toOperator.charpoly := by
    rw [← LinearMap.toMatrix_comp bH.toBasis bC.toBasis bH.toBasis]
    change (LinearMap.toMatrix bH.toBasis bH.toBasis (A.comp B)).charpoly = _
    rw [ket_comp_bra]
    exact LinearMap.charpoly_toMatrix _ bH.toBasis
  have hDC : (D * C).charpoly = Polynomial.X - 1 := by
    rw [← LinearMap.toMatrix_comp bC.toBasis bH.toBasis bC.toBasis]
    change (LinearMap.toMatrix bC.toBasis bC.toBasis (B.comp A)).charpoly = _
    rw [bra_comp_ket psi hpsi, LinearMap.charpoly_toMatrix, LinearMap.charpoly_one]
    simp [Module.finrank_self]
  have hmatrix := Matrix.charpoly_mul_comm' C D
  simpa [hCD, hDC, Fintype.card_unique] using hmatrix

/-- A normalized finite rank-one density has zero base-two von Neumann entropy. -/
theorem vonNeumannEntropy_pureDensity (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (pureDensity psi hpsi).vonNeumannEntropy = 0 := by
  have hpure : (pureDensity psi hpsi).toOperator.charpoly ≠ 0 :=
    (LinearMap.charpoly_monic (pureDensity psi hpsi).toOperator).ne_zero
  have hleft : (Polynomial.X : Polynomial Complex) *
      (pureDensity psi hpsi).toOperator.charpoly ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero hpure
  have hright : (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
      (Polynomial.X - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_sub_C_ne_zero 1)
  have hroots := congrArg Polynomial.roots (pureDensity_balanced_charpoly psi hpsi)
  rw [Polynomial.roots_mul hleft, Polynomial.roots_X,
    Polynomial.roots_mul hright, Polynomial.roots_X_pow] at hroots
  have hXone : (Polynomial.X - 1 : Polynomial Complex).roots = {1} := by
    simpa using (Polynomial.roots_X_sub_C (1 : Complex))
  rw [hXone] at hroots
  have hsum := congrArg (fun s : Multiset Complex =>
    ((s.map Complex.re).map entropyTerm).sum) hroots
  have hzero (q : Nat) : (q • ({0} : Multiset Real)).sum = 0 := by
    rw [Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_zero]
  unfold vonNeumannEntropy finiteSpectrum
  simpa [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add, entropyTerm_zero,
    entropyTerm_one, hzero] using hsum

/-- Conditional entropy with the right tensor factor as the conditioned subsystem. -/
def conditionalEntropy {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (omega : DensityOperator (CompositeSystem H K)) : Real :=
  omega.vonNeumannEntropy - (rightMarginal omega).vonNeumannEntropy

/-- A finite pure density has conditional entropy equal to minus its right marginal entropy. -/
theorem conditionalEntropy_pureDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    conditionalEntropy (pureDensity psi hpsi) =
      - (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
  unfold conditionalEntropy
  rw [vonNeumannEntropy_pureDensity]
  ring

/-- A finite pure density has conditional entropy equal to minus either marginal entropy. -/
theorem conditionalEntropy_pureDensity_eq_neg_leftMarginal {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    conditionalEntropy (pureDensity psi hpsi) =
      - (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
  rw [conditionalEntropy_pureDensity,
    vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure psi hpsi]


/-- Tracing out the reference of the explicit spectral purification recovers the input state. -/
theorem rightMarginal_spectralPurification (rho : DensityOperator H) :
    (rightMarginal (spectralPurification rho)).toOperator = rho.toOperator := by
  change partialTraceRightRaw H H (spectralPurification rho).toOperator = rho.toOperator
  rw [spectralPurification, pureDensity_toOperator]
  change partialTraceRightRaw H H
    ((InnerProductSpace.rankOne Complex
      (∑ i, ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) ⊗ₜ[Complex]
        rho.spectralEigenbasis i)
      (∑ j, ((Real.sqrt (rho.spectralEigenvalues j) : Complex) • rho.spectralEigenbasis j) ⊗ₜ[Complex]
        rho.spectralEigenbasis j)).toLinearMap) = rho.toOperator
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simpa [rho.spectralEigenbasis.inner_eq_ite] using rho.spectralDecomposition.symm

/-- The spectral purification vector is invariant under swapping its equal factors. -/
theorem tensorSwap_spectralPurificationVector (rho : DensityOperator H) :
    tensorSwap H H rho.spectralPurificationVector = rho.spectralPurificationVector := by
  unfold spectralPurificationVector
  simp only [map_sum, map_smul, tensorSwap_apply_tmul]

/-- The spectral purification density operator is invariant under factor swap. -/
theorem tensorSwap_conj_spectralPurification (rho : DensityOperator H) :
    (tensorSwap H H).conjDensity (spectralPurification rho) = spectralPurification rho := by
  apply ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, spectralPurification,
    pureDensity_toOperator, QuditSubsystem.conjOperator_rankOne,
    tensorSwap_spectralPurificationVector]

/-- Tracing out the original factor of the spectral purification also recovers the input state. -/
theorem leftMarginal_spectralPurification (rho : DensityOperator H) :
    (leftMarginal (spectralPurification rho)).toOperator = rho.toOperator := by
  rw [leftMarginal, tensorSwap_conj_spectralPurification]
  exact rightMarginal_spectralPurification rho

/-- The concrete right marginal of the spectral purification is equal as a density operator. -/
theorem rightMarginal_spectralPurification_eq (rho : DensityOperator H) :
    rightMarginal (spectralPurification rho) = rho :=
  ext_toOperator (rightMarginal_spectralPurification rho)

/-- The concrete left marginal of the spectral purification is equal as a density operator. -/
theorem leftMarginal_spectralPurification_eq (rho : DensityOperator H) :
    leftMarginal (spectralPurification rho) = rho :=
  ext_toOperator (leftMarginal_spectralPurification rho)

/-- The spectral purification supplies the exact conditional-entropy identity used downstream. -/
theorem conditionalEntropy_spectralPurification (rho : DensityOperator H) :
    conditionalEntropy (spectralPurification rho) = -rho.vonNeumannEntropy := by
  calc
    conditionalEntropy (spectralPurification rho) =
      - (rightMarginal (spectralPurification rho)).vonNeumannEntropy := by
        exact conditionalEntropy_pureDensity _ _
    _ = -rho.vonNeumannEntropy := by rw [rightMarginal_spectralPurification_eq]

omit [FiniteQuantumSystem H] in
/-- Tensoring two rank-one operators yields the rank one on the tensor product. -/
theorem tensorMap_rankOne {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (x y : H) (u v : K) :
    TensorProduct.map (InnerProductSpace.rankOne Complex x y).toLinearMap
      (InnerProductSpace.rankOne Complex u v).toLinearMap =
      (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] u) (y ⊗ₜ[Complex] v)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      change ((inner Complex y h) • x) ⊗ₜ[Complex] ((inner Complex v k) • u) =
        (inner Complex (y ⊗ₜ[Complex] v) (h ⊗ₜ[Complex] k)) • (x ⊗ₜ[Complex] u)
      rw [TensorProduct.inner_tmul, TensorProduct.smul_tmul, smul_smul,
        TensorProduct.tmul_smul]
  | add z w hz hw =>
      simp [map_add, hz, hw]

/-- Tensor product is additive in each finite operator argument. -/
theorem tensorMap_sum_sum {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → Operator H) (b : κ → Operator K) :
    TensorProduct.map (∑ i, a i) (∑ j, b j) = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
  classical
  have hleft (s : Finset ι) :
      TensorProduct.map (∑ i ∈ s, a i) (∑ j, b j) =
        ∑ i ∈ s, TensorProduct.map (a i) (∑ j, b j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
  have hright (i : ι) (t : Finset κ) :
      TensorProduct.map (a i) (∑ j ∈ t, b j) =
        ∑ j ∈ t, TensorProduct.map (a i) (b j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
        simp [Finset.sum_insert hj, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
        ∑ i, TensorProduct.map (a i) (∑ j, b j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ

/-- The actual finite tensor product of two density operators. -/
noncomputable def tensorDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    DensityOperator (CompositeSystem H K) where
  toOperator := TensorProduct.map rho.toOperator sigma.toOperator
  positive := by
    rw [rho.spectralDecomposition, sigma.spectralDecomposition, tensorMap_sum_sum]
    apply LinearMap.isPositive_sum Finset.univ
    intro i _
    apply LinearMap.isPositive_sum Finset.univ
    intro j _
    rw [tensorMap_rankOne]
    let w : CompositeSystem H K :=
      ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) ⊗ₜ[Complex]
        ((Real.sqrt (sigma.spectralEigenvalues j) : Complex) • sigma.spectralEigenbasis j)
    exact (InnerProductSpace.isPositive_rankOne_self w).toLinearMap
  trace_one := by
    rw [LinearMap.trace_tensorProduct', rho.trace_one, sigma.trace_one, mul_one]

@[simp]
theorem tensorDensity_toOperator {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).toOperator = TensorProduct.map rho.toOperator sigma.toOperator :=
  rfl

/-- A finite orthonormal eigenbasis computes the characteristic-polynomial entropy directly. -/
theorem vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis {ι : Type*}
    [Fintype ι] [DecidableEq ι] (rho : DensityOperator H)
    (b : OrthonormalBasis ι Complex H) (e : ι → Real)
    (happly : ∀ i, rho.toOperator (b i) = (e i : Complex) • b i) :
    rho.vonNeumannEntropy = ∑ i, entropyTerm (e i) := by
  classical
  unfold vonNeumannEntropy finiteSpectrum
  rw [← LinearMap.charpoly_toMatrix rho.toOperator b.toBasis]
  have hmatrix : LinearMap.toMatrix b.toBasis b.toBasis rho.toOperator =
      Matrix.diagonal fun i => (e i : Complex) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (rho.toOperator (b j)) i = _
    rw [happly]
    rw [map_smul]
    change (e j : Complex) * b.repr (b j) i = _
    rw [OrthonormalBasis.repr_apply_apply]
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, b.inner_eq_ite, hij]
  rw [hmatrix, Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp

/-- The tensor density is diagonal in the tensor product of the two spectral bases. -/
theorem tensorDensity_apply_spectralTensorBasis {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K)
    (i : Fin (Module.finrank Complex H)) (j : Fin (Module.finrank Complex K)) :
    (tensorDensity rho sigma).toOperator
        (rho.spectralEigenbasis i ⊗ₜ[Complex] sigma.spectralEigenbasis j) =
      ((rho.spectralEigenvalues i * sigma.spectralEigenvalues j : Real) : Complex) •
        (rho.spectralEigenbasis i ⊗ₜ[Complex] sigma.spectralEigenbasis j) := by
  rw [tensorDensity_toOperator, TensorProduct.map_tmul]
  unfold spectralEigenbasis spectralEigenvalues
  rw [rho.positive.isSymmetric.apply_eigenvectorBasis,
    sigma.positive.isSymmetric.apply_eigenvectorBasis]
  rw [TensorProduct.smul_tmul, smul_smul, TensorProduct.tmul_smul]
  norm_cast

/-- The finite tensor density has the pairwise products of the two spectral weights. -/
theorem vonNeumannEntropy_tensorDensity_eq_double_sum {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).vonNeumannEntropy = ∑ i, ∑ j,
      entropyTerm (rho.spectralEigenvalues i * sigma.spectralEigenvalues j) := by
  let b := rho.spectralEigenbasis.tensorProduct sigma.spectralEigenbasis
  have hdiagonal := vonNeumannEntropy_eq_sum_of_orthonormal_eigenbasis
    (tensorDensity rho sigma) b
    (fun ij => rho.spectralEigenvalues ij.1 * sigma.spectralEigenvalues ij.2) (by
      intro ij
      dsimp [b]
      rcases ij with ⟨i, j⟩
      rw [OrthonormalBasis.tensorProduct_apply]
      exact tensorDensity_apply_spectralTensorBasis rho sigma i j)
  rw [hdiagonal, Fintype.sum_prod_type]

/-- The base-two entropy term distributes over nonnegative spectral products. -/
theorem entropyTerm_mul (x y : Real) (hx : 0 <= x) (hy : 0 <= y) :
    entropyTerm (x * y) = y * entropyTerm x + x * entropyTerm y := by
  by_cases hx0 : x = 0
  · subst x
    simp
  by_cases hy0 : y = 0
  · subst y
    simp
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  simp only [entropyTerm, if_neg hxy0, if_neg hx0, if_neg hy0]
  rw [Real.logb_mul hx0 hy0]
  ring

/-- Base-two von Neumann entropy is additive for finite tensor density operators. -/
theorem vonNeumannEntropy_tensorDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    (tensorDensity rho sigma).vonNeumannEntropy =
      rho.vonNeumannEntropy + sigma.vonNeumannEntropy := by
  rw [vonNeumannEntropy_tensorDensity_eq_double_sum,
    rho.vonNeumannEntropy_eq_sum_spectralEigenvalues,
    sigma.vonNeumannEntropy_eq_sum_spectralEigenvalues]
  have hterm (i : Fin (Module.finrank Complex H))
      (j : Fin (Module.finrank Complex K)) :
      entropyTerm (rho.spectralEigenvalues i * sigma.spectralEigenvalues j) =
        sigma.spectralEigenvalues j * entropyTerm (rho.spectralEigenvalues i) +
          rho.spectralEigenvalues i * entropyTerm (sigma.spectralEigenvalues j) := by
    exact entropyTerm_mul _ _ (rho.spectralEigenvalues_nonnegative i)
      (sigma.spectralEigenvalues_nonnegative j)
  simp_rw [hterm]
  have hfirst :
      (∑ i, ∑ j, sigma.spectralEigenvalues j * entropyTerm (rho.spectralEigenvalues i)) =
        (∑ j, sigma.spectralEigenvalues j) *
          (∑ i, entropyTerm (rho.spectralEigenvalues i)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsecond :
      (∑ i, ∑ j, rho.spectralEigenvalues i * entropyTerm (sigma.spectralEigenvalues j)) =
        (∑ i, rho.spectralEigenvalues i) *
          (∑ j, entropyTerm (sigma.spectralEigenvalues j)) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  simp_rw [Finset.sum_add_distrib]
  rw [hfirst, hsecond,
    rho.spectralEigenvalues_sum_eq_one, sigma.spectralEigenvalues_sum_eq_one]
  ring

end DensityOperator

end
end Semantics
end QEC
