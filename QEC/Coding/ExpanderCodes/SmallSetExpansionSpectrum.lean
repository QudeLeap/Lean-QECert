import QEC.Coding.ExpanderCodes.SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Operator-norm form of finite graph spectral expansion

The PK22 graph interface uses a two-function bilinear estimate, while
representation-theoretic proofs of expansion naturally bound the `ℓ²` norm
of the adjacency operator on the mean-zero subspace.  This file proves the
finite-dimensional bridge between those formulations.
-/

namespace QEC.Coding.SmallSetExpansion

universe u

variable {V : Type u}

/-- A finite-dimensional self-adjoint operator whose eigenvalues all lie in
`[-spectral, spectral]` has the corresponding squared operator-norm bound.
This is the spectral-theorem step used after identifying Cayley adjacency
with a Hecke operator. -/
theorem LinearMap.IsSymmetric.norm_sq_apply_le_of_abs_eigenvalues_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {spectral : ℝ} (hSpectralNonnegative : 0 ≤ spectral)
    (hEigen : ∀ i : Fin (Module.finrank ℂ E),
      |hT.eigenvalues rfl i| ≤ spectral)
    (x : E) :
    ‖T x‖ ^ 2 ≤ spectral ^ 2 * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  have hCoordinate (i : Fin (Module.finrank ℂ E)) :
      ‖((hT.eigenvalues rfl i : ℝ) : ℂ) * (b.repr x) i‖ ^ 2 ≤
        spectral ^ 2 * ‖(b.repr x) i‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hAbsNonnegative : 0 ≤ |hT.eigenvalues rfl i| := abs_nonneg _
    have hSquare : |hT.eigenvalues rfl i| ^ 2 ≤ spectral ^ 2 :=
      (sq_le_sq₀ hAbsNonnegative hSpectralNonnegative).2 (hEigen i)
    calc
      (|hT.eigenvalues rfl i| * ‖(b.repr x) i‖) ^ 2 =
          |hT.eigenvalues rfl i| ^ 2 * ‖(b.repr x) i‖ ^ 2 := by ring
      _ ≤ spectral ^ 2 * ‖(b.repr x) i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hSquare (sq_nonneg _)
  calc
    ‖T x‖ ^ 2 = ‖b.repr (T x)‖ ^ 2 := by
      rw [b.repr.norm_map]
    _ = ∑ i, ‖(b.repr (T x)) i‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    _ = ∑ i, ‖((hT.eigenvalues rfl i : ℝ) : ℂ) *
          (b.repr x) i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show (b.repr (T x)) i =
          ((hT.eigenvalues rfl i : ℝ) : ℂ) * (b.repr x) i by
        simpa [b] using
          hT.eigenvectorBasis_apply_self_apply rfl x i]
    _ ≤ ∑ i, spectral ^ 2 * ‖(b.repr x) i‖ ^ 2 :=
      Finset.sum_le_sum fun i _hi => hCoordinate i
    _ = spectral ^ 2 * ∑ i, ‖(b.repr x) i‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = spectral ^ 2 * ‖b.repr x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    _ = spectral ^ 2 * ‖x‖ ^ 2 := by rw [b.repr.norm_map]

/-- The unnormalized adjacency operator has `ℓ²` norm at most `spectral` on
mean-zero real functions. -/
def HasMeanZeroOperatorBound [Fintype V]
    (M : WeightedGraph V) (spectral : ℝ) : Prop :=
  ∀ g : V → ℝ,
    (∑ v, g v) = 0 →
      (∑ v, (weightedNeighborSum M g v) ^ 2) ≤
        spectral ^ 2 * ∑ v, (g v) ^ 2

/-- Complexification of the unnormalized weighted adjacency operator. -/
noncomputable def complexWeightedNeighborSum [Fintype V]
    (M : WeightedGraph V) (g : V → ℂ) (v : V) : ℂ :=
  ∑ u, (M v u : ℂ) * g u

/-- The complex `ℓ²` operator-norm statement naturally supplied by unitary
representation theory. -/
def HasMeanZeroComplexOperatorBound [Fintype V]
    (M : WeightedGraph V) (spectral : ℝ) : Prop :=
  ∀ g : V → ℂ,
    (∑ v, g v) = 0 →
      (∑ v, ‖complexWeightedNeighborSum M g v‖ ^ 2) ≤
        spectral ^ 2 * ∑ v, ‖g v‖ ^ 2

@[simp] theorem complexWeightedNeighborSum_real
    [Fintype V] (M : WeightedGraph V) (g : V → ℝ) (v : V) :
    complexWeightedNeighborSum M (fun u => (g u : ℂ)) v =
      (weightedNeighborSum M g v : ℂ) := by
  classical
  unfold complexWeightedNeighborSum weightedNeighborSum
  push_cast
  rfl

/-- A complex adjacency-operator bound restricts to the real mean-zero
subspace without changing its spectral constant. -/
theorem HasMeanZeroComplexOperatorBound.toReal
    [Fintype V]
    {M : WeightedGraph V} {spectral : ℝ}
    (hComplex : HasMeanZeroComplexOperatorBound M spectral) :
    HasMeanZeroOperatorBound M spectral := by
  intro g hg
  have hMean : (∑ v, (g v : ℂ)) = 0 := by
    exact_mod_cast hg
  have hBound := hComplex (fun v => (g v : ℂ)) hMean
  simpa [complexWeightedNeighborSum_real, sq_abs] using hBound

/-- The complex adjacency operator on the canonical finite-dimensional
Euclidean coordinate space. -/
noncomputable def complexAdjacencyEuclidean [Fintype V]
    (M : WeightedGraph V) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V where
  toFun f := WithLp.toLp 2 (fun v =>
    complexWeightedNeighborSum M (fun u => f u) v)
  map_add' f g := by
    apply WithLp.ofLp_injective 2
    funext v
    simp [complexWeightedNeighborSum, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply WithLp.ofLp_injective 2
    funext v
    simp only [complexWeightedNeighborSum, PiLp.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _hu
    ring

@[simp] theorem complexAdjacencyEuclidean_apply
    [Fintype V] (M : WeightedGraph V)
    (f : EuclideanSpace ℂ V) (v : V) :
    complexAdjacencyEuclidean M f v =
      complexWeightedNeighborSum M (fun u => f u) v := rfl

/-- Symmetry of a weighted graph is exactly self-adjointness of its complex
Euclidean adjacency operator. -/
theorem complexAdjacencyEuclidean_isSymmetric
    [Fintype V]
    (M : WeightedGraph V) (hSymmetric : IsSymmetric M) :
    (complexAdjacencyEuclidean M).IsSymmetric := by
  classical
  intro f g
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (∑ v, g v * star (∑ u, (M v u : ℂ) * f u)) =
      ∑ u, (∑ v, (M u v : ℂ) * g v) * star (f u)
  simp_rw [star_sum, star_mul, star_natCast]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [hSymmetric]
  ring

/-- The constant-one vector in the complex Euclidean coordinate space. -/
noncomputable def constantEuclideanVector [Fintype V] :
    EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun _ => 1)

@[simp] theorem constantEuclideanVector_apply
    [Fintype V] (v : V) :
    constantEuclideanVector (V := V) v = 1 := rfl

@[simp] theorem inner_constantEuclideanVector
    [Fintype V] (f : EuclideanSpace ℂ V) :
    inner ℂ (constantEuclideanVector (V := V)) f = ∑ v, f v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ v, f v * star (1 : ℂ)) = ∑ v, f v
  simp

/-- Adjacency with the constant eigenmode removed.  Its eigenvalues are the
nontrivial adjacency eigenvalues together with zero, so it lets the standard
finite-dimensional spectral theorem express the mean-zero bound without a
type-class-sensitive restriction to a subtype. -/
noncomputable def centeredAdjacencyEuclidean [Fintype V]
    (M : WeightedGraph V) (degree : Nat) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V :=
  complexAdjacencyEuclidean M -
    (((degree : ℂ) / (Fintype.card V : ℂ)) •
      (InnerProductSpace.rankOne ℂ
        (constantEuclideanVector (V := V))
        (constantEuclideanVector (V := V))).toLinearMap)

/-- On a mean-zero vector, centered adjacency is ordinary adjacency. -/
theorem centeredAdjacencyEuclidean_apply_of_sum_eq_zero
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (f : EuclideanSpace ℂ V) (hf : (∑ v, f v) = 0) :
    centeredAdjacencyEuclidean M degree f =
      complexAdjacencyEuclidean M f := by
  simp [centeredAdjacencyEuclidean, hf]

/-- Centered adjacency is self-adjoint whenever the weighted graph is
symmetric. -/
theorem centeredAdjacencyEuclidean_isSymmetric
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) :
    (centeredAdjacencyEuclidean M degree).IsSymmetric := by
  apply (complexAdjacencyEuclidean_isSymmetric M hSymmetric).sub
  exact (InnerProductSpace.isSymmetric_rankOne_self
    (constantEuclideanVector (V := V))).smul (by simp)

/-- Sum of the coordinates of a finite Euclidean vector. -/
noncomputable def coordinateSum [Fintype V] :
    EuclideanSpace ℂ V →ₗ[ℂ] ℂ where
  toFun f := ∑ v, f v
  map_add' f g := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum]

/-- Orthogonal-to-constants coordinate subspace, expressed by its equivalent
zero coordinate-sum equation. -/
noncomputable def meanZeroEuclideanSubspace [Fintype V] :
    Submodule ℂ (EuclideanSpace ℂ V) :=
  LinearMap.ker coordinateSum

@[simp] theorem mem_meanZeroEuclideanSubspace_iff
    [Fintype V] (f : EuclideanSpace ℂ V) :
    f ∈ meanZeroEuclideanSubspace ↔ (∑ v, f v) = 0 := by
  rfl

/-- For a symmetric regular weighted graph, complex adjacency preserves the
coordinate sum and multiplies it by the degree. -/
theorem sum_complexWeightedNeighborSum_eq_degree_mul_sum
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (g : V → ℂ) :
    ∑ v, complexWeightedNeighborSum M g v = degree * ∑ v, g v := by
  classical
  unfold complexWeightedNeighborSum
  rw [Finset.sum_comm]
  calc
    (∑ u, ∑ v, (M v u : ℂ) * g u) =
        ∑ u, g u * ∑ v, (M u v : ℂ) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hSymmetric]
      ring
    _ = ∑ u, g u * degree := by
      apply Finset.sum_congr rfl
      intro u _hu
      congr 1
      exact_mod_cast hRegular u
    _ = degree * ∑ u, g u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring

/-- Adjacency restricted to the invariant mean-zero Euclidean subspace. -/
noncomputable def meanZeroAdjacency
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree) :
    meanZeroEuclideanSubspace (V := V) →ₗ[ℂ]
      meanZeroEuclideanSubspace (V := V) :=
  (complexAdjacencyEuclidean M).restrict fun f hf => by
    rw [mem_meanZeroEuclideanSubspace_iff] at hf ⊢
    rw [show (∑ v, complexAdjacencyEuclidean M f v) =
        degree * ∑ v, f v by
      simpa using sum_complexWeightedNeighborSum_eq_degree_mul_sum
        M degree hSymmetric hRegular (fun v => f v),
      hf, mul_zero]

@[simp] theorem meanZeroAdjacency_apply_coe
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (f : meanZeroEuclideanSubspace (V := V)) (v : V) :
    (meanZeroAdjacency M degree hSymmetric hRegular f :
      EuclideanSpace ℂ V) v =
      complexWeightedNeighborSum M (fun u => f.1 u) v := rfl

/-- A bound on every eigenvalue of centered adjacency gives the complex
mean-zero adjacency operator bound.  This isolates the representation-
theoretic input needed for an LPS Ramanujan theorem. -/
theorem hasMeanZeroComplexOperatorBound_of_abs_meanZeroEigenvalues_le
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M)
    {spectral : ℝ} (hSpectralNonnegative : 0 ≤ spectral)
    (hEigen : ∀ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ V)),
      |(centeredAdjacencyEuclidean_isSymmetric M degree hSymmetric).eigenvalues
          rfl i| ≤ spectral) :
    HasMeanZeroComplexOperatorBound M spectral := by
  intro g hg
  let f : EuclideanSpace ℂ V := WithLp.toLp 2 g
  have hBound := LinearMap.IsSymmetric.norm_sq_apply_le_of_abs_eigenvalues_le
    (centeredAdjacencyEuclidean_isSymmetric M degree hSymmetric)
    hSpectralNonnegative hEigen f
  have hCentered : centeredAdjacencyEuclidean M degree f =
      complexAdjacencyEuclidean M f :=
    centeredAdjacencyEuclidean_apply_of_sum_eq_zero M degree f hg
  rw [hCentered] at hBound
  simpa [f, EuclideanSpace.norm_sq_eq] using hBound

private theorem abs_sum_mul_le_sqrt_mul_sqrt
    [Fintype V] (f g : V → ℝ) :
    |∑ v, f v * g v| ≤
      Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := by
  calc
    |∑ v, f v * g v| ≤ ∑ v, |f v * g v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v, |f v| * |g v| := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [abs_mul]
    _ ≤ Real.sqrt (∑ v, |f v| ^ 2) *
        Real.sqrt (∑ v, |g v| ^ 2) := by
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := by
      simp_rw [sq_abs]
      rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- An `ℓ²` adjacency-operator bound implies the two-function bilinear bound
used by expander mixing. -/
theorem HasMeanZeroOperatorBound.toBilinearBound
    [Fintype V]
    {M : WeightedGraph V} {spectral : ℝ}
    (hSpectralNonnegative : 0 ≤ spectral)
    (hOperator : HasMeanZeroOperatorBound M spectral) :
    HasMeanZeroBilinearBound M spectral := by
  intro f g _hf hg
  have hCauchy := abs_sum_mul_le_sqrt_mul_sqrt
    f (weightedNeighborSum M g)
  have hOperator' := hOperator g hg
  have hNormF : 0 ≤ ∑ v, (f v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNormG : 0 ≤ ∑ v, (g v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hNormA : 0 ≤ ∑ v, (weightedNeighborSum M g v) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hProduct :
      (∑ v, (f v) ^ 2) *
          (∑ v, (weightedNeighborSum M g v) ^ 2) ≤
        (∑ v, (f v) ^ 2) *
          (spectral ^ 2 * ∑ v, (g v) ^ 2) :=
    mul_le_mul_of_nonneg_left hOperator' hNormF
  have hRoot := Real.sqrt_le_sqrt hProduct
  calc
    |adjacencyPairing M f g| =
        |∑ v, f v * weightedNeighborSum M g v| := by
      rfl
    _ ≤ Real.sqrt ((∑ v, (f v) ^ 2) *
          ∑ v, (weightedNeighborSum M g v) ^ 2) := hCauchy
    _ ≤ Real.sqrt ((∑ v, (f v) ^ 2) *
          (spectral ^ 2 * ∑ v, (g v) ^ 2)) := hRoot
    _ = spectral *
        Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := by
      rw [show
        (∑ v, (f v) ^ 2) *
              (spectral ^ 2 * ∑ v, (g v) ^ 2) =
            spectral ^ 2 *
              ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg spectral), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hSpectralNonnegative]

/-- Symmetry and regularity make adjacency preserve the mean-zero subspace. -/
theorem sum_weightedNeighborSum_eq_degree_mul_sum
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (g : V → ℝ) :
    ∑ v, weightedNeighborSum M g v = degree * ∑ v, g v := by
  classical
  unfold weightedNeighborSum
  rw [Finset.sum_comm]
  calc
    (∑ u, ∑ v, (M v u : ℝ) * g u) =
        ∑ u, g u * ∑ v, (M u v : ℝ) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hSymmetric]
      ring
    _ = ∑ u, g u * degree := by
      apply Finset.sum_congr rfl
      intro u _hu
      congr 1
      exact_mod_cast hRegular u
    _ = degree * ∑ u, g u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring

/-- For a symmetric regular finite graph, the bilinear and adjacency
operator-norm formulations of the mean-zero spectral estimate are
equivalent. -/
theorem hasMeanZeroBilinearBound_iff_operatorBound
    [Fintype V]
    {M : WeightedGraph V} {degree : Nat} {spectral : ℝ}
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (hSpectralNonnegative : 0 ≤ spectral) :
    HasMeanZeroBilinearBound M spectral ↔
      HasMeanZeroOperatorBound M spectral := by
  constructor
  · intro hBilinear g hg
    let Ag := weightedNeighborSum M g
    have hAg : (∑ v, Ag v) = 0 := by
      dsimp [Ag]
      rw [sum_weightedNeighborSum_eq_degree_mul_sum
        M degree hSymmetric hRegular g, hg, mul_zero]
    have hBound := hBilinear Ag g hAg hg
    have hNormA : 0 ≤ ∑ v, (Ag v) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hNormG : 0 ≤ ∑ v, (g v) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hPairing : adjacencyPairing M Ag g = ∑ v, (Ag v) ^ 2 := by
      unfold adjacencyPairing
      change (∑ v, Ag v * Ag v) = ∑ v, (Ag v) ^ 2
      simp only [pow_two]
    rw [hPairing, abs_of_nonneg hNormA] at hBound
    by_cases hZero : ∑ v, (Ag v) ^ 2 = 0
    · rw [hZero]
      positivity
    · have hPositive : 0 < ∑ v, (Ag v) ^ 2 :=
        lt_of_le_of_ne hNormA (Ne.symm hZero)
      have hSquareRootPositive :
          0 < Real.sqrt (∑ v, (Ag v) ^ 2) := Real.sqrt_pos.2 hPositive
      have hRootProduct :
          Real.sqrt
              ((∑ v, (Ag v) ^ 2) * ∑ v, (g v) ^ 2) =
            Real.sqrt (∑ v, (Ag v) ^ 2) *
              Real.sqrt (∑ v, (g v) ^ 2) := by
        rw [Real.sqrt_mul hNormA]
      rw [hRootProduct] at hBound
      have hCancel :
          Real.sqrt (∑ v, (Ag v) ^ 2) ≤
            spectral * Real.sqrt (∑ v, (g v) ^ 2) := by
        nlinarith [Real.sq_sqrt hNormA]
      nlinarith [Real.sq_sqrt hNormA, Real.sq_sqrt hNormG]
  · exact HasMeanZeroOperatorBound.toBilinearBound hSpectralNonnegative

end QEC.Coding.SmallSetExpansion
