import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.ArithmeticIntersection
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.GlobalBuildingLattice
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.InfinityLattice
import QEC.Coding.HighDimensionalExpander.Combinatorics.LocalLinkReduction

/-!
# Integral cyclic coordinates at the Cartwright--Steger building place

The reductions of the matrices `e_i z^k` form a basis of the full residue
matrix algebra.  This is proved from Dedekind independence of the distinct
Frobenius automorphisms and the actual constant-field basis.  It is the
nondegeneracy input needed to recover integral cyclic coordinates from an
integral local matrix; no external change-of-basis matrix is assumed.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

/-- The residue matrix of the cyclic basis vector `e_i z^k`. -/
noncomputable def residueCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P) :=
  constantRegularMatrix P r (constantBasis P r p.1) *
    (frobeniusGL P r :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
        (p.2 : ℕ)

theorem toLin_residueCyclicBasisVector_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank)
    (x : ConstantExtension P r) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (residueCyclicBasisVector P r p) x =
      (constantBasis P r p.1) *
        ((constantFrobenius P r) ^ (p.2 : ℕ)) x := by
  rw [residueCyclicBasisVector]
  rw [Matrix.toLin_mul_apply (constantBasis P r) (constantBasis P r)
    (constantBasis P r)]
  rw [toLin_constantRegularMatrix]
  change (constantBasis P r p.1) *
      Matrix.toLin (constantBasis P r) (constantBasis P r)
        ((frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) ^
            (p.2 : ℕ)) x = _
  rw [Matrix.toLin_pow, frobeniusGL_coe, Matrix.toLin_toMatrix]
  simp [Module.End.coe_pow]

/-- The complete family of residue cyclic matrices is linearly independent.
The proof first groups a relation by the Frobenius exponent, uses Dedekind
independence over the constant extension, and then reads the coefficients in
the fixed constant-field basis. -/
theorem residueCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (BaseField P) (residueCyclicBasisVector P r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  have hfun : ∀ x : ConstantExtension P r,
      ∑ k : Fin r.matrixRank,
        (∑ j : Fin r.matrixRank,
          algebraMap (BaseField P) (ConstantExtension P r) (a (j, k)) *
            constantBasis P r j) *
          ((constantFrobenius P r) ^ (k : ℕ)) x = 0 := by
    intro x
    calc
      _ = ∑ k : Fin r.matrixRank, ∑ j : Fin r.matrixRank,
          a (j, k) •
            Matrix.toLin (constantBasis P r) (constantBasis P r)
              (residueCyclicBasisVector P r (j, k)) x := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [toLin_residueCyclicBasisVector_apply]
          simp [Algebra.smul_def, mul_assoc]
      _ = Matrix.toLin (constantBasis P r) (constantBasis P r)
          (∑ q, a q • residueCyclicBasisVector P r q) x := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp
      _ = 0 := by rw [ha]; simp
  let f : Fin r.matrixRank → ConstantExtension P r := fun k =>
    ∑ j : Fin r.matrixRank,
      algebraMap (BaseField P) (ConstantExtension P r) (a (j, k)) *
        constantBasis P r j
  have hfrob : ∀ k, f k = 0 := by
    have hrel : ∑ k : Fin r.matrixRank,
        f k • ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom.toLinearMap = 0 := by
      apply LinearMap.ext
      intro x
      simpa [f, Algebra.smul_def] using hfun x
    have hinj : Function.Injective
        (fun k : Fin r.matrixRank =>
          ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom) := by
      intro i j hij
      have hpowers : (constantFrobenius P r) ^ (i : ℕ) =
          (constantFrobenius P r) ^ (j : ℕ) := by
        apply AlgEquiv.ext
        intro x
        exact DFunLike.congr_fun hij x
      apply Fin.ext
      apply pow_injOn_Iio_orderOf (x := constantFrobenius P r)
      · simpa [constantFrobenius_order P r] using i.isLt
      · simpa [constantFrobenius_order P r] using j.isLt
      · exact hpowers
    have hli : LinearIndependent (ConstantExtension P r)
        (fun k : Fin r.matrixRank =>
          ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom.toLinearMap) :=
      (linearIndependent_algHom_toLinearMap
        (BaseField P) (ConstantExtension P r) (ConstantExtension P r)).comp
          (fun k : Fin r.matrixRank =>
            ((constantFrobenius P r) ^ (k : ℕ)).toAlgHom) hinj
    exact Fintype.linearIndependent_iff.mp hli f hrel
  have hp := hfrob p.2
  have hp' : (∑ j : Fin r.matrixRank,
      a (j, p.2) • constantBasis P r j) = 0 := by
    simpa [f, Algebra.smul_def] using hp
  have hpcoord := congrArg (fun x => (constantBasis P r).repr x p.1) hp'
  simp only [map_sum, map_smul] at hpcoord
  simp_rw [(constantBasis P r).repr_self] at hpcoord
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, map_zero,
    Finsupp.zero_apply] at hpcoord
  have hsingle : (∑ c : Fin r.matrixRank,
      Finsupp.single c (a (c, p.2))) p.1 = a p := by
    simp [Finsupp.single_apply]
  rw [hsingle] at hpcoord
  exact hpcoord

/-- The residue cyclic family, bundled as a basis of the full matrix algebra. -/
noncomputable def residueCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank) (BaseField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) :=
  Module.Basis.mk (residueCyclicBasisVector_linearIndependent P r)
    ((residueCyclicBasisVector_linearIndependent P r).span_eq_top_of_card_eq_finrank
      (by simp [Module.finrank_matrix])).ge

@[simp] theorem residueCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    residueCyclicBasis P r p = residueCyclicBasisVector P r p := by
  simp [residueCyclicBasis]

/-- The integral lift of the cyclic basis vector at the building place. -/
noncomputable def buildingIntegralCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P) :=
  (constantRegularMatrix P r (constantBasis P r p.1)).map PowerSeries.C *
    ((buildingCyclicGeneratorIntegralGL P r :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingIntegerRing P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)) ^
          (p.2 : ℕ)

/-- Reduction modulo `y` of an integral cyclic basis vector. -/
@[simp] theorem buildingIntegralCyclicBasisVector_reduction
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingIntegralCyclicBasisVector P r p).map PowerSeries.constantCoeff =
      residueCyclicBasisVector P r p := by
  rw [buildingIntegralCyclicBasisVector, residueCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow]
  congr 1
  exact congrArg
    (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P) =>
      M ^ (p.2 : ℕ))
    (congrArg Units.val
      (powerSeriesReductionGL_buildingCyclicGeneratorIntegralGL P r))

/-- Inclusion of an integral cyclic vector into the local field is the
corresponding vector used by the cyclic-algebra representation. -/
@[simp] theorem buildingIntegralCyclicBasisVector_toLocal
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingIntegralCyclicBasisVector P r p).map
        (SphericalHecke.integerEmbedding (BaseField P)) =
      buildingCyclicBasisVector P r p := by
  rw [buildingIntegralCyclicBasisVector, buildingCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow]
  congr 1
  have hz := congrArg Units.val
    (buildingCyclicGeneratorIntegralGL_toLocal P r)
  change (↑(buildingCyclicGeneratorIntegralGL P r) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)).map
        (SphericalHecke.integerEmbedding (BaseField P)) =
      (buildingCyclicGeneratorGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) at hz
  rw [buildingCyclicGeneratorGL_coe] at hz
  exact congrArg
    (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P) => M ^ (p.2 : ℕ))
    hz

/-- The determinant of the integral cyclic family in the standard matrix
basis is a unit, detected after reduction modulo `y`. -/
theorem buildingIntegralCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit ((Matrix.stdBasis (BuildingIntegerRing P)
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (buildingIntegralCyclicBasisVector P r)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hmap : PowerSeries.constantCoeff
      ((Matrix.stdBasis (BuildingIntegerRing P)
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (buildingIntegralCyclicBasisVector P r)) =
      (Matrix.stdBasis (BaseField P)
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (residueCyclicBasisVector P r) := by
    simp only [Module.Basis.det_apply]
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro p q
    change PowerSeries.constantCoeff
        (buildingIntegralCyclicBasisVector P r q p.1 p.2) =
      residueCyclicBasisVector P r q p.1 p.2
    exact congrFun (congrFun
      (buildingIntegralCyclicBasisVector_reduction P r q) p.1) p.2
  rw [hmap]
  let hli := residueCyclicBasisVector_linearIndependent P r
  exact (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (BaseField P)
      (Fin r.matrixRank) (Fin r.matrixRank))).mp
        ⟨hli, hli.span_eq_top_of_card_eq_finrank
          (by simp [Module.finrank_matrix])⟩

/-- The integral cyclic family is a basis of all integral matrices. -/
noncomputable def buildingIntegralCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (BuildingIntegerRing P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingIntegerRing P)) :=
  Module.Basis.mk
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingIntegerRing P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingIntegralCyclicBasisVector_det_isUnit P r)).1
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingIntegerRing P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingIntegralCyclicBasisVector_det_isUnit P r)).2.ge

@[simp] theorem buildingIntegralCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    buildingIntegralCyclicBasis P r p =
      buildingIntegralCyclicBasisVector P r p := by
  simp [buildingIntegralCyclicBasis]

/-- The local cyclic family is a basis of the full local matrix algebra. -/
theorem buildingCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) :
    IsUnit ((Matrix.stdBasis (BuildingLocalField P)
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (buildingCyclicBasisVector P r)) := by
  have hint := buildingIntegralCyclicBasisVector_det_isUnit P r
  have hmapped :
      SphericalHecke.integerEmbedding (BaseField P)
          ((Matrix.stdBasis (BuildingIntegerRing P)
            (Fin r.matrixRank) (Fin r.matrixRank)).det
              (buildingIntegralCyclicBasisVector P r)) =
        (Matrix.stdBasis (BuildingLocalField P)
          (Fin r.matrixRank) (Fin r.matrixRank)).det
            (buildingCyclicBasisVector P r) := by
    simp only [Module.Basis.det_apply]
    have hmatrix :
        (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
            ((Matrix.stdBasis (BuildingIntegerRing P)
              (Fin r.matrixRank) (Fin r.matrixRank)).toMatrix
                (buildingIntegralCyclicBasisVector P r)) =
          (Matrix.stdBasis (BuildingLocalField P)
            (Fin r.matrixRank) (Fin r.matrixRank)).toMatrix
              (buildingCyclicBasisVector P r) := by
      apply Matrix.ext
      intro p q
      change SphericalHecke.integerEmbedding (BaseField P)
          (buildingIntegralCyclicBasisVector P r q p.1 p.2) =
        buildingCyclicBasisVector P r q p.1 p.2
      exact congrFun (congrFun
        (buildingIntegralCyclicBasisVector_toLocal P r q) p.1) p.2
    rw [RingHom.map_det, hmatrix]
  rw [← hmapped]
  exact IsUnit.map (SphericalHecke.integerEmbedding (BaseField P)) hint

noncomputable def buildingLocalCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (BuildingLocalField P)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)) :=
  Module.Basis.mk
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingLocalField P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingCyclicBasisVector_det_isUnit P r)).1
    ((Module.Basis.is_basis_iff_det
      (Matrix.stdBasis (BuildingLocalField P)
        (Fin r.matrixRank) (Fin r.matrixRank))).mpr
          (buildingCyclicBasisVector_det_isUnit P r)).2.ge

@[simp] theorem buildingLocalCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    buildingLocalCyclicBasis P r p = buildingCyclicBasisVector P r p := by
  simp [buildingLocalCyclicBasis]

/-- Local cyclic coordinates of the represented global cyclic algebra are
the images of its function-field cyclic coordinates. -/
theorem buildingLocalCyclicBasis_repr_cyclicAlgebra
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingLocalCyclicBasis P r).repr
        (cyclicAlgebraToBuilding P r x) p =
      functionFieldToBuildingLocalField P
        ((functionFieldCyclicBasis P r).repr x p) := by
  have hx' : cyclicAlgebraToBuilding P r x =
      ∑ q, functionFieldToBuildingLocalField P
          ((functionFieldCyclicBasis P r).repr x q) •
            buildingCyclicBasisVector P r q := by
    calc
      cyclicAlgebraToBuilding P r x =
          cyclicAlgebraToBuilding P r
            (∑ q, ((functionFieldCyclicBasis P r).repr x q) •
              functionFieldCyclicBasis P r q) := by
                rw [(functionFieldCyclicBasis P r).sum_repr]
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [cyclicAlgebraToBuilding_apply, map_smul]
        change functionFieldToBuildingLocalField P
            ((functionFieldCyclicBasis P r).repr x q) •
              cyclicAlgebraToBuildingLinear P r
                (functionFieldCyclicBasis P r q) = _
        rw [cyclicAlgebraToBuildingLinear_basis]
  have hrepr (q : Fin r.matrixRank × Fin r.matrixRank) :
      (buildingLocalCyclicBasis P r).repr
          (buildingCyclicBasisVector P r q) p = if q = p then 1 else 0 := by
    rw [← buildingLocalCyclicBasis_apply P r q]
    have h := congrArg
      (fun f : (Fin r.matrixRank × Fin r.matrixRank) →₀
          BuildingLocalField P => f p)
      ((buildingLocalCyclicBasis P r).repr_self q)
    simpa [Finsupp.single_apply] using h
  rw [hx']
  change (buildingLocalCyclicBasis P r).coord p
      (∑ q, functionFieldToBuildingLocalField P
        ((functionFieldCyclicBasis P r).repr x q) •
          buildingCyclicBasisVector P r q) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ q, functionFieldToBuildingLocalField P
      ((functionFieldCyclicBasis P r).repr x q) *
        (buildingLocalCyclicBasis P r).repr
          (buildingCyclicBasisVector P r q) p) = _
  simp_rw [hrepr]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

/-- Local cyclic coordinates of an included integral matrix are the images
of its integral cyclic coordinates. -/
theorem buildingLocalCyclicBasis_repr_integralMatrix
    (P : BasePrime) (r : Rank)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingIntegerRing P))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingLocalCyclicBasis P r).repr
        (M.map (SphericalHecke.integerEmbedding (BaseField P))) p =
      SphericalHecke.integerEmbedding (BaseField P)
        ((buildingIntegralCyclicBasis P r).repr M p) := by
  have hM' : M.map (SphericalHecke.integerEmbedding (BaseField P)) =
      ∑ q, SphericalHecke.integerEmbedding (BaseField P)
          ((buildingIntegralCyclicBasis P r).repr M q) •
            buildingCyclicBasisVector P r q := by
    calc
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
          (∑ q, ((buildingIntegralCyclicBasis P r).repr M q) •
            buildingIntegralCyclicBasis P r q).map
              (SphericalHecke.integerEmbedding (BaseField P)) := by
                rw [(buildingIntegralCyclicBasis P r).sum_repr]
      _ = _ := by
        change (SphericalHecke.integerEmbedding (BaseField P)).mapMatrix
            (∑ q, ((buildingIntegralCyclicBasis P r).repr M q) •
              buildingIntegralCyclicBasis P r q) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro q _
        change ((((buildingIntegralCyclicBasis P r).repr M q) •
          buildingIntegralCyclicBasis P r q).map
            (SphericalHecke.integerEmbedding (BaseField P))) = _
        rw [Matrix.map_smul'
          (SphericalHecke.integerEmbedding (BaseField P))
          ((buildingIntegralCyclicBasis P r).repr M q)
          (buildingIntegralCyclicBasis P r q)
          (map_mul (SphericalHecke.integerEmbedding (BaseField P))),
          buildingIntegralCyclicBasis_apply,
          buildingIntegralCyclicBasisVector_toLocal]
  have hrepr (q : Fin r.matrixRank × Fin r.matrixRank) :
      (buildingLocalCyclicBasis P r).repr
          (buildingCyclicBasisVector P r q) p = if q = p then 1 else 0 := by
    rw [← buildingLocalCyclicBasis_apply P r q]
    have h := congrArg
      (fun f : (Fin r.matrixRank × Fin r.matrixRank) →₀
          BuildingLocalField P => f p)
      ((buildingLocalCyclicBasis P r).repr_self q)
    simpa [Finsupp.single_apply] using h
  rw [hM']
  change (buildingLocalCyclicBasis P r).coord p
      (∑ q, SphericalHecke.integerEmbedding (BaseField P)
        ((buildingIntegralCyclicBasis P r).repr M q) •
          buildingCyclicBasisVector P r q) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ q, SphericalHecke.integerEmbedding (BaseField P)
      ((buildingIntegralCyclicBasis P r).repr M q) *
        (buildingLocalCyclicBasis P r).repr
          (buildingCyclicBasisVector P r q) p) = _
  simp_rw [hrepr]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

/-- Honest local matrix integrality forces every cyclic coordinate to lie
in the building integer ring. -/
theorem exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r x)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P
          ((functionFieldCyclicBasis P r).repr x p) := by
  obtain ⟨M, hM⟩ := hlocal
  refine ⟨(buildingIntegralCyclicBasis P r).repr M p, ?_⟩
  rw [← buildingLocalCyclicBasis_repr_integralMatrix P r M p, hM,
    buildingLocalCyclicBasis_repr_cyclicAlgebra]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
