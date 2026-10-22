import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Norm.GlobalNormOneBridge
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.SplittingFieldDescent
import QEC.Coding.HighDimensionalExpander.Algebra.MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots

/-!
# An intrinsic regular norm for the Cartwright--Steger cyclic algebra

Reduced norm must not depend on an arbitrarily selected matrix splitting.
The ordinary algebra norm, defined from left multiplication on the original
finite-dimensional cyclic algebra, supplies a common intrinsic invariant.
For a degree-`d` split central simple algebra it is the `d`-th power of the
reduced norm.  This module begins that comparison at the building place.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped Polynomial

/-- The determinant of left multiplication on the original cyclic algebra.
It is intrinsic, but has degree `d²`; reduced norm has degree `d`. -/
noncomputable def cyclicAlgebraRegularNorm
    (P : BasePrime) (r : Rank) :
    CyclicAlgebra P r →* FunctionField P :=
  Algebra.norm (FunctionField P)

theorem cyclicAlgebraRegularNorm_algebraMap
    (P : BasePrime) (r : Rank) (a : FunctionField P) :
    cyclicAlgebraRegularNorm P r
        (algebraMap (FunctionField P) (CyclicAlgebra P r) a) =
      a ^ (r.matrixRank * r.matrixRank) := by
  change Algebra.norm (FunctionField P)
      (algebraMap (FunctionField P) (CyclicAlgebra P r) a) = _
  rw [Algebra.norm_algebraMap, finrank_cyclicAlgebra]

theorem cyclicAlgebraRegularNorm_eq_zero_iff
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraRegularNorm P r x = 0 ↔ x = 0 := by
  letI : IsDomain (CyclicAlgebra P r) := cyclicAlgebraIsDomain P r
  exact Algebra.norm_eq_zero_iff_of_basis (functionFieldCyclicBasis P r)

/-- At the building splitting, the intrinsic regular norm is exactly the
`d`-th power of the construction's local reduced norm. -/
theorem buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
    (P : BasePrime) (r : Rank)
    (u : (BuildingCyclicScalarExtension P r)ˣ) :
    Algebra.norm (BuildingLocalField P)
        (u : BuildingCyclicScalarExtension P r) =
      ((buildingCyclicScalarExtensionReducedNorm P r u :
          (BuildingLocalField P)ˣ) : BuildingLocalField P) ^
        r.matrixRank := by
  calc
    Algebra.norm (BuildingLocalField P)
        (u : BuildingCyclicScalarExtension P r) =
      Algebra.norm (BuildingLocalField P)
        (buildingCyclicScalarExtensionEquivMatrix P r
          (u : BuildingCyclicScalarExtension P r)) :=
      (Algebra.norm_eq_of_algEquiv
        (buildingCyclicScalarExtensionEquivMatrix P r)
        (u : BuildingCyclicScalarExtension P r)).symm
    _ = Matrix.det
        (buildingCyclicScalarExtensionEquivMatrix P r
          (u : BuildingCyclicScalarExtension P r)) ^ r.matrixRank := by
      simpa using Matrix.algebraNorm_eq_det_pow_card
        (buildingCyclicScalarExtensionEquivMatrix P r
          (u : BuildingCyclicScalarExtension P r))
    _ = _ := by
      rfl

/-- For every global cyclic-algebra unit, its building-place reduced norm
has `d`-th power equal to the scalar extension of the intrinsic regular
norm.  This comparison is valid on all units and does not assume equality of
the reduced norms obtained from different splittings. -/
theorem map_cyclicAlgebraRegularNorm_eq_buildingReducedNorm_pow
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraBuildingReducedNorm P r u :
          (BuildingLocalField P)ˣ) : BuildingLocalField P) ^
        r.matrixRank := by
  calc
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      Algebra.norm (BuildingLocalField P)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := BuildingLocalField P)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) := by
      exact (Algebra.norm_tensorProduct_includeRight
        (functionFieldCyclicBasis P r) (u : CyclicAlgebra P r)).symm
    _ = Algebra.norm (BuildingLocalField P)
        ((cyclicAlgebraUnitToBuildingScalarExtension P r u :
          (BuildingCyclicScalarExtension P r)ˣ) :
            BuildingCyclicScalarExtension P r) := by
      rfl
    _ = _ :=
      buildingCyclicScalarExtension_regularNorm_eq_reducedNorm_pow
        P r (cyclicAlgebraUnitToBuildingScalarExtension P r u)

/-! ## The fixed global splitting as a genuine scalar extension -/

/-- Scalar extension of the cyclic algebra from the global function field
to the constant-field splitting extension. -/
abbrev SplittingCyclicScalarExtension (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (SplittingFunctionField P r)
    (CyclicAlgebra P r)

/-- The canonical scalar-extension map to the original global matrix
representation. -/
noncomputable def splittingCyclicScalarExtensionMap
    (P : BasePrime) (r : Rank) :
    SplittingCyclicScalarExtension P r →ₐ[SplittingFunctionField P r]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (SplittingFunctionField P r) <|
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))
    (CyclicAlgebra P r).val
    (fun a M => by
      change Commute
        (algebraMap (SplittingFunctionField P r)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) a)
        ((M : CyclicAlgebra P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))
      exact Algebra.commutes a _)

/-- The global cyclic basis after extension to the splitting field. -/
noncomputable def splittingCyclicScalarExtensionBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (SplittingFunctionField P r) (SplittingCyclicScalarExtension P r) :=
  Algebra.TensorProduct.basis (SplittingFunctionField P r)
    (functionFieldCyclicBasis P r)

@[simp] theorem splittingCyclicScalarExtensionMap_basis
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    splittingCyclicScalarExtensionMap P r
        (splittingCyclicScalarExtensionBasis P r p) =
      splittingCyclicBasis P r p := by
  rw [splittingCyclicScalarExtensionBasis,
    Algebra.TensorProduct.basis_apply,
    splittingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  simp only [functionFieldCyclicBasis_apply, splittingCyclicBasis_apply]
  simp

theorem splittingCyclicScalarExtensionMap_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (splittingCyclicScalarExtensionMap P r) := by
  let e := (splittingCyclicScalarExtensionBasis P r).equiv
    (splittingCyclicBasis P r) (Equiv.refl _)
  have heq : (splittingCyclicScalarExtensionMap P r).toLinearMap =
      e.toLinearMap := by
    apply (splittingCyclicScalarExtensionBasis P r).ext
    intro p
    change splittingCyclicScalarExtensionMap P r
        (splittingCyclicScalarExtensionBasis P r p) =
      e (splittingCyclicScalarExtensionBasis P r p)
    rw [splittingCyclicScalarExtensionMap_basis]
    exact (Module.Basis.equiv_apply
      (splittingCyclicScalarExtensionBasis P r) p
      (splittingCyclicBasis P r) (Equiv.refl _)).symm
  rw [show (splittingCyclicScalarExtensionMap P r : _ → _) = e by
    funext x
    exact DFunLike.congr_fun heq x]
  exact e.bijective

/-- The original global matrix representation is an actual splitting after
scalar extension, rather than merely a faithful embedding. -/
noncomputable def splittingCyclicScalarExtensionEquivMatrix
    (P : BasePrime) (r : Rank) :
    SplittingCyclicScalarExtension P r ≃ₐ[SplittingFunctionField P r]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  AlgEquiv.ofBijective (splittingCyclicScalarExtensionMap P r)
    (splittingCyclicScalarExtensionMap_bijective P r)

@[simp] theorem splittingCyclicScalarExtensionMap_includeRight
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    splittingCyclicScalarExtensionMap P r
        (Algebra.TensorProduct.includeRight x) =
      (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by
  rw [Algebra.TensorProduct.includeRight_apply,
    splittingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  simp

/-- In the global splitting, the regular norm of a scalar-extended global
unit is the `d`-th power of the fixed splitting reduced norm. -/
theorem splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Algebra.norm (SplittingFunctionField P r)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := SplittingFunctionField P r)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraSplitReducedNorm P r u :
          (SplittingFunctionField P r)ˣ) :
        SplittingFunctionField P r) ^ r.matrixRank := by
  calc
    Algebra.norm (SplittingFunctionField P r)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := SplittingFunctionField P r)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) =
      Algebra.norm (SplittingFunctionField P r)
        (splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) (u : CyclicAlgebra P r))) :=
      (Algebra.norm_eq_of_algEquiv
        (splittingCyclicScalarExtensionEquivMatrix P r) _).symm
    _ = Matrix.det
        (splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) (u : CyclicAlgebra P r))) ^
          r.matrixRank := by
      simpa using Matrix.algebraNorm_eq_det_pow_card
        (splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)))
    _ = _ := by
      rw [show splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) =
          ((u : CyclicAlgebra P r) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r)) by
        exact splittingCyclicScalarExtensionMap_includeRight P r u]
      rfl

/-- The global splitting reduced norm has `d`-th power equal to the scalar
extension of the intrinsic regular norm, for every global unit. -/
theorem map_cyclicAlgebraRegularNorm_eq_splitReducedNorm_pow
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraSplitReducedNorm P r u :
          (SplittingFunctionField P r)ˣ) :
        SplittingFunctionField P r) ^ r.matrixRank := by
  calc
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      Algebra.norm (SplittingFunctionField P r)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := SplittingFunctionField P r)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) := by
      exact (Algebra.norm_tensorProduct_includeRight
        (functionFieldCyclicBasis P r) (u : CyclicAlgebra P r)).symm
    _ = _ :=
      splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
        P r u

/-- The old determinant-valued split norm is exactly the scalar extension of
the descended base-function-field reduced norm. -/
theorem cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Units.map (functionFieldEmbedding P r)
        (cyclicAlgebraReducedNorm P r u) =
      cyclicAlgebraSplitReducedNorm P r u := by
  apply Units.ext
  change functionFieldEmbedding P r
      (cyclicAlgebraReducedNormValue P r (u : CyclicAlgebra P r)) =
    Matrix.det (u : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))
  exact functionFieldEmbedding_cyclicAlgebraReducedNormValue P r u

/-! ## Power comparison for arbitrary algebra elements -/

/-- The building determinant comparison holds for every element, including
nonunits. -/
theorem map_cyclicAlgebraRegularNorm_eq_buildingDet_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r x) =
      Matrix.det (cyclicAlgebraToBuilding P r x) ^ r.matrixRank := by
  calc
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraRegularNorm P r x) =
      Algebra.norm (BuildingLocalField P)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := BuildingLocalField P)
          (B := CyclicAlgebra P r) x) := by
      exact (Algebra.norm_tensorProduct_includeRight
        (functionFieldCyclicBasis P r) x).symm
    _ = Algebra.norm (BuildingLocalField P)
        (buildingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := BuildingLocalField P)
            (B := CyclicAlgebra P r) x)) :=
      (Algebra.norm_eq_of_algEquiv
        (buildingCyclicScalarExtensionEquivMatrix P r) _).symm
    _ = Matrix.det
        (buildingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := BuildingLocalField P)
            (B := CyclicAlgebra P r) x)) ^ r.matrixRank := by
      simpa using Matrix.algebraNorm_eq_det_pow_card
        (buildingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := BuildingLocalField P)
            (B := CyclicAlgebra P r) x))
    _ = _ := by
      rw [show buildingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := BuildingLocalField P)
            (B := CyclicAlgebra P r) x) =
          cyclicAlgebraToBuilding P r x by
        rw [Algebra.TensorProduct.includeRight_apply,
          buildingCyclicScalarExtensionEquivMatrix]
        change buildingCyclicScalarExtensionMap P r
            (1 ⊗ₜ[FunctionField P] x) = _
        rw [buildingCyclicScalarExtensionMap,
          Algebra.TensorProduct.lift_tmul]
        simp]

/-- The global splitting determinant comparison also holds for every
element. -/
theorem map_cyclicAlgebraRegularNorm_eq_splittingDet_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r x) =
      Matrix.det (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ^ r.matrixRank := by
  calc
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r x) =
      Algebra.norm (SplittingFunctionField P r)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := SplittingFunctionField P r)
          (B := CyclicAlgebra P r) x) := by
      exact (Algebra.norm_tensorProduct_includeRight
        (functionFieldCyclicBasis P r) x).symm
    _ = Algebra.norm (SplittingFunctionField P r)
        (splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) x)) :=
      (Algebra.norm_eq_of_algEquiv
        (splittingCyclicScalarExtensionEquivMatrix P r) _).symm
    _ = Matrix.det
        (splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) x)) ^ r.matrixRank := by
      simpa using Matrix.algebraNorm_eq_det_pow_card
        (splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) x))
    _ = _ := by
      rw [show splittingCyclicScalarExtensionEquivMatrix P r
          (Algebra.TensorProduct.includeRight
            (R := FunctionField P) (A := SplittingFunctionField P r)
            (B := CyclicAlgebra P r) x) =
          (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) by
        exact splittingCyclicScalarExtensionMap_includeRight P r x]

/-- The intrinsic regular norm is the `d`-th power of the descended reduced
norm, already over the base function field. -/
theorem cyclicAlgebraRegularNorm_eq_reducedNormValue_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraRegularNorm P r x =
      cyclicAlgebraReducedNormValue P r x ^ r.matrixRank := by
  apply (functionFieldEmbedding P r).injective
  rw [map_pow, functionFieldEmbedding_cyclicAlgebraReducedNormValue]
  exact map_cyclicAlgebraRegularNorm_eq_splittingDet_pow P r x

/-! ## Normalized reduced-norm polynomials -/

theorem splittingFunctionFieldFrobenius_affineLineDet
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (splittingFunctionFieldFrobenius P r).toRingHom
        (Matrix.affineLineDet
          (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) =
      Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by
  rw [Matrix.map_affineLineDet]
  change Matrix.affineLineDet
      ((splittingFunctionFieldFrobenius P r).toRingHom.mapMatrix
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))) = _
  rw [splittingFunctionFieldFrobenius_mapMatrix_eq_cyclicGenerator_conj]
  exact Matrix.affineLineDet_conj _ _ _ (cyclicGenerator_mul_inverse P r)

/-- Polynomial fixed-field descent, proved coefficientwise from the explicit
fixed-field theorem for the rational-function splitting field. -/
theorem exists_eq_polynomial_map_functionFieldEmbedding_of_frobenius_eq
    (P : BasePrime) (r : Rank)
    (p : (SplittingFunctionField P r)[X])
    (hp : Polynomial.map (splittingFunctionFieldFrobenius P r).toRingHom p = p) :
    ∃ q : (FunctionField P)[X],
      Polynomial.map (functionFieldEmbedding P r) q = p := by
  have hcoeff (i : ℕ) : splittingFunctionFieldFrobenius P r (p.coeff i) =
      p.coeff i := by
    have h := congrArg
      (fun q : (SplittingFunctionField P r)[X] => q.coeff i) hp
    simpa using h
  have hlifts : p ∈ Polynomial.lifts (functionFieldEmbedding P r) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact exists_eq_functionFieldEmbedding_of_frobenius_eq P r
      (p.coeff i) (hcoeff i)
  obtain ⟨q, hq, -⟩ := Polynomial.exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq⟩

/-- The reduced-norm polynomial on the affine line from `1` to `x`, descended
from the global splitting. -/
noncomputable def cyclicAlgebraReducedNormPolynomial
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (FunctionField P)[X] :=
  Classical.choose
    (exists_eq_polynomial_map_functionFieldEmbedding_of_frobenius_eq P r
      (Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)))
      (splittingFunctionFieldFrobenius_affineLineDet P r x))

theorem map_cyclicAlgebraReducedNormPolynomial
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (functionFieldEmbedding P r)
        (cyclicAlgebraReducedNormPolynomial P r x) =
      Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) :=
  Classical.choose_spec
    (exists_eq_polynomial_map_functionFieldEmbedding_of_frobenius_eq P r
      (Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)))
      (splittingFunctionFieldFrobenius_affineLineDet P r x))

theorem cyclicAlgebraReducedNormPolynomial_coeff_zero
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (cyclicAlgebraReducedNormPolynomial P r x).coeff 0 = 1 := by
  apply (functionFieldEmbedding P r).injective
  rw [← Polynomial.coeff_map, map_cyclicAlgebraReducedNormPolynomial,
    Matrix.affineLineDet_coeff_zero, map_one]

theorem cyclicAlgebraReducedNormPolynomial_eval_one
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.eval 1 (cyclicAlgebraReducedNormPolynomial P r x) =
      cyclicAlgebraReducedNormValue P r x := by
  apply (functionFieldEmbedding P r).injective
  calc
    functionFieldEmbedding P r
        (Polynomial.eval 1 (cyclicAlgebraReducedNormPolynomial P r x)) =
      Polynomial.eval (functionFieldEmbedding P r 1)
        (Polynomial.map (functionFieldEmbedding P r)
          (cyclicAlgebraReducedNormPolynomial P r x)) := by
        exact (Polynomial.eval_map_apply
          (p := cyclicAlgebraReducedNormPolynomial P r x)
          (functionFieldEmbedding P r) 1).symm
    _ = Polynomial.eval 1
        (Matrix.affineLineDet
          (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) := by
      rw [map_one, map_cyclicAlgebraReducedNormPolynomial]
    _ = _ := by
      rw [Matrix.affineLineDet_eval_one,
        functionFieldEmbedding_cyclicAlgebraReducedNormValue]

theorem cyclicAlgebraReducedNormPolynomial_eval
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) (a : FunctionField P) :
    Polynomial.eval a (cyclicAlgebraReducedNormPolynomial P r x) =
      cyclicAlgebraReducedNormValue P r (1 + a • (x - 1)) := by
  apply (functionFieldEmbedding P r).injective
  calc
    functionFieldEmbedding P r
        (Polynomial.eval a (cyclicAlgebraReducedNormPolynomial P r x)) =
      Polynomial.eval (functionFieldEmbedding P r a)
        (Polynomial.map (functionFieldEmbedding P r)
          (cyclicAlgebraReducedNormPolynomial P r x)) :=
      (Polynomial.eval_map_apply
        (p := cyclicAlgebraReducedNormPolynomial P r x)
        (functionFieldEmbedding P r) a).symm
    _ = Matrix.det ((1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) +
        functionFieldEmbedding P r a •
          ((x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) - 1)) := by
      rw [map_cyclicAlgebraReducedNormPolynomial,
        Matrix.eval_affineLineDet]
    _ = Matrix.det
        ((1 + a • (x - 1) : CyclicAlgebra P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
      rfl
    _ = _ := by
      rw [← functionFieldEmbedding_cyclicAlgebraReducedNormValue]

theorem map_cyclicAlgebraReducedNormPolynomial_pow_eq_buildingAffineLineDet_pow
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (algebraMap (FunctionField P) (BuildingLocalField P))
        (cyclicAlgebraReducedNormPolynomial P r x) ^ r.matrixRank =
      Matrix.affineLineDet (cyclicAlgebraToBuilding P r x) ^ r.matrixRank := by
  letI : Infinite (FunctionField P) :=
    Infinite.of_injective
      (algebraMap (PolynomialRing P) (FunctionField P))
      (IsFractionRing.injective _ _)
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective
    (functionFieldToBuildingLocalField P).injective).mono ?_
  intro z hz
  obtain ⟨a, rfl⟩ := hz
  change Polynomial.eval (algebraMap (FunctionField P) (BuildingLocalField P) a)
      (Polynomial.map (algebraMap (FunctionField P) (BuildingLocalField P))
        (cyclicAlgebraReducedNormPolynomial P r x) ^ r.matrixRank) = _
  rw [Polynomial.eval_pow, Polynomial.eval_pow,
    Polynomial.eval_map_apply,
    cyclicAlgebraReducedNormPolynomial_eval,
    Matrix.eval_affineLineDet]
  rw [← map_pow]
  rw [← cyclicAlgebraRegularNorm_eq_reducedNormValue_pow]
  rw [map_cyclicAlgebraRegularNorm_eq_buildingDet_pow]
  congr 2
  simp
  rw [cyclicAlgebraToBuildingLinear_map_one]
  rfl

/-- The matrix rank is invertible at the building place.  This is precisely
where the source restriction `q ≥ 5` excludes characteristics dividing
`d = 3` or `d = 4`. -/
theorem matrixRank_isUnit_buildingLocalField
    (P : BasePrime) (r : Rank) :
    IsUnit (r.matrixRank : BuildingLocalField P) := by
  rw [isUnit_iff_ne_zero]
  intro h
  cases r with
  | three =>
      change (3 : BuildingLocalField P) = 0 at h
      have hbase : (3 : BaseField P) = 0 := by
        apply (algebraMap (BaseField P) (BuildingLocalField P)).injective
        simpa only [map_ofNat, map_zero] using h
      have hdiv : P.q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 P.q).mp hbase
      have hle : P.q ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
      have := P.five_le
      omega
  | four =>
      change (4 : BuildingLocalField P) = 0 at h
      have hbase : (4 : BaseField P) = 0 := by
        apply (algebraMap (BaseField P) (BuildingLocalField P)).injective
        simpa only [map_ofNat, map_zero] using h
      have hdiv : P.q ∣ 4 := (ZMod.natCast_eq_zero_iff 4 P.q).mp hbase
      have hle : P.q ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
      have := P.five_le
      omega

/-- The descended normalized reduced-norm polynomial agrees exactly with the
building-place determinant polynomial, not merely after taking a power. -/
theorem map_cyclicAlgebraReducedNormPolynomial_eq_buildingAffineLineDet
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (algebraMap (FunctionField P) (BuildingLocalField P))
        (cyclicAlgebraReducedNormPolynomial P r x) =
      Matrix.affineLineDet (cyclicAlgebraToBuilding P r x) := by
  apply Polynomial.eq_of_pow_eq_pow_of_coeff_zero_eq_one
    (matrixRank_isUnit_buildingLocalField P r)
  · rw [Polynomial.coeff_map,
      cyclicAlgebraReducedNormPolynomial_coeff_zero, map_one]
  · exact Matrix.affineLineDet_coeff_zero _
  · exact
      map_cyclicAlgebraReducedNormPolynomial_pow_eq_buildingAffineLineDet_pow
        P r x

/-- Exact compatibility of the construction-owned reduced norm with the
distinguished building-place splitting. -/
theorem map_cyclicAlgebraReducedNormValue_eq_buildingDet
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraReducedNormValue P r x) =
      Matrix.det (cyclicAlgebraToBuilding P r x) := by
  calc
    algebraMap (FunctionField P) (BuildingLocalField P)
        (cyclicAlgebraReducedNormValue P r x) =
      algebraMap (FunctionField P) (BuildingLocalField P)
        (Polynomial.eval 1 (cyclicAlgebraReducedNormPolynomial P r x)) := by
      rw [cyclicAlgebraReducedNormPolynomial_eval_one]
    _ = Polynomial.eval 1
        (Polynomial.map
          (algebraMap (FunctionField P) (BuildingLocalField P))
          (cyclicAlgebraReducedNormPolynomial P r x)) := by
      symm
      simpa using Polynomial.eval_map_apply
        (p := cyclicAlgebraReducedNormPolynomial P r x)
        (algebraMap (FunctionField P) (BuildingLocalField P)) 1
    _ = Polynomial.eval 1
        (Matrix.affineLineDet (cyclicAlgebraToBuilding P r x)) := by
      rw [map_cyclicAlgebraReducedNormPolynomial_eq_buildingAffineLineDet]
    _ = _ := Matrix.affineLineDet_eval_one _

/-- On units, the base-field reduced norm becomes the existing concrete
building reduced norm under scalar extension. -/
theorem cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Units.map (functionFieldToBuildingLocalField P)
        (cyclicAlgebraReducedNorm P r u) =
      cyclicAlgebraBuildingReducedNorm P r u := by
  apply Units.ext
  dsimp [cyclicAlgebraReducedNorm, cyclicAlgebraReducedNormMonoidHom,
    cyclicAlgebraBuildingReducedNorm,
    buildingCyclicScalarExtensionReducedNorm,
    cyclicAlgebraUnitToBuildingScalarExtension,
    buildingCyclicScalarExtensionUnitEquivGL]
  change functionFieldToBuildingLocalField P
      (cyclicAlgebraReducedNormValue P r (u : CyclicAlgebra P r)) =
    Matrix.det (buildingCyclicScalarExtensionEquivMatrix P r
      (1 ⊗ₜ[FunctionField P] (u : CyclicAlgebra P r)))
  rw [show buildingCyclicScalarExtensionEquivMatrix P r
      (1 ⊗ₜ[FunctionField P] (u : CyclicAlgebra P r)) =
      cyclicAlgebraToBuilding P r (u : CyclicAlgebra P r) by
    rw [buildingCyclicScalarExtensionEquivMatrix]
    change buildingCyclicScalarExtensionMap P r
        (1 ⊗ₜ[FunctionField P] (u : CyclicAlgebra P r)) = _
    rw [buildingCyclicScalarExtensionMap,
      Algebra.TensorProduct.lift_tmul]
    simp]
  change algebraMap (FunctionField P) (BuildingLocalField P)
      (cyclicAlgebraReducedNormValue P r (u : CyclicAlgebra P r)) =
    Matrix.det (cyclicAlgebraToBuilding P r (u : CyclicAlgebra P r))
  exact map_cyclicAlgebraReducedNormValue_eq_buildingDet P r u

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
