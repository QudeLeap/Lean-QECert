import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.SimpleTransitivity
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Projective.SpecialLinear
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.Reduction
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The norm-one endpoint of Cartwright--Steger strong approximation

This module records the source and target subgroups in the form needed by
the strong-approximation argument in LSV.  In particular, the source
norm-one group is the kernel of the determinant of the *actual arithmetic
order-unit representation*.  It is deliberately not replaced by an
unrelated matrix special-linear group over the coefficient ring.

The final group-theoretic lemma below isolates the exact remaining input:
once reduction of the construction-owned norm-one inner form contains the
finite `PSL`, normality of the Cartwright--Steger image and its explicit
nonidentity color-zero element force the whole `PSL` into that image.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups SphericalHecke.LocalTopology Valued

/-! ## The noncompact building-place factor

The strong-approximation input used by LSV is the norm-one group of the
cyclic algebra, not an unrelated split special-linear group.  At the
distinguished building place the cyclic algebra has already been split by
the concrete representation in `CartwrightStegerBuildingAction`.  The
following diagonal family records the required unbounded norm-one local
points in those same split coordinates.
-/

/-- The two coordinates used for the explicit building-place escape ray.
Both exist because the construction ranks are three and four. -/
private def buildingEscapeIndexZero (r : Rank) : Fin r.matrixRank :=
  ⟨0, lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)⟩

private def buildingEscapeIndexOne (r : Rank) : Fin r.matrixRank :=
  ⟨1, Rank.two_le_matrixRank r⟩

/-- The explicit determinant-one local point escaping along the first
apartment of the building. -/
private noncomputable def buildingNormOneEscapeThree
    (P : BasePrime) (n : Nat) :
    Matrix.SpecialLinearGroup (Fin 3) (BuildingLocalField P) := by
  let π := SphericalHecke.uniformizerUnit (BaseField P) ^ n
  refine ⟨Matrix.diagonal ![(π : BuildingLocalField P),
    (π⁻¹ : (BuildingLocalField P)ˣ), 1], ?_⟩
  rw [Matrix.det_diagonal]
  simp_rw [Fin.prod_univ_three]
  simp

private noncomputable def buildingNormOneEscapeFour
    (P : BasePrime) (n : Nat) :
    Matrix.SpecialLinearGroup (Fin 4) (BuildingLocalField P) := by
  let π := SphericalHecke.uniformizerUnit (BaseField P) ^ n
  refine ⟨Matrix.diagonal ![(π : BuildingLocalField P),
    (π⁻¹ : (BuildingLocalField P)ˣ), 1, 1], ?_⟩
  rw [Matrix.det_diagonal]
  simp_rw [Fin.prod_univ_four]
  simp

noncomputable def buildingNormOneEscape
    (P : BasePrime) (r : Rank) (n : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  match r with
  | .three => buildingNormOneEscapeThree P n
  | .four => buildingNormOneEscapeFour P n

@[simp] theorem buildingNormOneEscape_apply_zero_zero
    (P : BasePrime) (r : Rank) (n : Nat) :
    ((buildingNormOneEscape P r n :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexZero r) (buildingEscapeIndexZero r) =
      (SphericalHecke.uniformizerUnit (BaseField P) ^ n :
        BuildingLocalField P) := by
  cases r <;>
    simp [buildingNormOneEscape, buildingNormOneEscapeThree,
      buildingNormOneEscapeFour, buildingEscapeIndexZero,
      SphericalHecke.coe_uniformizerUnit]

@[simp] theorem buildingNormOneEscape_apply_one_one
    (P : BasePrime) (r : Rank) (n : Nat) :
    ((buildingNormOneEscape P r n :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexOne r) (buildingEscapeIndexOne r) =
      ((SphericalHecke.uniformizerUnit (BaseField P) ^ n)⁻¹ :
        (BuildingLocalField P)ˣ) := by
  have hne : buildingEscapeIndexOne r ≠ buildingEscapeIndexZero r := by
    intro h
    exact one_ne_zero (congrArg Fin.val h)
  cases r <;>
    simp [buildingNormOneEscape, buildingNormOneEscapeThree,
      buildingNormOneEscapeFour, buildingEscapeIndexOne,
      SphericalHecke.coe_uniformizerUnit]

/-- The escape ray has precisely increasing uniformizer order in its first
diagonal coordinate. -/
theorem buildingNormOneEscape_zero_orderTop
    (P : BasePrime) (r : Rank) (n : Nat) :
    (((buildingNormOneEscape P r n :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexZero r) (buildingEscapeIndexZero r)).orderTop =
      (n : WithTop Int) := by
  rw [buildingNormOneEscape_apply_zero_zero]
  exact SphericalHecke.orderTop_uniformizerUnit_pow n

/-- Distinct distances along the apartment give distinct norm-one local
points.  This is the algebraic unboundedness witness used to discharge the
building-place noncompactness premise of specialized strong approximation. -/
theorem buildingNormOneEscape_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingNormOneEscape P r) := by
  intro m n hmn
  have hentry := congrArg (fun s :
      Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) ↦
    (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
        (buildingEscapeIndexZero r) (buildingEscapeIndexZero r)).orderTop) hmn
  have hcoe : (m : WithTop Int) = (n : WithTop Int) := by
    simpa only [buildingNormOneEscape_zero_orderTop] using hentry
  have hint : (m : Int) = (n : Int) := WithTop.coe_eq_coe.mp hcoe
  exact_mod_cast hint

/-- The inverse uniformizer genuinely expands in the rank-one norm attached
to the already selected `X`-adic topology. -/
theorem one_lt_norm_buildingUniformizerUnit_inv (P : BasePrime) :
    1 < ‖(((SphericalHecke.uniformizerUnit (BaseField P))⁻¹ :
      (BuildingLocalField P)ˣ) : BuildingLocalField P)‖ := by
  rw [Valued.toNormedField.one_lt_norm_iff]
  simp [SphericalHecke.uniformizerUnit,
    LaurentSeries.valuation_single_zpow]
  rw [show (1 : WithZero (Multiplicative Int)) =
    (1 : Multiplicative Int) by rfl, WithZero.exp]
  exact WithZero.coe_lt_coe.mpr (show (0 : Int) < 1 by norm_num)

/-- The split norm-one factor at the distinguished building place is not
compact.  This discharges the noncompact-place premise in the LSV strong
approximation argument with the concrete local representation: a compact
group would have bounded second-coordinate image, whereas the explicit
norm-one apartment ray has second coordinate `π⁻ⁿ`. -/
theorem buildingNormOneLocal_not_compactSpace
    (P : BasePrime) (r : Rank) :
    ¬ CompactSpace
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) := by
  intro hcompact
  letI : CompactSpace
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
    hcompact
  let coordinate :
      Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) →
        BuildingLocalField P :=
    fun s ↦ ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) (buildingEscapeIndexOne r)
        (buildingEscapeIndexOne r))
  have hcoordinate : Continuous coordinate :=
    (continuous_apply (buildingEscapeIndexOne r)).comp
      ((continuous_apply (buildingEscapeIndexOne r)).comp continuous_subtype_val)
  have hbounded : Bornology.IsBounded
      (coordinate '' (Set.univ : Set
        (Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)))) :=
    (isCompact_univ.image hcoordinate).isBounded
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  let a : BuildingLocalField P :=
    (((SphericalHecke.uniformizerUnit (BaseField P))⁻¹ :
      (BuildingLocalField P)ˣ) : BuildingLocalField P)
  have ha : 1 < ‖a‖ := one_lt_norm_buildingUniformizerUnit_inv P
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop C |>.exists
  have hmem : a ^ n ∈ coordinate '' (Set.univ : Set
      (Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (BuildingLocalField P))) := by
    refine ⟨buildingNormOneEscape P r n, Set.mem_univ _, ?_⟩
    change
      ((buildingNormOneEscape P r n :
          Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
          (buildingEscapeIndexOne r) (buildingEscapeIndexOne r) = a ^ n
    rw [buildingNormOneEscape_apply_one_one]
    simp [a]
  have hle := hC (a ^ n) hmem
  rw [norm_pow] at hle
  exact (not_le_of_gt hn) hle

/-! ### The actual cyclic algebra splits at the noncompact place -/

/-- Scalar extension of the construction-owned global cyclic algebra from
`F_q(y)` to the distinguished building local field. -/
abbrev BuildingCyclicScalarExtension (P : BasePrime) (r : Rank) :=
  TensorProduct (FunctionField P) (BuildingLocalField P) (CyclicAlgebra P r)

/-- The scalar-extended cyclic algebra maps to the concrete building-place
matrix representation.  The left tensor factor acts by scalar matrices and
the right factor uses the already checked cyclic multiplication law. -/
noncomputable def buildingCyclicScalarExtensionMap
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtension P r →ₐ[BuildingLocalField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (BuildingLocalField P) <|
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P))
    (cyclicAlgebraToBuilding P r)
    (fun a M ↦ by
      change Commute
        (algebraMap (BuildingLocalField P)
          (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) a)
        (cyclicAlgebraToBuilding P r M)
      exact Algebra.commutes a _)

/-- The global cyclic basis after extension to the building local field. -/
noncomputable def buildingCyclicScalarExtensionBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (BuildingLocalField P) (BuildingCyclicScalarExtension P r) :=
  Algebra.TensorProduct.basis (BuildingLocalField P)
    (functionFieldCyclicBasis P r)

@[simp] theorem buildingCyclicScalarExtensionMap_basis
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    buildingCyclicScalarExtensionMap P r
        (buildingCyclicScalarExtensionBasis P r p) =
      buildingLocalCyclicBasis P r p := by
  rw [buildingCyclicScalarExtensionBasis,
    Algebra.TensorProduct.basis_apply]
  rw [buildingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  rw [cyclicAlgebraToBuilding_apply,
    cyclicAlgebraToBuildingLinear_basis,
    buildingLocalCyclicBasis_apply]
  simp

/-- The scalar-extension representation is bijective because it sends the
actual extended global cyclic basis to the proved basis of the full local
matrix algebra. -/
theorem buildingCyclicScalarExtensionMap_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingCyclicScalarExtensionMap P r) := by
  let e := (buildingCyclicScalarExtensionBasis P r).equiv
    (buildingLocalCyclicBasis P r) (Equiv.refl _)
  have heq : (buildingCyclicScalarExtensionMap P r).toLinearMap =
      e.toLinearMap := by
    apply (buildingCyclicScalarExtensionBasis P r).ext
    intro p
    change buildingCyclicScalarExtensionMap P r
        (buildingCyclicScalarExtensionBasis P r p) =
      e (buildingCyclicScalarExtensionBasis P r p)
    rw [buildingCyclicScalarExtensionMap_basis]
    exact (Module.Basis.equiv_apply
      (buildingCyclicScalarExtensionBasis P r) p
      (buildingLocalCyclicBasis P r) (Equiv.refl _)).symm
  rw [show (buildingCyclicScalarExtensionMap P r : _ → _) = e by
    funext x
    exact DFunLike.congr_fun heq x]
  exact e.bijective

/-- Explicit splitting of the genuine Cartwright--Steger cyclic algebra at
the building place.  In particular the noncompact group proved above is the
local norm-one group of the construction's inner form, rather than an
auxiliary `SL` selected without descent data. -/
noncomputable def buildingCyclicScalarExtensionEquivMatrix
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtension P r ≃ₐ[BuildingLocalField P]
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
  AlgEquiv.ofBijective (buildingCyclicScalarExtensionMap P r)
    (buildingCyclicScalarExtensionMap_bijective P r)

/-- Faithfully-flat scalar descent in the one form needed below: if an
element of an algebra becomes a scalar after extending a field, then it was
already a scalar over the original field. -/
private theorem eq_algebraMap_of_one_tmul_eq_tmul_one
    (K L A : Type*) [Field K] [Field L] [Ring A]
    [Algebra K L] [Algebra K A] [Module.FaithfullyFlat K L]
    (x : A) (a : L)
    (h : (1 : L) ⊗ₜ[K] x = a ⊗ₜ[K] (1 : A)) :
    ∃ k : K, x = algebraMap K A k := by
  let S : Submodule K A := K ∙ (1 : A)
  have hzero : (1 : L) ⊗ₜ[K] S.mkQ x = 0 := by
    have hm := congrArg
      (TensorProduct.map (LinearMap.id (R := K) (M := L)) S.mkQ) h
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul] at hm
    simp only [LinearMap.id_coe, id_eq] at hm
    rw [hm]
    have hone : S.mkQ (1 : A) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero S).mpr
      exact Submodule.mem_span_singleton_self (1 : A)
    rw [hone, TensorProduct.tmul_zero]
  have hqx : S.mkQ x = 0 :=
    (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := K)
      (M := A ⧸ S) (A := L) (S.mkQ x)).mp hzero
  have hx : x ∈ S := by
    rw [← S.ker_mkQ, LinearMap.mem_ker]
    exact hqx
  change x ∈ K ∙ (1 : A) at hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by simpa [Algebra.smul_def] using hk.symm⟩

/-- The explicit cyclic algebra is central over `F_q(y)`.  The proof does
not assume the usual cyclic-algebra center theorem: a central element is
sent into the center of the proved building-place matrix splitting, hence
becomes a local scalar, and faithful-flat descent brings that scalar back to
the global function field. -/
theorem cyclicAlgebraIsCentral
    (P : BasePrime) (r : Rank) :
    Algebra.IsCentral (FunctionField P) (CyclicAlgebra P r) := by
  constructor
  intro x hx
  have ht : Algebra.TensorProduct.includeRight
      (R := FunctionField P) (A := BuildingLocalField P)
        (B := CyclicAlgebra P r) x ∈
      Set.center (BuildingCyclicScalarExtension P r) := by
    refine
      { comm := ?_
        left_assoc := fun _ _ => (mul_assoc _ _ _).symm
        right_assoc := fun _ _ => mul_assoc _ _ _ }
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | add y z hy hz => exact hy.add_right hz
    | tmul a b =>
        change ((1 : BuildingLocalField P) ⊗ₜ[FunctionField P] x) *
            (a ⊗ₜ[FunctionField P] b) =
          (a ⊗ₜ[FunctionField P] b) *
            ((1 : BuildingLocalField P) ⊗ₜ[FunctionField P] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
          (Subalgebra.mem_center_iff.mp hx b).symm]
  let e := buildingCyclicScalarExtensionEquivMatrix P r
  have hm : e (Algebra.TensorProduct.includeRight
      (R := FunctionField P) (A := BuildingLocalField P)
        (B := CyclicAlgebra P r) x) ∈
      Subalgebra.center (BuildingLocalField P)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := by
    change e (Algebra.TensorProduct.includeRight x) ∈
      Set.center (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingLocalField P))
    exact (MulEquivClass.apply_mem_center_iff e).mpr ht
  obtain ⟨a, ha⟩ :=
    (Algebra.IsCentral.mem_center_iff (BuildingLocalField P)).mp hm
  have heq : (1 : BuildingLocalField P) ⊗ₜ[FunctionField P]
        (x : CyclicAlgebra P r) =
      a ⊗ₜ[FunctionField P] (1 : CyclicAlgebra P r) := by
    apply e.injective
    rw [← Algebra.TensorProduct.includeRight_apply]
    rw [ha]
    simp [Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨k, hk⟩ := eq_algebraMap_of_one_tmul_eq_tmul_one
    (FunctionField P) (BuildingLocalField P) (CyclicAlgebra P r) x a heq
  rw [Algebra.mem_bot]
  exact ⟨k, hk.symm⟩

/-- Units of the global cyclic division algebra in its fixed splitting-field
matrix representation. -/
noncomputable def cyclicAlgebraUnitToGlobalGL
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r) :=
  Units.map (CyclicAlgebra P r).val.toRingHom

/-- Reduced norm on global cyclic-algebra units, computed in the explicit
splitting representation.  Its kernel is independent of the chosen splitting
and is the global simply-connected inner form used by LSV. -/
noncomputable def cyclicAlgebraSplitReducedNorm
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (SplittingFunctionField P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp (cyclicAlgebraUnitToGlobalGL P r)

/-- Global norm-one points of the construction-owned cyclic division
algebra. -/
noncomputable def CyclicAlgebraSplitNormOne
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  (cyclicAlgebraSplitReducedNorm P r).ker

/-- Scalar extension of global cyclic-algebra units to the distinguished
building local field. -/
noncomputable def cyclicAlgebraUnitToBuildingScalarExtension
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (BuildingCyclicScalarExtension P r)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight
    (R := FunctionField P) (A := BuildingLocalField P)
      (B := CyclicAlgebra P r)).toRingHom

/-- Units of the genuinely scalar-extended cyclic algebra are the concrete
building-place general-linear group under the proved splitting. -/
noncomputable def buildingCyclicScalarExtensionUnitEquivGL
    (P : BasePrime) (r : Rank) :
    (BuildingCyclicScalarExtension P r)ˣ ≃*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  let e : BuildingCyclicScalarExtension P r ≃*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P) :=
    (buildingCyclicScalarExtensionEquivMatrix P r).toMulEquiv
  Units.mapEquiv e

/-- Local reduced norm transported through the explicit matrix splitting. -/
noncomputable def buildingCyclicScalarExtensionReducedNorm
    (P : BasePrime) (r : Rank) :
    (BuildingCyclicScalarExtension P r)ˣ →* (BuildingLocalField P)ˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (buildingCyclicScalarExtensionUnitEquivGL P r).toMonoidHom

/-- The abstract scalar-extension map and the original concrete
building-place representation agree on every global cyclic-algebra unit. -/
theorem buildingScalarExtensionUnitEquivGL_global_compatibility
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    buildingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToBuildingScalarExtension P r u) =
      cyclicUnitToBuildingGL P r u := by
  apply Units.ext
  change buildingCyclicScalarExtensionMap P r
      (Algebra.TensorProduct.includeRight (u : CyclicAlgebra P r)) =
    cyclicAlgebraToBuilding P r (u : CyclicAlgebra P r)
  rw [Algebra.TensorProduct.includeRight_apply,
    buildingCyclicScalarExtensionMap,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem cyclicUnitToBuildingGL_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicUnitToBuildingGL P r) := by
  intro u v huv
  apply Units.ext
  apply cyclicAlgebraToBuilding_injective P r
  exact congrArg Units.val huv

theorem cyclicAlgebraUnitToBuildingScalarExtension_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraUnitToBuildingScalarExtension P r) := by
  intro u v huv
  apply cyclicUnitToBuildingGL_injective P r
  rw [← buildingScalarExtensionUnitEquivGL_global_compatibility,
    ← buildingScalarExtensionUnitEquivGL_global_compatibility, huv]

/-- The building-place reduced norm of a global cyclic-algebra unit, defined
by genuine scalar extension to the local algebra. -/
noncomputable def cyclicAlgebraBuildingReducedNorm
    (P : BasePrime) (r : Rank) :
    (CyclicAlgebra P r)ˣ →* (BuildingLocalField P)ˣ :=
  (buildingCyclicScalarExtensionReducedNorm P r).comp
    (cyclicAlgebraUnitToBuildingScalarExtension P r)

/-- Global cyclic-algebra units whose genuine building-place base change has
reduced norm one. -/
noncomputable def CyclicAlgebraBuildingNormOne
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  (cyclicAlgebraBuildingReducedNorm P r).ker

/-- The genuine local norm-one group of the scalar-extended cyclic algebra. -/
noncomputable def BuildingCyclicScalarExtensionNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (BuildingCyclicScalarExtension P r)ˣ :=
  (buildingCyclicScalarExtensionReducedNorm P r).ker

/-- Base change of a global building-norm-one point to the genuine local
norm-one group. -/
noncomputable def cyclicAlgebraBuildingNormOneToLocal
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraBuildingNormOne P r →*
      BuildingCyclicScalarExtensionNormOne P r where
  toFun u := ⟨cyclicAlgebraUnitToBuildingScalarExtension P r u, u.property⟩
  map_one' := Subtype.ext
    (map_one (cyclicAlgebraUnitToBuildingScalarExtension P r))
  map_mul' u v := Subtype.ext
    (map_mul (cyclicAlgebraUnitToBuildingScalarExtension P r)
      (u : (CyclicAlgebra P r)ˣ) (v : (CyclicAlgebra P r)ˣ))

theorem cyclicAlgebraBuildingNormOneToLocal_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (cyclicAlgebraBuildingNormOneToLocal P r) := by
  intro u v huv
  apply Subtype.ext
  apply cyclicAlgebraUnitToBuildingScalarExtension_injective P r
  exact congrArg Subtype.val huv

/-- The ratio of two explicit Cartwright--Steger cyclic units, bundled in
the global group detected as norm one at the building place. -/
noncomputable def cyclicAlgebraBuildingNormOneGeneratorRatio
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    CyclicAlgebraBuildingNormOne P r := by
  let gu := cartwrightStegerGeneratorCyclicUnit P r u
  let gv := cartwrightStegerGeneratorCyclicUnit P r v
  refine ⟨gu * gv⁻¹, ?_⟩
  change buildingCyclicScalarExtensionReducedNorm P r
      (cyclicAlgebraUnitToBuildingScalarExtension P r (gu * gv⁻¹)) = 1
  rw [buildingCyclicScalarExtensionReducedNorm]
  change Matrix.GeneralLinearGroup.det
      (buildingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToBuildingScalarExtension P r (gu * gv⁻¹))) = 1
  rw [buildingScalarExtensionUnitEquivGL_global_compatibility]
  rw [map_mul, map_inv,
    cartwrightStegerGeneratorCyclicUnit_to_buildingGL,
    cartwrightStegerGeneratorCyclicUnit_to_buildingGL,
    map_mul, map_inv,
    buildingCartwrightStegerGeneratorGL_det,
    buildingCartwrightStegerGeneratorGL_det]
  simp

/-- The global splitting representation sends each genuine cyclic-algebra
Cartwright--Steger unit to the original global generator matrix. -/
@[simp] theorem cyclicAlgebraUnitToGlobalGL_generator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicAlgebraUnitToGlobalGL P r
        (cartwrightStegerGeneratorCyclicUnit P r u) =
      cartwrightStegerGenerator P r u := by
  apply Units.ext
  change
    ((cartwrightStegerGeneratorCyclicUnit P r u : CyclicAlgebra P r) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) = _
  rw [cartwrightStegerGeneratorCyclicUnit_coe,
    cartwrightStegerGeneratorCyclicElement_coe]

/-- The explicit generator ratio used at the building place also has
reduced norm one in the independent global splitting representation.  Thus
the nonidentity witness belongs simultaneously to both concrete kernels;
no equality of reduced norms from different splittings is assumed here. -/
theorem cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    (cyclicAlgebraBuildingNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) ∈ CyclicAlgebraSplitNormOne P r := by
  change cyclicAlgebraSplitReducedNorm P r
      (cartwrightStegerGeneratorCyclicUnit P r u *
        (cartwrightStegerGeneratorCyclicUnit P r v)⁻¹) = 1
  rw [cyclicAlgebraSplitReducedNorm, map_mul, map_inv]
  change Matrix.GeneralLinearGroup.det
          (cyclicAlgebraUnitToGlobalGL P r
            (cartwrightStegerGeneratorCyclicUnit P r u)) *
        (Matrix.GeneralLinearGroup.det
          (cyclicAlgebraUnitToGlobalGL P r
            (cartwrightStegerGeneratorCyclicUnit P r v)))⁻¹ = 1
  rw [cyclicAlgebraUnitToGlobalGL_generator,
    cyclicAlgebraUnitToGlobalGL_generator]
  simp [cartwrightStegerGenerator]

/-- Under the checked local splitting, the genuine local reduced-norm-one
group is exactly the special-linear group used by the escape ray. -/
noncomputable def buildingCyclicScalarExtensionNormOneEquivSL
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtensionNormOne P r ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) where
  toFun u := ⟨((buildingCyclicScalarExtensionUnitEquivGL P r u :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BuildingLocalField P)),
    congrArg Units.val u.property⟩
  invFun s :=
    ⟨(buildingCyclicScalarExtensionUnitEquivGL P r).symm
        (Matrix.SpecialLinearGroup.toGL s), by
      change buildingCyclicScalarExtensionReducedNorm P r
        ((buildingCyclicScalarExtensionUnitEquivGL P r).symm
          (Matrix.SpecialLinearGroup.toGL s)) = 1
      rw [buildingCyclicScalarExtensionReducedNorm]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    apply (buildingCyclicScalarExtensionUnitEquivGL P r).injective
    apply Units.ext
    simp
    rfl
  right_inv s := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply Units.ext
    simp
    rfl

theorem cyclicAlgebraBuildingNormOneGeneratorRatio_toLocal
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    buildingCyclicScalarExtensionNormOneEquivSL P r
        (cyclicAlgebraBuildingNormOneToLocal P r
          (cyclicAlgebraBuildingNormOneGeneratorRatio P r u v)) =
      ⟨((buildingCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (buildingCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)), by
        have hdet : Matrix.GeneralLinearGroup.det
            (buildingCartwrightStegerGeneratorGL P r
                (constantClassRepresentative P r u) *
              (buildingCartwrightStegerGeneratorGL P r
                (constantClassRepresentative P r v))⁻¹) = 1 := by
          rw [map_mul, map_inv,
            buildingCartwrightStegerGeneratorGL_det,
            buildingCartwrightStegerGeneratorGL_det]
          simp
        simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
          congrArg Units.val hdet⟩ := by
  apply Subtype.ext
  calc
    _ = ((buildingCyclicScalarExtensionUnitEquivGL P r
        (cyclicAlgebraUnitToBuildingScalarExtension P r
          (cartwrightStegerGeneratorCyclicUnit P r u *
            (cartwrightStegerGeneratorCyclicUnit P r v)⁻¹)) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) := rfl
    _ = ((cyclicUnitToBuildingGL P r
        (cartwrightStegerGeneratorCyclicUnit P r u *
          (cartwrightStegerGeneratorCyclicUnit P r v)⁻¹) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P)) := congrArg Units.val
      (buildingScalarExtensionUnitEquivGL_global_compatibility P r _)
    _ = _ := by
      rw [map_mul, map_inv,
        cartwrightStegerGeneratorCyclicUnit_to_buildingGL,
        cartwrightStegerGeneratorCyclicUnit_to_buildingGL]

/-- The canonical building-place topology on the genuine local norm-one
group, pulled back along the explicit splitting equivalence. -/
noncomputable instance buildingCyclicScalarExtensionNormOneTopologicalSpace
    (P : BasePrime) (r : Rank) :
    TopologicalSpace (BuildingCyclicScalarExtensionNormOne P r) :=
  TopologicalSpace.induced
    (buildingCyclicScalarExtensionNormOneEquivSL P r)
    inferInstance

/-- The algebraic norm-one equivalence is a homeomorphism for the canonical
pulled-back building-place topology. -/
noncomputable def buildingCyclicScalarExtensionNormOneHomeomorphSL
    (P : BasePrime) (r : Rank) :
    BuildingCyclicScalarExtensionNormOne P r ≃ₜ
      Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (buildingCyclicScalarExtensionNormOneEquivSL P r).toEquiv
    |>.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual local norm-one group of the Cartwright--Steger cyclic algebra
is noncompact at the building place.  This is the exact structural premise
used by strong approximation, now stated on the genuine scalar extension. -/
theorem buildingCyclicScalarExtensionNormOne_not_compactSpace
    (P : BasePrime) (r : Rank) :
    ¬ CompactSpace (BuildingCyclicScalarExtensionNormOne P r) := by
  intro hcompact
  letI : CompactSpace (BuildingCyclicScalarExtensionNormOne P r) := hcompact
  letI : CompactSpace
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
    (buildingCyclicScalarExtensionNormOneHomeomorphSL P r).compactSpace
  exact buildingNormOneLocal_not_compactSpace P r inferInstance

/-- Reduced norm on units of the actual Cartwright--Steger arithmetic order.
In the fixed splitting representation, reduced norm is determinant. -/
noncomputable def cartwrightStegerOrderReducedNorm
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      (SplittingFunctionField P r)ˣ :=
  Matrix.GeneralLinearGroup.det.comp (orderUnitToGlobalGL P r)

/-- Norm-one integral points of the construction-owned inner form. -/
noncomputable def CartwrightStegerNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  (cartwrightStegerOrderReducedNorm P r).ker

theorem mem_CartwrightStegerNormOneOrderUnits_iff
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) :
    u ∈ CartwrightStegerNormOneOrderUnits P r ↔
      Matrix.GeneralLinearGroup.det (orderUnitToGlobalGL P r u) = 1 := by
  rfl

noncomputable instance cartwrightStegerNormOneOrderUnitsNormal
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerNormOneOrderUnits P r).Normal := by
  dsimp [CartwrightStegerNormOneOrderUnits]
  infer_instance

theorem orderReducedNorm_factors_through_cyclicAlgebra
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ) :
    cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) =
      cartwrightStegerOrderReducedNorm P r u := by
  rfl

/-- Actual norm-one arithmetic-order units map into the global norm-one
group of the cyclic division algebra; the source is not an auxiliary split
special-linear group. -/
noncomputable def orderNormOneToCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) :
    CartwrightStegerNormOneOrderUnits P r →*
      CyclicAlgebraSplitNormOne P r where
  toFun u := ⟨orderUnitToCyclicUnit P r u, by
    change cyclicAlgebraSplitReducedNorm P r
      (orderUnitToCyclicUnit P r u) = 1
    rw [orderReducedNorm_factors_through_cyclicAlgebra]
    exact u.property⟩
  map_one' := Subtype.ext (map_one (orderUnitToCyclicUnit P r))
  map_mul' u v := Subtype.ext (map_mul (orderUnitToCyclicUnit P r)
    (u : (CartwrightStegerOrder P r)ˣ)
    (v : (CartwrightStegerOrder P r)ˣ))

/-- Projectivization of actual arithmetic-order units. -/
noncomputable def cartwrightStegerOrderProjectivization
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →*
      CartwrightStegerOrderProjectiveGroup P r :=
  QuotientGroup.mk' (Subgroup.center ((CartwrightStegerOrder P r)ˣ))

/-- `G'₁(R)`: the projective image of the genuine reduced-norm-one order
units.  Defining it as this image preserves the distinction, emphasized in
LSV, between a projective norm-one class and a chosen norm-one lift. -/
noncomputable def CartwrightStegerProjectiveNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (CartwrightStegerOrderProjectiveGroup P r) :=
  (CartwrightStegerNormOneOrderUnits P r).map
    (cartwrightStegerOrderProjectivization P r)

noncomputable instance cartwrightStegerProjectiveNormOneNormal
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerProjectiveNormOne P r).Normal := by
  exact Subgroup.Normal.map
    (inferInstance : (CartwrightStegerNormOneOrderUnits P r).Normal)
    (cartwrightStegerOrderProjectivization P r)
    (QuotientGroup.mk'_surjective _)

/-- LSV's genuine projective subgroup `Γ₁ = Γ ∩ G'₁(R)`.  It is
not identified with the projection of the norm-one lift lattice. -/
noncomputable def CartwrightStegerProjectiveGammaOne
    (P : BasePrime) (r : Rank) :
    Subgroup (CartwrightStegerOrderProjectiveGroup P r) :=
  CartwrightStegerOrderLattice P r ⊓
    CartwrightStegerProjectiveNormOne P r

theorem mem_CartwrightStegerProjectiveGammaOne_iff
    (P : BasePrime) (r : Rank)
    (g : CartwrightStegerOrderProjectiveGroup P r) :
    g ∈ CartwrightStegerProjectiveGammaOne P r ↔
      g ∈ CartwrightStegerOrderLattice P r ∧
        g ∈ CartwrightStegerProjectiveNormOne P r := by
  rfl

/-- Projectivizing the actual order-unit lift lattice gives precisely the
projective Cartwright--Steger lattice. -/
theorem map_orderUnitLattice_projectivization
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrderUnitLattice P r).map
        (cartwrightStegerOrderProjectivization P r) =
      CartwrightStegerOrderLattice P r := by
  rw [CartwrightStegerOrderUnitLattice, MonoidHom.map_closure,
    CartwrightStegerOrderLattice]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨cartwrightStegerOrderUnitGenerator P r x,
      ⟨x, rfl⟩, rfl⟩

/-- The norm-one lift lattice inside actual arithmetic-order units.  Its
projective image is contained in, but need not equal, LSV's projective
subgroup `Γ₁ = Γ ∩ G'₁(R)`. -/
noncomputable def CartwrightStegerNormOneLiftLattice
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  CartwrightStegerOrderUnitLattice P r ⊓
    CartwrightStegerNormOneOrderUnits P r

theorem mem_CartwrightStegerNormOneLiftLattice_iff
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) :
    u ∈ CartwrightStegerNormOneLiftLattice P r ↔
      u ∈ CartwrightStegerOrderUnitLattice P r ∧
        Matrix.GeneralLinearGroup.det (orderUnitToGlobalGL P r u) = 1 := by
  rfl

/-! ## The selected split coordinates of the norm-one inner form -/

/-- The special-linear matrices over the constant-extended coefficient ring
whose matrix and inverse both descend to the actual Cartwright--Steger
arithmetic order.  The two descent conditions ensure that these are integral
points of the order-unit group, rather than arbitrary matrices in
`SL_d(ConstantArithmeticRing)`. -/
noncomputable def OrderNormOneInnerForm
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) where
  carrier s :=
    ((orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL s) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r ∧
    ((orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL s)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
  one_mem' := by
    constructor <;> simp
  mul_mem' {a b} ha hb := by
    constructor
    · simpa only [map_mul, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem ha.1 hb.1
    · simpa only [map_inv, map_mul, mul_inv_rev, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem hb.2 ha.2
  inv_mem' {a} ha := by
    have hto : Matrix.SpecialLinearGroup.toGL a⁻¹ =
        (Matrix.SpecialLinearGroup.toGL a)⁻¹ :=
      map_inv (Matrix.SpecialLinearGroup.toGL) a
    constructor
    · rw [hto, map_inv]
      exact ha.2
    · rw [hto, inv_inv]
      exact ha.1

/-- Coefficient reduction on special-linear matrices in the selected split
coordinates.  This is kept separate from the descent subgroup so that the
comparison with ordinary matrix lifting remains explicit. -/
noncomputable def orderSpecialLinearReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (indexConstantArithmeticEval P r level)

/-- The split local integral model lifts every finite special-linear point.
This is the local-lifting half of the argument only: the source here is the
full split `SL`, so the separate theorem below still has to force a lift into
the cyclic-order descent subgroup `OrderNormOneInnerForm`. -/
theorem orderSpecialLinearReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderSpecialLinearReduction P r level) := by
  cases r with
  | three =>
      exact CongruenceLifting.specialLinearMap_surjective_fin3
        (indexConstantArithmeticEval P .three level)
        (indexConstantArithmeticEval_surjective P .three level)
  | four =>
      exact CongruenceLifting.specialLinearMap_surjective_fin4
        (indexConstantArithmeticEval P .four level)
        (indexConstantArithmeticEval_surjective P .four level)

/-- Genuine congruence reduction of the selected norm-one inner-form
integral points to finite `PSL`.  Its domain carries the checked descent of
both a unit and its inverse to the actual cyclic-algebra order. -/
noncomputable def orderNormOneInnerFormReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →* PSL P r level :=
  (specialLinearToPSL P r level).comp
    ((orderSpecialLinearReduction P r level).comp
      (OrderNormOneInnerForm P r).subtype)

/-- Kernel of the split local special-linear reduction. -/
noncomputable def OrderSpecialLinearCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  (orderSpecialLinearReduction P r level).ker

noncomputable instance orderSpecialLinearCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSpecialLinearCongruenceSubgroup P r level).Normal := by
  dsimp [OrderSpecialLinearCongruenceSubgroup]
  infer_instance

/-- Exact algebraic form of the remaining construction-specialized strong
approximation statement.  Because split local lifting is already proved,
restriction to the genuine cyclic-order descent subgroup is onto precisely
when that subgroup together with the split congruence kernel fills the whole
split integral special-linear group. -/
theorem orderNormOneInnerForm_splitReduction_surjective_iff_sup_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
        ((orderSpecialLinearReduction P r level).comp
          (OrderNormOneInnerForm P r).subtype) ↔
      OrderNormOneInnerForm P r ⊔
          OrderSpecialLinearCongruenceSubgroup P r level = ⊤ := by
  constructor
  · intro hsurj
    apply top_unique
    intro x hx
    obtain ⟨d, hd⟩ := hsurj (orderSpecialLinearReduction P r level x)
    change orderSpecialLinearReduction P r level
        (d : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) =
      orderSpecialLinearReduction P r level x at hd
    have hk : (d : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))⁻¹ * x ∈
        OrderSpecialLinearCongruenceSubgroup P r level := by
      change orderSpecialLinearReduction P r level
          ((d : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))⁻¹ * x) = 1
      rw [map_mul, map_inv, hd]
      simp
    have hmem := Subgroup.mul_mem_sup d.property hk
    simpa using hmem
  · intro htop y
    obtain ⟨x, hx⟩ := orderSpecialLinearReduction_surjective P r level y
    have hmem : x ∈ OrderNormOneInnerForm P r ⊔
        OrderSpecialLinearCongruenceSubgroup P r level := by
      rw [htop]
      exact Subgroup.mem_top x
    obtain ⟨d, hd, k, hk, hdk⟩ :=
      (Subgroup.mem_sup_of_normal_right).mp hmem
    refine ⟨⟨d, hd⟩, ?_⟩
    change orderSpecialLinearReduction P r level d = y
    have hkone : orderSpecialLinearReduction P r level k = 1 := hk
    rw [← hx, ← hdk, map_mul, hkone, mul_one]

/-- A descended split-coordinate point gives an actual unit of the
Cartwright--Steger arithmetic order. -/
noncomputable def orderNormOneInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      (CartwrightStegerOrder P r)ˣ where
  toFun s :=
    { val := ⟨(orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL (s :
            Matrix.SpecialLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r))) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), s.property.1⟩
      inv := ⟨((orderSplitBaseChangeGLHom P r
          (Matrix.SpecialLinearGroup.toGL (s :
            Matrix.SpecialLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r))))⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), s.property.2⟩
      val_inv := by
        apply Subtype.ext
        exact Units.val_inv _
      inv_val := by
        apply Subtype.ext
        exact Units.inv_val _ }
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply Units.ext
    apply Subtype.ext
    simp

theorem orderUnitToGlobalGL_orderNormOneInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    orderUnitToGlobalGL P r
        (orderNormOneInnerFormToOrderUnits P r s) =
      orderSplitBaseChangeGLHom P r
        (Matrix.SpecialLinearGroup.toGL (s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) := by
  apply Units.ext
  rfl

theorem orderNormOneInnerFormToOrderUnits_mem_normOne
    (P : BasePrime) (r : Rank) (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormToOrderUnits P r s ∈
      CartwrightStegerNormOneOrderUnits P r := by
  rw [mem_CartwrightStegerNormOneOrderUnits_iff,
    orderUnitToGlobalGL_orderNormOneInnerFormToOrderUnits]
  change Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map
        (constantArithmeticToSplittingFunctionField P r)
        (Matrix.SpecialLinearGroup.toGL (s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)))) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  simp

/-- The descended split-coordinate group maps into the independently
defined norm-one kernel of actual arithmetic-order units. -/
noncomputable def orderNormOneInnerFormToActualNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      CartwrightStegerNormOneOrderUnits P r where
  toFun s := ⟨orderNormOneInnerFormToOrderUnits P r s,
    orderNormOneInnerFormToOrderUnits_mem_normOne P r s⟩
  map_one' := Subtype.ext (map_one (orderNormOneInnerFormToOrderUnits P r))
  map_mul' s t :=
    Subtype.ext (map_mul (orderNormOneInnerFormToOrderUnits P r) s t)

theorem constantArithmeticToSplittingFunctionField_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (constantArithmeticToSplittingFunctionField P r) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers
      (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r))
    (constantArithmeticToSplittingFunctionField P r)]
  intro f g
  simp only [constantArithmeticToSplittingFunctionField_algebraMap]
  constructor
  · intro h
    simpa only [constantArithmeticToSplittingFunctionField_algebraMap] using
      congrArg (constantArithmeticToSplittingFunctionField P r) h
  · intro h
    have hfg : f = g :=
      RatFunc.algebraMap_injective (ConstantExtension P r) h
    subst g
    rfl

theorem orderSplitBaseChangeGLHom_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderSplitBaseChangeGLHom P r) := by
  intro A B hAB
  apply Units.ext
  ext i j
  apply constantArithmeticToSplittingFunctionField_injective P r
  exact congrArg (fun M : Matrix.GeneralLinearGroup
      (Fin r.matrixRank) (SplittingFunctionField P r) =>
    ((M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) i j)) hAB

theorem cyclicAlgebraBuildingNormOneGeneratorRatio_ne_one
    (P : BasePrime) (r : Rank)
    {u v : ConstantProjectiveClass P r} (huv : u ≠ v) :
    cyclicAlgebraBuildingNormOneGeneratorRatio P r u v ≠ 1 := by
  intro hratio
  have hcyclic : cartwrightStegerGeneratorCyclicUnit P r u =
      cartwrightStegerGeneratorCyclicUnit P r v := by
    have hunit := congrArg Subtype.val hratio
    change cartwrightStegerGeneratorCyclicUnit P r u *
        (cartwrightStegerGeneratorCyclicUnit P r v)⁻¹ = 1 at hunit
    exact mul_inv_eq_one.mp hunit
  have hglobal : cartwrightStegerGenerator P r u =
      cartwrightStegerGenerator P r v := by
    apply Units.ext
    simpa only [cartwrightStegerGeneratorCyclicUnit_coe,
      cartwrightStegerGeneratorCyclicElement_coe] using
        congrArg (fun x : (CyclicAlgebra P r)ˣ =>
          ((x : CyclicAlgebra P r) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (SplittingFunctionField P r))) hcyclic
  have hsplit : orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) =
      orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r v) := by
    apply orderSplitBaseChangeGLHom_injective P r
    rw [map_orderSplitCartwrightStegerClassGeneratorGL_to_global,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact hglobal
  have hfinite := congrArg (orderSplitReductionPGLHom P r 0) hsplit
  rw [orderSplitReductionPGLHom_classGenerator,
    orderSplitReductionPGLHom_classGenerator] at hfinite
  exact huv (indexCartwrightStegerClassGenerator_injective P r 0 hfinite)

theorem exists_ne_one_cyclicAlgebraBuildingNormOne
    (P : BasePrime) (r : Rank) :
    ∃ g : CyclicAlgebraBuildingNormOne P r, g ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  exact ⟨cyclicAlgebraBuildingNormOneGeneratorRatio P r u v,
    cyclicAlgebraBuildingNormOneGeneratorRatio_ne_one P r huv⟩

/-- Extension of localized arithmetic coefficients from `F_q` to the
construction's constant field `F_(q^d)`. -/
noncomputable def arithmeticToConstantArithmetic
    (P : BasePrime) (r : Rank) :
    ArithmeticRing P →+* ConstantArithmeticRing P r :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
    (S := ArithmeticRing P)
    (g := (algebraMap (ConstantPolynomialRing P r)
      (ConstantArithmeticRing P r)).comp
        (Polynomial.mapRingHom
          (algebraMap (BaseField P) (ConstantExtension P r)))) (by
      change IsUnit (algebraMap (ConstantPolynomialRing P r)
        (ConstantArithmeticRing P r)
          (Polynomial.mapRingHom
            (algebraMap (BaseField P) (ConstantExtension P r))
              (Polynomial.X * (1 + Polynomial.X))))
      have hmap : Polynomial.mapRingHom
          (algebraMap (BaseField P) (ConstantExtension P r))
            (Polynomial.X * (1 + Polynomial.X)) =
          (Polynomial.X * (1 + Polynomial.X) : Polynomial (ConstantExtension P r)) := by
        simp only [map_mul, map_add, map_one, Polynomial.coe_mapRingHom,
          Polynomial.map_X]
      rw [hmap]
      exact
        (IsLocalization.Away.algebraMap_isUnit
          (R := ConstantPolynomialRing P r)
          (S := ConstantArithmeticRing P r)
          (Polynomial.X * (1 + Polynomial.X))))

@[simp] theorem arithmeticToConstantArithmetic_algebraMap
    (P : BasePrime) (r : Rank) (f : PolynomialRing P) :
    arithmeticToConstantArithmetic P r
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      algebraMap (ConstantPolynomialRing P r)
        (ConstantArithmeticRing P r)
          (Polynomial.mapRingHom
            (algebraMap (BaseField P) (ConstantExtension P r)) f) := by
  exact IsLocalization.Away.lift_eq _ _ _

theorem constantArithmeticToSplittingFunctionField_arithmeticBaseChange
    (P : BasePrime) (r : Rank) (a : ArithmeticRing P) :
    constantArithmeticToSplittingFunctionField P r
        (arithmeticToConstantArithmetic P r a) =
      arithmeticRingToSplittingFunctionField P r a := by
  have heq :
      (constantArithmeticToSplittingFunctionField P r).comp
          (arithmeticToConstantArithmetic P r) =
        arithmeticRingToSplittingFunctionField P r := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers
        (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    ext f
    simp [RingHom.comp_apply, arithmeticRingToSplittingFunctionField,
      arithmeticRingToFunctionField_algebraMap,
      constantArithmeticToSplittingFunctionField_algebraMap,
      functionFieldEmbedding_C]
    simp only [RingHom.comp_apply]
    rw [arithmeticToConstantArithmetic_algebraMap,
      constantArithmeticToSplittingFunctionField_algebraMap,
      arithmeticRingToSplittingFunctionField,
      RingHom.comp_apply, arithmeticRingToFunctionField_algebraMap]
    simp [functionFieldEmbedding_X]
  exact DFunLike.congr_fun heq a

theorem indexConstantArithmeticEval_arithmeticBaseChange
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ArithmeticRing P) :
    indexConstantArithmeticEval P r level
        (arithmeticToConstantArithmetic P r a) =
      indexArithmeticEval P r level a := by
  have heq :
      (indexConstantArithmeticEval P r level).comp
          (arithmeticToConstantArithmetic P r) =
        indexArithmeticEval P r level := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers
        (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P))
    ext f
    simp [RingHom.comp_apply, indexArithmeticEval_algebraMap,
      indexConstantArithmeticEval_algebraMap, indexPolynomialEval]
    simp only [RingHom.comp_apply]
    rw [arithmeticToConstantArithmetic_algebraMap,
      indexConstantArithmeticEval_algebraMap,
      indexArithmeticEval_algebraMap]
    change indexConstantPolynomialEval P r level
        (Polynomial.map
          (algebraMap (BaseField P) (ConstantExtension P r)) Polynomial.X) =
      indexPolynomialEval P r level Polynomial.X
    exact indexConstantPolynomialEval_map_base P r level Polynomial.X
  exact DFunLike.congr_fun heq a

/-- Base extension on special-linear matrices. -/
noncomputable def arithmeticSpecialLinearToConstant
    (P : BasePrime) (r : Rank) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (arithmeticToConstantArithmetic P r)

theorem orderSpecialLinearReduction_arithmeticBaseChange
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P)) :
    orderSpecialLinearReduction P r level
        (arithmeticSpecialLinearToConstant P r s) =
      CongruenceLifting.indexSpecialLinearReduction P r level s := by
  apply Subtype.ext
  ext i j
  exact indexConstantArithmeticEval_arithmeticBaseChange P r level (s i j)

/-! ## Nondegeneracy of the selected finite cyclic coordinates -/

/-- The matrix of the inverse-Frobenius conjugates of the fixed constant-field
basis, evaluated in the selected residue field.  This is the change-of-
coordinates matrix which makes the cyclic algebra split at the selected
finite place; it is constructed from the chosen embedding rather than
received as external matrix data. -/
noncomputable def indexConjugateBasisMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  fun i j => indexConstantEmbedding P r level
    (((constantFrobenius P r).symm ^ (i : Nat))
      (constantBasis P r j))

/-- The inverse-Frobenius embeddings whose basis evaluations form
`indexConjugateBasisMatrix`. -/
noncomputable def indexConjugateAlgHom
    (P : BasePrime) (r : Rank) (level : Nat)
    (i : Fin r.matrixRank) :
    ConstantExtension P r →ₐ[BaseField P] ResidueField P r level :=
  (indexConstantEmbedding P r level).comp
    (((constantFrobenius P r).symm ^ (i : Nat)).toAlgHom)

theorem indexConjugateAlgHom_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexConjugateAlgHom P r level) := by
  intro i j hij
  have hpowers : (constantFrobenius P r).symm ^ (i : Nat) =
      (constantFrobenius P r).symm ^ (j : Nat) := by
    apply AlgEquiv.ext
    intro x
    apply (indexConstantEmbedding P r level).injective
    exact DFunLike.congr_fun hij x
  apply Fin.ext
  apply pow_injOn_Iio_orderOf
      (x := (constantFrobenius P r).symm)
  · change (i : Nat) < orderOf ((constantFrobenius P r)⁻¹)
    rw [orderOf_inv, constantFrobenius_order]
    exact i.isLt
  · change (j : Nat) < orderOf ((constantFrobenius P r)⁻¹)
    rw [orderOf_inv, constantFrobenius_order]
    exact j.isLt
  · exact hpowers

theorem indexConjugateAlgHom_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (fun i : Fin r.matrixRank =>
        (indexConjugateAlgHom P r level i).toLinearMap) :=
  (linearIndependent_algHom_toLinearMap
    (BaseField P) (ConstantExtension P r)
      (ResidueField P r level)).comp
        (indexConjugateAlgHom P r level)
        (indexConjugateAlgHom_injective P r level)

/-- Evaluation of a base-field-linear map on the fixed constant-field
basis, with residue-field scalars on the space of maps. -/
noncomputable def indexConstantBasisEvaluationLinearMap
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ConstantExtension P r →ₗ[BaseField P] ResidueField P r level) →ₗ[
        ResidueField P r level]
      (Fin r.matrixRank → ResidueField P r level) where
  toFun f i := f (constantBasis P r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem indexConstantBasisEvaluationLinearMap_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (indexConstantBasisEvaluationLinearMap P r level) := by
  intro f g hfg
  apply (constantBasis P r).ext
  intro i
  exact congrFun hfg i

/-- The distinct inverse-Frobenius embeddings of the constant field into the
selected residue field are linearly independent over that residue field. -/
theorem indexConjugateBasisMatrix_rows_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (indexConjugateBasisMatrix P r level) := by
  have hmap := (indexConjugateAlgHom_linearIndependent P r level).map'
    (indexConstantBasisEvaluationLinearMap P r level)
    (LinearMap.ker_eq_bot.mpr
      (indexConstantBasisEvaluationLinearMap_injective P r level))
  exact hmap

/-- Consequently the conjugate-basis matrix is invertible. -/
theorem indexConjugateBasisMatrix_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexConjugateBasisMatrix P r level) :=
  Matrix.linearIndependent_rows_iff_isUnit.mp
    (indexConjugateBasisMatrix_rows_linearIndependent P r level)

/-- The columns of the conjugate-basis matrix are linearly independent as
well.  These columns are precisely the diagonal coordinate vectors of the
constant-field basis in the selected split representation. -/
theorem indexConjugateBasisMatrix_cols_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (fun j => Matrix.col
        (indexConjugateBasisMatrix P r level) j) :=
  Matrix.linearIndependent_cols_iff_isUnit.mpr
    (indexConjugateBasisMatrix_isUnit P r level)

theorem indexConstantMatrix_fixedBasis_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (fun j : Fin r.matrixRank =>
        indexConstantMatrix P r level (constantBasis P r j)) := by
  have hdiag :=
    (indexConjugateBasisMatrix_cols_linearIndependent P r level).map'
      (Matrix.diagonalLinearMap (Fin r.matrixRank)
        (ResidueField P r level) (ResidueField P r level))
      (LinearMap.ker_eq_bot.mpr
        (diagonalLinearMap_injective (Fin r.matrixRank)))
  exact hdiag

theorem span_indexConstantMatrix_fixedBasis_eq_range_diagonal
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule.span (ResidueField P r level)
        (Set.range (fun j : Fin r.matrixRank =>
          indexConstantMatrix P r level (constantBasis P r j))) =
      LinearMap.range (Matrix.diagonalLinearMap (Fin r.matrixRank)
        (ResidueField P r level) (ResidueField P r level)) := by
  let D := Matrix.diagonalLinearMap (Fin r.matrixRank)
    (ResidueField P r level) (ResidueField P r level)
  have hcols := indexConjugateBasisMatrix_cols_linearIndependent P r level
  have hspan : Submodule.span (ResidueField P r level)
      (Set.range (indexConjugateBasisMatrix P r level).col) = ⊤ := by
    apply hcols.span_eq_top_of_card_eq_finrank
    simp
  have hfamily :
      (fun j : Fin r.matrixRank =>
        indexConstantMatrix P r level (constantBasis P r j)) =
      D ∘ (indexConjugateBasisMatrix P r level).col := by
    funext j
    rfl
  rw [hfamily, Set.range_comp, ← Submodule.map_span, hspan,
    Submodule.map_top]

/-- The `d²` cyclic family in the selected finite split matrix algebra. -/
noncomputable def indexCyclicBasisVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  indexConstantMatrix P r level (constantBasis P r p.1) *
    indexCyclicGeneratorMatrix P r level ^ (p.2 : Nat)

theorem diagonal_mul_indexCyclicGenerator_pow_mem_span
    (P : BasePrime) (r : Rank) (level : Nat)
    (v : Fin r.matrixRank → ResidueField P r level)
    (k : Fin r.matrixRank) :
    Matrix.diagonal v * indexCyclicGeneratorMatrix P r level ^ (k : Nat) ∈
      Submodule.span (ResidueField P r level)
        (Set.range (indexCyclicBasisVector P r level)) := by
  let target := Submodule.span (ResidueField P r level)
    (Set.range (indexCyclicBasisVector P r level))
  have hDiagonal : Matrix.diagonal v ∈
      Submodule.span (ResidueField P r level)
        (Set.range (fun j : Fin r.matrixRank =>
          indexConstantMatrix P r level (constantBasis P r j))) := by
    rw [span_indexConstantMatrix_fixedBasis_eq_range_diagonal]
    exact ⟨v, rfl⟩
  refine Submodule.span_induction
    (p := fun D _ => D * indexCyclicGeneratorMatrix P r level ^ (k : Nat) ∈
      target) ?basis ?zero ?add ?smul hDiagonal
  · intro D hD
    obtain ⟨j, rfl⟩ := hD
    exact Submodule.subset_span ⟨(j, k), rfl⟩
  · simp [target]
  · intro A B _ _ hA hB
    rw [add_mul]
    exact target.add_mem hA hB
  · intro a A _ hA
    rw [smul_mul_assoc]
    exact target.smul_mem a hA

/-- The selected finite cyclic family spans every matrix.  The proof checks
the two construction ranks against their actual weighted shift matrices. -/
theorem span_indexCyclicBasisVector_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule.span (ResidueField P r level)
      (Set.range (indexCyclicBasisVector P r level)) = ⊤ := by
  apply top_unique
  intro A _
  cases r with
  | three =>
      simp only [Rank.matrixRank_three] at A ⊢
      let a : ResidueField P .three level :=
        1 + indexPlaceY P .three level
      let Z : Matrix (Fin 3) (Fin 3) (ResidueField P .three level) :=
        !![0, 0, a; 1, 0, 0; 0, 1, 0]
      let v0 : Fin 3 → ResidueField P .three level :=
        ![A 0 0, A 1 1, A 2 2]
      let v1 : Fin 3 → ResidueField P .three level :=
        ![a⁻¹ * A 0 2, A 1 0, A 2 1]
      let v2 : Fin 3 → ResidueField P .three level :=
        ![a⁻¹ * A 0 1, a⁻¹ * A 1 2, A 2 0]
      have h0 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .three level v0 (0 : Fin 3)
      have h1 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .three level v1 (1 : Fin 3)
      have h2 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .three level v2 (2 : Fin 3)
      have hsum := (Submodule.span (ResidueField P .three level)
        (Set.range (indexCyclicBasisVector P .three level))).add_mem
          ((Submodule.span (ResidueField P .three level)
            (Set.range (indexCyclicBasisVector P .three level))).add_mem h0 h1) h2
      have hdecomp : A = Matrix.diagonal v0 * Z ^ 0 +
          Matrix.diagonal v1 * Z ^ 1 + Matrix.diagonal v2 * Z ^ 2 := by
        dsimp [v0, v1, v2, Z, a]
        simp only [pow_zero, pow_one, pow_two]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          field_simp [indexPlaceY_one_add_ne_zero]
      rw [hdecomp]
      exact hsum
  | four =>
      simp only [Rank.matrixRank_four] at A ⊢
      let a : ResidueField P .four level :=
        1 + indexPlaceY P .four level
      let Z : Matrix (Fin 4) (Fin 4) (ResidueField P .four level) :=
        !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]
      let v0 : Fin 4 → ResidueField P .four level :=
        ![A 0 0, A 1 1, A 2 2, A 3 3]
      let v1 : Fin 4 → ResidueField P .four level :=
        ![a⁻¹ * A 0 3, A 1 0, A 2 1, A 3 2]
      let v2 : Fin 4 → ResidueField P .four level :=
        ![a⁻¹ * A 0 2, a⁻¹ * A 1 3, A 2 0, A 3 1]
      let v3 : Fin 4 → ResidueField P .four level :=
        ![a⁻¹ * A 0 1, a⁻¹ * A 1 2, a⁻¹ * A 2 3, A 3 0]
      have h0 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v0 (0 : Fin 4)
      have h1 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v1 (1 : Fin 4)
      have h2 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v2 (2 : Fin 4)
      have h3 := diagonal_mul_indexCyclicGenerator_pow_mem_span
        P .four level v3 (3 : Fin 4)
      let target := Submodule.span (ResidueField P .four level)
        (Set.range (indexCyclicBasisVector P .four level))
      have hsum := target.add_mem
        (target.add_mem (target.add_mem h0 h1) h2) h3
      have hdecomp : A = Matrix.diagonal v0 * Z ^ 0 +
          Matrix.diagonal v1 * Z ^ 1 + Matrix.diagonal v2 * Z ^ 2 +
            Matrix.diagonal v3 * Z ^ 3 := by
        dsimp [v0, v1, v2, v3, Z, a]
        simp only [pow_zero, pow_one, pow_two, pow_three]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
          field_simp [indexPlaceY_one_add_ne_zero]
      rw [hdecomp]
      exact hsum

theorem indexCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) (level : Nat) :
    LinearIndependent (ResidueField P r level)
      (indexCyclicBasisVector P r level) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_indexCyclicBasisVector_eq_top]
  · simp [Module.finrank_matrix]

/-- The actual cyclic basis of the full matrix algebra at the selected
finite place. -/
noncomputable def indexCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (ResidueField P r level)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level)) :=
  Module.Basis.mk (indexCyclicBasisVector_linearIndependent P r level)
    (by rw [span_indexCyclicBasisVector_eq_top])

@[simp] theorem indexCyclicBasis_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    indexCyclicBasis P r level p = indexCyclicBasisVector P r level p := by
  simp [indexCyclicBasis]

/-- Integral split-coordinate representative of a cyclic basis vector. -/
noncomputable def orderIndexCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  orderSplitConstantMatrix P r (constantBasis P r p.1) *
    orderSplitCyclicGeneratorMatrix P r ^ (p.2 : Nat)

@[simp] theorem orderIndexCyclicBasisVector_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (orderIndexCyclicBasisVector P r p).map
        (indexConstantArithmeticEval P r level) =
      indexCyclicBasisVector P r level p := by
  rw [orderIndexCyclicBasisVector, indexCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow, map_orderSplitConstantMatrix,
    map_orderSplitCyclicGeneratorMatrix]

@[simp] theorem orderIndexCyclicBasisVector_to_global
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (orderIndexCyclicBasisVector P r p).map
        (constantArithmeticToSplittingFunctionField P r) =
      splittingCyclicBasisVector P r p := by
  rw [orderIndexCyclicBasisVector, splittingCyclicBasisVector,
    Matrix.map_mul, Matrix.map_pow, map_orderSplitConstantMatrix_to_global,
    map_orderSplitCyclicGeneratorMatrix_to_global]

theorem splittingCyclicBasisVector_mem_order
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    splittingCyclicBasisVector P r p ∈ CartwrightStegerOrder P r := by
  exact (CartwrightStegerOrder P r).mul_mem
    (constantMatrix_mem_cartwrightStegerOrder P r (constantBasis P r p.1))
    ((CartwrightStegerOrder P r).pow_mem
      (cyclicGeneratorMatrix_mem_cartwrightStegerOrder P r) (p.2 : Nat))

/-- A chosen arithmetic coefficient lifting a selected residue-field
coefficient.  Surjectivity comes from the explicitly selected irreducible
polynomial, not from an external residue map. -/
noncomputable def indexArithmeticCoefficientLift
    (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level → ArithmeticRing P :=
  Function.surjInv (indexArithmeticEval_surjective P r level)

@[simp] theorem indexArithmeticCoefficientLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ResidueField P r level) :
    indexArithmeticEval P r level
        (indexArithmeticCoefficientLift P r level a) = a :=
  Function.surjInv_eq (indexArithmeticEval_surjective P r level) a

/-- A construction-owned additive lift of an arbitrary finite matrix in the
cyclic basis.  Its coefficients are lifted through the base arithmetic ring,
so its global image lies in the actual cyclic order. -/
noncomputable def orderIndexMatrixLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p : Fin r.matrixRank × Fin r.matrixRank,
    arithmeticToConstantArithmetic P r
        (indexArithmeticCoefficientLift P r level
          ((indexCyclicBasis P r level).repr A p)) •
      orderIndexCyclicBasisVector P r p

theorem orderIndexMatrixLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLift P r level A).map
        (indexConstantArithmeticEval P r level) = A := by
  rw [orderIndexMatrixLift]
  have hmapSum :
      ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          arithmeticToConstantArithmetic P r
              (indexArithmeticCoefficientLift P r level
                ((indexCyclicBasis P r level).repr A p)) •
            orderIndexCyclicBasisVector P r p).map
        (indexConstantArithmeticEval P r level)) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        (arithmeticToConstantArithmetic P r
              (indexArithmeticCoefficientLift P r level
                ((indexCyclicBasis P r level).repr A p)) •
            orderIndexCyclicBasisVector P r p).map
          (indexConstantArithmeticEval P r level) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  simp_rw [Matrix.map_smul' _ _ _ (map_mul _),
    orderIndexCyclicBasisVector_reduction,
    indexConstantArithmeticEval_arithmeticBaseChange,
    indexArithmeticCoefficientLift_reduction]
  simpa only [indexCyclicBasis_apply] using
    (indexCyclicBasis P r level).sum_repr A

theorem orderIndexMatrixLift_to_global
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLift P r level A).map
        (constantArithmeticToSplittingFunctionField P r) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        arithmeticRingToSplittingFunctionField P r
            (indexArithmeticCoefficientLift P r level
              ((indexCyclicBasis P r level).repr A p)) •
          splittingCyclicBasisVector P r p := by
  rw [orderIndexMatrixLift]
  have hmapSum :
      ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          arithmeticToConstantArithmetic P r
              (indexArithmeticCoefficientLift P r level
                ((indexCyclicBasis P r level).repr A p)) •
            orderIndexCyclicBasisVector P r p).map
        (constantArithmeticToSplittingFunctionField P r)) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        (arithmeticToConstantArithmetic P r
              (indexArithmeticCoefficientLift P r level
                ((indexCyclicBasis P r level).repr A p)) •
            orderIndexCyclicBasisVector P r p).map
          (constantArithmeticToSplittingFunctionField P r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  simp_rw [Matrix.map_smul' _ _ _ (map_mul _),
    constantArithmeticToSplittingFunctionField_arithmeticBaseChange,
    orderIndexCyclicBasisVector_to_global]

theorem orderIndexMatrixLift_to_global_mem_order
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLift P r level A).map
        (constantArithmeticToSplittingFunctionField P r) ∈
      CartwrightStegerOrder P r := by
  rw [orderIndexMatrixLift_to_global]
  apply (CartwrightStegerOrder P r).sum_mem
  intro p hp
  let c := indexArithmeticCoefficientLift P r level
    ((indexCyclicBasis P r level).repr A p)
  have hmem := (CartwrightStegerOrder P r).smul_mem
    (splittingCyclicBasisVector_mem_order P r p) c
  change arithmeticRingToSplitMatrix P r c * splittingCyclicBasisVector P r p ∈
    CartwrightStegerOrder P r at hmem
  simpa only [c, arithmeticRingToSplitMatrix, RingHom.comp_apply,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] using hmem

/-! ## The selected local order lift -/

/-- The selected prime of the constant-extended arithmetic coefficient ring. -/
noncomputable def IndexConstantArithmeticPrime
    (P : BasePrime) (r : Rank) (level : Nat) :
    Ideal (ConstantArithmeticRing P r) :=
  RingHom.ker (indexConstantArithmeticEval P r level)

noncomputable instance indexConstantArithmeticPrime_isPrime
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexConstantArithmeticPrime P r level).IsPrime := by
  dsimp [IndexConstantArithmeticPrime]
  exact RingHom.ker_isPrime (indexConstantArithmeticEval P r level)

/-- Local coefficient ring of the selected congruence place. -/
noncomputable abbrev IndexLocalCoefficientRing
    (P : BasePrime) (r : Rank) (level : Nat) :=
  Localization.AtPrime (IndexConstantArithmeticPrime P r level)

/-- The residue map extended from the arithmetic coefficient ring to its
localization at the selected congruence prime. -/
noncomputable def indexLocalReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexLocalCoefficientRing P r level →+* ResidueField P r level :=
  IsLocalization.lift
    (M := (IndexConstantArithmeticPrime P r level).primeCompl)
    (S := IndexLocalCoefficientRing P r level)
    (g := indexConstantArithmeticEval P r level) (by
      intro x
      rw [isUnit_iff_ne_zero]
      intro hx
      apply x.property
      change indexConstantArithmeticEval P r level x = 0
      exact hx)

@[simp] theorem indexLocalReduction_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ConstantArithmeticRing P r) :
    indexLocalReduction P r level
        (algebraMap (ConstantArithmeticRing P r)
          (IndexLocalCoefficientRing P r level) a) =
      indexConstantArithmeticEval P r level a := by
  exact IsLocalization.lift_eq _ _

/-- The additive cyclic-order lift, now regarded over the selected local
coefficient ring. -/
noncomputable def orderIndexMatrixLocalLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexLocalCoefficientRing P r level) :=
  (orderIndexMatrixLift P r level A).map
    (algebraMap (ConstantArithmeticRing P r)
      (IndexLocalCoefficientRing P r level))

theorem orderIndexMatrixLocalLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLocalLift P r level A).map
        (indexLocalReduction P r level) = A := by
  ext i j
  change indexLocalReduction P r level
      (algebraMap (ConstantArithmeticRing P r)
        (IndexLocalCoefficientRing P r level)
          (orderIndexMatrixLift P r level A i j)) = A i j
  rw [indexLocalReduction_algebraMap]
  exact congrFun (congrFun
    (orderIndexMatrixLift_reduction P r level A) i) j

theorem indexConstantArithmeticEval_det_orderIndexMatrixLift_special
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    indexConstantArithmeticEval P r level
        (Matrix.det (orderIndexMatrixLift P r level
          (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ResidueField P r level)))) = 1 := by
  calc
    _ = Matrix.det ((orderIndexMatrixLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).map
            (indexConstantArithmeticEval P r level)) :=
      by
        simpa only [RingHom.mapMatrix_apply] using
          RingHom.map_det (indexConstantArithmeticEval P r level)
            (orderIndexMatrixLift P r level
              (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (ResidueField P r level)))
    _ = Matrix.det (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
      rw [orderIndexMatrixLift_reduction]
    _ = 1 := s.property

theorem orderIndexMatrixLocalLift_special_isUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsUnit (orderIndexMatrixLocalLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : Matrix.det (orderIndexMatrixLocalLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))) =
      algebraMap (ConstantArithmeticRing P r)
        (IndexLocalCoefficientRing P r level)
          (Matrix.det (orderIndexMatrixLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ResidueField P r level)))) := by
    rw [orderIndexMatrixLocalLift]
    simpa only [RingHom.mapMatrix_apply] using
      (RingHom.map_det
        (algebraMap (ConstantArithmeticRing P r)
          (IndexLocalCoefficientRing P r level))
        (orderIndexMatrixLift P r level
          (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ResidueField P r level)))).symm
  rw [hdet]
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (IndexLocalCoefficientRing P r level)
    (IndexConstantArithmeticPrime P r level) _).mpr
  change Matrix.det (orderIndexMatrixLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))) ∉
    RingHom.ker (indexConstantArithmeticEval P r level)
  rw [RingHom.mem_ker,
    indexConstantArithmeticEval_det_orderIndexMatrixLift_special]
  exact one_ne_zero

/-- Every finite special-linear matrix has a local invertible lift whose
matrix comes from the explicitly lifted cyclic-order coordinates. -/
noncomputable def orderIndexSpecialLocalLiftGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (IndexLocalCoefficientRing P r level) :=
  (orderIndexMatrixLocalLift_special_isUnit P r level s).unit

@[simp] theorem orderIndexSpecialLocalLiftGL_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexSpecialLocalLiftGL P r level s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexLocalCoefficientRing P r level)) =
      orderIndexMatrixLocalLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) :=
  IsUnit.unit_spec (orderIndexMatrixLocalLift_special_isUnit P r level s)

theorem orderIndexSpecialLocalLiftGL_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.GeneralLinearGroup.map (indexLocalReduction P r level)
        (orderIndexSpecialLocalLiftGL P r level s) =
      Matrix.SpecialLinearGroup.toGL s := by
  apply Units.ext
  change (orderIndexSpecialLocalLiftGL P r level s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexLocalCoefficientRing P r level)).map
          (indexLocalReduction P r level) =
    (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level))
  rw [orderIndexSpecialLocalLiftGL_coe]
  exact orderIndexMatrixLocalLift_reduction P r level s

theorem orderIndexSpecialLift_to_global_mem_order
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).map
        (constantArithmeticToSplittingFunctionField P r) ∈
      CartwrightStegerOrder P r :=
  orderIndexMatrixLift_to_global_mem_order P r level s

/-! ## Norm correction in the selected completed local ring -/

theorem matrixRank_cast_ne_zero_residueField
    (P : BasePrime) (r : Rank) (level : Nat) :
    (r.matrixRank : ResidueField P r level) ≠ 0 := by
  intro hzero
  have hbase : (r.matrixRank : BaseField P) = 0 := by
    apply (algebraMap (BaseField P) (ResidueField P r level)).injective
    simpa using hzero
  rw [ZMod.natCast_eq_zero_iff] at hbase
  have hle : P.q ≤ r.matrixRank :=
    Nat.le_of_dvd (by cases r <;> simp [Rank.matrixRank]) hbase
  have hfive := P.five_le
  cases r <;> simp [Rank.matrixRank] at hle <;> omega

/-- In characteristic prime to the selected matrix rank, every power series
with constant coefficient one has a `d`-th root with constant coefficient
one.  This is the precise Hensel norm-correction step used in LSV. -/
theorem exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : PowerSeries (ResidueField P r level))
    (hu : PowerSeries.constantCoeff u = 1) :
    ∃ a : PowerSeries (ResidueField P r level),
      a ^ r.matrixRank = u ∧ PowerSeries.constantCoeff a = 1 := by
  let I : Ideal (PowerSeries (ResidueField P r level)) :=
    Ideal.span {PowerSeries.X}
  let f : Polynomial (PowerSeries (ResidueField P r level)) :=
    Polynomial.X ^ r.matrixRank - Polynomial.C u
  have hrank : r.matrixRank ≠ 0 := by cases r <;> simp [Rank.matrixRank]
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_C u hrank
  have hroot : f.eval 1 ∈ I := by
    dsimp [f, I]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, one_pow]
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [hu]
  have hdunit : IsUnit
      (r.matrixRank : PowerSeries (ResidueField P r level)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using matrixRank_cast_ne_zero_residueField P r level
  have hderiv : IsUnit
      (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    have heval : f.derivative.eval 1 =
        (r.matrixRank : PowerSeries (ResidueField P r level)) := by
      simp [f, Polynomial.derivative_X_pow]
    rw [heval]
    exact hdunit.map (Ideal.Quotient.mk I)
  obtain ⟨a, ha, haI⟩ :=
    HenselianRing.is_henselian f hfmonic 1 hroot hderiv
  refine ⟨a, ?_, ?_⟩
  · have hzero : a ^ r.matrixRank - u = 0 := by
      simpa [f] using ha
    exact sub_eq_zero.mp hzero
  · have hz : PowerSeries.constantCoeff (a - 1) = 0 :=
      PowerSeries.X_dvd_iff.mp (Ideal.mem_span_singleton.mp haI)
    have hz' : PowerSeries.constantCoeff a - 1 = 0 := by
      simpa using hz
    exact sub_eq_zero.mp hz'

/-- The Hensel-selected matrix-rank root preserves every finite jet on
which its target is already equal to one.  The geometric-series factor is
a unit because its constant coefficient is the nonzero matrix rank. -/
theorem powerSeries_root_finite_coeff_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (a u : PowerSeries (ResidueField P r level)) (n : Nat)
    (haPow : a ^ r.matrixRank = u)
    (haConst : PowerSeries.constantCoeff a = 1)
    (hu : ∀ k < n,
      PowerSeries.coeff k u = PowerSeries.coeff k 1) :
    ∀ k < n, PowerSeries.coeff k a = PowerSeries.coeff k 1 := by
  let geom : PowerSeries (ResidueField P r level) :=
    ∑ i ∈ Finset.range r.matrixRank, a ^ i
  have hgeomUnit : IsUnit geom := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    simp [geom, haConst, matrixRank_cast_ne_zero_residueField P r level]
  have hpowDvd : (PowerSeries.X :
      PowerSeries (ResidueField P r level)) ^ n ∣ a ^ r.matrixRank - 1 := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [haPow]
    have hkEq := hu k hk
    simpa using sub_eq_zero.mpr hkEq
  have hfactor : geom * (a - 1) = a ^ r.matrixRank - 1 := by
    simpa [geom] using
      ((Commute.one_right a).geom_sum₂_mul r.matrixRank)
  have hgeomDvd : (PowerSeries.X :
      PowerSeries (ResidueField P r level)) ^ n ∣ geom * (a - 1) := by
    rw [hfactor]
    exact hpowDvd
  have haDvd : (PowerSeries.X :
      PowerSeries (ResidueField P r level)) ^ n ∣ a - 1 :=
    hgeomUnit.dvd_mul_left.mp hgeomDvd
  rw [PowerSeries.X_pow_dvd_iff] at haDvd
  intro k hk
  have hz := haDvd k hk
  have hsub : PowerSeries.coeff k a - PowerSeries.coeff k 1 = 0 := by
    simpa using hz
  exact sub_eq_zero.mp hsub

/-- Inversion preserves agreement with one through a finite power-series
jet, provided the series has constant coefficient one. -/
theorem powerSeries_inv_finite_coeff_eq_one
    {K : Type*} [Field K] (a : PowerSeries K) (n : Nat)
    (haConst : PowerSeries.constantCoeff a = 1)
    (ha : ∀ k < n,
      PowerSeries.coeff k a = PowerSeries.coeff k 1) :
    ∀ k < n, PowerSeries.coeff k a⁻¹ = PowerSeries.coeff k 1 := by
  have ha0 : PowerSeries.constantCoeff a ≠ 0 := by
    rw [haConst]
    exact one_ne_zero
  have hinv : a⁻¹ * a = 1 := PowerSeries.inv_mul_cancel a ha0
  have haDvd : (PowerSeries.X : PowerSeries K) ^ n ∣ a - 1 := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    have hkEq := ha k hk
    simpa using sub_eq_zero.mpr hkEq
  have hinvDvd : (PowerSeries.X : PowerSeries K) ^ n ∣ a⁻¹ - 1 := by
    obtain ⟨c, hc⟩ := haDvd
    refine ⟨-(a⁻¹ * c), ?_⟩
    calc
      a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by
        rw [mul_sub, hinv, mul_one]
        ring
      _ = (PowerSeries.X : PowerSeries K) ^ n * (-(a⁻¹ * c)) := by
        rw [hc]
        ring
  rw [PowerSeries.X_pow_dvd_iff] at hinvDvd
  intro k hk
  have hz := hinvDvd k hk
  have hsub : PowerSeries.coeff k a⁻¹ - PowerSeries.coeff k 1 = 0 := by
    simpa using hz
  exact sub_eq_zero.mp hsub

/-- Taylor expansion at the selected finite-place value of `y`.  The formal
parameter `X` is the local uniformizer. -/
noncomputable def indexCompletedPolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r →+*
      PowerSeries (ResidueField P r level) :=
  Polynomial.eval₂RingHom
    ((PowerSeries.C : ResidueField P r level →+*
      PowerSeries (ResidueField P r level)).comp
        (indexConstantEmbedding P r level).toRingHom)
    (PowerSeries.C (indexPlaceY P r level) + PowerSeries.X)

private theorem powerSeries_coeff_one_polynomial_eval_C_add_X
    {R K : Type*} [CommSemiring R] [Field K]
    (f : Polynomial R) (φ : R →+* K) (y : K) :
    PowerSeries.coeff 1
        (Polynomial.eval₂ (PowerSeries.C.comp φ)
          (PowerSeries.C y + PowerSeries.X) f) =
      f.derivative.eval₂ φ y := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [Polynomial.eval₂_monomial, PowerSeries.coeff_one_pow,
        Polynomial.derivative_monomial, mul_assoc]

/-- The selected closed-point polynomial after extension to the cyclic
constant field. -/
noncomputable def indexCompletedUniformizerPolynomial
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantPolynomialRing P r :=
  (indexPlacePolynomial P r level).map
    (algebraMap (BaseField P) (ConstantExtension P r))

/-- Image of the selected closed-point polynomial in its completed local
ring.  It is a genuine uniformizer up to a unit. -/
noncomputable def indexCompletedUniformizer
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries (ResidueField P r level) :=
  indexCompletedPolynomialEval P r level
    (indexCompletedUniformizerPolynomial P r level)

@[simp] theorem indexCompletedPolynomialEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    PowerSeries.constantCoeff
        (indexCompletedPolynomialEval P r level f) =
      indexConstantPolynomialEval P r level f := by
  change PowerSeries.constantCoeff
      (Polynomial.eval₂
        ((PowerSeries.C : ResidueField P r level →+*
          PowerSeries (ResidueField P r level)).comp
            (indexConstantEmbedding P r level).toRingHom)
        (PowerSeries.C (indexPlaceY P r level) + PowerSeries.X) f) =
    Polynomial.eval₂ (indexConstantEmbedding P r level).toRingHom
      (indexPlaceY P r level) f
  have hc : PowerSeries.constantCoeff.comp
        ((PowerSeries.C : ResidueField P r level →+*
          PowerSeries (ResidueField P r level)).comp
            (indexConstantEmbedding P r level).toRingHom) =
      (indexConstantEmbedding P r level).toRingHom := by
    ext c
    simp
  rw [Polynomial.hom_eval₂, hc]
  simp

@[simp] theorem indexCompletedUniformizer_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries.constantCoeff (indexCompletedUniformizer P r level) = 0 := by
  rw [indexCompletedUniformizer,
    indexCompletedPolynomialEval_constantCoeff,
    indexCompletedUniformizerPolynomial,
    indexConstantPolynomialEval_map_base]
  exact minpoly.aeval (BaseField P) (indexPlaceY P r level)

theorem indexCompletedUniformizer_coeff_one_ne_zero
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries.coeff 1 (indexCompletedUniformizer P r level) ≠ 0 := by
  rw [indexCompletedUniformizer, indexCompletedPolynomialEval,
    indexCompletedUniformizerPolynomial]
  change PowerSeries.coeff 1
      (Polynomial.eval₂
        (PowerSeries.C.comp
          (indexConstantEmbedding P r level).toRingHom)
        (PowerSeries.C (indexPlaceY P r level) + PowerSeries.X)
        ((indexPlacePolynomial P r level).map
          (algebraMap (BaseField P) (ConstantExtension P r)))) ≠ 0
  rw [powerSeries_coeff_one_polynomial_eval_C_add_X,
    Polynomial.derivative_map, Polynomial.eval₂_map]
  have hcomp :
      (indexConstantEmbedding P r level).toRingHom.comp
          (algebraMap (BaseField P) (ConstantExtension P r)) =
        algebraMap (BaseField P) (ResidueField P r level) := by
    ext a
    exact (indexConstantEmbedding P r level).commutes a
  rw [hcomp]
  exact (Algebra.IsSeparable.isSeparable (BaseField P)
      (indexPlaceY P r level)).aeval_derivative_ne_zero
    (minpoly.aeval (BaseField P) (indexPlaceY P r level))

/-- Unit factor left after removing the one simple zero of the selected
closed-point polynomial in completed coordinates. -/
noncomputable def indexCompletedUniformizerUnitFactor
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries (ResidueField P r level) :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1) (indexCompletedUniformizer P r level)

@[simp] theorem indexCompletedUniformizerUnitFactor_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat) :
    PowerSeries.constantCoeff
        (indexCompletedUniformizerUnitFactor P r level) =
      PowerSeries.coeff 1 (indexCompletedUniformizer P r level) := by
  simp [indexCompletedUniformizerUnitFactor]

theorem indexCompletedUniformizerUnitFactor_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexCompletedUniformizerUnitFactor P r level) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedUniformizerUnitFactor_constantCoeff,
    isUnit_iff_ne_zero]
  exact indexCompletedUniformizer_coeff_one_ne_zero P r level

theorem indexCompletedUniformizer_eq_X_mul_unitFactor
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedUniformizer P r level =
      PowerSeries.X * indexCompletedUniformizerUnitFactor P r level := by
  simpa [indexCompletedUniformizerUnitFactor,
    indexCompletedUniformizer_constantCoeff] using
      PowerSeries.eq_X_mul_shift_add_const
        (indexCompletedUniformizer P r level)

theorem indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow
    (P : BasePrime) (r : Rank) (level n : Nat) :
    indexCompletedUniformizer P r level ^ n =
      PowerSeries.X ^ n *
        indexCompletedUniformizerUnitFactor P r level ^ n := by
  rw [indexCompletedUniformizer_eq_X_mul_unitFactor, mul_pow]

theorem indexCompletedUniformizer_pow_coeff_self_ne_zero
    (P : BasePrime) (r : Rank) (level n : Nat) :
    PowerSeries.coeff n (indexCompletedUniformizer P r level ^ n) ≠ 0 := by
  rw [indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow]
  have hcoeff := PowerSeries.coeff_X_pow_mul
    (indexCompletedUniformizerUnitFactor P r level ^ n) n 0
  have heq : PowerSeries.coeff n
        (PowerSeries.X ^ n *
          indexCompletedUniformizerUnitFactor P r level ^ n) =
      PowerSeries.constantCoeff
        (indexCompletedUniformizerUnitFactor P r level ^ n) := by
    simpa using hcoeff
  rw [heq, map_pow,
    indexCompletedUniformizerUnitFactor_constantCoeff]
  exact pow_ne_zero n
    (indexCompletedUniformizer_coeff_one_ne_zero P r level)

theorem coeff_mul_indexCompletedUniformizer_pow_eq_zero_of_lt
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : PowerSeries (ResidueField P r level)) {k n : Nat} (hkn : k < n) :
    PowerSeries.coeff k
        (A * indexCompletedUniformizer P r level ^ n) = 0 := by
  rw [indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow]
  rw [← mul_assoc, mul_comm A (PowerSeries.X ^ n), mul_assoc,
    PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hkn]

theorem coeff_mul_indexCompletedUniformizer_pow_self
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : PowerSeries (ResidueField P r level)) (n : Nat) :
    PowerSeries.coeff n
        (A * indexCompletedUniformizer P r level ^ n) =
      PowerSeries.constantCoeff A *
        PowerSeries.coeff n (indexCompletedUniformizer P r level ^ n) := by
  rw [indexCompletedUniformizer_pow_eq_X_pow_mul_unitFactor_pow]
  rw [← mul_assoc, mul_comm A (PowerSeries.X ^ n), mul_assoc,
    PowerSeries.coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    indexCompletedUniformizerUnitFactor_constantCoeff]
  have hcoeff := PowerSeries.coeff_X_pow_mul
    (indexCompletedUniformizerUnitFactor P r level ^ n) n 0
  have heq : PowerSeries.coeff n
        (PowerSeries.X ^ n *
          indexCompletedUniformizerUnitFactor P r level ^ n) =
      PowerSeries.coeff 1 (indexCompletedUniformizer P r level) ^ n := by
    calc
      _ = PowerSeries.constantCoeff
          (indexCompletedUniformizerUnitFactor P r level ^ n) := by
            simpa using hcoeff
      _ = _ := by simp
  rw [heq]

/-- Chosen polynomial representative of a residue-field scalar.  This uses
the already proved surjectivity of evaluation at the selected closed point. -/
noncomputable def indexConstantPolynomialCoefficientLift
    (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level → ConstantPolynomialRing P r :=
  Function.surjInv (indexConstantPolynomialEval_surjective P r level)

@[simp] theorem indexConstantPolynomialCoefficientLift_eval
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ResidueField P r level) :
    indexConstantPolynomialEval P r level
        (indexConstantPolynomialCoefficientLift P r level a) = a :=
  Function.surjInv_eq
    (indexConstantPolynomialEval_surjective P r level) a

/-- Every finite coefficient jet in the selected complete local coefficient
ring has a polynomial lift.  The induction corrects one coefficient at a
time with a power of the construction-owned closed-point uniformizer. -/
theorem exists_indexCompletedPolynomialEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ f : ConstantPolynomialRing P r, ∀ k < n,
      PowerSeries.coeff k (indexCompletedPolynomialEval P r level f) =
        PowerSeries.coeff k s := by
  induction n with
  | zero =>
      exact ⟨0, by intro k hk; omega⟩
  | succ n ih =>
      obtain ⟨f, hf⟩ := ih
      let c : ResidueField P r level :=
        PowerSeries.coeff n (indexCompletedUniformizer P r level ^ n)
      have hc : c ≠ 0 := by
        exact indexCompletedUniformizer_pow_coeff_self_ne_zero P r level n
      let e : ResidueField P r level :=
        PowerSeries.coeff n s -
          PowerSeries.coeff n (indexCompletedPolynomialEval P r level f)
      let a : ConstantPolynomialRing P r :=
        indexConstantPolynomialCoefficientLift P r level (e * c⁻¹)
      let g : ConstantPolynomialRing P r :=
        f + a * indexCompletedUniformizerPolynomial P r level ^ n
      refine ⟨g, ?_⟩
      intro k hk
      have hkle : k < n ∨ k = n := Nat.lt_succ_iff_lt_or_eq.mp hk
      rcases hkle with hkn | hkeq
      · dsimp only [g]
        rw [map_add, map_mul, map_pow]
        change PowerSeries.coeff k
            (indexCompletedPolynomialEval P r level f +
              indexCompletedPolynomialEval P r level a *
                indexCompletedUniformizer P r level ^ n) = _
        rw [map_add,
          coeff_mul_indexCompletedUniformizer_pow_eq_zero_of_lt
            P r level _ hkn,
          add_zero, hf k hkn]
      · subst k
        dsimp only [g]
        rw [map_add, map_mul, map_pow]
        change PowerSeries.coeff n
            (indexCompletedPolynomialEval P r level f +
              indexCompletedPolynomialEval P r level a *
                indexCompletedUniformizer P r level ^ n) = _
        rw [map_add,
          coeff_mul_indexCompletedUniformizer_pow_self P r level]
        have ha : PowerSeries.constantCoeff
            (indexCompletedPolynomialEval P r level a) = e * c⁻¹ := by
          rw [indexCompletedPolynomialEval_constantCoeff]
          exact indexConstantPolynomialCoefficientLift_eval
            P r level (e * c⁻¹)
        rw [ha]
        change PowerSeries.coeff n
              (indexCompletedPolynomialEval P r level f) +
            (e * c⁻¹) * c = PowerSeries.coeff n s
        have hcancel : (e * c⁻¹) * c = e := by
          field_simp
        rw [hcancel]
        dsimp only [e]
        ring

theorem indexCompletedPolynomialEval_denominator_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexCompletedPolynomialEval P r level
      (Polynomial.X * (1 + Polynomial.X))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    indexCompletedPolynomialEval_constantCoeff]
  exact indexConstantPolynomialEval_denominator_isUnit P r level

/-- The construction's coefficient ring embedded in the completed local ring
at the selected congruence place. -/
noncomputable def indexCompletedArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ConstantArithmeticRing P r →+*
      PowerSeries (ResidueField P r level) :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r)
    (S := ConstantArithmeticRing P r)
    (g := indexCompletedPolynomialEval P r level)
    (indexCompletedPolynomialEval_denominator_isUnit P r level)

@[simp] theorem indexCompletedArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : ConstantPolynomialRing P r) :
    indexCompletedArithmeticEval P r level
        (algebraMap (ConstantPolynomialRing P r)
          (ConstantArithmeticRing P r) f) =
      indexCompletedPolynomialEval P r level f := by
  exact IsLocalization.Away.lift_eq _ _ _

@[simp] theorem indexCompletedArithmeticEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ConstantArithmeticRing P r) :
    PowerSeries.constantCoeff
        (indexCompletedArithmeticEval P r level a) =
      indexConstantArithmeticEval P r level a := by
  have heq :
      PowerSeries.constantCoeff.comp
          (indexCompletedArithmeticEval P r level) =
        indexConstantArithmeticEval P r level := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers
        (Polynomial.X * (1 + Polynomial.X) : ConstantPolynomialRing P r))
    ext f
    · change PowerSeries.constantCoeff
          (indexCompletedArithmeticEval P r level
            (algebraMap (ConstantPolynomialRing P r)
              (ConstantArithmeticRing P r) (Polynomial.C f))) =
        indexConstantArithmeticEval P r level
          (algebraMap (ConstantPolynomialRing P r)
            (ConstantArithmeticRing P r) (Polynomial.C f))
      rw [indexCompletedArithmeticEval_algebraMap,
        indexConstantArithmeticEval_algebraMap,
        indexCompletedPolynomialEval_constantCoeff]
    · change PowerSeries.constantCoeff
          (indexCompletedArithmeticEval P r level
            (algebraMap (ConstantPolynomialRing P r)
              (ConstantArithmeticRing P r) Polynomial.X)) =
        indexConstantArithmeticEval P r level
          (algebraMap (ConstantPolynomialRing P r)
            (ConstantArithmeticRing P r) Polynomial.X)
      rw [indexCompletedArithmeticEval_algebraMap,
        indexConstantArithmeticEval_algebraMap,
        indexCompletedPolynomialEval_constantCoeff]
  exact DFunLike.congr_fun heq a

/-- Completed evaluation of the base arithmetic polynomial ring, before
localization. -/
noncomputable def indexCompletedBasePolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P →+* PowerSeries (ResidueField P r level) :=
  (indexCompletedPolynomialEval P r level).comp
    (Polynomial.mapRingHom
      (algebraMap (BaseField P) (ConstantExtension P r)))

@[simp] theorem indexCompletedBasePolynomialEval_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    PowerSeries.constantCoeff
        (indexCompletedBasePolynomialEval P r level f) =
      indexPolynomialEval P r level f := by
  rw [indexCompletedBasePolynomialEval, RingHom.comp_apply,
    indexCompletedPolynomialEval_constantCoeff]
  change indexConstantPolynomialEval P r level
      (Polynomial.map
        (algebraMap (BaseField P) (ConstantExtension P r)) f) = _
  exact indexConstantPolynomialEval_map_base P r level f

@[simp] theorem indexCompletedBasePolynomialEval_indexPlacePolynomial
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCompletedBasePolynomialEval P r level
        (indexPlacePolynomial P r level) =
      indexCompletedUniformizer P r level := by
  rfl

noncomputable def indexBasePolynomialCoefficientLift
    (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level → PolynomialRing P :=
  Function.surjInv (indexPolynomialEval_surjective P r level)

@[simp] theorem indexBasePolynomialCoefficientLift_eval
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : ResidueField P r level) :
    indexPolynomialEval P r level
        (indexBasePolynomialCoefficientLift P r level a) = a :=
  Function.surjInv_eq (indexPolynomialEval_surjective P r level) a

/-- Base-field polynomial version of selected-place finite-jet lifting. -/
theorem exists_indexCompletedBasePolynomialEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ f : PolynomialRing P, ∀ k < n,
      PowerSeries.coeff k (indexCompletedBasePolynomialEval P r level f) =
        PowerSeries.coeff k s := by
  induction n with
  | zero => exact ⟨0, by intro k hk; omega⟩
  | succ n ih =>
      obtain ⟨f, hf⟩ := ih
      let c := PowerSeries.coeff n
        (indexCompletedUniformizer P r level ^ n)
      have hc : c ≠ 0 :=
        indexCompletedUniformizer_pow_coeff_self_ne_zero P r level n
      let e := PowerSeries.coeff n s -
        PowerSeries.coeff n (indexCompletedBasePolynomialEval P r level f)
      let a := indexBasePolynomialCoefficientLift P r level (e * c⁻¹)
      let g := f + a * indexPlacePolynomial P r level ^ n
      refine ⟨g, ?_⟩
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | hkeq
      · dsimp only [g]
        rw [map_add, map_mul, map_pow,
          indexCompletedBasePolynomialEval_indexPlacePolynomial,
          map_add,
          coeff_mul_indexCompletedUniformizer_pow_eq_zero_of_lt
            P r level _ hkn,
          add_zero, hf k hkn]
      · subst k
        dsimp only [g]
        rw [map_add, map_mul, map_pow,
          indexCompletedBasePolynomialEval_indexPlacePolynomial,
          map_add,
          coeff_mul_indexCompletedUniformizer_pow_self P r level]
        have ha : PowerSeries.constantCoeff
            (indexCompletedBasePolynomialEval P r level a) = e * c⁻¹ := by
          rw [indexCompletedBasePolynomialEval_constantCoeff]
          exact indexBasePolynomialCoefficientLift_eval P r level (e * c⁻¹)
        rw [ha]
        change PowerSeries.coeff n
              (indexCompletedBasePolynomialEval P r level f) +
            (e * c⁻¹) * c = PowerSeries.coeff n s
        have hcancel : (e * c⁻¹) * c = e := by field_simp
        rw [hcancel]
        dsimp only [e]
        ring

/-- Completion map on the base arithmetic ring. -/
noncomputable def indexCompletedBaseArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P →+* PowerSeries (ResidueField P r level) :=
  (indexCompletedArithmeticEval P r level).comp
    (arithmeticToConstantArithmetic P r)

@[simp] theorem indexCompletedBaseArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat) (f : PolynomialRing P) :
    indexCompletedBaseArithmeticEval P r level
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      indexCompletedBasePolynomialEval P r level f := by
  rw [indexCompletedBaseArithmeticEval, RingHom.comp_apply,
    arithmeticToConstantArithmetic_algebraMap,
    indexCompletedArithmeticEval_algebraMap]
  rfl

theorem exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ a : ArithmeticRing P, ∀ k < n,
      PowerSeries.coeff k (indexCompletedBaseArithmeticEval P r level a) =
        PowerSeries.coeff k s := by
  obtain ⟨f, hf⟩ :=
    exists_indexCompletedBasePolynomialEval_finite_coeff_lift P r level s n
  refine ⟨algebraMap (PolynomialRing P) (ArithmeticRing P) f, ?_⟩
  intro k hk
  rw [indexCompletedBaseArithmeticEval_algebraMap]
  exact hf k hk

/-- The localized arithmetic coefficient ring realizes every finite jet in
the selected completion. -/
theorem exists_indexCompletedArithmeticEval_finite_coeff_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ a : ConstantArithmeticRing P r, ∀ k < n,
      PowerSeries.coeff k (indexCompletedArithmeticEval P r level a) =
        PowerSeries.coeff k s := by
  obtain ⟨f, hf⟩ :=
    exists_indexCompletedPolynomialEval_finite_coeff_lift P r level s n
  refine ⟨algebraMap (ConstantPolynomialRing P r)
    (ConstantArithmeticRing P r) f, ?_⟩
  intro k hk
  rw [indexCompletedArithmeticEval_algebraMap]
  exact hf k hk

/-- Completed local image of an integral cyclic basis vector. -/
noncomputable def completedIndexCyclicBasisVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexCyclicBasisVector P r p).map
    (indexCompletedArithmeticEval P r level)

@[simp] theorem completedIndexCyclicBasisVector_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (completedIndexCyclicBasisVector P r level p).map
        PowerSeries.constantCoeff =
      indexCyclicBasisVector P r level p := by
  ext i j
  change PowerSeries.constantCoeff
      (indexCompletedArithmeticEval P r level
        (orderIndexCyclicBasisVector P r p i j)) = _
  rw [indexCompletedArithmeticEval_constantCoeff]
  exact congrFun (congrFun
    (orderIndexCyclicBasisVector_reduction P r level p) i) j

theorem completedIndexCyclicBasisVector_det_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit ((Matrix.stdBasis (PowerSeries (ResidueField P r level))
      (Fin r.matrixRank) (Fin r.matrixRank)).det
        (completedIndexCyclicBasisVector P r level)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hmap : PowerSeries.constantCoeff
      ((Matrix.stdBasis (PowerSeries (ResidueField P r level))
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (completedIndexCyclicBasisVector P r level)) =
      (Matrix.stdBasis (ResidueField P r level)
        (Fin r.matrixRank) (Fin r.matrixRank)).det
          (indexCyclicBasisVector P r level) := by
    simp only [Module.Basis.det_apply]
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro p q
    change PowerSeries.constantCoeff
        (completedIndexCyclicBasisVector P r level q p.1 p.2) =
      indexCyclicBasisVector P r level q p.1 p.2
    exact congrFun (congrFun
      (completedIndexCyclicBasisVector_reduction P r level q) p.1) p.2
  rw [hmap]
  let hli := indexCyclicBasisVector_linearIndependent P r level
  exact (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (ResidueField P r level)
      (Fin r.matrixRank) (Fin r.matrixRank))).mp
        ⟨hli, hli.span_eq_top_of_card_eq_finrank
          (by simp [Module.finrank_matrix])⟩

/-- The completed cyclic family as an actual basis of the local split matrix
algebra. -/
noncomputable def completedIndexCyclicBasis
    (P : BasePrime) (r : Rank) (level : Nat) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) := by
  let hbasis := (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (PowerSeries (ResidueField P r level))
      (Fin r.matrixRank) (Fin r.matrixRank))).mpr
        (completedIndexCyclicBasisVector_det_isUnit P r level)
  exact Module.Basis.mk hbasis.1 hbasis.2.ge

@[simp] theorem completedIndexCyclicBasis_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    completedIndexCyclicBasis P r level p =
      completedIndexCyclicBasisVector P r level p := by
  simp [completedIndexCyclicBasis]

private theorem powerSeries_coeff_mul_eq_of_left_finite_coeff_eq
    {K : Type*} [CommSemiring K] {a b c : PowerSeries K} {n k : Nat}
    (hab : ∀ i < n, PowerSeries.coeff i a = PowerSeries.coeff i b)
    (hk : k < n) :
    PowerSeries.coeff k (a * c) = PowerSeries.coeff k (b * c) := by
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hab ij.1]
  have hijsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  omega

private theorem powerSeries_coeff_mul_eq_of_finite_coeff_eq
    {K : Type*} [CommSemiring K] {a b c d : PowerSeries K} {n k : Nat}
    (hab : ∀ i < n, PowerSeries.coeff i a = PowerSeries.coeff i b)
    (hcd : ∀ i < n, PowerSeries.coeff i c = PowerSeries.coeff i d)
    (hk : k < n) :
    PowerSeries.coeff k (a * c) = PowerSeries.coeff k (b * d) := by
  calc
    PowerSeries.coeff k (a * c) = PowerSeries.coeff k (b * c) :=
      powerSeries_coeff_mul_eq_of_left_finite_coeff_eq hab hk
    _ = PowerSeries.coeff k (c * b) := by rw [mul_comm]
    _ = PowerSeries.coeff k (d * b) :=
      powerSeries_coeff_mul_eq_of_left_finite_coeff_eq hcd hk
    _ = PowerSeries.coeff k (b * d) := by rw [mul_comm]

private theorem powerSeries_coeff_prod_eq_of_finite_coeff_eq
    {K ι : Type*} [CommSemiring K] [DecidableEq ι]
    {f g : ι → PowerSeries K} {s : Finset ι} {n k : Nat}
    (hfg : ∀ i ∈ s, ∀ m < n,
      PowerSeries.coeff m (f i) = PowerSeries.coeff m (g i))
    (hk : k < n) :
    PowerSeries.coeff k (∏ i ∈ s, f i) =
      PowerSeries.coeff k (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply powerSeries_coeff_mul_eq_of_finite_coeff_eq
      · exact hfg a (Finset.mem_insert_self a s)
      · intro m hm
        apply ih
        · intro i hi
          exact hfg i (Finset.mem_insert_of_mem hi)
        · exact hm
      · exact hk

/-- Determinant coefficients through order `n` depend only on the matrix
entry coefficients through order `n`. -/
private theorem powerSeries_coeff_det_eq_of_finite_coeff_eq
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (PowerSeries K)} {n k : Nat}
    (hAB : ∀ i j, ∀ m < n,
      PowerSeries.coeff m (A i j) = PowerSeries.coeff m (B i j))
    (hk : k < n) :
    PowerSeries.coeff k (Matrix.det A) =
      PowerSeries.coeff k (Matrix.det B) := by
  rw [Matrix.det_apply', Matrix.det_apply']
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : ∀ m < n,
      PowerSeries.coeff m (∏ i, A (σ i) i) =
        PowerSeries.coeff m (∏ i, B (σ i) i) := by
    intro m hm
    apply powerSeries_coeff_prod_eq_of_finite_coeff_eq
    · intro i _ j hj
      exact hAB (σ i) i j hj
    · exact hm
  calc
    PowerSeries.coeff k
        (((Equiv.Perm.sign σ : ℤ) : PowerSeries K) * ∏ i, A (σ i) i) =
      PowerSeries.coeff k
        ((∏ i, A (σ i) i) *
          ((Equiv.Perm.sign σ : ℤ) : PowerSeries K)) := by
          rw [mul_comm]
    _ = PowerSeries.coeff k
        ((∏ i, B (σ i) i) *
          ((Equiv.Perm.sign σ : ℤ) : PowerSeries K)) :=
      powerSeries_coeff_mul_eq_of_left_finite_coeff_eq hprod hk
    _ = PowerSeries.coeff k
        (((Equiv.Perm.sign σ : ℤ) : PowerSeries K) * ∏ i, B (σ i) i) := by
          rw [mul_comm]

/-- Arithmetic lift of one completed cyclic-basis coefficient through a
specified jet order. -/
noncomputable def indexCompletedCyclicCoefficientArithmeticLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (p : Fin r.matrixRank × Fin r.matrixRank) :
    ArithmeticRing P :=
  Classical.choose (exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
    P r level ((completedIndexCyclicBasis P r level).repr M p) n)

theorem indexCompletedCyclicCoefficientArithmeticLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (p : Fin r.matrixRank × Fin r.matrixRank)
    (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (indexCompletedBaseArithmeticEval P r level
          (indexCompletedCyclicCoefficientArithmeticLift
            P r level M n p)) =
      PowerSeries.coeff k
        ((completedIndexCyclicBasis P r level).repr M p) :=
  Classical.choose_spec
    (exists_indexCompletedBaseArithmeticEval_finite_coeff_lift
      P r level ((completedIndexCyclicBasis P r level).repr M p) n) k hk

/-- Arithmetic cyclic-order matrix matching a prescribed completed local
matrix through the first `n` coefficients. -/
noncomputable def orderIndexMatrixFiniteJetLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ∑ p : Fin r.matrixRank × Fin r.matrixRank,
    arithmeticToConstantArithmetic P r
        (indexCompletedCyclicCoefficientArithmeticLift P r level M n p) •
      orderIndexCyclicBasisVector P r p

theorem orderIndexMatrixFiniteJetLift_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    (orderIndexMatrixFiniteJetLift P r level M n).map
        (indexCompletedArithmeticEval P r level) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        indexCompletedBaseArithmeticEval P r level
            (indexCompletedCyclicCoefficientArithmeticLift
              P r level M n p) •
          completedIndexCyclicBasisVector P r level p := by
  rw [orderIndexMatrixFiniteJetLift]
  ext i j k
  simp [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    completedIndexCyclicBasisVector, smul_eq_mul,
    indexCompletedBaseArithmeticEval]

theorem orderIndexMatrixFiniteJetLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (((orderIndexMatrixFiniteJetLift P r level M n).map
          (indexCompletedArithmeticEval P r level)) i j) =
      PowerSeries.coeff k (M i j) := by
  rw [orderIndexMatrixFiniteJetLift_completed]
  calc
    PowerSeries.coeff k
        ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          indexCompletedBaseArithmeticEval P r level
              (indexCompletedCyclicCoefficientArithmeticLift
                P r level M n p) •
            completedIndexCyclicBasisVector P r level p) i j) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        PowerSeries.coeff k
          (indexCompletedBaseArithmeticEval P r level
              (indexCompletedCyclicCoefficientArithmeticLift
                P r level M n p) *
            completedIndexCyclicBasisVector P r level p i j) := by
              simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ = ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        PowerSeries.coeff k
          ((completedIndexCyclicBasis P r level).repr M p *
            completedIndexCyclicBasisVector P r level p i j) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply powerSeries_coeff_mul_eq_of_left_finite_coeff_eq
                (n := n) (hk := hk)
              intro m hm
              exact indexCompletedCyclicCoefficientArithmeticLift_coeff
                P r level M n p m hm
    _ = PowerSeries.coeff k (M i j) := by
      have hrepr := congrArg
        (fun A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level)) ↦
          PowerSeries.coeff k (A i j))
        ((completedIndexCyclicBasis P r level).sum_repr M)
      simpa [Matrix.sum_apply, Matrix.smul_apply,
        completedIndexCyclicBasis_apply, smul_eq_mul] using hrepr

/-- The arithmetic cyclic-order lift also matches the determinant of the
prescribed completed matrix through the selected finite jet. -/
theorem orderIndexMatrixFiniteJetLift_det_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (Matrix.det
          ((orderIndexMatrixFiniteJetLift P r level M n).map
            (indexCompletedArithmeticEval P r level))) =
      PowerSeries.coeff k (Matrix.det M) := by
  apply powerSeries_coeff_det_eq_of_finite_coeff_eq
  · intro i j m hm
    exact orderIndexMatrixFiniteJetLift_coeff P r level M n i j m hm
  · exact hk

/-- In particular, when the target completed matrix has determinant one,
the global arithmetic-order lift has reduced norm congruent to one through
every requested coefficient.  The remaining strong-approximation problem
is to make this congruence an exact global norm equation while preserving
the jet. -/
theorem orderIndexMatrixFiniteJetLift_special_det_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (Matrix.det
          ((orderIndexMatrixFiniteJetLift P r level
              (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) n).map
            (indexCompletedArithmeticEval P r level))) =
      PowerSeries.coeff k 1 := by
  rw [orderIndexMatrixFiniteJetLift_det_coeff P r level _ n k hk,
    s.property]

theorem orderIndexMatrixFiniteJetLift_to_global_mem_order
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    (orderIndexMatrixFiniteJetLift P r level M n).map
        (constantArithmeticToSplittingFunctionField P r) ∈
      CartwrightStegerOrder P r := by
  rw [orderIndexMatrixFiniteJetLift]
  have hmapSum :
      ((∑ p : Fin r.matrixRank × Fin r.matrixRank,
          arithmeticToConstantArithmetic P r
              (indexCompletedCyclicCoefficientArithmeticLift P r level M n p) •
            orderIndexCyclicBasisVector P r p).map
        (constantArithmeticToSplittingFunctionField P r)) =
      ∑ p : Fin r.matrixRank × Fin r.matrixRank,
        (arithmeticToConstantArithmetic P r
            (indexCompletedCyclicCoefficientArithmeticLift P r level M n p) •
          orderIndexCyclicBasisVector P r p).map
            (constantArithmeticToSplittingFunctionField P r) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]
  rw [hmapSum]
  apply (CartwrightStegerOrder P r).sum_mem
  intro p hp
  rw [Matrix.map_smul' _ _ _ (map_mul _),
    orderIndexCyclicBasisVector_to_global,
    constantArithmeticToSplittingFunctionField_arithmeticBaseChange]
  have hmem := (CartwrightStegerOrder P r).smul_mem
    (splittingCyclicBasisVector_mem_order P r p)
    (indexCompletedCyclicCoefficientArithmeticLift P r level M n p)
  change arithmeticRingToSplitMatrix P r
    (indexCompletedCyclicCoefficientArithmeticLift P r level M n p) *
      splittingCyclicBasisVector P r p ∈ CartwrightStegerOrder P r at hmem
  simpa only [arithmeticRingToSplitMatrix, RingHom.comp_apply,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] using hmem

/-- Combined finite-jet approximation inside the genuine arithmetic order.
For every completed special-linear point and every precision, this produces
one global order matrix whose entries match the point and whose reduced norm
matches one to the same precision.  No global invertibility or exact norm-one
claim is hidden in this statement. -/
theorem exists_orderMatrix_finiteJetLift_special
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    ∃ A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      A.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r ∧
      (∀ (i j : Fin r.matrixRank) (k : Nat), k < n →
        PowerSeries.coeff k
            ((A.map (indexCompletedArithmeticEval P r level)) i j) =
          PowerSeries.coeff k
            (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) :
              Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) i j)) ∧
      (∀ k : Nat, k < n →
        PowerSeries.coeff k
            (Matrix.det
              (A.map (indexCompletedArithmeticEval P r level))) =
          PowerSeries.coeff k 1) := by
  let A := orderIndexMatrixFiniteJetLift P r level
    (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) n
  refine ⟨A, ?_, ?_, ?_⟩
  · exact orderIndexMatrixFiniteJetLift_to_global_mem_order
      P r level _ n
  · intro i j k hk
    exact orderIndexMatrixFiniteJetLift_coeff P r level _ n i j k hk
  · intro k hk
    exact orderIndexMatrixFiniteJetLift_special_det_coeff
      P r level s n k hk

/-- Hensel root of the determinant of the global arithmetic-order
finite-jet lift.  A positive jet precision guarantees constant coefficient
one, so the construction-owned matrix-rank root theorem applies. -/
noncomputable def orderIndexFiniteJetDetRoot
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    PowerSeries (ResidueField P r level) :=
  Classical.choose
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level
      (Matrix.det
        ((orderIndexMatrixFiniteJetLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) n).map
          (indexCompletedArithmeticEval P r level))) (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simpa using
          (orderIndexMatrixFiniteJetLift_special_det_coeff
            P r level s n 0 hn)))

theorem orderIndexFiniteJetDetRoot_pow
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    orderIndexFiniteJetDetRoot P r level s n hn ^ r.matrixRank =
      Matrix.det
        ((orderIndexMatrixFiniteJetLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) n).map
          (indexCompletedArithmeticEval P r level)) :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _ (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simpa using
          (orderIndexMatrixFiniteJetLift_special_det_coeff
            P r level s n 0 hn)))).1

theorem orderIndexFiniteJetDetRoot_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    PowerSeries.constantCoeff
        (orderIndexFiniteJetDetRoot P r level s n hn) = 1 :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _ (by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simpa using
          (orderIndexMatrixFiniteJetLift_special_det_coeff
            P r level s n 0 hn)))).2

/-- The determinant-correcting Hensel root itself is invisible in every
coefficient below the requested precision. -/
theorem orderIndexFiniteJetDetRoot_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (orderIndexFiniteJetDetRoot P r level s n hn) =
      PowerSeries.coeff k 1 := by
  apply powerSeries_root_finite_coeff_eq_one P r level
      (orderIndexFiniteJetDetRoot P r level s n hn)
      (Matrix.det
        ((orderIndexMatrixFiniteJetLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) n).map
          (indexCompletedArithmeticEval P r level))) n
  · exact orderIndexFiniteJetDetRoot_pow P r level s n hn
  · exact orderIndexFiniteJetDetRoot_constantCoeff P r level s n hn
  · intro m hm
    exact orderIndexMatrixFiniteJetLift_special_det_coeff
      P r level s n m hm
  · exact hk

/-- Local determinant correction of the arithmetic-order finite-jet lift.
The scalar is constructed internally by Hensel lifting. -/
noncomputable def orderIndexFiniteJetNormOneCompletedLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexFiniteJetDetRoot P r level s n hn)⁻¹ •
    (orderIndexMatrixFiniteJetLift P r level
      (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) n).map
      (indexCompletedArithmeticEval P r level)

theorem orderIndexFiniteJetNormOneCompletedLift_det
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    Matrix.det (orderIndexFiniteJetNormOneCompletedLift
      P r level s n hn) = 1 := by
  rw [orderIndexFiniteJetNormOneCompletedLift, Matrix.det_smul,
    Fintype.card_fin, ← orderIndexFiniteJetDetRoot_pow P r level s n hn,
    ← mul_pow]
  have hinv := PowerSeries.inv_mul_cancel
    (orderIndexFiniteJetDetRoot P r level s n hn)
    (by
      rw [orderIndexFiniteJetDetRoot_constantCoeff P r level s n hn]
      exact one_ne_zero)
  exact (congrArg (fun x : PowerSeries (ResidueField P r level) =>
    x ^ r.matrixRank) hinv).trans (one_pow r.matrixRank)

/-- The local determinant correction does not alter any matrix coefficient
below the requested jet precision. -/
theorem orderIndexFiniteJetNormOneCompletedLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n)
    (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (orderIndexFiniteJetNormOneCompletedLift P r level s n hn i j) =
      PowerSeries.coeff k
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) := by
  rw [orderIndexFiniteJetNormOneCompletedLift, Matrix.smul_apply,
    smul_eq_mul]
  calc
    _ = PowerSeries.coeff k
        (1 * (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j)) := by
      apply powerSeries_coeff_mul_eq_of_finite_coeff_eq
      · exact powerSeries_inv_finite_coeff_eq_one
          (orderIndexFiniteJetDetRoot P r level s n hn) n
          (orderIndexFiniteJetDetRoot_constantCoeff P r level s n hn)
          (fun m hm => orderIndexFiniteJetDetRoot_coeff
            P r level s n hn m hm)
      · intro m hm
        exact orderIndexMatrixFiniteJetLift_coeff P r level _ n i j m hm
      · exact hk
    _ = _ := by rw [one_mul]

/-- The corrected finite-jet lift as an actual completed special-linear
point. -/
noncomputable def orderIndexFiniteJetNormOneCompletedLiftSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  ⟨orderIndexFiniteJetNormOneCompletedLift P r level s n hn,
    orderIndexFiniteJetNormOneCompletedLift_det P r level s n hn⟩

/-- The split-coordinate ring cut out by descent to the genuine
Cartwright--Steger arithmetic order. -/
noncomputable def OrderCyclicMatrixCoordinateRing
    (P : BasePrime) (r : Rank) :
    Subring (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  (CartwrightStegerOrder P r).toSubring.comap
    (constantArithmeticToSplittingFunctionField P r).mapMatrix

@[simp] theorem mem_OrderCyclicMatrixCoordinateRing_iff
    (P : BasePrime) (r : Rank)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :
    A ∈ OrderCyclicMatrixCoordinateRing P r ↔
      A.map (constantArithmeticToSplittingFunctionField P r) ∈
        CartwrightStegerOrder P r := by
  rfl

/-- Additive coordinates of the genuine arithmetic order. -/
noncomputable def OrderCyclicMatrixCoordinates
    (P : BasePrime) (r : Rank) :
    AddSubgroup (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) :=
  (OrderCyclicMatrixCoordinateRing P r).toAddSubgroup

/-- Reduction of the genuine descended cyclic-coordinate ring at the
selected congruence place. -/
noncomputable def orderCyclicMatrixCoordinateReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinateRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) :=
  (indexConstantArithmeticEval P r level).mapMatrix.comp
    (OrderCyclicMatrixCoordinateRing P r).subtype

/-- Every finite matrix has a lift in the actual descended cyclic order.
This is ring-level lifting; promotion of an invertible finite matrix to a
global order unit is the separate strong-approximation step. -/
theorem orderCyclicMatrixCoordinateReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (orderCyclicMatrixCoordinateReduction P r level) := by
  intro A
  let lift : OrderCyclicMatrixCoordinateRing P r :=
    ⟨orderIndexMatrixLift P r level A,
      orderIndexMatrixLift_to_global_mem_order P r level A⟩
  refine ⟨lift, ?_⟩
  change (orderIndexMatrixLift P r level A).map
      (indexConstantArithmeticEval P r level) = A
  exact orderIndexMatrixLift_reduction P r level A

/-- Completed evaluation on the genuine descended cyclic-coordinate ring. -/
noncomputable def orderCyclicMatrixCoordinateRingToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinateRing P r →+*
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) :=
  (indexCompletedArithmeticEval P r level).mapMatrix.comp
    (OrderCyclicMatrixCoordinateRing P r).subtype

/-- Selected completion map on actual arithmetic-order matrix coordinates. -/
noncomputable def orderCyclicMatrixCoordinatesToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinates P r →+
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) :=
  (indexCompletedArithmeticEval P r level).mapMatrix.toAddMonoidHom.comp
    (OrderCyclicMatrixCoordinates P r).subtype

theorem span_completedIndexCyclicBasisVector_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule.span (PowerSeries (ResidueField P r level))
      (Set.range (completedIndexCyclicBasisVector P r level)) = ⊤ := by
  have hbasis := (Module.Basis.is_basis_iff_det
    (Matrix.stdBasis (PowerSeries (ResidueField P r level))
      (Fin r.matrixRank) (Fin r.matrixRank))).mpr
        (completedIndexCyclicBasisVector_det_isUnit P r level)
  exact hbasis.2

/-- The completed cyclic order generated by the selected integral cyclic
basis. -/
noncomputable def IndexCompletedCyclicOrder
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subalgebra (PowerSeries (ResidueField P r level))
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :=
  Algebra.adjoin (PowerSeries (ResidueField P r level))
    (Set.range (completedIndexCyclicBasisVector P r level))

theorem IndexCompletedCyclicOrder_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedCyclicOrder P r level = ⊤ := by
  apply top_unique
  intro A hA
  have hspan : A ∈ Submodule.span
      (PowerSeries (ResidueField P r level))
      (Set.range (completedIndexCyclicBasisVector P r level)) := by
    rw [span_completedIndexCyclicBasisVector_eq_top]
    exact Submodule.mem_top
  change A ∈ (IndexCompletedCyclicOrder P r level).toSubmodule
  refine Submodule.span_le.mpr ?_ hspan
  rintro _ ⟨p, rfl⟩
  exact Algebra.subset_adjoin ⟨p, rfl⟩

/-- Cyclic-order matrix lift in the explicitly completed selected local
coefficient ring. -/
noncomputable def orderIndexMatrixCompletedLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexMatrixLift P r level A).map
    (indexCompletedArithmeticEval P r level)

theorem orderIndexMatrixCompletedLift_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level)) :
    (orderIndexMatrixCompletedLift P r level A).map
        PowerSeries.constantCoeff = A := by
  ext i j
  change PowerSeries.constantCoeff
      (indexCompletedArithmeticEval P r level
        (orderIndexMatrixLift P r level A i j)) = A i j
  rw [indexCompletedArithmeticEval_constantCoeff]
  exact congrFun (congrFun
    (orderIndexMatrixLift_reduction P r level A) i) j

theorem orderIndexMatrixCompletedLift_special_det_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    PowerSeries.constantCoeff
        (Matrix.det (orderIndexMatrixCompletedLift P r level
          (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ResidueField P r level)))) = 1 := by
  calc
    _ = Matrix.det ((orderIndexMatrixCompletedLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))).map PowerSeries.constantCoeff) := by
      simpa only [RingHom.mapMatrix_apply] using
        RingHom.map_det PowerSeries.constantCoeff
          (orderIndexMatrixCompletedLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ResidueField P r level)))
    _ = Matrix.det (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
      rw [orderIndexMatrixCompletedLift_reduction]
    _ = 1 := s.property

/-- Hensel-selected scalar root of the determinant of the local cyclic-order
lift. -/
noncomputable def orderIndexCompletedDetRoot
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    PowerSeries (ResidueField P r level) :=
  Classical.choose
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level
      (Matrix.det (orderIndexMatrixCompletedLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))))
      (orderIndexMatrixCompletedLift_special_det_constantCoeff P r level s))

theorem orderIndexCompletedDetRoot_pow
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    orderIndexCompletedDetRoot P r level s ^ r.matrixRank =
      Matrix.det (orderIndexMatrixCompletedLift P r level
        (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))) :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _
      (orderIndexMatrixCompletedLift_special_det_constantCoeff P r level s))).1

@[simp] theorem orderIndexCompletedDetRoot_constantCoeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    PowerSeries.constantCoeff
        (orderIndexCompletedDetRoot P r level s) = 1 :=
  (Classical.choose_spec
    (exists_powerSeries_pow_matrixRank_eq_of_constantCoeff_eq_one
      P r level _
      (orderIndexMatrixCompletedLift_special_det_constantCoeff P r level s))).2

theorem orderIndexCompletedDetRoot_isUnit
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IsUnit (orderIndexCompletedDetRoot P r level s) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The determinant-corrected local cyclic-order lift. -/
noncomputable def orderIndexNormOneCompletedLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  (orderIndexCompletedDetRoot P r level s)⁻¹ •
    orderIndexMatrixCompletedLift P r level s

theorem orderIndexNormOneCompletedLift_det
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.det (orderIndexNormOneCompletedLift P r level s) = 1 := by
  rw [orderIndexNormOneCompletedLift, Matrix.det_smul,
    Fintype.card_fin, ← orderIndexCompletedDetRoot_pow, ← mul_pow]
  have hinv : (orderIndexCompletedDetRoot P r level s)⁻¹ *
      orderIndexCompletedDetRoot P r level s = 1 :=
    PowerSeries.inv_mul_cancel _ (by
      rw [orderIndexCompletedDetRoot_constantCoeff]
      exact one_ne_zero)
  exact (congrArg (fun x : PowerSeries (ResidueField P r level) =>
    x ^ r.matrixRank) hinv).trans (one_pow r.matrixRank)

/-- The corrected lift is an actual special-linear point over the completed
selected local ring. -/
noncomputable def orderIndexNormOneCompletedLiftSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)) :=
  ⟨orderIndexNormOneCompletedLift P r level s,
    orderIndexNormOneCompletedLift_det P r level s⟩

theorem orderIndexNormOneCompletedLiftSL_reduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        PowerSeries.constantCoeff
        (orderIndexNormOneCompletedLiftSL P r level s) = s := by
  apply Subtype.ext
  change (orderIndexNormOneCompletedLift P r level s).map
      PowerSeries.constantCoeff =
    (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level))
  rw [orderIndexNormOneCompletedLift]
  rw [Matrix.map_smul' _ _ _ (map_mul _),
    PowerSeries.constantCoeff_inv,
    orderIndexCompletedDetRoot_constantCoeff,
    inv_one, one_smul,
    orderIndexMatrixCompletedLift_reduction]

/-- Norm-one units of the completed cyclic order in the selected split
coordinates.  Membership of both the matrix and inverse is recorded, just as
for the global arithmetic order. -/
noncomputable def IndexCompletedNormOneInnerForm
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) where
  carrier s :=
    ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level) ∧
    (((s⁻¹ : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level)
  one_mem' := by constructor <;> simp
  mul_mem' {a b} ha hb := by
    constructor
    · simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        (IndexCompletedCyclicOrder P r level).mul_mem ha.1 hb.1
    · simpa only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul] using
        (IndexCompletedCyclicOrder P r level).mul_mem hb.2 ha.2
  inv_mem' {a} ha := by
    constructor
    · exact ha.2
    · simpa only [inv_inv] using ha.1

/-- The arbitrary-precision corrected lift belongs to the genuine completed
norm-one cyclic order. -/
noncomputable def orderIndexFiniteJetNormOneCompletedInnerFormLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level)
    (n : Nat) (hn : 0 < n) :
    IndexCompletedNormOneInnerForm P r level := by
  refine ⟨orderIndexFiniteJetNormOneCompletedLiftSL P r level s n hn, ?_⟩
  constructor
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _

/-- Every completed norm-one point is matched to arbitrary precision by the
Hensel correction of an actual global arithmetic-order matrix.  The scalar
correction still lives in the completion; descending that correction to a
global norm-one unit is the remaining strong-approximation step. -/
theorem orderIndexFiniteJetNormOneCompletedInnerFormLift_coeff
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level)
    (n : Nat) (hn : 0 < n)
    (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (((orderIndexFiniteJetNormOneCompletedInnerFormLift
            P r level s n hn :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) =
      PowerSeries.coeff k
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) :=
  orderIndexFiniteJetNormOneCompletedLift_coeff
    P r level s n hn i j k hk

/-- Reduction of genuine completed norm-one cyclic-order points. -/
noncomputable def indexCompletedNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    PowerSeries.constantCoeff).comp
      (IndexCompletedNormOneInnerForm P r level).subtype

/-- The Hensel-corrected lift as a genuine point of the completed cyclic
order's norm-one group. -/
noncomputable def orderIndexNormOneCompletedInnerFormLift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    IndexCompletedNormOneInnerForm P r level := by
  refine ⟨orderIndexNormOneCompletedLiftSL P r level s, ?_⟩
  change
    (orderIndexNormOneCompletedLiftSL P r level s :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level ∧
    (((orderIndexNormOneCompletedLiftSL P r level s)⁻¹ :
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) ∈
        IndexCompletedCyclicOrder P r level
  constructor
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _
  · rw [IndexCompletedCyclicOrder_eq_top]
    exact Set.mem_univ _

theorem indexCompletedNormOneReduction_lift
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level)) :
    indexCompletedNormOneReduction P r level
        (orderIndexNormOneCompletedInnerFormLift P r level s) = s :=
  orderIndexNormOneCompletedLiftSL_reduction P r level s

/-- Construction-specialized local lifting: reduction of the actual
completed norm-one cyclic order is onto finite `SL` at every selected rank
and level. -/
theorem indexCompletedNormOneReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexCompletedNormOneReduction P r level) := by
  intro s
  exact ⟨orderIndexNormOneCompletedInnerFormLift P r level s,
    indexCompletedNormOneReduction_lift P r level s⟩

/-- Base change of a global norm-one inner-form point to the selected
completed local cyclic order. -/
noncomputable def orderNormOneInnerFormToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →*
      IndexCompletedNormOneInnerForm P r level where
  toFun s := by
    let t : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level)) :=
      Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (indexCompletedArithmeticEval P r level)
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))
    refine ⟨t, ?_⟩
    change
      (t : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) ∈
          IndexCompletedCyclicOrder P r level ∧
      (((t⁻¹ : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) ∈
          IndexCompletedCyclicOrder P r level)
    constructor
    · rw [IndexCompletedCyclicOrder_eq_top]
      exact Set.mem_univ _
    · rw [IndexCompletedCyclicOrder_eq_top]
      exact Set.mem_univ _
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' s t := by
    apply Subtype.ext
    exact map_mul
      (Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
        (indexCompletedArithmeticEval P r level))
      (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (t : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))

/-- Global coefficient reduction factors through the construction-owned
completed norm-one cyclic order. -/
theorem indexCompletedNormOneReduction_global_compatibility
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    indexCompletedNormOneReduction P r level
        (orderNormOneInnerFormToCompleted P r level s) =
      orderSpecialLinearReduction P r level
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Subtype.ext
  ext i j
  exact indexCompletedArithmeticEval_constantCoeff P r level
    ((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) i j)

/-- The global-to-finite norm-one reduction is exactly local completed
reduction after completed base change. -/
theorem orderNormOneInnerFormReduction_factor_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormReduction P r level s =
      specialLinearToPSL P r level
        (indexCompletedNormOneReduction P r level
          (orderNormOneInnerFormToCompleted P r level s)) := by
  rw [indexCompletedNormOneReduction_global_compatibility]
  rfl

/-- Exact remaining global approximation criterion: since completed local
norm-one reduction is already onto, global norm-one reduction is onto iff
the global completed image together with the local congruence kernel fills
the completed norm-one group. -/
theorem orderNormOneInnerForm_completed_surjective_iff_sup_ker_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
        ((indexCompletedNormOneReduction P r level).comp
          (orderNormOneInnerFormToCompleted P r level)) ↔
      (orderNormOneInnerFormToCompleted P r level).range ⊔
        (indexCompletedNormOneReduction P r level).ker = ⊤ := by
  constructor
  · intro hsurj
    apply top_unique
    intro x hx
    obtain ⟨g, hg⟩ := hsurj
      (indexCompletedNormOneReduction P r level x)
    have hk : (orderNormOneInnerFormToCompleted P r level g)⁻¹ * x ∈
        (indexCompletedNormOneReduction P r level).ker := by
      change indexCompletedNormOneReduction P r level
          (orderNormOneInnerFormToCompleted P r level g) =
        indexCompletedNormOneReduction P r level x at hg
      change indexCompletedNormOneReduction P r level
          ((orderNormOneInnerFormToCompleted P r level g)⁻¹ * x) = 1
      rw [map_mul, map_inv, hg]
      simp
    have himage : orderNormOneInnerFormToCompleted P r level g ∈
        (orderNormOneInnerFormToCompleted P r level).range :=
      ⟨g, rfl⟩
    have hmem := Subgroup.mul_mem_sup himage hk
    simpa using hmem
  · intro htop y
    obtain ⟨x, hx⟩ :=
      indexCompletedNormOneReduction_surjective P r level y
    have hmem : x ∈
        (orderNormOneInnerFormToCompleted P r level).range ⊔
          (indexCompletedNormOneReduction P r level).ker := by
      rw [htop]
      exact Subgroup.mem_top x
    obtain ⟨a, ha, k, hk, hak⟩ :=
      (Subgroup.mem_sup_of_normal_right).mp hmem
    obtain ⟨g, hga⟩ := ha
    refine ⟨g, ?_⟩
    have hkone : indexCompletedNormOneReduction P r level k = 1 := hk
    rw [← hx, ← hak, map_mul, hkone, mul_one, ← hga]
    rfl

/-- Principal congruence kernel of the completed norm-one cyclic order. -/
noncomputable def IndexCompletedNormOneCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexCompletedNormOneInnerForm P r level) :=
  (indexCompletedNormOneReduction P r level).ker

noncomputable instance indexCompletedNormOneCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCompletedNormOneCongruenceSubgroup P r level).Normal := by
  dsimp [IndexCompletedNormOneCongruenceSubgroup]
  infer_instance

/-- First isomorphism theorem for the selected completed local norm-one
cyclic order. -/
noncomputable def indexCompletedNormOneQuotientEquivSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ⧸
        IndexCompletedNormOneCongruenceSubgroup P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (indexCompletedNormOneReduction P r level)
    (indexCompletedNormOneReduction_surjective P r level)

/-- Projective reduction of the completed local norm-one cyclic order. -/
noncomputable def indexCompletedNormOneReductionToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level →* PSL P r level :=
  (specialLinearToPSL P r level).comp
    (indexCompletedNormOneReduction P r level)

theorem indexCompletedNormOneReductionToPSL_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (indexCompletedNormOneReductionToPSL P r level) := by
  intro y
  obtain ⟨s, rfl⟩ := specialLinearToPSL_surjective P r level y
  obtain ⟨x, hx⟩ := indexCompletedNormOneReduction_surjective P r level s
  exact ⟨x, by
    change specialLinearToPSL P r level
        (indexCompletedNormOneReduction P r level x) =
      specialLinearToPSL P r level s
    rw [hx]⟩

/-- Kernel presentation of the completed local projective norm-one
congruence quotient. -/
noncomputable def IndexCompletedProjectiveCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexCompletedNormOneInnerForm P r level) :=
  (indexCompletedNormOneReductionToPSL P r level).ker

noncomputable instance indexCompletedProjectiveCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCompletedProjectiveCongruenceSubgroup P r level).Normal := by
  dsimp [IndexCompletedProjectiveCongruenceSubgroup]
  infer_instance

noncomputable def indexCompletedProjectiveQuotientEquivPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCompletedNormOneInnerForm P r level ⧸
        IndexCompletedProjectiveCongruenceSubgroup P r level ≃*
      PSL P r level := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (indexCompletedNormOneReductionToPSL P r level)
    (indexCompletedNormOneReductionToPSL_surjective P r level)

/-! ## Topological bridge from global density to congruence surjectivity -/

section CompletedTopology

open scoped PowerSeries.WithPiTopology

variable (P : BasePrime) (r : Rank) (level : Nat)

local instance residueFieldDiscreteTopologicalSpace :
    TopologicalSpace (ResidueField P r level) := ⊥

local instance residueFieldDiscreteTopology :
    DiscreteTopology (ResidueField P r level) := ⟨rfl⟩

private theorem denseRange_powerSeries_of_finite_coeff_lifts
    {A K : Type*} [TopologicalSpace K] [CommSemiring K]
    (f : A → PowerSeries K)
    (hlift : ∀ (s : PowerSeries K) (n : Nat), ∃ a : A,
      ∀ k < n, PowerSeries.coeff k (f a) = PowerSeries.coeff k s) :
    DenseRange f := by
  intro s
  choose a ha using fun n ↦ hlift s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ f (a n))
    (b := (Filter.atTop : Filter Nat))
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) ↦
      ha n k hkn
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_range_self (a n)

/-- The actual localized arithmetic coefficient ring is dense in the
selected complete local coefficient ring. -/
theorem denseRange_indexCompletedArithmeticEval :
    DenseRange (indexCompletedArithmeticEval P r level) :=
  denseRange_powerSeries_of_finite_coeff_lifts
    (indexCompletedArithmeticEval P r level)
    (exists_indexCompletedArithmeticEval_finite_coeff_lift P r level)

/-- The construction-owned global cyclic order is dense, as an additive
matrix lattice, in its selected completed split matrix algebra. -/
theorem denseRange_orderIndexMatrixToCompleted :
    DenseRange (fun A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r) ↦
      A.map (indexCompletedArithmeticEval P r level)) := by
  intro M
  let A : Nat → Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
    fun n ↦ orderIndexMatrixFiniteJetLift P r level M n
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ (A n).map
      (indexCompletedArithmeticEval P r level))
    (b := (Filter.atTop : Filter Nat))
  · apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) ↦
      orderIndexMatrixFiniteJetLift_coeff P r level M n i j k hkn
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_range_self (A n)

/-- Actual arithmetic-order matrix coordinates are dense in the selected
completed split matrix algebra. -/
theorem denseRange_orderCyclicMatrixCoordinatesToCompleted :
    DenseRange (orderCyclicMatrixCoordinatesToCompleted P r level) := by
  intro M
  let A : Nat → OrderCyclicMatrixCoordinates P r := fun n ↦
    ⟨orderIndexMatrixFiniteJetLift P r level M n,
      orderIndexMatrixFiniteJetLift_to_global_mem_order P r level M n⟩
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ orderCyclicMatrixCoordinatesToCompleted
      P r level (A n))
    (b := (Filter.atTop : Filter Nat))
  · apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) ↦
      orderIndexMatrixFiniteJetLift_coeff P r level M n i j k hkn
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_range_self (A n)

/-- A coordinatewise finite-jet lifting theorem is enough to establish the
actual global density statement for the completed norm-one cyclic order. -/
private theorem denseRange_orderNormOneInnerFormToCompleted_of_finite_coeff_lifts
    (hlift : ∀ (s : IndexCompletedNormOneInnerForm P r level) (n : Nat),
      ∃ g : OrderNormOneInnerForm P r,
        ∀ (i j : Fin r.matrixRank) (k : Nat), k < n →
          PowerSeries.coeff k
              (((orderNormOneInnerFormToCompleted P r level g :
                Matrix.SpecialLinearGroup (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) :
                Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) i j) =
            PowerSeries.coeff k
              (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) :
                Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) i j)) :
    DenseRange (orderNormOneInnerFormToCompleted P r level) := by
  intro s
  choose g hg using fun n ↦ hlift s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ orderNormOneInnerFormToCompleted P r level (g n))
    (b := (Filter.atTop : Filter Nat))
  · rw [tendsto_subtype_rng]
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) ↦
      hg n i j k hkn
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_range_self (g n)

/-- Constant-coefficient reduction is continuous for the coefficientwise
topology on the selected completed norm-one cyclic order. -/
theorem continuous_indexCompletedNormOneReduction :
    Continuous (indexCompletedNormOneReduction P r level) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (PowerSeries.WithPiTopology.continuous_constantCoeff
    (ResidueField P r level)).comp
      ((continuous_apply j).comp
        ((continuous_apply i).comp
          ((show Continuous (fun s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level)) =>
                (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level)))) from continuous_subtype_val).comp
            continuous_subtype_val)))

/-- The principal local norm-one congruence subgroup is open in the actual
completed cyclic-order group. -/
theorem isOpen_indexCompletedNormOneCongruenceSubgroup :
    IsOpen (IndexCompletedNormOneCongruenceSubgroup P r level :
      Set (IndexCompletedNormOneInnerForm P r level)) := by
  change IsOpen {x |
    indexCompletedNormOneReduction P r level x = 1}
  exact (discreteTopology_iff_isOpen_singleton.mp inferInstance 1).preimage
    (continuous_indexCompletedNormOneReduction P r level)

private theorem range_sup_open_ker_eq_top_of_denseRange
    {A G H : Type*} [Group A] [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G]
    [Group H] (f : A →* G) (reduction : G →* H)
    (hdense : DenseRange f) (hopen : IsOpen (reduction.ker : Set G)) :
    f.range ⊔ reduction.ker = ⊤ := by
  apply top_unique
  intro x _
  let U : Set G := (fun k : G ↦ x * k) '' (reduction.ker : Set G)
  have hUopen : IsOpen U := isOpenMap_mul_left x _ hopen
  have hUne : U.Nonempty := ⟨x, ⟨1, Subgroup.one_mem _, mul_one x⟩⟩
  obtain ⟨y, hyU, hyRange⟩ :=
    (dense_iff_inter_open.mp hdense U hUopen hUne)
  obtain ⟨k, hk, rfl⟩ := hyU
  have hleft : x * k ∈ f.range ⊔ reduction.ker :=
    (le_sup_left : f.range ≤ f.range ⊔ reduction.ker) hyRange
  have hright : k⁻¹ ∈ f.range ⊔ reduction.ker :=
    (le_sup_right : reduction.ker ≤ f.range ⊔ reduction.ker)
      (reduction.ker.inv_mem hk)
  simpa using (f.range ⊔ reduction.ker).mul_mem hleft hright

/-- The precise topological implication used in the LSV proof: density of
the construction-owned global norm-one points in the selected completed
local norm-one group forces genuine finite `SL` reduction to be onto.  This
is an internal bridge; the density premise is proved separately from the
cyclic-algebra construction before the final exported surjectivity theorem. -/
private theorem orderNormOneInnerForm_completed_surjective_of_denseRange
    (hdense : DenseRange (orderNormOneInnerFormToCompleted P r level)) :
    Function.Surjective
      ((indexCompletedNormOneReduction P r level).comp
        (orderNormOneInnerFormToCompleted P r level)) := by
  rw [orderNormOneInnerForm_completed_surjective_iff_sup_ker_eq_top]
  exact range_sup_open_ker_eq_top_of_denseRange
    (orderNormOneInnerFormToCompleted P r level)
    (indexCompletedNormOneReduction P r level) hdense
    (isOpen_indexCompletedNormOneCongruenceSubgroup P r level)

/-- Construction-level strong approximation can now be discharged by the
finite-jet statement alone: compatible global norm-one lifts of every finite
matrix jet imply the required finite `SL` reduction surjectivity. -/
private theorem orderNormOneInnerForm_completed_surjective_of_finite_coeff_lifts
    (hlift : ∀ (s : IndexCompletedNormOneInnerForm P r level) (n : Nat),
      ∃ g : OrderNormOneInnerForm P r,
        ∀ (i j : Fin r.matrixRank) (k : Nat), k < n →
          PowerSeries.coeff k
              (((orderNormOneInnerFormToCompleted P r level g :
                Matrix.SpecialLinearGroup (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) :
                Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) i j) =
            PowerSeries.coeff k
              (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) :
                Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (PowerSeries (ResidueField P r level))) i j)) :
    Function.Surjective
      ((indexCompletedNormOneReduction P r level).comp
        (orderNormOneInnerFormToCompleted P r level)) :=
  orderNormOneInnerForm_completed_surjective_of_denseRange P r level
    (denseRange_orderNormOneInnerFormToCompleted_of_finite_coeff_lifts
      P r level hlift)

end CompletedTopology

theorem orderNormOneInnerFormToOrderUnits_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderNormOneInnerFormToOrderUnits P r) := by
  intro s t hst
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toGL_injective
  apply Units.ext
  ext i j
  apply constantArithmeticToSplittingFunctionField_injective P r
  have hval := congrArg (fun u : (CartwrightStegerOrder P r)ˣ =>
    (((u : CartwrightStegerOrder P r) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) i j)) hst
  exact hval

theorem orderNormOneInnerFormToActualNormOne_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderNormOneInnerFormToActualNormOne P r) := by
  intro s t hst
  apply orderNormOneInnerFormToOrderUnits_injective P r
  exact congrArg Subtype.val hst

/-! ## An explicit nonidentity element in the norm-one reduction -/

theorem orderSplitCartwrightStegerGeneratorGL_det
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup.det
        (orderSplitCartwrightStegerGeneratorGL P r u) =
      Matrix.GeneralLinearGroup.det (orderSplitBGL P r) := by
  simp [orderSplitCartwrightStegerGeneratorGL]

/-- Ratio of two integral Cartwright--Steger generators, bundled in the
special linear group before imposing the inner-form descent conditions. -/
noncomputable def orderSplitGeneratorRatioSpecial
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  ⟨(orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r u) *
    (orderSplitCartwrightStegerGeneratorGL P r
      (constantClassRepresentative P r v))⁻¹ :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)), by
    have hdet : Matrix.GeneralLinearGroup.det
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹) = 1 := by
      rw [map_mul, map_inv,
        orderSplitCartwrightStegerGeneratorGL_det,
        orderSplitCartwrightStegerGeneratorGL_det]
      simp
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg Units.val hdet⟩

theorem cartwrightStegerGenerator_matrix_mem_order
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    ((cartwrightStegerGenerator P r u :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r := by
  rw [← orderUnitToGlobalGL_generator P r u]
  exact (cartwrightStegerOrderUnitGenerator P r u).val.property

theorem cartwrightStegerGenerator_inverse_matrix_mem_order
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    (((cartwrightStegerGenerator P r u)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r := by
  rw [← orderUnitToGlobalGL_generator P r u, ← map_inv]
  exact ((cartwrightStegerOrderUnitGenerator P r u)⁻¹).val.property

theorem orderSplitGeneratorRatioSpecial_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    orderSplitGeneratorRatioSpecial P r u v ∈
      OrderNormOneInnerForm P r := by
  constructor
  · change (((orderSplitBaseChangeGLHom P r)
        (orderSplitCartwrightStegerGeneratorGL P r
            (constantClassRepresentative P r u) *
          (orderSplitCartwrightStegerGeneratorGL P r
            (constantClassRepresentative P r v))⁻¹) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
    rw [map_mul, map_inv,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact (CartwrightStegerOrder P r).mul_mem
      (cartwrightStegerGenerator_matrix_mem_order P r u)
      (cartwrightStegerGenerator_inverse_matrix_mem_order P r v)
  · have hto : Matrix.SpecialLinearGroup.toGL
        (orderSplitGeneratorRatioSpecial P r u v) =
      orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ := by
      apply Units.ext
      rfl
    rw [hto, mul_inv_rev, inv_inv, map_mul, map_inv,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact (CartwrightStegerOrder P r).mul_mem
      (cartwrightStegerGenerator_matrix_mem_order P r v)
      (cartwrightStegerGenerator_inverse_matrix_mem_order P r u)

/-- The explicit generator ratio as a genuine integral point of the
construction-owned norm-one inner form. -/
noncomputable def orderNormOneGeneratorRatio
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    OrderNormOneInnerForm P r :=
  ⟨orderSplitGeneratorRatioSpecial P r u v,
    orderSplitGeneratorRatioSpecial_mem_innerForm P r u v⟩

theorem orderNormOneInnerFormReduction_generatorRatio
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : ConstantProjectiveClass P r) :
    ((orderNormOneInnerFormReduction P r level
        (orderNormOneGeneratorRatio P r u v) : PSL P r level) :
      PGL P r level) =
      indexCartwrightStegerClassGenerator P r level u *
        (indexCartwrightStegerClassGenerator P r level v)⁻¹ := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL
        (orderSpecialLinearReduction P r level
          (orderSplitGeneratorRatioSpecial P r u v))) = _
  have hmap : Matrix.SpecialLinearGroup.toGL
      (orderSpecialLinearReduction P r level
        (orderSplitGeneratorRatioSpecial P r u v)) =
      Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (Matrix.SpecialLinearGroup.toGL
          (orderSplitGeneratorRatioSpecial P r u v)) := by
    apply Units.ext
    rfl
  have hto : Matrix.SpecialLinearGroup.toGL
        (orderSplitGeneratorRatioSpecial P r u v) =
      orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ := by
    apply Units.ext
    rfl
  rw [hmap, hto]
  change orderSplitReductionPGLHom P r level
      (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹) = _
  rw [map_mul, map_inv,
    orderSplitReductionPGLHom_classGenerator,
    orderSplitReductionPGLHom_classGenerator]

/-- Distinct construction-owned generators give a nonidentity element after
genuine global norm-one reduction. -/
theorem orderNormOneInnerFormReduction_generatorRatio_ne_one
    (P : BasePrime) (r : Rank) (level : Nat)
    {u v : ConstantProjectiveClass P r} (huv : u ≠ v) :
    orderNormOneInnerFormReduction P r level
        (orderNormOneGeneratorRatio P r u v) ≠ 1 := by
  intro hg
  have hprojective := congrArg (fun q : PSL P r level ↦
    (q : PGL P r level)) hg
  have hratio :
      indexCartwrightStegerClassGenerator P r level u *
          (indexCartwrightStegerClassGenerator P r level v)⁻¹ = 1 := by
    simpa [orderNormOneInnerFormReduction_generatorRatio] using hprojective
  have heq : indexCartwrightStegerClassGenerator P r level u =
      indexCartwrightStegerClassGenerator P r level v :=
    mul_inv_eq_one.mp hratio
  exact huv (indexCartwrightStegerClassGenerator_injective P r level heq)

/-- The genuine norm-one reduction has a construction-owned nonidentity
element, namely the ratio of two distinct Cartwright--Steger generators. -/
theorem exists_ne_one_mem_range_orderNormOneInnerFormReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PSL P r level,
      g ∈ (orderNormOneInnerFormReduction P r level).range ∧ g ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  let x := orderNormOneGeneratorRatio P r u v
  let g := orderNormOneInnerFormReduction P r level x
  refine ⟨g, ⟨x, rfl⟩, ?_⟩
  intro hg
  have hprojective := congrArg (fun q : PSL P r level =>
    (q : PGL P r level)) hg
  have hratio :
      indexCartwrightStegerClassGenerator P r level u *
          (indexCartwrightStegerClassGenerator P r level v)⁻¹ = 1 := by
    simpa [g, x,
      orderNormOneInnerFormReduction_generatorRatio] using hprojective
  have heq : indexCartwrightStegerClassGenerator P r level u =
      indexCartwrightStegerClassGenerator P r level v :=
    mul_inv_eq_one.mp hratio
  exact huv (indexCartwrightStegerClassGenerator_injective P r level heq)

/-- The actual finite image of the construction-owned norm-one inner-form
reduction. -/
noncomputable def IndexNormOneInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PSL P r level) :=
  (orderNormOneInnerFormReduction P r level).range

theorem IndexNormOneInnerFormImage_ne_bot
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneInnerFormImage P r level ≠ ⊥ := by
  obtain ⟨g, hg, hgne⟩ :=
    exists_ne_one_mem_range_orderNormOneInnerFormReduction P r level
  intro hbot
  have : g = 1 := by
    rw [← Subgroup.mem_bot, ← hbot]
    exact hg
  exact hgne this

/-! ## The explicit generator-ratio core of strong approximation -/

/-- Reductions of the explicit global norm-one ratios.  Unlike the full
norm-one image, this set is presented solely by the original
Cartwright--Steger generators. -/
def indexNormOneGeneratorRatioSet
    (P : BasePrime) (r : Rank) (level : Nat) : Set (PSL P r level) :=
  {g | ∃ u v : ConstantProjectiveClass P r,
    g = orderNormOneInnerFormReduction P r level
      (orderNormOneGeneratorRatio P r u v)}

/-- The subgroup generated by the explicit global norm-one ratios. -/
noncomputable def IndexNormOneGeneratorRatioSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PSL P r level) :=
  Subgroup.closure (indexNormOneGeneratorRatioSet P r level)

theorem orderNormOneInnerFormReduction_generatorRatio_mem_subgroup
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : ConstantProjectiveClass P r) :
    orderNormOneInnerFormReduction P r level
        (orderNormOneGeneratorRatio P r u v) ∈
      IndexNormOneGeneratorRatioSubgroup P r level := by
  apply Subgroup.subset_closure
  exact ⟨u, v, rfl⟩

/-- Every element generated by explicit ratios belongs to the genuine
global norm-one reduction image. -/
theorem IndexNormOneGeneratorRatioSubgroup_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneGeneratorRatioSubgroup P r level ≤
      IndexNormOneInnerFormImage P r level := by
  rw [IndexNormOneGeneratorRatioSubgroup]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, rfl⟩
  exact ⟨orderNormOneGeneratorRatio P r u v, rfl⟩

/-- The explicit generator-ratio subgroup is already nontrivial at every
selected rank and level. -/
theorem IndexNormOneGeneratorRatioSubgroup_ne_bot
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneGeneratorRatioSubgroup P r level ≠ ⊥ := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  intro hbot
  have hmem := orderNormOneInnerFormReduction_generatorRatio_mem_subgroup
    P r level u v
  rw [hbot, Subgroup.mem_bot] at hmem
  exact orderNormOneInnerFormReduction_generatorRatio_ne_one
    P r level huv hmem

/-- The normal closure of the explicit global norm-one generator ratios is
the whole finite `PSL`.  Hence the remaining construction-specific global
step is conjugation stability of this concrete subgroup, not generation of
new nonidentity witnesses or another simplicity argument. -/
theorem normalClosure_IndexNormOneGeneratorRatioSubgroup_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup.normalClosure
        (IndexNormOneGeneratorRatioSubgroup P r level :
          Set (PSL P r level)) = ⊤ := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
  intro hbot
  apply IndexNormOneGeneratorRatioSubgroup_ne_bot P r level
  apply le_antisymm
  · intro g hg
    have hclosure : g ∈ Subgroup.normalClosure
        (IndexNormOneGeneratorRatioSubgroup P r level :
          Set (PSL P r level)) :=
      Subgroup.subset_normalClosure hg
    rw [hbot, Subgroup.mem_bot] at hclosure
    exact hclosure
  · exact bot_le

/-- Simplicity and the explicit generator ratio already imply that the
normal closure of the genuine norm-one reduction image is all of finite
`PSL`.  Thus the remaining strong-approximation content is precisely
conjugation stability of this actual image, not nontriviality or simplicity. -/
theorem normalClosure_IndexNormOneInnerFormImage_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup.normalClosure
        (IndexNormOneInnerFormImage P r level : Set (PSL P r level)) = ⊤ := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
  intro hbot
  apply IndexNormOneInnerFormImage_ne_bot P r level
  apply le_antisymm
  · intro g hg
    have hclosure : g ∈ Subgroup.normalClosure
        (IndexNormOneInnerFormImage P r level : Set (PSL P r level)) :=
      Subgroup.subset_normalClosure hg
    rw [hbot, Subgroup.mem_bot] at hclosure
    exact hclosure
  · exact bot_le

/-! ## Full inner-form image and normality of its norm-one part -/

/-- Integral points of the full construction-owned inner form in the same
split coordinates.  As above, descent of both the matrix and its inverse is
part of the definition. -/
noncomputable def OrderInnerFormUnits
    (P : BasePrime) (r : Rank) :
    Subgroup (Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) where
  carrier g :=
    ((orderSplitBaseChangeGLHom P r g :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r ∧
    ((orderSplitBaseChangeGLHom P r g⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
  one_mem' := by
    constructor <;> simp
  mul_mem' {a b} ha hb := by
    constructor
    · simpa only [map_mul, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem ha.1 hb.1
    · simpa only [mul_inv_rev, map_mul, Units.val_mul] using
        (CartwrightStegerOrder P r).mul_mem hb.2 ha.2
  inv_mem' {a} ha := by
    constructor
    · exact ha.2
    · simpa only [inv_inv] using ha.1

/-- A unit of the descended cyclic-coordinate ring is exactly a unit of the
full construction-owned inner form. -/
noncomputable def orderCyclicMatrixCoordinateUnitsEquivInnerForm
    (P : BasePrime) (r : Rank) :
    (OrderCyclicMatrixCoordinateRing P r)ˣ ≃*
      OrderInnerFormUnits P r where
  toFun u := by
    let g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
      Units.map (OrderCyclicMatrixCoordinateRing P r).subtype u
    refine ⟨g, ?_⟩
    constructor
    · change ((u : OrderCyclicMatrixCoordinateRing P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r) ∈
        CartwrightStegerOrder P r
      exact (u : OrderCyclicMatrixCoordinateRing P r).property
    · change (((u⁻¹ : (OrderCyclicMatrixCoordinateRing P r)ˣ) :
          OrderCyclicMatrixCoordinateRing P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r) ∈
        CartwrightStegerOrder P r
      exact ((u⁻¹ : (OrderCyclicMatrixCoordinateRing P r)ˣ) :
        OrderCyclicMatrixCoordinateRing P r).property
  invFun g :=
    { val := ⟨((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)), g.property.1⟩
      inv := ⟨(((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))⁻¹) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ConstantArithmeticRing P r)), by
        rw [mem_OrderCyclicMatrixCoordinateRing_iff]
        rw [← Matrix.GeneralLinearGroup.coe_inv]
        exact g.property.2⟩
      val_inv := by
        apply Subtype.ext
        change ((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) *
          (((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ConstantArithmeticRing P r))⁻¹) = 1
        exact Matrix.mul_nonsing_inv _
          (Matrix.isUnits_det_units (g : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (ConstantArithmeticRing P r)))
      inv_val := by
        apply Subtype.ext
        change (((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r))⁻¹) *
          ((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (ConstantArithmeticRing P r)) = 1
        exact Matrix.nonsing_inv_mul _
          (Matrix.isUnits_det_units (g : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (ConstantArithmeticRing P r))) }
  left_inv u := by
    apply Units.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' u v := by
    apply Subtype.ext
    apply Units.ext
    rfl

/-- Reduced norm on units of the genuine descended cyclic-coordinate ring. -/
noncomputable def orderCyclicMatrixCoordinateReducedNorm
    (P : BasePrime) (r : Rank) :
    (OrderCyclicMatrixCoordinateRing P r)ˣ →*
      (ConstantArithmeticRing P r)ˣ :=
  (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r) →*
        (ConstantArithmeticRing P r)ˣ).comp
    (Units.map (OrderCyclicMatrixCoordinateRing P r).subtype)

@[simp] theorem orderCyclicMatrixCoordinateUnitsEquivInnerForm_reducedNorm
    (P : BasePrime) (r : Rank)
    (u : (OrderCyclicMatrixCoordinateRing P r)ˣ) :
    Matrix.GeneralLinearGroup.det
        ((orderCyclicMatrixCoordinateUnitsEquivInnerForm P r u :
          OrderInnerFormUnits P r) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) =
      orderCyclicMatrixCoordinateReducedNorm P r u := by
  rfl

/-- Norm-one units of the genuine descended cyclic-coordinate ring. -/
noncomputable def OrderCyclicMatrixCoordinateNormOneUnits
    (P : BasePrime) (r : Rank) :
    Subgroup ((OrderCyclicMatrixCoordinateRing P r)ˣ) :=
  (orderCyclicMatrixCoordinateReducedNorm P r).ker

/-- Reduction on units of the genuine descended cyclic-coordinate ring. -/
noncomputable def orderCyclicMatrixCoordinateUnitReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderCyclicMatrixCoordinateRing P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Units.map (orderCyclicMatrixCoordinateReduction P r level)

/-- A full descended split-coordinate point gives an actual unit of the
Cartwright--Steger arithmetic order. -/
noncomputable def orderInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderInnerFormUnits P r →* (CartwrightStegerOrder P r)ˣ where
  toFun g :=
    { val := ⟨(orderSplitBaseChangeGLHom P r
          (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), g.property.1⟩
      inv := ⟨(orderSplitBaseChangeGLHom P r
          ((g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))⁻¹) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)), g.property.2⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Units.ext
    apply Subtype.ext
    simp

theorem orderUnitToGlobalGL_orderInnerFormToOrderUnits
    (P : BasePrime) (r : Rank) (g : OrderInnerFormUnits P r) :
    orderUnitToGlobalGL P r (orderInnerFormToOrderUnits P r g) =
      orderSplitBaseChangeGLHom P r
        (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)) := by
  apply Units.ext
  rfl

/-- Every class-indexed integral Cartwright--Steger generator is an actual
point of the full descended inner form. -/
theorem orderSplitCartwrightStegerClassGeneratorGL_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) ∈
      OrderInnerFormUnits P r := by
  constructor
  · change (((orderSplitBaseChangeGLHom P r)
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) ∈ CartwrightStegerOrder P r
    rw [map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact cartwrightStegerGenerator_matrix_mem_order P r u
  · rw [map_inv,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global]
    exact cartwrightStegerGenerator_inverse_matrix_mem_order P r u

theorem OrderSplitCartwrightStegerLattice_le_innerForm
    (P : BasePrime) (r : Rank) :
    OrderSplitCartwrightStegerLattice P r ≤ OrderInnerFormUnits P r := by
  rw [OrderSplitCartwrightStegerLattice]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, rfl⟩
  exact orderSplitCartwrightStegerClassGeneratorGL_mem_innerForm P r u

/-- The integral Cartwright--Steger lattice as a subgroup of the full actual
inner-form group. -/
noncomputable def OrderInnerFormCartwrightStegerLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (OrderInnerFormUnits P r) :=
  (OrderSplitCartwrightStegerLattice P r).comap
    (OrderInnerFormUnits P r).subtype

theorem map_OrderInnerFormCartwrightStegerLattice_subtype
    (P : BasePrime) (r : Rank) :
    (OrderInnerFormCartwrightStegerLattice P r).map
        (OrderInnerFormUnits P r).subtype =
      OrderSplitCartwrightStegerLattice P r := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    exact hx
  · intro g hg
    exact ⟨⟨g, OrderSplitCartwrightStegerLattice_le_innerForm P r hg⟩,
      hg, rfl⟩

/-- Norm-one points as a genuine kernel inside the full inner-form group. -/
noncomputable def OrderInnerFormNormOne
    (P : BasePrime) (r : Rank) :
    Subgroup (OrderInnerFormUnits P r) :=
  ((Matrix.GeneralLinearGroup.det).comp
    (OrderInnerFormUnits P r).subtype).ker

noncomputable instance orderInnerFormNormOneNormal
    (P : BasePrime) (r : Rank) :
    (OrderInnerFormNormOne P r).Normal := by
  dsimp [OrderInnerFormNormOne]
  infer_instance

/-- Projective reduction of all integral points of the inner form. -/
noncomputable def orderInnerFormReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormUnits P r →* PGL P r level :=
  (orderSplitReductionPGLHom P r level).comp
    (OrderInnerFormUnits P r).subtype

/-- The actual finite projective image of all descended inner-form points. -/
noncomputable def IndexInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (orderInnerFormReduction P r level).range

/-- The finite reduction of the Cartwright--Steger lattice, viewed inside the
full descended inner form, is exactly the construction's selected finite
Cartwright--Steger image. -/
theorem map_OrderInnerFormCartwrightStegerLattice
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderInnerFormCartwrightStegerLattice P r).map
        (orderInnerFormReduction P r level) =
      IndexCartwrightStegerImage P r level := by
  apply le_antisymm
  · rintro y ⟨g, hg, rfl⟩
    rw [← map_OrderSplitCartwrightStegerLattice P r level]
    refine ⟨(g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r)), ?_, rfl⟩
    rw [← map_OrderInnerFormCartwrightStegerLattice_subtype P r]
    exact ⟨g, hg, rfl⟩
  · intro y hy
    rw [← map_OrderSplitCartwrightStegerLattice P r level] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    have hinner : g ∈ OrderInnerFormUnits P r :=
      OrderSplitCartwrightStegerLattice_le_innerForm P r hg
    exact ⟨⟨g, hinner⟩, hg, rfl⟩

/-- Integral constant points used by the vertex stabilizer are genuine
points of the descended inner form. -/
theorem orderSplitConstantGL_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    orderSplitConstantGLHom P r u ∈ OrderInnerFormUnits P r := by
  constructor
  · rw [map_orderSplitConstantGL_to_global]
    exact constantMatrix_mem_cartwrightStegerOrder P r u
  · rw [map_inv, map_orderSplitConstantGL_to_global]
    rw [constantUnitMatrix_inv, constantUnitMatrix_val]
    exact constantMatrix_mem_cartwrightStegerOrder P r
      ((u⁻¹ : (ConstantExtension P r)ˣ) : ConstantExtension P r)

/-- The integral cyclic point used by the vertex stabilizer is a genuine
point of the descended inner form. -/
theorem orderSplitCyclicGeneratorGL_mem_innerForm
    (P : BasePrime) (r : Rank) :
    orderSplitCyclicGeneratorGL P r ∈ OrderInnerFormUnits P r := by
  constructor
  · rw [map_orderSplitCyclicGeneratorGL_to_global]
    exact cyclicGeneratorMatrix_mem_cartwrightStegerOrder P r
  · rw [map_inv, map_orderSplitCyclicGeneratorGL_to_global]
    exact cyclicGeneratorInverseMatrix_mem_cartwrightStegerOrder P r

/-- Every explicitly represented finite stabilizer element is the reduction
of an actual descended inner-form point. -/
theorem IndexCartwrightStegerStabilizer_le_IndexInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      IndexInnerFormImage P r level := by
  rw [IndexCartwrightStegerStabilizer]
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | hg)
  · obtain ⟨u, rfl⟩ := hg
    refine ⟨⟨orderSplitConstantGLHom P r u,
      orderSplitConstantGL_mem_innerForm P r u⟩, ?_⟩
    change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitConstantGLHom P r u)) = _
    rw [map_orderSplitConstantGL]
    rfl
  · rw [Set.mem_singleton_iff] at hg
    subst g
    refine ⟨⟨orderSplitCyclicGeneratorGL P r,
      orderSplitCyclicGeneratorGL_mem_innerForm P r⟩, ?_⟩
    change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitCyclicGeneratorGL P r)) = _
    rw [map_orderSplitCyclicGeneratorGL]

/-- The explicit finite Cartwright--Steger ambient group embeds into the
actual finite reduction image of the full descended inner form. -/
theorem IndexCartwrightStegerAmbient_le_IndexInnerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerAmbient P r level ≤
      IndexInnerFormImage P r level := by
  rw [IndexCartwrightStegerAmbient,
    IndexCartwrightStegerUnitImage_eq_image]
  exact sup_le
    (IndexCartwrightStegerStabilizer_le_IndexInnerFormImage P r level)
    (by
      rw [← map_OrderInnerFormCartwrightStegerLattice P r level,
        IndexInnerFormImage]
      exact (OrderInnerFormCartwrightStegerLattice P r).map_le_range
        (orderInnerFormReduction P r level))

/-- Projective equality after the injective global base change already forces
equality after every selected finite projective reduction.  The proof
descends the scalar relating the two global matrices from an actual entry of
their integral quotient; it does not assume a projective localization
principle. -/
theorem orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (A B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r))
    (hglobal : Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r A) =
      Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r B)) :
    orderSplitReductionPGLHom P r level A =
      orderSplitReductionPGLHom P r level B := by
  let C : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) := A⁻¹ * B
  have hCprojective : Matrix.ProjGenLinGroup.mk
      (orderSplitBaseChangeGLHom P r C) = 1 := by
    dsimp [C]
    rw [map_mul, map_inv, map_mul, map_inv, hglobal]
    simp
  obtain ⟨c, hc⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq hCprojective
  have hc' : orderSplitBaseChangeGLHom P r C =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) c := by
    simpa using hc
  let i0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  let a : ConstantArithmeticRing P r :=
    (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r)) i0 i0
  have hentry (i j : Fin r.matrixRank) :
      constantArithmeticToSplittingFunctionField P r
          ((C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) i j) =
        Matrix.scalar (Fin r.matrixRank)
          (c : SplittingFunctionField P r) i j := by
    have hmat := congrArg Units.val hc'
    have hij := congrFun (congrFun hmat i) j
    exact hij
  have ha : constantArithmeticToSplittingFunctionField P r a =
      (c : SplittingFunctionField P r) := by
    have h := hentry i0 i0
    simpa [a, Matrix.scalar_apply] using h
  have hCscalar :
      (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) =
      Matrix.scalar (Fin r.matrixRank) a := by
    ext i j
    apply constantArithmeticToSplittingFunctionField_injective P r
    rw [hentry, Matrix.scalar_apply]
    by_cases hij : i = j
    · subst j
      simp [ha]
    · simp [hij]
  have hcenter : orderSplitReductionGLHom P r level C ∈
      Subgroup.center
        (Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ResidueField P r level)) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨indexConstantArithmeticEval P r level a, ?_⟩
    change Matrix.scalar (Fin r.matrixRank)
        (indexConstantArithmeticEval P r level a) =
      (C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
        (indexConstantArithmeticEval P r level)
    rw [hCscalar]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  apply QuotientGroup.eq.mpr
  change (orderSplitReductionGLHom P r level A)⁻¹ *
      orderSplitReductionGLHom P r level B ∈
    Subgroup.center
      (Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level))
  simpa [C] using hcenter

/-- The integral split-coordinate lift of a compact normal form `u z^j`. -/
noncomputable def orderSplitCompactNormalFormGL
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
  orderSplitConstantGLHom P r u * orderSplitCyclicGeneratorGL P r ^ j

theorem map_orderSplitCompactNormalFormGL_to_global
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCompactNormalFormGL P r u j) =
      globalCompactNormalForm P r u j := by
  rw [orderSplitCompactNormalFormGL, globalCompactNormalForm,
    map_mul, map_pow, map_orderSplitConstantGL_to_global,
    map_orderSplitCyclicGeneratorGL_to_global]

theorem orderSplitCompactNormalFormGL_reduction_mem_stabilizer
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    orderSplitReductionPGLHom P r level
        (orderSplitCompactNormalFormGL P r u j) ∈
      IndexCartwrightStegerStabilizer P r level := by
  rw [orderSplitCompactNormalFormGL, map_mul, map_pow]
  apply (IndexCartwrightStegerStabilizer P r level).mul_mem
  · rw [IndexCartwrightStegerStabilizer]
    apply Subgroup.subset_closure
    left
    refine ⟨u, ?_⟩
    change indexConstantPGLHom P r level u =
      orderSplitReductionPGLHom P r level
        (orderSplitConstantGLHom P r u)
    change indexConstantPGLHom P r level u =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitConstantGLHom P r u))
    rw [map_orderSplitConstantGL]
    rfl
  · apply (IndexCartwrightStegerStabilizer P r level).pow_mem
    rw [IndexCartwrightStegerStabilizer]
    apply Subgroup.subset_closure
    right
    rw [Set.mem_singleton_iff]
    change Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map
          (indexConstantArithmeticEval P r level)
          (orderSplitCyclicGeneratorGL P r)) =
      Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level)
    rw [map_orderSplitCyclicGeneratorGL]

theorem orderSplitCompactNormalFormGL_mem_innerForm
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) (j : Nat) :
    orderSplitCompactNormalFormGL P r u j ∈
      OrderInnerFormUnits P r := by
  exact (OrderInnerFormUnits P r).mul_mem
    (orderSplitConstantGL_mem_innerForm P r u)
    ((OrderInnerFormUnits P r).pow_mem
      (orderSplitCyclicGeneratorGL_mem_innerForm P r) j)

/-- Simple transitivity at the building place decomposes every actual
arithmetic-order unit, projectively over the global field, as a
Cartwright--Steger lattice point times an explicit compact normal form. -/
theorem exists_orderSplitCartwrightSteger_mul_compact_of_orderUnit
    (P : BasePrime) (r : Rank)
    (ug : (CartwrightStegerOrder P r)ˣ) :
    ∃ x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      x ∈ OrderSplitCartwrightStegerLattice P r ∧
      ∃ u : (ConstantExtension P r)ˣ, ∃ j : Nat,
        orderUnitToGlobalPGL P r ug =
          Matrix.ProjGenLinGroup.mk
            (orderSplitBaseChangeGLHom P r
              (x * orderSplitCompactNormalFormGL P r u j)) := by
  let q : CartwrightStegerBuildingVertex P r :=
    QuotientGroup.mk (orderUnitToBuildingPGL P r ug)
  obtain ⟨ℓ, hℓ⟩ :=
    (buildingLatticeVertexMap_bijective P r).2 q
  obtain ⟨v, hvLattice, hvBuilding⟩ :=
    exists_orderUnitLattice_lift_of_buildingLattice P r ℓ
  have hvertex :
      (QuotientGroup.mk (orderUnitToBuildingPGL P r v) :
          CartwrightStegerBuildingVertex P r) =
        QuotientGroup.mk (orderUnitToBuildingPGL P r ug) := by
    simpa [buildingLatticeVertexMap, q, hvBuilding] using hℓ
  let w : (CartwrightStegerOrder P r)ˣ := v⁻¹ * ug
  have hwCompact : orderUnitToBuildingPGL P r w ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
    have hrel := QuotientGroup.eq.mp hvertex
    simpa [w, map_mul, map_inv] using hrel
  have hwCyclic : orderUnitToBuildingPGL P r w ∈
      BuildingCompactCyclicSubgroup P r :=
    orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
      P r w hwCompact
  obtain ⟨u, j, hj, hwBuilding⟩ :=
    exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
      P r (orderUnitToBuildingPGL P r w) hwCyclic
  have hwGlobal : orderUnitToGlobalPGL P r w =
      Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r u j) :=
    orderUnitToGlobalPGL_eq_compactNormalForm_of_building_eq
      P r w hwCompact u j hwBuilding
  have hvGlobalMem : orderUnitToGlobalGL P r v ∈
      CartwrightStegerMatrixGroup P r := by
    rw [← map_orderUnitLattice_to_global P r]
    exact ⟨v, hvLattice, rfl⟩
  have hvSplitMem : orderUnitToGlobalGL P r v ∈
      (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) := by
    rw [map_OrderSplitCartwrightStegerLattice_to_global P r]
    exact hvGlobalMem
  obtain ⟨x, hx, hxGlobal⟩ := hvSplitMem
  refine ⟨x, hx, u, j, ?_⟩
  calc
    orderUnitToGlobalPGL P r ug =
        orderUnitToGlobalPGL P r v * orderUnitToGlobalPGL P r w := by
      rw [← map_mul]
      congr 1
      simp [w]
    _ = orderUnitToGlobalPGL P r v *
        Matrix.ProjGenLinGroup.mk (globalCompactNormalForm P r u j) := by
      rw [hwGlobal]
    _ = Matrix.ProjGenLinGroup.mk
        (orderSplitBaseChangeGLHom P r
          (x * orderSplitCompactNormalFormGL P r u j)) := by
      rw [map_mul, map_mul, hxGlobal,
        map_orderSplitCompactNormalFormGL_to_global]
      rfl

/-- The order-unit decomposition specialized to an actual descended
split-coordinate inner-form point. -/
theorem exists_orderSplitCartwrightSteger_mul_compact_of_innerForm
    (P : BasePrime) (r : Rank) (g : OrderInnerFormUnits P r) :
    ∃ x : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      x ∈ OrderSplitCartwrightStegerLattice P r ∧
      ∃ u : (ConstantExtension P r)ˣ, ∃ j : Nat,
        Matrix.ProjGenLinGroup.mk
            (orderSplitBaseChangeGLHom P r
              (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (ConstantArithmeticRing P r))) =
          Matrix.ProjGenLinGroup.mk
            (orderSplitBaseChangeGLHom P r
              (x * orderSplitCompactNormalFormGL P r u j)) := by
  obtain ⟨x, hx, u, j, hglobal⟩ :=
    exists_orderSplitCartwrightSteger_mul_compact_of_orderUnit
      P r (orderInnerFormToOrderUnits P r g)
  refine ⟨x, hx, u, j, ?_⟩
  rw [← hglobal]
  apply congrArg Matrix.ProjGenLinGroup.mk
  exact orderUnitToGlobalGL_orderInnerFormToOrderUnits P r g

/-- Equality of global projective matrices detects equality in the genuine
projective unit group of the arithmetic order. -/
theorem cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq
    (P : BasePrime) (r : Rank)
    (u v : (CartwrightStegerOrder P r)ˣ)
    (hglobal : orderUnitToGlobalPGL P r u =
      orderUnitToGlobalPGL P r v) :
    cartwrightStegerOrderProjectivization P r u =
      cartwrightStegerOrderProjectivization P r v := by
  apply QuotientGroup.eq.mpr
  change Matrix.ProjGenLinGroup.mk (orderUnitToGlobalGL P r u) =
    Matrix.ProjGenLinGroup.mk (orderUnitToGlobalGL P r v) at hglobal
  have hcenterGlobal : orderUnitToGlobalGL P r (u⁻¹ * v) ∈
      Subgroup.center
        (Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    rw [map_mul, map_inv, map_mul, map_inv, hglobal]
    simp
  apply Subgroup.mem_center_iff.mpr
  intro w
  have hcomm := (Subgroup.mem_center_iff.mp hcenterGlobal)
    (orderUnitToGlobalGL P r w)
  apply Units.ext
  apply Subtype.ext
  exact congrArg Units.val hcomm

/-- Projectivization of descended split-coordinate points in the actual
arithmetic-order projective group. -/
noncomputable def orderInnerFormToOrderProjective
    (P : BasePrime) (r : Rank) :
    OrderInnerFormUnits P r →*
      CartwrightStegerOrderProjectiveGroup P r :=
  (cartwrightStegerOrderProjectivization P r).comp
    (orderInnerFormToOrderUnits P r)

/-- The checked split-coordinate descent model covers every genuine
projective arithmetic-order unit.  Thus later strong approximation is not
silently applied to a proper selected subgroup of `G'(R)`. -/
theorem orderInnerFormToOrderProjective_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (orderInnerFormToOrderProjective P r) := by
  intro q
  let u : (CartwrightStegerOrder P r)ˣ := q.out
  obtain ⟨x, hx, c, j, hglobal⟩ :=
    exists_orderSplitCartwrightSteger_mul_compact_of_orderUnit P r u
  let gGL : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
    x * orderSplitCompactNormalFormGL P r c j
  have hgInner : gGL ∈ OrderInnerFormUnits P r :=
    (OrderInnerFormUnits P r).mul_mem
      (OrderSplitCartwrightStegerLattice_le_innerForm P r hx)
      (orderSplitCompactNormalFormGL_mem_innerForm P r c j)
  let g : OrderInnerFormUnits P r := ⟨gGL, hgInner⟩
  refine ⟨g, ?_⟩
  change cartwrightStegerOrderProjectivization P r
      (orderInnerFormToOrderUnits P r g) = q
  calc
    cartwrightStegerOrderProjectivization P r
        (orderInnerFormToOrderUnits P r g) =
      cartwrightStegerOrderProjectivization P r u := by
        apply cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq
        rw [orderUnitToGlobalPGL]
        change Matrix.ProjGenLinGroup.mk
            (orderUnitToGlobalGL P r
              (orderInnerFormToOrderUnits P r g)) = _
        rw [orderUnitToGlobalGL_orderInnerFormToOrderUnits]
        exact hglobal.symm
    _ = q := QuotientGroup.out_eq' q

/-- Every finite reduction of a descended inner-form point lies in the
explicit Cartwright--Steger ambient group.  This is the finite-place image of
the lattice-times-stabilizer decomposition proved above. -/
theorem IndexInnerFormImage_le_IndexCartwrightStegerAmbient
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormImage P r level ≤
      IndexCartwrightStegerAmbient P r level := by
  rintro y ⟨g, rfl⟩
  obtain ⟨x, hx, u, j, hglobal⟩ :=
    exists_orderSplitCartwrightSteger_mul_compact_of_innerForm P r g
  have hreduction :=
    orderSplitReductionPGLHom_eq_of_baseChange_projective_eq
      P r level
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (x * orderSplitCompactNormalFormGL P r u j) hglobal
  rw [map_mul] at hreduction
  change orderSplitReductionPGLHom P r level
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) ∈
    IndexCartwrightStegerAmbient P r level
  rw [hreduction]
  apply (IndexCartwrightStegerAmbient P r level).mul_mem
  · rw [IndexCartwrightStegerAmbient,
      IndexCartwrightStegerUnitImage_eq_image]
    apply (le_sup_right : IndexCartwrightStegerImage P r level ≤ _)
    rw [← map_OrderSplitCartwrightStegerLattice P r level]
    exact ⟨x, hx, rfl⟩
  · rw [IndexCartwrightStegerAmbient,
      IndexCartwrightStegerUnitImage_eq_image]
    apply (le_sup_left : IndexCartwrightStegerStabilizer P r level ≤ _)
    exact orderSplitCompactNormalFormGL_reduction_mem_stabilizer
      P r level u j

/-- The actual finite reduction image of the full descended inner form is
exactly the explicitly generated Cartwright--Steger ambient subgroup. -/
theorem IndexInnerFormImage_eq_IndexCartwrightStegerAmbient
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormImage P r level =
      IndexCartwrightStegerAmbient P r level :=
  le_antisymm
    (IndexInnerFormImage_le_IndexCartwrightStegerAmbient P r level)
    (IndexCartwrightStegerAmbient_le_IndexInnerFormImage P r level)

/-- Consequently the Cartwright--Steger image is normal in the actual full
inner-form reduction image, not merely in an auxiliary generated group. -/
noncomputable instance indexCartwrightStegerImage_normal_in_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexCartwrightStegerImage P r level).subgroupOf
      (IndexInnerFormImage P r level)).Normal := by
  rw [IndexInnerFormImage_eq_IndexCartwrightStegerAmbient]
  infer_instance

/-- Reduction with codomain restricted to its actual image. -/
noncomputable def orderInnerFormReductionToImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormUnits P r →* IndexInnerFormImage P r level where
  toFun g := ⟨orderInnerFormReduction P r level g, ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one (orderInnerFormReduction P r level))
  map_mul' g h :=
    Subtype.ext (map_mul (orderInnerFormReduction P r level) g h)

theorem orderInnerFormReductionToImage_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderInnerFormReductionToImage P r level) := by
  intro g
  obtain ⟨x, hx⟩ := g.property
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- Image of the genuine norm-one kernel inside the full finite inner-form
image. -/
noncomputable def IndexInnerFormNormOneImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexInnerFormImage P r level) :=
  (OrderInnerFormNormOne P r).map
    (orderInnerFormReductionToImage P r level)

/-- The norm-one finite image is normal in the full finite inner-form image.
This is the exact source-side normality used in the LSV subgroup argument. -/
noncomputable instance indexInnerFormNormOneImageNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexInnerFormNormOneImage P r level).Normal := by
  exact Subgroup.Normal.map (inferInstance :
      (OrderInnerFormNormOne P r).Normal)
    (orderInnerFormReductionToImage P r level)
    (orderInnerFormReductionToImage_surjective P r level)

/-! ## The full congruence kernel and its norm-one intersection -/

/-- `H`: the genuine congruence kernel in the full integral inner-form
group, before restricting to reduced norm one. -/
noncomputable def OrderInnerFormCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderInnerFormUnits P r) :=
  (orderInnerFormReductionToImage P r level).ker

noncomputable instance orderInnerFormCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderInnerFormCongruenceSubgroup P r level).Normal := by
  dsimp [OrderInnerFormCongruenceSubgroup]
  infer_instance

theorem OrderInnerFormCongruenceSubgroup_eq_reduction_ker
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormCongruenceSubgroup P r level =
      (orderInnerFormReduction P r level).ker := by
  ext g
  change orderInnerFormReductionToImage P r level g = 1 ↔
    orderInnerFormReduction P r level g = 1
  constructor
  · exact fun h ↦ congrArg Subtype.val h
  · exact fun h ↦ Subtype.ext h

/-- `H₁ = H ∩ G'₁(R)`, represented as a subgroup of the genuine
norm-one kernel. -/
noncomputable def OrderInnerFormNormOneCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderInnerFormNormOne P r) :=
  (OrderInnerFormCongruenceSubgroup P r level).comap
    (OrderInnerFormNormOne P r).subtype

noncomputable instance orderInnerFormNormOneCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderInnerFormNormOneCongruenceSubgroup P r level).Normal := by
  exact Subgroup.Normal.comap
    (inferInstance : (OrderInnerFormCongruenceSubgroup P r level).Normal)
    (OrderInnerFormNormOne P r).subtype

/-- Reduction on the full-kernel presentation of norm-one points, with
codomain kept in finite `PGL`. -/
noncomputable def orderInnerFormNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormNormOne P r →* PGL P r level :=
  (orderInnerFormReduction P r level).comp
    (OrderInnerFormNormOne P r).subtype

theorem OrderInnerFormNormOneCongruenceSubgroup_eq_ker
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormNormOneCongruenceSubgroup P r level =
      (orderInnerFormNormOneReduction P r level).ker := by
  ext g
  change (g : OrderInnerFormUnits P r) ∈
      OrderInnerFormCongruenceSubgroup P r level ↔
    orderInnerFormNormOneReduction P r level g = 1
  rw [OrderInnerFormCongruenceSubgroup_eq_reduction_ker]
  rfl

/-- The full inner-form reduction has kernel exactly `H`, even after its
codomain is restricted to the actual finite image. -/
theorem ker_orderInnerFormReductionToImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderInnerFormReductionToImage P r level).ker =
      OrderInnerFormCongruenceSubgroup P r level := by
  rfl

/-- First isomorphism theorem for the full genuine inner-form congruence
reduction. -/
noncomputable def orderInnerFormCongruenceQuotientEquivImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormUnits P r ⧸
        OrderInnerFormCongruenceSubgroup P r level ≃*
      IndexInnerFormImage P r level := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (orderInnerFormReductionToImage P r level)
    (orderInnerFormReductionToImage_surjective P r level)

theorem natCard_orderInnerFormCongruenceQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (OrderInnerFormUnits P r ⧸
          OrderInnerFormCongruenceSubgroup P r level) =
      Nat.card (IndexInnerFormImage P r level) :=
  Nat.card_congr
    (orderInnerFormCongruenceQuotientEquivImage P r level).toEquiv

/-- The special-linear presentation of norm-one descended points agrees
with the kernel presentation inside the full inner-form unit group. -/
noncomputable def orderNormOneInnerFormEquivFullNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      OrderInnerFormNormOne P r where
  toFun s :=
    ⟨⟨Matrix.SpecialLinearGroup.toGL (s :
        Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)), s.property⟩, by
      change Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL (s :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) = 1
      simp⟩
  invFun g := by
    let s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
      ⟨(((g : OrderInnerFormUnits P r) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (ConstantArithmeticRing P r)),
        congrArg Units.val g.property⟩
    have hto : Matrix.SpecialLinearGroup.toGL s =
        ((g : OrderInnerFormUnits P r) :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) := by
      apply Units.ext
      rfl
    refine ⟨s, ?_⟩
    rw [OrderNormOneInnerForm]
    change Matrix.SpecialLinearGroup.toGL s ∈ OrderInnerFormUnits P r
    rw [hto]
    exact (g : OrderInnerFormUnits P r).property
  left_inv s := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.toGL_injective
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' s t := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul Matrix.SpecialLinearGroup.toGL
      (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))
      (t : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r))

/-- The determinant kernel in the descended cyclic-coordinate unit ring is
the same construction-owned norm-one inner form. -/
noncomputable def orderCyclicMatrixCoordinateNormOneEquiv
    (P : BasePrime) (r : Rank) :
    OrderCyclicMatrixCoordinateNormOneUnits P r ≃*
      OrderNormOneInnerForm P r :=
  { toFun := fun u =>
      (orderNormOneInnerFormEquivFullNormOne P r).symm
        ⟨orderCyclicMatrixCoordinateUnitsEquivInnerForm P r u, by
          have hu := u.property
          change orderCyclicMatrixCoordinateReducedNorm P r u = 1 at hu
          exact hu⟩
    invFun := fun s =>
      ⟨(orderCyclicMatrixCoordinateUnitsEquivInnerForm P r).symm
          (orderNormOneInnerFormEquivFullNormOne P r s), by
        change orderCyclicMatrixCoordinateReducedNorm P r
            ((orderCyclicMatrixCoordinateUnitsEquivInnerForm P r).symm
              (orderNormOneInnerFormEquivFullNormOne P r s)) = 1
        rw [← orderCyclicMatrixCoordinateUnitsEquivInnerForm_reducedNorm]
        simp only [MulEquiv.apply_symm_apply]
        exact (orderNormOneInnerFormEquivFullNormOne P r s).property⟩
    left_inv := by
      intro u
      apply Subtype.ext
      simp
    right_inv := by
      intro s
      apply Subtype.ext
      simp
    map_mul' := by
      intro u v
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.toGL_injective
      apply Units.ext
      rfl }

/-- Finite special-linear reduction transported to the norm-one units of the
genuine descended cyclic-coordinate ring. -/
noncomputable def orderCyclicMatrixCoordinateNormOneReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderCyclicMatrixCoordinateNormOneUnits P r →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  (orderSpecialLinearReduction P r level).comp
    ((OrderNormOneInnerForm P r).subtype.comp
      (orderCyclicMatrixCoordinateNormOneEquiv P r).toMonoidHom)

@[simp] theorem orderCyclicMatrixCoordinateNormOneReduction_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : OrderCyclicMatrixCoordinateNormOneUnits P r) :
    orderCyclicMatrixCoordinateNormOneReduction P r level u =
      orderSpecialLinearReduction P r level
        (orderCyclicMatrixCoordinateNormOneEquiv P r u :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)) := by
  rfl

/-- Surjectivity in the genuine coordinate-ring norm-one presentation gives
the required construction-owned projective norm-one reduction theorem. -/
theorem orderNormOneInnerFormReduction_surjective_of_coordinate_normOne
    (P : BasePrime) (r : Rank) (level : Nat)
    (hsurj : Function.Surjective
      (orderCyclicMatrixCoordinateNormOneReduction P r level)) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) := by
  intro y
  obtain ⟨s, hs⟩ := specialLinearToPSL_surjective P r level y
  obtain ⟨u, hu⟩ := hsurj s
  refine ⟨orderCyclicMatrixCoordinateNormOneEquiv P r u, ?_⟩
  change specialLinearToPSL P r level
      (orderSpecialLinearReduction P r level
        (orderCyclicMatrixCoordinateNormOneEquiv P r u :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) = y
  rw [← orderCyclicMatrixCoordinateNormOneReduction_apply, hu, hs]

/-- The special-linear norm-one reduction, viewed in ambient finite `PGL`. -/
noncomputable def orderNormOneInnerFormReductionToPGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →* PGL P r level :=
  (PSL P r level).subtype.comp
    (orderNormOneInnerFormReduction P r level)

/-- The kernel presentation of norm-one reduction, also viewed in finite
`PGL`. -/
noncomputable def orderInnerFormNormOneReductionToPGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderInnerFormNormOne P r →* PGL P r level :=
  (orderInnerFormReduction P r level).comp
    (OrderInnerFormNormOne P r).subtype

theorem orderNormOne_reduction_compatible_with_full_kernel
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormReductionToPGL P r level s =
      orderInnerFormNormOneReductionToPGL P r level
        (orderNormOneInnerFormEquivFullNormOne P r s) := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL
        (orderSpecialLinearReduction P r level
          (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)))) =
    orderSplitReductionPGLHom P r level
      (Matrix.SpecialLinearGroup.toGL
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)))
  have hmap : Matrix.SpecialLinearGroup.toGL
      (orderSpecialLinearReduction P r level
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))) =
      Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (Matrix.SpecialLinearGroup.toGL
          (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) := by
    apply Units.ext
    rfl
  rw [hmap]
  rfl

/-- Both presentations therefore have exactly the same finite projective
image. -/
theorem range_orderNormOne_reductionToPGL_eq_full_kernel
    (P : BasePrime) (r : Rank) (level : Nat) :
    (orderNormOneInnerFormReductionToPGL P r level).range =
      (orderInnerFormNormOneReductionToPGL P r level).range := by
  apply le_antisymm
  · rintro g ⟨s, rfl⟩
    exact ⟨orderNormOneInnerFormEquivFullNormOne P r s,
      (orderNormOne_reduction_compatible_with_full_kernel
        P r level s).symm⟩
  · rintro g ⟨t, rfl⟩
    let s := (orderNormOneInnerFormEquivFullNormOne P r).symm t
    refine ⟨s, ?_⟩
    rw [orderNormOne_reduction_compatible_with_full_kernel]
    simp [s]

/-- The norm-one image embedded back into ambient finite `PGL`. -/
noncomputable def IndexInnerFormNormOnePGLImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (IndexInnerFormNormOneImage P r level).map
    (IndexInnerFormImage P r level).subtype

theorem IndexInnerFormNormOnePGLImage_eq_range
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormNormOnePGLImage P r level =
      (orderInnerFormNormOneReductionToPGL P r level).range := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := ha
    refine ⟨⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val hxa
  · rintro ⟨x, rfl⟩
    refine ⟨orderInnerFormReductionToImage P r level
        (x : OrderInnerFormUnits P r), ?_, rfl⟩
    exact ⟨x, x.property, rfl⟩

theorem IndexInnerFormNormOnePGLImage_eq_orderNormOne_range
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormNormOnePGLImage P r level =
      (orderNormOneInnerFormReductionToPGL P r level).range := by
  rw [IndexInnerFormNormOnePGLImage_eq_range,
    range_orderNormOne_reductionToPGL_eq_full_kernel]

theorem IndexInnerFormNormOnePGLImage_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexInnerFormNormOnePGLImage P r level ≤
      IndexInnerFormImage P r level := by
  rintro g ⟨a, ha, rfl⟩
  exact a.property

/-- After embedding in `PGL`, the norm-one image remains normal in the full
inner-form image. -/
noncomputable instance indexInnerFormNormOnePGLImageNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexInnerFormNormOnePGLImage P r level).subgroupOf
      (IndexInnerFormImage P r level)).Normal := by
  have heq :
      (IndexInnerFormNormOnePGLImage P r level).subgroupOf
          (IndexInnerFormImage P r level) =
        IndexInnerFormNormOneImage P r level := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      have : b = a := Subtype.ext hba
      simpa [this] using hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [heq]
  infer_instance

/-! ## The genuine norm-one congruence kernel and quotient -/

/-- Norm-one reduction with codomain restricted to its actual finite image. -/
noncomputable def orderNormOneInnerFormReductionToImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r →*
      IndexNormOneInnerFormImage P r level :=
  (orderNormOneInnerFormReduction P r level).rangeRestrict

theorem orderNormOneInnerFormReductionToImage_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (orderNormOneInnerFormReductionToImage P r level) := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- `H₁`: the principal congruence kernel inside the actual norm-one
inner-form group at the selected place. -/
noncomputable def OrderNormOneCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderNormOneInnerForm P r) :=
  (orderNormOneInnerFormReductionToImage P r level).ker

noncomputable instance orderNormOneCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneCongruenceSubgroup P r level).Normal := by
  dsimp [OrderNormOneCongruenceSubgroup]
  infer_instance

theorem orderNormOneCongruenceSubgroup_eq_reduction_ker
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneCongruenceSubgroup P r level =
      (orderNormOneInnerFormReduction P r level).ker := by
  ext g
  change
    (orderNormOneInnerFormReduction P r level).rangeRestrict g = 1 ↔
      orderNormOneInnerFormReduction P r level g = 1
  constructor
  · exact fun h ↦ congrArg Subtype.val h
  · exact fun h ↦ Subtype.ext h

/-- The special-linear and full-kernel presentations define exactly the same
genuine norm-one congruence subgroup `H₁`. -/
theorem map_orderNormOneCongruenceSubgroup_equivFullNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneCongruenceSubgroup P r level).map
        (orderNormOneInnerFormEquivFullNormOne P r).toMonoidHom =
      OrderInnerFormNormOneCongruenceSubgroup P r level := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [OrderInnerFormNormOneCongruenceSubgroup_eq_ker,
      MonoidHom.mem_ker]
    rw [orderNormOneCongruenceSubgroup_eq_reduction_ker] at hs
    change orderNormOneInnerFormReduction P r level s = 1 at hs
    have hcompat := orderNormOne_reduction_compatible_with_full_kernel
      P r level s
    change (PSL P r level).subtype
        (orderNormOneInnerFormReduction P r level s) =
      orderInnerFormNormOneReduction P r level
        (orderNormOneInnerFormEquivFullNormOne P r s) at hcompat
    rw [hs, map_one] at hcompat
    exact hcompat.symm
  · intro ht
    let s := (orderNormOneInnerFormEquivFullNormOne P r).symm t
    refine ⟨s, ?_, by simp [s]⟩
    rw [orderNormOneCongruenceSubgroup_eq_reduction_ker]
    change orderNormOneInnerFormReduction P r level s = 1
    rw [OrderInnerFormNormOneCongruenceSubgroup_eq_ker,
      MonoidHom.mem_ker] at ht
    have hcompat := orderNormOne_reduction_compatible_with_full_kernel
      P r level s
    rw [show orderNormOneInnerFormEquivFullNormOne P r s = t by simp [s]]
      at hcompat
    change (PSL P r level).subtype
        (orderNormOneInnerFormReduction P r level s) =
      orderInnerFormNormOneReduction P r level t at hcompat
    rw [ht] at hcompat
    apply Subtype.ext
    exact hcompat

/-- First isomorphism theorem for the genuine norm-one congruence
reduction, without prematurely identifying its image with all of `PSL`. -/
noncomputable def orderNormOneCongruenceQuotientEquivImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneInnerForm P r ⧸
        OrderNormOneCongruenceSubgroup P r level ≃*
      IndexNormOneInnerFormImage P r level := by
  exact QuotientGroup.quotientKerEquivOfSurjective
    (orderNormOneInnerFormReductionToImage P r level)
    (orderNormOneInnerFormReductionToImage_surjective P r level)

theorem natCard_orderNormOneCongruenceQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (OrderNormOneInnerForm P r ⧸
          OrderNormOneCongruenceSubgroup P r level) =
      Nat.card (IndexNormOneInnerFormImage P r level) :=
  Nat.card_congr
    (orderNormOneCongruenceQuotientEquivImage P r level).toEquiv

/-! ## The actual norm-one Cartwright--Steger lattice -/

/-- Forget the descent certificate and determinant-one certificate, retaining
the split general-linear matrix of an actual norm-one inner-form point. -/
noncomputable def orderNormOneInnerFormToSplitGL
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r) :=
  Matrix.SpecialLinearGroup.toGL.comp (OrderNormOneInnerForm P r).subtype

/-- The norm-one lift subgroup: the intersection of the integral split
Cartwright--Steger lattice with the construction-owned norm-one inner form.
LSV explicitly warns that its projective image can be strictly smaller than
the projective subgroup `Γ₁`; the latter is constructed separately below. -/
noncomputable def OrderNormOneCartwrightStegerLiftLattice
    (P : BasePrime) (r : Rank) :
    Subgroup (OrderNormOneInnerForm P r) :=
  (OrderSplitCartwrightStegerLattice P r).comap
    (orderNormOneInnerFormToSplitGL P r)

/-- Every ratio of two class-indexed Cartwright--Steger generators belongs to
the actual norm-one lift lattice. -/
theorem orderNormOneGeneratorRatio_mem_liftLattice
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    orderNormOneGeneratorRatio P r u v ∈
      OrderNormOneCartwrightStegerLiftLattice P r := by
  change Matrix.SpecialLinearGroup.toGL
      (orderSplitGeneratorRatioSpecial P r u v) ∈
    OrderSplitCartwrightStegerLattice P r
  have hu : orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u) ∈
      OrderSplitCartwrightStegerLattice P r :=
    Subgroup.subset_closure ⟨u, rfl⟩
  have hv : orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r v) ∈
      OrderSplitCartwrightStegerLattice P r :=
    Subgroup.subset_closure ⟨v, rfl⟩
  have hto : Matrix.SpecialLinearGroup.toGL
        (orderSplitGeneratorRatioSpecial P r u v) =
      orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) *
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r v))⁻¹ := by
    apply Units.ext
    rfl
  rw [hto]
  have hratio := (OrderSplitCartwrightStegerLattice P r).mul_mem
    hu ((OrderSplitCartwrightStegerLattice P r).inv_mem hv)
  exact hratio

/-- The finite reduction image of the norm-one lift lattice inside `PSL`. -/
noncomputable def IndexNormOneCartwrightStegerLiftImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PSL P r level) :=
  (OrderNormOneCartwrightStegerLiftLattice P r).map
    (orderNormOneInnerFormReduction P r level)

theorem IndexNormOneCartwrightStegerLiftImage_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneCartwrightStegerLiftImage P r level ≤
      IndexNormOneInnerFormImage P r level := by
  rintro g ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

/-- The finite image of the norm-one lift lattice is nontrivial, witnessed by
the ratio of two distinct explicit Cartwright--Steger generators. -/
theorem exists_ne_one_mem_IndexNormOneCartwrightStegerLiftImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PSL P r level,
      g ∈ IndexNormOneCartwrightStegerLiftImage P r level ∧ g ≠ 1 := by
  letI : Nontrivial (ConstantProjectiveClass P r) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa [Nat.card_eq_fintype_card] using
        one_lt_natCard_constantProjectiveClass P r)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (ConstantProjectiveClass P r)
  let x := orderNormOneGeneratorRatio P r u v
  let g := orderNormOneInnerFormReduction P r level x
  refine ⟨g, ⟨x, orderNormOneGeneratorRatio_mem_liftLattice P r u v,
    rfl⟩, ?_⟩
  intro hg
  have hprojective := congrArg (fun q : PSL P r level =>
    (q : PGL P r level)) hg
  have hratio :
      indexCartwrightStegerClassGenerator P r level u *
          (indexCartwrightStegerClassGenerator P r level v)⁻¹ = 1 := by
    simpa [g, x,
      orderNormOneInnerFormReduction_generatorRatio] using hprojective
  have heq : indexCartwrightStegerClassGenerator P r level u =
      indexCartwrightStegerClassGenerator P r level v :=
    mul_inv_eq_one.mp hratio
  exact huv (indexCartwrightStegerClassGenerator_injective P r level heq)

theorem IndexNormOneCartwrightStegerLiftImage_ne_bot
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneCartwrightStegerLiftImage P r level ≠ ⊥ := by
  obtain ⟨g, hg, hg1⟩ :=
    exists_ne_one_mem_IndexNormOneCartwrightStegerLiftImage P r level
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hg
  exact hg1 hg

/-- Compatibility of norm-one reduction with the integral split
Cartwright--Steger reduction, before restricting either finite image. -/
theorem orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : OrderNormOneInnerForm P r) :
    orderNormOneInnerFormReductionToPGL P r level s =
      orderSplitReductionPGLHom P r level
        (orderNormOneInnerFormToSplitGL P r s) := by
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL
        (orderSpecialLinearReduction P r level
          (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r)))) =
    orderSplitReductionPGLHom P r level
      (Matrix.SpecialLinearGroup.toGL
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r)))
  have hmap : Matrix.SpecialLinearGroup.toGL
      (orderSpecialLinearReduction P r level
        (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))) =
      Matrix.GeneralLinearGroup.map
        (indexConstantArithmeticEval P r level)
        (Matrix.SpecialLinearGroup.toGL
          (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) := by
    apply Units.ext
    rfl
  rw [hmap]
  rfl

/-- The norm-one lift image, embedded into finite `PGL`. -/
noncomputable def IndexNormOneCartwrightStegerLiftPGLImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  (IndexNormOneCartwrightStegerLiftImage P r level).map
    (PSL P r level).subtype

/-- Every finite point produced by the norm-one lift lattice belongs to the
actual Cartwright--Steger finite image. -/
theorem IndexNormOneCartwrightStegerLiftPGLImage_le_indexImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneCartwrightStegerLiftPGLImage P r level ≤
      IndexCartwrightStegerImage P r level := by
  rintro y ⟨g, hg, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hg
  rw [← map_OrderSplitCartwrightStegerLattice P r level]
  refine ⟨orderNormOneInnerFormToSplitGL P r x, hx, ?_⟩
  exact (orderNormOneInnerFormReductionToPGL_eq_orderSplitReduction
    P r level x).symm

/-- Product of the norm-one lift lattice and its congruence kernel, formed
inside the genuine norm-one inner-form group. -/
noncomputable def OrderNormOneLiftCongruenceProduct
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderNormOneInnerForm P r) :=
  OrderNormOneCartwrightStegerLiftLattice P r ⊔
    OrderNormOneCongruenceSubgroup P r level

theorem normOne_liftLattice_le_liftCongruenceProduct
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneCartwrightStegerLiftLattice P r ≤
      OrderNormOneLiftCongruenceProduct P r level :=
  le_sup_left

theorem normOne_congruence_le_liftCongruenceProduct
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneCongruenceSubgroup P r level ≤
      OrderNormOneLiftCongruenceProduct P r level :=
  le_sup_right

theorem map_orderNormOneCongruenceSubgroup_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneCongruenceSubgroup P r level).map
        (orderNormOneInnerFormReduction P r level) = ⊥ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    have hxker : x ∈
        (orderNormOneInnerFormReduction P r level).ker := by
      rw [← orderNormOneCongruenceSubgroup_eq_reduction_ker P r level]
      exact hx
    exact hxker
  · exact bot_le

/-- Adding the congruence kernel does not enlarge the finite reduction image:
the product has exactly the image of the norm-one lift lattice. -/
theorem map_orderNormOneLiftCongruenceProduct_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneLiftCongruenceProduct P r level).map
        (orderNormOneInnerFormReduction P r level) =
      IndexNormOneCartwrightStegerLiftImage P r level := by
  rw [OrderNormOneLiftCongruenceProduct, Subgroup.map_sup,
    map_orderNormOneCongruenceSubgroup_reduction, sup_bot_eq]
  rfl

/-- Reduction of the norm-one-lift/congruence product, with codomain
restricted to its exact finite image. -/
noncomputable def orderNormOneLiftCongruenceReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneLiftCongruenceProduct P r level →*
      IndexNormOneCartwrightStegerLiftImage P r level where
  toFun g := ⟨orderNormOneInnerFormReduction P r level g, by
    have hmem : orderNormOneInnerFormReduction P r level g ∈
        (OrderNormOneLiftCongruenceProduct P r level).map
          (orderNormOneInnerFormReduction P r level) :=
      ⟨g, g.property, rfl⟩
    rw [map_orderNormOneLiftCongruenceProduct_reduction] at hmem
    exact hmem⟩
  map_one' := Subtype.ext (map_one (orderNormOneInnerFormReduction P r level))
  map_mul' g h := Subtype.ext
    (map_mul (orderNormOneInnerFormReduction P r level)
      (g : OrderNormOneInnerForm P r)
      (h : OrderNormOneInnerForm P r))

theorem orderNormOneLiftCongruenceReduction_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (orderNormOneLiftCongruenceReduction P r level) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, normOne_liftLattice_le_liftCongruenceProduct P r level hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The kernel of reduction on the norm-one-lift/congruence product; below it
is identified with the restriction of the genuine principal congruence
subgroup. -/
noncomputable def OrderNormOneLiftCongruenceKernel
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (OrderNormOneLiftCongruenceProduct P r level) :=
  (orderNormOneLiftCongruenceReduction P r level).ker

theorem orderNormOneLiftCongruenceKernel_eq_subgroupOf
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneLiftCongruenceKernel P r level =
      (OrderNormOneCongruenceSubgroup P r level).subgroupOf
        (OrderNormOneLiftCongruenceProduct P r level) := by
  ext g
  change orderNormOneLiftCongruenceReduction P r level g = 1 ↔
    (g : OrderNormOneInnerForm P r) ∈
      OrderNormOneCongruenceSubgroup P r level
  constructor
  · intro hg
    have hg' : orderNormOneInnerFormReduction P r level
        (g : OrderNormOneInnerForm P r) = 1 :=
      congrArg Subtype.val hg
    rw [orderNormOneCongruenceSubgroup_eq_reduction_ker]
    exact hg'
  · intro hg
    apply Subtype.ext
    rw [orderNormOneCongruenceSubgroup_eq_reduction_ker] at hg
    exact hg

noncomputable instance orderNormOneLiftCongruenceKernelNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneLiftCongruenceKernel P r level).Normal := by
  dsimp [OrderNormOneLiftCongruenceKernel]
  infer_instance

/-- First isomorphism theorem for the exact norm-one-lift reduction. -/
noncomputable def orderNormOneLiftCongruenceQuotientEquivImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderNormOneLiftCongruenceProduct P r level ⧸
        OrderNormOneLiftCongruenceKernel P r level ≃*
      IndexNormOneCartwrightStegerLiftImage P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (orderNormOneLiftCongruenceReduction P r level)
    (orderNormOneLiftCongruenceReduction_surjective P r level)

theorem natCard_orderNormOneLiftCongruenceQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (OrderNormOneLiftCongruenceProduct P r level ⧸
          OrderNormOneLiftCongruenceKernel P r level) =
      Nat.card (IndexNormOneCartwrightStegerLiftImage P r level) :=
  Nat.card_congr
    (orderNormOneLiftCongruenceQuotientEquivImage P r level).toEquiv

/-- A normal subgroup of an ambient finite group which meets a contained
simple subgroup nontrivially contains that simple subgroup. -/
theorem simple_le_of_normal_subgroupOf_of_exists_ne_one
    {G : Type*} [Group G]
    (S H A : Subgroup G) [IsSimpleGroup S]
    (hSA : S ≤ A)
    [((H.subgroupOf A)).Normal]
    (hne : ∃ g : G, g ∈ H ∧ g ∈ S ∧ g ≠ 1) :
    S ≤ H := by
  let N : Subgroup S := H.comap S.subtype
  have hNnormal : N.Normal := by
    constructor
    intro n hn s
    change (s : G) * (n : G) * (s : G)⁻¹ ∈ H
    have hnA : (n : G) ∈ A := hSA n.property
    have hsA : (s : G) ∈ A := hSA s.property
    have hnH : (n : G) ∈ H := hn
    let nA : A := ⟨n, hnA⟩
    let sA : A := ⟨s, hsA⟩
    have hnSub : nA ∈ H.subgroupOf A := hnH
    have hconj := (inferInstance : (H.subgroupOf A).Normal).conj_mem
      nA hnSub sA
    exact hconj
  obtain ⟨g, hgH, hgS, hg1⟩ := hne
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hgN : (⟨g, hgS⟩ : S) ∈ N := hgH
    rw [hbot, Subgroup.mem_bot] at hgN
    exact hg1 (congrArg Subtype.val hgN)
  have hNtop : N = ⊤ :=
    hNnormal.eq_bot_or_eq_top.resolve_left hNne
  intro s hs
  have hsN : (⟨s, hs⟩ : S) ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top _
  exact hsN

/-- Group-theoretic endpoint of construction-specialized strong
approximation.  Once the actual full inner-form reduction contains finite
`PSL`, the genuine norm-one reduction is surjective; the proof uses only the
proved normality, explicit nonidentity element, and simplicity of `PSL`. -/
theorem orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexInnerFormImage P r level) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  have hne : ∃ g : PGL P r level,
      g ∈ IndexInnerFormNormOnePGLImage P r level ∧
      g ∈ PSL P r level ∧ g ≠ 1 := by
    obtain ⟨g, hg, hg1⟩ :=
      exists_ne_one_mem_range_orderNormOneInnerFormReduction P r level
    obtain ⟨x, rfl⟩ := hg
    refine ⟨(orderNormOneInnerFormReduction P r level x : PGL P r level),
      ?_, (orderNormOneInnerFormReduction P r level x).property, ?_⟩
    · rw [IndexInnerFormNormOnePGLImage_eq_orderNormOne_range]
      exact ⟨x, rfl⟩
    · intro hx
      apply hg1
      apply Subtype.ext
      exact hx
  have hcontain : PSL P r level ≤
      IndexInnerFormNormOnePGLImage P r level :=
    simple_le_of_normal_subgroupOf_of_exists_ne_one
      (PSL P r level)
      (IndexInnerFormNormOnePGLImage P r level)
      (IndexInnerFormImage P r level) hPSL hne
  intro y
  have hy : (y : PGL P r level) ∈
      IndexInnerFormNormOnePGLImage P r level :=
    hcontain y.property
  rw [IndexInnerFormNormOnePGLImage_eq_orderNormOne_range] at hy
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- Once construction-specialized strong approximation places finite `PSL`
inside the explicit finite ambient reduction, the already proved normality,
nontrivial intersection, and simplicity force `PSL` into the finite
Cartwright--Steger image. -/
theorem PSL_le_IndexCartwrightStegerImage_of_le_ambient
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerAmbient P r level) :
    PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  letI : IsSimpleGroup (PSL P r level) :=
    PSL_isSimpleGroup P r level
  exact simple_le_of_normal_subgroupOf_of_exists_ne_one
    (PSL P r level)
    (IndexCartwrightStegerImage P r level)
    (IndexCartwrightStegerAmbient P r level)
    hPSL (exists_nontrivial_mem_image_inter_PSL P r level)

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
