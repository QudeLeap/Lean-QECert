import QEC.Coding.HighDimensionalExpander.Hecke.CartanDecomposition
import QEC.Coding.HighDimensionalExpander.Combinatorics.FiniteGrassmannian

/-!
# Reduction of the maximal compact subgroup to the residue field

This file supplies the concrete reduction and constant-lift maps used to
identify fundamental local-building links with finite Grassmannians.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.SphericalHecke

open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

/-- Entrywise reduction of an invertible power-series matrix modulo `X`. -/
def powerSeriesReductionGL (k : Type*) [Field k] (d : ℕ) :
    GL (Fin d) (IntegerRing k) →* GL (Fin d) k :=
  Matrix.GeneralLinearGroup.map PowerSeries.constantCoeff

/-- The constant-series lift of an invertible residue-field matrix. -/
def constantGeneralLinearLift (k : Type*) [Field k] (d : ℕ) :
    GL (Fin d) k →* GL (Fin d) (IntegerRing k) :=
  Matrix.GeneralLinearGroup.map PowerSeries.C

theorem powerSeriesReductionGL_constantGeneralLinearLift
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) k) :
    powerSeriesReductionGL k d (constantGeneralLinearLift k d g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [powerSeriesReductionGL, constantGeneralLinearLift]

/-- Reduction `GL_d(k[[X]]) → GL_d(k)` is onto, with the concrete
constant-matrix section above. -/
theorem powerSeriesReductionGL_surjective
    (k : Type*) [Field k] (d : ℕ) :
    Function.Surjective (powerSeriesReductionGL k d) := by
  intro g
  exact ⟨constantGeneralLinearLift k d g,
    powerSeriesReductionGL_constantGeneralLinearLift k d g⟩

/-- Transport an integral invertible matrix back to the power-series model. -/
def integerGeneralLinearToPowerSeries (k : Type*) [Field k] (d : ℕ) :
    GL (Fin d) (Valued.integer (LocalFunctionField k)) →*
      GL (Fin d) (IntegerRing k) :=
  Matrix.GeneralLinearGroup.map
    (LocalTopology.powerSeriesIntegerEquiv k).symm.toRingHom

theorem powerSeriesGeneralLinearToInteger_inverse
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    powerSeriesGeneralLinearToInteger k d
        (integerGeneralLinearToPowerSeries k d g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [powerSeriesGeneralLinearToInteger,
    integerGeneralLinearToPowerSeries]

theorem integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse
    (k : Type*) [Field k] (d : ℕ)
    (g : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    integralProjectiveMap k d g =
      powerSeriesProjectiveMap k d
        (integerGeneralLinearToPowerSeries k d g) := by
  change Matrix.ProjGenLinGroup.mk (integralGeneralLinearToLocal k d g) =
    Matrix.ProjGenLinGroup.mk (powerSeriesGeneralLinearToLocal k d
      (integerGeneralLinearToPowerSeries k d g))
  congr 1
  rw [← powerSeries_integer_local_triangle,
    powerSeriesGeneralLinearToInteger_inverse]

/-- The analytically defined maximal compact subgroup is exactly the
projective image of `GL_d(k[[X]])`. -/
theorem maximalCompact_eq_range_powerSeriesProjectiveMap
    (k : Type*) [Field k] (d : ℕ) :
    (maximalCompact k d :
      Set (PGL(Fin d, LocalFunctionField k))) =
      Set.range (powerSeriesProjectiveMap k d) := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, rfl⟩ := (mem_maximalCompact_iff k d g).1 hg
    exact ⟨integerGeneralLinearToPowerSeries k d h,
      (integralProjectiveMap_eq_powerSeriesProjectiveMap_inverse k d h).symm⟩
  · rintro ⟨h, rfl⟩
    exact mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact h

/-- A local-field unit of Laurent order zero is an actual unit of the
valuation ring. -/
noncomputable def integerUnitOfLocalUnitOrderZero
    (k : Type*) [Field k] (c : Units (LocalFunctionField k))
    (hc : localUnitOrder c = 0) :
    Units (Valued.integer (LocalFunctionField k)) := by
  have hcint : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k) := by
    have h := integralClearingExponent_spec (c : LocalFunctionField k)
    have hclear : integralClearingExponent (c : LocalFunctionField k) = 0 := by
      change (c : LocalFunctionField k).order = 0 at hc
      rw [integralClearingExponent, hc]
      simp
    simpa [hclear] using h
  have hcinv : ((c⁻¹ : Units (LocalFunctionField k)) : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k) := by
    have h := integralClearingExponent_spec
      ((c : LocalFunctionField k)⁻¹)
    have horder : localUnitOrder c⁻¹ = 0 := by simp [localUnitOrder_inv, hc]
    have hfieldorder : ((c : LocalFunctionField k)⁻¹).order = 0 := by
      simpa [localUnitOrder] using horder
    have hclear : integralClearingExponent
        ((c : LocalFunctionField k)⁻¹) = 0 := by
      rw [integralClearingExponent, hfieldorder]
      simp
    simpa [hclear] using h
  exact {
    val := ⟨c, hcint⟩
    inv := ⟨((c⁻¹ : Units (LocalFunctionField k)) : LocalFunctionField k), hcinv⟩
    val_inv := by ext; simp
    inv_val := by ext; simp }

/-- For positive matrix rank and determinant order zero, projective maximal
compactness is equivalent to honest integrality of the matrix and its inverse.
The determinant hypothesis removes the otherwise invisible projective scalar. -/
theorem projective_mk_mem_maximalCompact_iff_integral
    (k : Type*) [Field k] [Finite k] (d : ℕ) (hd : 0 < d)
    (A : GL (Fin d) (LocalFunctionField k))
    (hdet : localUnitOrder (Matrix.GeneralLinearGroup.det A) = 0) :
    Matrix.ProjGenLinGroup.mk A ∈ maximalCompact k d ↔
      A ∈ integralGeneralLinearSet k d := by
  constructor
  · intro hA
    obtain ⟨B, hB⟩ := (mem_maximalCompact_iff k d _).mp hA
    change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k d B) = Matrix.ProjGenLinGroup.mk A at hB
    obtain ⟨c, hGL⟩ :=
      exists_scalar_mul_eq_of_projective_mk_eq hB.symm
    have horder := congrArg localUnitOrder
      (congrArg Matrix.GeneralLinearGroup.det hGL)
    have hc : localUnitOrder c = 0 := by
      simp [Matrix.GeneralLinearGroup.det_scalar, localUnitOrder_mul,
        localUnitOrder_pow, integralGeneralLinear_det_localUnitOrder_eq_zero,
        hdet] at horder
      omega
    let ci := integerUnitOfLocalUnitOrderZero k c hc
    rw [← range_integralGeneralLinearToLocal]
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) ci * B, ?_⟩
    calc
      integralGeneralLinearToLocal k d
          (Matrix.GeneralLinearGroup.scalar (Fin d) ci * B) =
          Matrix.GeneralLinearGroup.scalar (Fin d) c *
            integralGeneralLinearToLocal k d B := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        simp [ci, integerUnitOfLocalUnitOrderZero,
          integralGeneralLinearToLocal, Matrix.mul_apply]
      _ = A := hGL.symm
  · intro hA
    rw [← range_integralGeneralLinearToLocal] at hA
    obtain ⟨B, rfl⟩ := hA
    exact (mem_maximalCompact_iff k d _).mpr ⟨B, rfl⟩

/-! ### The residue-plane invariant -/

/-- Reduce an integral invertible matrix modulo `X` and apply it to the
standard coordinate `r`-plane. -/
def residueCoordinatePlane
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    FiniteGrassmannian k (Fin d → k) r := by
  let e := (Matrix.GeneralLinearGroup.toLin
    (powerSeriesReductionGL k d g)).toLinearEquiv
  exact ⟨(coordinateGrassmannian k d r hr).1.map e.toLinearMap, by
    rw [LinearEquiv.finrank_map_eq]
    exact (coordinateGrassmannian k d r hr).property⟩

/-- Every residue-field `r`-plane has an integral lift. -/
theorem residueCoordinatePlane_surjective
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Function.Surjective (residueCoordinatePlane k d r hr) := by
  intro W
  obtain ⟨g, hg⟩ :=
    exists_generalLinear_map_coordinateGrassmannian k d r hr W
  refine ⟨constantGeneralLinearLift k d g, ?_⟩
  apply Subtype.ext
  change (coordinateGrassmannian k d r hr).1.map
      (Matrix.GeneralLinearGroup.toLin
        (powerSeriesReductionGL k d (constantGeneralLinearLift k d g))).val = W.1
  rw [powerSeriesReductionGL_constantGeneralLinearLift]
  exact hg

/-- The contragredient residue-plane invariant appropriate to the right
cosets in `K a_r K / K`. -/
def residueFundamentalPlane
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    FiniteGrassmannian k (Fin d → k) r := by
  let e := (Matrix.GeneralLinearGroup.toLin
    (contragredientGeneralLinearHom (powerSeriesReductionGL k d g))).toLinearEquiv
  exact ⟨(coordinateGrassmannian k d r hr).1.map e.toLinearMap, by
    rw [LinearEquiv.finrank_map_eq]
    exact (coordinateGrassmannian k d r hr).property⟩

/-- Every finite `r`-plane has a concrete contragredient integral lift. -/
theorem residueFundamentalPlane_surjective
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Function.Surjective (residueFundamentalPlane k d r hr) := by
  intro W
  obtain ⟨g, hg⟩ :=
    exists_generalLinear_map_coordinateGrassmannian k d r hr W
  refine ⟨constantGeneralLinearLift k d
    (contragredientGeneralLinearHom g), ?_⟩
  apply Subtype.ext
  change (coordinateGrassmannian k d r hr).1.map
      (Matrix.GeneralLinearGroup.toLin
        (contragredientGeneralLinearHom
          (powerSeriesReductionGL k d
            (constantGeneralLinearLift k d
              (contragredientGeneralLinearHom g))))).val = W.1
  rw [powerSeriesReductionGL_constantGeneralLinearLift,
    contragredientGeneralLinear_involutive]
  exact hg

/-! ### One-step divisibility at the uniformizer -/

/-- Delete the constant coefficient of a power series and shift the
remaining coefficients down by one. -/
def powerSeriesTail (k : Type*) [Field k] (f : IntegerRing k) : IntegerRing k :=
  PowerSeries.mk fun p ↦ PowerSeries.coeff (p + 1) f

/-- If the residue of `f` vanishes, division by the uniformizer remains in
the valuation ring, with the displayed integral representative. -/
theorem uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
    (k : Type*) [Field k] (f : IntegerRing k)
    (hf : PowerSeries.constantCoeff f = 0) :
    ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f =
      integerEmbedding k (powerSeriesTail k f) := by
  let q := powerSeriesTail k f
  have hfq : f = PowerSeries.X * q := by
    simpa [hf, q, powerSeriesTail] using (PowerSeries.eq_X_mul_shift_add_const f)
  change ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f =
    integerEmbedding k q
  rw [hfq]
  simp [integerEmbedding, coe_uniformizerUnit, HahnSeries.ofPowerSeries_X,
    map_mul, ← mul_assoc]

/-- Conversely, an integral quotient by the uniformizer forces vanishing
of the constant coefficient. -/
theorem constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer
    (k : Type*) [Field k] (f : IntegerRing k)
    (hf : ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f ∈
      Valued.integer (LocalFunctionField k)) :
    PowerSeries.constantCoeff f = 0 := by
  let x : Valued.integer (LocalFunctionField k) :=
    ⟨((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f, hf⟩
  let q : IntegerRing k := (LocalTopology.powerSeriesIntegerEquiv k).symm x
  have hq : integerEmbedding k q =
      ((uniformizerUnit k)⁻¹ : LocalFunctionField k) * integerEmbedding k f := by
    have hx := (LocalTopology.powerSeriesIntegerEquiv k).apply_symm_apply x
    exact congrArg Subtype.val hx
  have hmul := congrArg
    (fun z : LocalFunctionField k ↦ (uniformizerUnit k : LocalFunctionField k) * z) hq
  have hembed : integerEmbedding k (PowerSeries.X * q) = integerEmbedding k f := by
    calc
      integerEmbedding k (PowerSeries.X * q) =
          (uniformizerUnit k : LocalFunctionField k) * integerEmbedding k q := by
        simp [integerEmbedding, coe_uniformizerUnit,
          HahnSeries.ofPowerSeries_X, map_mul]
      _ = (uniformizerUnit k : LocalFunctionField k) *
          (((uniformizerUnit k)⁻¹ : LocalFunctionField k) *
            integerEmbedding k f) := hmul
      _ = integerEmbedding k f := by
        rw [← mul_assoc]
        simp
  have hseries : PowerSeries.X * q = f := integerEmbedding_injective k hembed
  rw [← hseries]
  simp

/-! ### Entrywise fundamental conjugation -/

/-- Conjugate an integral matrix by the fundamental diagonal. -/
def fundamentalIntegralConjugate
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    GL (Fin d) (LocalFunctionField k) :=
  (fundamentalDiagonal k d r)⁻¹ *
    powerSeriesGeneralLinearToLocal k d g *
      fundamentalDiagonal k d r

theorem fundamentalIntegralConjugate_apply
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) (i j : Fin d) :
    fundamentalIntegralConjugate k d r g i j =
      (if i.val < r then ((uniformizerUnit k)⁻¹ : LocalFunctionField k) else 1) *
        integerEmbedding k (g i j) *
      (if j.val < r then (uniformizerUnit k : LocalFunctionField k) else 1) := by
  simp [fundamentalIntegralConjugate, fundamentalDiagonal,
    diagonalGeneralLinear_inv, diagonalGeneralLinear_apply,
    fundamentalDiagonalUnits, Matrix.mul_apply]
  split_ifs <;>
    simp [powerSeriesGeneralLinearToLocal, integerEmbedding,
      coe_uniformizerUnit]

/-- The upper-right residue block that controls fundamental conjugation. -/
def UpperRightResidueZero
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) : Prop :=
  ∀ i j : Fin d, i.val < r → r ≤ j.val →
    PowerSeries.constantCoeff (g i j) = 0

theorem integerEmbedding_mem_integer
    (k : Type*) [Field k] (f : IntegerRing k) :
    integerEmbedding k f ∈ Valued.integer (LocalFunctionField k) := by
  exact ((LocalTopology.powerSeriesIntegerEquiv k) f).property

/-- Entrywise integrality of the conjugate is exactly vanishing of the
upper-right residue block. -/
theorem fundamentalIntegralConjugate_entries_mem_integer_iff
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    (∀ i j, fundamentalIntegralConjugate k d r g i j ∈
      Valued.integer (LocalFunctionField k)) ↔
      UpperRightResidueZero k d r g := by
  constructor
  · intro h i j hi hj
    apply constantCoeff_eq_zero_of_uniformizer_inv_mul_mem_integer k
    have hij := h i j
    rw [fundamentalIntegralConjugate_apply] at hij
    simp only [if_pos hi, if_neg (not_lt.mpr hj), mul_one] at hij
    exact hij
  · intro h i j
    rw [fundamentalIntegralConjugate_apply]
    by_cases hi : i.val < r
    · by_cases hj : j.val < r
      · simp only [if_pos hi, if_pos hj]
        rw [show ((uniformizerUnit k)⁻¹ : LocalFunctionField k) *
            integerEmbedding k (g i j) *
              (uniformizerUnit k : LocalFunctionField k) =
            integerEmbedding k (g i j) by
          calc
            _ = ((uniformizerUnit k)⁻¹ : LocalFunctionField k) *
                (uniformizerUnit k : LocalFunctionField k) *
                  integerEmbedding k (g i j) := by ac_rfl
            _ = _ := by simp]
        exact integerEmbedding_mem_integer k (g i j)
      · simp only [if_pos hi, if_neg hj, mul_one]
        rw [uniformizer_inv_mul_integerEmbedding_eq_integerEmbedding_of_constantCoeff_zero
          k (g i j) (h i j hi (not_lt.mp hj))]
        exact integerEmbedding_mem_integer k (powerSeriesTail k (g i j))
    · by_cases hj : j.val < r
      · simp only [if_neg hi, if_pos hj, one_mul]
        change integerEmbedding k (g i j) *
          (uniformizerUnit k : LocalFunctionField k) ∈ _
        have hX : (uniformizerUnit k : LocalFunctionField k) ∈
            Valued.integer (LocalFunctionField k) := by
          simpa [coe_uniformizerUnit, integerEmbedding,
            HahnSeries.ofPowerSeries_X] using
            (integerEmbedding_mem_integer k (PowerSeries.X : IntegerRing k))
        exact (Valued.integer (LocalFunctionField k)).mul_mem
          (integerEmbedding_mem_integer k (g i j)) hX
      · simp only [if_neg hi, if_neg hj, one_mul, mul_one]
        exact integerEmbedding_mem_integer k (g i j)

theorem fundamentalIntegralConjugate_inv
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    (fundamentalIntegralConjugate k d r g)⁻¹ =
      fundamentalIntegralConjugate k d r g⁻¹ := by
  simp [fundamentalIntegralConjugate]
  group

/-- Fundamental diagonal conjugation preserves determinant order zero for
integral invertible matrices. -/
theorem fundamentalIntegralConjugate_det_localUnitOrder_eq_zero
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    localUnitOrder (Matrix.GeneralLinearGroup.det
      (fundamentalIntegralConjugate k d r g)) = 0 := by
  rw [fundamentalIntegralConjugate]
  simp [map_mul, ← powerSeries_integer_local_triangle,
    integralGeneralLinear_det_localUnitOrder_eq_zero]

/-- Full invertible integrality of the conjugate, including its inverse,
is the two-sided residue block condition. -/
theorem fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    fundamentalIntegralConjugate k d r g ∈ integralGeneralLinearSet k d ↔
      UpperRightResidueZero k d r g ∧
        UpperRightResidueZero k d r g⁻¹ := by
  change ((∀ i j, fundamentalIntegralConjugate k d r g i j ∈
      Valued.integer (LocalFunctionField k)) ∧
    ∀ i j, (fundamentalIntegralConjugate k d r g)⁻¹ i j ∈
      Valued.integer (LocalFunctionField k)) ↔ _
  rw [fundamentalIntegralConjugate_inv]
  exact and_congr
    (fundamentalIntegralConjugate_entries_mem_integer_iff k d r g)
    (fundamentalIntegralConjugate_entries_mem_integer_iff k d r g⁻¹)

/-- The power-series upper-right residue condition is literally the
corresponding zero block after reduction modulo `X`. -/
theorem upperRightResidueZero_iff_reduction
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    UpperRightResidueZero k d r g ↔
      ∀ i j : Fin d, i.val < r → r ≤ j.val →
        powerSeriesReductionGL k d g i j = 0 := by
  rfl

/-- Two integral representatives have the same contragredient residue plane
exactly when the inverse relative matrix has zero upper-right residue block. -/
theorem residueFundamentalPlane_eq_iff_upperRight
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h ↔
      UpperRightResidueZero k d r (g⁻¹ * h)⁻¹ := by
  let P := (coordinateGrassmannian k d r hr).1
  let cg := contragredientGeneralLinearHom (powerSeriesReductionGL k d g)
  let ch := contragredientGeneralLinearHom (powerSeriesReductionGL k d h)
  have hmatrix :
      P.map (Matrix.GeneralLinearGroup.toLin cg).val =
          P.map (Matrix.GeneralLinearGroup.toLin ch).val ↔
        UpperRightResidueZero k d r (g⁻¹ * h)⁻¹ := by
    rw [map_generalLinear_eq_map_iff]
    have hrel : cg⁻¹ * ch = contragredientGeneralLinearHom
        (powerSeriesReductionGL k d (g⁻¹ * h)) := by
      simp [cg, ch]
    rw [hrel]
    rw [map_coordinateGrassmannian_eq_self_iff]
    rw [upperRightResidueZero_iff_reduction]
    constructor
    · intro hb i j hi hj
      have hzero := hb j i hj hi
      change (powerSeriesReductionGL k d (g⁻¹ * h))⁻¹ i j = 0 at hzero
      change powerSeriesReductionGL k d ((g⁻¹ * h)⁻¹) i j = 0
      simpa using hzero
    · intro hb i j hi hj
      have hzero := hb j i hj hi
      change powerSeriesReductionGL k d ((g⁻¹ * h)⁻¹) j i = 0 at hzero
      change (powerSeriesReductionGL k d (g⁻¹ * h))⁻¹ j i = 0
      simpa using hzero
  constructor
  · intro h
    apply hmatrix.mp
    have hv := congrArg Subtype.val h
    change P.map (Matrix.GeneralLinearGroup.toLin cg).val =
      P.map (Matrix.GeneralLinearGroup.toLin ch).val at hv
    exact hv
  · intro h
    apply Subtype.ext
    change P.map (Matrix.GeneralLinearGroup.toLin cg).val =
      P.map (Matrix.GeneralLinearGroup.toLin ch).val
    exact hmatrix.mpr h

/-- For an invertible residue matrix, upper-right block vanishing is
preserved by inversion. -/
theorem upperRightResidueZero_inv_iff
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    UpperRightResidueZero k d r g⁻¹ ↔
      UpperRightResidueZero k d r g := by
  have hforward := residueFundamentalPlane_eq_iff_upperRight k d r hr 1 g
  have hbackward := residueFundamentalPlane_eq_iff_upperRight k d r hr g 1
  constructor
  · intro hg
    have heq := hforward.mpr (by simpa using hg)
    have hout := hbackward.mp heq.symm
    simpa using hout
  · intro hg
    have heq := hbackward.mpr (by simpa using hg)
    have hout := hforward.mp heq.symm
    simpa using hout

/-- The contragredient residue-plane map and integral fundamental
conjugation have exactly the same fibers. -/
theorem residueFundamentalPlane_eq_iff_integralConjugate
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h ↔
      fundamentalIntegralConjugate k d r (g⁻¹ * h) ∈
        integralGeneralLinearSet k d := by
  rw [residueFundamentalPlane_eq_iff_upperRight,
    fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff]
  constructor
  · intro hinv
    exact ⟨(upperRightResidueZero_inv_iff k d r hr (g⁻¹ * h)).mp hinv,
      hinv⟩
  · exact fun hpair => hpair.2

end QEC.Coding.HighDimensionalExpander.SphericalHecke
