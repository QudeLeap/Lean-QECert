import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.CompactNormalForm

/-!
# The projective constant kernel at the building place

The regular representation of the constant extension in the building local
field is proved faithful.  Its projective kernel is then computed exactly:
two represented nonzero constants agree in `PGL_d` precisely when their
ratio lies in `F_qˣ`.  The forward direction is derived from scalar lifting,
the Frobenius commutation relation, and the proved fixed-field theorem.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

theorem buildingConstantMatrix_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingConstantMatrix P r) := by
  intro c d h
  apply constantRegularMatrix_injective P r
  ext i j
  apply (algebraMap (BaseField P) (BuildingLocalField P)).injective
  exact congrFun (congrFun h i) j

theorem buildingConstantMatrix_mul
    (P : BasePrime) (r : Rank) (c d : ConstantExtension P r) :
    buildingConstantMatrix P r c * buildingConstantMatrix P r d =
      buildingConstantMatrix P r (c * d) := by
  change (constantRegularMatrix P r c).map
      (algebraMap (BaseField P) (BuildingLocalField P)) *
    (constantRegularMatrix P r d).map
      (algebraMap (BaseField P) (BuildingLocalField P)) = _
  rw [← Matrix.map_mul, ← map_mul]
  rfl

theorem buildingConstant_conj_frobeniusMatrix
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantMatrix P r u * buildingFrobeniusMatrix P r *
        buildingConstantMatrix P r (u⁻¹ : (ConstantExtension P r)ˣ) =
      buildingConstantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r (u : ConstantExtension P r))⁻¹) *
        buildingFrobeniusMatrix P r := by
  rw [mul_assoc, buildingFrobeniusMatrix_mul_buildingConstantMatrix]
  rw [← mul_assoc, buildingConstantMatrix_mul]
  congr 1
  congr 2
  simp

set_option maxHeartbeats 400000 in
theorem quotientMk_eq_of_buildingConstantPGL_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : buildingConstantPGLHom P r u = buildingConstantPGLHom P r v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by
  change Matrix.ProjGenLinGroup.mk (buildingConstantGL P r u) =
    Matrix.ProjGenLinGroup.mk (buildingConstantGL P r v) at h
  obtain ⟨a, ha⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq h
  let U := buildingConstantGL P r u
  let V := buildingConstantGL P r v
  let S := Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) a
  have hUV : U = S * V := ha
  have hScomm (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
      (S : Matrix _ _ _) * M = M * (S : Matrix _ _ _) := by
    dsimp [S]
    exact Matrix.scalar_comm _ (fun b => Commute.all _ b) M
  have hScancel (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (BuildingLocalField P)) :
      (S : Matrix _ _ _) * M *
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _) = M := by
    rw [hScomm]
    simp only [mul_assoc]
    rw [← Units.val_mul]
    simp
  have hconj :
      (U : Matrix _ _ _) * buildingFrobeniusMatrix P r *
          ((U⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) =
        (V : Matrix _ _ _) * buildingFrobeniusMatrix P r *
          ((V⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) := by
    rw [hUV]
    calc
      (((S * V : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _) *
          buildingFrobeniusMatrix P r *
          (((S * V)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _)) =
        (S : Matrix _ _ _) *
          ((V : Matrix _ _ _) * buildingFrobeniusMatrix P r *
            ((V⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _)) *
          ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (BuildingLocalField P)) : Matrix _ _ _) := by
              simp only [mul_inv_rev, Units.val_mul]
              group
      _ = _ := by
        let M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingLocalField P) :=
          (V : Matrix _ _ _) * buildingFrobeniusMatrix P r *
            ((V⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _)
        calc
          _ = (S : Matrix _ _ _) * M *
              ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                (BuildingLocalField P)) : Matrix _ _ _) := by
                  dsimp [M]
          _ = M := hScancel M
          _ = _ := by dsimp [M]
  have hratioMatrix : buildingConstantMatrix P r
        ((u : ConstantExtension P r) *
          (constantFrobenius P r (u : ConstantExtension P r))⁻¹) =
      buildingConstantMatrix P r
        ((v : ConstantExtension P r) *
          (constantFrobenius P r (v : ConstantExtension P r))⁻¹) := by
    have hprod : buildingConstantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r (u : ConstantExtension P r))⁻¹) *
          buildingFrobeniusMatrix P r =
        buildingConstantMatrix P r
          ((v : ConstantExtension P r) *
            (constantFrobenius P r (v : ConstantExtension P r))⁻¹) *
          buildingFrobeniusMatrix P r := by
      rw [← buildingConstant_conj_frobeniusMatrix P r u,
        ← buildingConstant_conj_frobeniusMatrix P r v]
      exact hconj
    have hc := congrArg (fun M => M *
      (((buildingFrobeniusGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) : Matrix _ _ _)) hprod
    change buildingConstantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r (u : ConstantExtension P r))⁻¹) *
          ((buildingFrobeniusGL P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (BuildingLocalField P)) : Matrix _ _ _) *
          (((buildingFrobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _) =
      buildingConstantMatrix P r
          ((v : ConstantExtension P r) *
            (constantFrobenius P r (v : ConstantExtension P r))⁻¹) *
          ((buildingFrobeniusGL P r : Matrix.GeneralLinearGroup
            (Fin r.matrixRank) (BuildingLocalField P)) : Matrix _ _ _) *
          (((buildingFrobeniusGL P r)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (BuildingLocalField P)) : Matrix _ _ _) at hc
    simpa only [mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, mul_one] using hc
  have hratio := buildingConstantMatrix_injective P r hratioMatrix
  have hfu : constantFrobenius P r (u : ConstantExtension P r) ≠ 0 := by simp
  have hfv : constantFrobenius P r (v : ConstantExtension P r) ≠ 0 := by simp
  have hcross : (u : ConstantExtension P r) *
      constantFrobenius P r (v : ConstantExtension P r) =
    (v : ConstantExtension P r) *
      constantFrobenius P r (u : ConstantExtension P r) := by
    apply (div_eq_div_iff hfu hfv).mp
    simpa [div_eq_mul_inv] using hratio
  have hfixed : constantFrobenius P r
      ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
    (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have hdiv : constantFrobenius P r (u : ConstantExtension P r) /
        constantFrobenius P r (v : ConstantExtension P r) =
      (u : ConstantExtension P r) / (v : ConstantExtension P r) := by
      apply (div_eq_div_iff hfv (Units.ne_zero v)).mpr
      simpa [mul_comm] using hcross.symm
    simpa [map_mul, map_inv, div_eq_mul_inv] using hdiv
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_constantFrobenius_eq P r _ hfixed
  have hc0 : c ≠ 0 := by
    intro hcZero
    rw [hcZero, map_zero] at hc
    exact (mul_ne_zero (Units.ne_zero u) (inv_ne_zero (Units.ne_zero v))) hc.symm
  apply QuotientGroup.eq_iff_div_mem.mpr
  change u / v ∈ baseScalarUnits P r
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simpa [baseScalarUnitHom, div_eq_mul_inv] using hc

theorem buildingConstantPGL_eq_of_quotientMk_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v) :
    buildingConstantPGLHom P r u = buildingConstantPGLHom P r v := by
  have hdiv : u / v ∈ baseScalarUnits P r :=
    QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨a, ha⟩ := hdiv
  apply div_eq_one.mp
  rw [← map_div, ← ha]
  simpa [baseScalarUnitHom] using
    buildingConstantPGLHom_map_baseUnit_eq_one P r a

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
