import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The determinant-square obstruction to PSL₂

The image of SL₂ in PGL₂ consists exactly of projective classes whose
determinant is a square. The proof constructs the determinant-one lift by
rescaling an actual matrix. In particular, a split quaternion presentation
does not by itself put its generators in PSL₂.
-/

namespace QEC.Coding.ExpanderCodes.ProjectiveDeterminant

open Matrix

variable {K : Type*} [Field K]

/-- The canonical PSL₂ image inside PGL₂, expressed as the image of SL₂. -/
def specialProjectiveSubgroup : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K) :=
  Matrix.SpecialLinearGroup.toPGL.range

/-- This subgroup is also the image of the canonical injective map from PSL₂. -/
theorem specialProjectiveSubgroup_eq_psl_range :
    specialProjectiveSubgroup (K := K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨QuotientGroup.mk s, rfl⟩
  · rintro ⟨s, rfl⟩
    induction s using Quotient.inductionOn with
    | h s => exact ⟨s, rfl⟩

/-- A matrix class has a determinant-one representative precisely when its
unit determinant has an actual square root. -/
theorem mk_mem_specialProjectiveSubgroup_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk g ∈ specialProjectiveSubgroup ↔
      ∃ r : Kˣ, r ^ 2 = Matrix.GeneralLinearGroup.det g := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hs
    refine ⟨r, ?_⟩
    have hDet := congrArg Matrix.GeneralLinearGroup.det hr
    simpa using hDet
  · rintro ⟨r, hr⟩
    have hDet : Matrix.GeneralLinearGroup.det
        (g * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹) = 1 := by
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
        ← hr, inv_pow, mul_inv_cancel]
    let s : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨(g * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹).val,
        congrArg Units.val hDet⟩
    refine ⟨s, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) =
      Matrix.ProjGenLinGroup.mk g
    have hs : Matrix.SpecialLinearGroup.toGL s =
        g * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹ := Units.ext rfl
    rw [hs, map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]

/-- The unit-square criterion is equivalent to the usual field-square criterion. -/
theorem mk_mem_specialProjectiveSubgroup_iff_field_square
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.ProjGenLinGroup.mk g ∈ specialProjectiveSubgroup ↔
      ∃ r : K, r ^ 2 = (Matrix.GeneralLinearGroup.det g : K) := by
  rw [mk_mem_specialProjectiveSubgroup_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, congrArg Units.val hr⟩
  · rintro ⟨r, hr⟩
    have hR : r ≠ 0 := by
      intro hZero
      exact (Matrix.GeneralLinearGroup.det g).ne_zero
        (by simpa [hZero] using hr.symm)
    exact ⟨Units.mk0 r hR, Units.ext (by simpa using hr)⟩

/-- The determinant-square subgroup is invariant under every projective conjugation. -/
theorem conjugate_mem_specialProjectiveSubgroup (c g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) :
    c * g * c⁻¹ ∈ specialProjectiveSubgroup := by
  induction c using Matrix.ProjGenLinGroup.induction_on with | mk c =>
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  rw [mk_mem_specialProjectiveSubgroup_iff] at hg
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_specialProjectiveSubgroup_iff]
  obtain ⟨r, hr⟩ := hg
  refine ⟨r, ?_⟩
  simpa [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc] using hr

/-- The unique PSL₂ preimage of an actual member of its projective image. -/
noncomputable def liftToPSL (g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  (MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm
    ⟨g, by rwa [← specialProjectiveSubgroup_eq_psl_range]⟩

@[simp] theorem toPGL_liftToPSL (g : Matrix.ProjGenLinGroup (Fin 2) K)
    (hg : g ∈ specialProjectiveSubgroup) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (liftToPSL g hg) = g :=
  MonoidHom.apply_ofInjective_symm Matrix.ProjectiveSpecialLinearGroup.toPGL_injective _

end QEC.Coding.ExpanderCodes.ProjectiveDeterminant
