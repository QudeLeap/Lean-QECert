import QEC.Coding.ExpanderCodes.QuaternionSpecialization
import QEC.Coding.ExpanderCodes.QuadraticTorusIndex

/-!
# Constant-index arithmetic generators in PSL₂

The actual quaternion orbits are transported into PSL₂ through their proved
determinant-square membership. The canonical PSL₂-to-PGL₂ map is injective,
so injectivity, inverse permutations and total nonconjugacy are preserved.
The index and its inverse permutation depend only on the constant field.
No generating-set or spectral conclusion is asserted here.
-/

noncomputable section

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K]
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)

local notation "E" => projectiveMatrixEquivOfRoot (f epsilon) r y hRoot hR hOne hTwo
local notation "L" => indexedLeft f epsilon y hTwoF hY hOne hTwo
local notation "R" => indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo

include hEpsilon hRatio hI

theorem indexedLeft_matrix_mem_psl (t : TorusIndex epsilon) :
    E (L t) ∈ ProjectiveDeterminant.specialProjectiveSubgroup := by
  unfold indexedLeft
  rw [map_mul, map_mul, map_inv]
  apply ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup
  exact (base_prime_matrix_mem_psl_of_root (f epsilon) r y s i
    ((map_ne_zero f).mpr hEpsilon) hRoot hR hY hOne hTwo hRatio hI).1

theorem indexedRight_matrix_mem_psl (t : TorusIndex epsilon) :
    E (R t) ∈ ProjectiveDeterminant.specialProjectiveSubgroup := by
  unfold indexedRight
  rw [map_mul, map_mul, map_inv]
  apply ProjectiveDeterminant.conjugate_mem_specialProjectiveSubgroup
  exact (base_prime_matrix_mem_psl_of_root (f epsilon) r y s i
    ((map_ne_zero f).mpr hEpsilon) hRoot hR hY hOne hTwo hRatio hI).2

def pslLeft (t : TorusIndex epsilon) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  ProjectiveDeterminant.liftToPSL (E (L t))
    (indexedLeft_matrix_mem_psl f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI t)

def pslRight (t : TorusIndex epsilon) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  ProjectiveDeterminant.liftToPSL (E (R t))
    (indexedRight_matrix_mem_psl f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI t)

local notation "PL" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "PR" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI

@[simp] theorem toPGL_pslLeft (t : TorusIndex epsilon) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (PL t) = E (L t) :=
  ProjectiveDeterminant.toPGL_liftToPSL _ _

@[simp] theorem toPGL_pslRight (t : TorusIndex epsilon) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (PR t) = E (R t) :=
  ProjectiveDeterminant.toPGL_liftToPSL _ _

theorem pslLeft_injective : Function.Injective PL := by
  intro a b h
  have hImage := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  simp only [toPGL_pslLeft] at hImage
  exact indexedLeft_injective f epsilon y hEpsilon hTwoF hY hOne hTwo
    ((E).injective hImage)

theorem pslRight_injective : Function.Injective PR := by
  intro a b h
  have hImage := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  simp only [toPGL_pslRight] at hImage
  exact indexedRight_injective f epsilon y hEpsilon hTwoF hY hOne hTwo
    ((E).injective hImage)

theorem pslLeft_inverse (t : TorusIndex epsilon) :
    PL (indexedLeftInverse epsilon hEpsilon t) = (PL t)⁻¹ := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  simp only [toPGL_pslLeft, map_inv]
  rw [indexedLeft_inverse, map_inv]

theorem pslRight_inverse (t : TorusIndex epsilon) : PR t = (PR t)⁻¹ := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  simp only [toPGL_pslRight, map_inv]
  simpa only [map_inv] using congrArg E
    (indexedRight_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo t)

theorem psl_total_nonconjugacy (a b : TorusIndex epsilon)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) : PL a * g ≠ g * PR b := by
  intro h
  have hImage := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  simp only [map_mul, toPGL_pslLeft, toPGL_pslRight] at hImage
  have hOriginal := congrArg (E).symm hImage
  simp only [map_mul, MulEquiv.symm_apply_apply] at hOriginal
  exact indexed_total_nonconjugacy f epsilon y hEpsilon hTwoF hY hOne hTwo a b
    ((E).symm (Matrix.ProjectiveSpecialLinearGroup.toPGL g)) hOriginal

end QEC.Coding.ExpanderCodes.QuaternionGenerators
