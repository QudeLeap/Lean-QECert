import QEC.Coding.ExpanderCodes.QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Inverse-closed quaternion conjugacy sets

The coefficient-quadratic unit centralizer and its projective image are actual
subgroups. Their conjugacy sets satisfy inverse closure and total
nonconjugacy by coordinate calculations [DEL21, Section 6.2]. This file does
not yet identify a finite residue group, count the torus, or prove a spectrum.
-/

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

universe u

variable {K : Type u} [Field K]

def projectiveAlpha (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    ProjectiveGroup epsilon y :=
  QuotientGroup.mk' _ (alphaUnit epsilon y hEpsilon)

/-- The inverse of the first generator is conjugate by the quadratic unit. -/
theorem projectiveAlpha_conjugate_base (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectiveAlpha epsilon y hEpsilon * projectiveBase epsilon y hY hOne *
      (projectiveAlpha epsilon y hEpsilon)⁻¹ =
        (projectiveBase epsilon y hY hOne)⁻¹ := by
  have hScalar :
      ((alphaUnit epsilon y hEpsilon * baseUnit epsilon y hY hOne *
        (alphaUnit epsilon y hEpsilon)⁻¹ * baseUnit epsilon y hY hOne) :
          Model epsilon y) = ((y / (1 + y) : K) : Model epsilon y) := by
    ext <;> simp [alphaUnit, baseUnit, alpha, base] <;> field_simp <;> ring
  have hCentral := mem_center_of_val_scalar
    (alphaUnit epsilon y hEpsilon * baseUnit epsilon y hY hOne *
      (alphaUnit epsilon y hEpsilon)⁻¹ * baseUnit epsilon y hY hOne)
    (y / (1 + y)) hScalar
  have hProduct := (QuotientGroup.eq_one_iff _).mpr hCentral
  apply mul_eq_one_iff_eq_inv.mp
  simpa [projectiveAlpha, projectiveBase, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv] using hProduct

/-- The projective image of units commuting with the quadratic generator.
The finite-field torus cardinality is a separate theorem, not an input here. -/
def quadraticTorus (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    Subgroup (ProjectiveGroup epsilon y) :=
  (Subgroup.centralizer {alphaUnit epsilon y hEpsilon}).map
    (QuotientGroup.mk' _)

theorem projectiveAlpha_mem_quadraticTorus (epsilon y : K)
    (hEpsilon : epsilon ≠ 0) :
    projectiveAlpha epsilon y hEpsilon ∈ quadraticTorus epsilon y hEpsilon := by
  refine ⟨alphaUnit epsilon y hEpsilon, ?_, rfl⟩
  simp [Subgroup.mem_centralizer_iff]

section Group

variable {H : Type*} [Group H]

/-- The conjugacy set parametrized by an actual subgroup. -/
def conjugacySet (T : Subgroup H) (a : H) : Set H :=
  Set.range (fun t : T => (t : H) * a * (t : H)⁻¹)

/-- One conjugation realizing the inverse makes the whole orbit inverse closed. -/
theorem inv_mem_conjugacySet (T : Subgroup H) (a u : H) (hu : u ∈ T)
    (hInverse : u * a * u⁻¹ = a⁻¹) {g : H} (hg : g ∈ conjugacySet T a) :
    g⁻¹ ∈ conjugacySet T a := by
  obtain ⟨t, rfl⟩ := hg
  refine ⟨t * ⟨u, hu⟩, ?_⟩
  change ((t : H) * u) * a * ((t : H) * u)⁻¹ =
    ((t : H) * a * (t : H)⁻¹)⁻¹
  calc
    _ = (t : H) * (u * a * u⁻¹) * (t : H)⁻¹ := by simp [mul_assoc]
    _ = (t : H) * a⁻¹ * (t : H)⁻¹ := by rw [hInverse]
    _ = _ := by simp [mul_assoc]

theorem inv_mem_conjugacySet_of_sq_one (T : Subgroup H) (a : H)
    (hSquare : a ^ 2 = 1) {g : H} (hg : g ∈ conjugacySet T a) :
    g⁻¹ ∈ conjugacySet T a := by
  apply inv_mem_conjugacySet T a 1 T.one_mem _ hg
  simpa using (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hSquare)).symm

/-- Separated squares prove nonconjugacy for all members of both orbits. -/
theorem conjugacySet_total_nonconjugacy (T U : Subgroup H) (a b : H)
    (ha : a ^ 2 ≠ 1) (hb : b ^ 2 = 1)
    {x y : H} (hx : x ∈ conjugacySet T a) (hy : y ∈ conjugacySet U b) (g : H) :
    x * g ≠ g * y := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  apply mul_ne_mul_of_separated_squares
  · exact conjugate_sq_ne_one a s ha
  · rw [conj_pow, hb]
    simp

end Group

/-- The first arithmetic conjugacy set. -/
def leftSet (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Set (ProjectiveGroup epsilon y) :=
  conjugacySet (quadraticTorus epsilon y hEpsilon)
    (projectiveBase epsilon y hY hOne)

/-- The second arithmetic conjugacy set. -/
def rightSet (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Set (ProjectiveGroup epsilon y) :=
  conjugacySet (quadraticTorus epsilon y hEpsilon)
    (projectivePrime epsilon y hEpsilon hY hOne)

theorem leftSet_inv_mem (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) {g : ProjectiveGroup epsilon y}
    (hg : g ∈ leftSet epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ leftSet epsilon y hEpsilon hY hOne :=
  inv_mem_conjugacySet _ _ _ (projectiveAlpha_mem_quadraticTorus epsilon y hEpsilon)
    (projectiveAlpha_conjugate_base epsilon y hEpsilon hY hOne) hg

theorem rightSet_inv_mem (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) {g : ProjectiveGroup epsilon y}
    (hg : g ∈ rightSet epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ rightSet epsilon y hEpsilon hY hOne :=
  inv_mem_conjugacySet_of_sq_one _ _
    (projectivePrime_sq epsilon y hEpsilon hY hOne) hg

theorem leftSet_rightSet_total_nonconjugacy (epsilon y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) {a b : ProjectiveGroup epsilon y}
    (ha : a ∈ leftSet epsilon y hEpsilon hY hOne)
    (hb : b ∈ rightSet epsilon y hEpsilon hY hOne) (g : ProjectiveGroup epsilon y) :
    a * g ≠ g * b :=
  conjugacySet_total_nonconjugacy _ _ _ _
    (projectiveBase_sq_ne_one epsilon y hEpsilon hY hOne hTwo)
    (projectivePrime_sq epsilon y hEpsilon hY hOne) ha hb g

end QEC.Coding.ExpanderCodes.QuaternionGenerators
