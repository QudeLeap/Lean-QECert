import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quaternion generators with separated projective squares

This is the coefficient-field quaternion model of [DEL21, Section 6.2,
Claims 6.5 and 6.7]. The relations and inverses below are calculated from
coordinates. Quotienting the unit group by its center is explicit; no
identification with a finite PSL₂ group or spectral estimate is asserted.

The model uses `i² = epsilon`, `j² = 1 + y`, and `ji = -ij`. In particular
the fourth term of its reduced norm has a **plus** sign; the minus sign in
the displayed coordinate norm in the pinned DEL21 v2 text is not assumed.
-/

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

universe u

variable {K : Type u} [Field K]

/-- The odd-characteristic arithmetic quaternion presentation. -/
abbrev Model (epsilon y : K) := QuaternionAlgebra K epsilon 0 (1 + y)

/-- The quadratic constant generator. -/
def alpha (epsilon y : K) : Model epsilon y := ⟨0, 1, 0, 0⟩

/-- The skew generator. -/
def z (epsilon y : K) : Model epsilon y := ⟨0, 0, 1, 0⟩

/-- The generator `1 - z / (1 + y)`. -/
def base (epsilon y : K) : Model epsilon y := ⟨1, 0, -(1 + y)⁻¹, 0⟩

/-- The generator `alpha * base`. -/
def prime (epsilon y : K) : Model epsilon y := ⟨0, 1, 0, -(1 + y)⁻¹⟩

theorem alpha_sq (epsilon y : K) : alpha epsilon y ^ 2 = (epsilon : Model epsilon y) := by
  ext <;> simp [alpha, pow_two]

theorem z_sq (epsilon y : K) : z epsilon y ^ 2 = ((1 + y : K) : Model epsilon y) := by
  ext <;> simp [z, pow_two]

theorem z_mul_alpha (epsilon y : K) : z epsilon y * alpha epsilon y =
    -(alpha epsilon y * z epsilon y) := by
  ext <;> simp [z, alpha]

theorem alpha_mul_base (epsilon y : K) : alpha epsilon y * base epsilon y =
    prime epsilon y := by
  ext <;> simp [alpha, base, prime]

theorem base_sq (epsilon y : K) (hOne : 1 + y ≠ 0) :
    base epsilon y ^ 2 = ⟨1 + (1 + y)⁻¹, 0, -(2 * (1 + y)⁻¹), 0⟩ := by
  ext <;> simp [base, pow_two] <;> field_simp <;> ring

theorem prime_sq (epsilon y : K) (hOne : 1 + y ≠ 0) :
    prime epsilon y ^ 2 = ((epsilon * y / (1 + y) : K) : Model epsilon y) := by
  ext <;> simp [prime, pow_two] <;> field_simp <;> ring

/-- The norm dictated by the multiplication and conjugation operations. -/
theorem reduced_norm (epsilon y : K) (q : Model epsilon y) :
    (star q * q).re = q.re ^ 2 - epsilon * q.imI ^ 2 -
      (1 + y) * q.imJ ^ 2 + epsilon * (1 + y) * q.imK ^ 2 := by
  rcases q with ⟨a, b, c, d⟩
  simp
  ring

/-- The actual unit with value `alpha`. -/
def alphaUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0) : (Model epsilon y)ˣ where
  val := alpha epsilon y
  inv := ⟨0, epsilon⁻¹, 0, 0⟩
  val_inv := by ext <;> simp [alpha, hEpsilon]
  inv_val := by ext <;> simp [alpha, hEpsilon]

/-- The actual unit with value `base`; the inverse is not an input. -/
def baseUnit (epsilon y : K) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (Model epsilon y)ˣ where
  val := base epsilon y
  inv := ⟨(1 + y) / y, 0, y⁻¹, 0⟩
  val_inv := by ext <;> simp [base] <;> field_simp <;> ring
  inv_val := by ext <;> simp [base] <;> field_simp <;> ring

/-- The second unit is constructed by multiplication of the first two. -/
def primeUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : (Model epsilon y)ˣ :=
  alphaUnit epsilon y hEpsilon * baseUnit epsilon y hY hOne

@[simp] theorem val_alphaUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    (alphaUnit epsilon y hEpsilon : Model epsilon y) = alpha epsilon y := rfl

@[simp] theorem val_baseUnit (epsilon y : K) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (baseUnit epsilon y hY hOne : Model epsilon y) = base epsilon y := rfl

@[simp] theorem val_primeUnit (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (primeUnit epsilon y hEpsilon hY hOne : Model epsilon y) = prime epsilon y := by
  exact alpha_mul_base epsilon y

/-- The projective group used here is exactly the units modulo their center. -/
abbrev ProjectiveGroup (epsilon y : K) :=
  (Model epsilon y)ˣ ⧸ Subgroup.center (Model epsilon y)ˣ

def projectiveBase (epsilon y : K) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    ProjectiveGroup epsilon y :=
  QuotientGroup.mk' _ (baseUnit epsilon y hY hOne)

def projectivePrime (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : ProjectiveGroup epsilon y :=
  QuotientGroup.mk' _ (primeUnit epsilon y hEpsilon hY hOne)

theorem mem_center_of_val_scalar {epsilon y : K} (a : (Model epsilon y)ˣ)
    (r : K) (hScalar : (a : Model epsilon y) = (r : Model epsilon y)) :
    a ∈ Subgroup.center (Model epsilon y)ˣ := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Units.ext
  change (g : Model epsilon y) * (a : Model epsilon y) =
    (a : Model epsilon y) * (g : Model epsilon y)
  rw [hScalar]
  exact (QuaternionAlgebra.coe_commutes r (g : Model epsilon y)).symm

/-- The second generator has projective square one by its explicit quaternion square. -/
theorem projectivePrime_sq (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectivePrime epsilon y hEpsilon hY hOne ^ 2 = 1 := by
  change ((primeUnit epsilon y hEpsilon hY hOne : ProjectiveGroup epsilon y) ^ 2) = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply mem_center_of_val_scalar _ (epsilon * y / (1 + y))
  simpa using prime_sq epsilon y hOne

/-- The first generator is not a projective involution in odd characteristic. -/
theorem projectiveBase_sq_ne_one (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveBase epsilon y hY hOne ^ 2 ≠ 1 := by
  intro hSquare
  change ((baseUnit epsilon y hY hOne : ProjectiveGroup epsilon y) ^ 2) = 1 at hSquare
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hSquare
  have hCommute := Subgroup.mem_center_iff.mp hSquare (alphaUnit epsilon y hEpsilon)
  have hCoordinate := congrArg (fun a : (Model epsilon y)ˣ =>
    (a : Model epsilon y).imK) hCommute
  have hBaseSquare : ((baseUnit epsilon y hY hOne) ^ 2 : (Model epsilon y)ˣ) =
      baseUnit epsilon y hY hOne * baseUnit epsilon y hY hOne := pow_two _
  rw [hBaseSquare] at hCoordinate
  simp [alpha, base] at hCoordinate
  have hFour : (4 : K) = 0 := by
    field_simp at hCoordinate
    linear_combination -hCoordinate
  apply mul_ne_zero hTwo hTwo
  calc
    (2 : K) * 2 = 4 := by ring
    _ = 0 := hFour

/-- The second projective generator is nonidentity, so its square-one
property is not merely the trivial element. -/
theorem projectivePrime_ne_one (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectivePrime epsilon y hEpsilon hY hOne ≠ 1 := by
  intro hIdentity
  change (primeUnit epsilon y hEpsilon hY hOne : ProjectiveGroup epsilon y) = 1
    at hIdentity
  rw [QuotientGroup.eq_one_iff] at hIdentity
  have hCommute := Subgroup.mem_center_iff.mp hIdentity (alphaUnit epsilon y hEpsilon)
  have hCoordinate := congrArg (fun a : (Model epsilon y)ˣ =>
    (a : Model epsilon y).imJ) hCommute
  simp [alpha, prime] at hCoordinate
  apply hTwo
  field_simp at hCoordinate
  linear_combination -hCoordinate

section Group

variable {H : Type*} [Group H]

/-- An involution cannot be conjugate to an element whose square is nontrivial. -/
theorem mul_ne_mul_of_separated_squares (a b g : H) (ha : a ^ 2 ≠ 1)
    (hb : b ^ 2 = 1) : a * g ≠ g * b := by
  intro hEqual
  have hConjugate : a = g * b * g⁻¹ := by
    calc
      a = a * g * g⁻¹ := by simp [mul_assoc]
      _ = g * b * g⁻¹ := by rw [hEqual]
  apply ha
  rw [hConjugate, conj_pow, hb]
  simp

/-- Nontriviality of a square is preserved by conjugation. -/
theorem conjugate_sq_ne_one (a t : H) (ha : a ^ 2 ≠ 1) :
    (t * a * t⁻¹) ^ 2 ≠ 1 := by
  intro hSquare
  apply ha
  rw [conj_pow] at hSquare
  have hCancel := congrArg (fun x => t⁻¹ * x * t) hSquare
  simpa [mul_assoc] using hCancel

end Group

/-- The actual quaternion generators, and all their conjugates, satisfy the
total-nonconjugacy equation used by the left/right square construction. -/
theorem conjugates_total_nonconjugacy (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (s t g : ProjectiveGroup epsilon y) :
    (s * projectiveBase epsilon y hY hOne * s⁻¹) * g ≠
      g * (t * projectivePrime epsilon y hEpsilon hY hOne * t⁻¹) := by
  apply mul_ne_mul_of_separated_squares
  · exact conjugate_sq_ne_one _ s
      (projectiveBase_sq_ne_one epsilon y hEpsilon hY hOne hTwo)
  · rw [conj_pow, projectivePrime_sq epsilon y hEpsilon hY hOne]
    simp

end QEC.Coding.ExpanderCodes.QuaternionGenerators
