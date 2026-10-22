import QEC.Coding.ExpanderCodes.QuaternionCayleySets
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Coset.Card
import Lean.Elab.Tactic.Omega

/-!
# Constant-field quadratic torus

Unlike the full coefficient-field centralizer, this subgroup is the image of
the units of the quadratic algebra over the chosen **constant field**. Its
projective kernel is exactly the constant scalars. For a finite field with a
nonsquare parameter this proves the `q + 1` torus cardinality in [DEL21,
Section 6.2], without assuming the cardinality or a finite PSL₂ identification.
-/

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

open scoped QuadraticAlgebra

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K]

/-- Coordinate embedding of the constant quadratic algebra. -/
def coefficientEmbedding (f : F →+* K) (epsilon : F) (y : K) :
    QuadraticAlgebra F epsilon 0 →+* Model (f epsilon) y where
  toFun a := ⟨f a.re, f a.im, 0, 0⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem coefficientEmbedding_injective (f : F →+* K) (epsilon : F) (y : K) :
    Function.Injective (coefficientEmbedding f epsilon y) := by
  intro a b h
  ext
  · exact f.injective (congrArg QuaternionAlgebra.re h)
  · exact f.injective (congrArg QuaternionAlgebra.imI h)

/-- The actual homomorphism of constant quadratic units to the projective group. -/
def constantProjectiveMap (f : F →+* K) (epsilon : F) (y : K) :
    (QuadraticAlgebra F epsilon 0)ˣ →* ProjectiveGroup (f epsilon) y :=
  (QuotientGroup.mk' _).comp
    (Units.map (coefficientEmbedding f epsilon y).toMonoidHom)

def constantTorus (f : F →+* K) (epsilon : F) (y : K) :
    Subgroup (ProjectiveGroup (f epsilon) y) :=
  (constantProjectiveMap f epsilon y).range

/-- The skew element is invertible away from `y = -1`. -/
def skewUnit (epsilon y : K) (hOne : 1 + y ≠ 0) : (Model epsilon y)ˣ where
  val := z epsilon y
  inv := ⟨0, 0, (1 + y)⁻¹, 0⟩
  val_inv := by ext <;> simp [z, hOne]
  inv_val := by ext <;> simp [z, hOne]

/-- Projectivizing kills exactly the constant scalar units, not the entire
quadratic unit group. The nontrivial direction uses a genuine skew unit. -/
theorem constantProjectiveMap_eq_one_iff (f : F →+* K) (epsilon : F) (y : K)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ) :
    constantProjectiveMap f epsilon y a = 1 ↔ (a : QuadraticAlgebra F epsilon 0).im = 0 := by
  let image := Units.map (coefficientEmbedding f epsilon y).toMonoidHom a
  change (image : ProjectiveGroup (f epsilon) y) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hCenter
    have hCommute := Subgroup.mem_center_iff.mp hCenter (skewUnit (f epsilon) y hOne)
    have hCoordinate := congrArg (fun b : (Model (f epsilon) y)ˣ =>
      (b : Model (f epsilon) y).imK) hCommute
    simp [image, coefficientEmbedding, skewUnit, z] at hCoordinate
    have hDouble : (2 : K) * f (a : QuadraticAlgebra F epsilon 0).im = 0 := by
      linear_combination -hCoordinate
    have hZero := (mul_eq_zero.mp hDouble).resolve_left hTwo
    exact f.injective (by simpa using hZero)
  · intro hImag
    apply mem_center_of_val_scalar image (f (a : QuadraticAlgebra F epsilon 0).re)
    ext <;> simp [image, coefficientEmbedding, hImag]

/-- Extract the scalar unit from a quadratic unit with zero imaginary part. -/
def scalarUnitOfZeroImag (epsilon : F) (a : (QuadraticAlgebra F epsilon 0)ˣ)
    (hImag : (a : QuadraticAlgebra F epsilon 0).im = 0) : Fˣ where
  val := (a : QuadraticAlgebra F epsilon 0).re
  inv := a.inv.re
  val_inv := by
    have h := congrArg QuadraticAlgebra.re a.val_inv
    simpa only [QuadraticAlgebra.re_mul, hImag, mul_zero, zero_mul, add_zero,
      QuadraticAlgebra.re_one] using h
  inv_val := by
    have h := congrArg QuadraticAlgebra.re a.val_inv
    simpa only [QuadraticAlgebra.re_mul, hImag, mul_zero, zero_mul, add_zero,
      QuadraticAlgebra.re_one, mul_comm] using h

/-- The projective kernel is bijective with the units of the constant field. -/
def constantKernelEquiv (f : F →+* K) (epsilon : F) (y : K)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    (constantProjectiveMap f epsilon y).ker ≃ Fˣ where
  toFun a := scalarUnitOfZeroImag epsilon a.val
    ((constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo a.val).mp a.property)
  invFun a := ⟨Units.map (algebraMap F (QuadraticAlgebra F epsilon 0)).toMonoidHom a,
    (constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo _).mpr (by simp)⟩
  left_inv a := by
    apply Subtype.ext
    apply Units.ext
    ext
    · rfl
    · exact ((constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo a.val).mp
        a.property).symm
  right_inv a := by
    apply Units.ext
    rfl

/-- The constant nonsplit torus has exactly `q + 1` elements even when the
coefficient field is much larger than the constant field. -/
theorem card_constantTorus (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Nat.card (constantTorus f epsilon y) = Fintype.card F + 1 := by
  classical
  letI : Fact (∀ r : F, r ^ 2 ≠ epsilon + 0 * r) :=
    ⟨fun r => by simpa using hNonSquare r⟩
  letI : Fintype (QuadraticAlgebra F epsilon 0) :=
    Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd epsilon 0).symm
  have hQuadraticCard : Nat.card (QuadraticAlgebra F epsilon 0) =
      Fintype.card F * Fintype.card F := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd epsilon 0), Nat.card_prod,
      Nat.card_eq_fintype_card]
  have hKernelCard : Nat.card (constantProjectiveMap f epsilon y).ker =
      Fintype.card F - 1 := by
    rw [Nat.card_congr (constantKernelEquiv f epsilon y hOne hTwo),
      Nat.card_units, Nat.card_eq_fintype_card]
  have hProduct := (constantProjectiveMap f epsilon y).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_units, hQuadraticCard, hKernelCard,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (constantProjectiveMap f epsilon y)).toEquiv] at hProduct
  have hFieldCard : 1 < Fintype.card F := Fintype.one_lt_card
  have hFactor : Fintype.card F * Fintype.card F - 1 =
      (Fintype.card F + 1) * (Fintype.card F - 1) := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Fintype.card_pos (α := F)))
    rw [hq]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    have hIdentity : (q + 1) * (q + 1) = (q + 1 + 1) * q + 1 := by ring
    omega
  change Nat.card (constantProjectiveMap f epsilon y).range = _
  exact Nat.eq_of_mul_eq_mul_right (by omega)
    (hProduct.symm.trans hFactor)

end QEC.Coding.ExpanderCodes.QuaternionGenerators
