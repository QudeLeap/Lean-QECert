import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import QEC.Coding.AlgebraicGeometry.Adeles.Adele
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PlaceIncrementDimension

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Exact one-place increments of the intrinsic adele filtration

At an actual global place `P`, scaling the `P`-component by the normalized
uniformizer produces a leading-coefficient map from `A(D + P)` to the actual
residue field.  This file proves that its kernel is exactly `A(D)`, that it is
surjective, and hence that the one-place quotient has dimension `deg(P)`.

The proof architecture is adapted to Lean-QEC's intrinsic place API from
Guanghao Li's Apache-2.0 formalization
`vaca22/riemann-roch-function-fields`.  It makes no duality, genus, or
Riemann--Roch assumption.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

noncomputable section

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

private theorem globalAdele_exp_neg_mul_lt_one_iff_le (x : ℤᵐ⁰) (n : ℤ) :
    WithZero.exp (-n) * x < 1 ↔ x ≤ WithZero.exp (n - 1) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← WithZero.log_lt_log (mul_ne_zero WithZero.exp_ne_zero hx) one_ne_zero]
  rw [WithZero.log_mul WithZero.exp_ne_zero hx, WithZero.log_exp,
    WithZero.log_one]
  rw [← WithZero.log_le_iff_le_exp hx]
  omega

private theorem globalAdele_localParameterPower_valuation
    (P : GlobalPlace k F) (n : ℤ) :
    P.valuation (Differential.localParameterPower P n) = WithZero.exp (-n) := by
  rw [Differential.localParameterPower, Units.val_zpow_eq_zpow_val, map_zpow₀,
    Differential.localParameterUnit, Units.val_mk0,
    Differential.localParameter, P.valuation_uniformizer,
    ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem globalAdele_localParameterPower_ne_zero
    (P : GlobalPlace k F) (n : ℤ) :
    Differential.localParameterPower P n ≠ 0 :=
  Units.ne_zero _

/-- The valuation-ring-valued leading coefficient of an adele in `A(D + P)`
at its distinguished place. -/
private noncomputable def globalAdeleLocalLeadingCoefficientValue
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (a : globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :
    P.valuationRing :=
  ⟨Differential.localParameterPower P (D P + 1) *
      ((a.val : GlobalAdele (k := k) (F := F)).val P), by
    rw [mem_valuationRing_iff, map_mul,
      globalAdele_localParameterPower_valuation]
    have ha := a.property P
    simp only [Finsupp.add_apply, placeDivisor_apply] at ha
    calc
      WithZero.exp (-(D P + 1)) *
          P.valuation ((a.val : GlobalAdele (k := k) (F := F)).val P) ≤
          WithZero.exp (-(D P + 1)) * WithZero.exp (D P + 1) :=
        mul_le_mul_right ha _
      _ = 1 := by
        rw [← WithZero.exp_add]
        simp⟩

private theorem globalAdeleLocalLeadingCoefficientValue_add
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (a b : globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :
    globalAdeleLocalLeadingCoefficientValue D P (a + b) =
      globalAdeleLocalLeadingCoefficientValue D P a +
        globalAdeleLocalLeadingCoefficientValue D P b := by
  apply Subtype.ext
  change Differential.localParameterPower P (D P + 1) *
      (((a.val : GlobalAdele (k := k) (F := F)).val P) +
        ((b.val : GlobalAdele (k := k) (F := F)).val P)) = _
  exact mul_add _ _ _

private theorem globalAdeleLocalLeadingCoefficientValue_smul
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (c : k)
    (a : globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :
    globalAdeleLocalLeadingCoefficientValue D P (c • a) =
      constantsToValuationRing P c *
        globalAdeleLocalLeadingCoefficientValue D P a := by
  apply Subtype.ext
  calc
    ((globalAdeleLocalLeadingCoefficientValue D P (c • a) :
        P.valuationRing) : F) =
        Differential.localParameterPower P (D P + 1) *
          (algebraMap k F c *
            ((a.val : GlobalAdele (k := k) (F := F)).val P)) := by
      simp only [globalAdeleLocalLeadingCoefficientValue,
        Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
    _ = algebraMap k F c *
        (Differential.localParameterPower P (D P + 1) *
          ((a.val : GlobalAdele (k := k) (F := F)).val P)) := by
      ring
    _ = ((constantsToValuationRing P c *
        globalAdeleLocalLeadingCoefficientValue D P a :
          P.valuationRing) : F) := rfl

/-- Reduction of the actual one-place adele leading coefficient. -/
noncomputable def globalAdeleLocalLeadingCoefficient
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) →ₗ[k]
      P.residueField := by
  letI : Algebra k P.residueField := residueAlgebra P
  refine
    { toFun := fun a => P.residue (globalAdeleLocalLeadingCoefficientValue D P a)
      map_add' := ?_
      map_smul' := ?_ }
  · intro a b
    rw [globalAdeleLocalLeadingCoefficientValue_add, map_add]
  · intro c a
    rw [globalAdeleLocalLeadingCoefficientValue_smul, map_mul]
    change constantsToResidue P c *
        P.residue (globalAdeleLocalLeadingCoefficientValue D P a) =
      algebraMap k P.residueField c *
        P.residue (globalAdeleLocalLeadingCoefficientValue D P a)
    rfl

/-- The one-place adele leading coefficient vanishes exactly on the smaller
filtration piece `A(D)`. -/
theorem globalAdeleLocalLeadingCoefficient_ker
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    LinearMap.ker (globalAdeleLocalLeadingCoefficient D P) =
      Submodule.comap
        (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
        (globalAdeleFilter (k := k) (F := F) D) := by
  letI : Algebra k P.residueField := residueAlgebra P
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  change P.residue (globalAdeleLocalLeadingCoefficientValue D P a) = 0 ↔
    ∀ Q, Q.valuation ((a.val : GlobalAdele (k := k) (F := F)).val Q) ≤
      WithZero.exp (D Q)
  rw [P.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change P.valuation
      (Differential.localParameterPower P (D P + 1) *
        ((a.val : GlobalAdele (k := k) (F := F)).val P)) < 1 ↔ _
  rw [map_mul, globalAdele_localParameterPower_valuation,
    globalAdele_exp_neg_mul_lt_one_iff_le]
  constructor
  · intro hP Q
    by_cases hQP : Q = P
    · subst Q
      simpa only [add_sub_cancel_right] using hP
    · have haQ := a.property Q
      simpa only [Finsupp.add_apply, placeDivisor_apply_of_ne P Q (Ne.symm hQP),
        add_zero] using haQ
  · intro ha
    simpa using ha P

/-- The one-place adele leading-coefficient map is onto the actual residue
field. -/
theorem globalAdeleLocalLeadingCoefficient_surjective
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    Function.Surjective (globalAdeleLocalLeadingCoefficient D P) := by
  letI : Algebra k P.residueField := residueAlgebra P
  classical
  let n : ℤ := D P + 1
  intro y
  obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective y
  let x : F := Differential.localParameterPower P (-n) * (z : F)
  let a₀ : GlobalAdele (k := k) (F := F) :=
    globalAdeleUpdate (k := k) (F := F) (zeroGlobalAdele (k := k) (F := F)) P x
  have ha₀ : a₀ ∈ globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      have hzle : P.valuation (z : F) ≤ 1 :=
        (mem_valuationRing_iff P (z : F)).mp z.property
      have hvalue : (a₀ : GlobalAdele (k := k) (F := F)).val P = x := by
        simp only [a₀, globalAdeleUpdate, Function.update_self]
      rw [hvalue]
      simp only [x, map_mul, globalAdele_localParameterPower_valuation, neg_neg]
      have hzle' : P.valuation (z : F) ≤ WithZero.exp (0 : ℤ) := by
        simpa only [WithZero.exp_zero] using hzle
      calc
        WithZero.exp n * P.valuation (z : F) ≤
            WithZero.exp n * WithZero.exp 0 := mul_le_mul_right hzle' _
        _ = WithZero.exp (D P + 1) := by
          rw [← WithZero.exp_add]
          simp only [add_zero, n]
        _ = WithZero.exp ((D + placeDivisor P) P) := by
          simp only [Finsupp.add_apply, placeDivisor_apply]
    · have hzero : (a₀ : GlobalAdele (k := k) (F := F)).val Q = 0 := by
        simp only [a₀, globalAdeleUpdate, zeroGlobalAdele,
          Function.update_of_ne hQP, Pi.zero_apply]
      rw [hzero, map_zero]
      exact zero_le
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  have hpi_ne : Differential.localParameter P ≠ 0 :=
    Differential.localParameter_ne_zero (k := k) (F := F) P
  have hcancel :
      Differential.localParameterPower P n *
          (Differential.localParameterPower P (-n) * (z : F)) = (z : F) := by
    simp only [Differential.localParameterPower,
      Differential.localParameterUnit, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← mul_assoc, ← zpow_add₀ hpi_ne, add_neg_cancel, zpow_zero, one_mul]
  change P.residue (globalAdeleLocalLeadingCoefficientValue D P ⟨a₀, ha₀⟩) = y
  rw [← hz]
  congr 1
  apply Subtype.ext
  simp only [globalAdeleLocalLeadingCoefficientValue]
  change Differential.localParameterPower P (D P + 1) *
      ((a₀ : GlobalAdele (k := k) (F := F)).val P) = (z : F)
  rw [show (a₀ : GlobalAdele (k := k) (F := F)).val P = x by
    simp only [a₀, globalAdeleUpdate, Function.update_self]]
  simpa only [n, x] using hcancel

/-- The one-place intrinsic adele quotient has dimension equal to the actual
residue degree of its supporting place. -/
theorem globalAdeleFilterDiffDimension_add_placeDivisor
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (D + placeDivisor P) =
      residueDegree (k := k) (F := F) P := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField := residueField_finiteDimensional P
  letI : AddCommGroup
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :=
    Submodule.addCommGroup _
  letI : Module k
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :=
    Submodule.module _
  let f := globalAdeleLocalLeadingCoefficient (k := k) (F := F) D P
  have hker := globalAdeleLocalLeadingCoefficient_ker (k := k) (F := F) D P
  have hsurj := globalAdeleLocalLeadingCoefficient_surjective (k := k) (F := F) D P
  rw [globalAdeleFilterDiffDimension, ← hker]
  calc
    Module.finrank k
        (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) ⧸
          LinearMap.ker f) = Module.finrank k (LinearMap.range f) :=
      LinearEquiv.finrank_eq f.quotKerEquivRange
    _ = Module.finrank k P.residueField := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    _ = residueDegree (k := k) (F := F) P :=
      (residueDegree_eq_finrank P).symm

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
