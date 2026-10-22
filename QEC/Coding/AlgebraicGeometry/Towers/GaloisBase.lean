import QEC.Coding.AlgebraicGeometry.Towers.BasePlaces

import Mathlib.Data.Fintype.EquivFin

/-!
# The rational base of the F256 Garcia--Stichtenoth Galois tower

The Galois family used by Stichtenoth's self-dual-code construction starts
from `w = x₀^16 + x₀` and `z = w^15`.  This file constructs those literal
functions and the 240 finite `x₀`-values above `z = 1`.  The count is derived
from the sixteen-element Artin--Schreier kernel; no finite-field truth table or
tower conclusion is stored here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The distinguished `w = x₀^16 + x₀` in the rational seed field. -/
noncomputable def galoisBaseW : RatFunc F256 :=
  RatFunc.X ^ 16 + RatFunc.X

/-- The rational base parameter `z = w^15`. -/
noncomputable def galoisBaseZ : RatFunc F256 :=
  galoisBaseW ^ 15

/-- Evaluation of the distinguished function `w` at a finite constant. -/
noncomputable def galoisBaseWValue (a : F256) : F256 :=
  f256ArtinSchreier a

theorem galoisBaseWValue_eq (a : F256) :
    galoisBaseWValue a = a ^ 16 + a := by
  exact f256ArtinSchreier_apply a

/-- Evaluation of the rational base parameter `z` at a finite constant. -/
noncomputable def galoisBaseZValue (a : F256) : F256 :=
  galoisBaseWValue a ^ 15

theorem galoisBaseZValue_eq (a : F256) :
    galoisBaseZValue a = (a ^ 16 + a) ^ 15 := by
  rw [galoisBaseZValue, galoisBaseWValue_eq]

private theorem galoisBaseWValue_pow_sixteen (a : F256) :
    galoisBaseWValue a ^ 16 = galoisBaseWValue a := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  have ha : a ^ 256 = a := by
    simpa only [f256_card] using FiniteField.pow_card a
  rw [galoisBaseWValue_eq]
  calc
    (a ^ 16 + a) ^ 16 = (a ^ 16) ^ 16 + a ^ 16 := by
      have hport := (add_pow_char_pow (a ^ 16) a 2 4)
      norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num] at hport
      change (a ^ 16 + a) ^ 16 = (a ^ 16) ^ 16 + a ^ 16
      exact hport
    _ = a ^ 256 + a ^ 16 := by rw [← pow_mul]
    _ = a + a ^ 16 := by rw [ha]
    _ = a ^ 16 + a := add_comm _ _

/-- Over `F256`, the equation `z(a) = 1` is exactly the condition `w(a) ≠ 0`.
This is the finite splitting condition printed in Sti06, item F10. -/
theorem galoisBaseZValue_eq_one_iff (a : F256) :
    galoisBaseZValue a = 1 ↔ galoisBaseWValue a ≠ 0 := by
  constructor
  · intro hz hw
    rw [galoisBaseZValue, hw] at hz
    simpa using hz
  · intro hw
    apply mul_left_cancel₀ hw
    calc
      galoisBaseWValue a * galoisBaseWValue a ^ 15 =
          galoisBaseWValue a ^ 16 := by ring
      _ = galoisBaseWValue a := galoisBaseWValue_pow_sixteen a
      _ = galoisBaseWValue a * 1 := (mul_one _).symm

/-- The literal finite `x₀`-values lying over the rational base place `z=1`. -/
abbrev GaloisBaseSplitPoint : Type :=
  {a : F256 // galoisBaseWValue a ≠ 0}

private noncomputable def galoisBaseWZeroEquivKernel :
    {a : F256 // galoisBaseWValue a = 0} ≃
      LinearMap.ker f256ArtinSchreier where
  toFun a := ⟨a, a.property⟩
  invFun a := ⟨a, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are exactly `256 - 16 = 240` finite seed places over `z = 1`. -/
theorem galoisBaseSplitPoint_card :
    Fintype.card GaloisBaseSplitPoint = 240 := by
  calc
    Fintype.card GaloisBaseSplitPoint =
        Fintype.card F256 -
          Fintype.card {a : F256 // galoisBaseWValue a = 0} :=
      Fintype.card_subtype_compl
        (fun a : F256 => galoisBaseWValue a = 0)
    _ = 256 - 16 := by
      rw [f256_card,
        Fintype.card_congr galoisBaseWZeroEquivKernel,
        f256ArtinSchreier_ker_card]
    _ = 240 := by norm_num

/-- A fixed finite-coordinate enumeration of the 240 base split points. -/
noncomputable def galoisBaseSplitPointEquiv :
    Fin 240 ≃ GaloisBaseSplitPoint :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using galoisBaseSplitPoint_card.symm)

private noncomputable def galoisBaseSplitPointUnit
    (a : GaloisBaseSplitPoint) : F256ˣ :=
  Units.mk0 a (by
    intro ha
    apply a.property
    simp [galoisBaseWValue_eq, ha])

/-- The actual rational place `x₀=a` above `z=1` for one split point. -/
noncomputable def galoisBaseSplitRationalPlace
    (a : GaloisBaseSplitPoint) : RationalPlace F256 (RatFunc F256) :=
  baseRationalPlace (galoisBaseSplitPointUnit a)

/-- Distinct split values give distinct actual rational places. -/
theorem galoisBaseSplitRationalPlace_injective :
    Function.Injective galoisBaseSplitRationalPlace := by
  intro a b hab
  have hplace :
      (baseRationalPlace (galoisBaseSplitPointUnit a)).place =
        (baseRationalPlace (galoisBaseSplitPointUnit b)).place :=
    congrArg RationalPlace.place hab
  have hunit := baseRationalPlace_injective hplace
  apply Subtype.ext
  exact congrArg Units.val hunit

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
