import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Filter.Cofinite
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Space
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Intrinsic all-place adeles

This file constructs the restricted product of the function field over the
actual `GlobalPlace` carrier, its divisor filtration, and the diagonal copy of
the function field.  The construction is adapted to Lean-QEC's intrinsic
place API from Guanghao Li's Apache-2.0 formalization
`vaca22/riemann-roch-function-fields`.

No genus, Weil differential, duality, canonical-degree identity, or
Riemann--Roch formula is assumed or proved here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Filter
open scoped Polynomial RatFunc WithZero

noncomputable section

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

/-- The `k`-submodule of tuples integral at all but finitely many actual global
places. -/
def globalAdeleSubmodule : Submodule k (GlobalPlace k F → F) where
  carrier := {a | ∀ᶠ P in cofinite, a P ∈ P.valuationRing}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ∀ᶠ P in cofinite, a P ∈ P.valuationRing at ha
    change ∀ᶠ P in cofinite, b P ∈ P.valuationRing at hb
    change ∀ᶠ P in cofinite, (a + b) P ∈ P.valuationRing
    exact (ha.and hb).mono fun P hP => P.valuationRing.add_mem _ _ hP.1 hP.2
  smul_mem' c a ha := by
    change ∀ᶠ P in cofinite, a P ∈ P.valuationRing at ha
    change ∀ᶠ P in cofinite, (c • a) P ∈ P.valuationRing
    filter_upwards [ha] with P hP
    rw [Pi.smul_apply, Algebra.smul_def]
    exact P.valuationRing.mul_mem _ _
      ((mem_valuationRing_iff P _).mpr
        (FiniteField.valuation_algebraMap_le_one P.valuation c)) hP

/-- The intrinsic `F`-valued restricted product over all global places. -/
abbrev GlobalAdele := globalAdeleSubmodule (k := k) (F := F)

variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

/-- Every function is integral at all but finitely many actual global places.
The exceptional set is contained in the support of its principal divisor. -/
theorem eventually_mem_valuationRing (f : F) :
    ∀ᶠ P : GlobalPlace k F in cofinite, f ∈ P.valuationRing := by
  rw [Filter.eventually_cofinite]
  by_cases hf : f = 0
  · subst f
    simp
  · let u : Fˣ := Units.mk0 f hf
    refine (GlobalPlace.principalDivisor (k := k) (F := F) u).support.finite_toSet.subset ?_
    intro P hP
    change f ∉ P.valuationRing at hP
    change P ∈ (GlobalPlace.principalDivisor (k := k) (F := F) u).support
    apply Finsupp.mem_support_iff.mpr
    rw [GlobalPlace.principalDivisor_apply]
    intro horder
    have horder' : P.order f = 0 := by
      simpa only [u, Units.val_mk0] using horder
    apply hP
    exact (regularAt_iff_mem_valuationRing P f).mp
      ((regularAt_iff_order_nonnegative P hf).mpr (by rw [horder']))

/-- Pointwise multiplication of an adele by an element of the function
field. -/
def smulGlobalAdele (x : F) (a : GlobalAdele (k := k) (F := F)) :
    GlobalAdele (k := k) (F := F) :=
  ⟨fun P => x * a.val P, by
    have hx := eventually_mem_valuationRing (k := k) (F := F) x
    have ha := a.property
    change ∀ᶠ P : GlobalPlace k F in cofinite, a.val P ∈ P.valuationRing at ha
    change ∀ᶠ P : GlobalPlace k F in cofinite, x * a.val P ∈ P.valuationRing
    exact (hx.and ha).mono fun P hP =>
      P.valuationRing.mul_mem _ _ hP.1 hP.2⟩

instance : SMul F (GlobalAdele (k := k) (F := F)) :=
  ⟨smulGlobalAdele (k := k) (F := F)⟩

instance : Module F (GlobalAdele (k := k) (F := F)) :=
  Module.ofMinimalAxioms
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_add _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => add_mul _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_assoc _ _ _)
    (fun _ => Subtype.ext <| funext fun _ => one_mul _)

/-- Multiplication by a field element as a `k`-linear endomorphism of the
adele space. -/
def mulGlobalAdeleLinear (x : F) :
    GlobalAdele (k := k) (F := F) →ₗ[k] GlobalAdele (k := k) (F := F) where
  toFun a := x • a
  map_add' _ _ := smul_add x _ _
  map_smul' c a := by
    ext P
    change x * (c • a.val P) = c • (x * a.val P)
    simp only [Algebra.smul_def]
    ring

/-- Membership in the divisor filtration piece of the intrinsic adele
space. -/
def MemGlobalAdeleFilter (D : Divisor (GlobalPlace k F))
    (a : GlobalAdele (k := k) (F := F)) : Prop :=
  ∀ P, P.valuation (a.val P) ≤ WithZero.exp (D P)

/-- The divisor filtration piece `A(D)` of the intrinsic adele space. -/
def globalAdeleFilter (D : Divisor (GlobalPlace k F)) :
    Submodule k (GlobalAdele (k := k) (F := F)) where
  carrier := {a | MemGlobalAdeleFilter D a}
  zero_mem' := fun P => by simp
  add_mem' {a b} ha hb := by
    intro P
    exact (Valuation.map_add P.valuation (a.val P) (b.val P)).trans
      (max_le (ha P) (hb P))
  smul_mem' c a ha := by
    intro P
    change P.valuation (c • a.val P) ≤ _
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_mul'
      (FiniteField.valuation_algebraMap_le_one P.valuation c) (ha P)).trans_eq
        (one_mul _)

/-- The diagonal embedding of the function field into its intrinsic adele
space. -/
def diagonalAdele : F →ₗ[k] GlobalAdele (k := k) (F := F) where
  toFun f := ⟨fun _ => f, eventually_mem_valuationRing (k := k) (F := F) f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The diagonal copy of the function field inside the adele space. -/
def diagonalAdeleSubmodule : Submodule k (GlobalAdele (k := k) (F := F)) :=
  LinearMap.range (diagonalAdele (k := k) (F := F))

/-- Intersecting an adele filtration piece with the diagonal recovers the
actual all-place Riemann--Roch submodule. -/
theorem globalAdeleFilter_inf_diagonal (D : Divisor (GlobalPlace k F)) :
    globalAdeleFilter (k := k) (F := F) D ⊓
        diagonalAdeleSubmodule (k := k) (F := F) =
      Submodule.map (diagonalAdele (k := k) (F := F)) (riemannRochSubmodule D) := by
  ext a
  constructor
  · rintro ⟨ha, f, rfl⟩
    refine ⟨f, ?_, rfl⟩
    exact ha
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hf, ⟨f, rfl⟩⟩

/-- The intrinsic adele filtration is monotone in the divisor. -/
theorem globalAdeleFilter_mono {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    globalAdeleFilter (k := k) (F := F) D ≤
      globalAdeleFilter (k := k) (F := F) E := by
  intro a ha P
  exact (ha P).trans (WithZero.exp_le_exp.mpr (hDE P))

/-- A smaller adele filtration piece as a submodule of a larger one. -/
@[nolint unusedArguments]
def globalAdeleFilterWithin {D E : Divisor (GlobalPlace k F)} (_hDE : D ≤ E) :
    Submodule k (globalAdeleFilter (k := k) (F := F) E) :=
  Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
    (globalAdeleFilter (k := k) (F := F) D)

/-- The dimension of one quotient between intrinsic adele filtration pieces. -/
noncomputable def globalAdeleFilterDiffDimension
    (D E : Divisor (GlobalPlace k F)) : ℕ := by
  letI : AddCommGroup (globalAdeleFilter (k := k) (F := F) E) :=
    Submodule.addCommGroup _
  letI : Module k (globalAdeleFilter (k := k) (F := F) E) := Submodule.module _
  exact Module.finrank k
    (globalAdeleFilter (k := k) (F := F) E ⧸
      Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
        (globalAdeleFilter (k := k) (F := F) D))

/-- The zero intrinsic adele. -/
def zeroGlobalAdele : GlobalAdele (k := k) (F := F) := ⟨0, by simp⟩

/-- Replace one component of an intrinsic adele. -/
noncomputable def globalAdeleUpdate (a : GlobalAdele (k := k) (F := F))
    (P : GlobalPlace k F) (x : F) : GlobalAdele (k := k) (F := F) := by
  classical
  refine ⟨Function.update a.val P x, ?_⟩
  change ∀ᶠ Q : GlobalPlace k F in cofinite,
    Function.update a.val P x Q ∈ Q.valuationRing
  filter_upwards [a.property, Filter.eventually_cofinite_ne P] with Q hQ hQP
  simpa only [Function.update_of_ne hQP] using hQ

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
