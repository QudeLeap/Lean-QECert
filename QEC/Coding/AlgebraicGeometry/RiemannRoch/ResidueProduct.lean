import QEC.Coding.AlgebraicGeometry.Residues.Global.SimplePoleResidue
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PlaceIncrement

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Product differentials for the Riemann--Roch residue pairing

For `x ∈ L(G + P)` and `y ∈ L((ω) - G)`, the product `xyω` has at
most a simple pole globally and is regular away from `P`. Consequently its
finite traced-residue family is supported at that one place.

This is the local support calculation needed by the later duality argument.
It does not assert that the remaining residue vanishes, and therefore does
not assume or prove the global residue theorem, duality, genus, or
Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The actual function product multiplying a chosen nonzero differential in
the one-place residue pairing. -/
noncomputable def riemannRochProductDifferential
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    Differential k F :=
  ((x : F) * (y : F)) • omega

/-- The product differential used by the one-place pairing has at most a
simple pole at every actual global place. -/
theorem riemannRochProductDifferential_isGlobalSimplePole
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    IsGlobalSimplePole
      (riemannRochProductDifferential omega homega G P x y) := by
  intro Q
  by_cases hx : (x : F) = 0
  · simp only [riemannRochProductDifferential, hx, zero_mul, zero_smul]
    exact (simplePoleDifferentialLattice Q).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [riemannRochProductDifferential, hy, mul_zero, zero_smul]
    exact (simplePoleDifferentialLattice Q).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply (smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
    (k := k) (F := F) Q ((x : F) * (y : F)) hxy omega homega).mpr
  rw [GlobalPlace.order_mul Q hx hy]
  have hxQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (G + P.placeDivisor) hx).mp x.property Q
  have hyQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (differentialDivisor (k := k) (F := F) omega homega - G) hy).mp
        y.property Q
  simp only [Finsupp.add_apply] at hxQ
  simp only [Finsupp.sub_apply, differentialDivisor_apply] at hyQ
  by_cases hQP : Q = P
  · subst Q
    rw [GlobalPlace.placeDivisor_apply] at hxQ
    omega
  · rw [GlobalPlace.placeDivisor_apply_of_ne P Q (Ne.symm hQP)] at hxQ
    omega

/-- Away from the selected place, the same product differential is regular. -/
theorem riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P Q : GlobalPlace k F) (hQP : Q ≠ P)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    riemannRochProductDifferential omega homega G P x y ∈
      localDifferentialLattice Q := by
  by_cases hx : (x : F) = 0
  · simp only [riemannRochProductDifferential, hx, zero_mul, zero_smul]
    exact (localDifferentialLattice Q).zero_mem
  by_cases hy : (y : F) = 0
  · simp only [riemannRochProductDifferential, hy, mul_zero, zero_smul]
    exact (localDifferentialLattice Q).zero_mem
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  apply (smul_mem_localDifferentialLattice_iff_order_add_nonnegative
    (k := k) (F := F) Q ((x : F) * (y : F)) hxy omega homega).mpr
  rw [GlobalPlace.order_mul Q hx hy]
  have hxQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (G + P.placeDivisor) hx).mp x.property Q
  have hyQ :=
    (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative
      (differentialDivisor (k := k) (F := F) omega homega - G) hy).mp
        y.property Q
  rw [Finsupp.add_apply,
    GlobalPlace.placeDivisor_apply_of_ne P Q (Ne.symm hQP), add_zero] at hxQ
  simp only [Finsupp.sub_apply, differentialDivisor_apply] at hyQ
  omega

/-- Every traced residue coefficient of the one-place product differential
away from the selected place is zero. -/
theorem globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero_of_ne
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P Q : GlobalPlace k F) (hQP : Q ≠ P)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) Q = 0 := by
  rw [globalSimplePoleResidue_apply]
  change simplePoleTraceResidue (k := k) (F := F) Q
      (riemannRochProductDifferential omega homega G P x y)
      ((riemannRochProductDifferential_isGlobalSimplePole
        omega homega G P x y) Q) = 0
  exact simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) Q
    (riemannRochProductDifferential omega homega G P x y)
    ((riemannRochProductDifferential_isGlobalSimplePole
      omega homega G P x y) Q)
    (riemannRochProductDifferential_mem_localDifferentialLattice_of_ne
      omega homega G P Q hQP x y)

end Differential

end QEC.Coding.AlgebraicGeometry
