import QEC.Coding.AlgebraicGeometry.Adeles.AdeleDifferentialWeil

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Converse adelic duality for an intrinsic differential

Multiplication by a nonzero function translates vanishing divisors by its
actual principal divisor.  For the adelic Weil functional realized from a
nonzero function-field differential, this translation and maximality of the
intrinsic differential divisor show that multiplication by the differential
identifies `L((omega) - D)` with the fixed-divisor adelic differential space.

Taking dimensions identifies the Riemann--Roch dimension at `(omega) - D`
with the intrinsic specialty index at `D`.  Canonical degree, genus, and the
Riemann--Roch correction identity are not asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance globalAdeleDifferentialDualityAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance globalAdeleDifferentialDualityScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

variable [IsFullConstantField k F]

local instance globalAdeleDifferentialDualityRiemannRochFiniteDimensional
    (D : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule D) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D

private theorem principalDivisor_inv (x : Fˣ) :
    principalDivisor (k := k) (F := F) x⁻¹ =
      -principalDivisor (k := k) (F := F) x := by
  ext P
  simp only [Finsupp.neg_apply, principalDivisor_apply,
    Units.val_inv_eq_inv_val]
  exact GlobalPlace.order_inv P (x : F)

/-- Translating a divisor by the principal divisor of `x` is equivalent to
scaling the adelic Weil functional by `x`. -/
theorem add_principal_mem_globalAdeleVanishingDivisors_smul_iff
    (x : Fˣ) (omega : GlobalAdeleWeilDifferential k F)
    (D : Divisor (GlobalPlace k F)) :
    D + principalDivisor (k := k) (F := F) x ∈
        globalAdeleVanishingDivisors (k := k) (F := F)
          (GlobalAdeleWeilDifferential.smulWeil (x : F) omega) ↔
      D ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by
  constructor
  · intro h a ha
    have hsource :
        (D + principalDivisor (k := k) (F := F) x) +
            principalDivisor (k := k) (F := F) x⁻¹ = D := by
      rw [principalDivisor_inv (k := k) (F := F)]
      abel
    have haSource : a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
        ((D + principalDivisor (k := k) (F := F) x) +
          principalDivisor (k := k) (F := F) x⁻¹) := by
      simpa only [hsource] using ha
    have ha' : ((x⁻¹ : Fˣ) : F) • a ∈
        globalAdeleFilterAddDiagonal (k := k) (F := F)
          (D + principalDivisor (k := k) (F := F) x) :=
      mul_mem_globalAdeleFilterAddDiagonal
        (k := k) (F := F) x⁻¹
        (D + principalDivisor (k := k) (F := F) x) haSource
    have hz := h (((x⁻¹ : Fˣ) : F) • a) ha'
    rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply] at hz
    simpa only [Units.val_inv_eq_inv_val, ← mul_smul, mul_inv_cancel₀ x.ne_zero,
      one_smul] using hz
  · intro h a ha
    rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply]
    exact h ((x : F) • a)
      (mul_mem_globalAdeleFilterAddDiagonal (k := k) (F := F) x D ha)

/-- Multiplication by the realized nonzero differential identifies the
Riemann--Roch space at `(omega) - D` with the adelic differential space at
`D`, hence its dimension is the specialty index at `D`. -/
theorem differentialDivisor_duality
    (omega : Differential k F) (homega : omega ≠ 0)
    (D : Divisor (GlobalPlace k F)) :
    riemannRochDimension
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega - D) =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  let omegaA := globalAdeleWeilDifferentialOfDifferential
    (k := k) (F := F) omega homega
  have hKmem : K ∈ globalAdeleVanishingDivisors (k := k) (F := F) omegaA :=
    differentialDivisor_mem_globalAdeleVanishingDivisors
      (k := k) (F := F) omega homega
  have homegaAToFun : omegaA.toFun ≠ 0 :=
    globalAdeleWeilDifferentialOfDifferential_isNonzero
      (k := k) (F := F) omega homega
  have homegaA : omegaA ≠ 0 := by
    intro hzero
    apply homegaAToFun
    rw [hzero]
    rfl
  have hKD : K - (K - D) = D := sub_sub_cancel K D
  let mu := globalAdeleSmulIntoDifferentialSpace
    (k := k) (F := F) omegaA hKmem (K - D)
  have hmuInjective : Function.Injective mu :=
    globalAdeleSmulIntoDifferentialSpace_injective
      (k := k) (F := F) omegaA hKmem (K - D) homegaAToFun
  have hmuSurjective : Function.Surjective mu := by
    intro psi
    let eta : GlobalAdeleWeilDifferential k F :=
      ⟨(psi : GlobalAdele (k := k) (F := F) →ₗ[k] k), ⟨D, by
        intro a ha
        exact psi.property a (by simpa only [hKD] using ha)⟩⟩
    have hetaD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F) eta := by
      intro a ha
      change (psi : GlobalAdele (k := k) (F := F) →ₗ[k] k) a = 0
      exact psi.property a (by simpa only [hKD] using ha)
    by_cases hpsi : (psi : GlobalAdele (k := k) (F := F) →ₗ[k] k) = 0
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa only [map_zero, Submodule.coe_zero] using hpsi.symm
    · have hetaToFun : eta.toFun ≠ 0 := hpsi
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
        (globalAdeleWeilDifferential_finrank_eq_one
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
        homegaA eta
      have hc0 : c ≠ 0 := by
        intro hcZero
        subst c
        apply hetaToFun
        have hetaZero : eta = 0 := by
          rw [← hc, zero_smul]
        rw [hetaZero]
        rfl
      let cu : Fˣ := Units.mk0 c hc0
      let J := principalDivisor (k := k) (F := F) cu
      have hDmem : D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
          (GlobalAdeleWeilDifferential.smulWeil (cu : F) omegaA) := by
        have hscaled : GlobalAdeleWeilDifferential.smulWeil (cu : F) omegaA =
            eta := by
          exact hc
        rw [hscaled]
        exact hetaD
      have hDJmem : D - J ∈
          globalAdeleVanishingDivisors (k := k) (F := F) omegaA := by
        apply (add_principal_mem_globalAdeleVanishingDivisors_smul_iff
          (k := k) (F := F) cu omegaA (D - J)).mp
        simpa only [J, sub_add_cancel] using hDmem
      have hDJle : D - J ≤ K :=
        globalAdeleVanishingDivisor_le_differentialDivisor
          (k := k) (F := F) omega homega hDJmem
      have hcmem : c ∈ riemannRochSubmodule (K - D) := by
        apply (mem_riemannRochSubmodule_iff_order_add_nonnegative
          (K - D) hc0).mpr
        intro P
        have hP := hDJle P
        simp only [Finsupp.sub_apply, J, principalDivisor_apply,
          cu, Units.val_mk0] at hP ⊢
        omega
      refine ⟨⟨c, hcmem⟩, ?_⟩
      apply Subtype.ext
      rw [globalAdeleSmulIntoDifferentialSpace_coe]
      change (GlobalAdeleWeilDifferential.smulWeil c omegaA).toFun =
        (psi : GlobalAdele (k := k) (F := F) →ₗ[k] k)
      exact congrArg GlobalAdeleWeilDifferential.toFun hc
  let e := LinearEquiv.ofBijective mu ⟨hmuInjective, hmuSurjective⟩
  have hfinrank :
      Module.finrank k (riemannRochSubmodule (K - D)) =
        Module.finrank k
          (globalAdeleDifferentialSpace (k := k) (F := F) (K - (K - D))) :=
    e.finrank_eq
  change Module.finrank k (riemannRochSubmodule (K - D)) =
    riemannRochIndexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  rw [hfinrank, hKD,
    globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty]

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
