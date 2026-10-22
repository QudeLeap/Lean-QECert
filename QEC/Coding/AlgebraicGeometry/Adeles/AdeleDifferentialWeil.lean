import Mathlib.LinearAlgebra.Basis.VectorSpace
import QEC.Coding.AlgebraicGeometry.Adeles.AdeleDifferentialResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Realizing a differential as an intrinsic adelic Weil functional

For a fixed nonzero function-field differential, the finite sum of traced
local residues is defined on the intrinsic simple-pole adele submodule and
vanishes on its intersection with the diagonal.  This file glues that map
with zero on the diagonal, extends the resulting partial linear map to the
whole intrinsic adele space, and proves that its maximal vanishing divisor is
the intrinsic divisor of the original differential.

No converse duality, canonical-degree formula, genus identity, or
Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance globalAdeleDifferentialWeilAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance globalAdeleDifferentialWeilScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

variable [IsFullConstantField k F]

private noncomputable def differentialResiduePartial
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdele (k := k) (F := F) →ₗ.[k] k :=
  ⟨globalAdeleSimplePoleSubmodule (k := k) (F := F) omega,
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega⟩

private noncomputable def diagonalZeroPartial :
    GlobalAdele (k := k) (F := F) →ₗ.[k] k :=
  ⟨diagonalAdeleSubmodule (k := k) (F := F), 0⟩

private theorem differentialResiduePartial_compatible
    (omega : Differential k F) (homega : omega ≠ 0)
    (x : (differentialResiduePartial (k := k) (F := F) omega homega).domain)
    (y : (diagonalZeroPartial (k := k) (F := F)).domain)
    (hxy : (x : GlobalAdele (k := k) (F := F)) = y) :
    differentialResiduePartial (k := k) (F := F) omega homega x =
      diagonalZeroPartial (k := k) (F := F) y := by
  change globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega x = 0
  rcases y.property with ⟨f, hf⟩
  have hxf : (x : GlobalAdele (k := k) (F := F)) =
      diagonalAdele (k := k) (F := F) f := hxy.trans hf.symm
  have hfSimple : diagonalAdele (k := k) (F := F) f ∈
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega := by
    rw [← hxf]
    exact x.property
  have hx : x = ⟨diagonalAdele (k := k) (F := F) f, hfSimple⟩ :=
    Subtype.ext hxf
  rw [hx]
  exact globalAdeleSimplePoleResidueSum_diagonal_eq_zero
    (k := k) (F := F) omega homega f hfSimple

private noncomputable def differentialResidueGluedPartial
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdele (k := k) (F := F) →ₗ.[k] k :=
  (differentialResiduePartial (k := k) (F := F) omega homega).sup
    (diagonalZeroPartial (k := k) (F := F))
    (differentialResiduePartial_compatible
      (k := k) (F := F) omega homega)

private noncomputable def differentialResidueExtension
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdele (k := k) (F := F) →ₗ[k] k :=
  Classical.choose
    (LinearMap.exists_extend
      (differentialResidueGluedPartial
        (k := k) (F := F) omega homega).toFun)

private theorem differentialResidueExtension_comp
    (omega : Differential k F) (homega : omega ≠ 0) :
    (differentialResidueExtension (k := k) (F := F) omega homega).comp
        (differentialResidueGluedPartial
          (k := k) (F := F) omega homega).domain.subtype =
      (differentialResidueGluedPartial
        (k := k) (F := F) omega homega).toFun :=
  Classical.choose_spec
    (LinearMap.exists_extend
      (differentialResidueGluedPartial
        (k := k) (F := F) omega homega).toFun)

private theorem differentialResidueExtension_apply
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : (differentialResidueGluedPartial
      (k := k) (F := F) omega homega).domain) :
    differentialResidueExtension (k := k) (F := F) omega homega
        (a : GlobalAdele (k := k) (F := F)) =
      differentialResidueGluedPartial (k := k) (F := F) omega homega a := by
  have h := congrArg (fun f => f a)
    (differentialResidueExtension_comp
      (k := k) (F := F) omega homega)
  exact h

private theorem differentialResidueExtension_apply_of_mem_simplePole
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    differentialResidueExtension (k := k) (F := F) omega homega a =
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega ⟨a, ha⟩ := by
  let aGlued : (differentialResidueGluedPartial
      (k := k) (F := F) omega homega).domain :=
    ⟨a, Submodule.mem_sup_left ha⟩
  have hext := differentialResidueExtension_apply
    (k := k) (F := F) omega homega aGlued
  have hleft :=
    (LinearPMap.left_le_sup
      (differentialResiduePartial (k := k) (F := F) omega homega)
      (diagonalZeroPartial (k := k) (F := F))
      (differentialResiduePartial_compatible
        (k := k) (F := F) omega homega)).2
      (x := ⟨a, ha⟩) (y := aGlued) rfl
  exact hext.trans hleft.symm

private theorem differentialResidueExtension_apply_of_mem_diagonal
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ diagonalAdeleSubmodule (k := k) (F := F)) :
    differentialResidueExtension (k := k) (F := F) omega homega a = 0 := by
  let aGlued : (differentialResidueGluedPartial
      (k := k) (F := F) omega homega).domain :=
    ⟨a, Submodule.mem_sup_right ha⟩
  have hext := differentialResidueExtension_apply
    (k := k) (F := F) omega homega aGlued
  have hright :=
    (LinearPMap.right_le_sup
      (differentialResiduePartial (k := k) (F := F) omega homega)
      (diagonalZeroPartial (k := k) (F := F))
      (differentialResiduePartial_compatible
        (k := k) (F := F) omega homega)).2
      (x := ⟨a, ha⟩) (y := aGlued) rfl
  exact hext.trans hright.symm

private theorem differentialResidueExtension_vanishes
    (omega : Differential k F) (homega : omega ≠ 0) :
    ∀ a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega),
      differentialResidueExtension (k := k) (F := F) omega homega a = 0 := by
  intro a ha
  change a ∈ globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega) +
      diagonalAdeleSubmodule (k := k) (F := F) at ha
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  rw [map_add,
    differentialResidueExtension_apply_of_mem_simplePole
      (k := k) (F := F) omega homega a₁
      (globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega ha₁),
    globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
      (k := k) (F := F) omega homega ⟨a₁, ha₁⟩,
    differentialResidueExtension_apply_of_mem_diagonal
      (k := k) (F := F) omega homega a₂ ha₂,
    add_zero]

/-- The adelic Weil functional obtained by extending the actual traced
simple-pole residue sum of a nonzero differential. -/
noncomputable def globalAdeleWeilDifferentialOfDifferential
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdeleWeilDifferential k F :=
  ⟨differentialResidueExtension (k := k) (F := F) omega homega,
    ⟨FunctionFieldDifferential.differentialDivisor
      (k := k) (F := F) omega homega,
      differentialResidueExtension_vanishes
        (k := k) (F := F) omega homega⟩⟩

/-- The extended functional agrees with the traced residue sum on every
intrinsic simple-pole adele. -/
theorem globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    (globalAdeleWeilDifferentialOfDifferential
      (k := k) (F := F) omega homega).toFun a =
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨a, ha⟩ :=
  differentialResidueExtension_apply_of_mem_simplePole
    (k := k) (F := F) omega homega a ha

private theorem globalPlace_nonempty : Nonempty (GlobalPlace k F) := by
  obtain ⟨D⟩ := InverseAffinePlace.infinityFibre_nonempty
    (oldRationalAlgebra := ρ) k F
  exact ⟨InverseAffinePlace.infinityFibreGlobalPlace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s) D⟩

/-- The residue extension of a nonzero differential is itself a nonzero
adelic Weil functional. -/
theorem globalAdeleWeilDifferentialOfDifferential_isNonzero
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdeleWeilDifferential.IsNonzero
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega) := by
  let P := Classical.choice
    (globalPlace_nonempty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  obtain ⟨a, ha⟩ :=
    globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
      (k := k) (F := F) omega homega P (1 : k)
  intro hzero
  have hvalue :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 1 := by
    rw [globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
      (k := k) (F := F) omega homega _
      (globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega P a.property)]
    exact ha
  have hvalueZero :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 0 := by
    rw [hzero]
    exact LinearMap.zero_apply _
  exact one_ne_zero (hvalue.symm.trans hvalueZero)

/-- The intrinsic divisor of a nonzero differential is a vanishing divisor
of its realized adelic Weil functional. -/
theorem differentialDivisor_mem_globalAdeleVanishingDivisors
    (omega : Differential k F) (homega : omega ≠ 0) :
    FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega ∈
      globalAdeleVanishingDivisors (k := k) (F := F)
        (globalAdeleWeilDifferentialOfDifferential
          (k := k) (F := F) omega homega) :=
  differentialResidueExtension_vanishes
    (k := k) (F := F) omega homega

private theorem globalAdeleFilter_sup_eq_add
    {D₁ D₂ : Divisor (GlobalPlace k F)} :
    globalAdeleFilter (k := k) (F := F) (D₁ ⊔ D₂) =
      globalAdeleFilter (k := k) (F := F) D₁ +
        globalAdeleFilter (k := k) (F := F) D₂ := by
  classical
  rw [Submodule.add_eq_sup]
  apply le_antisymm
  · intro a ha
    have haevent := a.property
    change ∀ᶠ P : GlobalPlace k F in Filter.cofinite,
      a.val P ∈ P.valuationRing at haevent
    let a₁ : GlobalAdele (k := k) (F := F) :=
      ⟨fun P => if D₂ P ≤ D₁ P then a.val P else 0, by
        change ∀ᶠ P : GlobalPlace k F in Filter.cofinite,
          (if D₂ P ≤ D₁ P then a.val P else 0) ∈ P.valuationRing
        exact haevent.mono fun P hP => by
          by_cases h : D₂ P ≤ D₁ P
          · rw [if_pos h]
            exact hP
          · rw [if_neg h]
            exact P.valuationRing.zero_mem⟩
    let a₂ : GlobalAdele (k := k) (F := F) :=
      ⟨fun P => if D₂ P ≤ D₁ P then 0 else a.val P, by
        change ∀ᶠ P : GlobalPlace k F in Filter.cofinite,
          (if D₂ P ≤ D₁ P then 0 else a.val P) ∈ P.valuationRing
        exact haevent.mono fun P hP => by
          by_cases h : D₂ P ≤ D₁ P
          · rw [if_pos h]
            exact P.valuationRing.zero_mem
          · rw [if_neg h]
            exact hP⟩
    have ha₁ : a₁ ∈ globalAdeleFilter (k := k) (F := F) D₁ := by
      intro P
      by_cases h : D₂ P ≤ D₁ P
      · change P.valuation (if D₂ P ≤ D₁ P then a.val P else 0) ≤ _
        rw [if_pos h]
        simpa only [Finsupp.sup_apply, sup_eq_left.mpr h] using ha P
      · simp only [a₁, if_neg h, map_zero]
        exact zero_le
    have ha₂ : a₂ ∈ globalAdeleFilter (k := k) (F := F) D₂ := by
      intro P
      by_cases h : D₂ P ≤ D₁ P
      · simp only [a₂, if_pos h, map_zero]
        exact zero_le
      · have hle : D₁ P ≤ D₂ P := le_of_not_ge h
        change P.valuation (if D₂ P ≤ D₁ P then 0 else a.val P) ≤ _
        rw [if_neg h]
        simpa only [Finsupp.sup_apply, sup_eq_right.mpr hle] using ha P
    refine Submodule.mem_sup.mpr ⟨a₁, ha₁, a₂, ha₂, ?_⟩
    ext P
    by_cases h : D₂ P ≤ D₁ P <;> simp [a₁, a₂, h]
  · apply sup_le
    · exact globalAdeleFilter_mono (k := k) (F := F) le_sup_left
    · exact globalAdeleFilter_mono (k := k) (F := F) le_sup_right

private theorem globalAdeleVanishingDivisors_sup
    {omega : GlobalAdeleWeilDifferential k F}
    {D₁ D₂ : Divisor (GlobalPlace k F)}
    (hD₁ : D₁ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (hD₂ : D₂ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega) :
    D₁ ⊔ D₂ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by
  intro a ha
  change a ∈ globalAdeleFilter (k := k) (F := F) (D₁ ⊔ D₂) +
      diagonalAdeleSubmodule (k := k) (F := F) at ha
  rw [globalAdeleFilter_sup_eq_add] at ha
  rcases Submodule.mem_sup.mp ha with ⟨b, hb, d, hd, rfl⟩
  rcases Submodule.mem_sup.mp hb with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  have hsplit : a₁ + a₂ + d = (a₁ + d) + a₂ := by abel
  rw [hsplit, map_add]
  have hleft : omega.toFun (a₁ + d) = 0 := by
    apply hD₁
    exact Submodule.mem_sup.mpr ⟨a₁, ha₁, d, hd, rfl⟩
  have hright : omega.toFun a₂ = 0 := by
    apply hD₂
    exact Submodule.mem_sup_left ha₂
  rw [hleft, hright, add_zero]

/-- Every vanishing divisor of the realized functional is bounded above by
the intrinsic divisor of the original nonzero differential. -/
theorem globalAdeleVanishingDivisor_le_differentialDivisor
    (omega : Differential k F) (homega : omega ≠ 0)
    {D : Divisor (GlobalPlace k F)}
    (hD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega)) :
    D ≤ FunctionFieldDifferential.differentialDivisor
      (k := k) (F := F) omega homega := by
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  intro P
  by_contra hnot
  have hstrict : K P < D P := lt_of_not_ge hnot
  have hsup : K ⊔ D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega) :=
    globalAdeleVanishingDivisors_sup
      (k := k) (F := F)
      (differentialDivisor_mem_globalAdeleVanishingDivisors
        (k := k) (F := F) omega homega) hD
  have hle : K + placeDivisor P ≤ K ⊔ D := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp only [Finsupp.add_apply, placeDivisor_apply, Finsupp.sup_apply]
      omega
    · simp only [Finsupp.add_apply,
        placeDivisor_apply_of_ne P Q (Ne.symm hQP), add_zero,
        Finsupp.sup_apply]
      exact le_sup_left
  obtain ⟨a, ha⟩ :=
    globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
      (k := k) (F := F) omega homega P (1 : k)
  have hvanish :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 0 := by
    apply hsup
    exact Submodule.mem_sup_left
      (globalAdeleFilter_mono (k := k) (F := F) hle a.property)
  have hvalue :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 1 := by
    rw [globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
      (k := k) (F := F) omega homega _
      (globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega P a.property)]
    exact ha
  exact one_ne_zero (hvalue.symm.trans hvanish)

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
