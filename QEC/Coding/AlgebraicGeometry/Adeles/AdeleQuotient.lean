import QEC.Coding.AlgebraicGeometry.Adeles.AdeleSandwich

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# The intrinsic adele quotient

For an all-place divisor `D`, this file forms the actual quotient of the
intrinsic adele space by `A(D) + F`.  The saturation theorem for a
genus-attaining divisor identifies its finite rank with the previously
constructed Riemann--Roch index of specialty.

The finite-dimensional quotient argument follows the architecture of
`RiemannRoch/Genus/AdeleQuotient.lean` in Guanghao Li's Apache-2.0
formalization `vaca22/riemann-roch-function-fields` at commit
`dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`, adapted to this repository's
intrinsic global-place carrier.

No pairing with differentials, converse duality, canonical-degree formula,
or Riemann--Roch identity is assumed or proved here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance globalAdeleQuotientAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance globalAdeleQuotientScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

variable [IsFullConstantField k F]

local instance globalAdeleQuotientFilterAddCommGroup
    (D : Divisor (GlobalPlace k F)) :
    AddCommGroup (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.addCommGroup _

local instance globalAdeleQuotientFilterModule
    (D : Divisor (GlobalPlace k F)) :
    Module k (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.module _

/-- The denominator `A(D) + F` inside the intrinsic adele space. -/
def globalAdeleFilterAddDiagonal
    (D : Divisor (GlobalPlace k F)) :
    Submodule k (GlobalAdele (k := k) (F := F)) :=
  globalAdeleFilter (k := k) (F := F) D +
    diagonalAdeleSubmodule (k := k) (F := F)

/-- The intrinsic adele quotient `A / (A(D) + F)`. -/
abbrev GlobalAdeleQuotient
    (D : Divisor (GlobalPlace k F)) :=
  GlobalAdele (k := k) (F := F) ⧸
    globalAdeleFilterAddDiagonal (k := k) (F := F) D

/-- The rank of the intrinsic adele quotient. -/
noncomputable def globalAdeleQuotientRank
    (D : Divisor (GlobalPlace k F)) : ℕ :=
  Module.finrank k (GlobalAdeleQuotient (k := k) (F := F) D)

/-- Once `A(E) + F` is the whole adele space, the quotient rank at `D` is
the corresponding finite sandwich rank. -/
theorem globalAdeleQuotientRank_eq_sandwichRank
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hfull : globalAdeleTopSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :
    globalAdeleQuotientRank (k := k) (F := F) D =
      (globalAdeleSandwichRank (k := k) (F := F) D E hDE).toNat := by
  classical
  let denominator := globalAdeleFilterAddDiagonal (k := k) (F := F) D
  let topModule := globalAdeleTopSubmodule (k := k) (F := F)
  letI : AddCommGroup ↥topModule := Submodule.addCommGroup _
  letI : Module k ↥topModule := Submodule.module _
  let q := Submodule.comap topModule.subtype denominator
  let e : ↥topModule ≃ₗ[k] GlobalAdele (k := k) (F := F) :=
    Submodule.topEquiv (R := k) (M := GlobalAdele (k := k) (F := F))
  have hmap := Submodule.map_comap_subtype
    (p := topModule) (p' := denominator)
  have heq : (e : ↥topModule →ₗ[k] GlobalAdele (k := k) (F := F)) =
      topModule.subtype := by
    apply LinearMap.ext
    rintro ⟨a, ha⟩
    apply Subtype.ext
    funext P
    rfl
  have hqmap : q.map (e : ↥topModule →ₗ[k]
      GlobalAdele (k := k) (F := F)) = denominator := by
    rw [show q.map (e : ↥topModule →ₗ[k]
        GlobalAdele (k := k) (F := F)) = q.map topModule.subtype by rw [heq],
      hmap, inf_eq_right]
    exact le_top
  dsimp only [globalAdeleQuotientRank, globalAdeleSandwichRank,
    globalAdeleFilterAddDiagonal, denominator]
  rw [← (Submodule.Quotient.equiv q denominator e hqmap).finrank_eq,
    hfull.symm]
  simp only [topModule, globalAdeleTopSubmodule, q]
  simp only [denominator, globalAdeleFilterAddDiagonal,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  rfl

/-- The intrinsic adele quotient is finite-dimensional over the full constant
field. -/
theorem globalAdeleQuotient_finite
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k (GlobalAdeleQuotient (k := k) (F := F) D) := by
  classical
  obtain ⟨G, hG⟩ := exists_riemannRochDefect_eq_genus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  let E := D ⊔ G
  have hDE : D ≤ E := le_sup_left
  have hGE : G ≤ E := le_sup_right
  have hE : riemannRochDefect (k := k) (F := F) E =
      (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) := by
    have hlower := riemannRochDefect_mono
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hGE
    have hupper := riemannRochDefect_le_genus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F E
    omega
  have hfull :=
    globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hE
  let p := globalAdeleFilter (k := k) (F := F) E
  let q := Submodule.comap p.subtype
    (globalAdeleFilter (k := k) (F := F) D)
  let denominator := globalAdeleFilterAddDiagonal (k := k) (F := F) D
  letI : AddCommGroup ↥p := Submodule.addCommGroup _
  letI : Module k ↥p := Submodule.module _
  haveI : Module.Finite k (↥p ⧸ q) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDE
  let quotientMap := denominator.mkQ.comp (p.subtype : p →ₗ[k]
    GlobalAdele (k := k) (F := F))
  have hqker : q ≤ quotientMap.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    apply (Submodule.Quotient.mk_eq_zero denominator).mpr
    exact Submodule.mem_sup_left hx
  let induced := q.liftQ quotientMap hqker
  have hinduced : Function.Surjective induced := by
    intro z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective denominator z
    have ha : a ∈ p + diagonalAdeleSubmodule (k := k) (F := F) := by
      rw [← hfull]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp ha with ⟨x, hxp, y, hyr, hxy⟩
    refine ⟨Submodule.Quotient.mk ⟨x, hxp⟩, ?_⟩
    change Submodule.Quotient.mk x = Submodule.Quotient.mk a
    apply (Submodule.Quotient.eq denominator).mpr
    have hnegy : -y ∈ denominator :=
      denominator.neg_mem (Submodule.mem_sup_right hyr)
    simpa only [← hxy, sub_add_eq_sub_sub, sub_self, zero_sub] using hnegy
  exact Module.Finite.of_surjective induced hinduced

/-- The rank of the actual intrinsic adele quotient is the Riemann--Roch
index of specialty. -/
theorem globalAdeleQuotientRank_eq_indexOfSpecialty
    (D : Divisor (GlobalPlace k F)) :
    globalAdeleQuotientRank (k := k) (F := F) D =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
  obtain ⟨G, hG⟩ := exists_riemannRochDefect_eq_genus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  let E := D ⊔ G
  have hDE : D ≤ E := le_sup_left
  have hGE : G ≤ E := le_sup_right
  have hE : riemannRochDefect (k := k) (F := F) E =
      (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) := by
    have hlower := riemannRochDefect_mono
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hGE
    have hupper := riemannRochDefect_le_genus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F E
    omega
  have hfull :=
    globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hE
  have hrank := globalAdeleQuotientRank_eq_sandwichRank
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE hfull
  have hsandwich := globalAdeleSandwichRank_eq_defect_sub
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hsandwichGenus :
      globalAdeleSandwichRank (k := k) (F := F) D E hDE =
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) -
          riemannRochDefect (k := k) (F := F) D := by
    rw [hsandwich, hE]
  have hindexGenus :
      (riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D : ℤ) =
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) -
          riemannRochDefect (k := k) (F := F) D := by
    rw [hindex]
    simp only [riemannRochDefect]
    ring
  calc
    globalAdeleQuotientRank (k := k) (F := F) D =
        (globalAdeleSandwichRank (k := k) (F := F) D E hDE).toNat := hrank
    _ = ((functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) -
          riemannRochDefect (k := k) (F := F) D).toNat := by
      rw [hsandwichGenus]
    _ = riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
      rw [← hindexGenus]
      simp only [Int.toNat_natCast]

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
