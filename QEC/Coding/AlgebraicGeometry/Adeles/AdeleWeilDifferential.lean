import Mathlib.LinearAlgebra.Dual.Lemmas
import QEC.Coding.AlgebraicGeometry.Adeles.AdeleQuotient

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Intrinsic adelic Weil differentials

An intrinsic adelic Weil differential is a constant-field linear functional
on the actual restricted product which vanishes on `A(D) + F` for some
all-place divisor `D`.  Its finite vanishing space at a fixed divisor is the
dual annihilator of that denominator, so its rank is the previously computed
specialty index.

The construction and dimension argument follow the architecture of
`RiemannRoch/WeilDifferential/Basic.lean` in Guanghao Li's Apache-2.0
formalization `vaca22/riemann-roch-function-fields` at commit
`dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`, adapted to this repository's
intrinsic global-place carrier.

This file does not yet identify an actual Kähler differential with an adelic
functional.  In particular, it does not prove canonical duality, canonical
degree, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance globalAdeleWeilAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance globalAdeleWeilScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

local instance globalAdeleWeilRiemannRochFiniteDimensional
    (D : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule D) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D

variable [IsFullConstantField k F]

/-- The `k`- and `F`-scalar actions on the intrinsic adele space are
compatible. -/
instance globalAdeleIsScalarTower :
    IsScalarTower k F (GlobalAdele (k := k) (F := F)) :=
  ⟨fun c x a => Subtype.ext <| funext fun P => by
    change (c • x) * a.val P = c • (x * a.val P)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩

/-- An intrinsic adelic Weil differential is a linear functional which
vanishes on `A(D) + F` for some actual all-place divisor. -/
structure GlobalAdeleWeilDifferential where
  /-- The underlying constant-field linear functional on intrinsic adeles. -/
  toFun : GlobalAdele (k := k) (F := F) →ₗ[k] k
  /-- A divisor filtration piece plus the diagonal lies in its kernel. -/
  vanishes_on : ∃ D : Divisor (GlobalPlace k F),
    ∀ a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D,
      toFun a = 0

namespace GlobalAdeleWeilDifferential

variable {k F}

/-- A nonzero intrinsic adelic Weil differential. -/
def IsNonzero (omega : GlobalAdeleWeilDifferential k F) : Prop :=
  omega.toFun ≠ 0

end GlobalAdeleWeilDifferential

/-- The finite space of adelic functionals vanishing on `A(D) + F`. -/
def globalAdeleDifferentialSpace
    (D : Divisor (GlobalPlace k F)) :
    Submodule k (GlobalAdele (k := k) (F := F) →ₗ[k] k) where
  carrier := {psi | ∀ a ∈ globalAdeleFilterAddDiagonal
    (k := k) (F := F) D, psi a = 0}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    intro a ha
    simp only [LinearMap.add_apply, hf a ha, hg a ha, add_zero]
  smul_mem' c f hf := by
    intro a ha
    simp only [LinearMap.smul_apply, RingHom.id_apply, hf a ha, smul_zero]

/-- The fixed-divisor differential space is exactly the dual annihilator of
`A(D) + F`. -/
theorem globalAdeleDifferentialSpace_eq_dualAnnihilator
    (D : Divisor (GlobalPlace k F)) :
    globalAdeleDifferentialSpace (k := k) (F := F) D =
      (globalAdeleFilterAddDiagonal (k := k) (F := F) D).dualAnnihilator := by
  ext psi
  rw [Submodule.mem_dualAnnihilator]
  rfl

/-- The fixed-divisor differential space is finite-dimensional. -/
theorem globalAdeleDifferentialSpace_finite
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k (globalAdeleDifferentialSpace (k := k) (F := F) D) := by
  letI : Module.Finite k (GlobalAdeleQuotient (k := k) (F := F) D) :=
    globalAdeleQuotient_finite
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  rw [globalAdeleDifferentialSpace_eq_dualAnnihilator]
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator
      (globalAdeleFilterAddDiagonal (k := k) (F := F) D))

local instance globalAdeleDifferentialSpaceFinite
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k (globalAdeleDifferentialSpace (k := k) (F := F) D) :=
  globalAdeleDifferentialSpace_finite
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D

/-- The rank of the fixed-divisor adelic differential space is the intrinsic
index of specialty. -/
theorem globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
    (D : Divisor (GlobalPlace k F)) :
    Module.finrank k (globalAdeleDifferentialSpace (k := k) (F := F) D) =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
  let S := globalAdeleFilterAddDiagonal (k := k) (F := F) D
  have hspace : globalAdeleDifferentialSpace (k := k) (F := F) D =
      S.dualAnnihilator :=
    globalAdeleDifferentialSpace_eq_dualAnnihilator
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  rw [hspace, ← S.dualQuotEquivDualAnnihilator.finrank_eq,
    Subspace.dual_finrank_eq]
  exact globalAdeleQuotientRank_eq_indexOfSpecialty
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D

private theorem exists_nontrivial_globalAdeleDifferentialSpace :
    ∃ D : Divisor (GlobalPlace k F),
      globalAdeleDifferentialSpace (k := k) (F := F) D ≠ ⊥ := by
  let E : Divisor (GlobalPlace k F) :=
    polarDivisor (k := k) (F := F) (chartVariable (k := k) (F := F))
  let D : Divisor (GlobalPlace k F) := -(E + E)
  have hEdegree : 0 <
      Divisor.degree (residueDegree (k := k) (F := F)) E := by
    rw [show Divisor.degree (residueDegree (k := k) (F := F)) E =
        (Module.finrank (RatFunc k) F : ℤ) by
      exact polarDivisor_chartVariable_degree_eq_finrank
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F]
    exact_mod_cast Module.finrank_pos (R := RatFunc k) (M := F)
  have hDdegree :
      Divisor.degree (residueDegree (k := k) (F := F)) D < 0 := by
    simp only [D, Divisor.degree_neg, Divisor.degree_add]
    omega
  have hDdegreeStrong :
      Divisor.degree (residueDegree (k := k) (F := F)) D ≤ -2 := by
    simp only [D, Divisor.degree_neg, Divisor.degree_add]
    omega
  letI : FiniteDimensional k (riemannRochSubmodule D) :=
    finiteDimensional_riemannRochSubmodule
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hdimension : riemannRochDimension D = 0 :=
    riemannRochDimension_eq_zero_of_negative_degree
      (k := k) (F := F) D hDdegree
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hindexPositive : 0 < riemannRochIndexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
    have hgenus : 0 ≤
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := Int.natCast_nonneg _
    rw [hdimension] at hindex
    have hindexInt : (0 : ℤ) <
        (riemannRochIndexOfSpecialty
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D : ℤ) := by
      omega
    exact_mod_cast hindexInt
  refine ⟨D, fun hbot => ?_⟩
  have hfinrank : 0 < Module.finrank k
      (globalAdeleDifferentialSpace (k := k) (F := F) D) := by
    rw [globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
    exact hindexPositive
  rw [hbot, finrank_bot] at hfinrank
  omega

/-- A nonzero intrinsic adelic Weil differential exists. -/
theorem exists_nonzero_globalAdeleWeilDifferential :
    ∃ omega : GlobalAdeleWeilDifferential k F,
      GlobalAdeleWeilDifferential.IsNonzero omega := by
  obtain ⟨D, hD⟩ := exists_nontrivial_globalAdeleDifferentialSpace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  obtain ⟨psi, hpsi, hpsiZero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  exact ⟨⟨psi, ⟨D, hpsi⟩⟩, hpsiZero⟩

private theorem valuation_eq_exp_neg_principalDivisor
    (x : Fˣ) (P : GlobalPlace k F) :
    P.valuation (x : F) = WithZero.exp
      (-(principalDivisor (k := k) (F := F) x P)) := by
  rw [principalDivisor_apply, order, neg_neg,
    WithZero.exp_log ((P.valuation).ne_zero_iff.mpr x.ne_zero)]

/-- Multiplication by a nonzero function sends
`A(D + (x)) + F` into `A(D) + F`. -/
theorem mul_mem_globalAdeleFilterAddDiagonal
    (x : Fˣ) (D : Divisor (GlobalPlace k F))
    {a : GlobalAdele (k := k) (F := F)}
    (ha : a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
      (D + principalDivisor (k := k) (F := F) x)) :
    (x : F) • a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D := by
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  refine Submodule.mem_sup.mpr ⟨(x : F) • a₁, ?_, (x : F) • a₂, ?_,
    (smul_add (x : F) a₁ a₂).symm⟩
  · intro P
    change P.valuation ((x : F) * a₁.val P) ≤ WithZero.exp (D P)
    rw [map_mul, valuation_eq_exp_neg_principalDivisor]
    have haP := ha₁ P
    simp only [Finsupp.add_apply, WithZero.exp_add] at haP
    calc
      WithZero.exp (-(principalDivisor (k := k) (F := F) x P)) *
          P.valuation (a₁.val P) ≤
          WithZero.exp (-(principalDivisor (k := k) (F := F) x P)) *
            (WithZero.exp (D P) *
              WithZero.exp (principalDivisor (k := k) (F := F) x P)) :=
        mul_le_mul_right haP _
      _ = WithZero.exp (D P) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        ring
  · rcases ha₂ with ⟨f, rfl⟩
    exact ⟨(x : F) * f, by ext P; rfl⟩

namespace GlobalAdeleWeilDifferential

variable {k F}

/-- Scalar multiplication of an adelic Weil differential by a function. -/
noncomputable def smulWeil (x : F) (omega : GlobalAdeleWeilDifferential k F) :
    GlobalAdeleWeilDifferential k F := by
  by_cases hx : x = 0
  · exact ⟨0, ⟨0, by simp⟩⟩
  let xu : Fˣ := Units.mk0 x hx
  refine ⟨omega.toFun.comp (mulGlobalAdeleLinear (k := k) (F := F) x), ?_⟩
  obtain ⟨D, hD⟩ := omega.vanishes_on
  refine ⟨D + principalDivisor (k := k) (F := F) xu, fun a ha => hD _ ?_⟩
  change x • a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D
  simpa only [xu, Units.val_mk0] using
    (mul_mem_globalAdeleFilterAddDiagonal
      (k := k) (F := F) xu D ha)

@[simp]
theorem smulWeil_toFun_apply (x : F)
    (omega : GlobalAdeleWeilDifferential k F)
    (a : GlobalAdele (k := k) (F := F)) :
    (smulWeil x omega).toFun a = omega.toFun (x • a) := by
  by_cases hx : x = 0
  · simp [smulWeil, hx]
  · simp only [smulWeil, hx, ↓reduceDIte, LinearMap.comp_apply]
    congr 1

instance : Zero (GlobalAdeleWeilDifferential k F) :=
  ⟨⟨0, ⟨0, by simp⟩⟩⟩

instance : Add (GlobalAdeleWeilDifferential k F) where
  add omega eta := ⟨omega.toFun + eta.toFun, by
    obtain ⟨Domega, homega⟩ := omega.vanishes_on
    obtain ⟨Deta, heta⟩ := eta.vanishes_on
    refine ⟨Domega ⊓ Deta, fun a ha => ?_⟩
    have hleft : globalAdeleFilterAddDiagonal (k := k) (F := F)
        (Domega ⊓ Deta) ≤
        globalAdeleFilterAddDiagonal (k := k) (F := F) Domega := by
      exact sup_le_sup
        (globalAdeleFilter_mono (k := k) (F := F) inf_le_left) le_rfl
    have hright : globalAdeleFilterAddDiagonal (k := k) (F := F)
        (Domega ⊓ Deta) ≤
        globalAdeleFilterAddDiagonal (k := k) (F := F) Deta := by
      exact sup_le_sup
        (globalAdeleFilter_mono (k := k) (F := F) inf_le_right) le_rfl
    simp only [LinearMap.add_apply, homega a (hleft ha), heta a (hright ha),
      add_zero]⟩

@[ext]
theorem ext {omega eta : GlobalAdeleWeilDifferential k F}
    (h : omega.toFun = eta.toFun) : omega = eta := by
  cases omega
  cases eta
  cases h
  rfl

instance : Neg (GlobalAdeleWeilDifferential k F) where
  neg omega := ⟨-omega.toFun, by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    exact ⟨D, fun a ha => by simp only [LinearMap.neg_apply, hD a ha, neg_zero]⟩⟩

instance : AddCommGroup (GlobalAdeleWeilDifferential k F) where
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  add_comm _ _ := ext (add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := ext rfl
  nsmul_succ _ _ := ext rfl
  neg := Neg.neg
  neg_add_cancel omega := ext (neg_add_cancel omega.toFun)
  sub := fun omega eta => omega + -eta
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

@[simp]
theorem add_toFun (omega eta : GlobalAdeleWeilDifferential k F) :
    (omega + eta).toFun = omega.toFun + eta.toFun := rfl

noncomputable instance : SMul F (GlobalAdeleWeilDifferential k F) :=
  ⟨smulWeil⟩

noncomputable instance : Module F (GlobalAdeleWeilDifferential k F) :=
  Module.ofMinimalAxioms
    (fun x omega eta => by
      apply ext
      ext a
      change (smulWeil x (omega + eta)).toFun a =
        ((smulWeil x omega).toFun + (smulWeil x eta).toFun) a
      rw [smulWeil_toFun_apply]
      change (omega.toFun + eta.toFun) (x • a) =
        (smulWeil x omega).toFun a + (smulWeil x eta).toFun a
      rw [LinearMap.add_apply, smulWeil_toFun_apply, smulWeil_toFun_apply])
    (fun x y omega => by
      apply ext
      ext a
      change (smulWeil (x + y) omega).toFun a =
        ((smulWeil x omega).toFun + (smulWeil y omega).toFun) a
      rw [smulWeil_toFun_apply]
      change omega.toFun ((x + y) • a) =
        (smulWeil x omega).toFun a + (smulWeil y omega).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply, add_smul, map_add])
    (fun x y omega => by
      apply ext
      ext a
      change (smulWeil (x * y) omega).toFun a =
        (smulWeil x (smulWeil y omega)).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply,
        smulWeil_toFun_apply, ← mul_smul, mul_comm x y])
    (fun omega => by
      apply ext
      ext a
      change (smulWeil 1 omega).toFun a = omega.toFun a
      rw [smulWeil_toFun_apply, one_smul])

theorem smulWeil_algebraMap (c : k)
    (omega : GlobalAdeleWeilDifferential k F)
    (a : GlobalAdele (k := k) (F := F)) :
    (smulWeil (algebraMap k F c) omega).toFun a = c • omega.toFun a := by
  rw [smulWeil_toFun_apply, algebraMap_smul, map_smul]

theorem smulWeil_eq_zero_iff (x : F) (hx : x ≠ 0)
    (omega : GlobalAdeleWeilDifferential k F) :
    smulWeil x omega = 0 ↔ omega = 0 := by
  constructor
  · intro hxomega
    calc
      omega = (1 : F) • omega := (one_smul F omega).symm
      _ = (x⁻¹ * x) • omega := by rw [inv_mul_cancel₀ hx]
      _ = x⁻¹ • (x • omega) := mul_smul x⁻¹ x omega
      _ = x⁻¹ • smulWeil x omega := rfl
      _ = x⁻¹ • (0 : GlobalAdeleWeilDifferential k F) := by rw [hxomega]
      _ = 0 := smul_zero x⁻¹
  · intro homega
    subst omega
    exact smul_zero x

end GlobalAdeleWeilDifferential

/-- Divisors on whose filtration-plus-diagonal an adelic functional
vanishes. -/
def globalAdeleVanishingDivisors
    (omega : GlobalAdeleWeilDifferential k F) :
    Set (Divisor (GlobalPlace k F)) :=
  {D | ∀ a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F) D,
    omega.toFun a = 0}

theorem globalAdeleVanishingDivisors_mono
    {omega : GlobalAdeleWeilDifferential k F}
    {D E : Divisor (GlobalPlace k F)} (hED : E ≤ D)
    (hD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega) :
    E ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by
  intro a ha
  apply hD a
  exact (sup_le_sup
    (globalAdeleFilter_mono (k := k) (F := F) hED) le_rfl) ha

private theorem le_add_principal_of_mem_riemannRochSubmodule'
    {D₀ D₁ : Divisor (GlobalPlace k F)} {f : F} (hf : f ≠ 0)
    (hmem : f ∈ riemannRochSubmodule (D₁ - D₀)) :
    D₀ ≤ D₁ + principalDivisor (k := k) (F := F) (Units.mk0 f hf) := by
  intro P
  have hP :=
    (mem_riemannRochSubmodule_iff_order_add_nonnegative (D₁ - D₀) hf).mp
      hmem P
  simp only [Finsupp.sub_apply] at hP
  rw [Finsupp.add_apply, principalDivisor_apply]
  simp only [Units.val_mk0]
  omega

private theorem smulWeil_toFun_mem_globalAdeleDifferentialSpace
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    {E : Divisor (GlobalPlace k F)} (f : riemannRochSubmodule E) :
    (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun ∈
      globalAdeleDifferentialSpace (k := k) (F := F) (D₀ - E) := by
  intro a ha
  rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply]
  by_cases hf : (f : F) = 0
  · rw [hf, zero_smul, map_zero]
  · have hmem : (f : F) ∈ riemannRochSubmodule
        (D₀ - (D₀ - E)) := by
      rw [sub_sub_cancel]
      exact f.property
    have hdivle : D₀ - E ≤ D₀ +
        principalDivisor (k := k) (F := F) (Units.mk0 (f : F) hf) :=
      le_add_principal_of_mem_riemannRochSubmodule'
        (k := k) (F := F) hf hmem
    have ha' : a ∈ globalAdeleFilterAddDiagonal (k := k) (F := F)
        (D₀ + principalDivisor (k := k) (F := F)
          (Units.mk0 (f : F) hf)) :=
      (sup_le_sup (globalAdeleFilter_mono (k := k) (F := F) hdivle)
        le_rfl) ha
    exact hD₀ _ (by
      simpa only [Units.val_mk0] using
        (mul_mem_globalAdeleFilterAddDiagonal
          (k := k) (F := F) (Units.mk0 (f : F) hf) D₀ ha'))

/-- Multiplication into a fixed adelic Weil differential sends `L(E)` into
the vanishing space at `D₀ - E`. -/
noncomputable def globalAdeleSmulIntoDifferentialSpace
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (E : Divisor (GlobalPlace k F)) :
    riemannRochSubmodule E →ₗ[k]
      globalAdeleDifferentialSpace (k := k) (F := F) (D₀ - E) where
  toFun f := ⟨(GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun,
    smulWeil_toFun_mem_globalAdeleDifferentialSpace
      (k := k) (F := F) omega hD₀ f⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (GlobalAdeleWeilDifferential.smulWeil
        ((f : F) + (g : F)) omega).toFun a =
      (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun a +
        (GlobalAdeleWeilDifferential.smulWeil (g : F) omega).toFun a
    rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      GlobalAdeleWeilDifferential.smulWeil_toFun_apply, add_smul, map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (GlobalAdeleWeilDifferential.smulWeil
        (c • (f : F)) omega).toFun a =
      c • (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun a
    rw [GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      GlobalAdeleWeilDifferential.smulWeil_toFun_apply,
      Algebra.smul_def, mul_smul, algebraMap_smul, map_smul]

@[simp]
theorem globalAdeleSmulIntoDifferentialSpace_coe
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (E : Divisor (GlobalPlace k F)) (f : riemannRochSubmodule E) :
    (globalAdeleSmulIntoDifferentialSpace
        (k := k) (F := F) omega hD₀ E f :
      GlobalAdele (k := k) (F := F) →ₗ[k] k) =
      (GlobalAdeleWeilDifferential.smulWeil (f : F) omega).toFun := rfl

theorem globalAdeleSmulIntoDifferentialSpace_injective
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (E : Divisor (GlobalPlace k F)) (homega : omega.toFun ≠ 0) :
    Function.Injective
      (globalAdeleSmulIntoDifferentialSpace
        (k := k) (F := F) omega hD₀ E) := by
  intro f g hfg
  by_contra hne
  have hdifference : globalAdeleSmulIntoDifferentialSpace
      (k := k) (F := F) omega hD₀ E (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hvalue : (((f - g : riemannRochSubmodule E) : F)) ≠ 0 := by
    intro hzero
    exact hne (sub_eq_zero.mp (Subtype.ext hzero))
  have htoFun :
      (GlobalAdeleWeilDifferential.smulWeil
        ((f - g : riemannRochSubmodule E) : F) omega).toFun = 0 :=
    congrArg Subtype.val hdifference
  have hzero : GlobalAdeleWeilDifferential.smulWeil
      ((f - g : riemannRochSubmodule E) : F) omega = 0 :=
    GlobalAdeleWeilDifferential.ext htoFun
  have homegaZero :=
    (GlobalAdeleWeilDifferential.smulWeil_eq_zero_iff
      ((f - g : riemannRochSubmodule E) : F) hvalue omega).mp hzero
  apply homega
  rw [homegaZero]
  rfl

private theorem divisorDegree_nsmul'
    (n : ℕ) (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom (residueDegree (k := k) (F := F))).map_nsmul n D

/-- The space of intrinsic adelic Weil differentials is one-dimensional over
the function field. -/
theorem globalAdeleWeilDifferential_finrank_eq_one :
    Module.finrank F (GlobalAdeleWeilDifferential k F) = 1 := by
  obtain ⟨omega₀, homega₀⟩ :=
    exists_nonzero_globalAdeleWeilDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have homega₀ne : omega₀ ≠ 0 := by
    intro hzero
    apply homega₀
    rw [hzero]
    rfl
  refine (finrank_eq_one_iff_of_nonzero' omega₀ homega₀ne).mpr ?_
  intro omega
  by_contra hspan
  push Not at hspan
  have hindependent : ∀ f g : F,
      f • omega₀ + g • omega = 0 → f = 0 ∧ g = 0 := by
    intro f g hfg
    by_cases hg : g = 0
    · subst g
      rw [zero_smul, add_zero] at hfg
      refine ⟨?_, rfl⟩
      by_contra hf
      exact homega₀ne
        ((GlobalAdeleWeilDifferential.smulWeil_eq_zero_iff
          f hf omega₀).mp hfg)
    · exfalso
      apply hspan (g⁻¹ * (-f))
      have hgomega : g • omega = (-f) • omega₀ := by
        have hneg : g • omega = -(f • omega₀) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hfg
        rw [hneg, neg_smul]
      have homega : omega = (g⁻¹ * (-f)) • omega₀ := by
        rw [mul_smul, ← hgomega, ← mul_smul, inv_mul_cancel₀ hg, one_smul]
      exact homega.symm
  obtain ⟨D₁, hD₁⟩ := omega₀.vanishes_on
  obtain ⟨D₂, hD₂⟩ := omega.vanishes_on
  let D₀ : Divisor (GlobalPlace k F) := D₁ ⊓ D₂
  have h₀ : D₀ ∈ globalAdeleVanishingDivisors
      (k := k) (F := F) omega₀ :=
    globalAdeleVanishingDivisors_mono
      (k := k) (F := F) inf_le_left hD₁
  have h₂ : D₀ ∈ globalAdeleVanishingDivisors
      (k := k) (F := F) omega :=
    globalAdeleVanishingDivisors_mono
      (k := k) (F := F) inf_le_right hD₂
  let B : Divisor (GlobalPlace k F) :=
    polarDivisor (k := k) (F := F) (chartVariable (k := k) (F := F))
  have hBpositive : 0 <
      Divisor.degree (residueDegree (k := k) (F := F)) B := by
    rw [show Divisor.degree (residueDegree (k := k) (F := F)) B =
        (Module.finrank (RatFunc k) F : ℤ) by
      exact polarDivisor_chartVariable_degree_eq_finrank
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F]
    exact_mod_cast Module.finrank_pos (R := RatFunc k) (M := F)
  have hBone : 1 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) B := hBpositive
  have hcount : ∀ n : ℕ,
      2 * (riemannRochDimension (n • B) : ℤ) ≤
        (riemannRochIndexOfSpecialty
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
          k F (D₀ - n • B) : ℤ) := by
    intro n
    let E : Divisor (GlobalPlace k F) := n • B
    have hinjective : Function.Injective
        (LinearMap.coprod
          (globalAdeleSmulIntoDifferentialSpace
            (k := k) (F := F) omega₀ h₀ E)
          (globalAdeleSmulIntoDifferentialSpace
            (k := k) (F := F) omega h₂ E)) := by
      intro x y hxy
      have hdifference :
          (LinearMap.coprod
            (globalAdeleSmulIntoDifferentialSpace
              (k := k) (F := F) omega₀ h₀ E)
            (globalAdeleSmulIntoDifferentialSpace
              (k := k) (F := F) omega h₂ E)) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      rw [LinearMap.coprod_apply] at hdifference
      have hcoe :
          (GlobalAdeleWeilDifferential.smulWeil
              (((x - y).1 : riemannRochSubmodule E) : F) omega₀).toFun +
            (GlobalAdeleWeilDifferential.smulWeil
              (((x - y).2 : riemannRochSubmodule E) : F) omega).toFun = 0 := by
        have hvalue := congrArg Subtype.val hdifference
        simpa only [Submodule.coe_add,
          globalAdeleSmulIntoDifferentialSpace_coe,
          Submodule.coe_zero] using hvalue
      have hsum :
          ((((x - y).1 : riemannRochSubmodule E) : F) • omega₀ +
            (((x - y).2 : riemannRochSubmodule E) : F) • omega).toFun = 0 := by
        rw [GlobalAdeleWeilDifferential.add_toFun]
        exact hcoe
      have hzero :
          (((x - y).1 : riemannRochSubmodule E) : F) • omega₀ +
            (((x - y).2 : riemannRochSubmodule E) : F) • omega = 0 :=
        GlobalAdeleWeilDifferential.ext hsum
      obtain ⟨hfzero, hgzero⟩ := hindependent _ _ hzero
      have hxyzero : x - y = 0 :=
        Prod.ext (Subtype.ext hfzero) (Subtype.ext hgzero)
      exact sub_eq_zero.mp hxyzero
    have hfinrank :
        Module.finrank k (riemannRochSubmodule E × riemannRochSubmodule E) ≤
          Module.finrank k
            (globalAdeleDifferentialSpace (k := k) (F := F) (D₀ - E)) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_prod,
      globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty] at hfinrank
    have hdimension : Module.finrank k (riemannRochSubmodule E) =
        riemannRochDimension E := rfl
    rw [hdimension] at hfinrank
    dsimp only [E] at hfinrank
    omega
  let genus := functionFieldGenus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  let M : ℤ := max
    (Divisor.degree (residueDegree (k := k) (F := F)) D₀)
    (3 * (genus : ℤ) - 3 -
      Divisor.degree (residueDegree (k := k) (F := F)) D₀)
  let n : ℕ := M.toNat + 1
  have hnLarge : (n : ℤ) ≥ M + 1 := by
    have hself := Int.self_le_toNat M
    push_cast [n]
    omega
  have hnD₀ : (n : ℤ) >
      Divisor.degree (residueDegree (k := k) (F := F)) D₀ := by
    have hle : Divisor.degree (residueDegree (k := k) (F := F)) D₀ ≤ M :=
      le_max_left _ _
    omega
  have hnGenus : (n : ℤ) > 3 * (genus : ℤ) - 3 -
      Divisor.degree (residueDegree (k := k) (F := F)) D₀ := by
    have hle : 3 * (genus : ℤ) - 3 -
        Divisor.degree (residueDegree (k := k) (F := F)) D₀ ≤ M :=
      le_max_right _ _
    omega
  have hnBDegree : (n : ℤ) *
      Divisor.degree (residueDegree (k := k) (F := F)) B ≥ (n : ℤ) := by
    have hnNonnegative : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    nlinarith [hBone, hnNonnegative]
  have hdegreeSub :
      Divisor.degree (residueDegree (k := k) (F := F)) (D₀ - n • B) =
        Divisor.degree (residueDegree (k := k) (F := F)) D₀ -
          (n : ℤ) *
            Divisor.degree (residueDegree (k := k) (F := F)) B := by
    rw [Divisor.degree_sub, divisorDegree_nsmul']
  have hdegreeNegative :
      Divisor.degree (residueDegree (k := k) (F := F)) (D₀ - n • B) < 0 := by
    rw [hdegreeSub]
    omega
  have hdimensionZero : riemannRochDimension (D₀ - n • B) = 0 :=
    riemannRochDimension_eq_zero_of_negative_degree
      (k := k) (F := F) (D₀ - n • B) hdegreeNegative
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (D₀ - n • B)
  rw [hdimensionZero, hdegreeSub] at hindex
  have hlower := riemannRochDimension_lower_bound
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (n • B)
  rw [divisorDegree_nsmul'] at hlower
  have hcountN := hcount n
  dsimp only [genus] at hnGenus hindex hlower
  omega

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
