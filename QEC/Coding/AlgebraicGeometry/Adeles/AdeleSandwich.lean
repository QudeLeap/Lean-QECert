import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import QEC.Coding.AlgebraicGeometry.Adeles.AdeleEffectiveIncrement
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Genus

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# The intrinsic adele sandwich

For comparable divisors `D ≤ E`, adjoining the diagonal function field to
the intrinsic adele filtration loses exactly the difference of the two
Riemann--Roch defects.  A divisor attaining the maximal defect therefore
saturates the whole adele space modulo the diagonal.

The finite-dimensional sandwich argument follows the architecture of
`RiemannRoch/AdeleSpace/FilterChain.lean` and
`RiemannRoch/Genus/AdeleQuotient.lean` in Guanghao Li's Apache-2.0
formalization `vaca22/riemann-roch-function-fields` at commit
`dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`, adapted to this repository's
intrinsic global-place carrier.

No specialty duality, Weil-differential classification, canonical-degree
formula, or Riemann--Roch identity is assumed or proved here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Filter
open scoped Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance globalAdeleSandwichAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance globalAdeleSandwichScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

variable [IsFullConstantField k F]

local instance globalAdeleSandwichRiemannRochFiniteDimensional
    (D : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule D) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D

local instance globalAdeleSandwichFilterAddCommGroup
    (D : Divisor (GlobalPlace k F)) :
    AddCommGroup (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.addCommGroup _

local instance globalAdeleSandwichFilterModule
    (D : Divisor (GlobalPlace k F)) :
    Module k (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.module _

/-- The top submodule of the intrinsic adele space. -/
def globalAdeleTopSubmodule :
    Submodule k (GlobalAdele (k := k) (F := F)) :=
  ⊤

private theorem globalAdeleExceptionalFinite
    (a : GlobalAdele (k := k) (F := F)) :
    {P : GlobalPlace k F | ¬P.valuation (a.val P) ≤ 1}.Finite :=
  (Filter.eventually_cofinite.mp a.property).subset (by
    intro P hP
    change a.val P ∉ P.valuationRing
    rw [mem_valuationRing_iff]
    exact hP)

private noncomputable def globalAdeleExceptionalPlaces
    (a : GlobalAdele (k := k) (F := F)) : Finset (GlobalPlace k F) :=
  (globalAdeleExceptionalFinite (k := k) (F := F) a).toFinset

private noncomputable def divisorOfGlobalAdele
    (a : GlobalAdele (k := k) (F := F)) :
    Divisor (GlobalPlace k F) :=
  Finsupp.onFinset (globalAdeleExceptionalPlaces (k := k) (F := F) a)
    (fun P =>
      if 1 < P.valuation (a.val P) then
        WithZero.log (P.valuation (a.val P))
      else 0)
    (by
      intro P hP
      by_cases hlt : 1 < P.valuation (a.val P)
      · dsimp only [globalAdeleExceptionalPlaces]
        exact (globalAdeleExceptionalFinite (k := k) (F := F) a).mem_toFinset.mpr
          (not_le.mpr hlt)
      · simp only [hlt, ite_false, ne_eq, not_true_eq_false] at hP)

private theorem mem_globalAdeleFilter_divisorOfGlobalAdele
    (a : GlobalAdele (k := k) (F := F)) :
    a ∈ globalAdeleFilter (k := k) (F := F)
      (divisorOfGlobalAdele (k := k) (F := F) a) := by
  intro P
  show P.valuation (a.val P) ≤
    WithZero.exp (divisorOfGlobalAdele (k := k) (F := F) a P)
  change P.valuation (a.val P) ≤ WithZero.exp
    (if 1 < P.valuation (a.val P) then
      WithZero.log (P.valuation (a.val P)) else 0)
  by_cases hP : P.valuation (a.val P) ≤ 1
  · have hnotlt : ¬1 < P.valuation (a.val P) := not_lt.mpr hP
    rw [if_neg hnotlt, WithZero.exp_zero]
    exact hP
  · have hlt : 1 < P.valuation (a.val P) := not_le.mp hP
    have hval : P.valuation (a.val P) ≠ 0 :=
      ne_of_gt (zero_lt_one.trans hlt)
    rw [if_pos hlt, WithZero.exp_log hval]

/-- Every intrinsic adele belongs to some divisor-filtration piece. -/
theorem exists_globalAdeleFilter_mem
    (a : GlobalAdele (k := k) (F := F)) :
    ∃ D : Divisor (GlobalPlace k F),
      a ∈ globalAdeleFilter (k := k) (F := F) D :=
  ⟨divisorOfGlobalAdele (k := k) (F := F) a,
    mem_globalAdeleFilter_divisorOfGlobalAdele (k := k) (F := F) a⟩

private noncomputable def riemannRochFilterDiffDimension
    (D E : Divisor (GlobalPlace k F)) : ℕ :=
  Module.finrank k
    (riemannRochSubmodule E ⧸
      Submodule.comap (riemannRochSubmodule E).subtype
        (riemannRochSubmodule D))

private theorem riemannRochFilterDiffDimension_add
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    riemannRochFilterDiffDimension (k := k) (F := F) D E +
        riemannRochDimension D =
      riemannRochDimension E := by
  let p := riemannRochSubmodule E
  let q := Submodule.comap p.subtype (riemannRochSubmodule D)
  have hq : Module.finrank k q = riemannRochDimension D := by
    let e := Submodule.comapSubtypeEquivOfLe
      (riemannRochSubmodule_mono (k := k) (F := F) hDE)
    simpa only [p, q, riemannRochDimension] using e.finrank_eq
  have hadd := Submodule.finrank_quotient_add_finrank q
  simpa only [riemannRochFilterDiffDimension, riemannRochDimension, p, q, hq]
    using hadd

private theorem globalPlace_nonempty : Nonempty (GlobalPlace k F) := by
  obtain ⟨D⟩ := InverseAffinePlace.infinityFibre_nonempty
    (oldRationalAlgebra := ρ) k F
  exact ⟨InverseAffinePlace.infinityFibreGlobalPlace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s) D⟩

private theorem diagonalAdele_injective :
    Function.Injective (diagonalAdele (k := k) (F := F)) := by
  intro x y hxy
  let P := Classical.choice (globalPlace_nonempty
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  have hvalue := congrArg
    (fun a : GlobalAdele (k := k) (F := F) => a.val P) hxy
  exact hvalue

/-- The finite rank of `(A(E) + F) / (A(D) + F)` for `D ≤ E`, recorded as
an integer so it can be compared directly with divisor degrees and defects. -/
@[nolint unusedArguments]
noncomputable def globalAdeleSandwichRank
    (D E : Divisor (GlobalPlace k F)) (_hDE : D ≤ E) : ℤ := by
  letI : AddCommGroup
      (globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :=
    Submodule.addCommGroup _
  letI : Module k
      (globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) :=
    Submodule.module _
  exact Int.ofNat (Module.finrank k
    (↥(globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F)) ⧸
      Submodule.comap
        (globalAdeleFilter (k := k) (F := F) E +
          diagonalAdeleSubmodule (k := k) (F := F)).subtype
        (globalAdeleFilter (k := k) (F := F) D +
          diagonalAdeleSubmodule (k := k) (F := F))))

private theorem finrank_map_comap_mkQ_eq_quotient
    {E : Divisor (GlobalPlace k F)}
    {s t : Submodule k (GlobalAdele (k := k) (F := F))}
    (_hs : s ≤ globalAdeleFilter (k := k) (F := F) E)
    (ht : t ≤ globalAdeleFilter (k := k) (F := F) E) (_hst : s ≤ t) :
    Module.finrank k
        (Submodule.map
          (Submodule.comap
            (globalAdeleFilter (k := k) (F := F) E).subtype s).mkQ
          (Submodule.comap
            (globalAdeleFilter (k := k) (F := F) E).subtype t)) =
      Module.finrank k
        (↥(Submodule.comap
            (globalAdeleFilter (k := k) (F := F) E).subtype t) ⧸
          Submodule.comap
            (Submodule.comap
              (globalAdeleFilter (k := k) (F := F) E).subtype t).subtype
            (Submodule.comap
              (globalAdeleFilter (k := k) (F := F) E).subtype s)) := by
  classical
  let p := globalAdeleFilter (k := k) (F := F) E
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  let st := Submodule.comap t.subtype s
  let qpInQt := Submodule.comap qt.subtype qp
  letI : AddCommGroup t := Submodule.addCommGroup _
  letI : Module k t := Submodule.module _
  letI : AddCommGroup qt := Submodule.addCommGroup _
  letI : Module k qt := Submodule.module _
  let eT := Submodule.comapSubtypeEquivOfLe ht
  have hmap : st.map (eT.symm : t →ₗ[k] qt) = qpInQt := by
    ext x
    simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
  have hker : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).ker = qpInQt := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).range =
      Submodule.map qp.mkQ qt := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (qt ⧸ qpInQt) ≃ₗ[k] Submodule.map qp.mkQ qt := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p))
  have eTS : (t ⧸ st) ≃ₗ[k] (qt ⧸ qpInQt) :=
    Submodule.Quotient.equiv st qpInQt eT.symm hmap
  rw [← eQuot.finrank_eq, ← eTS.finrank_eq]

/-- The intrinsic adele sandwich rank is the difference of the actual
Riemann--Roch defects. -/
theorem globalAdeleSandwichRank_eq_defect_sub
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    globalAdeleSandwichRank (k := k) (F := F) D E hDE =
      riemannRochDefect (k := k) (F := F) E -
        riemannRochDefect (k := k) (F := F) D := by
  let p := globalAdeleFilter (k := k) (F := F) E
  let sA := globalAdeleFilter (k := k) (F := F) D
  let r := diagonalAdeleSubmodule (k := k) (F := F)
  let l := Submodule.map (diagonalAdele (k := k) (F := F))
    (riemannRochSubmodule E)
  let t := l ⊔ sA
  have hs_le_p : sA ≤ p := globalAdeleFilter_mono hDE
  have hst : sA ≤ t := le_sup_right
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      (by exact hf)
      (hs_le_p hz)
  have hmod : p ⊓ (sA + r) = sA + p ⊓ r := by
    apply le_antisymm
    · rintro x ⟨hxp, hxsr⟩
      rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_sup.mpr ⟨a, has, diagonalAdele (k := k) (F := F) f,
        ?_, rfl⟩
      exact Submodule.mem_inf.mpr
        ⟨(by simpa only [add_sub_cancel_left] using
            Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
    · rintro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
      rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
      exact ⟨Submodule.add_mem p (hs_le_p has) hyp,
        Submodule.add_mem (sA + r) (Submodule.mem_sup_left has)
          (Submodule.mem_sup_right hyr)⟩
  have hinter : p ⊓ (sA + r) = t := by
    have hpr : p ⊓ r = l := globalAdeleFilter_inf_diagonal E
    calc
      p ⊓ (sA + r) = sA + (p ⊓ r) := hmod
      _ = sA + l := by rw [hpr]
      _ = t := by simp only [t, Submodule.add_eq_sup, sup_comm]
  letI : AddCommGroup p := Submodule.addCommGroup _
  letI : Module k p := Submodule.module _
  letI : AddCommGroup (p + r) := Submodule.addCommGroup _
  letI : Module k (p + r) := Submodule.module _
  let qp := Submodule.comap p.subtype sA
  let qt := Submodule.comap p.subtype t
  have hqp : qp ≤ qt := Submodule.comap_mono hst
  have hpsum : p ⊔ (sA + r) = p + r := by
    rw [← Submodule.add_eq_sup]
    apply le_antisymm
    · exact sup_le le_sup_left (add_le_add hs_le_p le_rfl)
    · intro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
      have hb' : b ∈ sA + r := Submodule.mem_sup_right hb
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
        (Submodule.mem_sup_right hb')
  letI : AddCommGroup ↥(p ⊔ (sA + r)) := Submodule.addCommGroup _
  letI : Module k ↥(p ⊔ (sA + r)) := Submodule.module _
  have e1 := LinearMap.quotientInfEquivSupQuotient p (sA + r)
  have hsand :
      Module.finrank k
          ((p + r) ⧸ Submodule.comap (p + r).subtype (sA + r)) =
        Module.finrank k (p ⧸ qt) := by
    have hinfl :
        Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (sA + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hfin := e1.symm.finrank_eq
    rw [← hpsum.symm, hinfl] at hfin
    exact hfin
  haveI : Module.Finite k (p ⧸ qp) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDE
  have e2 := Submodule.quotientQuotientEquivQuotient qp qt hqp
  have hsecond :
      Module.finrank k (Submodule.map qp.mkQ qt) =
        riemannRochFilterDiffDimension (k := k) (F := F) D E := by
    have hfin_map := finrank_map_comap_mkQ_eq_quotient
      (k := k) (F := F) hs_le_p htp hst
    let st := Submodule.comap t.subtype sA
    let qpInQt := Submodule.comap qt.subtype qp
    letI : AddCommGroup t := Submodule.addCommGroup _
    letI : Module k t := Submodule.module _
    let eT := Submodule.comapSubtypeEquivOfLe htp
    have hmap : st.map (eT.symm : t →ₗ[k] qt) = qpInQt := by
      ext x
      simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
    have eTS : (t ⧸ st) ≃ₗ[k] (qt ⧸ qpInQt) :=
      Submodule.Quotient.equiv st qpInQt eT.symm hmap
    have e3 := LinearMap.quotientInfEquivSupQuotient l sA
    letI : AddCommGroup ↥(l ⊔ sA) := Submodule.addCommGroup _
    letI : Module k ↥(l ⊔ sA) := Submodule.module _
    letI : AddCommGroup l := Submodule.addCommGroup _
    letI : Module k l := Submodule.module _
    calc
      Module.finrank k (Submodule.map qp.mkQ qt) =
          Module.finrank k (qt ⧸ Submodule.comap qt.subtype qp) := hfin_map
      _ = Module.finrank k (t ⧸ st) := eTS.finrank_eq.symm
      _ = Module.finrank k
          (↥(l ⊔ sA) ⧸ Submodule.comap (l ⊔ sA).subtype sA) := rfl
      _ = Module.finrank k
          (l ⧸ (Submodule.comap l.subtype l ⊓
            Submodule.comap l.subtype sA)) := e3.symm.finrank_eq
      _ = riemannRochFilterDiffDimension (k := k) (F := F) D E := by
        let pR := riemannRochSubmodule E
        let qR := Submodule.comap pR.subtype (riemannRochSubmodule D)
        let qInL : Submodule k l := Submodule.comap l.subtype
          (Submodule.map (diagonalAdele (k := k) (F := F))
            (riemannRochSubmodule D))
        let f' := (diagonalAdele (k := k) (F := F)).comp pR.subtype
        have hf' : ∀ g, f' g ∈ l := fun g =>
          Submodule.mem_map.mpr ⟨g, g.property, rfl⟩
        let f : pR →ₗ[k] l := f'.codRestrict l hf'
        have hf_inj : Function.Injective f := by
          intro g₁ g₂ hfg
          apply Subtype.ext
          apply diagonalAdele_injective (k := k) (F := F)
          exact congrArg Subtype.val hfg
        have hf_surj : Function.Surjective f := by
          rintro ⟨a, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
        let eL : pR ≃ₗ[k] l := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
        have hld : l ⊓ sA =
            Submodule.map (diagonalAdele (k := k) (F := F))
              (riemannRochSubmodule D) := by
          rw [show l = p ⊓ r from (globalAdeleFilter_inf_diagonal E).symm]
          rw [inf_right_comm, inf_eq_right.mpr hs_le_p,
            globalAdeleFilter_inf_diagonal D]
        have hmapR : qR.map f = qInL := by
          ext x
          simp only [Submodule.mem_map, Submodule.mem_comap, qR, qInL, l]
          constructor
          · rintro ⟨g, hg, heq⟩
            refine ⟨g.val, ?_, ?_⟩
            · exact hg
            · rw [← heq]
              rfl
          · rintro ⟨y, hy, hxy⟩
            refine ⟨⟨y, riemannRochSubmodule_mono (k := k) (F := F) hDE hy⟩,
              hy, ?_⟩
            apply Subtype.ext
            exact hxy
        have eQuot : (pR ⧸ qR) ≃ₗ[k] (l ⧸ qInL) :=
          Submodule.Quotient.equiv qR qInL eL hmapR
        dsimp only [riemannRochFilterDiffDimension]
        rw [← Submodule.comap_inf, hld, eQuot.finrank_eq]
  have hsplit :
      Module.finrank k (p ⧸ qt) =
        globalAdeleFilterDiffDimension (k := k) (F := F) D E -
          riemannRochFilterDiffDimension (k := k) (F := F) D E := by
    have hle : Module.finrank k (Submodule.map qp.mkQ qt) ≤
        Module.finrank k (p ⧸ qp) := Submodule.finrank_le _
    have hadd := Submodule.finrank_quotient_add_finrank (Submodule.map qp.mkQ qt)
    rw [e2.finrank_eq, hsecond] at hadd
    dsimp only [globalAdeleFilterDiffDimension]
    exact (Nat.sub_eq_of_eq_add hadd.symm).symm
  have hfilter := globalAdeleFilterDiffDimension_of_le
    (k := k) (F := F) hDE
  have hdegreeNonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) (E - D) := by
    apply Divisor.degree_nonnegative
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hrr := riemannRochFilterDiffDimension_add
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hle : riemannRochFilterDiffDimension (k := k) (F := F) D E ≤
      globalAdeleFilterDiffDimension (k := k) (F := F) D E := by
    dsimp only [globalAdeleFilterDiffDimension]
    rw [← hsecond]
    exact Submodule.finrank_le _
  have hmain :
      globalAdeleSandwichRank (k := k) (F := F) D E hDE =
        (globalAdeleFilterDiffDimension (k := k) (F := F) D E : ℤ) -
          riemannRochFilterDiffDimension (k := k) (F := F) D E := by
    dsimp only [globalAdeleSandwichRank]
    rw [hsand, hsplit]
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hle]
  have hfilterZ :
      (globalAdeleFilterDiffDimension (k := k) (F := F) D E : ℤ) =
        Divisor.degree (residueDegree (k := k) (F := F)) (E - D) := by
    rw [hfilter, Int.toNat_of_nonneg hdegreeNonnegative]
  have hrrZ :
      (riemannRochFilterDiffDimension (k := k) (F := F) D E : ℤ) =
        (riemannRochDimension E : ℤ) - riemannRochDimension D := by
    have hrrInt :
        (riemannRochFilterDiffDimension (k := k) (F := F) D E : ℤ) +
            (riemannRochDimension D : ℤ) =
          (riemannRochDimension E : ℤ) := by
      exact_mod_cast hrr
    omega
  rw [hmain, hfilterZ, hrrZ, Divisor.degree_sub]
  simp only [riemannRochDefect]
  ring

/-- Vanishing sandwich rank forces the two diagonal-augmented filtration
pieces to coincide. -/
theorem globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hzero : globalAdeleSandwichRank (k := k) (F := F) D E hDE = 0) :
    globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) D +
        diagonalAdeleSubmodule (k := k) (F := F) := by
  let p := globalAdeleFilter (k := k) (F := F) E
  let sA := globalAdeleFilter (k := k) (F := F) D
  let r := diagonalAdeleSubmodule (k := k) (F := F)
  let l := Submodule.map (diagonalAdele (k := k) (F := F))
    (riemannRochSubmodule E)
  let t := l ⊔ sA
  let qp := Submodule.comap p.subtype sA
  let qt := Submodule.comap p.subtype t
  have hs_le_p : sA ≤ p := globalAdeleFilter_mono hDE
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      (by exact hf)
      (hs_le_p hz)
  have hinter : p ⊓ (sA + r) = t := by
    have hmod : p ⊓ (sA + r) = sA + p ⊓ r := by
      apply le_antisymm
      · rintro x ⟨hxp, hxsr⟩
        rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
        obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
        refine Submodule.mem_sup.mpr ⟨a, has,
          diagonalAdele (k := k) (F := F) f, ?_, rfl⟩
        exact Submodule.mem_inf.mpr
          ⟨(by simpa only [add_sub_cancel_left] using
              Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
      · rintro x hx
        rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
        rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
        exact ⟨Submodule.add_mem p (hs_le_p has) hyp,
          Submodule.add_mem (sA + r) (Submodule.mem_sup_left has)
            (Submodule.mem_sup_right hyr)⟩
    have hpr : p ⊓ r = l := globalAdeleFilter_inf_diagonal E
    calc
      p ⊓ (sA + r) = sA + (p ⊓ r) := hmod
      _ = sA + l := by rw [hpr]
      _ = t := by simp only [t, Submodule.add_eq_sup, sup_comm]
  have hqp_le : qp ≤ qt := Submodule.comap_mono le_sup_right
  letI : AddCommGroup p := Submodule.addCommGroup _
  letI : Module k p := Submodule.module _
  letI : AddCommGroup (p + r) := Submodule.addCommGroup _
  letI : Module k (p + r) := Submodule.module _
  haveI : Module.Finite k (p ⧸ qp) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDE
  haveI : Module.Finite k (p ⧸ qt) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient qp qt hqp_le)
  have hfin_qt : Module.finrank k (p ⧸ qt) = 0 := by
    have hfin_sandwich :
        Module.finrank k
          ((p + r) ⧸ Submodule.comap (p + r).subtype (sA + r)) = 0 :=
      Int.ofNat_eq_zero.mp hzero
    have hinfl :
        Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (sA + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hpsum : p ⊔ (sA + r) = p + r := by
      rw [← Submodule.add_eq_sup]
      apply le_antisymm
      · exact sup_le le_sup_left (add_le_add hs_le_p le_rfl)
      · intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        have hb' : b ∈ sA + r := Submodule.mem_sup_right hb
        exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
          (Submodule.mem_sup_right hb')
    letI : AddCommGroup ↥(p ⊔ (sA + r)) := Submodule.addCommGroup _
    letI : Module k ↥(p ⊔ (sA + r)) := Submodule.module _
    have hsand := (LinearMap.quotientInfEquivSupQuotient p (sA + r)).symm.finrank_eq
    rw [hpsum, hinfl] at hsand
    exact hsand.symm.trans hfin_sandwich
  have hsub : Subsingleton (p ⧸ qt) := Module.finrank_zero_iff.mp hfin_qt
  have htopqt : qt = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  have hp_le_t : p ≤ t := Submodule.comap_subtype_eq_top.mp htopqt
  have hp_eq_t : p = t := le_antisymm hp_le_t htp
  have hp_le_sr : p ≤ sA + r := by
    have h := inf_le_right (a := p) (b := sA + r)
    rw [hinter] at h
    exact hp_eq_t.symm ▸ h
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨a, hap, y, hyr, rfl⟩
    rcases Submodule.mem_sup.mp (hp_le_sr hap) with ⟨b, hbs, w, hwr, hbc⟩
    exact Submodule.mem_sup.mpr
      ⟨b, hbs, w + y, Submodule.add_mem r hwr hyr, by rw [← hbc, add_assoc]⟩
  · exact add_le_add hs_le_p le_rfl

private theorem riemannRochDefect_eq_genus_of_ge
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E)
    (hD : riemannRochDefect (k := k) (F := F) D =
      functionFieldGenus (k := k) (F := F)) :
    riemannRochDefect (k := k) (F := F) E =
      functionFieldGenus (k := k) (F := F) := by
  have hlower := riemannRochDefect_mono
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hupper := riemannRochDefect_le_genus
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F E
  omega

/-- A genus-attaining divisor saturates the intrinsic adele space after the
diagonal function field is adjoined. -/
theorem globalAdeleTopSubmodule_eq_filter_add_diagonal_of_defect_eq_genus
    {D : Divisor (GlobalPlace k F)}
    (hD : riemannRochDefect (k := k) (F := F) D =
      functionFieldGenus (k := k) (F := F)) :
    globalAdeleTopSubmodule (k := k) (F := F) =
      globalAdeleFilter (k := k) (F := F) D +
        diagonalAdeleSubmodule (k := k) (F := F) := by
  apply le_antisymm
  · intro a _
    obtain ⟨Da, ha⟩ := exists_globalAdeleFilter_mem (k := k) (F := F) a
    let E := D ⊔ Da
    have hDE : D ≤ E := le_sup_left
    have hE : riemannRochDefect (k := k) (F := F) E =
        functionFieldGenus (k := k) (F := F) :=
      riemannRochDefect_eq_genus_of_ge
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE hD
    have hrank := globalAdeleSandwichRank_eq_defect_sub
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
    have hzero : globalAdeleSandwichRank (k := k) (F := F) D E hDE = 0 := by
      rw [hrank, hE, hD, sub_self]
    have heq := globalAdeleFilter_add_diagonal_eq_of_sandwichRank_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE hzero
    have hmem : a ∈ globalAdeleFilter (k := k) (F := F) E +
        diagonalAdeleSubmodule (k := k) (F := F) :=
      Submodule.mem_sup_left (globalAdeleFilter_mono le_sup_right ha)
    rw [heq] at hmem
    exact hmem
  · exact le_top

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
