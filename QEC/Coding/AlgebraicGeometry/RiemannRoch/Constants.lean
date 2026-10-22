import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import QEC.Coding.AlgebraicGeometry.Places.FullConstantField
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Dimension

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Constants in the zero Riemann--Roch space

A function regular at every actual normalized global place is algebraic over
the supplied constant field.  Under the standard full-constant-field
hypothesis this identifies the zero-divisor Riemann--Roch space with `k` and
proves `ℓ(0) = 1`.

The two-chart integrality/minimal-polynomial proof is adapted from Guanghao
Li's Apache-2.0 formalization `vaca22/riemann-roch-function-fields`.  No
genus, specialty, duality, or Riemann--Roch formula is assumed here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Polynomial
open scoped Polynomial RatFunc WithZero nonZeroDivisors

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance : IsScalarTower k k[X] F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance : IsScalarTower k k⟮X⟯ F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

private local instance : DecidableEq k⟮X⟯ := Classical.decEq _

/-- The valuation ring of `k(X)` at rational infinity. -/
private abbrev inftyValuationSubring : Type _ :=
  (RatFunc.inftyValuation k).valuationSubring

private instance inftyValuationSubring_isDedekindDomain :
    IsDedekindDomain (inftyValuationSubring k) := by
  infer_instance

/-- The integral closure in `F` of the rational infinity valuation ring. -/
private abbrev infiniteIntegers : Type _ :=
  integralClosure (inftyValuationSubring k) F

private instance infiniteIntegers_isTorsionFree :
    Module.IsTorsionFree (inftyValuationSubring k) (infiniteIntegers k F) :=
  IsIntegralClosure.isTorsionFree (inftyValuationSubring k) F

private instance infiniteIntegers_isFractionRing :
    IsFractionRing (infiniteIntegers k F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (inftyValuationSubring k) k⟮X⟯ F (infiniteIntegers k F)

private instance infiniteIntegers_isDedekindDomain :
    IsDedekindDomain (infiniteIntegers k F) :=
  integralClosure.isDedekindDomain (inftyValuationSubring k) k⟮X⟯ F

namespace GlobalPlace

/-- A function integral at every normalized global place is algebraic over
the constant field.  The proof uses the direct integral closure and the
integral closure of the rational infinity valuation ring; it does not assume
that a globally regular function is constant. -/
theorem isAlgebraic_of_valuation_le_one (f : F)
    (hf : ∀ P : GlobalPlace k F, P.valuation f ≤ 1) : IsAlgebraic k f := by
  by_cases hf0 : f = 0
  · subst f
    exact isAlgebraic_zero
  have hfin := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := _root_.FunctionField.ringOfIntegers k F) F f fun P =>
      hf (AffinePlace.globalPlace k F P)
  have hinf := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := infiniteIntegers k F) F f fun P =>
      hf ({ valuation := P.valuation F
            normalized := P.valuation_surjective F } : GlobalPlace k F)
  obtain ⟨a, ha⟩ := hfin
  obtain ⟨b, hb⟩ := hinf
  let p : k[X][X] := minpoly k[X] a
  let q : (inftyValuationSubring k)[X] := minpoly (inftyValuationSubring k) b
  have hpmap : minpoly k⟮X⟯ f = p.map (algebraMap k[X] k⟮X⟯) := by
    rw [← ha]
    exact minpoly.isIntegrallyClosed_eq_field_fractions k⟮X⟯ F
      (Algebra.IsIntegral.isIntegral a)
  have hqmap : minpoly k⟮X⟯ f =
      q.map (algebraMap (inftyValuationSubring k) k⟮X⟯) := by
    rw [← hb]
    exact minpoly.isIntegrallyClosed_eq_field_fractions k⟮X⟯ F
      (Algebra.IsIntegral.isIntegral b)
  have hpcoeff : ∀ i, p.coeff i ∈ Set.range (Polynomial.C : k →+* k[X]) := by
    intro i
    let c := p.coeff i
    have hcval : RatFunc.inftyValuation k (algebraMap k[X] k⟮X⟯ c) ≤ 1 := by
      have hc : algebraMap k[X] k⟮X⟯ c =
          algebraMap (inftyValuationSubring k) k⟮X⟯ (q.coeff i) := by
        have hc' := congrArg (fun r : k⟮X⟯[X] => r.coeff i) (hpmap.symm.trans hqmap)
        simpa only [p, q, c, Polynomial.coeff_map] using hc'
      rw [hc]
      exact (q.coeff i).property
    by_cases hc0 : c = 0
    · refine ⟨0, ?_⟩
      change Polynomial.C 0 = c
      simp only [map_zero, hc0]
    have hdegree : c.natDegree = 0 := by
      rw [RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation.polynomial (F := k) hc0,
        ← WithZero.exp_zero, WithZero.exp_le_exp] at hcval
      omega
    exact ⟨c.coeff 0, (Polynomial.eq_C_of_natDegree_eq_zero hdegree).symm⟩
  have hprange : p ∈ (Polynomial.mapRingHom (Polynomial.C : k →+* k[X])).range := by
    rw [Polynomial.mem_map_range]
    exact hpcoeff
  obtain ⟨P, hP⟩ := hprange
  have hP0 : P ≠ 0 := by
    intro hP0
    rw [hP0, map_zero] at hP
    have hpmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
    exact hpmonic.ne_zero hP.symm
  refine ⟨P, hP0, ?_⟩
  have hroot : Polynomial.aeval a p = 0 := minpoly.aeval _ _
  rw [← hP] at hroot
  change Polynomial.aeval a (P.map (Polynomial.C : k →+* k[X])) = 0 at hroot
  calc
    Polynomial.aeval f P =
        Polynomial.aeval f (P.map (Polynomial.C : k →+* k[X])) := by
      symm
      exact Polynomial.aeval_map_algebraMap k[X] f P
    _ = algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (Polynomial.aeval a (P.map (Polynomial.C : k →+* k[X]))) := by
      rw [← ha]
      symm
      simp
    _ = 0 := by rw [hroot, map_zero]

/-- Under full constants, scalar extension identifies `k` with the actual
zero-divisor Riemann--Roch submodule. -/
noncomputable def constantsLinearEquivRiemannRochZero [IsFullConstantField k F] :
    k ≃ₗ[k] riemannRochSubmodule (0 : Divisor (GlobalPlace k F)) := by
  let inclusion : k →ₗ[k] riemannRochSubmodule (0 : Divisor (GlobalPlace k F)) :=
    { toFun := fun c => ⟨algebraMap k F c, by
        intro P
        simp only [Finsupp.zero_apply, WithZero.exp_zero]
        exact FiniteField.valuation_algebraMap_le_one P.valuation c⟩
      map_add' := fun x y => Subtype.ext (map_add (algebraMap k F) x y)
      map_smul' := fun c x => Subtype.ext (by simp [Algebra.smul_def]) }
  refine LinearEquiv.ofBijective inclusion ⟨?_, ?_⟩
  · intro c d hcd
    have hcd' : (inclusion c : F) = (inclusion d : F) :=
      congrArg Subtype.val hcd
    change algebraMap k F c = algebraMap k F d at hcd'
    apply (algebraMap k F).injective
    exact hcd'
  · intro f
    have hfalg : IsAlgebraic k (f : F) := by
      apply isAlgebraic_of_valuation_le_one k F (f : F)
      intro P
      have hregular := f.property P
      simp only [Finsupp.zero_apply, WithZero.exp_zero] at hregular
      exact hregular
    obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem
      (k := k) (F := F) (f : F) hfalg
    refine ⟨c, Subtype.ext ?_⟩
    exact hc.symm

/-- The zero-divisor Riemann--Roch dimension is one when `k` is the full
constant field. -/
theorem riemannRochDimension_zero [IsFullConstantField k F]
    [FiniteDimensional k (riemannRochSubmodule
      (0 : Divisor (GlobalPlace k F)))] :
    riemannRochDimension (0 : Divisor (GlobalPlace k F)) = 1 := by
  rw [riemannRochDimension,
    ← (constantsLinearEquivRiemannRochZero k F).finrank_eq]
  exact Module.finrank_self k

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
