import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorSemilocalCokernelTrace
import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorSemilocalLogarithmicResidue
import QEC.Coding.AlgebraicGeometry.Residues.Direct.SmithDifferentialTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A direct Smith trace--residue comparison at one upper factor

Both the localization residue field of a polynomial prime and the normalized
rational-place residue field are canonically obtained from the same quotient
`k[X] / p`.  After making that transport explicit, the Smith residue of a
semilocal principal multiplier agrees with the traced normalized residue at
the selected upper factor.  The same Smith differential is the actual
differential trace of `b * dt/t`.

This is a one-factor local trace--residue comparison.  It does not sum over
places or assert a global residue, duality, genus, or Riemann--Roch theorem.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue

open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

local instance : Module.Finite (R k) (B k F) :=
  AffinePlace.finite_ringOfIntegers k F

open DirectIntegralDifferentialResidue DirectFactorTraceResidue
open DirectFactorSemilocalLogarithmicResidue

/-- The residue field of the height-one localization and the residue field of
the corresponding normalized rational place are canonically equivalent. -/
noncomputable def directBaseResidueRationalAdicEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    p.asIdeal.ResidueField ≃+* (GlobalPlace.rationalAdic p).residueField :=
  (Ideal.Factors.quotientResidueEquiv p.asIdeal).symm.trans
    (GlobalPlace.rationalAdicIdealResidueEquiv p)

/-- The canonical base-residue transport agrees on the common quotient
representative. -/
@[simp]
theorem directBaseResidueRationalAdicEquiv_quotientResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (x : R k ⧸ p.asIdeal) :
    directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.quotientResidueEquiv p.asIdeal x) =
      GlobalPlace.rationalAdicIdealResidueEquiv p x := by
  rw [directBaseResidueRationalAdicEquiv, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply]

private theorem lmul_comp_lmul (t b : B k F) :
    (Algebra.lmul (R k) (B k F) t).comp
        (Algebra.lmul (R k) (B k F) b) =
      (Algebra.lmul (R k) (B k F) b).comp
        (Algebra.lmul (R k) (B k F) t) := by
  apply LinearMap.ext
  intro x
  change t * (b * x) = b * (t * x)
  ring

/-- For supplied Smith data of a semilocal multiplier, the rational-place
Smith residue is the canonical transport of the traced normalized residue at
the selected upper factor. -/
theorem simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0) (b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J)
    {n : ℕ}
    (source target : Module.Basis (Fin n) (R k) (B k F))
    (a : Fin n → R k) (ha : ∀ i, a i ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a) :
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      directBaseResidueRationalAdicEquiv k p
        (directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directFactorSemilocalLogarithmicDifferentialAtSimplePole
              k F p P t ht b))) := by
  let depth : ℕ :=
    (∑ i, multiplicity p.asIdeal
      (Ideal.span ({a i} : Set (R k)))).succ
  have hdepth : ∀ i, multiplicity p.asIdeal
      (Ideal.span ({a i} : Set (R k))) ≤ depth := by
    intro i
    apply le_trans ?_ (Nat.le_succ _)
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le
        (multiplicity p.asIdeal (Ideal.span ({a j} : Set (R k)))))
      (Finset.mem_univ i)
  have hcomm := lmul_comp_lmul k F t b
  have hcokernel :
      cokernelEndomorphism
          (Algebra.lmul (R k) (B k F) t)
          (Algebra.lmul (R k) (B k F) b) hcomm =
        principalCokernelMul (R := R k) t b := by
    rfl
  have hrational :=
    Differential.simplePoleResidue_rationalAdicSmithLogarithmicDifferential
      p source target a ha
        (Algebra.lmul (R k) (B k F) t)
        (Algebra.lmul (R k) (B k F) b)
        hdiag hcomm depth hdepth
  have hprimary :=
    DirectFactorSemilocalCokernelTrace.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_factorResidueTrace
      k F p P J hcop t b hspan depth (Nat.succ_pos _)
  have hupper :=
    directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
      k F p P J hcop t ht b hspan
  calc
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha (Algebra.lmul (R k) (B k F) b)) =
      GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism
            (Algebra.lmul (R k) (B k F) t)
            (Algebra.lmul (R k) (B k F) b) hcomm) depth) := hrational
    _ = directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.quotientResidueEquiv p.asIdeal
          (primaryTorsionTrace p.asIdeal
            (principalCokernelMul (R := R k) t b) depth)) := by
      rw [hcokernel,
        directBaseResidueRationalAdicEquiv_quotientResidueEquiv]
    _ = directBaseResidueRationalAdicEquiv k p
        (Ideal.Factors.factorResidueTrace p.asIdeal P b) := by
      rw [hprimary]
    _ = directBaseResidueRationalAdicEquiv k p
        (directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directFactorSemilocalLogarithmicDifferentialAtSimplePole
              k F p P t ht b))) := by
      rw [hupper]

/-- Smith bases and a semilocal multiplier can be chosen so that the same
actual Smith differential is the differential trace of `b * dt/t`, while its
rational residue is the transported traced residue at the selected factor. -/
theorem exists_directFactorSmith_trace_residue_compatibility
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      ∃ source target : Module.Basis
        (Fin (Module.finrank (R k) (B k F))) (R k) (B k F),
      ∃ a : Fin (Module.finrank (R k) (B k F)) → R k,
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target
            (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a ∧
        GlobalPlace.order
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1 ∧
        ((Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
            source target a ha (Algebra.lmul (R k) (B k F) b) :
              Differential.simplePoleDifferentialLattice
                (GlobalPlace.rationalAdic p)) :
            Differential k (RatFunc k)) =
          FunctionFieldDifferential.functionFieldDifferentialTrace
            (k := k) (F := F)
            ((algebraMap (B k F) F b) •
              Differential.logarithmicDifferential (k := k) (F := F)
                (algebraMap (B k F) F t)) ∧
        Differential.simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole
              p source target a ha (Algebra.lmul (R k) (B k F) b)) =
          directBaseResidueRationalAdicEquiv k p
            (directFactorPlaceTrace k F p P
              (Differential.simplePoleResidue (k := k) (F := F)
                (AffinePlace.globalPlace k F (directFactorPlace k F p P))
                (directFactorSemilocalLogarithmicDifferentialAtSimplePole
                  k F p P t ht b))) := by
  obtain ⟨t, ht, J, hspan, hcop⟩ :=
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  let basis : Module.Basis
      (Fin (Module.finrank (R k) (B k F))) (R k) (B k F) :=
    Module.finBasis (R k) (B k F)
  have hf : Function.Injective (Algebra.lmul (R k) (B k F) t) := by
    intro x y hxy
    change t * x = t * y at hxy
    exact mul_left_cancel₀ ht hxy
  have hcomm := lmul_comp_lmul k F t b
  obtain ⟨source, target, a, ha, hdiag, _hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute basis
      (Algebra.lmul (R k) (B k F) t)
      (Algebra.lmul (R k) (B k F) b) hf hcomm
  refine ⟨t, ht, source, target, a, ha, hdiag, ?_, ?_, ?_⟩
  · exact directFactorPlace_order_semilocalMultiplier_eq_one
      k F p P J hcop t ht hspan
  · exact
      Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
        (k := k) (F := F) p source target a ha t b ht hdiag
  · exact simplePoleResidue_rationalAdicSmith_eq_directFactorTrace
      k F p P J hcop t ht b hspan source target a ha hdiag

end QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue
