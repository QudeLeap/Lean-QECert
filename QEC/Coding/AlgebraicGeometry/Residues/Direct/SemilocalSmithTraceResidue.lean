import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorSmithTraceResidue
import QEC.Coding.AlgebraicGeometry.Residues.Direct.SemilocalCokernelTraceSum
import QEC.Coding.AlgebraicGeometry.Residues.Direct.SmithDifferentialTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A Smith trace--residue sum over one direct fibre

For a simultaneous principal factorization over one direct polynomial prime,
the rational-place residue of its Smith logarithmic differential is the
canonical transport of the sum of all upper factor-residue traces.  Smith
bases can be chosen so that this same rational differential is the actual
differential trace of an integral coefficient times the logarithmic
differential of the simultaneous order-one element.

This is a direct finite-fibre comparison.  It does not yet treat an arbitrary
simple-pole differential, the inverse chart, a global residue theorem,
duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue

open scoped Polynomial RatFunc nonZeroDivisors BigOperators
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

open DirectFactorSmithTraceResidue

private theorem lmul_comp_lmul (t b : B k F) :
    (Algebra.lmul (R k) (B k F) t).comp
        (Algebra.lmul (R k) (B k F) b) =
      (Algebra.lmul (R k) (B k F) b).comp
        (Algebra.lmul (R k) (B k F) t) := by
  apply LinearMap.ext
  intro x
  change t * (b * x) = b * (t * x)
  ring

/-- For supplied Smith data of a simultaneous principal factorization, the
rational Smith residue is the canonical transport of the complete sum of
upper factor-residue traces. -/
theorem simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (∏ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          (P : Ideal (B k F))) * J)
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
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b) := by
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
    DirectSemilocalCokernelTraceSum.quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
      k F p J hcop t b hspan depth (Nat.succ_pos _)
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
    _ = _ := by rw [hprimary]

/-- Smith data can be chosen for one simultaneous order-one integral element
so that its Smith differential is the actual differential trace and its
rational residue is the transported full upper factor-residue sum. -/
theorem exists_directSemilocalSmith_trace_residue_sum_compatibility
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      ∃ source target : Module.Basis
        (Fin (Module.finrank (R k) (B k F))) (R k) (B k F),
      ∃ a : Fin (Module.finrank (R k) (B k F)) → R k,
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target
            (Algebra.lmul (R k) (B k F) t) = Matrix.diagonal a ∧
        (∀ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          GlobalPlace.order
              (AffinePlace.globalPlace k F
                (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
              (algebraMap (B k F) F t) = 1) ∧
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
            (∑ P : (factors
                (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
              Ideal.Factors.factorResidueTrace p.asIdeal P b) := by
  obtain ⟨t, ht, J, hspan, hcop, horder⟩ :=
    DirectSemilocalPrincipalFactorization.exists_directSemilocalUniformizerFactorization
      k F p
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
  refine ⟨t, ht, source, target, a, ha, hdiag, horder, ?_, ?_⟩
  · exact
      Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
        (k := k) (F := F) p source target a ha t b ht hdiag
  · exact simplePoleResidue_rationalAdicSmith_eq_sum_factorResidueTraces
      k F p J hcop t b hspan source target a ha hdiag

end QEC.Coding.AlgebraicGeometry.DirectSemilocalSmithTraceResidue
