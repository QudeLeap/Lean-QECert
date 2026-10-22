import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorSemilocalMultiplier
import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorTraceResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A semilocal logarithmic residue at one direct factor

For one chosen upper factor `P`, a semilocal principal multiplier has ideal
`P * J`, with `J` coprime to the whole extended base prime.  Its multiplicity
at `P` is therefore exactly one.  Multiplying its logarithmic differential by
an integral coefficient gives an actual simple-pole differential whose traced
local residue is the established factor-residue trace.

This is a one-place direct-chart calculation.  It does not compare with a
Smith matrix, sum over places, or assert a global residue, duality, genus, or
Riemann--Roch theorem.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue

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

open DirectIntegralDifferentialResidue DirectFactorTraceResidue

/-- A semilocal multiplier with principal ideal `P * J`, where the complement
is coprime to the extended base prime, has normalized order one at `P`. -/
theorem directFactorPlace_order_semilocalMultiplier_eq_one
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    GlobalPlace.order
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (B k F) F t) = 1 := by
  have hP_ne : (P : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal P
  have hP_prime : Prime (P : Ideal (B k F)) :=
    Ideal.prime_of_isPrime hP_ne (Ideal.Factors.isPrime p.asIdeal P)
  have hmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤
      (P : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  have hPJ : IsCoprime (P : Ideal (B k F)) J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hmap J
  have hP_not_dvd_J : ¬(P : Ideal (B k F)) ∣ J := by
    rw [Ideal.dvd_iff_le]
    intro hJ_le
    have hP_top : (P : Ideal (B k F)) = ⊤ := by
      calc
        (P : Ideal (B k F)) = (P : Ideal (B k F)) ⊔ J :=
          (sup_eq_left.mpr hJ_le).symm
        _ = ⊤ := hPJ.sup_eq
    exact (Ideal.Factors.isPrime p.asIdeal P).ne_top hP_top
  have hspan_ne : Ideal.span ({t} : Set (B k F)) ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt ht
  have hprod_ne : (P : Ideal (B k F)) * J ≠ 0 := by
    rw [← hspan]
    exact hspan_ne
  have hfinite : FiniteMultiplicity (P : Ideal (B k F))
      ((P : Ideal (B k F)) * J) :=
    FiniteMultiplicity.of_prime_left hP_prime hprod_ne
  have hmultiplicity :
      multiplicity (P : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) = 1 := by
    calc
      multiplicity (P : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) =
          multiplicity (P : Ideal (B k F))
            ((P : Ideal (B k F)) * J) := by rw [hspan]
      _ = multiplicity (P : Ideal (B k F)) (P : Ideal (B k F)) +
          multiplicity (P : Ideal (B k F)) J :=
        multiplicity_mul hP_prime hfinite
      _ = 1 := by
        rw [multiplicity_self, multiplicity_eq_zero.mpr hP_not_dvd_J, add_zero]
  rw [AffinePlace.globalPlace_order_of_integral_eq_multiplicity k F
    (directFactorPlace k F p P) ht, directFactorPlace_asIdeal]
  exact_mod_cast hmultiplicity

/-- The actual simple-pole differential obtained from a semilocal multiplier
and an integral coefficient. -/
noncomputable def directFactorSemilocalLogarithmicDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (t : B k F) (ht : t ≠ 0) (b : B k F) :
    Differential.simplePoleDifferentialLattice
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)) :=
  directIntegralToValuationRing k F p P b •
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := F)
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
      (algebraMap (B k F) F t)
      ((map_ne_zero_iff _ (IsFractionRing.injective (B k F) F)).mpr ht)

/-- For a supplied semilocal principal factorization, the base-field trace of
the normalized local residue is exactly the chosen factor-residue trace. -/
theorem
    directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0) (b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    directFactorPlaceTrace k F p P
        (Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (directFactorSemilocalLogarithmicDifferentialAtSimplePole
            k F p P t ht b)) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  unfold directFactorSemilocalLogarithmicDifferentialAtSimplePole
  rw [Differential.simplePoleResidue_smul,
    Differential.simplePoleResidue_logarithmicDifferential,
    directFactorPlace_order_semilocalMultiplier_eq_one
      k F p P J hcop t ht hspan,
    Int.cast_one, mul_one,
    directFactorPlaceTrace_residue_integral]

/-- There is an actual semilocal multiplier of order one whose logarithmic
simple-pole residue realizes the chosen factor-residue trace. -/
theorem
    exists_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential_eq_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      GlobalPlace.order
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (algebraMap (B k F) F t) = 1 ∧
        directFactorPlaceTrace k F p P
            (Differential.simplePoleResidue (k := k) (F := F)
              (AffinePlace.globalPlace k F (directFactorPlace k F p P))
              (directFactorSemilocalLogarithmicDifferentialAtSimplePole
                k F p P t ht b)) =
          Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  obtain ⟨t, ht, J, hspan, hcop⟩ :=
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  exact ⟨t, ht,
    directFactorPlace_order_semilocalMultiplier_eq_one
      k F p P J hcop t ht hspan,
    directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
      k F p P J hcop t ht b hspan⟩

end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
