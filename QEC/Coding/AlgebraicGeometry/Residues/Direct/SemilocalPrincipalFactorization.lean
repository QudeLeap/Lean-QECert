import QEC.Coding.AlgebraicGeometry.Residues.Direct.SemilocalUniformizer

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A principal factorization for a simultaneous direct uniformizer

Multiplying the semilocal multiplier attached to every actual factor over a
fixed direct polynomial prime gives one integral element of normalized order
one at every factor.  Its principal ideal is the product of those distinct
factor ideals times a complement coprime to the full extended base prime.

This is a finite-fibre ideal factorization only.  It does not identify a
cokernel trace with a sum of residues, compare arbitrary simple-pole
differentials, treat the inverse chart, or prove a global residue theorem,
duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization

open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid

open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
open DirectSemilocalUniformizer

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

/-- There is one simultaneous direct uniformizer whose principal ideal is the
product of all actual upper factors times a complement coprime to the full
extended base prime. -/
theorem exists_directSemilocalUniformizerFactorization
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    ∃ t : B k F, t ≠ 0 ∧ ∃ J : Ideal (B k F),
      Ideal.span ({t} : Set (B k F)) =
          (∏ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
              (P : Ideal (B k F))) * J ∧
        IsCoprime
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J ∧
        ∀ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          GlobalPlace.order
              (AffinePlace.globalPlace k F (directFactorPlace k F p P))
              (algebraMap (B k F) F t) = 1 := by
  classical
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  let S := (factors M).toFinset
  choose t ht J hspan hcop using fun P : S =>
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  let T : B k F := ∏ P : S, t P
  let K : Ideal (B k F) := ∏ P : S, (P : Ideal (B k F))
  let Jall : Ideal (B k F) := ∏ P : S, J P
  have hT_ne : T ≠ 0 := by
    dsimp only [T]
    exact Finset.prod_ne_zero_iff.mpr fun P _ => ht P
  have hspanT : Ideal.span ({T} : Set (B k F)) = K * Jall := by
    calc
      Ideal.span ({T} : Set (B k F)) =
          ∏ P : S, Ideal.span ({t P} : Set (B k F)) := by
        simpa only [T] using
          (Ideal.prod_span_singleton (Finset.univ : Finset S) t).symm
      _ = ∏ P : S, ((P : Ideal (B k F)) * J P) := by
        apply Finset.prod_congr rfl
        intro P _
        exact hspan P
      _ = K * Jall := by
        simp only [K, Jall, Finset.prod_mul_distrib]
  have hcopJall : IsCoprime M Jall := by
    apply IsCoprime.prod_right
    intro P _
    exact hcop P
  refine ⟨T, hT_ne, Jall, ?_, ?_, ?_⟩
  · simpa only [M, S, K] using hspanT
  · simpa only [M] using hcopJall
  · intro Q
    let Qplace : GlobalPlace k F :=
      AffinePlace.globalPlace k F (directFactorPlace k F p Q)
    have htF_ne (P : S) : algebraMap (B k F) F (t P) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (B k F) F)).mpr (ht P)
    have hcomponent (P : S) :
        Qplace.order (algebraMap (B k F) F (t P)) =
          if P = Q then 1 else 0 := by
      by_cases hPQ : P = Q
      · subst P
        rw [if_pos rfl]
        exact directFactorPlace_order_semilocalMultiplier_eq_one
          k F p Q (J Q) (hcop Q) (t Q) (ht Q) (hspan Q)
      · rw [if_neg hPQ]
        exact directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
          k F p P Q (Ne.symm hPQ) (J P) (hcop P) (t P) (ht P) (hspan P)
    have horderProd (s : Finset S) :
        Qplace.order (∏ P ∈ s, algebraMap (B k F) F (t P)) =
          ∑ P ∈ s, Qplace.order (algebraMap (B k F) F (t P)) := by
      induction s using Finset.induction_on with
      | empty =>
          simp [GlobalPlace.order]
      | @insert P s hPs ih =>
          have hs_ne :
              (∏ Q ∈ s, algebraMap (B k F) F (t Q)) ≠ 0 := by
            exact Finset.prod_ne_zero_iff.mpr fun Q _ => htF_ne Q
          rw [Finset.prod_insert hPs, Finset.sum_insert hPs,
            Qplace.order_mul (htF_ne P) hs_ne, ih]
    change Qplace.order (algebraMap (B k F) F T) = 1
    rw [show algebraMap (B k F) F T =
        ∏ P : S, algebraMap (B k F) F (t P) by
          simp only [T, map_prod]]
    rw [horderProd]
    calc
      (∑ P : S, Qplace.order (algebraMap (B k F) F (t P))) =
          ∑ P : S, if P = Q then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro P _
        exact hcomponent P
      _ = 1 := by simp

end QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization
