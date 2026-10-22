import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorSemilocalLogarithmicResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A simultaneous order-one element over a direct prime

The semilocal multiplier attached to one upper factor has order one there and
order zero at every other factor over the same direct base prime.  Multiplying
one such element for every factor produces one actual integral element of
order one at every place in the finite fibre.

This is a finite-fibre ideal calculation.  It does not clear differential
denominators, compare residues with a field trace, or prove a global residue
theorem, duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer

open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid

open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue

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

/-- A multiplier isolating `P` is a unit at every distinct factor `Q` over
the same direct prime, so its normalized order at `Q` is zero. -/
theorem directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hQP : Q ≠ P)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    GlobalPlace.order
        (AffinePlace.globalPlace k F (directFactorPlace k F p Q))
        (algebraMap (B k F) F t) = 0 := by
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  have hP_ne : (P : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal P
  have hQ_ne : (Q : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal Q
  have hQ_prime : Prime (Q : Ideal (B k F)) :=
    Ideal.prime_of_isPrime hQ_ne (Ideal.Factors.isPrime p.asIdeal Q)
  have hP_max : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal hP_ne
  have hQ_ne_top : (Q : Ideal (B k F)) ≠ ⊤ :=
    (Ideal.Factors.isPrime p.asIdeal Q).ne_top
  have hQ_not_dvd_P : ¬(Q : Ideal (B k F)) ∣ (P : Ideal (B k F)) := by
    rw [Ideal.dvd_iff_le]
    intro hP_le_Q
    have hPQ : (P : Ideal (B k F)) = (Q : Ideal (B k F)) :=
      hP_max.eq_of_le hQ_ne_top hP_le_Q
    apply hQP
    exact Subtype.ext hPQ.symm
  have hM_le_Q : M ≤ (Q : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp Q.2))
  have hQJ : IsCoprime (Q : Ideal (B k F)) J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hM_le_Q J
  have hQ_not_dvd_J : ¬(Q : Ideal (B k F)) ∣ J := by
    rw [Ideal.dvd_iff_le]
    intro hJ_le_Q
    have hQ_top : (Q : Ideal (B k F)) = ⊤ := by
      calc
        (Q : Ideal (B k F)) = (Q : Ideal (B k F)) ⊔ J :=
          (sup_eq_left.mpr hJ_le_Q).symm
        _ = ⊤ := hQJ.sup_eq
    exact hQ_ne_top hQ_top
  have hspan_ne : Ideal.span ({t} : Set (B k F)) ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt ht
  have hprod_ne : (P : Ideal (B k F)) * J ≠ 0 := by
    rw [← hspan]
    exact hspan_ne
  have hfinite : FiniteMultiplicity (Q : Ideal (B k F))
      ((P : Ideal (B k F)) * J) :=
    FiniteMultiplicity.of_prime_left hQ_prime hprod_ne
  have hmultiplicity :
      multiplicity (Q : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) = 0 := by
    calc
      multiplicity (Q : Ideal (B k F))
          (Ideal.span ({t} : Set (B k F))) =
          multiplicity (Q : Ideal (B k F))
            ((P : Ideal (B k F)) * J) := by rw [hspan]
      _ = multiplicity (Q : Ideal (B k F)) (P : Ideal (B k F)) +
          multiplicity (Q : Ideal (B k F)) J :=
        multiplicity_mul hQ_prime hfinite
      _ = 0 := by
        rw [multiplicity_eq_zero.mpr hQ_not_dvd_P,
          multiplicity_eq_zero.mpr hQ_not_dvd_J, zero_add]
  rw [AffinePlace.globalPlace_order_of_integral_eq_multiplicity k F
    (directFactorPlace k F p Q) ht, directFactorPlace_asIdeal]
  exact_mod_cast hmultiplicity

/-- There is one nonzero direct integral element having normalized order one
at every actual factor over a fixed direct base prime. -/
theorem exists_directSemilocalUniformizer
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    ∃ t : B k F, t ≠ 0 ∧
      ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.order
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1 := by
  classical
  let S := (factors
    (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset
  choose t ht J hspan hcop using fun P : S =>
    DirectFactorSemilocalMultiplier.exists_directFactorSemilocalMultiplier
      k F p P
  let T : B k F := ∏ P : S, t P
  have hT_ne : T ≠ 0 := by
    dsimp only [T]
    exact Finset.prod_ne_zero_iff.mpr fun P _ => ht P
  refine ⟨T, hT_ne, ?_⟩
  intro Q
  let Qplace : GlobalPlace k F :=
    AffinePlace.globalPlace k F (directFactorPlace k F p Q)
  have htF_ne (P : S) : algebraMap (B k F) F (t P) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (B k F) F)).mpr (ht P)
  have hcomponent (P : S) :
      Qplace.order (algebraMap (B k F) F (t P)) = if P = Q then 1 else 0 := by
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
        have hs_ne : (∏ Q ∈ s, algebraMap (B k F) F (t Q)) ≠ 0 := by
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

end QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
