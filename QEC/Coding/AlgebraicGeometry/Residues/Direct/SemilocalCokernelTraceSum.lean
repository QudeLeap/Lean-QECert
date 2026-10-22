import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorPrimaryTrace
import QEC.Coding.AlgebraicGeometry.Residues.Direct.SemilocalPrincipalFactorization
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.CoprimeQuotientTrace
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.CRTTrace
import QEC.Coding.AlgebraicGeometry.Trace.PrincipalCokernelTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A grouped cokernel trace over one direct fibre

Chinese remaindering the squarefree product of every actual factor above one
direct polynomial prime turns its positive-depth primary multiplication trace
into the sum of the ordinary quotient traces on those factors.  A complement
coprime to the extended base prime contributes zero.  Applying this to the
simultaneous principal factorization gives one principal cokernel whose
canonical base-residue trace is the sum of all factor residue traces.

The proof is symbolic over the finite factor set.  It does not enumerate a
quotient or residue field, compare arbitrary simple-pole differentials, treat
the inverse chart, or prove a global residue theorem, duality, genus, or
Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum

open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid

attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

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

private theorem directFactors_isCoprime_of_ne
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hPQ : P ≠ Q) :
    IsCoprime (P : Ideal (B k F)) (Q : Ideal (B k F)) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.IsMaximal.coprime_of_ne
    ((Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P))
    ((Ideal.Factors.isPrime p.asIdeal Q).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal Q))
  intro hideal
  apply hPQ
  exact Subtype.ext hideal

private theorem primaryTorsionTrace_product_directFactors_eq_sum
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth)
    (s : Finset
      ((factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k)
          (B k F ⧸ (∏ P ∈ s, (P : Ideal (B k F))))
          (Ideal.Quotient.mk (∏ P ∈ s, (P : Ideal (B k F))) b)) depth =
      ∑ P ∈ s,
        Algebra.trace (R k ⧸ p.asIdeal)
          (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      apply primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
        p.asIdeal (1 : Ideal (B k F))
      exact Ideal.isCoprime_iff_sup_eq.mpr (by simp)
  | @insert P s hPs ih =>
      have hPprod : IsCoprime (P : Ideal (B k F))
          (∏ Q ∈ s, (Q : Ideal (B k F))) := by
        apply IsCoprime.prod_right
        intro Q hQs
        apply directFactors_isCoprime_of_ne k F p P Q
        intro hPQ
        apply hPs
        simpa only [hPQ] using hQs
      rw [Finset.prod_insert hPs, Finset.sum_insert hPs,
        primaryTorsionTrace_quotientMul_eq_add p.asIdeal
          (P : Ideal (B k F))
          (∏ Q ∈ s, (Q : Ideal (B k F))) hPprod b depth,
        DirectFactorPrimaryTrace.primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
          k F p P b depth hdepth,
        ih]

/-- For a simultaneous principal factorization, canonical base-residue
transport turns the principal-cokernel primary trace into the sum of the
actual factor residue traces over the direct fibre. -/
theorem
    quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (∏ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          (P : Ideal (B k F))) * J)
    (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth) =
      ∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  classical
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  let S := (factors M).toFinset
  let K : Ideal (B k F) := ∏ P : S, (P : Ideal (B k F))
  have hKJ : IsCoprime K J := by
    apply IsCoprime.prod_left
    intro P _
    have hM_le_P : M ≤ (P : Ideal (B k F)) := by
      exact Ideal.le_of_dvd
        (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hM_le_P J
  have hJzero : primaryTorsionTrace p.asIdeal
      (Algebra.lmul (R k) (B k F ⧸ J) (Ideal.Quotient.mk J b)) depth = 0 :=
    primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
      p.asIdeal J hcop
        (Algebra.lmul (R k) (B k F ⧸ J) (Ideal.Quotient.mk J b)) depth
  have hKsum : primaryTorsionTrace p.asIdeal
      (Algebra.lmul (R k) (B k F ⧸ K) (Ideal.Quotient.mk K b)) depth =
        ∑ P : S,
          Algebra.trace (R k ⧸ p.asIdeal)
            (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
    simpa only [K] using
      primaryTorsionTrace_product_directFactors_eq_sum
        k F p b depth hdepth (Finset.univ : Finset S)
  have hprimary : primaryTorsionTrace p.asIdeal
      (principalCokernelMul (R := R k) t b) depth =
        ∑ P : S,
          Algebra.trace (R k ⧸ p.asIdeal)
            (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
    calc
      primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth =
        primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ (K * J))
            (Ideal.Quotient.mk (K * J) b)) depth :=
        primaryTorsionTrace_cokernel_lmul_eq_idealQuotientMul_of_eq
          p.asIdeal t b (K * J) (by simpa only [M, S, K] using hspan) depth
      _ = primaryTorsionTrace p.asIdeal
            (Algebra.lmul (R k) (B k F ⧸ K) (Ideal.Quotient.mk K b)) depth +
          primaryTorsionTrace p.asIdeal
            (Algebra.lmul (R k) (B k F ⧸ J) (Ideal.Quotient.mk J b)) depth :=
        primaryTorsionTrace_quotientMul_eq_add
          p.asIdeal K J hKJ b depth
      _ = _ := by rw [hJzero, add_zero, hKsum]
  rw [hprimary, map_sum]
  apply Finset.sum_congr rfl
  intro P _
  exact Ideal.Factors.quotientTrace_to_factorResidueTrace p.asIdeal P b

/-- One simultaneous direct uniformizer realizes the grouped factor-residue
sum as a principal-cokernel primary trace and has order one at every upper
place. -/
theorem exists_directSemilocalUniformizer_primaryTrace_eq_sum_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    ∃ t : B k F, t ≠ 0 ∧
      (∀ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        GlobalPlace.order
            (AffinePlace.globalPlace k F
              (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
            (algebraMap (B k F) F t) = 1) ∧
      Ideal.Factors.quotientResidueEquiv p.asIdeal
          (primaryTorsionTrace p.asIdeal
            (principalCokernelMul (R := R k) t b) depth) =
        ∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  obtain ⟨t, ht, J, hspan, hcop, horder⟩ :=
    DirectSemilocalPrincipalFactorization.exists_directSemilocalUniformizerFactorization
      k F p
  exact ⟨t, ht, horder,
    quotientResidueEquiv_primaryTorsionTrace_principalCokernel_eq_sum_factorResidueTrace
      k F p J hcop t b hspan depth hdepth⟩

end QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
