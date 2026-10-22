import QEC.Coding.AlgebraicGeometry.Trace.PrimePowerQuotientTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Trace on a split Dedekind quotient

This module combines the Chinese-remainder decomposition of a mapped prime
with the prime-power quotient trace formula.  The resulting trace is a finite
sum over the actual prime factors; no finite quotient is enumerated.
-/

namespace Ideal

universe u v w w'

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

namespace Factors

open UniqueFactorizationMonoid

private theorem trace_pi_apply {K : Type w} [Field K]
    {ι : Type w'} [Fintype ι] (A : ι → Type v)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Finite K (A i)] (x : ∀ i, A i) :
    Algebra.trace K (∀ i, A i) x = ∑ i, Algebra.trace K (A i) (x i) := by
  classical
  let κ := fun i => Module.Free.ChooseBasisIndex K (A i)
  let b : ∀ i, Module.Basis (κ i) K (A i) := fun i => Module.Free.chooseBasis K (A i)
  let B : Module.Basis (Σ i, κ i) K (∀ i, A i) := Pi.basis b
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', B, Pi.basis_apply, Pi.basis_repr,
    Pi.mul_apply, Pi.single_eq_same]

variable [IsDedekindDomain S] [Module.Finite R S]

/-- The multiplication trace on the quotient by a mapped maximal ideal is
the sum, over its actual prime factors, of ramification-index-weighted
residue-field multiplication traces. -/
theorem trace_quotient_map_eq_sum_ramificationIdx_mul
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ map (algebraMap R S) p)
        (Ideal.Quotient.mk _ x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : R ⧸ p) *
          Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
            (Ideal.Quotient.mk _ x) := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  let e : (S ⧸ map (algebraMap R S) p) ≃ₐ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S) :=
    { __ := Factors.piQuotientEquiv p hp
      commutes' := Quotient.ind fun _ => rfl }
  calc
    _ = Algebra.trace (R ⧸ p)
        (∀ P : (factors (map (algebraMap R S) p)).toFinset,
          S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        (e (Ideal.Quotient.mk _ x)) :=
      (Algebra.trace_eq_of_algEquiv e (Ideal.Quotient.mk _ x)).symm
    _ = ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        Algebra.trace (R ⧸ p)
          (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
          ((e (Ideal.Quotient.mk _ x)) P) :=
      trace_pi_apply _ _
    _ = _ := by
      refine Finset.sum_congr rfl fun P _ => ?_
      change Algebra.trace (R ⧸ p)
          (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
          (Ideal.Quotient.mk _ x) = _
      exact trace_quotient_pow_ramificationIdx p P x

end Factors

end Ideal
