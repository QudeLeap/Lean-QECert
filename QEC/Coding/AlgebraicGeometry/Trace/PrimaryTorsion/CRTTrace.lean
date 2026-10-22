import Mathlib.RingTheory.Ideal.Quotient.Operations
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.ProdTrace
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.TraceEquiv

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Primary trace and binary Chinese remaindering

For coprime ideals `I` and `J`, multiplication on `S ⧸ (I * J)` is
intertwined by the actual Chinese-remainder equivalence with the product of
the multiplication maps on `S ⧸ I` and `S ⧸ J`.  Consequently its
finite-depth primary-torsion trace is the sum of the two quotient traces.

The proof is symbolic and functorial.  It does not enumerate a quotient,
choose a basis, compute a residue, or assert a duality, genus, or
Riemann--Roch formula.
-/

namespace QEC.Coding.AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

private noncomputable def quotientMulLinearEquivQuotientProd
    (I J : Ideal S) (hcop : IsCoprime I J) :
    (S ⧸ (I * J)) ≃ₗ[R] (S ⧸ I) × (S ⧸ J) :=
  (Ideal.quotientMulEquivQuotientProd I J hcop).toAddEquiv.toLinearEquiv
    (R := R) (by
      intro r x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hmapI : Ideal.Quotient.factor
          (Ideal.mul_le_left : I * J ≤ I)
          (algebraMap R (S ⧸ (I * J)) r) =
          algebraMap R (S ⧸ I) r := by
        change Ideal.Quotient.factor Ideal.mul_le_left
          (Ideal.Quotient.mk (I * J) (algebraMap R S r)) =
            Ideal.Quotient.mk I (algebraMap R S r)
        exact Ideal.Quotient.factor_mk Ideal.mul_le_left _
      have hmapJ : Ideal.Quotient.factor
          (Ideal.mul_le_right : I * J ≤ J)
          (algebraMap R (S ⧸ (I * J)) r) =
          algebraMap R (S ⧸ J) r := by
        change Ideal.Quotient.factor Ideal.mul_le_right
          (Ideal.Quotient.mk (I * J) (algebraMap R S r)) =
            Ideal.Quotient.mk J (algebraMap R S r)
        exact Ideal.Quotient.factor_mk Ideal.mul_le_right _
      apply Prod.ext <;>
        simp [Ideal.quotientMulEquivQuotientProd_fst,
          Ideal.quotientMulEquivQuotientProd_snd, Algebra.smul_def,
          hmapI, hmapJ])

@[simp]
private theorem quotientMulLinearEquivQuotientProd_apply
    (I J : Ideal S) (hcop : IsCoprime I J) (x : S ⧸ (I * J)) :
    quotientMulLinearEquivQuotientProd (R := R) I J hcop x =
      Ideal.quotientMulEquivQuotientProd I J hcop x :=
  rfl

/-- Chinese remaindering splits the primary trace of multiplication on a
coprime product quotient into the two coordinate primary traces. -/
theorem primaryTorsionTrace_quotientMul_eq_add
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal]
    (I J : Ideal S) (hcop : IsCoprime I J)
    (b : S) (depth : ℕ) :
    primaryTorsionTrace p
        (Algebra.lmul R (S ⧸ (I * J)) (Ideal.Quotient.mk (I * J) b)) depth =
      primaryTorsionTrace p
          (Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)) depth +
        primaryTorsionTrace p
          (Algebra.lmul R (S ⧸ J) (Ideal.Quotient.mk J b)) depth := by
  let eRing := Ideal.quotientMulEquivQuotientProd I J hcop
  let e := quotientMulLinearEquivQuotientProd (R := R) I J hcop
  let fIJ := Algebra.lmul R (S ⧸ (I * J)) (Ideal.Quotient.mk (I * J) b)
  let fI := Algebra.lmul R (S ⧸ I) (Ideal.Quotient.mk I b)
  let fJ := Algebra.lmul R (S ⧸ J) (Ideal.Quotient.mk J b)
  have hintertwines : (e : (S ⧸ (I * J)) →ₗ[R] (S ⧸ I) × (S ⧸ J)).comp fIJ =
      (fI.prodMap fJ).comp
        (e : (S ⧸ (I * J)) →ₗ[R] (S ⧸ I) × (S ⧸ J)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, fIJ, fI, fJ,
      LinearMap.prodMap_apply, e]
    change eRing (Ideal.Quotient.mk (I * J) b * x) =
      (Ideal.Quotient.mk I b * (eRing x).1,
        Ideal.Quotient.mk J b * (eRing x).2)
    rw [map_mul]
    apply Prod.ext <;>
      simp [eRing, Ideal.quotientMulEquivQuotientProd_fst,
        Ideal.quotientMulEquivQuotientProd_snd]
  calc
    primaryTorsionTrace p fIJ depth =
        primaryTorsionTrace p (fI.prodMap fJ) depth :=
      primaryTorsionTrace_eq_of_intertwining p e fIJ
        (fI.prodMap fJ) hintertwines depth
    _ = _ := primaryTorsionTrace_prodMap_eq_add p fI fJ depth

end QEC.Coding.AlgebraicGeometry
