/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Divisors.GlobalPrincipalDegree
import QEC.Coding.AlgebraicGeometry.Residues.Local.LogarithmicResidue

/-!
# The global residue sum for logarithmic differentials

This module traces the local formula `res_P (df / f) = ord_P(f)` to the
constant field and identifies its finite global sum with the weighted degree
of the actual principal divisor of `f`.  The existing principal-divisor
product formula therefore makes that sum zero.

This is only the logarithmic case of the global residue theorem.  It does not
prove vanishing for arbitrary meromorphic differentials, construct
higher-order residues or Laurent expansions, establish duality, define genus,
or state Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The traced local residue of `df / f` is the valuation order weighted by
the degree of the actual place residue field. -/
theorem simplePoleTraceResidue_logarithmicDifferential
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleTraceResidue (k := k) (F := F) P
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf P) =
      (GlobalPlace.residueDegree (k := k) (F := F) P : k) * (P.order f : k) := by
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    GlobalPlace.residueField_finiteDimensional P
  change Algebra.trace k P.residueField
      (simplePoleResidue (k := k) (F := F) P
        ⟨logarithmicDifferential (k := k) (F := F) f,
          logarithmicDifferential_isGlobalSimplePole
            (k := k) (F := F) f hf P⟩) = _
  have hresidue :
      simplePoleResidue (k := k) (F := F) P
          ⟨logarithmicDifferential (k := k) (F := F) f,
            logarithmicDifferential_isGlobalSimplePole
              (k := k) (F := F) f hf P⟩ =
        (P.order f : P.residueField) := by
    rw [show (⟨logarithmicDifferential (k := k) (F := F) f,
        logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf P⟩ : simplePoleDifferentialLattice P) =
        logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf by
      apply Subtype.ext
      rfl]
    exact simplePoleResidue_logarithmicDifferential (k := k) (F := F) P f hf
  rw [hresidue, ← map_intCast (algebraMap k P.residueField),
    Algebra.trace_algebraMap, GlobalPlace.residueDegree_eq_finrank]
  simp only [nsmul_eq_mul]

/-- A coefficient of the finite global residue family of `df / f` is the
place order weighted by the place residue degree. -/
theorem globalSimplePoleResidue_logarithmicDifferential_apply
    (f : F) (hf : f ≠ 0) (P : GlobalPlace k F) :
    globalSimplePoleResidue (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf) P =
      (GlobalPlace.residueDegree (k := k) (F := F) P : k) * (P.order f : k) := by
  rw [globalSimplePoleResidue_apply]
  exact simplePoleTraceResidue_logarithmicDifferential
    (k := k) (F := F) P f hf

/-- The finite sum of the traced local residues of `df / f` is zero.  This is
the logarithmic specialization of the global residue theorem, derived from
the actual principal-divisor degree formula. -/
theorem globalSimplePoleResidueSum_logarithmicDifferential
    (f : F) (hf : f ≠ 0) :
    globalSimplePoleResidueSum (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf) = 0 := by
  classical
  let u : Fˣ := Units.mk0 f hf
  let D : GlobalPlace k F →₀ ℤ :=
    GlobalPlace.principalDivisor (k := k) (F := F) u
  let Dk : GlobalPlace k F →₀ k :=
    D.mapRange (fun coefficient : ℤ => (coefficient : k)) (by simp)
  rw [globalSimplePoleResidueSum]
  calc
    (globalSimplePoleResidue (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf)).sum (fun _ residue => residue) =
        Dk.sum (fun P coefficient => coefficient *
          (GlobalPlace.residueDegree (k := k) (F := F) P : k)) := by
      apply Finsupp.sum_congr_of_eq_on_union
      · intro P _
        rw [globalSimplePoleResidue_logarithmicDifferential_apply
          (k := k) (F := F) f hf P]
        simp only [Dk, Finsupp.mapRange_apply, D,
          GlobalPlace.principalDivisor_apply, u, Units.val_mk0]
        ring
      · intro P _
        rfl
      · intro P _
        simp
    _ = D.sum (fun P coefficient => (coefficient : k) *
        (GlobalPlace.residueDegree (k := k) (F := F) P : k)) := by
      simpa only [Dk] using
        (Finsupp.sum_mapRange_index (g := D)
          (h := fun P coefficient => coefficient *
            (GlobalPlace.residueDegree (k := k) (F := F) P : k))
          (fun _ => by simp))
    _ = 0 := by
      have hdegree := congrArg (fun z : ℤ => (z : k))
        (GlobalPlace.principalOrder_weighted_sum_eq_zero k F u)
      simpa only [D, Int.cast_finsupp_sum, Int.cast_mul, Int.cast_natCast,
        Int.cast_zero] using hdegree

end Differential

end QEC.Coding.AlgebraicGeometry
