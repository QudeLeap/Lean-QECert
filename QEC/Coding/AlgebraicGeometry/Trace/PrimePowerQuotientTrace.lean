import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Trace.Basic
import QEC.Coding.AlgebraicGeometry.Trace.LinearTraceInvariantQuotient

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Trace on a ramified prime-power quotient

This module computes multiplication trace on a prime-power quotient by its
ideal-power filtration.  Each successive quotient is transported to the
actual residue-field extension.  The proof is symbolic: it does not enumerate
the finite quotient or choose a finite truth table.
-/

namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

namespace Factors

open UniqueFactorizationMonoid

variable [IsDedekindDomain S] [Module.Finite R S]

private noncomputable abbrev compatibleQuotientField (p : Ideal R) [p.IsMaximal] :
    Field (R ⧸ p) :=
  Ideal.Quotient.field p

private noncomputable abbrev powQuotientSubmodule (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (i : Nat) :
    Submodule (R ⧸ p)
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) :=
  Submodule.restrictScalars (R ⧸ p)
    (((P : Ideal S) ^ i).map
      (Ideal.Quotient.mk ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S))))

private noncomputable def powQuotientMul (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    powQuotientSubmodule p P i →ₗ[R ⧸ p] powQuotientSubmodule p P i :=
  ((Algebra.lmul (R ⧸ p)
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
      (Ideal.Quotient.mk _ x)).domRestrict (powQuotientSubmodule p P i)).codRestrict
    (powQuotientSubmodule p P i) fun y => by
      change Ideal.Quotient.mk _ x * (y :
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) ∈
          ((P : Ideal S) ^ i).map
            (Ideal.Quotient.mk ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S)))
      exact Ideal.mul_mem_left _ _ y.property

private noncomputable abbrev powQuotientInclusion (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (i : Nat) :
    powQuotientSubmodule p P (i + 1) →ₗ[R ⧸ p] powQuotientSubmodule p P i :=
  Ideal.powQuotSuccInclusion p (P : Ideal S) i

private noncomputable def residueQuotientMul (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    (S ⧸ (P : Ideal S)) →ₗ[R ⧸ p] (S ⧸ (P : Ideal S)) :=
  Algebra.lmul (R ⧸ p) (S ⧸ (P : Ideal S)) (Ideal.Quotient.mk _ x)

@[simp]
private theorem powQuotientMul_apply (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat)
    (y : powQuotientSubmodule p P i) :
    (powQuotientMul p P x i y :
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) =
      Ideal.Quotient.mk _ x * (y :
        S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) :=
  rfl

@[simp]
private theorem powQuotientInclusion_apply (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (i : Nat)
    (y : powQuotientSubmodule p P (i + 1)) :
    (powQuotientInclusion p P i y :
      S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) = y :=
  rfl

@[simp]
private theorem residueQuotientMul_apply (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S)
    (y : S ⧸ (P : Ideal S)) :
    residueQuotientMul p P x y = Ideal.Quotient.mk _ x * y :=
  rfl

private theorem powQuotientInclusion_range_invariant (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    LinearMap.range (powQuotientInclusion p P i) ≤
      (LinearMap.range (powQuotientInclusion p P i)).comap
        (powQuotientMul p P x i) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨powQuotientMul p P x (i + 1) y, ?_⟩
  apply Subtype.ext
  rfl

private noncomputable def powQuotientGradeMul (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i))
      →ₗ[R ⧸ p]
    (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i)) :=
  (LinearMap.range (powQuotientInclusion p P i)).mapQ
    (LinearMap.range (powQuotientInclusion p P i)) (powQuotientMul p P x i)
      (powQuotientInclusion_range_invariant p P x i)

private noncomputable def powQuotientGradeEmbedding (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) {i : Nat} {a : S}
    (ha : a ∈ (P : Ideal S) ^ i) :
    (S ⧸ (P : Ideal S)) →ₗ[R ⧸ p]
      (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i)) :=
  Ideal.quotientToQuotientRangePowQuotSucc p (P : Ideal S) ha

private theorem powQuotientGradeEmbedding_intertwines (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S)
    {i : Nat} {a : S} (ha : a ∈ (P : Ideal S) ^ i)
    (z : S ⧸ (P : Ideal S)) :
    powQuotientGradeMul p P x i (powQuotientGradeEmbedding p P ha z) =
      powQuotientGradeEmbedding p P ha (residueQuotientMul p P x z) := by
  induction z using Quotient.inductionOn' with
  | _ y =>
      rw [residueQuotientMul_apply]
      change
        powQuotientGradeMul p P x i
            (Ideal.quotientToQuotientRangePowQuotSucc p (P : Ideal S) ha
              (Submodule.Quotient.mk y)) =
          Ideal.quotientToQuotientRangePowQuotSucc p (P : Ideal S) ha
            (Ideal.Quotient.mk _ x * Submodule.Quotient.mk y)
      rw [Ideal.quotientToQuotientRangePowQuotSucc_mk]
      change
        powQuotientGradeMul p P x i
            (Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _
              (Ideal.mul_mem_right y _ ha)⟩) = _
      rw [powQuotientGradeMul, Submodule.mapQ_apply]
      change _ = Ideal.quotientToQuotientRangePowQuotSucc p (P : Ideal S) ha
        (Submodule.Quotient.mk (x * y))
      rw [Ideal.quotientToQuotientRangePowQuotSucc_mk]
      congr 2
      apply Subtype.ext
      simp only [powQuotientMul_apply]
      rw [← map_mul]
      congr 1
      ring

private theorem trace_powQuotientGradeMul_eq_residue (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S)
    {i : Nat} (hi : i < ramificationIdx' p (P : Ideal S)) :
    LinearMap.trace (R ⧸ p)
        (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i))
        (powQuotientGradeMul p P x i) =
      LinearMap.trace (R ⧸ p) (S ⧸ (P : Ideal S))
        (residueQuotientMul p P x) := by
  classical
  obtain ⟨a, ha, hna⟩ := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti (P : Ideal S) (Factors.ne_bot p P)
      (Ideal.IsPrime.ne_top inferInstance) (le_refl (i + 1)))
  let g := powQuotientGradeEmbedding p P ha
  have hg_injective : Function.Injective g := by
    exact Ideal.quotientToQuotientRangePowQuotSucc_injective
      p (P : Ideal S) hi ha hna
  have hg_surjective : Function.Surjective g := by
    exact Ideal.quotientToQuotientRangePowQuotSucc_surjective
      p (P : Ideal S) (Factors.ne_bot p P) hi ha hna
  let eg : (S ⧸ (P : Ideal S)) ≃ₗ[R ⧸ p]
      (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i)) :=
    LinearEquiv.ofBijective g ⟨hg_injective, hg_surjective⟩
  have hconj : eg.conj (residueQuotientMul p P x) = powQuotientGradeMul p P x i := by
    apply LinearMap.ext
    intro q
    obtain ⟨z, rfl⟩ := eg.surjective q
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    change g (residueQuotientMul p P x z) =
      powQuotientGradeMul p P x i (g z)
    exact (powQuotientGradeEmbedding_intertwines p P x ha z).symm
  calc
    _ = LinearMap.trace (R ⧸ p)
        (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i))
        (eg.conj (residueQuotientMul p P x)) :=
      congrArg (LinearMap.trace (R ⧸ p) _) hconj.symm
    _ = _ := @LinearMap.trace_conj'
      (R ⧸ p) (Ideal.Quotient.commRing p)
      (S ⧸ (P : Ideal S)) inferInstance inferInstance
      (powQuotientSubmodule p P i ⧸ LinearMap.range (powQuotientInclusion p P i))
      inferInstance inferInstance (residueQuotientMul p P x) eg

private theorem trace_powQuotientMul_restrict_range_eq (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) (i : Nat) :
    LinearMap.trace (R ⧸ p) (LinearMap.range (powQuotientInclusion p P i))
        (((powQuotientMul p P x i).domRestrict
          (LinearMap.range (powQuotientInclusion p P i))).codRestrict
            (LinearMap.range (powQuotientInclusion p P i))
            (fun y => powQuotientInclusion_range_invariant p P x i y.property)) =
      LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P (i + 1))
        (powQuotientMul p P x (i + 1)) := by
  let e : powQuotientSubmodule p P (i + 1) ≃ₗ[R ⧸ p]
      LinearMap.range (powQuotientInclusion p P i) :=
    LinearEquiv.ofInjective (powQuotientInclusion p P i)
      (Ideal.powQuotSuccInclusion_injective p (P : Ideal S) i)
  have hconj :
      e.conj (powQuotientMul p P x (i + 1)) =
        ((powQuotientMul p P x i).domRestrict
          (LinearMap.range (powQuotientInclusion p P i))).codRestrict
            (LinearMap.range (powQuotientInclusion p P i))
            (fun y => powQuotientInclusion_range_invariant p P x i y.property) := by
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  calc
    _ = LinearMap.trace (R ⧸ p) (LinearMap.range (powQuotientInclusion p P i))
        (e.conj (powQuotientMul p P x (i + 1))) :=
      congrArg (LinearMap.trace (R ⧸ p) _) hconj.symm
    _ = _ := @LinearMap.trace_conj'
      (R ⧸ p) (Ideal.Quotient.commRing p)
      (powQuotientSubmodule p P (i + 1)) inferInstance inferInstance
      (LinearMap.range (powQuotientInclusion p P i)) inferInstance inferInstance
      (powQuotientMul p P x (i + 1)) e

private theorem trace_powQuotientMul_step (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S)
    {i : Nat} (hi : i < ramificationIdx' p (P : Ideal S)) :
    LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P i)
        (powQuotientMul p P x i) =
      LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P (i + 1))
          (powQuotientMul p P x (i + 1)) +
        LinearMap.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (residueQuotientMul p P x) := by
  letI : Field (R ⧸ p) := compatibleQuotientField p
  calc
    _ = LinearMap.trace (R ⧸ p) (LinearMap.range (powQuotientInclusion p P i))
          (((powQuotientMul p P x i).domRestrict
            (LinearMap.range (powQuotientInclusion p P i))).codRestrict
              (LinearMap.range (powQuotientInclusion p P i))
              (fun y => powQuotientInclusion_range_invariant p P x i y.property)) +
        LinearMap.trace (R ⧸ p)
          (powQuotientSubmodule p P i ⧸
            LinearMap.range (powQuotientInclusion p P i))
          (powQuotientGradeMul p P x i) :=
      QEC.Coding.AlgebraicGeometry.LinearMap.trace_eq_restrict_add_quotient
        (powQuotientMul p P x i)
        (LinearMap.range (powQuotientInclusion p P i))
        (powQuotientInclusion_range_invariant p P x i)
    _ = _ := by
      rw [trace_powQuotientMul_restrict_range_eq,
        trace_powQuotientGradeMul_eq_residue p P x hi]

private theorem powQuotientSubmodule_ramificationIdx_eq_bot (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    powQuotientSubmodule p P (ramificationIdx' p (P : Ideal S)) = ⊥ := by
  ext y
  change y ∈ ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S)).map
      (Ideal.Quotient.mk ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S))) ↔
    y ∈ (⊥ : Ideal
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)))
  rw [Ideal.map_quotient_self]

private theorem trace_powQuotientMul_ramificationIdx_eq_zero (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    LinearMap.trace (R ⧸ p)
        (powQuotientSubmodule p P (ramificationIdx' p (P : Ideal S)))
        (powQuotientMul p P x (ramificationIdx' p (P : Ideal S))) = 0 := by
  letI : Subsingleton
      (powQuotientSubmodule p P (ramificationIdx' p (P : Ideal S))) := by
    constructor
    intro y z
    apply Subtype.ext
    have hy : (y : S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) = 0 := by
      have hy' : (y : S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) ∈
          (⊥ : Submodule (R ⧸ p)
            (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))) := by
        rw [← powQuotientSubmodule_ramificationIdx_eq_bot p P]
        exact y.property
      simpa only [Submodule.mem_bot] using hy'
    have hz : (z : S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) = 0 := by
      have hz' : (z : S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) ∈
          (⊥ : Submodule (R ⧸ p)
            (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))) := by
        rw [← powQuotientSubmodule_ramificationIdx_eq_bot p P]
        exact z.property
      simpa only [Submodule.mem_bot] using hz'
    exact hy.trans hz.symm
  have hmul :
      powQuotientMul p P x (ramificationIdx' p (P : Ideal S)) = 0 :=
    Subsingleton.elim _ _
  rw [hmul, map_zero]

private theorem powQuotientSubmodule_zero_eq_top (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    powQuotientSubmodule p P 0 = ⊤ := by
  ext y
  change y ∈ ((P : Ideal S) ^ 0).map
      (Ideal.Quotient.mk ((P : Ideal S) ^ ramificationIdx' p (P : Ideal S))) ↔
    y ∈ (⊤ : Ideal
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)))
  simp only [pow_zero, Ideal.one_eq_top, Ideal.map_top]

private theorem trace_powQuotientMul_zero_eq_algebraTrace (p : Ideal R)
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P 0)
        (powQuotientMul p P x 0) =
      Algebra.trace (R ⧸ p)
        (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        (Ideal.Quotient.mk _ x) := by
  let e0 : powQuotientSubmodule p P 0 ≃ₗ[R ⧸ p]
      (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S)) :=
    (LinearEquiv.ofEq _ _ (powQuotientSubmodule_zero_eq_top p P)).trans
      Submodule.topEquiv
  have hconj : e0.conj (powQuotientMul p P x 0) =
      Algebra.lmul (R ⧸ p)
        (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        (Ideal.Quotient.mk _ x) := by
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := e0.surjective y
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  calc
    _ = LinearMap.trace (R ⧸ p)
        (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        (e0.conj (powQuotientMul p P x 0)) :=
      (@LinearMap.trace_conj'
        (R ⧸ p) (Ideal.Quotient.commRing p)
        (powQuotientSubmodule p P 0) inferInstance inferInstance
        (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        inferInstance inferInstance (powQuotientMul p P x 0) e0).symm
    _ = LinearMap.trace (R ⧸ p)
        (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        (Algebra.lmul (R ⧸ p)
          (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
          (Ideal.Quotient.mk _ x)) :=
      congrArg (LinearMap.trace (R ⧸ p) _) hconj
    _ = _ := (Algebra.trace_apply (R ⧸ p) (Ideal.Quotient.mk _ x)).symm

private theorem trace_powQuotientMul_eq_natCast_mul (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S)
    (i : Nat) (hi : i ≤ ramificationIdx' p (P : Ideal S)) :
    LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P i)
        (powQuotientMul p P x i) =
      ((ramificationIdx' p (P : Ideal S) - i : Nat) : R ⧸ p) *
        LinearMap.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (residueQuotientMul p P x) := by
  let e := ramificationIdx' p (P : Ideal S)
  let Q : Nat → Prop := fun j =>
    LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P j)
        (powQuotientMul p P x j) =
      ((e - j : Nat) : R ⧸ p) *
        LinearMap.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (residueQuotientMul p P x)
  refine Nat.decreasingInduction' (P := Q) (fun j hj _ ih => ?_) hi ?_
  · dsimp only [Q]
    have hsub : e - j = (e - (j + 1)) + 1 := by
      dsimp only [e]
      omega
    rw [trace_powQuotientMul_step p P x hj, ih, hsub, Nat.cast_add, Nat.cast_one]
    ring
  · dsimp only [Q, e]
    rw [Nat.sub_self, Nat.cast_zero, zero_mul,
      trace_powQuotientMul_ramificationIdx_eq_zero]

/-- Multiplication trace on the ramified prime-power quotient is the
ramification index times multiplication trace on its residue-field quotient.

The proof uses the ideal-power filtration and trace additivity across invariant
subspaces; it does not enumerate elements of either finite quotient. -/
theorem trace_quotient_pow_ramificationIdx (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    Algebra.trace (R ⧸ p)
        (S ⧸ (P : Ideal S) ^ ramificationIdx' p (P : Ideal S))
        (Ideal.Quotient.mk _ x) =
      (ramificationIdx' p (P : Ideal S) : R ⧸ p) *
        Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (Ideal.Quotient.mk _ x) := by
  letI : Field (R ⧸ p) := compatibleQuotientField p
  calc
    _ = LinearMap.trace (R ⧸ p) (powQuotientSubmodule p P 0)
        (powQuotientMul p P x 0) :=
      (trace_powQuotientMul_zero_eq_algebraTrace p P x).symm
    _ = ((ramificationIdx' p (P : Ideal S) - 0 : Nat) : R ⧸ p) *
        LinearMap.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (residueQuotientMul p P x) :=
      trace_powQuotientMul_eq_natCast_mul p P x 0 (Nat.zero_le _)
    _ = _ := by
      simp only [Nat.sub_zero, residueQuotientMul, Algebra.trace_apply]

end Factors

end Ideal
