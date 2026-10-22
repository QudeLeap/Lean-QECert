import Mathlib.LinearAlgebra.Isomorphisms
import QEC.Coding.AlgebraicGeometry.Adeles.AdelePlaceIncrement

/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Finite effective increments of the intrinsic adele filtration

The exact one-place residue quotient extends along finite divisor support.
This file proves finiteness and additivity of the resulting filtration
quotients and identifies their dimensions with weighted divisor degrees.

The proof architecture is adapted to Lean-QEC's intrinsic place API from
Guanghao Li's Apache-2.0 formalization
`vaca22/riemann-roch-function-fields`.  It makes no specialty, duality,
genus, canonical-degree, or Riemann--Roch assumption.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

noncomputable section

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

local instance globalAdeleFilterAddCommGroup
    (D : Divisor (GlobalPlace k F)) :
    AddCommGroup (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.addCommGroup _

local instance globalAdeleFilterModule
    (D : Divisor (GlobalPlace k F)) :
    Module k (globalAdeleFilter (k := k) (F := F) D) :=
  Submodule.module _

private theorem globalAdeleFilterDiffQuotient_finite_add_placeDivisor
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) ⧸
        Submodule.comap
          (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField := residueField_finiteDimensional P
  let f := globalAdeleLocalLeadingCoefficient (k := k) (F := F) D P
  let p := Submodule.comap
    (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
    (globalAdeleFilter (k := k) (F := F) D)
  haveI : Module.Finite k f.range := inferInstance
  haveI : Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq f.ker p
    (globalAdeleLocalLeadingCoefficient_ker (k := k) (F := F) D P))

private theorem globalAdeleFilterDiffQuotient_finite_self
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) D ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) D).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  rw [show Submodule.comap
      (globalAdeleFilter (k := k) (F := F) D).subtype
      (globalAdeleFilter (k := k) (F := F) D) = ⊤ from
    Submodule.comap_subtype_self (globalAdeleFilter (k := k) (F := F) D)]
  exact Module.Finite.of_finite

private theorem globalAdeleFilterDiffQuotient_finite_mono_add
    {D M N : Divisor (GlobalPlace k F)} (hDM : D ≤ M) (hMN : M ≤ N)
    [Module.Finite k
      (globalAdeleFilter (k := k) (F := F) N ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) N).subtype
          (globalAdeleFilter (k := k) (F := F) M))]
    [Module.Finite k
      (globalAdeleFilter (k := k) (F := F) M ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) M).subtype
          (globalAdeleFilter (k := k) (F := F) D))] :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) N ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) N).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  let p := globalAdeleFilter (k := k) (F := F) N
  let q := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) D)
  let r := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) M)
  let pM := globalAdeleFilter (k := k) (F := F) M
  let qM := Submodule.comap pM.subtype (globalAdeleFilter (k := k) (F := F) D)
  have hqr : q ≤ r := Submodule.comap_mono (globalAdeleFilter_mono hDM)
  let eR := Submodule.comapSubtypeEquivOfLe (globalAdeleFilter_mono hMN)
  let qInR : Submodule k ↑r := Submodule.comap r.subtype q
  have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
    rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
    rfl
  have eMq : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) :=
    Submodule.Quotient.equiv qM qInR eR.symm hqmap
  haveI : Module.Finite k (r ⧸ qInR) := Module.Finite.equiv eMq
  have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range =
      r.map q.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
  haveI : Module.Finite k (r.map q.mkQ) := Module.Finite.equiv eQuot
  have eThird := Submodule.quotientQuotientEquivQuotient q r hqr
  haveI : Module.Finite k (p ⧸ r) := by
    dsimp only [p, r]
    infer_instance
  haveI : Module.Finite k ((p ⧸ q) ⧸ Submodule.map q.mkQ r) :=
    Module.Finite.equiv eThird.symm
  exact Module.Finite.of_submodule_quotient (Submodule.map q.mkQ r)

private theorem globalAdeleFilterDiffQuotient_finite_single_nat
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (n : ℕ) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + Finsupp.single P (n : ℤ)) ⧸
        Submodule.comap
          (globalAdeleFilter (k := k) (F := F)
            (D + Finsupp.single P (n : ℤ))).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  classical
  induction n with
  | zero =>
      have heq : D + Finsupp.single P ((0 : ℕ) : ℤ) = D := by simp
      rw [heq]
      exact globalAdeleFilterDiffQuotient_finite_self D
  | succ n ih =>
      have heq : D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
          D + Finsupp.single P (n : ℤ) + placeDivisor P := by
        ext Q
        simp only [Finsupp.add_apply, Finsupp.single_apply, placeDivisor]
        split <;> omega
      have hDM : D ≤ D + Finsupp.single P (n : ℤ) := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hMN : D + Finsupp.single P (n : ℤ) ≤
          D + Finsupp.single P (n : ℤ) + placeDivisor P := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [placeDivisor, Finsupp.single_apply]
          split <;> omega)
      letI := ih
      haveI := globalAdeleFilterDiffQuotient_finite_add_placeDivisor
        (D + Finsupp.single P (n : ℤ)) P
      rw [heq]
      exact globalAdeleFilterDiffQuotient_finite_mono_add hDM hMN

private theorem globalAdeleFilterDiffQuotient_finite_add_nonnegative
    (D E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) (D + E) ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) (D + E)).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero]
      exact globalAdeleFilterDiffQuotient_finite_self D
  | single_add P coefficient tail hPtail hcoefficient ih =>
      have htailP : tail P = 0 := Finsupp.notMem_support_iff.mp hPtail
      have htail : Divisor.Nonnegative tail := by
        intro Q
        by_cases hQP : Q = P
        · subst Q
          rw [htailP]
        · simpa [Finsupp.single_apply, hQP] using hE Q
      have hcoefficient_nonnegative : 0 ≤ coefficient := by
        simpa [Finsupp.single_apply, htailP] using hE P
      letI := ih D htail
      haveI := globalAdeleFilterDiffQuotient_finite_single_nat
        (D + tail) P coefficient.toNat
      have hcoefficient_cast : (coefficient.toNat : ℤ) = coefficient :=
        Int.toNat_of_nonneg hcoefficient_nonnegative
      have heq : D + (Finsupp.single P coefficient + tail) =
          (D + tail) + Finsupp.single P (coefficient.toNat : ℤ) := by
        rw [hcoefficient_cast]
        abel
      have hDM : D ≤ D + tail := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (htail Q)
      have hMN : D + tail ≤
          (D + tail) + Finsupp.single P (coefficient.toNat : ℤ) := by
        intro Q
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      rw [heq]
      exact globalAdeleFilterDiffQuotient_finite_mono_add hDM hMN

/-- Every quotient between comparable intrinsic adele filtration pieces is
finite-dimensional over the constant field. -/
theorem globalAdeleFilterDiffQuotient_finite_of_le
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) E ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have heq : E = D + (E - D) := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [heq]
  exact globalAdeleFilterDiffQuotient_finite_add_nonnegative D (E - D) hnonnegative

/-- Dimensions of comparable intrinsic adele filtration quotients add through
an intermediate divisor. -/
theorem globalAdeleFilterDiffDimension_mono_add
    {D M N : Divisor (GlobalPlace k F)} (hDM : D ≤ M) (hMN : M ≤ N) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D N =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        globalAdeleFilterDiffDimension (k := k) (F := F) M N := by
  let p := globalAdeleFilter (k := k) (F := F) N
  let q := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) D)
  let r := Submodule.comap p.subtype (globalAdeleFilter (k := k) (F := F) M)
  have hqr : q ≤ r := Submodule.comap_mono (globalAdeleFilter_mono hDM)
  have hDN : D ≤ N := hDM.trans hMN
  haveI : Module.Finite k (p ⧸ q) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDN
  haveI : Module.Finite k (p ⧸ r) :=
    globalAdeleFilterDiffQuotient_finite_of_le hMN
  have e := Submodule.quotientQuotientEquivQuotient q r hqr
  have hadd := Submodule.finrank_quotient_add_finrank (r.map q.mkQ)
  have hrmap : Module.finrank k (r.map q.mkQ) =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M := by
    let pM := globalAdeleFilter (k := k) (F := F) M
    let qM := Submodule.comap pM.subtype (globalAdeleFilter (k := k) (F := F) D)
    let qInR : Submodule k ↑r := Submodule.comap r.subtype q
    let eR := Submodule.comapSubtypeEquivOfLe (globalAdeleFilter_mono hMN)
    have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
      rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
      rfl
    have eM : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) :=
      Submodule.Quotient.equiv qM qInR eR.symm hqmap
    have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range =
        r.map q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
      rw [← hker, ← hrange]
      exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
    dsimp only [globalAdeleFilterDiffDimension]
    rw [← eQuot.finrank_eq, eM.finrank_eq]
  calc
    Module.finrank k (p ⧸ q) =
        Module.finrank k ((p ⧸ q) ⧸ Submodule.map q.mkQ r) +
          Module.finrank k ↑(Submodule.map q.mkQ r) := hadd.symm
    _ = Module.finrank k (p ⧸ r) +
        globalAdeleFilterDiffDimension (k := k) (F := F) D M := by
      rw [e.finrank_eq, hrmap]
    _ = globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        globalAdeleFilterDiffDimension (k := k) (F := F) M N := by
      dsimp only [globalAdeleFilterDiffDimension]
      rw [add_comm]

private theorem globalAdeleFilterDiffDimension_add_placeDivisor_of_le
    {D M : Divisor (GlobalPlace k F)} (P : GlobalPlace k F) (hDM : D ≤ M) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (M + placeDivisor P) =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        residueDegree (k := k) (F := F) P := by
  have hMN : M ≤ M + placeDivisor P := by
    intro Q
    simp only [Finsupp.add_apply]
    exact le_add_of_nonneg_right (by
      by_cases hQP : Q = P
      · subst Q
        simp
      · rw [placeDivisor_apply_of_ne P Q (Ne.symm hQP)])
  rw [globalAdeleFilterDiffDimension_mono_add hDM hMN,
    globalAdeleFilterDiffDimension_add_placeDivisor]

private theorem globalAdeleFilterDiffDimension_add_single_nat
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (n : ℕ) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D
        (D + Finsupp.single P (n : ℤ)) =
      n * residueDegree (k := k) (F := F) P := by
  classical
  induction n with
  | zero =>
      simp only [Nat.cast_zero, Finsupp.single_zero, add_zero, zero_mul]
      rw [globalAdeleFilterDiffDimension]
      have hp : Submodule.comap
          (globalAdeleFilter (k := k) (F := F) D).subtype
          (globalAdeleFilter (k := k) (F := F) D) = ⊤ := by
        ext a
        simp
      rw [hp]
      exact Module.finrank_zero_of_subsingleton
  | succ n ih =>
      let M := D + Finsupp.single P (n : ℤ)
      have hDM : D ≤ M := by
        intro Q
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have heq : D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
          M + placeDivisor P := by
        dsimp only [M]
        ext Q
        simp only [Finsupp.add_apply, Finsupp.single_apply, placeDivisor]
        split <;> omega
      calc
        globalAdeleFilterDiffDimension (k := k) (F := F) D
            (D + Finsupp.single P ((n + 1 : ℕ) : ℤ)) =
            globalAdeleFilterDiffDimension (k := k) (F := F) D
              (M + placeDivisor P) := by rw [heq]
        _ = globalAdeleFilterDiffDimension (k := k) (F := F) D M +
            residueDegree (k := k) (F := F) P :=
          globalAdeleFilterDiffDimension_add_placeDivisor_of_le P hDM
        _ = n * residueDegree (k := k) (F := F) P +
            residueDegree (k := k) (F := F) P := by
          rw [← ih]
        _ = (n + 1) * residueDegree (k := k) (F := F) P := by ring

/-- An effective divisor increment contributes exactly its weighted degree to
the intrinsic adele filtration quotient. -/
theorem globalAdeleFilterDiffDimension_add_nonnegative
    (D E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (D + E) =
      (Divisor.degree (residueDegree (k := k) (F := F)) E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero, globalAdeleFilterDiffDimension, Divisor.degree_zero]
      have hp : Submodule.comap
          (globalAdeleFilter (k := k) (F := F) D).subtype
          (globalAdeleFilter (k := k) (F := F) D) = ⊤ := by
        ext a
        simp
      rw [hp]
      exact Module.finrank_zero_of_subsingleton
  | single_add P coefficient tail hPtail hcoefficient ih =>
      have htailP : tail P = 0 := Finsupp.notMem_support_iff.mp hPtail
      have htail : Divisor.Nonnegative tail := by
        intro Q
        by_cases hQP : Q = P
        · subst Q
          rw [htailP]
        · have hQE := hE Q
          simpa [Finsupp.single_apply, hQP] using hQE
      have hcoefficient_nonnegative : 0 ≤ coefficient := by
        have hPE := hE P
        simpa [Finsupp.single_apply, htailP] using hPE
      let M := D + tail
      let N := M + Finsupp.single P (coefficient.toNat : ℤ)
      have hDM : D ≤ M := by
        intro Q
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (htail Q)
      have hMN : M ≤ N := by
        intro Q
        dsimp only [N]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hfirst := ih D htail
      have hsecond : globalAdeleFilterDiffDimension (k := k) (F := F) M N =
          coefficient.toNat * residueDegree (k := k) (F := F) P := by
        exact globalAdeleFilterDiffDimension_add_single_nat M P coefficient.toNat
      have hdegree_tail : 0 ≤
          Divisor.degree (residueDegree (k := k) (F := F)) tail :=
        Divisor.degree_nonnegative _ tail htail
      have hdegree_total : 0 ≤
          Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail) :=
        Divisor.degree_nonnegative _ _ hE
      have hdegree :
          Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail) =
            coefficient * (residueDegree (k := k) (F := F) P : ℤ) +
              Divisor.degree (residueDegree (k := k) (F := F)) tail := by
        rw [Divisor.degree_add]
        simp [Divisor.degree, Divisor.degreeHom]
      have hdegree_nat :
          (Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat =
            coefficient.toNat * residueDegree (k := k) (F := F) P +
              (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat := by
        have htail_cast :
            ((Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat : ℤ) =
              Divisor.degree (residueDegree (k := k) (F := F)) tail :=
          Int.toNat_of_nonneg hdegree_tail
        have htotal_cast :
            ((Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat : ℤ) =
                Divisor.degree (residueDegree (k := k) (F := F))
                  (Finsupp.single P coefficient + tail) :=
          Int.toNat_of_nonneg hdegree_total
        apply Int.ofNat_injective
        change ((Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail)).toNat : ℤ) =
          ((coefficient.toNat * residueDegree (k := k) (F := F) P +
            (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat : ℕ) : ℤ)
        rw [htotal_cast, Nat.cast_add, Nat.cast_mul,
          Int.toNat_of_nonneg hcoefficient_nonnegative, htail_cast]
        exact hdegree
      have htotal : globalAdeleFilterDiffDimension (k := k) (F := F) D N =
          (Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail)).toNat := by
        have hadd := globalAdeleFilterDiffDimension_mono_add hDM hMN
        rw [hadd, hfirst, hsecond, hdegree_nat, Nat.add_comm]
      have heq : D + (Finsupp.single P coefficient + tail) = N := by
        dsimp only [N, M]
        rw [Int.toNat_of_nonneg hcoefficient_nonnegative]
        abel
      rw [heq]
      exact htotal

/-- For comparable divisors, the intrinsic adele quotient dimension is the
weighted degree of their effective difference. -/
theorem globalAdeleFilterDiffDimension_of_le
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D E =
      (Divisor.degree (residueDegree (k := k) (F := F)) (E - D)).toNat := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hrank := globalAdeleFilterDiffDimension_add_nonnegative D (E - D) hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [heq] at hrank
  exact hrank

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
