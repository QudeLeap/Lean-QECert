import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import QEC.Coding.AlgebraicGeometry.RiemannRoch.EffectiveDimensionBound

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li, Lean-QEC contributors
-/

/-!
# Pole divisors and the chart-variable growth family

This file constructs the actual pole divisor of a function from its global
principal divisor.  For a finite rational-function-field basis of `F`, it
then puts the independent family `b_i X^j` inside one explicit family of
Riemann--Roch spaces.  The elementary effective-divisor upper bound forces
the degree of the pole divisor of the chart variable to dominate
`[F : k(X)]`.

The finite-growth proof follows the architecture of
`RiemannRoch/Genus/Polar.lean` in
`vaca22/riemann-roch-function-fields` at commit
`dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`, adapted to this repository's
intrinsic all-place carrier and divisor API.

No genus, canonical divisor, specialty, duality, or Riemann--Roch identity is
assumed or proved here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance riemannRochPolarFamilyAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance riemannRochPolarFamilyPolynomialScalarTower :
    IsScalarTower k (Polynomial k) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance riemannRochPolarFamilyRationalScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

local instance riemannRochPolarFamilyFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

/-- The effective divisor of poles of a function.  At a nonzero function it
is the coefficientwise positive part of the negative principal divisor. -/
noncomputable def polarDivisor (x : F) : Divisor (GlobalPlace k F) := by
  classical
  exact if hx : x = 0 then 0
    else (-principalDivisor (k := k) (F := F) (Units.mk0 x hx)) ⊔ 0

@[simp]
theorem polarDivisor_zero : polarDivisor (k := k) (F := F) (0 : F) = 0 := by
  simp [polarDivisor]

/-- A pole divisor is coefficientwise nonnegative. -/
theorem polarDivisor_nonnegative (x : F) :
    Divisor.Nonnegative (polarDivisor (k := k) (F := F) x) := by
  intro P
  unfold polarDivisor
  split_ifs
  · simp
  · exact le_sup_right

/-- A nonzero function belongs to the Riemann--Roch space of its pole
divisor. -/
theorem mem_riemannRochSubmodule_polarDivisor_of_ne_zero
    {x : F} (hx : x ≠ 0) :
    x ∈ riemannRochSubmodule (polarDivisor (k := k) (F := F) x) := by
  apply (mem_riemannRochSubmodule_iff_order_add_nonnegative
    (polarDivisor (k := k) (F := F) x) hx).mpr
  intro P
  simp only [polarDivisor, dif_neg hx, Finsupp.sup_apply]
  change 0 ≤ P.order x + max
    (-(principalDivisor (k := k) (F := F) (Units.mk0 x hx) P)) 0
  rw [principalDivisor_apply]
  simp only [Units.val_mk0]
  omega

private theorem pow_mem_riemannRochSubmodule_nsmul_polar
    {x : F} (hx : x ≠ 0) (n : ℕ) :
    x ^ n ∈ riemannRochSubmodule
      (n • polarDivisor (k := k) (F := F) x) := by
  induction n with
  | zero =>
      simp only [pow_zero, zero_nsmul]
      rw [mem_riemannRochSubmodule_iff]
      intro P
      simp
  | succ n ih =>
      have hxmem := mem_riemannRochSubmodule_polarDivisor_of_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx
      have hmul := mul_mem_riemannRochSubmodule_add ih hxmem
      simpa [pow_succ, succ_nsmul] using hmul

omit ρ τ φ s in
private theorem nsmul_polarDivisor_mono {D : Divisor (GlobalPlace k F)}
    (hD : Divisor.Nonnegative D) {j r : ℕ} (hjr : j ≤ r) :
    j • D ≤ r • D := by
  intro P
  change (j : ℤ) * D P ≤ (r : ℤ) * D P
  exact mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hjr) (hD P)

/-- A common effective pole bound for a finite family of functions. -/
noncomputable def basisPoleBound {ι : Type*} [Fintype ι]
    (b : ι → F) : Divisor (GlobalPlace k F) :=
  (Finset.univ : Finset ι).sum fun i =>
    polarDivisor (k := k) (F := F) (b i)

private theorem polarDivisor_le_basisPoleBound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → F) (i : ι) :
    polarDivisor (k := k) (F := F) (b i) ≤
      basisPoleBound (k := k) (F := F) b := by
  classical
  simp only [basisPoleBound]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => polarDivisor_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (b j))

/-- The common pole bound of a finite family is effective. -/
theorem basisPoleBound_nonnegative {ι : Type*} [Fintype ι] (b : ι → F) :
    Divisor.Nonnegative (basisPoleBound (k := k) (F := F) b) := by
  intro P
  unfold basisPoleBound
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i _ =>
    polarDivisor_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (b i) P

private theorem basis_mem_riemannRochSubmodule_basisPoleBound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → F) (i : ι) :
    b i ∈ riemannRochSubmodule (basisPoleBound (k := k) (F := F) b) := by
  by_cases hi : b i = 0
  · rw [hi]
    exact zero_mem_riemannRochSubmodule _
  · exact riemannRochSubmodule_mono
      (polarDivisor_le_basisPoleBound
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b i)
      (mem_riemannRochSubmodule_polarDivisor_of_ne_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hi)

private theorem basis_mul_pow_mem_polarFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → F) {x : F} (hx : x ≠ 0) (r : ℕ)
    (i : ι) (j : ℕ) (hj : j ≤ r) :
    b i * x ^ j ∈ riemannRochSubmodule
      (basisPoleBound (k := k) (F := F) b +
        r • polarDivisor (k := k) (F := F) x) := by
  apply mul_mem_riemannRochSubmodule_add
    (basis_mem_riemannRochSubmodule_basisPoleBound
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b i)
  exact riemannRochSubmodule_mono
    (nsmul_polarDivisor_mono (k := k) (F := F)
      (polarDivisor_nonnegative
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x) hj)
    (pow_mem_riemannRochSubmodule_nsmul_polar
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx j)

/-- The image in `F` of the direct rational-function coordinate `X`. -/
noncomputable def chartVariable : F :=
  algebraMap (RatFunc k) F RatFunc.X

/-- The chart variable remains transcendental over the constant field. -/
theorem chartVariable_transcendental :
    Transcendental k (chartVariable (k := k) (F := F)) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).2
    RatFunc.transcendental_X

omit [Finite k] π τ φ s in
/-- The chart variable is nonzero. -/
theorem chartVariable_ne_zero : chartVariable (k := k) (F := F) ≠ 0 :=
  (map_ne_zero_iff (algebraMap (RatFunc k) F)
    (algebraMap (RatFunc k) F).injective).mpr RatFunc.X_ne_zero

omit [Finite k] in
private theorem linearIndependent_fin_pow_of_transcendental
    {L : Type*} [Field L] [Algebra k L] {x : L}
    (hx : Transcendental k x) (r : ℕ) :
    LinearIndependent k fun j : Fin (r + 1) => x ^ (j : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  let p : Polynomial k :=
    ∑ i : Fin (r + 1), Polynomial.C (g i) * Polynomial.X ^ (i : ℕ)
  have hzero : Polynomial.aeval x p = 0 := by
    have hsum : Polynomial.aeval x p =
        ∑ i : Fin (r + 1), g i • x ^ (i : ℕ) := by
      simp only [p, map_sum, map_mul, Polynomial.aeval_C]
      congr 1
      ext i
      rw [Polynomial.aeval_X_pow, Algebra.smul_def, mul_comm]
    rw [hsum, hg]
  have hp0 : p = 0 := (transcendental_iff.mp hx) p hzero
  have hcoeff : g j = 0 := by
    have hgj : g j = p.coeff (j : ℕ) := by
      classical
      dsimp only [p]
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      · intro i _ hne
        rw [Polynomial.coeff_C_mul_X_pow]
        split_ifs with h
        · exact absurd h (Fin.val_ne_of_ne hne.symm)
        · rfl
      · simp
    rw [hgj, hp0, Polynomial.coeff_zero]
  exact hcoeff

private theorem linearIndependent_basis_mul_chartVariable_pow {n r : ℕ}
    (b : Module.Basis (Fin n) (RatFunc k) F) :
    LinearIndependent k fun p : Fin n × Fin (r + 1) =>
      (b p.1 : F) * chartVariable (k := k) (F := F) ^ (p.2 : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let c : Fin n → RatFunc k := fun i =>
    ∑ j : Fin (r + 1), g (i, j) • RatFunc.X ^ (j : ℕ)
  have hsingle : ∀ i, algebraMap (RatFunc k) F (c i) * (b i : F) =
      ∑ j : Fin (r + 1), g (i, j) •
        ((b i : F) * chartVariable (k := k) (F := F) ^ (j : ℕ)) := by
    intro i
    dsimp only [c, chartVariable]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Algebra.smul_def, map_mul, map_pow, mul_assoc,
      mul_comm (b i : F), IsScalarTower.algebraMap_apply k (RatFunc k) F]
  have hcombo : ∑ i : Fin n, algebraMap (RatFunc k) F (c i) * (b i : F) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hsingle i, ← Finset.sum_product']
    exact hg
  have hcombo' : ∑ i : Fin n, c i • (b i : F) = 0 := by
    simpa only [Algebra.smul_def] using hcombo
  have hc : ∀ i, c i = 0 :=
    (Fintype.linearIndependent_iff.mp b.linearIndependent) c hcombo'
  intro p
  have hc' := hc p.1
  have hlin := linearIndependent_fin_pow_of_transcendental
    (k := k) (L := RatFunc k) RatFunc.transcendental_X r
  rw [Fintype.linearIndependent_iff] at hlin
  exact hlin (fun j => g (p.1, j)) (by dsimp only [c] at hc'; exact hc') p.2

/-- The explicit family `b_i X^j`, for `0 ≤ j ≤ r`, gives the lower
dimension bound along the pole-divisor ray. -/
theorem riemannRochDimension_basis_polarFamily_lower_bound {n r : ℕ}
    (b : Module.Basis (Fin n) (RatFunc k) F) :
    n * (r + 1) ≤ riemannRochDimension
      (basisPoleBound (k := k) (F := F) b +
        r • polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) := by
  let C := basisPoleBound (k := k) (F := F) b
  let B := polarDivisor (k := k) (F := F)
    (chartVariable (k := k) (F := F))
  let x := chartVariable (k := k) (F := F)
  let v : Fin n × Fin (r + 1) → F := fun p =>
    (b p.1 : F) * x ^ (p.2 : ℕ)
  have hmem : ∀ p, v p ∈ riemannRochSubmodule (C + r • B) := by
    intro p
    exact basis_mul_pow_mem_polarFamily
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
      (chartVariable_ne_zero
        (ρ := ρ) k F)
      r p.1 (p.2 : ℕ) (Nat.le_of_lt_succ p.2.isLt)
  have hlin : LinearIndependent k v :=
    linearIndependent_basis_mul_chartVariable_pow
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
  have hspan : span k (Set.range v) ≤ riemannRochSubmodule (C + r • B) := by
    refine span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hcard : n * (r + 1) ≤ Module.finrank k (span k (Set.range v)) := by
    have heq := finrank_span_eq_card hlin
    simp [heq, Fintype.card_prod, Fintype.card_fin]
  have hle : Module.finrank k (span k (Set.range v)) ≤
      Module.finrank k (riemannRochSubmodule (C + r • B)) :=
    Submodule.finrank_mono hspan
  exact hcard.trans (by
    simpa only [riemannRochDimension, C, B] using hle)

private theorem exists_valuation_gt_one_of_not_isAlgebraic
    {x : F} (hx : ¬IsAlgebraic k x) :
    ∃ P : GlobalPlace k F, 1 < P.valuation x := by
  by_contra h
  push Not at h
  exact hx (isAlgebraic_of_valuation_le_one
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x h)

private theorem residueDegree_pos (P : GlobalPlace k F) :
    0 < residueDegree (k := k) (F := F) P := by
  letI : Algebra k (residueField P) := residueAlgebra P
  letI : FiniteDimensional k (residueField P) :=
    residueField_finiteDimensional P
  rw [residueDegree_eq_finrank P]
  exact Module.finrank_pos

private theorem divisorDegree_mono
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Divisor.degree (residueDegree (k := k) (F := F)) D ≤
      Divisor.degree (residueDegree (k := k) (F := F)) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegree_nonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegree_nonnegative

private theorem polarDivisor_degree_pos
    {x : F} (hx0 : x ≠ 0) (hx : ¬IsAlgebraic k x) :
    0 < Divisor.degree (residueDegree (k := k) (F := F))
      (polarDivisor (k := k) (F := F) x) := by
  classical
  obtain ⟨P, hP⟩ := exists_valuation_gt_one_of_not_isAlgebraic
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hx
  have hcoefficient : 0 < polarDivisor (k := k) (F := F) x P := by
    have hlog : WithZero.log 1 < WithZero.log (P.valuation x) :=
      (WithZero.log_lt_log one_ne_zero
        ((P.valuation).ne_zero_iff.mpr hx0)).2 hP
    simp only [WithZero.log_one] at hlog
    simp only [polarDivisor, dif_neg hx0, Finsupp.sup_apply]
    change 0 < max
      (-(principalDivisor (k := k) (F := F) (Units.mk0 x hx0) P)) 0
    rw [principalDivisor_apply]
    simp only [Units.val_mk0]
    have hnegOrder : 0 < -P.order x := by
      simpa only [order, neg_neg] using hlog
    exact hnegOrder.trans_le (le_max_left _ _)
  have hsingle : Finsupp.single P
      (polarDivisor (k := k) (F := F) x P) ≤
      polarDivisor (k := k) (F := F) x := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)]
      exact polarDivisor_nonnegative
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F x Q
  have hle := divisorDegree_mono
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hsingle
  have hsingleDegree :
      Divisor.degree (residueDegree (k := k) (F := F))
        (Finsupp.single P (polarDivisor (k := k) (F := F) x P)) =
      polarDivisor (k := k) (F := F) x P *
        (residueDegree (k := k) (F := F) P : ℤ) := by
    simp [Divisor.degree, Divisor.degreeHom]
  rw [hsingleDegree] at hle
  have hresidue : 0 < (residueDegree (k := k) (F := F) P : ℤ) := by
    exact_mod_cast residueDegree_pos
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F P
  exact (mul_pos hcoefficient hresidue).trans_le hle

private theorem le_of_forall_nat_mul_le {n d c : ℕ} (_hd : 0 < d)
    (h : ∀ r : ℕ, n * (r + 1) ≤ d * r + c) : n ≤ d := by
  by_contra hn
  have hdn : d < n := lt_of_not_ge hn
  have hnd : 0 < n - d := Nat.sub_pos_of_lt hdn
  have hbound : ∀ r : ℕ, (n - d) * r + n ≤ c := by
    intro r
    have hr := h r
    have hn_eq : d + (n - d) = n := by omega
    rw [Nat.mul_succ, ← hn_eq, add_mul] at hr
    omega
  let q := (c - n) / (n - d)
  have hq_lt : c - n < (q + 1) * (n - d) := by
    have hmod := Nat.mod_lt (c - n) hnd
    calc
      c - n = (n - d) * q + (c - n) % (n - d) :=
        (Nat.div_add_mod (c - n) (n - d)).symm
      _ = q * (n - d) + (c - n) % (n - d) := by rw [Nat.mul_comm]
      _ < q * (n - d) + (n - d) := by gcongr
      _ = (q + 1) * (n - d) := by ring
  have hq := hbound (q + 1)
  have : (n - d) * (q + 1) ≤ c - n := by omega
  rw [Nat.mul_comm] at this
  exact (not_lt_of_ge this) hq_lt

private theorem divisorDegree_nsmul
    (n : ℕ) (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom (residueDegree (k := k) (F := F))).map_nsmul n D

/-- The dimension-growth family forces the chart variable's pole-divisor
degree to dominate the rational-function extension degree. -/
theorem functionFieldFinrank_le_polarDivisor_chartVariable_degree
    [IsFullConstantField k F] :
    Module.finrank (RatFunc k) F ≤
      (Divisor.degree (residueDegree (k := k) (F := F))
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F)))).toNat := by
  let n := Module.finrank (RatFunc k) F
  let b : Module.Basis (Fin n) (RatFunc k) F := Module.finBasis (RatFunc k) F
  let C := basisPoleBound (k := k) (F := F) b
  let B := polarDivisor (k := k) (F := F)
    (chartVariable (k := k) (F := F))
  have hBnonnegative : Divisor.Nonnegative B :=
    polarDivisor_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F _
  have hCnonnegative : Divisor.Nonnegative C :=
    basisPoleBound_nonnegative
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
  have hBdegree_nonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) B :=
    Divisor.degree_nonnegative _ _ hBnonnegative
  have hBdegree_pos : 0 <
      Divisor.degree (residueDegree (k := k) (F := F)) B :=
    polarDivisor_degree_pos
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
      (chartVariable_ne_zero
        (ρ := ρ) k F)
      (chartVariable_transcendental
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  have hdpos : 0 <
      (Divisor.degree (residueDegree (k := k) (F := F)) B).toNat := by
    rw [← Int.toNat_of_nonneg hBdegree_nonnegative] at hBdegree_pos
    exact Int.ofNat_lt.mp hBdegree_pos
  apply le_of_forall_nat_mul_le hdpos
  intro r
  let D := C + r • B
  have hDnonnegative : Divisor.Nonnegative D := by
    intro P
    exact add_nonneg (hCnonnegative P)
      (mul_nonneg (Int.natCast_nonneg r) (hBnonnegative P))
  have hlower : n * (r + 1) ≤ riemannRochDimension D :=
    riemannRochDimension_basis_polarFamily_lower_bound
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F b
  have hupper : riemannRochDimension D ≤
      (Divisor.degree (residueDegree (k := k) (F := F)) D).toNat + 1 :=
    riemannRochDimension_le_degree_add_one
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D hDnonnegative
  have hCdegree_nonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) C :=
    Divisor.degree_nonnegative _ _ hCnonnegative
  have hdegree :
      Divisor.degree (residueDegree (k := k) (F := F)) D =
        Divisor.degree (residueDegree (k := k) (F := F)) C +
          (r : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) B := by
    dsimp only [D]
    rw [Divisor.degree_add, divisorDegree_nsmul
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)]
  have hdegree_nat :
      (Divisor.degree (residueDegree (k := k) (F := F)) D).toNat =
        (Divisor.degree (residueDegree (k := k) (F := F)) C).toNat +
          r * (Divisor.degree (residueDegree (k := k) (F := F)) B).toNat := by
    have hDdegree_nonnegative : 0 ≤
        Divisor.degree (residueDegree (k := k) (F := F)) D :=
      Divisor.degree_nonnegative _ _ hDnonnegative
    apply Int.ofNat_injective
    change ((Divisor.degree (residueDegree (k := k) (F := F)) D).toNat : ℤ) =
      ((Divisor.degree (residueDegree (k := k) (F := F)) C).toNat : ℤ) +
        (r : ℤ) *
          ((Divisor.degree (residueDegree (k := k) (F := F)) B).toNat : ℤ)
    rw [Int.toNat_of_nonneg hDdegree_nonnegative,
      Int.toNat_of_nonneg hCdegree_nonnegative,
      Int.toNat_of_nonneg hBdegree_nonnegative]
    exact hdegree
  calc
    n * (r + 1) ≤ riemannRochDimension D := hlower
    _ ≤ (Divisor.degree (residueDegree (k := k) (F := F)) D).toNat + 1 := hupper
    _ = (Divisor.degree (residueDegree (k := k) (F := F)) B).toNat * r +
        ((Divisor.degree (residueDegree (k := k) (F := F)) C).toNat + 1) := by
      rw [hdegree_nat]
      ring

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
