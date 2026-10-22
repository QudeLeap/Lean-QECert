/-
Copyright (c) 2026 The Lean-QEC authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EnjiXiong
-/
/-
# Artin–Schreier valuation exclusions for the WHY24 F1024 tower (#887)

The Garcia–Stichtenoth tower over `F_1024` (`l = 32`) is
`F₁ = F₁₀₂₄(x₁)`, `F_{i+1} = F_i(z_{i+1})` with `z_{i+1}³² + z_{i+1} = x_i³³`.
Each step is an Artin–Schreier extension: `X³² + X - C(x_i³³)` over `F_i`,
and its irreducibility — which is what makes `F_{i+1}` a *field* — is
classically proved at the infinity place: the root would need valuation
`exp 33` (`x_i` has a simple pole, so `ν(x_i³³) = exp 33`), and the two
obstructions that make this impossible are exactly `asNoRoot` and
`frobeniusCombo_ne` below.

* `asNoRoot`: `y³² + y` never has valuation `exp 33` — by the strict
  triangle inequality the sum is dominated by either `y³²` (valuation
  `exp (32·t)`) or `y` (valuation `exp t`), and `32·t = 33` resp. `t = 33`
  both fail in `ℤᵐ⁰`.
* `frobeniusCombo_ne`: the surviving case of the Frobenius-iteration
  argument (`u = ∑ cⱼ a^{2^j}`, top coefficient 1, `cⱼ³² = cⱼ`, hence
  `ν cⱼ ∈ {0, 1}`) is excluded because the dominant term of the sum has
  valuation `exp (2^j · log (ν a))` for some `j ∈ {1, 2, 3, 4}`, which can
  never equal `exp 33` (`33` is odd).

Together with the abstract Frobenius-iteration structure theorem (to be
added in a follow-up in this module) these give `Irreducible (X³² + X - C u)`
for every level of the tower. Source: Garcia–Stichtenoth 1995 (bibliographic
record, citation-only) as used by WHY24 `main.tex`, `technicalCodeTheorem`
region, `l = 32`; formalized here from scratch, no project axioms.
-/
import Mathlib

namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier

open scoped WithZero BigOperators
open Polynomial

variable {F : Type*} [Field F]

/-- The degree-32 additive polynomial used at each `l = 32` tower step. -/
noncomputable def artinSchreierPolynomial (u : F) : F[X] :=
  X ^ 32 + X - C u

/-- The displayed additive polynomial is monic, independently of its root behavior. -/
theorem artinSchreierPolynomial_monic (u : F) :
    (artinSchreierPolynomial u).Monic := by
  rw [artinSchreierPolynomial]
  convert monic_X_pow_add (p := X - C u) (show degree (X - C u) < (32 : ℕ) by
    calc
      degree (X - C u) ≤ max (degree X) (degree (C u)) := degree_sub_le _ _
      _ ≤ 1 := by exact max_le (by simp) (degree_C_le.trans (by norm_num))
      _ < (32 : ℕ) := by norm_num) using 1; ring

/-- In characteristic two, the tower's additive polynomial is separable because its
derivative is one.  This is distinct from the valuation-based irreducibility work. -/
theorem artinSchreierPolynomial_separable [CharP F 2] (u : F) :
    (artinSchreierPolynomial u).Separable := by
  rw [artinSchreierPolynomial]
  have hrewrite : (X ^ 32 + X - C u : F[X]) =
      C 1 * X ^ 32 + C 1 * X + C (-u) := by
    simp only [map_one, one_mul, C_neg]
    ring
  rw [hrewrite]
  exact separable_C_mul_X_pow_add_C_mul_X_add_C' 2 32 (1 : F) 1 (-u)
    (by norm_num) isUnit_one

/-- `exp a < exp b ↔ a < b` in `ℤᵐ⁰` (the standard order, in which
`exp 0 = 1` and poles have valuation `> 1`). -/
private theorem exp_lt_exp {a b : ℤ} : WithZero.exp a < WithZero.exp b ↔ a < b := by
  simp [WithZero.exp]

/-- A Frobenius-fixed element (`c³² = c`) has valuation `0` (iff `c = 0`)
or `1`: applying `ν` gives `(ν c)³² = ν c`, i.e. `32·log (ν c) = log (ν c)`
in `ℤᵐ⁰`. -/
theorem val_of_frobenius_fixed (ν : Valuation F ℤᵐ⁰) {c : F} (hc : c ^ 32 = c) :
    ν c = 0 ∨ ν c = 1 := by
  have hν : (ν c) ^ 32 = ν c := by
    simpa [map_pow] using congrArg ν hc
  by_cases h0 : ν c = 0
  · exact Or.inl h0
  · right
    have hce : ν c = WithZero.exp (WithZero.log (ν c)) := (WithZero.exp_log h0).symm
    rw [hce] at hν
    rw [← WithZero.exp_nsmul] at hν
    have hlog32 : (32 : ℕ) • WithZero.log (ν c) = WithZero.log (ν c) :=
      WithZero.exp_inj.mp hν
    have hlog0 : WithZero.log (ν c) = 0 := by
      rw [nsmul_eq_mul] at hlog32
      omega
    rw [hce, hlog0]
    simp

/--
**Root obstruction at the infinity place.** If `ν u = exp 33` (a pole of order
33, e.g. `u = x_i³³` for the tower coordinate `x_i`), then no `y` satisfies
`y³² + y = u`. By the strict triangle inequality, `ν (y³² + y)` is either
`exp (32·t)` (when `y` is a pole, `t > 0`), `exp t` (when `y` is a zero,
`t < 0`), or `≤ 1` (when `ν y = 1`); equating with `exp 33` forces
`t = 33/32` or `t = 33 > 0`, both impossible.
-/
theorem asNoRoot (ν : Valuation F ℤᵐ⁰) (u : F) (hu : ν u = WithZero.exp (33 : ℤ))
    (y : F) : y ^ 32 + y ≠ u := by
  intro h
  have hν : ν (y ^ 32 + y) = WithZero.exp (33 : ℤ) := by
    rw [h, hu]
  by_cases hy0 : ν y = 0
  · -- y = 0, so u = 0, contradicting `ν u = exp 33 ≠ 0`
    have hy : y = 0 := (Valuation.zero_iff ν).mp hy0
    subst y
    have hu0 : u = 0 := by simpa using h.symm
    rw [hu0, Valuation.map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  · -- ν y = exp r for a unique r : ℤ
    let r : ℤ := WithZero.log (ν y)
    have hye : ν y = WithZero.exp r := by
      dsimp [r]
      exact (WithZero.exp_log hy0).symm
    have hνy32 : ν (y ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
      rw [map_pow, hye, ← WithZero.exp_nsmul]
    by_cases hrpos : 0 < r
    · -- y is a pole: `y³²` strictly dominates, `ν (y³² + y) = exp (32·r)`
      have hlt : ν y < ν (y ^ 32) := by
        rw [hye, hνy32]
        exact exp_lt_exp.mpr (by
          rw [nsmul_eq_mul]
          omega)
      have hsum : ν (y ^ 32 + y) = WithZero.exp ((32 : ℕ) • r) := by
        rw [Valuation.map_add_eq_of_lt_left ν hlt, hνy32]
      rw [hsum] at hν
      have h32r : (32 : ℕ) • r = 33 := WithZero.exp_inj.mp hν
      rw [nsmul_eq_mul] at h32r
      omega -- 32·r = 33 has no integer solution
    · by_cases hrneg : r < 0
      · -- y is a zero: `ν (y³²) < ν y`, so `ν (y³² + y) = exp r`
        have hlt : ν (y ^ 32) < ν y := by
          rw [hνy32, hye]
          exact exp_lt_exp.mpr (by
            rw [nsmul_eq_mul]
            omega)
        have hsum : ν (y ^ 32 + y) = ν y := by
          rw [Valuation.map_add_eq_of_lt_right ν hlt]
        rw [hsum, hye] at hν
        have hr33 : r = 33 := WithZero.exp_inj.mp hν
        omega -- r = 33 contradicts r < 0
      · -- r = 0: both summands have valuation 1, so the sum has valuation ≤ 1 < exp 33
        have hr0 : r = 0 := by omega
        have hy1 : ν y = 1 := by simp [hye, hr0]
        have hy321 : ν (y ^ 32) = 1 := by rw [map_pow, hy1, one_pow]
        have hle : ν (y ^ 32 + y) ≤ 1 := by
          have := map_add_le_max ν (y ^ 32) y
          rwa [hy321, hy1] at this
        have hlt1 : 1 < WithZero.exp (33 : ℤ) := exp_lt_exp.mpr (by norm_num)
        rw [hν] at hle
        exact (not_lt_of_ge hle) hlt1

/--
**Frobenius-combination exclusion.** `u` is never of the form
`∑ cⱼ a^{2^j}` with top coefficient `c_m = 1` and all coefficients
Frobenius-fixed (`cⱼ³² = cⱼ`, hence `ν cⱼ ∈ {0, 1}`) for `1 ≤ m ≤ 4`.
Writing `ν a = exp r`: the terms have valuations `exp (2^j·r)` (up to the
coefficient factor `ν cⱼ ∈ {0, 1}`), and the strict maximum is attained at
a unique `j₀` (`j₀ = m` when `r > 0`, the least nonzero-coefficient index when
`r < 0`), so `ν u = exp (2^{j₀}·r)`. Equating with `exp 33` forces
`r = 33/2^{j₀}`; for `r < 0` this is positive, and for `r > 0` it is not an
integer while `r : ℤ` — both impossible. The `r = 0` case has all valuations
`≤ 1 < exp 33`. This excludes the surviving case of the Frobenius-iteration
argument for the irreducibility of `X³² + X - C u`.
-/
theorem frobeniusCombo_ne (ν : Valuation F ℤᵐ⁰) (u : F)
    (hu : ν u = WithZero.exp (33 : ℤ)) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (a : F) (c : Fin (m + 1) → F) (hc : ∀ j : Fin (m + 1), c j ^ 32 = c j)
    (hcTop : c ⟨m, Nat.lt_succ_self m⟩ = 1) :
    u ≠ ∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) := by
  intro h
  have hν : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = WithZero.exp (33 : ℤ) := by
    rw [← h, hu]
  by_cases ha0 : a = 0
  · -- a = 0 makes the whole sum vanish, contradicting `ν u = exp 33 ≠ 0`
    subst a
    have hsum : (∑ j : Fin (m + 1), c j * 0 ^ (2 ^ (j : ℕ))) = 0 := by
      simp
    have hu0 : u = 0 := by simpa [hsum] using h
    rw [hu0, Valuation.map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  · -- ν a = exp r, r : ℤ
    have hva0 : ν a ≠ 0 := (Valuation.ne_zero_iff ν).mpr ha0
    let r : ℤ := WithZero.log (ν a)
    have hae : ν a = WithZero.exp r := by
      dsimp [r]
      exact (WithZero.exp_log hva0).symm
    have hcv : ∀ j : Fin (m + 1), ν (c j) = 0 ∨ ν (c j) = 1 :=
      fun j => val_of_frobenius_fixed ν (hc j)
    have hg : ∀ j : Fin (m + 1),
        ν (c j * a ^ (2 ^ (j : ℕ))) = ν (c j) * WithZero.exp (((2 ^ (j : ℕ) : ℕ) : ℤ) * r) := by
      intro j
      rw [map_mul, map_pow, hae, ← WithZero.exp_nsmul, nsmul_eq_mul]
    by_cases hrpos : 0 < r
    · -- r > 0: the top term `a^{2^m}` (coefficient 1) strictly dominates
      let g : Fin (m + 1) → ℤᵐ⁰ := fun j => ν (c j * a ^ (2 ^ (j : ℕ)))
      let jmax : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      have hgmax : g jmax = WithZero.exp (((2 ^ m : ℕ) : ℤ) * r) := by
        dsimp [g, jmax]
        rw [hg, hcTop, ν.map_one, one_mul]
        norm_cast
      have hstrict : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))) \ {jmax}, g i < g jmax := by
        intro i hi
        have hine : i ≠ jmax := by
          simpa using (Finset.mem_sdiff.mp hi).2
        have him : (i : ℕ) < m := by
          have hilt : (i : ℕ) < m + 1 := i.isLt
          have hineN : (i : ℕ) ≠ m := by
            intro hiN
            exact hine (Fin.ext hiN)
          omega
        have hpowlt : (2 ^ (i : ℕ) : ℕ) < 2 ^ m := by
          exact pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) him
        have hpowltz : ((2 ^ (i : ℕ) : ℕ) : ℤ) < ((2 ^ m : ℕ) : ℤ) := by
          exact_mod_cast hpowlt
        have hci : ν (c i) ≤ 1 := by
          rcases hcv i with h0 | h1
          · exact le_trans (le_of_eq h0) (zero_le (a := (1 : ℤᵐ⁰)))
          · exact le_of_eq h1
        have hgile : g i ≤ WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r) := by
          dsimp [g]
          rw [hg]
          simpa using mul_le_mul_left hci (WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r))
        have hexp : WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r) <
            WithZero.exp (((2 ^ m : ℕ) : ℤ) * r) := by
          rw [exp_lt_exp]
          exact mul_lt_mul_of_pos_right hpowltz hrpos
        exact lt_of_le_of_lt hgile (hexp.trans_eq hgmax.symm)
      have hsum : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = g jmax := by
        change ν (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))),
          (fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) i) = ν
          ((fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) jmax)
        exact ν.map_sum_eq_of_lt (Finset.mem_univ jmax) (by intro i hi; exact hstrict i hi)
      rw [hsum, hgmax] at hν
      have hEq : ((2 ^ m : ℕ) : ℤ) * r = 33 := WithZero.exp_inj.mp hν
      interval_cases m <;> norm_num at hEq <;> omega
    · by_cases hrneg : r < 0
      · -- r < 0: the strict maximum over the finitely many term valuations is
        -- attained at a unique index, and equals `exp (2^{j₀}·r)`
        let g : Fin (m + 1) → ℤᵐ⁰ := fun j => ν (c j * a ^ (2 ^ (j : ℕ)))
        obtain ⟨jmax, hjmem, hjmaxle⟩ :=
          Finset.exists_max_image (Finset.univ : Finset (Fin (m + 1))) g
            (Finset.univ_nonempty)
        have hsum0 : (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) ≠ 0 := by
          intro hs
          have hz : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = 0 := by
            simp [hs]
          rw [hν] at hz
          exact WithZero.exp_ne_zero hz
        have hex : ∃ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) ≠ 0 := by
          by_contra hne
          have hne' : ∀ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) = 0 := by
            intro j
            by_contra hj
            exact hne ⟨j, hj⟩
          exact hsum0 (Finset.sum_eq_zero (fun j _ => hne' j))
        rcases hex with ⟨j0, hj0⟩
        have hgmax0 : g jmax ≠ 0 := by
          intro hz
          have hle : g j0 ≤ g jmax := hjmaxle j0 (Finset.mem_univ j0)
          have hg0 : g j0 ≠ 0 := by
            dsimp [g]
            exact (Valuation.ne_zero_iff ν).mpr hj0
          rw [hz] at hle
          exact hg0 (le_antisymm hle (zero_le (a := g j0)))
        have hstrict : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))) \ {jmax}, g i < g jmax := by
          intro i hi
          have hle : g i ≤ g jmax := hjmaxle i (Finset.mem_univ i)
          have hne : g i ≠ g jmax := by
            intro hEq
            have hine : i ≠ jmax := by simpa using (Finset.mem_sdiff.mp hi).2
            have hci : c i ≠ 0 := by
              intro hcz
              have : g i = 0 := by dsimp [g]; simp [hcz]
              exact hgmax0 (hEq.symm.trans this)
            have hνci : ν (c i) = 1 := by
              rcases hcv i with h0 | h1
              · exfalso; exact hci ((Valuation.zero_iff ν).mp h0)
              · exact h1
            have gi : g i = WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r) := by
              dsimp [g]
              rw [hg, hνci, one_mul]
              norm_cast
            have hcj : c jmax ≠ 0 := by
              intro hcz
              have : g jmax = 0 := by dsimp [g]; simp [hcz]
              exact hgmax0 this
            have hνcj : ν (c jmax) = 1 := by
              rcases hcv jmax with h0 | h1
              · exfalso; exact hcj ((Valuation.zero_iff ν).mp h0)
              · exact h1
            have gj : g jmax = WithZero.exp (((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r) := by
              dsimp [g]
              rw [hg, hνcj, one_mul]
              norm_cast
            have hexp : ((2 ^ (i : ℕ) : ℕ) : ℤ) * r = ((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r := by
              rw [gi, gj] at hEq
              exact WithZero.exp_inj.mp hEq
            have hr0 : r ≠ 0 := ne_of_lt hrneg
            have hpow : ((2 ^ (i : ℕ) : ℕ) : ℤ) = ((2 ^ (jmax : ℕ) : ℕ) : ℤ) := by
              exact mul_right_cancel₀ hr0 hexp
            have hpowN : 2 ^ (i : ℕ) = 2 ^ (jmax : ℕ) := by exact_mod_cast hpow
            have hij : i = jmax := by
              apply Fin.ext
              exact (pow_right_injective₀ (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) ≠ 1)) hpowN
            exact hine hij
          exact lt_of_le_of_ne hle hne
        have hsum : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = g jmax := by
          change ν (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))),
            (fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) i) = ν
            ((fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) jmax)
          exact ν.map_sum_eq_of_lt (Finset.mem_univ jmax) (by intro i hi; exact hstrict i hi)
        have hcj : c jmax ≠ 0 := by
          intro hcz
          have : g jmax = 0 := by dsimp [g]; simp [hcz]
          exact hgmax0 this
        have hνcj : ν (c jmax) = 1 := by
          rcases hcv jmax with h0 | h1
          · exfalso; exact hcj ((Valuation.zero_iff ν).mp h0)
          · exact h1
        have hgmaxexp : g jmax = WithZero.exp (((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r) := by
          dsimp [g]
          rw [hg, hνcj, one_mul]
          norm_cast
        rw [hsum, hgmaxexp] at hν
        have hEq : ((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r = 33 := WithZero.exp_inj.mp hν
        have hpos : (0 : ℤ) < ((2 ^ (jmax : ℕ) : ℕ) : ℤ) := by
          exact_mod_cast (pow_pos (by norm_num : (0 : ℕ) < 2) (jmax : ℕ))
        have hneg : ((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r < 0 := mul_neg_of_pos_of_neg hpos hrneg
        omega -- (2^{j₀}·r = 33) and (2^{j₀}·r < 0)
      · -- r = 0: every term has valuation ≤ 1, but the sum has valuation exp 33 > 1
        have hr0 : r = 0 := by omega
        have hle1 : ∀ j : Fin (m + 1), ν (c j * a ^ (2 ^ (j : ℕ))) ≤ 1 := by
          intro j
          rcases hcv j with h0 | h1
          · rw [hg, h0]
            simp
          · rw [hg, h1, hr0]
            simp
        have hsumle : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) ≤ 1 := by
          refine (Finset.sum_induction
            (fun j : Fin (m + 1) => c j * a ^ (2 ^ (j : ℕ))) (fun x : F => ν x ≤ 1)
            (fun x y hx hy => ν.map_add_le hx hy) (by simp) ?_)
          intro j
          simp only [Finset.mem_univ, true_implies]
          exact hle1 j
        have hlt1 : 1 < WithZero.exp (33 : ℤ) := exp_lt_exp.mpr (by norm_num)
        rw [hν] at hsumle
        exact (not_lt_of_ge hsumle) hlt1

end QEC.Coding.AlgebraicGeometry.ArtinSchreier
