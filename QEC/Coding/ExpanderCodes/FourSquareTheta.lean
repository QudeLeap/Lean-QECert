import QEC.Coding.ExpanderCodes.LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Theta-series encoding of four-square representations

This module expresses the finite four-square representation count as the
fourth coefficient convolution of the one-variable integer theta series.
It is the combinatorial bridge needed before proving Jacobi's theta identity.
-/

namespace QEC.Coding.TannerLiftedProduct

open Finset

/-- The finite set of integral square roots of `n`. -/
noncomputable def integerSquareRoots (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun z => z ^ 2 = n

theorem mem_integerSquareRoots_iff (n : ℕ) (z : ℤ) :
    z ∈ integerSquareRoots n ↔ z ^ 2 = n := by
  rw [integerSquareRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hz => ?_
  simp only [Finset.mem_Icc]
  have hn : (0 : ℤ) ≤ n := by positivity
  constructor
  · by_cases h : 0 ≤ z
    · omega
    · have hle : -z ≤ (-z) ^ 2 := by
        nlinarith [sq_nonneg (-z - 1)]
      nlinarith
  · by_cases h : z ≤ 0
    · omega
    · have hle : z ≤ z ^ 2 := by
        nlinarith [sq_nonneg (z - 1)]
      nlinarith

@[simp] theorem integerSquareRoots_zero :
    integerSquareRoots 0 = {0} := by
  ext z
  rw [mem_integerSquareRoots_iff]
  simp

/-- A positive integral square has exactly its positive and negative roots. -/
theorem integerSquareRoots_sq (m : ℕ) :
    integerSquareRoots (m ^ 2) = {(m : ℤ), -(m : ℤ)} := by
  ext z
  rw [mem_integerSquareRoots_iff]
  push_cast
  rw [sq_eq_sq_iff_eq_or_eq_neg]
  simp

@[simp] theorem card_integerSquareRoots_zero :
    (integerSquareRoots 0).card = 1 := by
  simp

/-- Consequently every positive square contributes coefficient two to the
integer theta series. -/
theorem card_integerSquareRoots_sq (m : ℕ) (hm : 0 < m) :
    (integerSquareRoots (m ^ 2)).card = 2 := by
  rw [integerSquareRoots_sq m]
  simp [hm.ne']

/-- Complete coefficient classification for the integer theta series. -/
theorem card_integerSquareRoots (n : ℕ) :
    (integerSquareRoots n).card =
      if n = 0 then 1 else if IsSquare n then 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · by_cases hs : IsSquare n
    · rw [isSquare_iff_exists_sq] at hs
      obtain ⟨m, rfl⟩ := hs
      have hm : 0 < m := by
        by_contra h
        push Not at h
        simp_all
      have hsq : IsSquare (m ^ 2) := by
        rw [isSquare_iff_exists_sq]
        exact ⟨m, rfl⟩
      rw [if_neg hn, if_pos hsq]
      exact card_integerSquareRoots_sq m hm
    · have hempty : integerSquareRoots n = ∅ := by
        ext z
        simp only [mem_integerSquareRoots_iff, Finset.notMem_empty, iff_false]
        intro hz
        apply hs
        rw [isSquare_iff_exists_sq]
        refine ⟨z.natAbs, ?_⟩
        rw [← Nat.cast_inj (R := ℤ), Nat.cast_pow, Int.natCast_natAbs,
          sq_abs, hz]
      simp [hn, hs, hempty]

/-- The formal integer theta series, with coefficient at `n` equal to the
number of integral solutions of `z² = n`. -/
noncomputable def integerThetaSeries : PowerSeries ℕ :=
  PowerSeries.mk fun n => (integerSquareRoots n).card

@[simp] theorem coeff_integerThetaSeries (n : ℕ) :
    PowerSeries.coeff n integerThetaSeries = (integerSquareRoots n).card := by
  simp [integerThetaSeries]

@[simp] theorem coeff_integerThetaSeries_zero :
    PowerSeries.coeff 0 integerThetaSeries = 1 := by
  simp

theorem coeff_integerThetaSeries_sq (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff (m ^ 2) integerThetaSeries = 2 := by
  simp [card_integerSquareRoots_sq m hm]

/-- Coefficientwise normal form of the integer theta series. -/
theorem coeff_integerThetaSeries_eq_ite (n : ℕ) :
    PowerSeries.coeff n integerThetaSeries =
      if n = 0 then 1 else if IsSquare n then 2 else 0 := by
  rw [coeff_integerThetaSeries, card_integerSquareRoots]

/-- Coefficient witnesses for the fourth power of `integerThetaSeries`:
choose four exponents summing to `n`, then one signed square root for each
exponent. -/
abbrev IntegerThetaFourWitness (n : ℕ) :=
  Σ l : {l : Fin 4 →₀ ℕ // l ∈ Finset.finsuppAntidiag Finset.univ n},
    (i : Fin 4) → {z : ℤ // z ∈ integerSquareRoots (l.1 i)}

/-- The fourth theta coefficient counts the explicit exponent/root
witnesses. -/
theorem coeff_integerThetaSeries_pow_four_eq_card (n : ℕ) :
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
      Fintype.card (IntegerThetaFourWitness n) := by
  rw [show integerThetaSeries ^ 4 =
      ∏ _i : Fin 4, integerThetaSeries by simp]
  rw [PowerSeries.coeff_prod]
  simp only [coeff_integerThetaSeries, Fintype.card_sigma,
    Fintype.card_pi, Fintype.card_coe]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro l hl
  simp

/-- View an integral quaternion as four coordinates. -/
def lpsQuaternionEquivFinFour : LPSQuaternion ≃ (Fin 4 → ℤ) where
  toFun t := ![t.a, t.b, t.c, t.d]
  invFun f := ⟨f 0, f 1, f 2, f 3⟩
  left_inv t := by cases t; rfl
  right_inv f := by funext i; fin_cases i <;> rfl

@[simp] theorem lpsQuaternionEquivFinFour_norm (t : LPSQuaternion) :
    ∑ i, (lpsQuaternionEquivFinFour t i) ^ 2 = t.norm := by
  simp [lpsQuaternionEquivFinFour, LPSQuaternion.norm, Fin.sum_univ_four]

/-- Send a theta coefficient witness to its ordered signed quaternion. -/
noncomputable def integerThetaFourWitnessToFullShell
    {n : ℕ} (hn : 0 < n) :
    IntegerThetaFourWitness n → {t // t ∈ lpsQuaternionFullShell n} :=
  fun w => ⟨lpsQuaternionEquivFinFour.symm (fun i => (w.2 i).1),
    (mem_lpsQuaternionFullShell_iff hn _).mpr <| by
      have hs := (Finset.mem_finsuppAntidiag.mp w.1.2).1
      have hi (i : Fin 4) : ((w.2 i).1 : ℤ) ^ 2 = w.1.1 i :=
        (mem_integerSquareRoots_iff _ _).mp (w.2 i).2
      rw [← lpsQuaternionEquivFinFour_norm]
      simp only [Equiv.apply_symm_apply]
      calc
        ∑ i, (w.2 i).1 ^ 2 = ∑ i, (w.1.1 i : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hi i
        _ = n := by
          exact_mod_cast hs⟩

/-- The combinatorial witnesses for the fourth theta coefficient are exactly
the ordered signed integral quaternions of norm `n`. -/
noncomputable def integerThetaFourWitnessEquivFullShell
    {n : ℕ} (hn : 0 < n) :
    IntegerThetaFourWitness n ≃ {t // t ∈ lpsQuaternionFullShell n} :=
  Equiv.ofBijective (integerThetaFourWitnessToFullShell hn) <| by
    constructor
    · rintro ⟨l, z⟩ ⟨l', z'⟩ h
      have hz : (fun i => (z i).1) = fun i => (z' i).1 := by
        apply lpsQuaternionEquivFinFour.symm.injective
        exact congrArg Subtype.val h
      have hl : l = l' := by
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        have hzi := congrFun hz i
        have hi := (mem_integerSquareRoots_iff _ _).mp (z i).2
        have hi' := (mem_integerSquareRoots_iff _ _).mp (z' i).2
        exact_mod_cast hi.symm.trans ((congrArg (fun x : ℤ => x ^ 2) hzi).trans hi')
      subst l'
      congr
      funext i
      apply Subtype.ext
      exact congrFun hz i
    · intro t
      let f : Fin 4 → ℤ := lpsQuaternionEquivFinFour t.1
      let l : Fin 4 →₀ ℕ :=
        Finsupp.equivFunOnFinite.symm fun i => (f i).natAbs ^ 2
      have hNorm : t.1.norm = n :=
        (mem_lpsQuaternionFullShell_iff hn t.1).mp t.2
      have hSum : ∑ i, l i = n := by
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        simp only [l, Finsupp.coe_equivFunOnFinite_symm]
        simpa [f, lpsQuaternionEquivFinFour_norm] using hNorm
      have hl : l ∈ Finset.finsuppAntidiag Finset.univ n := by
        rw [Finset.mem_finsuppAntidiag]
        exact ⟨by simpa using hSum, by simp⟩
      let z : (i : Fin 4) → {x : ℤ // x ∈ integerSquareRoots (l i)} :=
        fun i => ⟨f i, (mem_integerSquareRoots_iff _ _).mpr <| by
          simp [l]⟩
      refine ⟨⟨⟨l, hl⟩, z⟩, ?_⟩
      apply Subtype.ext
      exact lpsQuaternionEquivFinFour.symm_apply_apply t.1

/-- The full ordered signed representation count is exactly the coefficient
of the fourth power of the integer theta series. -/
theorem coeff_integerThetaSeries_pow_four_eq_fullShell_card
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
      (lpsQuaternionFullShell n).card := by
  calc
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
        Fintype.card (IntegerThetaFourWitness n) :=
      coeff_integerThetaSeries_pow_four_eq_card n
    _ = Fintype.card {t // t ∈ lpsQuaternionFullShell n} :=
      Fintype.card_congr (integerThetaFourWitnessEquivFullShell hn)
    _ = (lpsQuaternionFullShell n).card := Fintype.card_coe _

/-- The divisor-sum series appearing on the right-hand side of Jacobi's
four-square identity.  The constant coefficient is separated because
`Nat.divisors 0` is empty. -/
noncomputable def jacobiFourSquareSeries : PowerSeries ℕ :=
  PowerSeries.mk fun n =>
    if n = 0 then 1
    else 8 * ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

@[simp] theorem coeff_jacobiFourSquareSeries_zero :
    PowerSeries.coeff 0 jacobiFourSquareSeries = 1 := by
  simp [jacobiFourSquareSeries]

/-- At a prime congruent to one modulo four, Jacobi's divisor sum has only
the divisors `1` and `p`, and hence equals `8 (p + 1)`. -/
theorem coeff_jacobiFourSquareSeries_prime
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    PowerSeries.coeff p jacobiFourSquareSeries = 8 * (p + 1) := by
  have h4p : ¬ 4 ∣ p := by
    intro h
    have hzero := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  simp only [jacobiFourSquareSeries, PowerSeries.coeff_mk,
    if_neg hp.ne_zero, hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm)]
  simp [h4p, Nat.add_comm]

/-- Jacobi's formal theta identity implies the exact prime full-shell count.
This pins the remaining arithmetic theorem to one standard power-series
identity, with the combinatorial and prime-specialization steps discharged. -/
theorem card_lpsQuaternionFullShell_eq_prime_of_theta_identity
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hTheta : integerThetaSeries ^ 4 = jacobiFourSquareSeries) :
    (lpsQuaternionFullShell p).card = 8 * (p + 1) := by
  rw [← coeff_integerThetaSeries_pow_four_eq_fullShell_card hp.pos]
  rw [hTheta]
  exact coeff_jacobiFourSquareSeries_prime hp hp4

/-- The same standard theta identity supplies the exact normalized LPS
generator count. -/
theorem card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hTheta : integerThetaSeries ^ 4 = jacobiFourSquareSeries) :
    (lpsQuaternionShell p).card = p + 1 :=
  card_lpsQuaternionShell_eq_prime_add_one_of_full_count hp.pos hp4
    (card_lpsQuaternionFullShell_eq_prime_of_theta_identity hp hp4 hTheta)

end QEC.Coding.TannerLiftedProduct
