import QEC.Coding.ExpanderCodes.FourSquareTheta
import QEC.Coding.ExpanderCodes.LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Product expansion of the LPS trace theta series

The diagonal form in the LPS trace calculation has one unscaled coordinate
and three coordinates scaled by `2q`.  This module proves coefficientwise
that its theta series is the product of the four corresponding unary theta
series.  The statement is entirely combinatorial; modularity is a later
analytic layer.
-/

namespace QEC.Coding.TannerLiftedProduct

open Finset

/-- Integral solutions of `m²z²=n`, kept in an explicit finite box. -/
noncomputable def scaledIntegerSquareRoots (m n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun z =>
    ((m : ℤ) ^ 2) * z ^ 2 = n

theorem mem_scaledIntegerSquareRoots_iff
    {m : ℕ} (hm : 0 < m) (n : ℕ) (z : ℤ) :
    z ∈ scaledIntegerSquareRoots m n ↔
      ((m : ℤ) ^ 2) * z ^ 2 = n := by
  rw [scaledIntegerSquareRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hz => ?_
  simp only [Finset.mem_Icc]
  have hmOne : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hmSq : (1 : ℤ) ≤ (m : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℤ) - 1)]
  have hzSq : z ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg z]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (z + n)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (z - n)]

/-- Unary theta series for the scaled square `m²z²`. -/
noncomputable def scaledIntegerThetaSeries (m : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun n => (scaledIntegerSquareRoots m n).card

@[simp] theorem coeff_scaledIntegerThetaSeries (m n : ℕ) :
    PowerSeries.coeff n (scaledIntegerThetaSeries m) =
      (scaledIntegerSquareRoots m n).card := by
  simp [scaledIntegerThetaSeries]

theorem scaledIntegerSquareRoots_eq_of_dvd
    {m n : ℕ} (hm : 0 < m) (hdiv : m ^ 2 ∣ n) :
    scaledIntegerSquareRoots m n = integerSquareRoots (n / m ^ 2) := by
  ext z
  rw [mem_scaledIntegerSquareRoots_iff hm,
    mem_integerSquareRoots_iff]
  have hmSq : (m ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hm.ne'
  have hcast : (((m ^ 2 : ℕ) : ℤ)) = (m : ℤ) ^ 2 := by norm_num
  have hn : m ^ 2 * (n / m ^ 2) = n := Nat.mul_div_cancel' hdiv
  constructor
  · intro hz
    apply mul_left_cancel₀ (show (((m ^ 2 : ℕ) : ℤ)) ≠ 0 by
      exact_mod_cast hmSq)
    rw [hcast]
    calc
      (m : ℤ) ^ 2 * z ^ 2 = (n : ℤ) := hz
      _ = (((m ^ 2) * (n / m ^ 2) : ℕ) : ℤ) := by rw [hn]
      _ = ((m ^ 2 : ℕ) : ℤ) * ((n / m ^ 2 : ℕ) : ℤ) := by
        push_cast
        rfl
  · intro hz
    rw [← hcast]
    calc
      ((m ^ 2 : ℕ) : ℤ) * z ^ 2 =
          ((m ^ 2 : ℕ) : ℤ) * ((n / m ^ 2 : ℕ) : ℤ) := by
        rw [hz]
      _ = (((m ^ 2) * (n / m ^ 2) : ℕ) : ℤ) := by
        push_cast
        rfl
      _ = (n : ℤ) := by rw [hn]

theorem scaledIntegerSquareRoots_eq_empty_of_not_dvd
    {m n : ℕ} (hm : 0 < m) (hdiv : ¬ m ^ 2 ∣ n) :
    scaledIntegerSquareRoots m n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  apply hdiv
  refine ⟨z.natAbs ^ 2, ?_⟩
  rw [mem_scaledIntegerSquareRoots_iff hm] at hz
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast
  simpa [sq_abs] using hz.symm

/-- After extending coefficients to the integers, scaling the variable in
the unary theta series by `m` is formal substitution `X ↦ X^(m²)`. -/
theorem map_scaledIntegerThetaSeries_eq_subst
    {m : ℕ} (hm : 0 < m) :
    (scaledIntegerThetaSeries m).map (Nat.castRingHom ℤ) =
      PowerSeries.subst (PowerSeries.X ^ (m ^ 2))
        (integerThetaSeries.map (Nat.castRingHom ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_scaledIntegerThetaSeries,
    PowerSeries.coeff_subst_X_pow (pow_ne_zero 2 hm.ne')]
  by_cases hdiv : m ^ 2 ∣ n
  · rw [if_pos hdiv, scaledIntegerSquareRoots_eq_of_dvd hm hdiv,
      PowerSeries.coeff_map, coeff_integerThetaSeries]
    simp
  · rw [if_neg hdiv, scaledIntegerSquareRoots_eq_empty_of_not_dvd hm hdiv]
    simp

/-- The four unary root fibres for the diagonal trace form. -/
noncomputable def lpsTraceCoordinateRoots
    (q : ℕ) (i : Fin 4) (n : ℕ) : Finset ℤ :=
  if i = 0 then integerSquareRoots n
  else scaledIntegerSquareRoots (2 * q) n

/-- The unary theta series attached to one coordinate of the trace form. -/
noncomputable def lpsTraceCoordinateThetaSeries
    (q : ℕ) (i : Fin 4) : PowerSeries ℕ :=
  PowerSeries.mk fun n => (lpsTraceCoordinateRoots q i n).card

@[simp] theorem coeff_lpsTraceCoordinateThetaSeries
    (q : ℕ) (i : Fin 4) (n : ℕ) :
    PowerSeries.coeff n (lpsTraceCoordinateThetaSeries q i) =
      (lpsTraceCoordinateRoots q i n).card := by
  simp [lpsTraceCoordinateThetaSeries]

/-- The contribution of one coordinate to the diagonal trace form. -/
def lpsTraceCoordinateValue (q : ℕ) (i : Fin 4) (z : ℤ) : ℤ :=
  if i = 0 then z ^ 2 else ((2 * q : ℕ) : ℤ) ^ 2 * z ^ 2

theorem mem_lpsTraceCoordinateRoots_iff
    {q : ℕ} (hq : 0 < q) (i : Fin 4) (n : ℕ) (z : ℤ) :
    z ∈ lpsTraceCoordinateRoots q i n ↔
      lpsTraceCoordinateValue q i z = n := by
  by_cases hi : i = 0
  · subst i
    simp [lpsTraceCoordinateRoots, lpsTraceCoordinateValue,
      mem_integerSquareRoots_iff]
  · simp [lpsTraceCoordinateRoots, lpsTraceCoordinateValue, hi,
      mem_scaledIntegerSquareRoots_iff (by omega : 0 < 2 * q)]

@[simp] theorem sum_lpsTraceCoordinateValue
    (q : ℕ) (t : LPSQuaternion) :
    ∑ i : Fin 4,
        lpsTraceCoordinateValue q i (lpsQuaternionEquivFinFour t i) =
      lpsTraceQuadraticForm q t := by
  simp [lpsTraceCoordinateValue, lpsQuaternionEquivFinFour,
    lpsTraceQuadraticForm, Fin.sum_univ_four]

/-- Coefficient witnesses for the product of the four unary trace theta
series. -/
abbrev LPSTraceThetaWitness (q n : ℕ) :=
  Σ l : {l : Fin 4 →₀ ℕ // l ∈ Finset.finsuppAntidiag Finset.univ n},
    (i : Fin 4) → {z : ℤ // z ∈ lpsTraceCoordinateRoots q i (l.1 i)}

/-- The coefficient of the unary-product presentation counts its explicit
exponent/root witnesses. -/
theorem coeff_lpsTraceCoordinateThetaSeries_prod_eq_card
    (q n : ℕ) :
    PowerSeries.coeff n
        (∏ i : Fin 4, lpsTraceCoordinateThetaSeries q i) =
      Fintype.card (LPSTraceThetaWitness q n) := by
  rw [PowerSeries.coeff_prod]
  simp only [coeff_lpsTraceCoordinateThetaSeries, Fintype.card_sigma,
    Fintype.card_pi, Fintype.card_coe]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro l hl
  simp

/-- Send a unary-product coefficient witness to the represented integral
quaternion. -/
noncomputable def lpsTraceThetaWitnessToShell
    {q n : ℕ} (hq : 0 < q) :
    LPSTraceThetaWitness q n → {t // t ∈ lpsTraceQuadraticShell q n} :=
  fun w => ⟨lpsQuaternionEquivFinFour.symm (fun i => (w.2 i).1),
    (mem_lpsTraceQuadraticShell_iff hq _).mpr <| by
      have hs := (Finset.mem_finsuppAntidiag.mp w.1.2).1
      have hi (i : Fin 4) :
          lpsTraceCoordinateValue q i (w.2 i).1 = w.1.1 i :=
        (mem_lpsTraceCoordinateRoots_iff hq i _ _).mp (w.2 i).2
      rw [← sum_lpsTraceCoordinateValue]
      simp only [Equiv.apply_symm_apply]
      calc
        ∑ i, lpsTraceCoordinateValue q i (w.2 i).1 =
            ∑ i, (w.1.1 i : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hi i
        _ = n := by exact_mod_cast hs⟩

/-- Unary-product witnesses are exactly the representations of `n` by the
LPS trace quadratic form. -/
noncomputable def lpsTraceThetaWitnessEquivShell
    {q n : ℕ} (hq : 0 < q) :
    LPSTraceThetaWitness q n ≃ {t // t ∈ lpsTraceQuadraticShell q n} :=
  Equiv.ofBijective (lpsTraceThetaWitnessToShell hq) <| by
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
        have hi := (mem_lpsTraceCoordinateRoots_iff hq i _ _).mp (z i).2
        have hi' := (mem_lpsTraceCoordinateRoots_iff hq i _ _).mp (z' i).2
        exact_mod_cast hi.symm.trans
          ((congrArg (lpsTraceCoordinateValue q i) hzi).trans hi')
      subst l'
      congr
      funext i
      apply Subtype.ext
      exact congrFun hz i
    · intro t
      let f : Fin 4 → ℤ := lpsQuaternionEquivFinFour t.1
      let l : Fin 4 →₀ ℕ :=
        Finsupp.equivFunOnFinite.symm fun i =>
          (lpsTraceCoordinateValue q i (f i)).natAbs
      have hForm : lpsTraceQuadraticForm q t.1 = n :=
        (mem_lpsTraceQuadraticShell_iff hq t.1).mp t.2
      have hNonneg (i : Fin 4) :
          0 ≤ lpsTraceCoordinateValue q i (f i) := by
        simp [lpsTraceCoordinateValue]
        positivity
      have hSum : ∑ i, l i = n := by
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        simp only [l, Finsupp.coe_equivFunOnFinite_symm,
          Int.natCast_natAbs, abs_of_nonneg (hNonneg _)]
        simpa [f, sum_lpsTraceCoordinateValue] using hForm
      have hl : l ∈ Finset.finsuppAntidiag Finset.univ n := by
        rw [Finset.mem_finsuppAntidiag]
        exact ⟨by simpa using hSum, by simp⟩
      let z : (i : Fin 4) →
          {x : ℤ // x ∈ lpsTraceCoordinateRoots q i (l i)} :=
        fun i => ⟨f i, (mem_lpsTraceCoordinateRoots_iff hq i _ _).mpr <| by
          change lpsTraceCoordinateValue q i (f i) =
            ((lpsTraceCoordinateValue q i (f i)).natAbs : ℤ)
          rw [Int.natCast_natAbs, abs_of_nonneg (hNonneg i)]⟩
      refine ⟨⟨⟨l, hl⟩, z⟩, ?_⟩
      apply Subtype.ext
      exact lpsQuaternionEquivFinFour.symm_apply_apply t.1

/-- The LPS trace theta series is coefficientwise the product of its four
unary diagonal factors. -/
theorem lpsTraceThetaSeries_eq_coordinateProduct
    {q : ℕ} (hq : 0 < q) :
    lpsTraceThetaSeries q =
      ∏ i : Fin 4, lpsTraceCoordinateThetaSeries q i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_lpsTraceThetaSeries,
    coeff_lpsTraceCoordinateThetaSeries_prod_eq_card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (lpsTraceThetaWitnessEquivShell hq) |>.symm

/-- Concretely, the trace theta series has one ordinary unary theta factor
and three factors scaled by `2q`. -/
theorem lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three
    {q : ℕ} (hq : 0 < q) :
    lpsTraceThetaSeries q =
      integerThetaSeries * scaledIntegerThetaSeries (2 * q) ^ 3 := by
  rw [lpsTraceThetaSeries_eq_coordinateProduct hq]
  simp [lpsTraceCoordinateThetaSeries, lpsTraceCoordinateRoots,
    integerThetaSeries, scaledIntegerThetaSeries, Fin.prod_univ_four]
  ring

/-- Integral-coefficient substitution form of the diagonal factorization.
This is the standard theta-product expression used to establish modularity
of the trace series. -/
theorem map_lpsTraceThetaSeries_eq_integerTheta_mul_subst_pow_three
    {q : ℕ} (hq : 0 < q) :
    (lpsTraceThetaSeries q).map (Nat.castRingHom ℤ) =
      integerThetaSeries.map (Nat.castRingHom ℤ) *
        (PowerSeries.subst
          (PowerSeries.X ^ ((2 * q) ^ 2))
          (integerThetaSeries.map (Nat.castRingHom ℤ))) ^ 3 := by
  rw [lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three hq,
    map_mul, map_pow,
    map_scaledIntegerThetaSeries_eq_subst (by omega : 0 < 2 * q)]

end QEC.Coding.TannerLiftedProduct
