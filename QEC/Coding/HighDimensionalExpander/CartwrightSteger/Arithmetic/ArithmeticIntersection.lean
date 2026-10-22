import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.Arithmetic
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The Cartwright--Steger arithmetic intersection at the building place

Inside `F_q((y))`, the intersection of
`F_q[y, 1/y, 1/(1+y)]` with `F_q[[y]]` is proved to be
`F_q[y, 1/(1+y)]`.  The proof derives denominator characterizations from
the actual localization maps and removes the possible `y`-factor using the
`y`-adic valuation and coprimality of normalized rational-function
numerators and denominators.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem mem_integralArithmetic_image_iff_denom_dvd
    (P : BasePrime) (x : FunctionField P) :
    (∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a = x) ↔
      ∃ n : ℕ, x.denom ∣
        (1 + Polynomial.X : PolynomialRing P) ^ n := by
  constructor
  · rintro ⟨a, rfl⟩
    have hone : (1 + Polynomial.X : PolynomialRing P) ≠ 0 := by
      intro h
      have := congrArg (Polynomial.eval (0 : BaseField P)) h
      simp at this
    obtain ⟨⟨p, s⟩, ha⟩ :=
      IsLocalization.surj
        (Submonoid.powers (1 + Polynomial.X : PolynomialRing P)) a
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, (RatFunc.denom_dvd
      (pow_ne_zero n hone)).mpr ?_⟩
    refine ⟨p, ?_⟩
    have hmap := congrArg (integralArithmeticToFunctionField P) ha
    simp only [map_mul, integralArithmeticToFunctionField_algebraMap] at hmap
    rw [← hn] at hmap
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero
      (pow_ne_zero n hone))).2
    simpa only using hmap
  · rintro ⟨n, hn⟩
    have hq : (1 + Polynomial.X : PolynomialRing P) ^ n ≠ 0 :=
      pow_ne_zero n (by
        intro h
        have := congrArg (Polynomial.eval (0 : BaseField P)) h
        simp at this)
    obtain ⟨p, hp⟩ := (RatFunc.denom_dvd hq).mp hn
    let s : Submonoid.powers
        (1 + Polynomial.X : PolynomialRing P) :=
      ⟨(1 + Polynomial.X) ^ n, ⟨n, rfl⟩⟩
    refine ⟨IsLocalization.mk' (IntegralArithmeticRing P) p s, ?_⟩
    let g : PolynomialRing P →+* FunctionField P :=
      algebraMap (PolynomialRing P) (FunctionField P)
    have hg : ∀ y : Submonoid.powers
        (1 + Polynomial.X : PolynomialRing P), IsUnit (g y) := by
      intro y
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      obtain ⟨k, hk⟩ := y.property
      rw [← hk]
      exact pow_ne_zero k (by
        intro h
        have := congrArg (Polynomial.eval (0 : BaseField P)) h
        simp at this)
    change IsLocalization.lift hg
        (IsLocalization.mk' (IntegralArithmeticRing P) p s) = x
    apply (IsLocalization.lift_mk'_spec hg p x s).2
    have hpMul := (eq_div_iff
      (RatFunc.algebraMap_ne_zero hq)).mp hp
    dsimp [g, s]
    simpa [mul_comm] using hpMul.symm

theorem mem_arithmetic_image_iff_denom_dvd
    (P : BasePrime) (x : FunctionField P) :
    (∃ a : ArithmeticRing P,
        arithmeticRingToFunctionField P a = x) ↔
      ∃ n : ℕ, x.denom ∣
        (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P) ^ n := by
  let q : PolynomialRing P := Polynomial.X * (1 + Polynomial.X)
  have hq0 : q ≠ 0 := mul_ne_zero Polynomial.X_ne_zero (by
    intro h
    have := congrArg (Polynomial.eval (0 : BaseField P)) h
    simp at this)
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨p, s⟩, ha⟩ :=
      IsLocalization.surj (Submonoid.powers q) a
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, (RatFunc.denom_dvd (pow_ne_zero n hq0)).mpr ?_⟩
    refine ⟨p, ?_⟩
    have hmap := congrArg (arithmeticRingToFunctionField P) ha
    simp only [map_mul, arithmeticRingToFunctionField_algebraMap] at hmap
    rw [← hn] at hmap
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero
      (pow_ne_zero n hq0))).2
    simpa only using hmap
  · rintro ⟨n, hn⟩
    have hqpow : q ^ n ≠ 0 := pow_ne_zero n hq0
    obtain ⟨p, hp⟩ := (RatFunc.denom_dvd hqpow).mp hn
    let s : Submonoid.powers q := ⟨q ^ n, ⟨n, rfl⟩⟩
    refine ⟨IsLocalization.mk' (ArithmeticRing P) p s, ?_⟩
    let g : PolynomialRing P →+* FunctionField P :=
      algebraMap (PolynomialRing P) (FunctionField P)
    have hg : ∀ y : Submonoid.powers q, IsUnit (g y) := by
      intro y
      rw [isUnit_iff_ne_zero]
      apply RatFunc.algebraMap_ne_zero
      obtain ⟨k, hk⟩ := y.property
      rw [← hk]
      exact pow_ne_zero k hq0
    change IsLocalization.lift hg
        (IsLocalization.mk' (ArithmeticRing P) p s) = x
    apply (IsLocalization.lift_mk'_spec hg p x s).2
    have hpMul := (eq_div_iff
      (RatFunc.algebraMap_ne_zero hqpow)).mp hp
    dsimp [g, s]
    simpa [mul_comm] using hpMul.symm

theorem not_X_dvd_denom_of_building_integral
    (P : BasePrime) (x : FunctionField P)
    (hlocal : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P x) :
    ¬ Polynomial.X ∣ x.denom := by
  have hxle : yAdicPlace P x ≤ 1 := by
    rw [RatFunc.valuation_eq_LaurentSeries_valuation]
    obtain ⟨f, hf⟩ := hlocal
    change (PowerSeries.idealX (BaseField P)).valuation
        (BuildingLocalField P) (functionFieldToBuildingLocalField P x) ≤ 1
    rw [← hf]
    change (PowerSeries.idealX (BaseField P)).valuation
        (BuildingLocalField P)
        (algebraMap (BuildingIntegerRing P) (BuildingLocalField P) f) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (PowerSeries.idealX (BaseField P)).intValuation_le_one f
  intro hden
  have hnum : ¬ Polynomial.X ∣ x.num := by
    intro hn
    exact Polynomial.not_isUnit_X
      (x.isCoprime_num_denom.isUnit_of_dvd' hn hden)
  let v := Polynomial.idealX (BaseField P)
  have hnumLe : v.intValuation x.num ≤ 1 :=
    v.intValuation_le_one x.num
  have hnumNotLt : ¬ v.intValuation x.num < 1 := by
    rw [v.intValuation_lt_one_iff_mem, Polynomial.idealX_span,
      Ideal.mem_span_singleton]
    exact hnum
  have hnumEq : v.intValuation x.num = 1 :=
    le_antisymm hnumLe (not_lt.mp hnumNotLt)
  have hdenLt : v.intValuation x.denom < 1 := by
    rw [v.intValuation_lt_one_iff_mem, Polynomial.idealX_span,
      Ideal.mem_span_singleton]
    exact hden
  have hdenPos : 0 < v.intValuation x.denom :=
    v.intValuation_zero_lt
      ⟨x.denom, mem_nonZeroDivisors_iff_ne_zero.mpr
        (RatFunc.denom_ne_zero x)⟩
  have hxgt : 1 < yAdicPlace P x := by
    rw [← x.num_div_denom]
    rw [map_div₀,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      hnumEq, one_div]
    exact (one_lt_inv₀ hdenPos).mpr hdenLt
  exact (not_lt_of_ge hxle) hxgt

theorem arithmetic_building_integer_intersection
    (P : BasePrime) (x : FunctionField P)
    (harithmetic : ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a = x)
    (hlocal : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P x) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a = x := by
  obtain ⟨n, hden⟩ :=
    (mem_arithmetic_image_iff_denom_dvd P x).mp harithmetic
  have hnot := not_X_dvd_denom_of_building_integral P x hlocal
  have hcop : IsCoprime x.denom (Polynomial.X ^ n) :=
    ((Polynomial.prime_X.coprime_iff_not_dvd.mpr hnot).symm).pow_right
  have hproduct : x.denom ∣
      Polynomial.X ^ n *
        (1 + Polynomial.X : PolynomialRing P) ^ n := by
    simpa only [mul_pow] using hden
  have htarget : x.denom ∣
      (1 + Polynomial.X : PolynomialRing P) ^ n :=
    hcop.dvd_of_dvd_mul_left hproduct
  exact (mem_integralArithmetic_image_iff_denom_dvd P x).mpr
    ⟨n, htarget⟩

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
