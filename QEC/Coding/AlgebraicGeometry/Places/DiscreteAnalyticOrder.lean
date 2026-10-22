import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Discrete analytic order gaps

A DVR unit has order zero. Fraction-field factorization makes all finite
orders integer multiples of the positive uniformizer order. This proves
the derivative-shift no-pole test without assuming uniformizer order one.
-/

namespace QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

/-- A unit of the valuation ring has additive order zero. -/
lemma valuationUnit_order (u : Vˣ) : v ((u : V) : K) = 0 := by
  exact (Valuation.valuationSubring.integers (AddValuation.toValuation v)).valuation_unit u

/-- An irreducible valuation-ring element has strictly positive additive order. -/
lemma uniformizer_order_positive (π : V) (hπ : Irreducible π) :
    0 < v (π : K) := by
  exact (Valuation.valuationSubring.integers (AddValuation.toValuation v)).valuation_irreducible_lt_one hπ

/-- A genuine DVR uniformizer has finite positive integer analytic order. -/
lemma exists_uniformizer_order [IsDiscreteValuationRing V] :
    ∃ (π : V) (m : ℤ), Irreducible π ∧ 0 < m ∧ v (π : K) = (m : WithTop ℤ) := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hne : v (π : K) ≠ ⊤ := v.ne_top_iff.mpr (by
    intro h
    exact hπ.ne_zero (Subtype.ext h))
  lift v (π : K) to ℤ using hne with m hm
  refine ⟨π,m,hπ,?_,hm.symm⟩
  have hp := uniformizer_order_positive v π hπ
  rw [← hm] at hp
  exact_mod_cast hp

/-- The order of a natural power is the exponent times its finite order. -/
lemma valuation_pow_finite {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℕ) :
    v (f ^ n) = ((n : ℤ) * m : ℤ) := by
  rw [v.map_pow,hf,← WithTop.coe_nsmul,nsmul_eq_mul]

/-- The same order formula holds for every integer power in the fraction field. -/
lemma valuation_zpow_finite {f : K} {m : ℤ} (hf : v f = (m : WithTop ℤ)) (n : ℤ) :
    v (f ^ n) = (n * m : ℤ) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using valuation_pow_finite v hf n
  | negSucc n =>
      rw [zpow_negSucc,v.map_inv,valuation_pow_finite v hf]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
      congr 1
      simp only [Int.negSucc_eq,Int.natCast_add,Int.natCast_one]
      ring

/-- DVR factorization makes every nonzero field order an integer multiple of uniformizer order. -/
lemma valuation_eq_multiple_uniformizer [IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π) {m : ℤ} (hm : v (π : K) = (m : WithTop ℤ))
    {f : K} (hf : f ≠ 0) : ∃ n : ℤ, v f = (n * m : ℤ) := by
  obtain ⟨n,u,he⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hf
  have he' : f = (u : V).val * (π.val ^ n) := by
    simpa only [Units.smul_def,Algebra.smul_def,ValuationSubring.algebraMap_apply] using he
  refine ⟨n,?_⟩
  rw [he',v.map_mul,valuationUnit_order v u,zero_add]
  exact valuation_zpow_finite v hm n

/-- The discrete order gap detects nonnegativity even after adding the derivative shift. -/
lemma discrete_derivative_bound {n m : ℤ} (hm : 0 < m) :
    0 ≤ n * m + (m - 1) ↔ 0 ≤ n * m := by
  constructor
  · intro h
    by_contra hn
    have hn' : n ≤ -1 := by
      by_contra hnn
      have h0 : 0 ≤ n := by omega
      exact hn (mul_nonneg h0 hm.le)
    have hp : n * m ≤ -m := by nlinarith
    omega
  · intro h
    have h1 : 1 ≤ m := by omega
    omega

/-- The derivative shift by the positive uniformizer order preserves the field no-pole criterion. -/
lemma valuation_uniformizer_derivative_shift [IsDiscreteValuationRing V]
    (π : V) (hπ : Irreducible π) {m : ℤ}
    (hpos : 0 < m) (hm : v (π : K) = (m : WithTop ℤ)) {f : K} (hf : f ≠ 0) :
    0 ≤ v f + ((m - 1 : ℤ) : WithTop ℤ) ↔ 0 ≤ v f := by
  obtain ⟨n,hn⟩ := valuation_eq_multiple_uniformizer v π hπ hm hf
  rw [hn,← WithTop.coe_add]
  exact_mod_cast discrete_derivative_bound (n := n) hpos

end
end QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
