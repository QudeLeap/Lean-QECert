import QEC.Coding.ExpanderCodes.JacobiCubeReindex
import QEC.Coding.ExpanderCodes.JacobiGeneralCore.FPSAlgebra
import Mathlib

/-!
# Jacobi's cube-product specialization

This module specializes the general formal-power-series Jacobi triple
product by applying the Euler derivation in the Laurent variable at `-1`.
The product side becomes the cube of Euler's product, while the bilateral
series becomes Jacobi's signed triangular series.
-/

namespace QEC.Coding.TannerLiftedProduct

open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

namespace JacobiCubeProduct

open JacobiGeneralCore.FormalPowerSeries

set_option linter.style.haveILetI false

abbrev LaurentQ := LaurentPolynomial ℚ
abbrev Bivariate := PowerSeries LaurentQ

/-- Evaluate the Laurent variable at `-1`. -/
noncomputable def evalNegOne : LaurentQ →+* ℚ :=
  LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1)

/-- The Euler derivation `z d/dz`, evaluated at `z = -1`. -/
noncomputable def signedEulerCoeff : LaurentQ →+ ℚ where
  toFun f := f.coeff.sum fun m c => (m : ℚ) * c * ((-1 : ℚ) ^ m)
  map_zero' := Finsupp.sum_zero_index
  map_add' f g := Finsupp.sum_add_index'
    (fun _ => by simp) (fun _ a b => by ring)

/-- Apply the signed Euler derivation coefficientwise. -/
noncomputable def signedEuler (F : Bivariate) : PowerSeries ℚ :=
  PowerSeries.mk fun n => signedEulerCoeff (PowerSeries.coeff n F)

/-- Evaluate the Laurent variable coefficientwise at `-1`. -/
noncomputable def evalNegOneSeries : Bivariate →+* PowerSeries ℚ :=
  PowerSeries.map evalNegOne

@[simp] theorem coeff_signedEuler (n : ℕ) (F : Bivariate) :
    PowerSeries.coeff n (signedEuler F) =
      signedEulerCoeff (PowerSeries.coeff n F) := by
  simp [signedEuler]

@[simp] theorem coeff_evalNegOneSeries (n : ℕ) (F : Bivariate) :
    PowerSeries.coeff n (evalNegOneSeries F) =
      evalNegOne (PowerSeries.coeff n F) := by
  simp [evalNegOneSeries]

@[simp] theorem evalNegOne_C_mul_T (c : ℚ) (m : ℤ) :
    evalNegOne (LaurentPolynomial.C c * LaurentPolynomial.T m) =
      c * ((-1 : ℚ) ^ m) := by
  simp [evalNegOne]

@[simp] theorem signedEulerCoeff_C_mul_T (c : ℚ) (m : ℤ) :
    signedEulerCoeff (LaurentPolynomial.C c * LaurentPolynomial.T m) =
      (m : ℚ) * c * ((-1 : ℚ) ^ m) := by
  show (LaurentPolynomial.C c * LaurentPolynomial.T m).coeff.sum
      (fun j d => (j : ℚ) * d * ((-1 : ℚ) ^ j)) = _
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single,
    Finsupp.sum_single_index (by simp)]

@[simp] theorem signedEulerCoeff_C (c : ℚ) :
    signedEulerCoeff (LaurentPolynomial.C c) = 0 := by
  simpa using signedEulerCoeff_C_mul_T c 0

@[simp] theorem signedEulerCoeff_T (m : ℤ) :
    signedEulerCoeff (LaurentPolynomial.T m) =
      (m : ℚ) * ((-1 : ℚ) ^ m) := by
  simpa using signedEulerCoeff_C_mul_T 1 m

@[simp] theorem signedEulerCoeff_one : signedEulerCoeff 1 = 0 := by
  simpa using signedEulerCoeff_C 1

@[simp] theorem evalNegOne_C (c : ℚ) :
    evalNegOne (LaurentPolynomial.C c) = c := by
  simp [evalNegOne]

@[simp] theorem evalNegOne_T (m : ℤ) :
    evalNegOne (LaurentPolynomial.T m) = ((-1 : ℚ) ^ m) := by
  simpa using evalNegOne_C_mul_T 1 m

theorem signedEulerCoeff_mul (f g : LaurentQ) :
    signedEulerCoeff (f * g) =
      evalNegOne f * signedEulerCoeff g +
        signedEulerCoeff f * evalNegOne g := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [add_mul, map_add, hp, hq]
      ring
  | C_mul_T m a =>
      induction g using LaurentPolynomial.induction_on' with
      | add p q hp hq =>
          simp only [mul_add, map_add, hp, hq]
          ring
      | C_mul_T k b =>
          rw [show LaurentPolynomial.C a * LaurentPolynomial.T m *
                (LaurentPolynomial.C b * LaurentPolynomial.T k) =
              LaurentPolynomial.C (a * b) *
                LaurentPolynomial.T (m + k) by
            rw [map_mul, LaurentPolynomial.T_add]
            ring]
          simp only [signedEulerCoeff_C_mul_T, evalNegOne_C_mul_T]
          rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
          push_cast
          ring

theorem signedEuler_mul (F G : Bivariate) :
    signedEuler (F * G) =
      evalNegOneSeries F * signedEuler G +
        signedEuler F * evalNegOneSeries G := by
  ext n
  simp only [signedEuler, PowerSeries.coeff_mk, evalNegOneSeries,
    PowerSeries.coeff_map, map_add, PowerSeries.coeff_mul, map_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [signedEulerCoeff_mul]

theorem signedEuler_map_C (g : PowerSeries ℚ) :
    signedEuler (PowerSeries.map (LaurentPolynomial.C (R := ℚ)) g) = 0 := by
  ext n
  simp [signedEuler]

/-- Euler's product over the positive powers of `X`. -/
noncomputable def eulerProduct : PowerSeries ℚ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

theorem continuous_evalNegOneSeries :
    letI : TopologicalSpace LaurentQ := ⊥
    Continuous evalNegOneSeries := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro F
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  change Filter.Tendsto
    (fun G : Bivariate => evalNegOne (PowerSeries.coeff n G))
    (nhds F)
    (nhds (evalNegOne (PowerSeries.coeff n F)))
  exact (continuous_of_discreteTopology.comp
    (PowerSeries.WithPiTopology.continuous_coeff LaurentQ n)).continuousAt

/-- Evaluation at `-1` commutes with the convergent q-Pochhammer product. -/
theorem evalNegOneSeries_qPochhammerInf (a : Bivariate) :
    letI : TopologicalSpace LaurentQ := ⊥
    evalNegOneSeries (qPochhammerInf a) =
      ∏' n : ℕ,
        ((1 : PowerSeries ℚ) - evalNegOneSeries a * PowerSeries.X ^ n) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [qPochhammerInf]
  rw [(multipliable_one_sub_mul_pow a).map_tprod
    evalNegOneSeries continuous_evalNegOneSeries]
  simp only [map_sub, map_one, map_mul, map_pow,
    evalNegOneSeries, PowerSeries.map_X]

@[simp] theorem evalNegOneSeries_X :
    evalNegOneSeries (PowerSeries.X : Bivariate) = PowerSeries.X := by
  simp [evalNegOneSeries]

@[simp] theorem evalNegOneSeries_laurentZ :
    evalNegOneSeries laurentZ = -1 := by
  ext n
  cases n <;> simp [evalNegOneSeries, evalNegOne]

@[simp] theorem evalNegOneSeries_laurentZInv :
    evalNegOneSeries laurentZInv = -1 := by
  ext n
  cases n <;> simp [evalNegOneSeries, evalNegOne]

@[simp] theorem signedEuler_one_add_laurentZ :
    signedEuler (1 + laurentZ) = -1 := by
  ext n
  cases n <;> simp [signedEuler]

@[simp] theorem evalNegOneSeries_one_add_laurentZ :
    evalNegOneSeries (1 + laurentZ) = 0 := by
  rw [map_add, map_one, evalNegOneSeries_laurentZ]
  ring

theorem signedEuler_qPochhammerInf_X :
    signedEuler (qPochhammerInf (PowerSeries.X : Bivariate)) = 0 := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  ext d
  rw [coeff_signedEuler, coeff_qPochhammerInf]
  have hfinite :
      qPochhammer (PowerSeries.X : Bivariate) (d + 1) =
        PowerSeries.map (LaurentPolynomial.C (R := ℚ))
          (qPochhammer (PowerSeries.X : PowerSeries ℚ) (d + 1)) := by
    simp [qPochhammer]
  rw [hfinite, PowerSeries.coeff_map]
  simp

@[simp] theorem evalNegOneSeries_qPochhammerInf_X :
    evalNegOneSeries (qPochhammerInf (PowerSeries.X : Bivariate)) =
      eulerProduct := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [evalNegOneSeries_qPochhammerInf]
  rw [eulerProduct]
  apply tprod_congr
  intro n
  rw [evalNegOneSeries_X, pow_succ']

@[simp] theorem evalNegOneSeries_qPochhammerInf_neg_X_mul_laurentZInv :
    evalNegOneSeries (qPochhammerInf
        (-(PowerSeries.X : Bivariate) * laurentZInv)) =
      eulerProduct := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [evalNegOneSeries_qPochhammerInf]
  rw [eulerProduct]
  apply tprod_congr
  intro n
  simp only [map_neg, map_mul, evalNegOneSeries_X,
    evalNegOneSeries_laurentZInv, mul_neg, mul_one, neg_neg]
  rw [pow_succ']

theorem signedEuler_qPochhammerInf_neg_laurentZ :
    signedEuler (qPochhammerInf (-laurentZ)) =
      -eulerProduct := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [qPochhammerInf_eq_one_sub_mul]
  have hfactor : (1 : Bivariate) - -laurentZ = 1 + laurentZ := by ring
  rw [hfactor, signedEuler_mul]
  rw [signedEuler_one_add_laurentZ,
    evalNegOneSeries_one_add_laurentZ]
  have htail :
      evalNegOneSeries (qPochhammerInf (-laurentZ * PowerSeries.X)) =
        eulerProduct := by
    rw [evalNegOneSeries_qPochhammerInf]
    rw [eulerProduct]
    apply tprod_congr
    intro n
    simp only [map_mul, map_neg, evalNegOneSeries_laurentZ,
      evalNegOneSeries_X, neg_neg, one_mul]
    rw [pow_succ']
  rw [htail]
  ring

@[simp] theorem evalNegOneSeries_qPochhammerInf_neg_laurentZ :
    evalNegOneSeries (qPochhammerInf (-laurentZ)) = 0 := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [qPochhammerInf_eq_one_sub_mul]
  have hfactor : (1 : Bivariate) - -laurentZ = 1 + laurentZ := by ring
  rw [hfactor, map_mul, evalNegOneSeries_one_add_laurentZ, zero_mul]

/-- The Laurent Euler derivation turns the JTP product side into minus
the cube of Euler's product. -/
theorem signedEuler_jacobiProd :
    signedEuler jacobiProd = -(eulerProduct ^ 3) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [jacobiProd, qPochhammerInfX, qPochhammerInfNegZ,
    qPochhammerInfNegXMulZInv, signedEuler_mul, signedEuler_mul,
    map_mul]
  rw [evalNegOneSeries_qPochhammerInf_X,
    signedEuler_qPochhammerInf_X,
    evalNegOneSeries_qPochhammerInf_neg_laurentZ,
    signedEuler_qPochhammerInf_neg_laurentZ,
    evalNegOneSeries_qPochhammerInf_neg_X_mul_laurentZInv]
  ring

theorem neg_one_zpow_eq_jacobiParitySign (z : ℤ) :
    ((-1 : ℚ) ^ z) = jacobiParitySign z := by
  rw [neg_one_zpow_eq_ite]
  rfl

/-- A single term of the bilateral signed triangular series. -/
noncomputable def signedTriangularTerm (z : ℤ) : PowerSeries ℚ :=
  PowerSeries.C
      (jacobiParitySign z * (2 * (z : ℚ) + 1)) *
    PowerSeries.X ^ jacobiHalfTriangularDegree z

@[simp] theorem coeff_signedTriangularTerm (n : ℕ) (z : ℤ) :
    PowerSeries.coeff n (signedTriangularTerm z) =
      if jacobiHalfTriangularDegree z = n then
        jacobiParitySign z * (2 * (z : ℚ) + 1)
      else 0 := by
  rw [signedTriangularTerm, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  split_ifs <;> simp_all

theorem summable_signedTriangularTerm : Summable signedTriangularTerm := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  refine (integerTriangularRoots (2 * n)).finite_toSet.subset ?_
  intro z hz
  simp only [Function.mem_support, coeff_signedTriangularTerm] at hz
  by_contra hmem
  have hdegree : jacobiHalfTriangularDegree z ≠ n := by
    intro h
    apply hmem
    simpa [h] using mem_integerTriangularRoots_two_mul_degree z
  simp [hdegree] at hz

/-- The coefficient-fibre definition of the signed cube series is the
normalized bilateral sum. -/
theorem jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm :
    jacobiSignedCubeSeries =
      PowerSeries.C (1 / 2 : ℚ) *
        ∑' z : ℤ, signedTriangularTerm z := by
  ext n
  rw [coeff_jacobiSignedCubeSeries, PowerSeries.coeff_C_mul]
  rw [summable_signedTriangularTerm.map_tsum
    (PowerSeries.coeff n)
    (PowerSeries.WithPiTopology.continuous_coeff ℚ n)]
  rw [tsum_eq_sum (s := integerTriangularRoots (2 * n)) (fun z hz => by
    rw [coeff_signedTriangularTerm, if_neg]
    intro hdegree
    apply hz
    simpa [hdegree] using mem_integerTriangularRoots_two_mul_degree z)]
  congr 1
  change
    (∑ z ∈ (integerTriangularRoots (2 * n)).attach,
        jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1)) =
      ∑ z ∈ integerTriangularRoots (2 * n),
        PowerSeries.coeff n (signedTriangularTerm z)
  calc
    _ = ∑ z ∈ integerTriangularRoots (2 * n),
        jacobiParitySign z * (2 * (z : ℚ) + 1) :=
      Finset.sum_attach (integerTriangularRoots (2 * n))
        (fun z : ℤ => jacobiParitySign z * (2 * (z : ℚ) + 1))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [coeff_signedTriangularTerm,
        if_pos (jacobiHalfTriangularDegree_eq_of_mem hz)]

theorem jacobiHalfTriangularDegree_neg_sub_one (z : ℤ) :
    jacobiHalfTriangularDegree (-z - 1) =
      jacobiHalfTriangularDegree z := by
  rw [← Nat.cast_inj (R := ℤ)]
  have h₁ := two_mul_jacobiHalfTriangularDegree (-z - 1)
  have h₂ := two_mul_jacobiHalfTriangularDegree z
  nlinarith

theorem signedTriangularWeight_neg_sub_one (z : ℤ) :
    jacobiParitySign (-z - 1) * (2 * ((-z - 1 : ℤ) : ℚ) + 1) =
      jacobiParitySign z * (2 * (z : ℚ) + 1) := by
  rw [← neg_one_zpow_eq_jacobiParitySign,
    ← neg_one_zpow_eq_jacobiParitySign]
  have hsign : ((-1 : ℚ) ^ (-z - 1)) = -((-1 : ℚ) ^ z) := by
    rw [show -z - 1 = -z + (-1 : ℤ) by ring,
      zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_neg]
    norm_num
    rw [neg_one_zpow_eq_ite]
    split <;> norm_num
  rw [hsign]
  push_cast
  ring

theorem signedTriangularTerm_neg_sub_one (z : ℤ) :
    signedTriangularTerm (-z - 1) = signedTriangularTerm z := by
  rw [signedTriangularTerm, signedTriangularTerm,
    jacobiHalfTriangularDegree_neg_sub_one,
    signedTriangularWeight_neg_sub_one]

/-- Split all integers into the nonnegative chart and its reflected
negative chart. -/
def triangularPairEquiv : ℕ ⊕ ℕ ≃ ℤ where
  toFun s := match s with
    | Sum.inl n => n
    | Sum.inr n => -(n : ℤ) - 1
  invFun z := if 0 ≤ z then Sum.inl z.toNat else Sum.inr (-z - 1).toNat
  left_inv := by
    rintro (n | n)
    · simp
    · change (if 0 ≤ (-(n : ℤ) - 1) then
          Sum.inl (-(n : ℤ) - 1).toNat
        else Sum.inr (-(-(n : ℤ) - 1) - 1).toNat) = Sum.inr n
      rw [if_neg (by omega)]
      congr 1
      rw [show -(-(n : ℤ) - 1) - 1 = (n : ℤ) by ring]
      simp
  right_inv := by
    intro z
    simp only
    by_cases hz : 0 ≤ z
    · rw [if_pos hz]
      simp [Int.toNat_of_nonneg hz]
    · rw [if_neg hz]
      have hz' : 0 ≤ -z - 1 := by omega
      change -(((-z - 1).toNat : ℕ) : ℤ) - 1 = z
      rw [Int.toNat_of_nonneg hz']
      omega

/-- Pairing `z` with `-z-1` turns the bilateral signed triangular series
into twice its nonnegative half. -/
theorem summable_signedTriangularTerm_nonnegative :
    Summable (fun n : ℕ => signedTriangularTerm (n : ℤ)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  refine (Finset.range (d + 1)).finite_toSet.subset ?_
  intro n hn
  simp only [Function.mem_support, coeff_signedTriangularTerm] at hn
  by_contra hmem
  have hnd : d < n := by
    have : d + 1 ≤ n := by
      simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
    omega
  have hdegree : jacobiHalfTriangularDegree (n : ℤ) ≠ d := by
    intro h
    have htwo := two_mul_jacobiHalfTriangularDegree (n : ℤ)
    rw [h] at htwo
    nlinarith
  simp [hdegree] at hn

theorem tsum_signedTriangularTerm_eq_two_mul_nonnegative :
    (∑' z : ℤ, signedTriangularTerm z) =
      2 * ∑' n : ℕ, signedTriangularTerm (n : ℤ) := by
  have hnonneg := summable_signedTriangularTerm_nonnegative
  have hnegative : Summable (fun n : ℕ =>
      signedTriangularTerm (-(n : ℤ) - 1)) := by
    simpa only [signedTriangularTerm_neg_sub_one] using hnonneg
  have hsplit : HasSum
      (fun s : ℕ ⊕ ℕ => signedTriangularTerm (triangularPairEquiv s))
      ((∑' n : ℕ, signedTriangularTerm (n : ℤ)) +
        ∑' n : ℕ, signedTriangularTerm (-(n : ℤ) - 1)) := by
    apply HasSum.sum
    · exact hnonneg.hasSum
    · exact hnegative.hasSum
  have hall : HasSum signedTriangularTerm
      ((∑' n : ℕ, signedTriangularTerm (n : ℤ)) +
        ∑' n : ℕ, signedTriangularTerm (-(n : ℤ) - 1)) := by
    rw [← Equiv.hasSum_iff triangularPairEquiv]
    exact hsplit
  rw [hall.tsum_eq]
  simp_rw [signedTriangularTerm_neg_sub_one]
  ring

theorem jacobiSignedCubeSeries_eq_tsum_nonnegative :
    jacobiSignedCubeSeries =
      ∑' n : ℕ, signedTriangularTerm (n : ℤ) := by
  rw [jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm,
    tsum_signedTriangularTerm_eq_two_mul_nonnegative]
  change PowerSeries.C (1 / 2 : ℚ) *
      ((PowerSeries.C 2) * ∑' n : ℕ, signedTriangularTerm (n : ℤ)) = _
  rw [← mul_assoc, ← map_mul]
  norm_num

@[simp] theorem signedEuler_add (F G : Bivariate) :
    signedEuler (F + G) = signedEuler F + signedEuler G := by
  ext n
  simp [signedEuler]

/-- The signed Euler derivation bundled as an additive homomorphism. -/
noncomputable def signedEulerHom :
    Bivariate →+ PowerSeries ℚ where
  toFun := signedEuler
  map_zero' := by
    ext n
    simp [signedEuler]
  map_add' := signedEuler_add

theorem continuous_signedEulerHom :
    letI : TopologicalSpace LaurentQ := ⊥
    Continuous signedEulerHom := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  change Continuous signedEuler
  rw [continuous_iff_continuousAt]
  intro F
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [coeff_signedEuler]
  change Filter.Tendsto
    (fun G : Bivariate => signedEulerCoeff (PowerSeries.coeff n G))
    (nhds F)
    (nhds (signedEulerCoeff (PowerSeries.coeff n F)))
  exact (continuous_of_discreteTopology.comp
    (PowerSeries.WithPiTopology.continuous_coeff LaurentQ n)).continuousAt

/-- The nonnegative-index summands in the general JTP series. -/
noncomputable def jtpPositiveTerm (n : ℕ) : Bivariate :=
  PowerSeries.C (LaurentPolynomial.T (n : ℤ)) *
    PowerSeries.X ^ n.choose 2

/-- The negative-index summands in the general JTP series. -/
noncomputable def jtpNegativeTerm (m : ℕ) : Bivariate :=
  PowerSeries.C (LaurentPolynomial.T (-(m : ℤ) - 1)) *
    PowerSeries.X ^ (m + 2).choose 2

theorem summable_jtpPositiveTerm : Summable jtpPositiveTerm := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  refine (Finset.range (d + 2)).finite_toSet.subset ?_
  intro n hn
  simp only [Function.mem_support, jtpPositiveTerm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow] at hn
  by_contra hmem
  have hlarge : d + 2 ≤ n := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  rw [if_neg (ne_of_lt
    (JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le hlarge))] at hn
  simp at hn

theorem summable_jtpNegativeTerm : Summable jtpNegativeTerm := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  refine (Finset.range (d + 1)).finite_toSet.subset ?_
  intro m hm
  simp only [Function.mem_support, jtpNegativeTerm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow] at hm
  by_contra hmem
  have hlarge : d + 1 ≤ m := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  rw [if_neg (ne_of_lt
    (JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le (by omega)))] at hm
  simp at hm

/-- A uniform integer-indexed presentation of the general JTP series. -/
noncomputable def jtpIntegerTerm (z : ℤ) : Bivariate :=
  if 0 ≤ z then jtpPositiveTerm z.toNat
  else jtpNegativeTerm (-z - 1).toNat

@[simp] theorem jtpIntegerTerm_nat (n : ℕ) :
    jtpIntegerTerm (n : ℤ) = jtpPositiveTerm n := by
  simp [jtpIntegerTerm]

@[simp] theorem jtpIntegerTerm_neg_sub_one (n : ℕ) :
    jtpIntegerTerm (-(n : ℤ) - 1) = jtpNegativeTerm n := by
  rw [jtpIntegerTerm, if_neg (by omega)]
  congr 1
  rw [show -(-(n : ℤ) - 1) - 1 = (n : ℤ) by ring]
  simp

theorem jacobiBilateral_eq_jtpTerms :
    jacobiBilateral =
      (∑' n : ℕ, jtpPositiveTerm n) + ∑' n : ℕ, jtpNegativeTerm n := by
  rw [jacobiBilateral]
  congr 1
  apply tsum_congr
  intro m
  rw [jtpNegativeTerm]
  congr 3
  ring

/-- The split definition of `jacobiBilateral` is the sum of the uniform
integer-indexed family. -/
theorem hasSum_jtpIntegerTerm_jacobiBilateral :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum jtpIntegerTerm jacobiBilateral := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  have hsplit : HasSum
      (fun s : ℕ ⊕ ℕ => jtpIntegerTerm (triangularPairEquiv s))
      ((∑' n : ℕ, jtpPositiveTerm n) +
        ∑' n : ℕ, jtpNegativeTerm n) := by
    apply HasSum.sum
    · change HasSum (fun n : ℕ => jtpIntegerTerm (n : ℤ)) _
      simpa only [jtpIntegerTerm_nat] using summable_jtpPositiveTerm.hasSum
    · change HasSum (fun n : ℕ =>
          jtpIntegerTerm (-(n : ℤ) - 1)) _
      simpa only [jtpIntegerTerm_neg_sub_one] using
        summable_jtpNegativeTerm.hasSum
  rw [← Equiv.hasSum_iff triangularPairEquiv]
  rw [jacobiBilateral_eq_jtpTerms]
  exact hsplit

/-- Apply the Laurent Euler derivation termwise to the general JTP series. -/
theorem hasSum_signedEuler_jtpIntegerTerm :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum (fun z : ℤ => signedEuler (jtpIntegerTerm z))
      (signedEuler jacobiBilateral) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  exact hasSum_jtpIntegerTerm_jacobiBilateral.map
    signedEulerHom continuous_signedEulerHom

@[simp] theorem signedEuler_C_T_mul_X_pow (z : ℤ) (e : ℕ) :
    signedEuler
        (PowerSeries.C (LaurentPolynomial.T z) * PowerSeries.X ^ e) =
      PowerSeries.C ((z : ℚ) * ((-1 : ℚ) ^ z)) *
        PowerSeries.X ^ e := by
  ext n
  rw [coeff_signedEuler, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow]
  by_cases h : n = e
  · subst n
    simp
  · simp [h]

theorem jacobiHalfTriangularDegree_nat (t : ℕ) :
    jacobiHalfTriangularDegree (t : ℤ) = (t + 1).choose 2 := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_choose_two]
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (two_mul_jacobiHalfTriangularDegree (t : ℤ))
  push_cast at h ⊢
  nlinarith

/-- Split the integers into strictly positive and nonpositive indices,
the pairing naturally selected by the derivative of JTP at `z = -1`. -/
def cubePairEquiv : ℕ ⊕ ℕ ≃ ℤ where
  toFun s := match s with
    | Sum.inl t => (t : ℤ) + 1
    | Sum.inr t => -(t : ℤ)
  invFun z := if 0 < z then Sum.inl (z - 1).toNat else Sum.inr (-z).toNat
  left_inv := by
    rintro (t | t)
    · simp
    · change (if 0 < -(t : ℤ) then
          Sum.inl (-(t : ℤ) - 1).toNat
        else Sum.inr (-(-(t : ℤ))).toNat) = Sum.inr t
      rw [if_neg (by omega)]
      simp
  right_inv := by
    intro z
    simp only
    by_cases hz : 0 < z
    · rw [if_pos hz]
      change (((z - 1).toNat : ℕ) : ℤ) + 1 = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    · rw [if_neg hz]
      change -(((-z).toNat : ℕ) : ℤ) = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega

theorem signedEuler_jtpPair (t : ℕ) :
    signedEuler (jtpIntegerTerm ((t : ℤ) + 1)) +
        signedEuler (jtpIntegerTerm (-(t : ℤ))) =
      -signedTriangularTerm (t : ℤ) := by
  cases t with
  | zero =>
      rw [jtpIntegerTerm, if_pos (by omega),
        jtpIntegerTerm, if_pos (by omega)]
      norm_num
      rw [jtpPositiveTerm, jtpPositiveTerm,
        signedEuler_C_T_mul_X_pow, signedEuler_C_T_mul_X_pow,
        signedTriangularTerm]
      norm_num [jacobiParitySign, jacobiHalfTriangularDegree]
  | succ t =>
      rw [jtpIntegerTerm, if_pos (by omega),
        jtpIntegerTerm, if_neg (by omega)]
      norm_num
      rw [show ((t : ℤ) + 1 + 1).toNat = t + 2 by omega]
      rw [jtpPositiveTerm, jtpNegativeTerm,
        signedEuler_C_T_mul_X_pow, signedEuler_C_T_mul_X_pow,
        signedTriangularTerm]
      rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by omega,
        jacobiHalfTriangularDegree_nat]
      rw [← neg_one_zpow_eq_jacobiParitySign]
      push_cast
      rw [show ((-1 : ℚ) ^ ((t : ℤ) + 2)) = ((-1 : ℚ) ^ (t : ℤ)) by
        rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
        norm_num]
      rw [show ((-1 : ℚ) ^ (-(t : ℤ) - 1)) =
          -((-1 : ℚ) ^ (t : ℤ)) by
        rw [show -(t : ℤ) - 1 = -(t : ℤ) + (-1 : ℤ) by ring,
          zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_neg]
        norm_num
        rcases neg_one_pow_eq_or ℚ t with h | h <;> simp [h]]
      rw [show ((-1 : ℚ) ^ ((t : ℤ) + 1)) =
          -((-1 : ℚ) ^ (t : ℤ)) by
        rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
        norm_num]
      rw [show t + 1 + 1 = t + 2 by omega]
      ext n
      simp only [map_add, map_neg, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow]
      split_ifs <;> ring

@[simp] theorem signedEuler_jtpPositiveTerm (n : ℕ) :
    signedEuler (jtpPositiveTerm n) =
      PowerSeries.C (((n : ℤ) : ℚ) * ((-1 : ℚ) ^ (n : ℤ))) *
        PowerSeries.X ^ n.choose 2 := by
  rw [jtpPositiveTerm, signedEuler_C_T_mul_X_pow]

theorem summable_signedEuler_jtpPositiveShift :
    Summable (fun t : ℕ => signedEuler (jtpPositiveTerm (t + 1))) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  refine (Finset.range (d + 2)).finite_toSet.subset ?_
  intro t ht
  simp only [Function.mem_support, signedEuler_jtpPositiveTerm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow] at ht
  by_contra hmem
  have hlarge : d + 2 ≤ t := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  rw [if_neg (ne_of_lt
    (JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le (by omega)))] at ht
  simp at ht

theorem hasSum_signedEuler_jtpPairs :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum (fun t : ℕ =>
        signedEuler (jtpIntegerTerm ((t : ℤ) + 1)) +
          signedEuler (jtpIntegerTerm (-(t : ℤ))))
      (signedEuler jacobiBilateral) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  let f := fun z : ℤ => signedEuler (jtpIntegerTerm z)
  have hall : HasSum f (signedEuler jacobiBilateral) :=
    hasSum_signedEuler_jtpIntegerTerm
  have hpos : Summable (fun t : ℕ => f ((t : ℤ) + 1)) := by
    apply summable_signedEuler_jtpPositiveShift.congr
    intro t
    change signedEuler (jtpPositiveTerm (t + 1)) =
      signedEuler (jtpIntegerTerm ((t : ℤ) + 1))
    rw [jtpIntegerTerm, if_pos (by omega)]
    congr 2
  have hpairs : Summable (fun t : ℕ =>
      f ((t : ℤ) + 1) + f (-(t : ℤ))) := by
    apply summable_signedTriangularTerm_nonnegative.neg.congr
    intro t
    exact (signedEuler_jtpPair t).symm
  have hnonpos : Summable (fun t : ℕ => f (-(t : ℤ))) := by
    apply (hpairs.sub hpos).congr
    intro t
    ring
  have hsplit : HasSum
      (fun s : ℕ ⊕ ℕ => f (cubePairEquiv s))
      ((∑' t : ℕ, f ((t : ℤ) + 1)) +
        ∑' t : ℕ, f (-(t : ℤ))) := by
    apply HasSum.sum
    · exact hpos.hasSum
    · exact hnonpos.hasSum
  have hreindexed : HasSum
      (fun s : ℕ ⊕ ℕ => f (cubePairEquiv s))
      (signedEuler jacobiBilateral) := by
    change HasSum (f ∘ cubePairEquiv) (signedEuler jacobiBilateral)
    exact (Equiv.hasSum_iff cubePairEquiv).2 hall
  rw [← hsplit.unique hreindexed]
  exact hpos.hasSum.add hnonpos.hasSum

/-- The series side of differentiated JTP is minus Jacobi's signed
triangular-number series. -/
theorem signedEuler_jacobiBilateral :
    signedEuler jacobiBilateral = -jacobiSignedCubeSeries := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  have hnonneg := summable_signedTriangularTerm_nonnegative
  have hseries : HasSum (fun t : ℕ =>
      -signedTriangularTerm (t : ℤ)) (-jacobiSignedCubeSeries) := by
    rw [jacobiSignedCubeSeries_eq_tsum_nonnegative]
    exact hnonneg.hasSum.neg
  exact (HasSum.congr_fun hasSum_signedEuler_jtpPairs
    (fun t => (signedEuler_jtpPair t).symm)).unique hseries

/-- Jacobi's signed triangular-number series is Euler's product cubed. -/
theorem jacobiSignedCubeSeries_eq_eulerProduct_cube :
    jacobiSignedCubeSeries = eulerProduct ^ 3 := by
  have h := congrArg signedEuler
    jacobiTripleProduct
  rw [signedEuler_jacobiProd, signedEuler_jacobiBilateral] at h
  exact (neg_injective h).symm

theorem jacobiEulerSixProduct_eq_eulerProduct_pow_six :
    jacobiEulerSixProduct = eulerProduct ^ 6 := by
  rw [jacobiEulerSixProduct_eq_tprod_pow]
  rfl

/-- The exact cube-product input used by the four-square proof. -/
theorem jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct :
    jacobiSignedCubeSeries ^ 2 = jacobiEulerSixProduct := by
  rw [jacobiSignedCubeSeries_eq_eulerProduct_cube,
    jacobiEulerSixProduct_eq_eulerProduct_pow_six]
  ring

end JacobiCubeProduct

end QEC.Coding.TannerLiftedProduct
