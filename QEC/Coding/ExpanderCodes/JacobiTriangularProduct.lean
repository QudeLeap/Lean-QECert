import QEC.Coding.ExpanderCodes.JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology

/-!
# Jacobi's triangular-number product

This module evaluates the fixed-base formal-power-series identities in
`JacobiGeneralCore` at the topologically nilpotent series `X²`.  The source
coefficient ring is a discrete copy of `ℚ⟦X⟧`; its coefficients retain the
odd powers needed for the specialization while the outer formal variable is
sent to `X²`.
-/

namespace QEC.Coding.TannerLiftedProduct

open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

namespace JacobiTriangularProduct

open JacobiGeneralCore.FormalPowerSeries

abbrev DiscreteRat := ULift.{0, 0} ℚ

local instance discreteRatUniformSpace : UniformSpace DiscreteRat := ⊥
local instance discreteRatTopologicalSpace : TopologicalSpace DiscreteRat :=
  UniformSpace.toTopologicalSpace
local instance : DiscreteUniformity DiscreteRat := inferInstance
local instance : DiscreteTopology DiscreteRat := ⟨rfl⟩

abbrev Target := PowerSeries DiscreteRat
abbrev DiscreteTarget := ULift.{0, 0} Target
abbrev Outer := PowerSeries DiscreteTarget

local instance discreteTargetUniformSpace : UniformSpace DiscreteTarget := ⊥
local instance discreteTargetTopologicalSpace : TopologicalSpace DiscreteTarget :=
  UniformSpace.toTopologicalSpace
local instance : DiscreteUniformity DiscreteTarget := inferInstance
local instance : DiscreteTopology DiscreteTarget := ⟨rfl⟩

noncomputable def wrapTarget : Target →+* DiscreteTarget where
  toFun := ULift.up
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable def unwrapTarget : DiscreteTarget →+* Target where
  toFun := ULift.down
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem unwrapTarget_wrapTarget (f : Target) :
    unwrapTarget (wrapTarget f) = f := rfl

theorem continuous_unwrapTarget : Continuous unwrapTarget :=
  continuous_of_discreteTopology

theorem hasEval_X_sq : PowerSeries.HasEval (PowerSeries.X ^ 2 : Target) :=
  by
    simpa [pow_two] using
      (PowerSeries.HasEval.X.mul_right (PowerSeries.X : Target))

/-- Evaluate the outer formal variable at the square of the target variable. -/
noncomputable def evalOuter : Outer →+* Target :=
  PowerSeries.eval₂Hom continuous_unwrapTarget hasEval_X_sq

@[simp] theorem evalOuter_C (f : Target) :
    evalOuter (PowerSeries.C (wrapTarget f)) = f := by
  rw [evalOuter, PowerSeries.coe_eval₂Hom]
  rw [PowerSeries.eval₂_C]
  rfl

@[simp] theorem evalOuter_X :
    evalOuter (PowerSeries.X : Outer) =
      (PowerSeries.X : Target) ^ 2 := by
  rw [evalOuter, PowerSeries.coe_eval₂Hom]
  rw [PowerSeries.eval₂_X]

theorem continuous_evalOuter : Continuous evalOuter := by
  rw [evalOuter, PowerSeries.coe_eval₂Hom]
  exact PowerSeries.continuous_eval₂ continuous_unwrapTarget hasEval_X_sq

theorem evalOuter_qPochhammerInf (a : Outer) :
    evalOuter (qPochhammerInf a) =
      ∏' n : ℕ, ((1 : Target) - evalOuter a *
        (PowerSeries.X ^ 2 : Target) ^ n) := by
  rw [qPochhammerInf]
  rw [(multipliable_one_sub_mul_pow a).map_tprod
    evalOuter continuous_evalOuter]
  simp only [map_sub, map_one, map_mul, map_pow, evalOuter_X]

theorem summable_eulerSecondTerm (a : Outer) :
    Summable (fun k : ℕ =>
      (PowerSeries.X : Outer) ^ k.choose 2 * a ^ k *
        qPochhammerInv (R := DiscreteTarget) k) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  refine (Finset.range (d + 2)).finite_toSet.subset ?_
  intro k hk
  simp only [Function.mem_support] at hk
  by_contra hmem
  have hlarge : d + 2 ≤ k := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  have hdegree := JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le hlarge
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg hdegree.not_ge] at hk
  exact hk rfl

theorem evalOuter_eulerSecond (a : Outer) :
    evalOuter (qPochhammerInf (-a)) =
      ∑' k : ℕ, evalOuter
        ((PowerSeries.X : Outer) ^ k.choose 2 * a ^ k *
          qPochhammerInv (R := DiscreteTarget) k) := by
  rw [euler_second_identity a]
  exact (summable_eulerSecondTerm a).map_tsum
    evalOuter continuous_evalOuter

noncomputable def sourceQ : Outer :=
  PowerSeries.C (wrapTarget ((PowerSeries.X : Target) ^ 2))

noncomputable def sourceOne : Outer :=
  PowerSeries.C (wrapTarget 1)

@[simp] theorem evalOuter_sourceQ : evalOuter sourceQ =
    (PowerSeries.X : Target) ^ 2 := by
  simp [sourceQ]

@[simp] theorem evalOuter_sourceOne : evalOuter sourceOne = 1 := by
  simp [sourceOne]

theorem evalOuter_qPochhammerInf_X_mul_qPochhammerInv (n : ℕ) :
    evalOuter (qPochhammerInf (PowerSeries.X : Outer)) *
      evalOuter (qPochhammerInv (R := DiscreteTarget) n) =
      evalOuter (qPochhammerInf
        ((PowerSeries.X : Outer) * PowerSeries.X ^ n)) := by
  calc
    _ = evalOuter (qPochhammerInf (PowerSeries.X : Outer) *
          qPochhammerInv (R := DiscreteTarget) n) := by
      simp only [map_mul]
    _ = _ := congrArg evalOuter
      (qPochhammerInf_X_mul_qPochhammerInv (R := DiscreteTarget) n)

theorem evalOuter_hasSum_choose_nonnegative (k : ℕ) :
    HasSum (evalOuter ∘ fun m : ℕ =>
      ((PowerSeries.X : Outer) ^ (m + k).choose 2 *
        qPochhammerInf (PowerSeries.X * PowerSeries.X ^ (m + k)) *
        (PowerSeries.X ^ m.choose 2 * PowerSeries.X ^ m *
          qPochhammerInv (R := DiscreteTarget) m)))
      (((PowerSeries.X : Target) ^ 2) ^ k.choose 2) := by
  simpa only [map_pow, evalOuter_X] using
    (hasSum_pow_choose_two_nonneg (R := DiscreteTarget) k).map
      evalOuter continuous_evalOuter

theorem evalOuter_hasSum_choose_negative (l : ℕ) :
    HasSum (evalOuter ∘ fun n : ℕ =>
      ((PowerSeries.X : Outer) ^ n.choose 2 *
        qPochhammerInf (PowerSeries.X * PowerSeries.X ^ n) *
        (PowerSeries.X ^ (n + (l + 1)).choose 2 *
          PowerSeries.X ^ (n + (l + 1)) *
          qPochhammerInv (R := DiscreteTarget) (n + (l + 1)))))
      (((PowerSeries.X : Target) ^ 2) ^ (l + 2).choose 2) := by
  simpa only [map_pow, evalOuter_X] using
    (hasSum_pow_choose_two_neg (R := DiscreteTarget) l).map
      evalOuter continuous_evalOuter

noncomputable def baseQ : Target := (PowerSeries.X : Target) ^ 2

noncomputable def evaluatedPochhammerInf : Target :=
  evalOuter (qPochhammerInf (PowerSeries.X : Outer))

noncomputable def evaluatedPochhammerInv (n : ℕ) : Target :=
  evalOuter (qPochhammerInv (R := DiscreteTarget) n)

noncomputable def evaluatedTail (n : ℕ) : Target :=
  evalOuter (qPochhammerInf
    ((PowerSeries.X : Outer) * PowerSeries.X ^ n))

noncomputable def triangularLeftTerm (n : ℕ) : Target :=
  baseQ ^ n.choose 2 * baseQ ^ n * evaluatedTail n

noncomputable def triangularRightTerm (m : ℕ) : Target :=
  baseQ ^ m.choose 2 * evaluatedPochhammerInv m

theorem hasSum_triangularEulerLeft :
    HasSum triangularLeftTerm
      (evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) := by
  have heuler := evalOuter_eulerSecond sourceQ
  have hmapped : HasSum (fun n : ℕ => evalOuter
      ((PowerSeries.X : Outer) ^ n.choose 2 * sourceQ ^ n *
        qPochhammerInv (R := DiscreteTarget) n))
      (evalOuter (qPochhammerInf (-sourceQ))) := by
    rw [heuler]
    exact ((summable_eulerSecondTerm sourceQ).map
      evalOuter continuous_evalOuter).hasSum
  apply HasSum.congr_fun (hmapped.mul_left evaluatedPochhammerInf)
  intro n
  rw [triangularLeftTerm, evaluatedPochhammerInf,
    evaluatedTail, baseQ]
  simp only [map_mul, map_pow, evalOuter_X, evalOuter_sourceQ]
  rw [← evalOuter_qPochhammerInf_X_mul_qPochhammerInv]
  ring

theorem hasSum_triangularEulerRight :
    HasSum triangularRightTerm
      (evalOuter (qPochhammerInf (-sourceOne))) := by
  have heuler := evalOuter_eulerSecond sourceOne
  have hmapped : HasSum (fun n : ℕ => evalOuter
      ((PowerSeries.X : Outer) ^ n.choose 2 * sourceOne ^ n *
        qPochhammerInv (R := DiscreteTarget) n))
      (evalOuter (qPochhammerInf (-sourceOne))) := by
    rw [heuler]
    exact ((summable_eulerSecondTerm sourceOne).map
      evalOuter continuous_evalOuter).hasSum
  apply HasSum.congr_fun hmapped
  intro n
  rw [triangularRightTerm, evaluatedPochhammerInv, baseQ]
  simp only [map_mul, map_pow, evalOuter_X, evalOuter_sourceOne,
    one_pow]
  ring

noncomputable def triangularProductTerm (p : ℕ × ℕ) : Target :=
  triangularLeftTerm p.1 * triangularRightTerm p.2

private theorem coeff_triangularProductTerm_eq_zero {d i j : ℕ}
    (h : d < 2 * (i.choose 2 + i + j.choose 2)) :
    PowerSeries.coeff d (triangularProductTerm (i, j)) = 0 := by
  have hrw : triangularProductTerm (i, j) =
      (PowerSeries.X : Target) ^ (2 * (i.choose 2 + i + j.choose 2)) *
        (evaluatedTail i * evaluatedPochhammerInv j) := by
    rw [triangularProductTerm, triangularLeftTerm, triangularRightTerm, baseQ]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  rw [hrw, PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]

theorem summable_triangularProductTerm : Summable triangularProductTerm := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff DiscreteRat).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 1) ×ˢ Finset.range (d + 2)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_triangularProductTerm_eq_zero ?_
  rcases hp with hi | hj
  · omega
  · have := JacobiGeneralCore.Nat.lt_choose_two_of_add_two_le hj
    omega

theorem hasSum_triangularProductTerm :
    HasSum triangularProductTerm
      ((evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
        evalOuter (qPochhammerInf (-sourceOne))) := by
  have h :
      (evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
          evalOuter (qPochhammerInf (-sourceOne)) =
        ∑' p : ℕ × ℕ, triangularProductTerm p := by
    exact hasSum_triangularEulerLeft.mul_eq hasSum_triangularEulerRight
      summable_triangularProductTerm.hasSum
  rw [h]
  exact summable_triangularProductTerm.hasSum

/-- Split `ℕ × ℕ` into the weakly lower and strictly upper diagonals. -/
private def diagonalEquiv : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun p := if p.2 ≤ p.1 then
      Sum.inl (p.1 - p.2, p.2)
    else
      Sum.inr (p.2 - p.1 - 1, p.1)
  invFun s := match s with
    | Sum.inl (k, m) => (m + k, m)
    | Sum.inr (l, n) => (n, n + l + 1)
  left_inv := by
    intro ⟨n, m⟩
    simp only
    split_ifs with h <;> simp <;> omega
  right_inv := by
    intro s
    rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp
    omega

private theorem hasSum_split_diagonal (f : ℕ × ℕ → Target)
    {a b : Target}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + p.1 + 1)) b) :
    HasSum f (a + b) :=
  diagonalEquiv.symm.hasSum_iff.mp (h1.sum h2)

private theorem hasSum_of_hasSum_fiberwise {f : ℕ × ℕ → Target}
    {g : ℕ → Target} (hf : Summable f)
    (hrow : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m)) (g k)) :
    HasSum f (∑' k : ℕ, g k) := by
  rw [(hf.hasSum.prod_fiberwise hrow).tsum_eq]
  exact hf.hasSum

theorem hasSum_triangularDiagonal_nonnegative (k : ℕ) :
    HasSum (fun m : ℕ => triangularProductTerm (m + k, m))
      (baseQ ^ (k + 1).choose 2) := by
  have h := (evalOuter_hasSum_choose_nonnegative k).mul_left (baseQ ^ k)
  have hsum : baseQ ^ k * (PowerSeries.X ^ 2 : Target) ^ k.choose 2 =
      baseQ ^ (k + 1).choose 2 := by
    rw [JacobiGeneralCore.Nat.choose_two_succ, pow_add, baseQ]
    ring
  rw [← hsum]
  apply HasSum.congr_fun h
  intro m
  rw [triangularProductTerm, triangularLeftTerm, triangularRightTerm,
    evaluatedTail, evaluatedPochhammerInv, baseQ]
  simp only [Function.comp_apply, map_mul, map_pow, evalOuter_X]
  ring

theorem hasSum_triangularDiagonal_negative (l : ℕ) :
    HasSum (fun n : ℕ => triangularProductTerm (n, n + l + 1))
      (baseQ ^ (l + 1).choose 2) := by
  have hinjective : Function.Injective (fun n : ℕ => (n, n + l + 1)) := by
    intro n m h
    exact congrArg Prod.fst h
  have hrow : Summable
      (fun n : ℕ => triangularProductTerm (n, n + l + 1)) :=
    summable_triangularProductTerm.comp_injective hinjective
  have hscaled := hrow.hasSum.mul_left (baseQ ^ (l + 1))
  have hscaled' : HasSum (evalOuter ∘ fun n : ℕ =>
      ((PowerSeries.X : Outer) ^ n.choose 2 *
        qPochhammerInf (PowerSeries.X * PowerSeries.X ^ n) *
        (PowerSeries.X ^ (n + (l + 1)).choose 2 *
          PowerSeries.X ^ (n + (l + 1)) *
          qPochhammerInv (R := DiscreteTarget) (n + (l + 1)))))
      (baseQ ^ (l + 1) *
        ∑' n : ℕ, triangularProductTerm (n, n + l + 1)) := by
    apply HasSum.congr_fun hscaled
    intro n
    rw [triangularProductTerm, triangularLeftTerm, triangularRightTerm,
      evaluatedTail, evaluatedPochhammerInv, baseQ]
    simp only [Function.comp_apply, map_mul, map_pow, evalOuter_X]
    ring_nf
  have hscaledSum :
      baseQ ^ (l + 1) *
          (∑' n : ℕ, triangularProductTerm (n, n + l + 1)) =
        baseQ ^ (l + 2).choose 2 :=
    hscaled'.unique (evalOuter_hasSum_choose_negative l)
  have hrowSum :
      (∑' n : ℕ, triangularProductTerm (n, n + l + 1)) =
        baseQ ^ (l + 1).choose 2 := by
    apply mul_left_cancel₀ (a := baseQ ^ (l + 1))
    · simp [baseQ]
    · rw [hscaledSum, JacobiGeneralCore.Nat.choose_two_succ]
      ring
  rw [← hrowSum]
  exact hrow.hasSum

private theorem summable_triangularDiagonal_nonnegative :
    Summable (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2 + p.1, p.2)) := by
  apply summable_triangularProductTerm.comp_injective
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only at h
  injection h with hsum h₂
  congr
  omega

private theorem summable_triangularDiagonal_negative :
    Summable (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2, p.2 + p.1 + 1)) := by
  apply summable_triangularProductTerm.comp_injective
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only at h
  injection h with h₂ hsum
  congr
  omega

noncomputable def evaluatedTriangularSeries : Target :=
  ∑' n : ℕ, baseQ ^ (n + 1).choose 2

private theorem hasSum_triangularDiagonal_nonnegative_part :
    HasSum (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2 + p.1, p.2))
      evaluatedTriangularSeries := by
  exact hasSum_of_hasSum_fiberwise
    summable_triangularDiagonal_nonnegative
    hasSum_triangularDiagonal_nonnegative

private theorem hasSum_triangularDiagonal_negative_part :
    HasSum (fun p : ℕ × ℕ =>
      triangularProductTerm (p.2, p.2 + p.1 + 1))
      evaluatedTriangularSeries := by
  exact hasSum_of_hasSum_fiberwise
    summable_triangularDiagonal_negative
    hasSum_triangularDiagonal_negative

theorem evaluatedJacobiProduct_eq_two_mul_triangularSeries :
    (evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
        evalOuter (qPochhammerInf (-sourceOne)) =
      2 * evaluatedTriangularSeries := by
  have hdiagonal : HasSum triangularProductTerm
      (evaluatedTriangularSeries + evaluatedTriangularSeries) :=
    hasSum_split_diagonal triangularProductTerm
      hasSum_triangularDiagonal_nonnegative_part
      hasSum_triangularDiagonal_negative_part
  rw [hasSum_triangularProductTerm.unique hdiagonal]
  ring

noncomputable def evaluatedEvenMinusProduct : Target :=
  ∏' n : ℕ, (1 - baseQ ^ (n + 1))

noncomputable def evaluatedEvenPlusProduct : Target :=
  ∏' n : ℕ, (1 + baseQ ^ (n + 1))

noncomputable def evaluatedTriangularProduct : Target :=
  ∏' n : ℕ,
    (1 - baseQ ^ (n + 1)) * (1 + baseQ ^ (n + 1)) ^ 2

theorem multipliable_evaluatedEvenMinusFactor :
    Multipliable (fun n : ℕ => (1 : Target) - baseQ ^ (n + 1)) := by
  have h := (multipliable_one_sub_mul_pow (PowerSeries.X : Outer)).map
    evalOuter continuous_evalOuter
  apply h.congr
  intro n
  simp only [Function.comp_apply, map_sub, map_one, map_mul, map_pow,
    evalOuter_X]
  rw [baseQ, pow_succ]
  ring

theorem multipliable_evaluatedEvenPlusFactor :
    Multipliable (fun n : ℕ => (1 : Target) + baseQ ^ (n + 1)) := by
  have h := (multipliable_one_sub_mul_pow (-sourceQ)).map
    evalOuter continuous_evalOuter
  apply h.congr
  intro n
  simp only [Function.comp_apply, map_sub, map_one, map_mul, map_neg, map_pow,
    evalOuter_sourceQ, evalOuter_X]
  rw [baseQ, pow_succ]
  ring

theorem evaluatedPochhammerInf_eq_evenMinusProduct :
    evaluatedPochhammerInf = evaluatedEvenMinusProduct := by
  rw [evaluatedPochhammerInf, evalOuter_qPochhammerInf,
    evaluatedEvenMinusProduct]
  apply tprod_congr
  intro n
  rw [baseQ, pow_succ]
  simp only [evalOuter_X]
  ring

theorem evalOuter_qPochhammerInf_neg_sourceQ_eq_evenPlusProduct :
    evalOuter (qPochhammerInf (-sourceQ)) =
      evaluatedEvenPlusProduct := by
  rw [evalOuter_qPochhammerInf, evaluatedEvenPlusProduct]
  apply tprod_congr
  intro n
  rw [baseQ, pow_succ]
  simp only [map_neg, evalOuter_sourceQ]
  ring

set_option maxHeartbeats 800000 in
theorem evalOuter_qPochhammerInf_neg_sourceOne_eq_two_mul_evenPlusProduct :
    evalOuter (qPochhammerInf (-sourceOne)) =
      2 * evaluatedEvenPlusProduct := by
  calc
    evalOuter (qPochhammerInf (-sourceOne)) =
        ∏' n : ℕ, (1 + baseQ ^ n) := by
      rw [evalOuter_qPochhammerInf]
      apply tprod_congr
      intro n
      simp only [map_neg, evalOuter_sourceOne, neg_mul, one_mul,
        sub_neg_eq_add]
      rfl
    _ = (1 + baseQ ^ 0) * ∏' n : ℕ, (1 + baseQ ^ (n + 1)) := by
      rw [tprod_eq_zero_mul' multipliable_evaluatedEvenPlusFactor]
    _ = 2 * evaluatedEvenPlusProduct := by
      rw [evaluatedEvenPlusProduct, pow_zero]
      rw [one_add_one_eq_two]

theorem evaluatedTriangularProduct_eq_evenProducts :
    evaluatedTriangularProduct =
      evaluatedEvenMinusProduct * evaluatedEvenPlusProduct ^ 2 := by
  rw [evaluatedTriangularProduct, evaluatedEvenMinusProduct,
    evaluatedEvenPlusProduct]
  calc
    _ = (∏' n : ℕ, (1 - baseQ ^ (n + 1))) *
        (∏' n : ℕ, (1 + baseQ ^ (n + 1)) ^ 2) := by
      simpa using multipliable_evaluatedEvenMinusFactor.tprod_mul
        (multipliable_evaluatedEvenPlusFactor.pow 2)
    _ = _ := congrArg
      (fun z => (∏' n : ℕ, (1 - baseQ ^ (n + 1))) * z)
      (multipliable_evaluatedEvenPlusFactor.tprod_pow 2)

theorem evaluatedJacobiProduct_eq_two_mul_triangularProduct :
    (evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
        evalOuter (qPochhammerInf (-sourceOne)) =
      2 * evaluatedTriangularProduct := by
  rw [evaluatedPochhammerInf_eq_evenMinusProduct,
    evalOuter_qPochhammerInf_neg_sourceQ_eq_evenPlusProduct,
    evalOuter_qPochhammerInf_neg_sourceOne_eq_two_mul_evenPlusProduct,
    evaluatedTriangularProduct_eq_evenProducts]
  ring

theorem evaluatedTriangularProduct_eq_series :
    evaluatedTriangularProduct = evaluatedTriangularSeries := by
  apply mul_left_cancel₀ (a := (2 : Target))
  · intro h
    rw [← one_add_one_eq_two] at h
    have hc : (1 : DiscreteRat) + 1 = 0 := by
      simpa only [map_add, map_one, map_zero] using
        congrArg (PowerSeries.constantCoeff (R := DiscreteRat)) h
    have hc' := congrArg ULift.down hc
    norm_num at hc'
  · rw [← evaluatedJacobiProduct_eq_two_mul_triangularProduct,
      evaluatedJacobiProduct_eq_two_mul_triangularSeries]

noncomputable def unwrapRat : DiscreteRat →+* ℚ where
  toFun := ULift.down
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable def mapToRat : Target →+* PowerSeries ℚ :=
  PowerSeries.map unwrapRat

theorem continuous_mapToRat : Continuous mapToRat := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  change Filter.Tendsto
    (fun g : Target => unwrapRat (PowerSeries.coeff n g))
    (nhds f)
    (nhds (unwrapRat (PowerSeries.coeff n f)))
  exact (continuous_of_discreteTopology.comp
    (PowerSeries.WithPiTopology.continuous_coeff
      DiscreteRat n)).continuousAt

@[simp] theorem mapToRat_X :
    mapToRat (PowerSeries.X : Target) =
      (PowerSeries.X : PowerSeries ℚ) := by
  simp [mapToRat]

@[simp] theorem mapToRat_baseQ :
    mapToRat baseQ = (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  simp [baseQ]

theorem multipliable_evaluatedTriangularFactor :
    Multipliable (fun n : ℕ =>
      (1 - baseQ ^ (n + 1)) * (1 + baseQ ^ (n + 1)) ^ 2) :=
  multipliable_evaluatedEvenMinusFactor.mul
    (multipliable_evaluatedEvenPlusFactor.pow 2)

theorem mapToRat_evaluatedTriangularProduct :
    mapToRat evaluatedTriangularProduct = jacobiTriangularProduct := by
  rw [evaluatedTriangularProduct,
    multipliable_evaluatedTriangularFactor.map_tprod
      mapToRat continuous_mapToRat,
    jacobiTriangularProduct]
  apply tprod_congr
  intro n
  simp only [map_mul, map_sub, map_one, map_pow, map_add,
    mapToRat_baseQ]
  rw [← pow_mul]

theorem summable_evaluatedTriangularSeriesTerm :
    Summable (fun n : ℕ => baseQ ^ (n + 1).choose 2) := by
  exact (summable_triangularDiagonal_nonnegative.hasSum.prod_fiberwise
    hasSum_triangularDiagonal_nonnegative).summable

theorem mapToRat_evaluatedTriangularSeries :
    mapToRat evaluatedTriangularSeries =
      ∑' n : ℕ,
        (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1)) := by
  rw [evaluatedTriangularSeries,
    summable_evaluatedTriangularSeriesTerm.map_tsum
      mapToRat continuous_mapToRat]
  apply tsum_congr
  intro n
  simp only [map_pow, mapToRat_baseQ]
  rw [← pow_mul]
  congr 1
  rw [JacobiGeneralCore.Nat.choose_two_succ]
  have h₁ : n + 2 * n.choose 2 = n ^ 2 := by
    have hdvd : 2 ∣ n * (n - 1) := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩ <;>
        simp [hm] <;> ring_nf <;> omega
    rw [Nat.choose_two_right, Nat.mul_div_cancel' hdvd]
    rcases n with _ | n
    · simp
    · simp [sq]
      ring
  nlinarith

/-- The finite set of nonnegative triangular roots of `d`. -/
noncomputable def naturalTriangularRoots (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter fun n => n * (n + 1) = d

theorem mem_naturalTriangularRoots_iff (d n : ℕ) :
    n ∈ naturalTriangularRoots d ↔ n * (n + 1) = d := by
  rw [naturalTriangularRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hn => ?_
  rw [Finset.mem_range]
  have hle : n ≤ n * (n + 1) := by nlinarith
  omega

private def integerTriangularRootEquiv (d : ℕ) :
    {z : ℤ // z ∈ integerTriangularRoots d} ≃
      Bool × {n : ℕ // n ∈ naturalTriangularRoots d} where
  toFun z := if hz : 0 ≤ z.1 then
      (false, ⟨z.1.toNat, by
        rw [mem_naturalTriangularRoots_iff]
        have heq := (mem_integerTriangularRoots_iff d z.1).mp z.2
        have hcast : (z.1.toNat : ℤ) = z.1 := Int.toNat_of_nonneg hz
        rw [← hcast] at heq
        have hnat : z.1.toNat ^ 2 + z.1.toNat = d := by
          exact_mod_cast heq
        nlinarith⟩)
    else
      (true, ⟨(-z.1 - 1).toNat, by
        rw [mem_naturalTriangularRoots_iff]
        have heq := (mem_integerTriangularRoots_iff d z.1).mp z.2
        have hw : 0 ≤ -z.1 - 1 := by omega
        have hcast : (((-z.1 - 1).toNat : ℕ) : ℤ) = -z.1 - 1 :=
          Int.toNat_of_nonneg hw
        have heq' : (-z.1 - 1) ^ 2 + (-z.1 - 1) = (d : ℤ) := by
          nlinarith
        rw [← hcast] at heq'
        have hnat : (-z.1 - 1).toNat ^ 2 + (-z.1 - 1).toNat = d := by
          exact_mod_cast heq'
        nlinarith⟩)
  invFun p := match p with
    | (false, n) => ⟨(n.1 : ℤ), by
        rw [mem_integerTriangularRoots_iff]
        have hn := (mem_naturalTriangularRoots_iff d n.1).mp n.2
        have hn' : (n.1 : ℤ) * (n.1 + 1) = d := by exact_mod_cast hn
        nlinarith⟩
    | (true, n) => ⟨-(n.1 : ℤ) - 1, by
        rw [mem_integerTriangularRoots_iff]
        have hnNat := (mem_naturalTriangularRoots_iff d n.1).mp n.2
        have hn : (n.1 : ℤ) * (n.1 + 1) = d := by exact_mod_cast hnNat
        nlinarith⟩
  left_inv := by
    intro z
    simp only
    split_ifs with hz
    · apply Subtype.ext
      simp [Int.toNat_of_nonneg hz]
    · apply Subtype.ext
      have hw : 0 ≤ -z.1 - 1 := by omega
      change -((((-z.1 - 1).toNat : ℕ) : ℤ)) - 1 = z.1
      rw [Int.toNat_of_nonneg hw]
      omega
  right_inv := by
    rintro ⟨b, n⟩
    cases b
    · simp
    · simp
      omega

theorem card_integerTriangularRoots_eq_two_mul_natural (d : ℕ) :
    (integerTriangularRoots d).card =
      2 * (naturalTriangularRoots d).card := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card {z : ℤ // z ∈ integerTriangularRoots d} =
        Fintype.card (Bool × {n : ℕ // n ∈ naturalTriangularRoots d}) :=
      Fintype.card_congr (integerTriangularRootEquiv d)
    _ = 2 * (naturalTriangularRoots d).card := by simp

theorem mapToRat_triangularSeriesTerm (n : ℕ) :
    mapToRat (baseQ ^ (n + 1).choose 2) =
      (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1)) := by
  simp only [map_pow, mapToRat_baseQ]
  rw [← pow_mul]
  congr 1
  rw [JacobiGeneralCore.Nat.choose_two_succ]
  have h₁ : n + 2 * n.choose 2 = n ^ 2 := by
    have hdvd : 2 ∣ n * (n - 1) := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩ <;>
        simp [hm] <;> ring_nf <;> omega
    rw [Nat.choose_two_right, Nat.mul_div_cancel' hdvd]
    rcases n with _ | n
    · simp
    · simp [sq]
      ring
  nlinarith

theorem summable_rationalTriangularSeriesTerm :
    Summable (fun n : ℕ =>
      (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1))) := by
  have h := summable_evaluatedTriangularSeriesTerm.map
    mapToRat continuous_mapToRat
  apply h.congr
  intro n
  exact mapToRat_triangularSeriesTerm n

theorem coeff_rationalUnilateralTriangularSeries (d : ℕ) :
    PowerSeries.coeff d
        (∑' n : ℕ,
          (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1))) =
      (naturalTriangularRoots d).card := by
  rw [summable_rationalTriangularSeriesTerm.map_tsum
    (PowerSeries.coeff d)
    (PowerSeries.WithPiTopology.continuous_coeff ℚ d)]
  simp only [PowerSeries.coeff_X_pow]
  rw [tsum_eq_sum (s := naturalTriangularRoots d)]
  · calc
      (∑ b ∈ naturalTriangularRoots d,
          if d = b * (b + 1) then (1 : ℚ) else 0) =
          ∑ _b ∈ naturalTriangularRoots d, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [if_pos]
        exact ((mem_naturalTriangularRoots_iff d b).mp hb).symm
      _ = (naturalTriangularRoots d).card := by simp
  · intro n hn
    rw [if_neg]
    intro heq
    apply hn
    rw [mem_naturalTriangularRoots_iff]
    exact heq.symm

theorem rationalUnilateralTriangularSeries_eq_theta :
    (∑' n : ℕ,
        (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1))) =
      rationalTriangularThetaSeries := by
  ext d
  rw [coeff_rationalUnilateralTriangularSeries,
    coeff_rationalTriangularThetaSeries,
    card_integerTriangularRoots_eq_two_mul_natural]
  push_cast
  ring

/-- Jacobi's triangular-number product identity over rational formal power
series, obtained by a legal nested-FPS specialization of the fixed-base
triple-product proof. -/
theorem jacobiTriangularProduct_eq_rationalTriangularThetaSeries :
    jacobiTriangularProduct = rationalTriangularThetaSeries := by
  calc
    jacobiTriangularProduct = mapToRat evaluatedTriangularProduct :=
      mapToRat_evaluatedTriangularProduct.symm
    _ = mapToRat evaluatedTriangularSeries :=
      congrArg mapToRat evaluatedTriangularProduct_eq_series
    _ = ∑' n : ℕ,
        (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1)) :=
      mapToRat_evaluatedTriangularSeries
    _ = rationalTriangularThetaSeries :=
      rationalUnilateralTriangularSeries_eq_theta

end JacobiTriangularProduct

end QEC.Coding.TannerLiftedProduct
