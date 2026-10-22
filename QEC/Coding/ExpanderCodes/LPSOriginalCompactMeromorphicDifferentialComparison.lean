import QEC.Coding.ExpanderCodes.LPSOriginalHolomorphicDifferentialComparison
import QEC.Coding.ExpanderCodes.LPSOriginalCompactMeromorphicFunctionField
import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# All original compact meromorphic covector germs

Start from ALL sections of the actual tangent-to-trivial cotangent Hom bundle
whose coefficients are meromorphic in every original chart. Quotient by actual
global codiscrete zero, independently of the ratio map. Actual chart covariance,
finite critical set of dj, exact kernel and surjectivity identify this space with
the ENTIRE independently defined compact meromorphic function field. Point values
at poles remain representative values; genuine germs remove their ambiguity.

This is internal proof closure for parent #449 and the original LPS route in
PK22 ex:Xpq (pinned main.tex484–486), following the actual meromorphic/differential
interpretation of the same modular curve in Milne, Modular Functions and Modular
Forms. N is positive and 4 divides N, including the actual theta levels.

This module does not prove global algebraic regularity/GAGA, normalization base
change, uniform good reduction, Frobenius/Weil estimates or the arbitrary-field
PK22 quantum family theorem. No public node changes status here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold ContDiff
noncomputable section

/-- ALL actual cotangent Hom-bundle sections, with no meromorphy or generated-image restriction. -/
abbrev LPSOriginalFilledCovectorRepresentatives
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  letI := lpsOriginalFilled_isManifold N hN
  (x : LPSOriginalFilledCurve N) → TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledCovectorChartCoefficient
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x : LPSOriginalFilledCurve N) : ℂ → ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun z => ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
    (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ)
    x ((chartAt ℂ x).symm z) x ((chartAt ℂ x).symm z)
    (sectionForm ((chartAt ℂ x).symm z)) (1 : ℂ)

/-- Meromorphy of the actual coefficient at EVERY point of EVERY original chart target. -/
def lpsOriginalFilledCovectorChartMeromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN) : Prop :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  ∀ x : LPSOriginalFilledCurve N,
    MeromorphicOn (lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x)
      (chartAt ℂ x).target

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovectorChart_evaluate
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x y : LPSOriginalFilledCurve N) (v : ℂ)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    sectionForm y v = lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x
      (chartAt ℂ x y) • (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y v : ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let P : ℂ →L[ℂ] ℂ := ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
    (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y (sectionForm y)
  let e := trivializationAt ℂ (TangentSpace (M := LPSOriginalFilledCurve N) 𝓘(ℂ)) x
  have he : e.continuousLinearMapAt ℂ y = mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hy]
    exact TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy
  have hv : P (e.continuousLinearMapAt ℂ y v) = sectionForm y v := by
    dsimp only [P]
    have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
    rw [ContinuousLinearMap.inCoordinates, ht, ContinuousLinearMap.id_comp]
    change sectionForm y (e.symmL ℂ y (e.continuousLinearMapAt ℂ y v)) = _
    rw [e.symmL_continuousLinearMapAt hy]
  have hscalar : P (e.continuousLinearMapAt ℂ y v) =
      P (1 : ℂ) • (e.continuousLinearMapAt ℂ y v : ℂ) := by
    let z : ℂ := e.continuousLinearMapAt ℂ y v
    have hz := P.map_smul z (1 : ℂ)
    change P (z * 1) = z * P (1 : ℂ) at hz
    rw [mul_one, mul_comm] at hz
    exact hz
  rw [← hv, hscalar, he]
  congr 1
  unfold lpsOriginalFilledCovectorChartCoefficient
  rw [(chartAt ℂ x).left_inv hy]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledCovectorChartCoefficientLinearMap
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N) :
    LPSOriginalFilledCovectorRepresentatives N hN →ₗ[ℂ] (ℂ → ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact
    { toFun := fun sectionForm => lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x
      map_add' := by
        intro sectionForm otherForm
        funext z
        simp [lpsOriginalFilledCovectorChartCoefficient, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
      map_smul' := by
        intro c sectionForm
        funext z
        simp [lpsOriginalFilledCovectorChartCoefficient, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.smul_comp] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledMeromorphicCovectorSubmodule
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Submodule ℂ (LPSOriginalFilledCovectorRepresentatives N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact
    { carrier := {sectionForm | lpsOriginalFilledCovectorChartMeromorphic N hN sectionForm}
      zero_mem' := by
        intro x
        change MeromorphicOn (lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x 0)
          (chartAt ℂ x).target
        rw [map_zero]
        exact MeromorphicOn.const 0
      add_mem' := by
        intro sectionForm otherForm hsection hother x
        change MeromorphicOn
          (lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x (sectionForm+otherForm))
            (chartAt ℂ x).target
        rw [map_add]
        exact (hsection x).add (hother x)
      smul_mem' := by
        intro c sectionForm hsection x
        change MeromorphicOn
          (lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x (c • sectionForm))
            (chartAt ℂ x).target
        rw [map_smul]
        change MeromorphicOn (fun z => c *
          lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z) (chartAt ℂ x).target
        exact (MeromorphicOn.const c).mul (hsection x) }

/-- Native original differential object used by the comparison. -/
abbrev LPSOriginalFilledMeromorphicCovectorRepresentatives
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  ↥(lpsOriginalFilledMeromorphicCovectorSubmodule N hN)

/-- The actual manifold derivative of a function, including the native zero convention at nondifferentiable points. -/
def lpsOriginalFilledFunctionCovector
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) :
    LPSOriginalFilledCovectorRepresentatives N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun y => mfderiv 𝓘(ℂ) 𝓘(ℂ) F y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual derivative coefficient is the ordinary complex chart derivative, even at nondifferentiable points. -/
lemma lpsOriginalFilledFunctionCovector_chart
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) (x : LPSOriginalFilledCurve N)
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionCovector N hN F) x z =
        deriv (F ∘ (chartAt ℂ x).symm) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let y := e.symm z
  have hy : y ∈ e.source := e.map_target hz
  have he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := mdifferentiable_chart x
  have hinv := he.mdifferentiableAt_symm hz
  have hchart := he.mdifferentiableAt hy
  let chartDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e y
  let inverseDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z
  let functionDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) F y
  have hcoord : chartDerivative (inverseDerivative (1 : ℂ)) = 1 := by
    exact congrArg (fun L => (L (1 : ℂ) : ℂ)) (he.comp_symm_deriv hz)
  have hvalue := lpsOriginalFilledCovectorChart_evaluate N hN
    (lpsOriginalFilledFunctionCovector N hN F) x y (inverseDerivative (1 : ℂ)) hy
  change functionDerivative (inverseDerivative (1 : ℂ)) =
      lpsOriginalFilledCovectorChartCoefficient N hN
        (lpsOriginalFilledFunctionCovector N hN F) x (e y) *
          chartDerivative (inverseDerivative (1 : ℂ)) at hvalue
  rw [e.right_inv hz,hcoord,mul_one] at hvalue
  by_cases hF : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y
  · have hmaps : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (F ∘ e.symm) z : ℂ →L[ℂ] ℂ) =
        functionDerivative.comp inverseDerivative := mfderiv_comp z hF hinv
    rw [mfderiv_eq_fderiv] at hmaps
    have hchain := congrArg (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) hmaps
    change deriv (F ∘ e.symm) z = functionDerivative (inverseDerivative (1 : ℂ)) at hchain
    exact hvalue.symm.trans hchain.symm
  · have hnot : ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F ∘ e.symm) z := by
      intro hcomp
      have hh : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F ∘ e.symm) (e y) := by
        rw [e.right_inv hz]
        exact hcomp
      have hm := hh.comp y hchart
      have heq : (F ∘ e.symm ∘ e) =ᶠ[𝓝 y] F := by
        filter_upwards [e.open_source.mem_nhds hy] with w hw
        simp only [Function.comp_apply,e.left_inv hw]
      exact hF (hm.congr_of_eventuallyEq heq.symm)
    change mfderiv 𝓘(ℂ) 𝓘(ℂ) F y (inverseDerivative (1 : ℂ)) = _ at hvalue
    rw [mfderiv_zero_of_not_mdifferentiableAt hF] at hvalue
    change (0 : ℂ) = _ at hvalue
    rw [← hvalue,deriv_zero_of_not_differentiableAt
      (mt mdifferentiableAt_iff_differentiableAt.mpr hnot)]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledFunctionCovector_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledCovectorChartMeromorphic N hN
      (lpsOriginalFilledFunctionCovector N hN F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  have hm : MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := hF x
  apply (hm.deriv z hz).congr
  filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hz)] with w hw
  exact (lpsOriginalFilledFunctionCovector_chart N hN F x w hw).symm

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledCovectorRatio
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm otherForm : LPSOriginalFilledCovectorRepresentatives N hN) :
    LPSOriginalFilledCurve N → ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun y => sectionForm y (1 : ℂ) / otherForm y (1 : ℂ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual nonzero chart derivative cancels, making the covector ratio independent of the preferred frame. -/
lemma lpsOriginalFilledCovectorRatio_chart
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm otherForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    (lpsOriginalFilledCovectorRatio N hN sectionForm otherForm ∘ (chartAt ℂ x).symm) z =
      lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z /
        lpsOriginalFilledCovectorChartCoefficient N hN otherForm x z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let y := e.symm z
  have hy : y ∈ e.source := e.map_target hz
  have he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := mdifferentiable_chart x
  let chartDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e y
  have hframe : chartDerivative (1 : ℂ) ≠ 0 := by
    intro hzero
    have hmap : mfderiv 𝓘(ℂ) 𝓘(ℂ) e y (1 : ℂ) =
        mfderiv 𝓘(ℂ) 𝓘(ℂ) e y (0 : ℂ) := by
      change chartDerivative (1 : ℂ) = chartDerivative (0 : ℂ)
      rw [map_zero]
      exact hzero
    have h10 : (1 : ℂ) = (0 : ℂ) := (he.mfderiv_injective hy) hmap
    exact one_ne_zero h10
  have hsection := lpsOriginalFilledCovectorChart_evaluate N hN sectionForm x y (1 : ℂ) hy
  have hother := lpsOriginalFilledCovectorChart_evaluate N hN otherForm x y (1 : ℂ) hy
  change sectionForm y (1 : ℂ) =
    lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x (e y) * chartDerivative 1
    at hsection
  change otherForm y (1 : ℂ) =
    lpsOriginalFilledCovectorChartCoefficient N hN otherForm x (e y) * chartDerivative 1
    at hother
  rw [e.right_inv hz] at hsection hother
  change sectionForm y (1 : ℂ) / otherForm y (1 : ℂ) = _
  rw [hsection,hother,mul_div_mul_right _ _ hframe]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovectorRatio_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm otherForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (hsection : lpsOriginalFilledCovectorChartMeromorphic N hN sectionForm)
    (hother : lpsOriginalFilledCovectorChartMeromorphic N hN otherForm) :
    lpsOriginalFilledChartMeromorphic N hN
      (lpsOriginalFilledCovectorRatio N hN sectionForm otherForm) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  apply ((hsection x z hz).div (hother x z hz)).congr
  filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hz)] with w hw
  exact (lpsOriginalFilledCovectorRatio_chart N hN sectionForm otherForm x w hw).symm

end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalJComplexDerivative_order_ne_top
    (z : ℂ) (hz : 0 < z.im) :
    meromorphicOrderAt (deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex)) z ≠ ⊤ := by
  let f : ℂ → ℂ := lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex
  have hm : MeromorphicOn (deriv f) UpperHalfPlane.upperHalfPlaneSet :=
    (lpsOriginalHolomorphic_ofComplex_meromorphic lpsOriginalJHolomorphic).deriv
  have hex : ∃ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      meromorphicOrderAt (deriv f) w ≠ ⊤ := by
    by_contra! hall
    apply lpsOriginalJMeromorphicDerivative_ne_zero
    apply Subtype.ext
    rw [lpsOriginalMeromorphicGermCoefficientDerivative_value _ _ f
      (lpsOriginalHolomorphic_ofComplex_meromorphic lpsOriginalJHolomorphic) rfl]
    exact lpsOriginalMeromorphicGerm_zero_of_orders_top UpperHalfPlane.upperHalfPlaneSet
      (deriv f) hall
  exact ((hm.exists_meromorphicOrderAt_ne_top_iff_forall_mem
    (Complex.isConnected_of_upperHalfPlane Set.Subset.rfl
      (by intro w hw; exact (show 0 < w.im from hw).le))).mp hex) z hz

/-- The actual j derivative has finite local order: interior identity principle and genuine negative cusp pole order. -/
lemma lpsOriginalFilledJDerivativeChart_order_ne_top
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    meromorphicOrderAt (deriv (lpsOriginalFilledJ N ∘ (chartAt ℂ x).symm))
      (chartAt ℂ x x) ≠ ⊤ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y =>
      let e := lpsOriginalFilledInteriorChart N hN y
      have he : lpsOriginalFilledJ N ∘ e.symm =
          lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex := by
        funext w
        rw [Function.comp_apply,lpsOriginalFilledInteriorChart_symm,
          lpsOriginalFilledJ_projection]
        rfl
      change meromorphicOrderAt (deriv (lpsOriginalFilledJ N ∘ e.symm))
        (e (Sum.inl y)) ≠ ⊤
      rw [he]
      exact lpsOriginalJComplexDerivative_order_ne_top _
        (lpsOriginalFilledInteriorChart_target_pos N hN y _
          (e.map_source (lpsOriginalFilledInteriorChart_mem N hN y)))
  | inr c =>
      change meromorphicOrderAt (deriv (lpsOriginalFilledJ N ∘
        (lpsOriginalFilledCuspChart N c).symm))
          (lpsOriginalFilledCuspChart N c (Sum.inr c)) ≠ ⊤
      rw [lpsOriginalFilledCuspChart_cusp]
      let m := lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)
      have hm : 0 < m := lpsOriginalCuspWidthNat_positive N _
      have hn : ((-(m : ℤ) : ℤ) : ℂ) ≠ 0 := by
        simp only [Int.cast_neg,Int.cast_natCast,neg_ne_zero]
        exact_mod_cast (Nat.ne_of_gt hm)
      have ho := meromorphicOrderAt_deriv_eq_sub_one hn (lpsOriginalFilledJ_cusp_order N c)
      change meromorphicOrderAt (deriv (fun q : ℂ => lpsOriginalFilledJ N
        ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q))) 0 ≠ ⊤
      rw [ho]
      exact WithTop.coe_ne_top

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovectorChart_unit_deriv_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y (1 : ℂ) : ℂ) ≠ 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let D : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y
  intro hzero
  have hmap : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y (1 : ℂ) =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y (0 : ℂ) := by
    change D (1 : ℂ) = D (0 : ℂ)
    rw [map_zero]
    exact hzero
  have h10 : (1 : ℂ) = (0 : ℂ) := ((mdifferentiable_chart x).mfderiv_injective hy) hmap
  exact one_ne_zero h10

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledJCovector_eventually_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) ≠ 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  change {y : LPSOriginalFilledCurve N |
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) ≠ 0} ∈
      Filter.codiscreteWithin (Set.univ : Set (LPSOriginalFilledCurve N))
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  simp only [Set.compl_univ,Set.union_empty]
  let e := chartAt ℂ x
  have hsrc : x ∈ e.source := mem_chart_source ℂ x
  have hm : MeromorphicAt (deriv (lpsOriginalFilledJ N ∘ e.symm)) (e x) :=
    (lpsOriginalFilledJ_chart_meromorphic N hN x (e x) (e.map_source hsrc)).deriv
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp
    (lpsOriginalFilledJDerivativeChart_order_ne_top N hN x)
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt hsrc).tendsto.mono_left
      nhdsWithin_le_nhds,e.eventually_ne_nhdsWithin hsrc⟩
  filter_upwards [ht.eventually hn,nhdsWithin_le_nhds (e.open_source.mem_nhds hsrc)]
    with y hyn hy
  let D : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e y
  have hv := lpsOriginalFilledCovectorChart_evaluate N hN
    (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)) x y (1 : ℂ) hy
  change lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) =
    lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)) x (e y) * D 1 at hv
  rw [lpsOriginalFilledFunctionCovector_chart N hN (lpsOriginalFilledJ N) x
    (e y) (e.map_source hy)] at hv
  rw [hv]
  exact mul_ne_zero hyn (lpsOriginalFilledCovectorChart_unit_deriv_ne_zero N hN x y hy)

/-- Compactness makes the actual zero-unit-evaluation set of dj finite, including its pole representative points. -/
lemma lpsOriginalFilledJCovector_critical_finite
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    {y : LPSOriginalFilledCurve N |
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 0}.Finite := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology_compactSpace N
  have hc := lpsOriginalFilledJCovector_eventually_ne_zero N hN
  change {y : LPSOriginalFilledCurve N |
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) ≠ 0} ∈
      Filter.codiscreteWithin (Set.univ : Set (LPSOriginalFilledCurve N)) at hc
  convert isCompact_univ.finite_sdiff_of_mem_codiscreteWithin hc using 1
  ext y
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The independent native zero relation: actual whole covectors vanish outside a codiscrete set. -/
def lpsOriginalFilledMeromorphicCovectorZeroSubmodule
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Submodule ℂ (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) := by
  let := lpsOriginalFilledTopology N
  exact
    { carrier := {sectionForm | ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          sectionForm.val y = 0}
      zero_mem' := by
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          (0 : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN).val y = 0
        filter_upwards with y
        rfl
      add_mem' := by
        intro sectionForm otherForm hsection hother
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          (sectionForm + otherForm).val y = 0
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), sectionForm.val y = 0 at hsection
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), otherForm.val y = 0 at hother
        filter_upwards [hsection,hother] with y hy hy'
        change sectionForm.val y + otherForm.val y = 0
        rw [hy,hy',add_zero]
      smul_mem' := by
        intro c sectionForm hsection
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          (c • sectionForm).val y = 0
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), sectionForm.val y = 0 at hsection
        filter_upwards [hsection] with y hy
        change c • sectionForm.val y = 0
        rw [hy]
        apply ContinuousLinearMap.ext
        intro v
        change c * (0 : ℂ) = 0
        exact mul_zero c }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL actual meromorphic covector sections modulo genuine global codiscrete zero. -/
abbrev LPSOriginalCompactMeromorphicCovectorGerms
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact LPSOriginalFilledMeromorphicCovectorRepresentatives N hN ⧸
    lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine inherited structure on the native original quotient. -/
instance lpsOriginalCompactMeromorphicCovectorAddCommGroup
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    AddCommGroup (LPSOriginalCompactMeromorphicCovectorGerms N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact Submodule.Quotient.addCommGroup (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine inherited structure on the native original quotient. -/
instance lpsOriginalCompactMeromorphicCovectorModule
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Module ℂ (LPSOriginalCompactMeromorphicCovectorGerms N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact Submodule.Quotient.module (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN)

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledFunctionTimesCovector
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN) :
    LPSOriginalFilledCovectorRepresentatives N hN :=
  fun y => F y • sectionForm y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledFunctionTimesCovector_chart
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x : LPSOriginalFilledCurve N) (z : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionTimesCovector N hN F sectionForm) x z =
        F ((chartAt ℂ x).symm z) *
          lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  simp [lpsOriginalFilledCovectorChartCoefficient, lpsOriginalFilledFunctionTimesCovector,
    ContinuousLinearMap.inCoordinates, ContinuousLinearMap.smul_comp]

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledFunctionTimesCovector_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hsection : lpsOriginalFilledCovectorChartMeromorphic N hN sectionForm) :
    lpsOriginalFilledCovectorChartMeromorphic N hN
      (lpsOriginalFilledFunctionTimesCovector N hN F sectionForm) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  have he : lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionTimesCovector N hN F sectionForm) x =
      fun z => F ((chartAt ℂ x).symm z) *
        lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z :=
    funext (lpsOriginalFilledFunctionTimesCovector_chart N hN F sectionForm x)
  rw [he]
  exact (hF x z hz).mul (hsection x z hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovector_eq_zero_of_unit
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (y : LPSOriginalFilledCurve N) (hy : sectionForm y (1 : ℂ) = 0) :
    sectionForm y = 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let A : ℂ →L[ℂ] ℂ := sectionForm y
  have hA : A = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := A.map_smul v (1 : ℂ)
    change A (v * 1) = v * A (1 : ℂ) at hv
    rw [mul_one,show A (1 : ℂ) = 0 from hy,mul_zero] at hv
    exact hv
  exact hA

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledMeromorphicComplexConstants
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    ℂ →+* LPSOriginalFilledMeromorphicFunctionRing N hN where
  toFun c := ⟨fun _ => c,lpsOriginalFilledChartMeromorphic_const N hN c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

section CompactRatioLinear
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local notation "R" => LPSOriginalFilledMeromorphicFunctionRing N hN
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
local instance : Algebra ℂ R := (lpsOriginalFilledMeromorphicComplexConstants N hN).toAlgebra
local instance : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalCompactMeromorphicGermAlgHom : R →ₐ[ℂ] L where
  toRingHom := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
  commutes' _ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledCovectorRatioLinearMap
    (otherForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (hother : lpsOriginalFilledCovectorChartMeromorphic N hN otherForm) : V →ₗ[ℂ] R where
  toFun sectionForm := ⟨lpsOriginalFilledCovectorRatio N hN sectionForm.val otherForm,
    lpsOriginalFilledCovectorRatio_meromorphic N hN sectionForm.val otherForm sectionForm.property hother⟩
  map_add' := by
    intro sectionForm anotherForm
    apply Subtype.ext
    funext y
    change (sectionForm.val y (1 : ℂ) + anotherForm.val y (1 : ℂ)) / otherForm y (1 : ℂ) =
      sectionForm.val y (1 : ℂ) / otherForm y (1 : ℂ) +
        anotherForm.val y (1 : ℂ) / otherForm y (1 : ℂ)
    exact add_div _ _ _
  map_smul' := by
    intro c sectionForm
    apply Subtype.ext
    funext y
    change (c * sectionForm.val y (1 : ℂ)) / otherForm y (1 : ℂ) =
      c * (sectionForm.val y (1 : ℂ) / otherForm y (1 : ℂ))
    exact mul_div_assoc _ _ _

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalCompactMeromorphicCovectorRatioMap : V →ₗ[ℂ] L :=
  (lpsOriginalCompactMeromorphicGermAlgHom N hN).toLinearMap.comp
    (lpsOriginalFilledCovectorRatioLinearMap N hN
      (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N))
      (lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
        (lpsOriginalFilledChartMeromorphic_j N hN)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ratio map kernel equals the independently defined whole-covector zero relation. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_ker :
    (lpsOriginalCompactMeromorphicCovectorRatioMap N hN).ker =
      lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  ext sectionForm
  rw [LinearMap.mem_ker]
  change lpsOriginalCompactMeromorphicCovectorRatioMap N hN sectionForm = 0 ↔
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), sectionForm.val y = 0
  constructor
  · intro hz
    have hg := congrArg Subtype.val hz
    change ((lpsOriginalFilledCovectorRatio N hN sectionForm.val
      (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N))) :
        Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = 0 at hg
    have he := Filter.Germ.coe_eq.mp hg
    filter_upwards [he,lpsOriginalFilledJCovector_eventually_ne_zero N hN] with y hy hdy
    apply lpsOriginalFilledCovector_eq_zero_of_unit N hN sectionForm.val y
    change sectionForm.val y (1 : ℂ) /
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 0 at hy
    exact (div_eq_zero_iff).mp hy |>.resolve_right hdy
  · intro hz
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hz] with y hy
    change sectionForm.val y (1 : ℂ) /
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 0
    rw [hy]
    change (0 : ℂ) / _ = 0
    exact zero_div _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual meromorphic function germ is the ratio of its actual representative times dj. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_surjective :
    Function.Surjective (lpsOriginalCompactMeromorphicCovectorRatioMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro g
  obtain ⟨F,hF⟩ := g.property
  let dj := lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)
  have hdj : lpsOriginalFilledCovectorChartMeromorphic N hN dj :=
    lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN)
  let sectionForm : V := ⟨lpsOriginalFilledFunctionTimesCovector N hN F.val dj,
    lpsOriginalFilledFunctionTimesCovector_meromorphic N hN F.val dj F.property hdj⟩
  refine ⟨sectionForm,Subtype.ext ?_⟩
  change (lpsOriginalFilledCovectorRatio N hN sectionForm.val dj :
    Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = g.val
  rw [←hF]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [lpsOriginalFilledJCovector_eventually_ne_zero N hN] with y hy
  change (F.val y * dj y (1 : ℂ)) / dj y (1 : ℂ) = F.val y
  exact mul_div_cancel_right₀ (F.val y) hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL native meromorphic covector germs are equivalent to the ENTIRE independently defined meromorphic field. -/
def lpsOriginalCompactMeromorphicCovectorLinearEquiv :
    LPSOriginalCompactMeromorphicCovectorGerms N hN ≃ₗ[ℂ] L := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup V := (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  let f := lpsOriginalCompactMeromorphicCovectorRatioMap N hN
  let Z := lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN
  have hker : f.ker = Z := lpsOriginalCompactMeromorphicCovectorRatioMap_ker N hN
  exact (Submodule.quotEquivOfEq Z f.ker hker.symm).trans
    (f.quotKerEquivOfSurjective (lpsOriginalCompactMeromorphicCovectorRatioMap_surjective N hN))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalCompactMeromorphicCovectorClass :
    V →ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup V := (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN).mkQ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalCompactMeromorphicCovectorLinearEquiv_class (sectionForm : V) :
    lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN
      (lpsOriginalCompactMeromorphicCovectorClass N hN sectionForm) =
        lpsOriginalCompactMeromorphicCovectorRatioMap N hN sectionForm := by
  rfl

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledMeromorphicFunctionTimesCovector (F : R) (sectionForm : V) : V :=
  ⟨lpsOriginalFilledFunctionTimesCovector N hN F.val sectionForm.val,
    lpsOriginalFilledFunctionTimesCovector_meromorphic N hN F.val sectionForm.val
      F.property sectionForm.property⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ratio comparison preserves actual pointwise multiplication of any function and any covector. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_functionTimes
    (F : R) (sectionForm : V) :
    lpsOriginalCompactMeromorphicCovectorRatioMap N hN
      (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F sectionForm) =
        lpsOriginalCompactMeromorphicGermAlgHom N hN F *
          lpsOriginalCompactMeromorphicCovectorRatioMap N hN sectionForm := by
  let := lpsOriginalFilledTopology N
  apply Subtype.ext
  change ((fun y => (F.val y * sectionForm.val y (1 : ℂ)) /
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ)) :
      Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) =
    (F.val : Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) *
      ((fun y => sectionForm.val y (1 : ℂ) /
        lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ)) :
          Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ)
  rw [←Filter.Germ.coe_mul]
  congr 1
  funext y
  exact mul_div_assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_dj :
    lpsOriginalCompactMeromorphicCovectorRatioMap N hN
      ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
        lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
          (lpsOriginalFilledChartMeromorphic_j N hN)⟩ = 1 := by
  let := lpsOriginalFilledTopology N
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [lpsOriginalFilledJCovector_eventually_ne_zero N hN] with y hy
  change lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) /
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 1
  exact div_self hy

open scoped ContDiff

/-- The genuine original local quotient transports upstairs codiscreteness to compact-curve codiscreteness. -/
lemma lpsOriginalFilledProjection_tendsto_codiscrete
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    Tendsto (fun z : ℂ => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))
      (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
      (Filter.codiscrete (LPSOriginalFilledCurve N)) := by
  let := lpsOriginalFilledTopology N
  rw [Filter.tendsto_def]
  intro s hs
  change {z : ℂ | lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z) ∈ s} ∈
    Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  let π := lpsOriginalHolomorphicCovectorProjection N
  have hπ : IsLocalHomeomorph π :=
    (lpsOriginalFilledTopology_interior_openEmbedding N).isLocalHomeomorph.comp
      (lpsGamma0_quotient_localHomeomorph N hN)
  have hsource : z ∈ UpperHalfPlane.ofComplex.source := by
    change z ∈ (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
      (UpperHalfPlane.coe : ℍ → ℂ)).target
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨z,hz⟩,rfl⟩
  have ho : Tendsto UpperHalfPlane.ofComplex (𝓝[≠] z)
      (𝓝[≠] (UpperHalfPlane.ofComplex z)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(UpperHalfPlane.ofComplex.continuousAt hsource).tendsto.mono_left nhdsWithin_le_nhds,
        UpperHalfPlane.ofComplex.eventually_ne_nhdsWithin hsource⟩
  have ht := (lpsOriginalLocalHomeomorph_tendsto_punctured hπ
    (UpperHalfPlane.ofComplex z)).comp ho
  have hf : ∀ᶠ y in 𝓝[≠] (π (UpperHalfPlane.ofComplex z)), y ∈ s := by
    have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hs
      (π (UpperHalfPlane.ofComplex z)) (Set.mem_univ _)
    simp only [Set.compl_univ,Set.union_empty] at hh
    exact hh
  filter_upwards [ht.eventually hf] with w hw
  exact Or.inl hw

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledMeromorphicPullback_eventually_regular
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀ᶠ z in Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let : T1Space (LPSOriginalFilledCurve N) := @T2Space.t1Space _
    (lpsOriginalFilledTopology N) (lpsOriginalFilledTopology_t2Space N)
  have he := (lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F hF).compl_mem_codiscrete
  have hp := (lpsOriginalFilledProjection_tendsto_codiscrete N hN).eventually he
  filter_upwards [hp] with z hz
  exact not_not.mp hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledFunctionCovector_pullback_regular
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) (z : ℂ) (hz : 0 < z.im)
    (hF : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledFunctionCovector N hN F
      (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ)
        (fun w : ℂ => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w))
          z (1 : ℂ)) = deriv (lpsOriginalFilledMeromorphicPullback N F) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let p : ℂ → LPSOriginalFilledCurve N :=
    fun w => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w)
  let y := p z
  let A : ℂ →L[ℂ] ℂ := lpsOriginalFilledFunctionCovector N hN F y
  let B : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) p z
  have hp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) p z :=
    ((lpsOriginalHolomorphicCovectorProjection_contMDiff N hN
      (UpperHalfPlane.ofComplex z)).mdifferentiableAt (by decide)).comp z
        (UpperHalfPlane.mdifferentiableAt_ofComplex hz)
  have hmaps : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (F ∘ p) z : ℂ →L[ℂ] ℂ) = A.comp B :=
    mfderiv_comp z hF hp
  rw [mfderiv_eq_fderiv] at hmaps
  have he := congrArg (fun linearMap : ℂ →L[ℂ] ℂ => linearMap (1 : ℂ)) hmaps
  change deriv (lpsOriginalFilledMeromorphicPullback N F) z = A (B (1 : ℂ)) at he
  exact he.symm

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalJComplexDerivative_eventually_ne_zero :
    ∀ᶠ z in Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet,
      deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
  change {z | deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0} ∈
    Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  have hm := (lpsOriginalJInvariant_ofComplex_analytic (⟨z,hz⟩ : ℍ)).meromorphicAt.deriv
  have he := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp
    (lpsOriginalJComplexDerivative_order_ne_top z hz)
  filter_upwards [he] with w hw
  exact Or.inl hw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledFunctionCovectorRatio_pullback_regular
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) (z : ℂ) (hz : 0 < z.im)
    (hF : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)))
    (hJ : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalFilledJ N)
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)))
    (hj : deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0) :
    lpsOriginalFilledMeromorphicPullback N
      (lpsOriginalFilledCovectorRatio N hN
        (lpsOriginalFilledFunctionCovector N hN F)
        (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N))) z =
      deriv (lpsOriginalFilledMeromorphicPullback N F) z /
        deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let p : ℂ → LPSOriginalFilledCurve N :=
    fun w => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w)
  let y := p z
  let a : ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) p z (1 : ℂ)
  let A : ℂ →L[ℂ] ℂ := lpsOriginalFilledFunctionCovector N hN F y
  let B : ℂ →L[ℂ] ℂ := lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y
  have hA : A a = deriv (lpsOriginalFilledMeromorphicPullback N F) z :=
    lpsOriginalFilledFunctionCovector_pullback_regular N hN F z hz hF
  have hB : B a = deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z :=
    lpsOriginalFilledFunctionCovector_pullback_regular N hN (lpsOriginalFilledJ N) z hz hJ
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0,map_zero] at hB
    exact hj hB.symm
  have hAs := A.map_smul a (1 : ℂ)
  have hBs := B.map_smul a (1 : ℂ)
  change A (a * 1) = a * A (1 : ℂ) at hAs
  change B (a * 1) = a * B (1 : ℂ) at hBs
  rw [mul_one] at hAs hBs
  change A (1 : ℂ) / B (1 : ℂ) = _
  rw [←hA,←hB,hAs,hBs]
  exact (mul_div_mul_left _ _ ha).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ratio of the actual dF, restricted upstairs, times actual j derivative equals actual F derivative. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict
    (F : R) :
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalCompactMeromorphicCovectorRatioMap N hN
        ⟨lpsOriginalFilledFunctionCovector N hN F.val,
          lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩)).val *
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) =
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let G : R := ⟨lpsOriginalFilledCovectorRatio N hN
    (lpsOriginalFilledFunctionCovector N hN F.val)
    (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)),
      lpsOriginalFilledCovectorRatio_meromorphic N hN _ _
        (lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property)
        (lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
          (lpsOriginalFilledChartMeromorphic_j N hN))⟩
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict G)).val * _ = _
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply]
  apply Subtype.ext
  change ((lpsOriginalFilledMeromorphicPullback N G.val :
    Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) *
    (lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)).val) = _
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value UpperHalfPlane.upperHalfPlaneSet
    (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)
    (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex)
    (lpsOriginalHolomorphic_ofComplex_meromorphic lpsOriginalJHolomorphic) rfl]
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value UpperHalfPlane.upperHalfPlaneSet
    (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val
    (lpsOriginalFilledMeromorphicPullback N F.val)
    (lpsOriginalFilledMeromorphicPullback_meromorphic N hN F.val F.property) rfl]
  rw [←Filter.Germ.coe_mul]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [lpsOriginalFilledMeromorphicPullback_eventually_regular N hN F.val F.property,
    lpsOriginalFilledMeromorphicPullback_eventually_regular N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN),
    lpsOriginalJComplexDerivative_eventually_ne_zero,
    Filter.self_mem_codiscreteWithin UpperHalfPlane.upperHalfPlaneSet] with z hF hJ hj hz
  have he := lpsOriginalFilledFunctionCovectorRatio_pullback_regular N hN F.val z hz
    (hF.mdifferentiableAt (by decide)) (hJ.mdifferentiableAt (by decide)) hj
  change lpsOriginalFilledMeromorphicPullback N G.val z *
    deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z =
      deriv (lpsOriginalFilledMeromorphicPullback N F.val) z
  rw [he]
  exact div_mul_cancel₀ _ hj

end CompactRatioLinear

end
end QEC.Coding.TannerLiftedProduct
