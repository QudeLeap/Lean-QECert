import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicGerms
import QEC.Coding.ExpanderCodes.LPSOriginalModularFunction
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiation of genuine original meromorphic germs

Differentiate arbitrary actual meromorphic representatives and prove independence of
the representative. Actual holomorphic differentiation is preserved; the original
nonconstant j has nonzero derivative in the genuine upper-half-plane germ field.

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
noncomputable section

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalMeromorphicGermComplexConstants (U : Set ℂ) :
    ℂ →+* LPSOriginalMeromorphicGermRing U where
  toFun c := ⟨((fun _ : ℂ => c) : Filter.Germ (Filter.codiscreteWithin U) ℂ),
    (fun _ : ℂ => c), MeromorphicOn.const c, rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual derivative germ of a chosen meromorphic representative; independence is proved below. -/
def lpsOriginalMeromorphicGermCoefficientDerivative (U : Set ℂ)
    (A : LPSOriginalMeromorphicGermRing U) : LPSOriginalMeromorphicGermRing U :=
  ⟨(deriv A.property.choose : Filter.Germ (Filter.codiscreteWithin U) ℂ),
    deriv A.property.choose, A.property.choose_spec.1.deriv, rfl⟩

/-- The derivative agrees with EVERY actual meromorphic representative of the same germ. -/
lemma lpsOriginalMeromorphicGermCoefficientDerivative_value
    (U : Set ℂ) (A : LPSOriginalMeromorphicGermRing U)
    (f : ℂ → ℂ) (hf : MeromorphicOn f U)
    (he : A.val = (f : Filter.Germ (Filter.codiscreteWithin U) ℂ)) :
    (lpsOriginalMeromorphicGermCoefficientDerivative U A).val =
      (deriv f : Filter.Germ (Filter.codiscreteWithin U) ℂ) := by
  apply Filter.Germ.coe_eq.mpr
  exact A.property.choose_spec.1.deriv_eventuallyEq_codiscreteWithin hf
    (Filter.Germ.coe_eq.mp (A.property.choose_spec.2.symm.trans he))

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalMeromorphicGermCoefficientDerivative_add
    (U : Set ℂ) (A B : LPSOriginalMeromorphicGermRing U) :
    lpsOriginalMeromorphicGermCoefficientDerivative U (A+B) =
      lpsOriginalMeromorphicGermCoefficientDerivative U A +
        lpsOriginalMeromorphicGermCoefficientDerivative U B := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A+B).val = (f+g : Filter.Germ (Filter.codiscreteWithin U) ℂ) := by
    change A.val+B.val = _
    rw [he,he']
  apply Subtype.ext
  change (lpsOriginalMeromorphicGermCoefficientDerivative U (A+B)).val =
    (lpsOriginalMeromorphicGermCoefficientDerivative U A).val +
      (lpsOriginalMeromorphicGermCoefficientDerivative U B).val
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value U (A+B) (f+g) (hf.add hg) hab,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U A f hf he,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U B g hg he']
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.analyticAt_mem_codiscreteWithin,
    hg.analyticAt_mem_codiscreteWithin] with z hz hz'
  exact deriv_add hz.differentiableAt hz'.differentiableAt

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalMeromorphicGermCoefficientDerivative_mul
    (U : Set ℂ) (A B : LPSOriginalMeromorphicGermRing U) :
    lpsOriginalMeromorphicGermCoefficientDerivative U (A*B) =
      A*lpsOriginalMeromorphicGermCoefficientDerivative U B +
        B*lpsOriginalMeromorphicGermCoefficientDerivative U A := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A*B).val = (f*g : Filter.Germ (Filter.codiscreteWithin U) ℂ) := by
    change A.val*B.val = _
    rw [he,he']
  apply Subtype.ext
  change (lpsOriginalMeromorphicGermCoefficientDerivative U (A*B)).val =
    A.val*(lpsOriginalMeromorphicGermCoefficientDerivative U B).val +
      B.val*(lpsOriginalMeromorphicGermCoefficientDerivative U A).val
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value U (A*B) (f*g) (hf.mul hg) hab,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U A f hf he,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U B g hg he',he,he']
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.analyticAt_mem_codiscreteWithin,
    hg.analyticAt_mem_codiscreteWithin] with z hz hz'
  simpa only [Pi.mul_apply,Pi.add_apply,mul_comm,add_comm] using
    deriv_mul hz.differentiableAt hz'.differentiableAt

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalMeromorphicGermCoefficientDerivative_constant
    (U : Set ℂ) (c : ℂ) :
    lpsOriginalMeromorphicGermCoefficientDerivative U
      (lpsOriginalMeromorphicGermComplexConstants U c) = 0 := by
  apply Subtype.ext
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value U _
    (fun _ : ℂ => c) (MeromorphicOn.const c) rfl]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with z
  simp only [deriv_const]

section ComplexDerivation
variable (U : Set ℂ)
local instance : Algebra ℂ (LPSOriginalMeromorphicGermRing U) :=
  (lpsOriginalMeromorphicGermComplexConstants U).toAlgebra

/-- The genuine complex-linear Leibniz derivation on all meromorphic germs. -/
def lpsOriginalMeromorphicGermCoefficientDerivation :
    Derivation ℂ (LPSOriginalMeromorphicGermRing U)
      (LPSOriginalMeromorphicGermRing U) := by
  let D : LPSOriginalMeromorphicGermRing U →ₗ[ℂ] LPSOriginalMeromorphicGermRing U :=
    { toFun := lpsOriginalMeromorphicGermCoefficientDerivative U
      map_add' := lpsOriginalMeromorphicGermCoefficientDerivative_add U
      map_smul' := by
        intro c A
        change lpsOriginalMeromorphicGermCoefficientDerivative U
          (lpsOriginalMeromorphicGermComplexConstants U c * A) =
            lpsOriginalMeromorphicGermComplexConstants U c *
              lpsOriginalMeromorphicGermCoefficientDerivative U A
        rw [lpsOriginalMeromorphicGermCoefficientDerivative_mul,
          lpsOriginalMeromorphicGermCoefficientDerivative_constant,mul_zero,add_zero] }
  exact Derivation.mk' D (fun A B =>
    lpsOriginalMeromorphicGermCoefficientDerivative_mul U A B)

end ComplexDerivation
end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section

/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalHolomorphicCoefficientDerivative (f : LPSOriginalHolomorphicRing) :
    LPSOriginalHolomorphicRing :=
  ⟨fun τ : ℍ => deriv (f.val ∘ UpperHalfPlane.ofComplex) (τ : ℂ), by
    intro τ
    apply UpperHalfPlane.mdifferentiableAt_iff.mpr
    have ha := (UpperHalfPlane.mdifferentiable_iff.mp f.property).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
    exact (ha.deriv (τ : ℂ) τ.im_pos).differentiableAt.congr_of_eventuallyEq
      ((UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos).fun_comp
        (deriv (f.val ∘ UpperHalfPlane.ofComplex)))⟩

/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalHolomorphicCoefficientDerivative_germ (f : LPSOriginalHolomorphicRing) :
    lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalHolomorphicCoefficientDerivative f) =
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalHolomorphicToMeromorphicGerm f) := by
  apply Subtype.ext
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value _ _
    (f.val ∘ UpperHalfPlane.ofComplex) (lpsOriginalHolomorphic_ofComplex_meromorphic f) rfl]
  apply Filter.Germ.coe_eq.mpr
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  filter_upwards [nhdsWithin_le_nhds
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)] with w hw
  exact Or.inl (by
    change deriv (f.val ∘ UpperHalfPlane.ofComplex)
      (UpperHalfPlane.ofComplex w : ℂ) = deriv (f.val ∘ UpperHalfPlane.ofComplex) w
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw])

/-- The actual j derivative is nonzero by the identity principle and genuine j nonconstancy. -/
lemma lpsOriginalJMeromorphicDerivative_ne_zero :
    lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) ≠ 0 := by
  intro h
  have hd : lpsOriginalHolomorphicCoefficientDerivative lpsOriginalJHolomorphic = 0 := by
    apply lpsOriginalHolomorphicToMeromorphicGerm_injective
    rw [lpsOriginalHolomorphicCoefficientDerivative_germ, h, map_zero]
  have hd0 := congrArg Subtype.val hd
  have hz : UpperHalfPlane.upperHalfPlaneSet.EqOn
      (deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex)) 0 := by
    intro z hz
    have he := congrFun hd0 (⟨z,hz⟩ : ℍ)
    exact he
  have hconn := (Complex.isConnected_of_upperHalfPlane (r := 0) Set.Subset.rfl
    (by intro z hz; exact (show 0 < z.im from hz).le)).isPreconnected
  have hconst := UpperHalfPlane.isOpen_upperHalfPlaneSet.exists_is_const_of_deriv_eq_zero
    hconn (UpperHalfPlane.mdifferentiable_iff.mp lpsOriginalJInvariant_holomorphic) hz
  obtain ⟨c,hc⟩ := hconst
  apply lpsOriginalJInvariant_nonconstant
  refine ⟨c, fun τ => ?_⟩
  simpa only [Function.comp_apply,UpperHalfPlane.ofComplex_apply] using hc (τ : ℂ) τ.im_pos

end
end QEC.Coding.TannerLiftedProduct
