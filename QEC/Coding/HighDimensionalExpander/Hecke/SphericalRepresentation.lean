import QEC.Coding.HighDimensionalExpander.Hecke.SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible

/-!
# Analytic spherical representations of the local projective group

The predicates in this file are placed on an actual representation of the
constructed local group.  In particular, temperedness is stated using matrix
coefficients in every `L^(2 + epsilon)` space; it is not defined to mean a
Satake-parameter bound.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.SphericalHecke

open MeasureTheory
open scoped ComplexConjugate MatrixGroups LocalTopology

universe u v

/-- Restriction of a representation to the constructed maximal compact
subgroup. -/
def restrictToMaximalCompact
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) :
    Representation ℂ (maximalCompact k d) V :=
  rho.comp (maximalCompact k d).subtype

/-- The actual submodule of `K`-fixed vectors. -/
def kFixedSubmodule
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Submodule ℂ V :=
  Representation.invariants (restrictToMaximalCompact rho)

theorem mem_kFixedSubmodule_iff
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) (v : V) :
    v ∈ kFixedSubmodule rho ↔
      ∀ h : maximalCompact k d, rho h v = v :=
  Iff.rfl

/-- A representation is spherical when its actual `K`-fixed submodule is
nonzero. -/
def IsSpherical
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  kFixedSubmodule rho ≠ ⊥

/-- Smoothness: every vector has an open stabilizing subgroup. -/
def IsSmooth
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ v : V, ∃ H : Subgroup (HeckeGroup k d),
    IsOpen (H : Set (HeckeGroup k d)) ∧
      v ∈ Representation.invariants (rho.comp H.subtype)

/-- Admissibility: fixed vectors under every compact open subgroup form a
finite-dimensional complex vector space. -/
def IsAdmissible
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ H : Subgroup (HeckeGroup k d),
    IsOpen (H : Set (HeckeGroup k d)) →
      IsCompact (H : Set (HeckeGroup k d)) →
        Module.Finite ℂ (Representation.invariants (rho.comp H.subtype))

/-- Strong continuity of the orbit maps. -/
def IsStronglyContinuous
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ v : V, Continuous (fun g ↦ rho g v)

/-- Unitarity written directly as preservation of the Hilbert inner
product. -/
def IsUnitary
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ g v w, inner ℂ (rho g v) (rho g w) = inner ℂ v w

/-- Every group element of a unitary representation acts by a linear
isometry; this supplies the continuity needed to commute the action with a
Bochner integral. -/
def actionLinearIsometry
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hrho : IsUnitary rho) (g : HeckeGroup k d) : V →ₗᵢ[ℂ] V where
  toLinearMap := rho g
  norm_map' x := by
    have hsquare : ‖rho g x‖ ^ 2 = ‖x‖ ^ 2 := by
      calc
        ‖rho g x‖ ^ 2 = Complex.re (inner ℂ (rho g x) (rho g x)) :=
          norm_sq_eq_re_inner (𝕜 := ℂ) (rho g x)
        _ = Complex.re (inner ℂ x x) := congrArg Complex.re (hrho g x x)
        _ = ‖x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    nlinarith [norm_nonneg (rho g x), norm_nonneg x]

/-- A matrix coefficient of an actual local-group representation. -/
def matrixCoefficient
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) (v w : V) :
    HeckeGroup k d → ℂ :=
  fun g ↦ inner ℂ (rho g v) w

/-- The integrated action of an actual compactly supported spherical Hecke
function on an actual representation vector. -/
def integratedHeckeAction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (f : HeckeFunction k d) (v : V) : V :=
  ∫ g, f g • rho g v ∂(normalizedLocalHaarMeasure k d)

/-- Strong continuity and compact support prove all Bochner-integrability
conditions for the integrated Hecke action. -/
theorem integrable_integratedHeckeAction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hrho : IsStronglyContinuous rho)
    (f : HeckeFunction k d) (v : V) :
    Integrable (fun g ↦ f g • rho g v)
      (normalizedLocalHaarMeasure k d) := by
  have hcontinuous : Continuous (fun g ↦ f g • rho g v) :=
    f.continuous.smul (hrho v)
  have hcompact : HasCompactSupport (fun g ↦ f g • rho g v) :=
    f.hasCompactSupport.smul_right
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

/-- For a strongly continuous representation, integration gives a genuine
linear action of every spherical Hecke function. -/
def integratedHeckeActionLinear
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hrho : IsStronglyContinuous rho) (f : HeckeFunction k d) :
    V →ₗ[ℂ] V where
  toFun := integratedHeckeAction rho f
  map_add' v w := by
    simp only [integratedHeckeAction, map_add, smul_add]
    exact integral_add
      (integrable_integratedHeckeAction rho hrho f v)
      (integrable_integratedHeckeAction rho hrho f w)
  map_smul' c v := by
    simp only [integratedHeckeAction, map_smul, RingHom.id_apply]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with g
    rw [smul_comm]

/-- The concrete `L¹` size controlling every unitary integrated Hecke
action. -/
def heckeL1Norm
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : ℝ :=
  ∫ g, ‖f g‖ ∂normalizedLocalHaarMeasure k d

theorem heckeL1Norm_nonneg
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : 0 ≤ heckeL1Norm f := by
  exact integral_nonneg fun _ => norm_nonneg _

/-- The integrated action of a compactly supported Hecke function in a
unitary representation is bounded by its actual `L¹` norm. -/
theorem norm_integratedHeckeAction_le
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hunitary : IsUnitary rho) (f : HeckeFunction k d) (v : V) :
    ‖integratedHeckeAction rho f v‖ ≤ heckeL1Norm f * ‖v‖ := by
  refine (norm_integral_le_integral_norm
    (fun g => f g • rho g v)).trans_eq ?_
  change (∫ g, ‖f g • rho g v‖ ∂normalizedLocalHaarMeasure k d) =
    (∫ g, ‖f g‖ ∂normalizedLocalHaarMeasure k d) * ‖v‖
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with g
  rw [norm_smul]
  congr 1
  exact (actionLinearIsometry rho hunitary g).norm_map v

/-- The bounded integrated action as a genuine continuous linear operator. -/
def integratedHeckeActionContinuousLinear
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) : V →L[ℂ] V :=
  (integratedHeckeActionLinear rho hcontinuous f).mkContinuous
    (heckeL1Norm f) (norm_integratedHeckeAction_le rho hunitary f)

@[simp]
theorem integratedHeckeActionContinuousLinear_apply
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) (v : V) :
    integratedHeckeActionContinuousLinear rho hcontinuous hunitary f v =
      integratedHeckeAction rho f v :=
  rfl

/-- Integration respects the proved Hecke involution: in every strongly
continuous unitary representation, the operator integrated from `star f` is
the Hilbert-space adjoint of the operator integrated from `f`. -/
theorem inner_integratedHeckeAction_eq_star
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hd : 0 < d) (f : HeckeFunction k d) (v w : V) :
    inner ℂ (integratedHeckeAction rho f v) w =
      inner ℂ v (integratedHeckeAction rho (star f) w) := by
  letI : MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) :=
    normalizedLocalHaarMeasure_isInvInvariant k hd
  let μ := normalizedLocalHaarMeasure k d
  let F : HeckeGroup k d → V := fun g ↦ f g • rho g v
  let Fstar : HeckeGroup k d → V := fun g ↦ star f g • rho g w
  have hF : Integrable F μ :=
    integrable_integratedHeckeAction rho hcontinuous f v
  have hFstar : Integrable Fstar μ :=
    integrable_integratedHeckeAction rho hcontinuous (star f) w
  have hintegral_left :
      inner ℂ (∫ g, F g ∂μ) w = ∫ g, inner ℂ (F g) w ∂μ := by
    calc
      inner ℂ (∫ g, F g ∂μ) w =
          conj (inner ℂ w (∫ g, F g ∂μ)) := by simp
      _ = conj (∫ g, inner ℂ w (F g) ∂μ) := by
        rw [integral_inner hF w]
      _ = ∫ g, conj (inner ℂ w (F g)) ∂μ := by
        rw [integral_conj]
      _ = ∫ g, inner ℂ (F g) w ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        simp
  have hunit (g : HeckeGroup k d) :
      inner ℂ (rho g⁻¹ v) w = inner ℂ v (rho g w) := by
    have h := hunitary g (rho g⁻¹ v) w
    have hcancel : rho g (rho g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hcancel] at h
    exact h.symm
  change inner ℂ (∫ g, F g ∂μ) w = inner ℂ v (∫ g, Fstar g ∂μ)
  calc
    inner ℂ (∫ g, F g ∂μ) w =
        ∫ g, inner ℂ (F g) w ∂μ := hintegral_left
    _ = ∫ g, inner ℂ (F g⁻¹) w ∂μ :=
      (integral_inv_eq_self (fun g ↦ inner ℂ (F g) w) μ).symm
    _ = ∫ g, inner ℂ v (Fstar g) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      simp only [F, Fstar, HeckeFunction.star_apply]
      rw [inner_smul_left, inner_smul_right, hunit g]
    _ = inner ℂ v (∫ g, Fstar g ∂μ) := integral_inner hFstar v

/-- A bi-`K`-invariant Hecke function sends every vector to the actual
`K`-fixed submodule. -/
theorem integratedHeckeAction_mem_kFixedSubmodule
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) (v : V) :
    integratedHeckeAction rho f v ∈ kFixedSubmodule rho := by
  rw [mem_kFixedSubmodule_iff]
  intro h
  let L := actionLinearIsometry rho hunitary (h : HeckeGroup k d)
  let phi : HeckeGroup k d → V := fun g ↦ f g • rho g v
  have hphi : Integrable phi (normalizedLocalHaarMeasure k d) :=
    integrable_integratedHeckeAction rho hcontinuous f v
  change rho (h : HeckeGroup k d)
      (∫ g, phi g ∂(normalizedLocalHaarMeasure k d)) =
    ∫ g, phi g ∂(normalizedLocalHaarMeasure k d)
  calc
    rho (h : HeckeGroup k d)
        (∫ g, phi g ∂(normalizedLocalHaarMeasure k d)) =
        ∫ g, L (phi g) ∂(normalizedLocalHaarMeasure k d) := by
          exact (L.integral_comp_comm phi).symm
    _ = ∫ g, f g • rho ((h : HeckeGroup k d) * g) v
          ∂(normalizedLocalHaarMeasure k d) := by
      apply integral_congr_ae
      filter_upwards with g
      simp only [L, phi, actionLinearIsometry, map_smul]
      change f g • rho (h : HeckeGroup k d) (rho g v) =
        f g • rho ((h : HeckeGroup k d) * g) v
      rw [← Module.End.mul_apply, ← map_mul]
    _ = ∫ g, phi g ∂(normalizedLocalHaarMeasure k d) := by
      let F : HeckeGroup k d → V :=
        fun g ↦ f g • rho ((h : HeckeGroup k d) * g) v
      calc
        (∫ g, f g • rho ((h : HeckeGroup k d) * g) v
            ∂(normalizedLocalHaarMeasure k d)) =
            ∫ g, F ((h : HeckeGroup k d)⁻¹ * g)
              ∂(normalizedLocalHaarMeasure k d) :=
          (integral_mul_left_eq_self F (h : HeckeGroup k d)⁻¹).symm
        _ = ∫ g, phi g ∂(normalizedLocalHaarMeasure k d) := by
          apply integral_congr_ae
          filter_upwards with g
          simp only [F, phi]
          have hf : f ((h : HeckeGroup k d)⁻¹ * g) = f g :=
            f.left_invariant (h : HeckeGroup k d)⁻¹
              ((maximalCompact k d).inv_mem h.property) g
          rw [hf]
          simp

/-- The `r`-th fundamental Hecke operator on an actual strongly continuous
representation. -/
def fundamentalRepresentationAction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (r : ℕ) : V →ₗ[ℂ] V :=
  integratedHeckeActionLinear rho hcontinuous
    (HeckeFunction.fundamentalHeckeFunction k d r)

/-- The fundamental action is the integral over the actual Cartan double
coset. -/
theorem fundamentalRepresentationAction_apply
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (r : ℕ) (v : V) :
    fundamentalRepresentationAction rho hcontinuous r v =
      ∫ g in fundamentalDoubleCoset k d r, rho g v
        ∂(normalizedLocalHaarMeasure k d) := by
  change (∫ g, (fundamentalDoubleCoset k d r).indicator (fun _ ↦ (1 : ℂ)) g •
      rho g v ∂(normalizedLocalHaarMeasure k d)) = _
  have hfun : (fun g : HeckeGroup k d ↦
      (fundamentalDoubleCoset k d r).indicator (fun _ ↦ (1 : ℂ)) g • rho g v) =
      (fundamentalDoubleCoset k d r).indicator (fun g ↦ rho g v) := by
    funext g
    by_cases hg : g ∈ fundamentalDoubleCoset k d r <;> simp [hg]
  calc
    (∫ g, (fundamentalDoubleCoset k d r).indicator (fun _ ↦ (1 : ℂ)) g •
        rho g v ∂(normalizedLocalHaarMeasure k d)) =
        ∫ g, (fundamentalDoubleCoset k d r).indicator (fun g ↦ rho g v) g
          ∂(normalizedLocalHaarMeasure k d) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun g ↦ congrFun hfun g)
    _ = ∫ g in fundamentalDoubleCoset k d r, rho g v
          ∂(normalizedLocalHaarMeasure k d) := by
      rw [integral_indicator]
      exact (fundamentalDoubleCoset_isOpen k d r).measurableSet

/-- A concrete involution identity for fundamental Hecke functions becomes
the corresponding Hilbert-space adjoint identity for their represented
operators. -/
theorem inner_fundamentalRepresentationAction_eq_of_star
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hd : 0 < d) (r s : ℕ)
    (hstar : star (HeckeFunction.fundamentalHeckeFunction k d r) =
      HeckeFunction.fundamentalHeckeFunction k d s)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous r v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous s w) := by
  change inner ℂ
      (integratedHeckeAction rho
        (HeckeFunction.fundamentalHeckeFunction k d r) v) w =
    inner ℂ v
      (integratedHeckeAction rho
        (HeckeFunction.fundamentalHeckeFunction k d s) w)
  rw [← hstar]
  exact inner_integratedHeckeAction_eq_star
    rho hcontinuous hunitary hd _ v w

theorem inner_fundamentalRepresentationAction_rankThree_one
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 3) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 1 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 2 w) :=
  inner_fundamentalRepresentationAction_eq_of_star
    rho hcontinuous hunitary (by omega) 1 2
      (HeckeFunction.star_fundamentalHeckeFunction_rankThree_one k) v w

theorem inner_fundamentalRepresentationAction_rankThree_two
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 3) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 2 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 1 w) :=
  inner_fundamentalRepresentationAction_eq_of_star
    rho hcontinuous hunitary (by omega) 2 1
      (HeckeFunction.star_fundamentalHeckeFunction_rankThree_two k) v w

theorem inner_fundamentalRepresentationAction_rankFour_one
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 4) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 1 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 3 w) :=
  inner_fundamentalRepresentationAction_eq_of_star
    rho hcontinuous hunitary (by omega) 1 3
      (HeckeFunction.star_fundamentalHeckeFunction_rankFour_one k) v w

theorem inner_fundamentalRepresentationAction_rankFour_two
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 4) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 2 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 2 w) :=
  inner_fundamentalRepresentationAction_eq_of_star
    rho hcontinuous hunitary (by omega) 2 2
      (HeckeFunction.star_fundamentalHeckeFunction_rankFour_two k) v w

theorem inner_fundamentalRepresentationAction_rankFour_three
    {k : Type u} [Field k] [Finite k]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k 4) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (v w : V) :
    inner ℂ (fundamentalRepresentationAction rho hcontinuous 3 v) w =
      inner ℂ v (fundamentalRepresentationAction rho hcontinuous 1 w) :=
  inner_fundamentalRepresentationAction_eq_of_star
    rho hcontinuous hunitary (by omega) 3 1
      (HeckeFunction.star_fundamentalHeckeFunction_rankFour_three k) v w

/-- The scalar read from a unit spherical vector by an actual integrated
Hecke operator. -/
def sphericalHeckeEigenvalue
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho)
    (f : HeckeFunction k d) (v : V) : ℂ :=
  inner ℂ v (integratedHeckeActionLinear rho hcontinuous f v)

/-- If the actual `K`-fixed subspace is one-dimensional, every integrated
spherical Hecke operator acts on a unit `K`-fixed vector by the scalar just
constructed from the inner product. -/
theorem integratedHeckeAction_eq_eigenvalue_smul
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (hline : Module.finrank ℂ (kFixedSubmodule rho) = 1)
    (f : HeckeFunction k d) (v : V)
    (hvfixed : v ∈ kFixedSubmodule rho) (hvnorm : ‖v‖ = 1) :
    integratedHeckeActionLinear rho hcontinuous f v =
      sphericalHeckeEigenvalue rho hcontinuous f v • v := by
  have hvzero : v ≠ 0 := by
    intro hv
    simp [hv] at hvnorm
  let vK : kFixedSubmodule rho := ⟨v, hvfixed⟩
  let AvK : kFixedSubmodule rho :=
    ⟨integratedHeckeActionLinear rho hcontinuous f v,
      integratedHeckeAction_mem_kFixedSubmodule rho hcontinuous hunitary f v⟩
  have hvKzero : vK ≠ 0 := by
    intro h
    apply hvzero
    exact Subtype.ext_iff.mp h
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hvKzero AvK
  have haction : integratedHeckeActionLinear rho hcontinuous f v = c • v := by
    exact congrArg Subtype.val hc.symm
  rw [haction]
  have hinner : inner ℂ v (c • v) = c := by
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm]
  simp only [sphericalHeckeEigenvalue, haction, hinner]

/-- Analytic temperedness in the LSV normalization: one nonzero matrix
coefficient belongs to `L^(2 + epsilon)` for every positive `epsilon`. -/
def IsTempered
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∃ v w : V, v ≠ 0 ∧ w ≠ 0 ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      MemLp (matrixCoefficient rho v w)
        (ENNReal.ofReal (2 + epsilon)) (normalizedLocalHaarMeasure k d)

/-- The exact conjunction used by the local Satake criterion.  This is a
predicate, not a structure carrying a desired conclusion. -/
def IsIrreducibleUnitarySpherical
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  Representation.IsIrreducible rho ∧ IsUnitary rho ∧ IsSpherical rho

end QEC.Coding.HighDimensionalExpander.SphericalHecke
