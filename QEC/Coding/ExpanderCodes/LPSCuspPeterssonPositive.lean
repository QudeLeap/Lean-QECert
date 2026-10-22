import QEC.Coding.ExpanderCodes.LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# LPSCuspPeterssonPositive

Positive definiteness and squared Cauchy-Schwarz for the actual convergent finite-coset Petersson integral. Positive hyperbolic density, the closure of the real modular fundamental-domain interior and genuine modular orbit coverage prove nondegeneracy. No assumed positivity or competing global norm instance.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate

noncomputable section
/-- The actual hyperbolic measure is positive on every nonempty open set. -/
lemma lpsPetersson_volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  let μ : Measure ℍ := volume.comap UpperHalfPlane.coe
  let w : ℍ → ℝ≥0∞ := fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)^2)
  have hm : Measurable w := by
    dsimp [w]
    fun_prop
  have hw : ∀z,w z≠0 := by
    intro z
    have hz : NNReal.mk z.im z.im_pos.le≠0 := by
      intro h
      have hr := congrArg (fun x:ℝ≥0 => (x:ℝ)) h
      exact z.im_ne_zero hr
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (by simpa only [one_div] using inv_ne_zero hz))
  have hac : μ ≪ (volume : Measure ℍ) :=
    withDensity_absolutelyContinuous' hm.aemeasurable (Eventually.of_forall hw)
  let : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  exact ⟨fun U hU hne hzero => hU.measure_ne_zero μ hne (hac hzero)⟩

/-- Zero true self-mass forces the continuous modular-invariant density to vanish everywhere. -/
lemma lpsCuspPeterssonDensity_eq_zero_of_integral_eq_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : ∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ=0) :
    lpsCuspPeterssonDensity N f=0 := by
  let : (volume : Measure ℍ).IsOpenPosMeasure := lpsPetersson_volume_isOpenPosMeasure
  have hae : lpsCuspPeterssonDensity N f =ᵐ[volume.restrict ModularGroup.fd] 0 :=
    (integral_eq_zero_iff_of_nonneg (lpsCuspPeterssonDensity_nonneg N f)
      (lpsCuspPeterssonDensity_integrable N f)).mp h
  have hfd : EqOn (lpsCuspPeterssonDensity N f) 0 ModularGroup.fd := by
    apply Measure.eqOn_of_ae_eq hae (lpsCuspPeterssonDensity_continuous N f).continuousOn
      continuous_const.continuousOn
    rw [←ModularGroup.fdo_eq_interior_fd,←ModularGroup.fd_eq_closure_fdo]
  funext τ
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  rw [←lpsCuspPeterssonDensity_invariant N f g τ]
  exact hfd hg

/-- The identity-coset contribution forces an actual cusp form with zero true self-mass to be zero. -/
lemma lpsWeightTwoCusp_eq_zero_of_peterssonMass_eq_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : ∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ=0) : f=0 := by
  have hz := lpsCuspPeterssonDensity_eq_zero_of_integral_eq_zero N f h
  ext τ
  have hi := lpsCuspPeterssonDensity_individual_le N f τ
  rw [hz] at hi
  change ‖f τ‖^2*τ.im^2≤0 at hi
  have hn : ‖f τ‖=0 := by
    by_contra hn
    have hp : 0<‖f τ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_lt_of_ge hi) (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos τ.im_pos))
  exact norm_eq_zero.mp hn

/-- The actual convergent Petersson integral is positive definite. -/
lemma lpsCuspPeterssonPairing_self_eq_zero_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f f=0 ↔ f=0 := by
  constructor
  · intro h
    apply lpsWeightTwoCusp_eq_zero_of_peterssonMass_eq_zero N f
    rw [lpsCuspPeterssonPairing_self_eq] at h
    exact Complex.ofReal_eq_zero.mp h
  · rintro rfl
    have h := lpsCuspPeterssonPairing_smul_right N 0 0 (0:ℂ)
    simpa using h

/-- The genuine positive-definite integral defines an inner-product core, without changing global norm instances. -/
@[instance_reducible] def lpsCuspPeterssonCore (N : ℕ) [NeZero N] :
    InnerProductSpace.Core ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) where
  inner := lpsCuspPeterssonPairing N
  conj_inner_symm f g := by rw [lpsCuspPeterssonPairing_conj,conj_conj]
  re_inner_nonneg := lpsCuspPeterssonPairing_self_nonneg N
  add_left := lpsCuspPeterssonPairing_add_left N
  smul_left f g c := lpsCuspPeterssonPairing_smul_left N f g c
  definite f := (lpsCuspPeterssonPairing_self_eq_zero_iff N f).mp

/-- Squared Cauchy-Schwarz for the actual convergent Petersson pairing. -/
lemma lpsCuspPeterssonPairing_norm_sq_le (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ‖lpsCuspPeterssonPairing N f g‖^2 ≤
      (lpsCuspPeterssonPairing N f f).re*(lpsCuspPeterssonPairing N g g).re := by
  let : InnerProductSpace.Core ℂ
    (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) := lpsCuspPeterssonCore N
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜:=ℂ) f g
  rw [InnerProductSpace.Core.norm_inner_symm g f] at h
  change ‖lpsCuspPeterssonPairing N f g‖*‖lpsCuspPeterssonPairing N f g‖ ≤ (lpsCuspPeterssonPairing N f f).re*(lpsCuspPeterssonPairing N g g).re at h
  simpa only [pow_two] using h

/-- The real integral of the actual square density vanishes exactly for the zero form. -/
lemma lpsCuspPeterssonMass_eq_zero_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ)=0 ↔ f=0 := by
  constructor
  · exact lpsWeightTwoCusp_eq_zero_of_peterssonMass_eq_zero N f
  · intro h
    have hp := (lpsCuspPeterssonPairing_self_eq_zero_iff N f).mpr h
    rw [lpsCuspPeterssonPairing_self_eq] at hp
    exact Complex.ofReal_eq_zero.mp hp

/-- The actual square integral is strictly positive exactly when the cusp form is nonzero. -/
lemma lpsCuspPeterssonMass_pos_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    0<(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ) ↔ f≠0 := by
  have hp : 0≤(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ) :=
    integral_nonneg (lpsCuspPeterssonDensity_nonneg N f)
  rw [lt_iff_le_and_ne, and_iff_right hp, ne_comm, ne_eq, lpsCuspPeterssonMass_eq_zero_iff]

end
end QEC.Coding.TannerLiftedProduct
