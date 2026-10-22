import QEC.Coding.ExpanderCodes.LPSOriginalModularFunction
import QEC.Coding.ExpanderCodes.LPSEisensteinDifference

/-!
# LPSOriginalDilatedModularFunction

Genuine j(Ntau) for every positive integer level descends through the SAME
original Gamma0(N) orbit quotient. Actual integral dilation-conjugate matrices
prove invariance and the translated-group inclusion. The TRUE minimum cusp
width is a strict period of actual twice-translated E4 and Delta forms, so
Mathlib cusp boundedness gives analytic coordinate coefficients. Their genuine
meromorphic ratio recovers the original function and proves meromorphy in every
actual preferred-chart target, including all true added cusps.

Pinned Mathlib general-GL slash uses determinant to weight minus1: recovering j
from translated E4 cubed divided by Delta requires determinant squared, here
N squared. A finite value0 at a cusp only chooses a germ representative.

This supplies the original j(Ntau) ingredient of the X0(N) route (Milne MF110
Theorem6.1/section7), motivated by PK22 main.tex ex:Xpq. The original j/jN
modular equation, function-field generation, rational normalization, every-prime
away-level good reduction, geometric Frobenius/Hecke/Weil magnitude and public
PK22 main theorem remain unproved. No model or spectral bound is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

/-- The actual original j(Ntau) uses the positive integer affine dilation; used by Gamma0 descent, q limits and all chart pullbacks. -/
def lpsOriginalJDilated (N : ℕ) (hN : 0<N) (τ : ℍ) : ℂ :=
  lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • τ)

/-- The actual dilated upper-half-plane point has complex value N times tau; exercised by the original composite-level root fixture. -/
lemma lpsOriginalJDilated_coe (N : ℕ) (hN : 0<N) (τ : ℍ) :
    (((lpsE2AffineMatrix N hN 0 • τ):ℍ):ℂ)=(N:ℂ)*(τ:ℂ) := by
  simpa only [Complex.ofReal_zero,add_zero] using lpsE2AffineMatrix_action N hN 0 τ

/-- Actual integral Gamma0 lower-left divisibility constructs the genuine SL dilation conjugate and proves j(Ntau) invariance; used by real Gamma0 invariance. -/
lemma lpsOriginalJDilated_integral_Gamma0_invariant (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    lpsOriginalJDilated N hN (γ•τ)=lpsOriginalJDilated N hN τ := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdvd : (N:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp hγ
  obtain ⟨k,hk⟩ := hdvd
  let δ := lpsE2DilationConjugate N γ k hk
  have ha := lpsE2DilationConjugate_action N hN γ δ k hk rfl rfl rfl rfl τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • (γ•τ))=_
  rw [←ha]
  exact lpsOriginalJInvariant_SL_invariant (Matrix.SpecialLinearGroup.mapGL ℝ δ)
    ⟨δ,rfl⟩ (lpsE2AffineMatrix N hN 0 • τ)

/-- The original real Gamma0 subgroup inherits genuine j(Ntau) invariance; used by its literal orbit quotient lift. -/
lemma lpsOriginalJDilated_Gamma0_invariant (N : ℕ) (hN : 0<N)
    (g : GL (Fin 2) ℝ) (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (τ : ℍ) : lpsOriginalJDilated N hN (g•τ)=lpsOriginalJDilated N hN τ := by
  obtain ⟨γ,hγ,rfl⟩ := hg
  exact lpsOriginalJDilated_integral_Gamma0_invariant N hN γ hγ τ

/-- The actual positive-determinant dilation and genuine holomorphic j prove j(Ntau) holomorphic on the upper half plane; used by interior chart analyticity. -/
lemma lpsOriginalJDilated_holomorphic (N : ℕ) (hN : 0<N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalJDilated N hN) := by
  have hp : 0<(lpsE2AffineMatrix N hN 0).det.val := by
    rw [lpsE2AffineMatrix_det];exact_mod_cast hN
  exact lpsOriginalJInvariant_holomorphic.comp (UpperHalfPlane.mdifferentiable_smul hp)

/-- The literal original Gamma0 orbit quotient lift of genuine j(Ntau); used by projection recovery, quotient nonconstancy and the filled function. -/
def lpsOriginalJDilatedQuotient (N : ℕ) (hN : 0<N) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → ℂ :=
  Quotient.lift (lpsOriginalJDilated N hN) (by
    intro τ σ h
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ τ σ at h
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at h
    obtain ⟨g,hg⟩ := h
    rw [←hg]
    exact lpsOriginalJDilated_Gamma0_invariant N hN g.val g.property σ)

/-- Actual original quotient-projection recovery of j(Ntau); used by the root fixture and the filled restriction. -/
lemma lpsOriginalJDilatedQuotient_projection (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalJDilatedQuotient N hN ⟦τ⟧=lpsOriginalJDilated N hN τ := rfl

/-- True nome dilation gives q^N*j(Ntau)=K(q^N); used by its actual limit and the root fixture. -/
lemma lpsOriginalJDilated_qParam_pullback (N : ℕ) (hN : 0<N) (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)^N*lpsOriginalJDilated N hN τ=
      lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ:ℂ)^N) := by
  simpa only [lpsOriginalJDilated,lpsE2AffineMatrix_qParam] using
    lpsOriginalJInvariant_qParam_pullback (lpsE2AffineMatrix N hN 0 • τ)

/-- The true q^N*j(Ntau) limit is1; used by nonconstancy. -/
lemma lpsOriginalJDilated_q_limit (N : ℕ) (hN : 0<N) :
    Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ:ℂ)^N*lpsOriginalJDilated N hN τ)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ:ℂ)^N)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [zero_pow hN.ne'] using
      (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).pow N
  have h := lpsOriginalJQCoefficient_analytic_zero.continuousAt.tendsto.comp hq
  rw [lpsOriginalJQCoefficient_zero] at h
  exact h.congr (fun τ => (lpsOriginalJDilated_qParam_pullback N hN τ).symm)

/-- Nonconstancy of actual j(Ntau) follows from contradictory zero and one limits; used by quotient and filled nonconstancy. -/
lemma lpsOriginalJDilated_nonconstant (N : ℕ) (hN : 0<N) :
    ¬∃ c : ℂ, ∀ τ : ℍ, lpsOriginalJDilated N hN τ=c := by
  rintro ⟨c,hc⟩
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ:ℂ)^N)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [zero_pow hN.ne'] using
      (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).pow N
  have h0 := hq.mul (tendsto_const_nhds (x:=c))
  have h1 := lpsOriginalJDilated_q_limit N hN
  simp only [hc,zero_mul] at h1 h0
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

/-- The original descended j(Ntau) quotient function is nonconstant; used by the root fixture and the forthcoming original j/jN function-field equation. -/
lemma lpsOriginalJDilatedQuotient_nonconstant (N : ℕ) (hN : 0<N) :
    ¬∃ c : ℂ, ∀ x, lpsOriginalJDilatedQuotient N hN x=c := by
  rintro ⟨c,hc⟩
  exact lpsOriginalJDilated_nonconstant N hN ⟨c,fun τ => hc ⟦τ⟧⟩

/-- Actual integer matrix entries prove dilation-conjugate commutation; used by the genuine translated-SL subgroup inclusion. -/
lemma lpsOriginalJDilation_commute (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (k : ℤ) (hk : γ 1 0=(N:ℤ)*k) :
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) *
      lpsE2AffineMatrix N hN 0 =
      lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have hδ : (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) :
      Matrix (Fin 2) (Fin 2) ℝ)=!![(γ 0 0:ℝ),(N:ℝ)*(γ 0 1:ℝ);(k:ℝ),(γ 1 1:ℝ)] := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    change (!![γ 0 0,(N:ℤ)*γ 0 1;k,γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ).map
      (algebraMap ℤ ℝ)=_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map,Matrix.of_apply]
  apply Units.ext
  change (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk):
    Matrix (Fin 2) (Fin 2) ℝ) * (lpsE2AffineMatrix N hN 0:Matrix (Fin 2) (Fin 2) ℝ)=
    (lpsE2AffineMatrix N hN 0:Matrix (Fin 2) (Fin 2) ℝ) *
      (Matrix.SpecialLinearGroup.mapGL ℝ γ:Matrix (Fin 2) (Fin 2) ℝ)
  rw [hδ,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,hk] <;> ring

/-- The original Gamma0(N) subgroup lies in the actual dilation-conjugated SL range, with membership proved from integral entries; used by all cusp subgroup inclusions. -/
lemma lpsOriginalJDilation_Gamma0_le_translated_SL (N : ℕ) (hN : 0<N) :
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
        (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  intro g hg
  obtain ⟨γ,hγ,rfl⟩ := hg
  change γ∈CongruenceSubgroup.Gamma0 N at hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdvd : (N:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp hγ
  obtain ⟨k,hk⟩ := hdvd
  rw [ConjAct.toConjAct_inv,Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul]
  refine ⟨lpsE2DilationConjugate N γ k hk,?_⟩
  have h := lpsOriginalJDilation_commute N hN γ k hk
  calc
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) *
        lpsE2AffineMatrix N hN 0) * (lpsE2AffineMatrix N hN 0)⁻¹ := by simp
    _ = _ := by rw [h]

/-- Conjugating the proved original subgroup inclusion at each actual integral cusp representative gives the true translated group inclusion; used by its strict cusp period. -/
lemma lpsOriginalJDilation_cusp_le_translated_SL (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :
    lpsOriginalCuspGroup N ρ ≤
      ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
        (ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) := by
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
    (lpsOriginalJDilation_Gamma0_le_translated_SL N hN)

/-- The actual original minimum cusp width is a strict period of the twice-translated SL group; used by genuine translated E4 and Delta cusp analyticity and q recovery. -/
lemma lpsOriginalJDilation_cusp_period (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictWidthInfty ∈
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
        (ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)))).strictPeriods := by
  apply Subgroup.mem_strictPeriods_iff.mpr
  apply lpsOriginalJDilation_cusp_le_translated_SL N hN ρ
  exact Subgroup.mem_strictPeriods_iff.mp
    (Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ))

/-- The genuine twice-translated Mathlib E4 form on the actual conjugate subgroup; used by its analytic cusp coefficient and the original ratio recovery. -/
def lpsOriginalJDilationCuspE4 (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :=
  ModularForm.translate (ModularForm.translate ModularForm.E₄ (lpsE2AffineMatrix N hN 0))
    (Matrix.SpecialLinearGroup.mapGL ℝ ρ)

/-- The genuine twice-translated Mathlib Delta cusp form on the actual conjugate subgroup; used by its analytic cusp coefficient and original ratio recovery. -/
def lpsOriginalJDilationCuspDelta (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :=
  CuspForm.translate (CuspForm.translate CuspForm.discriminant (lpsE2AffineMatrix N hN 0))
    (Matrix.SpecialLinearGroup.mapGL ℝ ρ)

/-- Analyticity of the actual translated E4 cusp coefficient at zero from its proved positive strict period and bundled cusp boundedness; used by the meromorphic ratio. -/
lemma lpsOriginalJDilationCuspE4_analytic (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      (lpsOriginalJDilationCuspE4 N hN ρ)) 0 := by
  exact ModularFormClass.analyticAt_cuspFunction_zero
    (lpsOriginalJDilationCuspE4 N hN ρ) (lpsOriginalCuspGroup_width_positive N ρ)
    (lpsOriginalJDilation_cusp_period N hN ρ)

/-- Analyticity of the actual translated Delta cusp coefficient at zero from its proved positive strict period and bundled cusp boundedness; used by the meromorphic ratio. -/
lemma lpsOriginalJDilationCuspDelta_analytic (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      (lpsOriginalJDilationCuspDelta N hN ρ)) 0 := by
  exact ModularFormClass.analyticAt_cuspFunction_zero
    (lpsOriginalJDilationCuspDelta N hN ρ) (lpsOriginalCuspGroup_width_positive N ρ)
    (lpsOriginalJDilation_cusp_period N hN ρ)


/-- Exact general positive-GL ratio recovery includes determinant squared because pinned Mathlib slash uses determinant to weight minus1; used by original all-cusp recovery and the root fixture. -/
lemma lpsOriginalJInvariant_slash_ratio (M : GL (Fin 2) ℝ)
    (hM : 0<M.det.val) (τ : ℍ) :
    (M.det.val:ℂ)^2 * ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] M) τ^3 /
      ((CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] M) τ = lpsOriginalJInvariant (M•τ) := by
  have hd : (M.det.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hM.ne'
  simp only [ModularForm.slash_apply,UpperHalfPlane.σ,hM,if_pos,abs_of_pos hM,
    Int.reduceSub,Int.reduceNeg,zpow_neg,zpow_ofNat,lpsOriginalJInvariant,
    ContinuousAlgEquiv.refl_apply]
  change (M.det.val:ℂ)^2 * (ModularForm.E₄ (M•τ) * (M.det.val:ℂ)^3 *
    ((UpperHalfPlane.denom M τ)^4)⁻¹)^3 /
    (ModularForm.discriminant (M•τ)*(M.det.val:ℂ)^11*((UpperHalfPlane.denom M τ)^12)⁻¹)=_
  field_simp [hd,UpperHalfPlane.denom_ne_zero M τ,ModularForm.discriminant_ne_zero (M•τ)]

/-- The genuine twice-translated E4/Delta ratio multiplied by N squared recovers the same original j(Ntau) after every actual cusp representative; used by q recovery. -/
lemma lpsOriginalJDilationCusp_ratio (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) (τ : ℍ) :
    (N:ℂ)^2*(lpsOriginalJDilationCuspE4 N hN ρ τ)^3 /
      lpsOriginalJDilationCuspDelta N hN ρ τ=
      lpsOriginalJDilated N hN (Matrix.SpecialLinearGroup.mapGL ℝ ρ•τ) := by
  let M := lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ ρ
  have hd : M.det.val=(N:ℝ) := by
    change (lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ ρ).det.val=_
    rw [map_mul]
    simp only [Matrix.SpecialLinearGroup.det_mapGL,mul_one]
    exact lpsE2AffineMatrix_det N hN 0
  have hp : 0<M.det.val := by rw [hd];exact_mod_cast hN
  have he : (lpsOriginalJDilationCuspE4 N hN ρ:ℍ→ℂ)=
      (ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] M := by
    change ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0)
      ∣[(4:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ=_
    exact (SlashAction.slash_mul _ _ _ _).symm
  have hD : (lpsOriginalJDilationCuspDelta N hN ρ:ℍ→ℂ)=
      (CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] M := by
    change ((CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] lpsE2AffineMatrix N hN 0)
      ∣[(12:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ=_
    exact (SlashAction.slash_mul _ _ _ _).symm
  have h := lpsOriginalJInvariant_slash_ratio M hp τ
  rw [hd] at h
  simpa only [he,hD,Complex.ofReal_natCast,M,mul_smul,lpsOriginalJDilated] using h

/-- The actual original minimum-width cusp coefficient for j(Ntau) is the true N-squared translated analytic ratio; used by meromorphy and actual chart germs. -/
def lpsOriginalJDilationCuspCoefficient (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) (q : ℂ) : ℂ :=
  (N:ℂ)^2 * (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
    (lpsOriginalJDilationCuspE4 N hN ρ) q)^3 /
    UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      (lpsOriginalJDilationCuspDelta N hN ρ) q

/-- The genuine translated analytic numerator and denominator give a meromorphic cusp coefficient at zero; used by the true added-cusp germ. -/
lemma lpsOriginalJDilationCuspCoefficient_meromorphic (N : ℕ) [NeZero N]
    (hN : 0<N) (ρ : SL(2,ℤ)) :
    MeromorphicAt (lpsOriginalJDilationCuspCoefficient N hN ρ) 0 := by
  exact (analyticAt_const.mul ((lpsOriginalJDilationCuspE4_analytic N hN ρ).pow 3)).meromorphicAt.div
    (lpsOriginalJDilationCuspDelta_analytic N hN ρ).meromorphicAt

/-- The actual q-coordinate coefficient recovers j(Ntau) after the original integral cusp representative; used by all nonzero filled-disc parameters. -/
lemma lpsOriginalJDilationCuspCoefficient_qParam (N : ℕ) [NeZero N]
    (hN : 0<N) (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalJDilationCuspCoefficient N hN ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty (τ:ℂ))=
      lpsOriginalJDilated N hN (Matrix.SpecialLinearGroup.mapGL ℝ ρ•τ) := by
  have hp := lpsOriginalJDilation_cusp_period N hN ρ
  have hw := (lpsOriginalCuspGroup_width_positive N ρ).ne'
  rw [lpsOriginalJDilationCuspCoefficient,
    UpperHalfPlane.eq_cuspFunction τ hw
      (SlashInvariantFormClass.periodic_comp_ofComplex (lpsOriginalJDilationCuspE4 N hN ρ) hp),
    UpperHalfPlane.eq_cuspFunction τ hw
      (SlashInvariantFormClass.periodic_comp_ofComplex (lpsOriginalJDilationCuspDelta N hN ρ) hp)]
  exact lpsOriginalJDilationCusp_ratio N hN ρ τ


/-- The same original quotient j(Ntau) on the interior with finite value0 only as a cusp-germ representative; used by all chart proofs and nonconstancy. -/
def lpsOriginalFilledJDilated (N : ℕ) (hN : 0<N) : LPSOriginalFilledCurve N → ℂ :=
  Sum.elim (lpsOriginalJDilatedQuotient N hN) (fun _ => 0)

/-- The same genuine upper-half-plane j(Ntau) is recovered by the original filled projection; used by interior chart analyticity. -/
lemma lpsOriginalFilledJDilated_projection (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalFilledJDilated N hN (Sum.inl ⟦τ⟧)=lpsOriginalJDilated N hN τ := rfl

/-- Nonconstancy of the same filled original meromorphic j(Ntau) follows by its actual orbit projection; used by the root fixture and original function-field successor. -/
lemma lpsOriginalFilledJDilated_nonconstant (N : ℕ) (hN : 0<N) :
    ¬∃ c : ℂ, ∀ x : LPSOriginalFilledCurve N, lpsOriginalFilledJDilated N hN x=c := by
  rintro ⟨c,hc⟩
  exact lpsOriginalJDilated_nonconstant N hN ⟨c,fun τ => hc (Sum.inl ⟦τ⟧)⟩

/-- Every actual nonzero full-disc parameter recovers the genuine minimum-width translated cusp coefficient; used by the literal punctured chart germ. -/
lemma lpsOriginalFilledJDilated_cusp_param (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJDilated N hN (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJDilationCuspCoefficient N hN (lpsOriginalCuspRepresentative N c) q.val := by
  obtain ⟨τ,hτ,hq⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hq0
  rw [hτ]
  change lpsOriginalJDilated N hN
    (Matrix.SpecialLinearGroup.mapGL ℝ (lpsOriginalCuspRepresentative N c) •τ.val)=_
  rw [←lpsOriginalJDilationCuspCoefficient_qParam N hN
    (lpsOriginalCuspRepresentative N c) τ.val,←hq]

/-- The actual added-cusp inverse has precisely the translated-ratio punctured germ; used by cusp meromorphy. -/
lemma lpsOriginalFilledJDilated_cusp_germ (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (fun q : ℂ => lpsOriginalFilledJDilated N hN
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) =ᶠ[𝓝[≠] 0]
      lpsOriginalJDilationCuspCoefficient N hN (lpsOriginalCuspRepresentative N c) := by
  let r := lpsOriginalCuspRepresentative N c
  let e := lpsOriginalFilledCuspPartialEquiv N r
  have htarget : ∀ᶠ q in 𝓝 (0:ℂ), q∈e.target :=
    (lpsOriginalFilledCuspPartialEquiv_target_open N r).mem_nhds
      (lpsOriginalFilledCuspPartialEquiv_target_zero N r)
  filter_upwards [nhdsWithin_le_nhds htarget,self_mem_nhdsWithin] with q hqt hq
  have hq0 : q≠0 := by simpa using hq
  exact lpsOriginalFilledJDilated_cusp_param N hN c ⟨q,hqt⟩ hq0

/-- Meromorphy at every genuine added cusp in the actual original minimum-width chart; used by all-chart meromorphy. -/
lemma lpsOriginalFilledJDilated_cusp_meromorphic (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    MeromorphicAt (fun q : ℂ => lpsOriginalFilledJDilated N hN
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by
  exact (lpsOriginalJDilationCuspCoefficient_meromorphic N hN
    (lpsOriginalCuspRepresentative N c)).congr (lpsOriginalFilledJDilated_cusp_germ N hN c).symm

/-- Analyticity of j(Ntau) composed with ofComplex on the actual open upper half plane; used by all actual interior targets. -/
lemma lpsOriginalJDilated_ofComplex_analytic (N : ℕ) (hpos : 0<N) (τ : ℍ) :
    AnalyticAt ℂ ((lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex) (τ:ℂ) := by
  let U : Set ℂ := {z | 0<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ ((lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex) U := by
    intro z hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (lpsOriginalJDilated_holomorphic N hpos ⟨z,hz⟩)).differentiableWithinAt
  exact hf.analyticAt (hU.mem_nhds τ.im_pos)


/-- Analyticity at every target point of every true original interior chart; used by nonzero cusp overlaps and all-chart meromorphy. -/
lemma lpsOriginalFilledJDilated_interior_analytic (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  have he : (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledInteriorChart N hN x).symm w))=
      (lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex := by
    funext w
    rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledJDilated_projection]
    rfl
  rw [he]
  exact lpsOriginalJDilated_ofComplex_analytic N hpos
    ⟨z,lpsOriginalFilledInteriorChart_target_pos N hN x z hz⟩


/-- Every nonzero actual cusp-chart target is analytic by a genuine analytic overlap with an original interior chart; used by all-chart meromorphy. -/
lemma lpsOriginalFilledJDilated_cusp_analytic_nonzero (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by
  let := lpsOriginalFilledTopology N
  obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c ⟨z,hz⟩ hz0
  let y := lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ
  let a := lpsOriginalFilledCuspChart N c
  let b := lpsOriginalFilledInteriorChart N hN y
  let e := a.symm.trans b
  have hp : a.symm z=Sum.inl y := hτ
  have hs : z∈e.source := by
    refine ⟨hz,?_⟩
    change a.symm z∈b.source
    rw [hp]
    exact lpsOriginalFilledInteriorChart_mem N hN y
  have he := lpsOriginalFilled_cusp_interior_analytic N hN y c z hs
  have hb := lpsOriginalFilledJDilated_interior_analytic N hpos hN y (e z) (e.map_source hs).1
  have hf := hb.comp he
  apply hf.congr
  filter_upwards [e.open_source.mem_nhds hs] with w hw
  change lpsOriginalFilledJDilated N hpos (b.symm (b (a.symm w)))=
    lpsOriginalFilledJDilated N hpos (a.symm w)
  have hi := hw.2
  change a.symm w∈b.source at hi
  rw [b.left_inv hi]


/-- Meromorphy at every target point of every actual preferred chart of the same original filled curve, including its cusps; used by the root fixture and forthcoming original j/jN function-field construction. -/
lemma lpsOriginalFilledJDilated_chart_meromorphic (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MeromorphicAt (fun w : ℂ => lpsOriginalFilledJDilated N hpos ((chartAt ℂ x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y => exact (lpsOriginalFilledJDilated_interior_analytic N hpos hN y z hz).meromorphicAt
  | inr c =>
    by_cases hz0 : z=0
    · subst z
      exact lpsOriginalFilledJDilated_cusp_meromorphic N hpos c
    · exact (lpsOriginalFilledJDilated_cusp_analytic_nonzero N hpos hN c z hz hz0).meromorphicAt


end
end QEC.Coding.TannerLiftedProduct
