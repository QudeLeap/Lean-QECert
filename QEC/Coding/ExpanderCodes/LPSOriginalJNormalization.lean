import QEC.Coding.ExpanderCodes.LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# LPSOriginalJNormalization

The SAME original j is surjective. If it omitted a complex value a, its
reciprocal (j-a)^(-1), with genuine cusp value zero, would be holomorphic on
the SAME original compact connected Gamma0(4) filled curve. Actual cusp
widths yield q^m/(K(q^m)-a*q^m), analytic on a full ordinary neighborhood of
zero because m>0 and K(0)=1. Compact connected holomorphic constancy would
force original j constant, contradicting its proved q behavior. The omitted
value hypothesis is discharged in the final surjectivity theorem.

Consequently every genuine nowhere-zero level-one weight12m form is a
nonzero scalar times Delta^m. The actual translated-Delta finite-coset norm
is pointwise nowhere zero by its genuine slash product, and hence has this
scalar normalization. Its value supplies the actual top coefficient of the
literal coset product. Recovery and faithful SAMEj evaluation prove the
fixed original complex equation's degree bound and constant top coefficient.
An explicit inverse scalar normalizes it into a MONIC original j/jN equation
of EXACT finite-coset degree for every positive integer level, including
composite original theta levels.

This internal bridge is motivated by pinned PK22 main.tex ex:Xpq and
th:qLDPC. Complex monicity does not assert integral coefficients, minimality,
rational descent, identification with all compact meromorphic functions,
canonical arithmetic normalization, every-away-level good reduction,
geometric Hecke/Frobenius/Weil, or the unconditional public PK22 theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Actual reciprocal of original j minus an omitted value on the same filled curve, with genuine zero cusp value. -/
def lpsOriginalFilledJReciprocal (N : ℕ) (a : ℂ) : LPSOriginalFilledCurve N → ℂ :=
  Sum.elim (fun y => (lpsOriginalJQuotient N y-a)⁻¹) (fun _ => 0)

/-- Literal reciprocal evaluation on the same original interior orbit projection. -/
lemma lpsOriginalFilledJReciprocal_projection (N : ℕ) (a : ℂ) (τ : ℍ) :
    lpsOriginalFilledJReciprocal N a (Sum.inl ⟦τ⟧)=(lpsOriginalJInvariant τ-a)⁻¹ := rfl

/-- True nonzero cusp inverse evaluates the reciprocal of the actual original filled j. -/
lemma lpsOriginalFilledJReciprocal_cusp_nonzero_eq (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJReciprocal N a (lpsOriginalFilledCuspParam N c q)=
      (lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)-a)⁻¹ := by
  obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hq0
  rw [hτ]
  rfl

/-- Actual cusp-width q formula for the reciprocal, with the genuine numerator q^m. -/
lemma lpsOriginalFilledJReciprocal_cusp_formula (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJReciprocal N a (lpsOriginalFilledCuspParam N c q)=
      q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))/
      (lpsOriginalJQCoefficient (q.val^(lpsOriginalCuspWidthNat N
        (lpsOriginalCuspRepresentative N c)))-
        a*q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by
  let m := lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)
  have hqm : q.val^m≠0 := pow_ne_zero m hq0
  have hj := lpsOriginalFilledJ_cusp_param N c q hq0
  have he : lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJQCoefficient (q.val^m)/q.val^m :=
    (eq_div_iff hqm).mpr (by rw [mul_comm];exact hj)
  rw [lpsOriginalFilledJReciprocal_cusp_nonzero_eq N a c q hq0,he]
  have hh : lpsOriginalJQCoefficient (q.val^m)/q.val^m-a=
      (lpsOriginalJQCoefficient (q.val^m)-a*q.val^m)/q.val^m := by
    field_simp [hqm]
  rw [hh,inv_div]

/-- Ordinary-neighborhood analyticity at the true cusp zero, including its actual zero value. -/
lemma lpsOriginalFilledJReciprocal_cusp_analytic_zero (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    AnalyticAt ℂ (fun q : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let e := lpsOriginalFilledCuspPartialEquiv N r
  have hm : 0<m := lpsOriginalCuspWidthNat_positive N r
  have ha : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient (q^m)) 0 := by
    apply lpsOriginalJQCoefficient_analytic_zero.comp_of_eq (analyticAt_id.pow m)
    simp [Nat.ne_of_gt hm]
  have hd : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient (q^m)-a*q^m) 0 :=
    ha.sub (analyticAt_const.mul (analyticAt_id.pow m))
  have hn : lpsOriginalJQCoefficient ((0:ℂ)^m)-a*(0:ℂ)^m≠0 := by
    simp [Nat.ne_of_gt hm,lpsOriginalJQCoefficient_zero]
  have hf := (analyticAt_id.pow m).mul (hd.inv hn)
  apply hf.congr
  have htarget : ∀ᶠ q in 𝓝 (0:ℂ), q∈e.target :=
    (lpsOriginalFilledCuspPartialEquiv_target_open N r).mem_nhds
      (lpsOriginalFilledCuspPartialEquiv_target_zero N r)
  filter_upwards [htarget] with q hq
  by_cases hq0 : q=0
  · subst q
    have hz := lpsOriginalFilledCuspParam_zero N c ⟨0,hq⟩ rfl
    change e.symm 0=Sum.inr c at hz
    rw [hz]
    simp [lpsOriginalFilledJReciprocal,Nat.ne_of_gt hm]
  · have he := lpsOriginalFilledJReciprocal_cusp_formula N a c ⟨q,hq⟩ hq0
    change q^m*(lpsOriginalJQCoefficient (q^m)-a*q^m)⁻¹=
      lpsOriginalFilledJReciprocal N a (e.symm q)
    simpa only [div_eq_mul_inv,m,r,e,lpsOriginalFilledCuspParam,
      lpsOriginalFilledCuspPartialEquiv,PartialEquiv.coe_symm_mk] using he.symm

/-- Actual interior chart analyticity of the reciprocal under the temporary omitted-value hypothesis. -/
lemma lpsOriginalFilledJReciprocal_interior_analytic (N : ℕ) [NeZero N]
    (hN : 4∣N) (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  have he : (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledInteriorChart N hN x).symm w))=
      (fun w => (lpsOriginalJInvariant (UpperHalfPlane.ofComplex w)-a)⁻¹) := by
    funext w
    rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledJReciprocal_projection]
  rw [he]
  have hj := lpsOriginalJInvariant_ofComplex_analytic
    ⟨z,lpsOriginalFilledInteriorChart_target_pos N hN x z hz⟩
  exact (hj.sub analyticAt_const).inv (sub_ne_zero.mpr (ho (UpperHalfPlane.ofComplex z)))

/-- Actual nonzero cusp-target analyticity via true original interior overlap. -/
lemma lpsOriginalFilledJReciprocal_cusp_analytic_nonzero (N : ℕ) [NeZero N]
    (hN : 4∣N) (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let e := lpsOriginalFilledCuspChart N c
  obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c ⟨z,hz⟩ hz0
  have hn : lpsOriginalFilledJ N (e.symm z)-a≠0 := by
    rw [show e.symm z=Sum.inl (lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ) from hτ]
    change lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ
      (lpsOriginalCuspRepresentative N c) •τ.val)-a≠0
    exact sub_ne_zero.mpr (ho _)
  have hf := ((lpsOriginalFilledJ_cusp_analytic_nonzero N hN c z hz hz0).sub
    analyticAt_const).inv hn
  apply hf.congr
  have ht : ∀ᶠ w in 𝓝 z, w∈e.target := e.open_target.mem_nhds hz
  have hnz : ∀ᶠ w in 𝓝 z, w≠0 := IsOpen.mem_nhds isOpen_compl_singleton hz0
  filter_upwards [ht,hnz] with w hwt hw0
  exact (lpsOriginalFilledJReciprocal_cusp_nonzero_eq N a c ⟨w,hwt⟩ hw0).symm

/-- Reciprocal analyticity at every target point of every actual preferred chart. -/
lemma lpsOriginalFilledJReciprocal_chart_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a ((chartAt ℂ x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y => exact lpsOriginalFilledJReciprocal_interior_analytic N hN a ho y z hz
  | inr c =>
    by_cases hz0 : z=0
    · subst z
      exact lpsOriginalFilledJReciprocal_cusp_analytic_zero N a c
    · exact lpsOriginalFilledJReciprocal_cusp_analytic_nonzero N hN a ho c z hz hz0

/-- Global reciprocal holomorphy on the same original filled manifold from actual chart analyticity. -/
lemma lpsOriginalFilledJReciprocal_holomorphic (N : ℕ) [NeZero N] (hN : 4∣N)
    (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalFilledJReciprocal N a) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x
  apply (mdifferentiableAt_iff_source_of_mem_source (x:=x)
    (ChartedSpace.mem_chart_source x)).mpr
  have h := lpsOriginalFilledJReciprocal_chart_analytic N hN a ho x
    (chartAt ℂ x x) ((chartAt ℂ x).map_source (ChartedSpace.mem_chart_source x))
  simpa only [extChartAt,mfld_simps,Function.comp_def] using
    h.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt

/-- The SAME original j is surjective onto all complex values, proved by actual compact-connected constancy contradiction. -/
lemma lpsOriginalJInvariant_surjective : Function.Surjective lpsOriginalJInvariant := by
  intro a
  by_contra h
  have ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a := by
    intro τ ht
    exact h ⟨τ,ht⟩
  obtain ⟨c,hc⟩ := lpsOriginalFilled_holomorphic_eq_const 4 (by decide)
    (lpsOriginalFilledJReciprocal 4 a)
    (lpsOriginalFilledJReciprocal_holomorphic 4 (by decide) a ho)
  apply lpsOriginalJInvariant_nonconstant
  refine ⟨lpsOriginalJInvariant UpperHalfPlane.I,fun τ => ?_⟩
  have ht := congr_fun hc (Sum.inl ⟦τ⟧)
  have hi := congr_fun hc (Sum.inl ⟦UpperHalfPlane.I⟧)
  have he : (lpsOriginalJInvariant τ-a)⁻¹=(lpsOriginalJInvariant UpperHalfPlane.I-a)⁻¹ :=
    ht.trans hi.symm
  exact sub_left_inj.mp (inv_injective he)


/-- Every actual nowhere-zero level-one weight12m form is a nonzero scalar times genuine Delta^m. -/
lemma lpsOriginalLevelOne_nowherezero_delta_scalar (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) (hf : ∀ τ : ℍ, f τ≠0) :
    ∃ c : ℂ, c≠0 ∧ ∀ τ : ℍ, f τ=c*ModularForm.discriminant τ^m := by
  obtain ⟨P,_,hp⟩ := lpsOriginalLevelOne_polynomial_j m f
  have hr : ∀ z : ℂ, P.eval z≠0 := by
    intro z hz
    obtain ⟨τ,hτ⟩ := lpsOriginalJInvariant_surjective z
    apply hf τ
    rw [hp τ,hτ,hz,mul_zero]
  have hd : P.degree=0 := by
    by_contra h
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_root P h
    exact hr z hz
  have hc : P=Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hd.le
  refine ⟨P.coeff 0,?_,?_⟩
  · intro h
    apply hf UpperHalfPlane.I
    rw [hp UpperHalfPlane.I,hc,Polynomial.eval_C,h,mul_zero]
  · intro τ
    rw [hp τ,hc,Polynomial.eval_C,Polynomial.coeff_C_zero,mul_comm]

/-- The genuine original dilated-Delta finite-coset norm is nowhere zero at every actual upper-half-plane point. -/
lemma lpsOriginalDeltaDilatedNorm_ne_zero_apply (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) : lpsOriginalDeltaDilatedNorm N hN τ≠0 := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  simp only [lpsOriginalDeltaDilatedNorm,ModularForm.coe_norm,Finset.prod_apply]
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  induction q using Quotient.inductionOn with
  | h g =>
    have hd : (g.val⁻¹).det=1 := Subgroup.HasDetOne.det_eq (inv_mem g.property)
    have hf : lpsOriginalDeltaDilatedForm N hN (g.val⁻¹•τ)≠0 := by
      rw [lpsOriginalDeltaDilatedForm_apply]
      exact mul_ne_zero (pow_ne_zero 11 (by exact_mod_cast hN.ne'))
        (ModularForm.discriminant_ne_zero _)
    simp only [SlashInvariantForm.quotientFunc_mk,ModularForm.slash_apply,
      UpperHalfPlane.σ,hd,Units.val_one,zero_lt_one,ite_true,
      ContinuousAlgEquiv.refl_apply,abs_one,Complex.ofReal_one,one_zpow,mul_one]
    exact mul_ne_zero hf (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))

/-- For every positive level the genuine original Delta norm equals nonzero scalar times Delta^r. -/
lemma lpsOriginalDeltaDilatedNorm_delta_scalar (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ c : ℂ, c≠0 ∧ ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
      c*ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) :=
  lpsOriginalLevelOne_nowherezero_delta_scalar _
    (lpsOriginalDeltaDilatedNorm N hN)
    (lpsOriginalDeltaDilatedNorm_ne_zero_apply N hN)

/-- The actual top coefficient of the literal coset product is (-1)^r times genuine Delta norm. -/
lemma lpsOriginalModularCosetPolynomial_top_coeff (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularCosetPolynomial N hN τ).coeff (Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))=
      (-1:ℂ)^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
        lpsOriginalDeltaDilatedNorm N hN τ := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  unfold lpsOriginalModularCosetPolynomial
  have hc := Polynomial.coeff_prod_of_natDegree_le
    (s:=Finset.univ)
    (fun q : (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =>
      Polynomial.C (SlashInvariantForm.quotientFunc (lpsOriginalJNumeratorForm N hN) q τ)-
        Polynomial.X*Polynomial.C (SlashInvariantForm.quotientFunc (lpsOriginalDeltaDilatedForm N hN) q τ))
    1 (by
      intro q hq
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp))
  simpa [Polynomial.coeff_sub,Polynomial.coeff_X_mul,Finset.prod_neg,
    lpsOriginalDeltaDilatedNorm,ModularForm.coe_norm,Finset.prod_apply,
    Nat.card_eq_fintype_card] using hc

/-- The fixed original complex equation has degree at most the actual finite coset cardinal. -/
lemma lpsOriginalModularEquationComplex_degree (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalModularEquationComplex N hN).natDegree≤Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  simp only [lpsOriginalJPolynomialEvalHom_apply,Polynomial.eval_zero]
  have h := congrArg (fun P : Polynomial ℂ => P.coeff k)
    (lpsOriginalModularEquationComplex_recovery N hN τ)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,
    Polynomial.natDegree_le_iff_coeff_eq_zero.mp (lpsOriginalModularCosetPolynomial_degree N hN τ) k hk] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))

/-- The fixed original equation top coefficient is the actual scalar constant polynomial by faithful original j evaluation. -/
lemma lpsOriginalModularEquationComplex_top_coeff (N : ℕ) [NeZero N] (hN : 0<N)
    (lam : ℂ) (hlam : ∀ τ : ℍ, lpsOriginalDeltaDilatedNorm N hN τ=
      lam*ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))) :
    (lpsOriginalModularEquationComplex N hN).coeff (Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))=
      Polynomial.C ((-1:ℂ)^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*lam) := by
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  simp only [lpsOriginalJPolynomialEvalHom_apply]
  rw [Polynomial.eval_C]
  have h := congrArg (fun P : Polynomial ℂ => P.coeff (Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)))
    (lpsOriginalModularEquationComplex_recovery N hN τ)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,
    lpsOriginalModularCosetPolynomial_top_coeff,hlam] at h
  apply mul_left_cancel₀ (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
  exact h.trans (by ring)

/-- Explicitly normalized original j/jN relation is MONIC and has EXACT actual finite coset degree for every positive level. -/
lemma lpsOriginalJ_jN_monic_relation (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated N hN τ)=0 := by
  obtain ⟨lam,hlam0,hlam⟩ := lpsOriginalDeltaDilatedNorm_delta_scalar N hN
  let r := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let μ := (-1:ℂ)^r*lam
  have hμ : μ≠0 := mul_ne_zero (pow_ne_zero r (by norm_num)) hlam0
  let Φ : Polynomial (Polynomial ℂ) :=
    Polynomial.C (Polynomial.C μ⁻¹)*lpsOriginalModularEquationComplex N hN
  have hdeg : Φ.natDegree≤r :=
    Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C,zero_add] using
        lpsOriginalModularEquationComplex_degree N hN)
  have hcoeff : Φ.coeff r=1 := by
    rw [Polynomial.coeff_C_mul,lpsOriginalModularEquationComplex_top_coeff N hN lam hlam,
      ←Polynomial.C_mul,inv_mul_cancel₀ hμ,Polynomial.C_1]
  have heq : Φ.natDegree=r :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff];exact one_ne_zero)
  refine ⟨Φ,?_,heq,?_⟩
  · change Φ.coeff Φ.natDegree=1
    rw [heq,hcoeff]
  · intro τ
    simp only [Φ,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.coe_evalRingHom,
      Polynomial.eval_C,lpsOriginalModularEquationComplex_original_root,mul_zero]

end
end QEC.Coding.TannerLiftedProduct
