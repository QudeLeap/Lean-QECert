import QEC.Coding.ExpanderCodes.LPSQuadraticEisensteinModularForm

/-!
# Actual quadratic Eisenstein rational-cusp constants

Actual E2 and its genuine integral slash law have infinity limit one. Explicit
integer Bezout and real diagonal-translation matrices factor the rational cusp
action. Each translated residue term has limit one except the unique last
residue, whose actual dilation gives q squared. Finite quadratic-character
summation therefore computes the actual normalized twist's constant at 1/q as
chi_q(-1) * (q^2 - 1) / G_q, which is nonzero.

The same function tends to zero at infinity, but cannot underlie a CuspForm.
All limits use the full atImInfty filter, with no target limit or analytic
factorization assumed. These exact constants support the full LPS theta
Eisenstein correction. Other cusp/dilation constants, that complete correction,
strong coefficient growth, sparse-CSS runtime and the exact PK22 main theorem
remain separate proof obligations; no public node lifecycle is advanced here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The unchanged imaginary part proves the inverse shifted denominator tends to zero in the full filter. -/
lemma lpsRealShiftInverse_tendsto_zero (r : ℝ) :
    Tendsto (fun z : ℍ => ((z:ℂ)+(r:ℂ))⁻¹) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hi : Tendsto (fun z : ℍ => z.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
  have hn : Tendsto (fun z : ℍ => ‖(z:ℂ)+(r:ℂ)‖) UpperHalfPlane.atImInfty atTop :=
    tendsto_atTop_mono (fun z => by simpa using Complex.im_le_norm ((z:ℂ)+(r:ℂ))) hi
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_inv,Function.comp_def] using tendsto_inv_atTop_zero.comp hn

/-- Actual periodic holomorphic E2 and its genuine constant coefficient give the full infinity limit one. -/
lemma lpsE2_tendsto_one : Tendsto EisensteinSeries.E2 UpperHalfPlane.atImInfty (𝓝 1) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ lpsE2_add_one
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1)
    hp E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  let f : C(ℍ,ℂ) := ⟨EisensteinSeries.E2,E2_mdifferentiable.continuous⟩
  have hcoeff := UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [Function.Periodic.qParam,Complex.ofReal_one,div_one,f,
      ContinuousMap.coe_mk] using EisensteinSeries.hasSum_qExpansion_E2 (z:=z)) 0
  have hc : UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 0=1 := by
    simpa [UpperHalfPlane.qExpansion_coeff,f] using hcoeff.symm
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2
      (Function.Periodic.qParam 1 (z:ℂ)))=EisensteinSeries.E2 := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h

/-- The actual rational denominator and inverse limit prove the genuine slash defect tends to zero. -/
lemma lpsE2Defect_tendsto_zero (γ : SL(2,ℤ)) :
    Tendsto (EisensteinSeries.D2 γ) UpperHalfPlane.atImInfty (𝓝 0) := by
  by_cases hc : γ 1 0=0
  · have he : EisensteinSeries.D2 γ=(fun z : ℍ => (0:ℂ)) := by
      funext z
      simp [EisensteinSeries.D2,hc]
    rw [he]
    exact tendsto_const_nhds
  · have hcC : (γ 1 0:ℂ)≠0 := by exact_mod_cast hc
    have he : EisensteinSeries.D2 γ = (fun z : ℍ =>
        (2*Real.pi*Complex.I:ℂ)*((z:ℂ)+(((γ 1 1:ℝ)/(γ 1 0:ℝ)):ℂ))⁻¹) := by
      funext z
      rw [EisensteinSeries.D2,ModularGroup.denom_apply]
      simp only [Complex.ofReal_intCast]
      field_simp [hcC]
    rw [he]
    simpa only [Complex.ofReal_div,Complex.ofReal_intCast,mul_zero] using
      (lpsRealShiftInverse_tendsto_zero ((γ 1 1:ℝ)/(γ 1 0:ℝ))).const_mul
        (2*Real.pi*Complex.I:ℂ)

/-- The genuine E2 transformation and zero defect prove every integral slash limit one. -/
lemma lpsE2_slash_tendsto_one (γ : SL(2,ℤ)) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 1) := by
  rw [EisensteinSeries.E2_slash_action]
  change Tendsto (fun z : ℍ => EisensteinSeries.E2 z -
    (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z) UpperHalfPlane.atImInfty (𝓝 1)
  simpa only [smul_zero,sub_zero,smul_eq_mul,mul_zero] using lpsE2_tendsto_one.sub
    ((lpsE2Defect_tendsto_zero γ).const_smul (1/(2*riemannZeta 2)))

/-- Actual upper-triangular slash action transports the full-filter limit with its scalar. -/
lemma lpsWeightTwoSlash_tendsto_upperTriangular (f : ℍ→ℂ) (L : ℂ)
    (hf : Tendsto f UpperHalfPlane.atImInfty (𝓝 L)) (g : GL (Fin 2) ℝ)
    (hc : g 1 0=0) (hd : 0<g.det.val) :
    Tendsto (f ∣[(2:ℤ)] g) UpperHalfPlane.atImInfty
      (𝓝 (L*(g.det.val:ℂ)*(g 1 1:ℂ)^(-(2:ℤ)))) := by
  have hdMatrix : 0<(g:Matrix (Fin 2) (Fin 2) ℝ).det := hd
  have he : (f ∣[(2:ℤ)] g) = (fun z : ℍ =>
      f (g • z)*(g.det.val:ℂ)*(g 1 1:ℂ)^(-(2:ℤ))) := by
    funext z
    simp [ModularForm.slash_apply,UpperHalfPlane.σ,hdMatrix,UpperHalfPlane.denom,hc,
      abs_of_pos hdMatrix]
  rw [he]
  exact ((hf.comp (UpperHalfPlane.tendsto_smul_atImInfty hc)).mul_const
    (g.det.val:ℂ)).mul_const ((g 1 1:ℂ)^(-(2:ℤ)))

/-- An actual integral and upper-triangular matrix product gives its genuine E2 slash constant. -/
lemma lpsE2_slash_factor_tendsto (δ : SL(2,ℤ)) (h : GL (Fin 2) ℝ)
    (hc : h 1 0=0) (hd : 0<h.det.val) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ*h))
      UpperHalfPlane.atImInfty (𝓝 ((h.det.val:ℂ)*(h 1 1:ℂ)^(-(2:ℤ)))) := by
  rw [SlashAction.slash_mul]
  have hf : Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ δ)
      UpperHalfPlane.atImInfty (𝓝 1) := by
    simpa [Matrix.SpecialLinearGroup.mapGL,← ModularForm.SL_slash] using
      lpsE2_slash_tendsto_one δ
  simpa only [one_mul] using lpsWeightTwoSlash_tendsto_upperTriangular _ 1 hf h hc hd

/-- Actual integer Bezout coefficients give determinant one for the primitive-column matrix. -/
lemma lpsE2PrimitiveColumn_det (a c : ℕ) (h : Nat.Coprime a c) :
    Matrix.det !![(a:ℤ),-Nat.gcdB a c;(c:ℤ),Nat.gcdA a c]=1 := by
  have hg := Nat.gcd_eq_gcd_ab a c
  rw [h.gcd_eq_one] at hg
  rw [Matrix.det_fin_two]
  change (a:ℤ)*Nat.gcdA a c-(-Nat.gcdB a c)*(c:ℤ)=1
  linear_combination -hg

/-- The actual Bezout matrix realizes an integral primitive column. -/
def lpsE2PrimitiveColumn (a c : ℕ) (h : Nat.Coprime a c) : SL(2,ℤ) :=
  ⟨!![(a:ℤ),-Nat.gcdB a c;(c:ℤ),Nat.gcdA a c],lpsE2PrimitiveColumn_det a c h⟩

/-- The actual determinant-one real matrix realizes a diagonal dilation and translation. -/
noncomputable def lpsE2DiagonalTranslation (g b : ℝ) (hg : g≠0) : SL(2,ℝ) :=
  ⟨!![g,b;0,g⁻¹],by simp [Matrix.det_fin_two,Matrix.of_apply,hg]⟩

/-- The actual integral determinant-one matrix represents the cusp one over q. -/
def lpsE2PrimeCuspMatrix (q : ℕ) : SL(2,ℤ) :=
  ⟨!![1,0;(q:ℤ),1],by simp [Matrix.det_fin_two,Matrix.of_apply]⟩

/-- Actual arithmetic column relations and determinant prove the real matrix factorization. -/
lemma lpsE2CuspFactor_matrix (g q r A B C D : ℝ) (hg : g≠0) (hq : q≠0)
    (ha : A*g=r+1) (hc : C*g=q) (hd : A*D-B*C=1) :
    !![r+1,r/q;q,1]=!![A,B;C,D]*!![g,D*r/q-B;0,g⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using ha.symm
  · simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    change r/q=A*(D*r/q-B)+B*g⁻¹
    field_simp [hg,hq]
    linear_combination -r*g*hd - B*r*hc + B*q*ha
  · simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using hc.symm
  · simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    change 1=C*(D*r/q-B)+D*g⁻¹
    field_simp [hg,hq]
    linear_combination -q*g*hd + D*q*ha - D*r*hc

/-- The constructed integral and real matrices factor the actual rational translated cusp action. -/
lemma lpsE2CuspFactor (q : ℕ) [NeZero q] (r : ℤ) (g : ℝ) (hg : g≠0)
    (δ : SL(2,ℤ)) (ha : (δ 0 0:ℝ)*g=(r:ℝ)+1) (hc : (δ 1 0:ℝ)*g=(q:ℝ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation ((r:ℝ)/(q:ℝ))) *
      Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2PrimeCuspMatrix q) =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsE2DiagonalTranslation g ((δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)) hg) := by
  have hdet : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have hd : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast hd
  have hq : (q:ℝ)≠0 := by exact_mod_cast NeZero.ne q
  have hm := lpsE2CuspFactor_matrix g (q:ℝ) (r:ℝ) (δ 0 0:ℝ) (δ 0 1:ℝ)
    (δ 1 0:ℝ) (δ 1 1:ℝ) hg hq ha hc hdet
  apply Units.ext
  change ((lpsE2RealTranslation ((r:ℝ)/(q:ℝ)):Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℝ)) *
    ((lpsE2PrimeCuspMatrix q:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)) =
    ((δ:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)) *
    ((lpsE2DiagonalTranslation g ((δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)) hg:
      Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℝ))
  convert hm using 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply,lpsE2RealTranslation,lpsE2PrimeCuspMatrix,Matrix.mul_apply,
        Fin.sum_univ_two,Matrix.of_apply,add_comm]
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- The actual factorization proves the translated E2 cusp limit from arithmetic column data. -/
lemma lpsE2ShiftAtPrimeCusp_tendsto_of_column (q : ℕ) [NeZero q] (r : ℤ)
    (g : ℝ) (hg : g≠0) (δ : SL(2,ℤ))
    (ha : (δ 0 0:ℝ)*g=(r:ℝ)+1) (hc : (δ 1 0:ℝ)*g=(q:ℝ)) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ z))
      ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) UpperHalfPlane.atImInfty (𝓝 ((g:ℂ)^2)) := by
  let b : ℝ := (δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)
  let h := Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DiagonalTranslation g b hg)
  have hh10 : h 1 0=0 := by
    change (algebraMap ℝ ℝ) 0=0
    exact map_zero _
  have hh11 : h 1 1=g⁻¹ := by
    change (algebraMap ℝ ℝ) (g⁻¹)=g⁻¹
    rfl
  have hdet : h.det.val=1 := by simp [h]
  have hp : 0<h.det.val := by rw [hdet];norm_num
  have hl := lpsE2_slash_factor_tendsto δ h hh10 hp
  rw [ModularForm.SL_slash]
  change Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r:ℝ)/(q:ℝ)) +ᵥ z))
    ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2PrimeCuspMatrix q))
      UpperHalfPlane.atImInfty (𝓝 ((g:ℂ)^2))
  rw [← lpsE2RealTranslation_slash,← SlashAction.slash_mul,
    lpsE2CuspFactor q r g hg δ ha hc]
  simpa only [hdet,hh11,Complex.ofReal_one,one_mul,Complex.ofReal_inv,zpow_neg,zpow_ofNat,
    inv_pow,inv_inv] using hl

/-- Actual Bezout and exceptional-column matrices prove every translated residue cusp constant. -/
lemma lpsE2ShiftAtPrimeCusp_tendsto (q : ℕ) [Fact q.Prime] (r : Fin q) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ z))
      ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) UpperHalfPlane.atImInfty
        (𝓝 (if r.val+1=q then (q:ℂ)^2 else 1)) := by
  by_cases hr : r.val+1=q
  · let δ := lpsE2PrimeCuspMatrix 1
    have ha : (δ 0 0:ℝ)*(q:ℝ)=((r.val:ℤ):ℝ)+1 := by
      have h : (q:ℝ)=(r.val:ℝ)+1 := by exact_mod_cast hr.symm
      simpa [δ,lpsE2PrimeCuspMatrix,Matrix.of_apply] using h
    have hc : (δ 1 0:ℝ)*(q:ℝ)=(q:ℝ) := by
      simp [δ,lpsE2PrimeCuspMatrix,Matrix.of_apply]
    have hq : (q:ℝ)≠0 := by exact_mod_cast NeZero.ne q
    simpa only [if_pos hr,Int.cast_natCast,Complex.ofReal_natCast] using
      lpsE2ShiftAtPrimeCusp_tendsto_of_column q (r.val:ℤ) (q:ℝ) hq δ ha hc
  · have hlt : r.val+1<q := by omega
    have hd : ¬q∣r.val+1 := fun h => (Nat.le_of_dvd (by omega) h).not_gt hlt
    have hcop : Nat.Coprime (r.val+1) q :=
      ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hd).symm
    let δ := lpsE2PrimitiveColumn (r.val+1) q hcop
    have ha : (δ 0 0:ℝ)*(1:ℝ)=((r.val:ℤ):ℝ)+1 := by
      change ((r.val+1:ℕ):ℝ)*1=(r.val:ℝ)+1
      push_cast
      ring
    have hc : (δ 1 0:ℝ)*(1:ℝ)=(q:ℝ) := by
      change (q:ℝ)*1=(q:ℝ)
      ring
    simpa only [if_neg hr,Int.cast_natCast,Complex.ofReal_one,one_pow] using
      lpsE2ShiftAtPrimeCusp_tendsto_of_column q (r.val:ℤ) 1 (by norm_num) δ ha hc

/-- The actual zero character sum and exceptional residue compute the weighted cusp constant. -/
lemma lpsQuadraticE2PrimeCusp_sum (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      (if r.val+1=q then (q:ℂ)^2 else 1)) =
        lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1) := by
  classical
  have hq : 0<q := (Fact.out : q.Prime).pos
  let last : Fin q := ⟨q-1,Nat.sub_lt hq (by decide)⟩
  have hl : last.val+1=q := by dsimp [last];omega
  have hc : (last.val:ZMod q)= -1 := by
    have h : (last.val:ZMod q)+1=0 := by
      simpa only [Nat.cast_add,Nat.cast_one,ZMod.natCast_self] using
        congrArg (fun n : ℕ => (n:ZMod q)) hl
    linear_combination h
  have hr (r : Fin q) : r.val+1=q ↔ r=last := by
    constructor
    · intro h;apply Fin.ext;omega
    · intro h;subst r;exact hl
  simp_rw [hr]
  have he (r : Fin q) : lpsQuadraticE2Character q (r.val:ZMod q)*
      (if r=last then (q:ℂ)^2 else 1) =
      lpsQuadraticE2Character q (r.val:ZMod q)+
        (if r=last then lpsQuadraticE2Character q (last.val:ZMod q)*((q:ℂ)^2-1) else 0) := by
    by_cases h : r=last
    · subst r;simp;ring
    · simp only [if_neg h,mul_one,add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib,lpsQuadraticE2Character_sum_zero q hq2]
  simp [hc]

/-- The genuine finite weighted limits compute the actual twist constant at one over q. -/
lemma lpsQuadraticE2Twist_prime_cusp_tendsto (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q)
      UpperHalfPlane.atImInfty (𝓝 (lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))) := by
  classical
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin q) hr =>
    (lpsE2ShiftAtPrimeCusp_tendsto q r).const_mul
      (lpsQuadraticE2Character q (r.val:ZMod q)))
  rw [lpsQuadraticE2PrimeCusp_sum q hq2] at hs
  have h := hs.const_mul (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
  have he : (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) = (fun z : ℍ =>
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((fun w : ℍ => EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ w))
            ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) z)) := by
    funext z
    simp only [ModularForm.SL_slash_apply,lpsQuadraticE2Twist]
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  have hl : (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
      (lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)) =
      lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
    rw [div_eq_mul_inv];ring
  rw [hl] at h
  exact h

/-- Actual character and Gauss units plus q greater than one make the cusp constant nonzero. -/
lemma lpsQuadraticE2PrimeCuspConstant_ne_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))≠0 := by
  have hc : lpsQuadraticE2Character q (-1:ZMod q)≠0 :=
    (IsUnit.map (lpsQuadraticE2Character q) isUnit_neg_one).ne_zero
  have hq : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hq' : (q:ℝ)^2-1≠0 := by nlinarith
  have hn : (q:ℂ)^2-1≠0 := by exact_mod_cast hq'
  exact div_ne_zero (mul_ne_zero hc hn) (lpsQuadraticE2Gauss_ne_zero q hq2)

/-- The actual nonzero full-filter limit rejects vanishing at the rational cusp. -/
lemma lpsQuadraticE2Twist_prime_cusp_not_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ¬UpperHalfPlane.IsZeroAtImInfty
      (lpsQuadraticE2Twist q ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) := by
  intro hzero
  have h := tendsto_nhds_unique (lpsQuadraticE2Twist_prime_cusp_tendsto q hq2) hzero
  exact lpsQuadraticE2PrimeCuspConstant_ne_zero q hq2 h

/-- The actual zero coefficient and analytic cusp function prove the infinity limit zero. -/
lemma lpsQuadraticE2Twist_tendsto_zero (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsQuadraticE2Twist q) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsQuadraticE2Twist_add_one q)
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp
    (lpsQuadraticE2Twist_mdifferentiable q) (lpsQuadraticE2Twist_isBoundedAtImInfty q hq2)
  have hc : UpperHalfPlane.cuspFunction 1 (lpsQuadraticE2Twist q) 0=0 := by
    have h := lpsQuadraticE2Twist_coeff_qExpansion q hq2 0
    simpa [UpperHalfPlane.qExpansion_coeff,MulChar.map_zero] using h
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 (lpsQuadraticE2Twist q)
      (Function.Periodic.qParam 1 (z:ℂ)))=lpsQuadraticE2Twist q := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h

/-- The actual nonzero rational-cusp limit excludes a cusp form with the same underlying function. -/
lemma lpsQuadraticE2Twist_not_cuspForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 (q^2) : Subgroup (GL (Fin 2) ℝ)) 2,
      (f:ℍ→ℂ)=lpsQuadraticE2Twist q := by
  rintro ⟨f,hf⟩
  have h := CuspFormClass.zero_at_infty_slash f (g:=lpsE2PrimeCuspMatrix q)
  rw [hf] at h
  exact lpsQuadraticE2Twist_prime_cusp_not_zero q hq2 h

end QEC.Coding.TannerLiftedProduct
