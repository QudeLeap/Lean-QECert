import QEC.Coding.ExpanderCodes.LPSQuadraticEisensteinCusps

/-!
# Every actual cusp constant of dilated quadratic Eisenstein series

Signed integer Bezout constructs an actual primitive-column matrix. Its inverse
factor is genuinely upper triangular with proved entries and determinant. This
computes the full-filter limit of E2(m z + r/q) after every integral cusp
representative as gcd(q m A + r C, q C)^2 / (q^2 m^2). The actual normalized
quadratic twist and every positive integer dilation consequently have their
complete cusp vector expressed by a finite character-weighted gcd sum.

The formula covers both denominator signs, infinity and the prime two without
assuming odd-character cancellation. No target limit, factorization or cusp
conclusion is an input. These basis constants support the full LPS theta
Eisenstein correction. That correction, stronger coefficient growth, complete
sparse-CSS runtime and exact PK22 theorem remain separate proof obligations;
no public theorem binding or lifecycle is advanced here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The genuine inverse map has the signed integral adjugate entries used in the actual triangular factor. -/
lemma lpsE2SLInverse_real_matrix (δ : SL(2,ℤ)) :
    (((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(δ 1 1:ℝ),-(δ 0 1:ℝ);-(δ 1 0:ℝ),(δ 0 0:ℝ)] := by
  rw [← map_inv]
  change ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)=_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map,Matrix.of_apply]

/-- The actual delta inverse times M is triangular with derived entries and determinant, giving the E2 cusp scalar. -/
lemma lpsE2_slash_tendsto_of_column (M : GL (Fin 2) ℝ)
    (hd : 0<M.det.val) (δ : SL(2,ℤ)) (g : ℝ) (hg : g≠0)
    (ha : (δ 0 0:ℝ)*g=M 0 0) (hc : (δ 1 0:ℝ)*g=M 1 0) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] M) UpperHalfPlane.atImInfty
      (𝓝 ((g:ℂ)^2/(M.det.val:ℂ))) := by
  let h : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹*M
  have hdδ : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have hdet : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast hdet
  have hh10 : h 1 0=0 := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 1 0=0
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [← ha,← hc]
    ring
  have hh00 : h 0 0=g := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 0=g
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [← ha,← hc]
    linear_combination g*hdδ
  have hhdet : h.det.val=M.det.val := by simp [h]
  have hh11 : h 1 1=M.det.val/g := by
    have he : g*h 1 1=M.det.val := by
      have he := hhdet
      change Matrix.det (h:Matrix (Fin 2) (Fin 2) ℝ)=M.det.val at he
      simpa only [Matrix.det_fin_two,hh00,hh10,mul_zero,sub_zero] using he
    apply (eq_div_iff hg).2
    simpa [mul_comm] using he
  have hm : M=Matrix.SpecialLinearGroup.mapGL ℝ δ*h := by simp [h]
  have hp : 0<h.det.val := by rw [hhdet];exact hd
  have hl := lpsE2_slash_factor_tendsto δ h hh10 hp
  have hdc : (M.det.val:ℂ)≠0 := by exact_mod_cast hd.ne'
  have hgc : (g:ℂ)≠0 := by exact_mod_cast hg
  have he : (h.det.val:ℂ)*(h 1 1:ℂ)^(-(2:ℤ))=(g:ℂ)^2/(M.det.val:ℂ) := by
    rw [hhdet,hh11]
    simp only [Complex.ofReal_div,zpow_neg,zpow_ofNat]
    field_simp [hdc,hgc]
  rw [he] at hl
  simpa only [← hm] using hl

/-- Signed integer Bezout gives determinant one for the genuine primitive-column matrix. -/
lemma lpsE2IntegerPrimitiveColumn_det (a c : ℤ) (h : Int.gcd a c=1) :
    Matrix.det !![a,-Int.gcdB a c;c,Int.gcdA a c]=1 := by
  have hg := Int.gcd_eq_gcd_ab a c
  rw [h] at hg
  rw [Matrix.det_fin_two]
  change a*Int.gcdA a c-(-Int.gcdB a c)*c=1
  linear_combination -hg

/-- The actual signed Bezout matrix supplies the integral primitive column. -/
def lpsE2IntegerPrimitiveColumn (a c : ℤ) (h : Int.gcd a c=1) : SL(2,ℤ) :=
  ⟨!![a,-Int.gcdB a c;c,Int.gcdA a c],lpsE2IntegerPrimitiveColumn_det a c h⟩

/-- Actual gcd reduction constructs the primitive column and its scale, proving the rational-column E2 limit. -/
lemma lpsE2_slash_tendsto_integer_column (M : GL (Fin 2) ℝ)
    (hd : 0<M.det.val) (a c : ℤ) (t : ℝ) (ht : t≠0)
    (ha : M 0 0=(a:ℝ)/t) (hc : M 1 0=(c:ℝ)/t)
    (hpos : 0<Int.gcd a c) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] M) UpperHalfPlane.atImInfty
      (𝓝 ((((Int.gcd a c:ℕ):ℂ)/(t:ℂ))^2/(M.det.val:ℂ))) := by
  obtain ⟨a',c',hcop,ha',hc'⟩ := Int.exists_gcd_one hpos
  let δ := lpsE2IntegerPrimitiveColumn a' c' hcop
  let g : ℝ := (Int.gcd a c:ℝ)/t
  have hg : g≠0 := div_ne_zero (by exact_mod_cast hpos.ne') ht
  have hA : (δ 0 0:ℝ)*g=M 0 0 := by
    rw [ha]
    change (a':ℝ)*((Int.gcd a c:ℝ)/t)=(a:ℝ)/t
    have he : (a:ℝ)=(a':ℝ)*(Int.gcd a c:ℝ) := by exact_mod_cast ha'
    rw [he]
    ring
  have hC : (δ 1 0:ℝ)*g=M 1 0 := by
    rw [hc]
    change (c':ℝ)*((Int.gcd a c:ℝ)/t)=(c:ℝ)/t
    have he : (c:ℝ)=(c':ℝ)*(Int.gcd a c:ℝ) := by exact_mod_cast hc'
    rw [he]
    ring
  simpa only [g,Complex.ofReal_div,Complex.ofReal_natCast] using
    lpsE2_slash_tendsto_of_column M hd δ g hg hA hC

/-- A positive genuine determinant excludes an all-zero first column and proves gcd positivity. -/
lemma lpsE2IntegerColumn_gcd_pos (M : GL (Fin 2) ℝ) (hd : 0<M.det.val)
    (a c : ℤ) (t : ℝ) (ha : M 0 0=(a:ℝ)/t) (hc : M 1 0=(c:ℝ)/t) :
    0<Int.gcd a c := by
  by_contra hn
  have hz : Int.gcd a c=0 := Nat.eq_zero_of_not_pos hn
  have hac : a=0 ∧ c=0 := by
    simpa only [Int.gcd_def,Int.natAbs_eq_zero] using Nat.gcd_eq_zero_iff.mp hz
  have hA : M 0 0=0 := by rw [ha,hac.1];simp
  have hC : M 1 0=0 := by rw [hc,hac.2];simp
  have hdet : M.det.val=0 := by
    change (M:Matrix (Fin 2) (Fin 2) ℝ).det=0
    simp [Matrix.det_fin_two,hA,hC]
  rw [hdet] at hd
  exact lt_irrefl _ hd

/-- The actual positive-determinant matrix implements dilation and translation. -/
noncomputable def lpsE2AffineMatrix (m : ℕ) (hm : 0<m) (r : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m:ℝ),r;0,1]
    (by simpa [Matrix.det_fin_two,Matrix.of_apply] using
      (show (m:ℝ)≠0 by exact_mod_cast hm.ne'))

/-- The genuine affine determinant is the positive dilation used by the slash normalization. -/
lemma lpsE2AffineMatrix_det (m : ℕ) (hm : 0<m) (r : ℝ) :
    (lpsE2AffineMatrix m hm r).det.val=(m:ℝ) := by
  change Matrix.det !![(m:ℝ),r;0,1]=(m:ℝ)
  simp [Matrix.det_fin_two,Matrix.of_apply]

/-- The actual affine matrix entries are used by the action and cusp arithmetic proofs. -/
lemma lpsE2AffineMatrix_coe (m : ℕ) (hm : 0<m) (r : ℝ) :
    (lpsE2AffineMatrix m hm r:Matrix (Fin 2) (Fin 2) ℝ)=!![(m:ℝ),r;0,1] := rfl

/-- The actual positive-determinant action is the complex affine map m z plus r. -/
lemma lpsE2AffineMatrix_action (m : ℕ) (hm : 0<m) (r : ℝ) (z : ℍ) :
    ((lpsE2AffineMatrix m hm r • z:ℍ):ℂ)=(m:ℂ)*(z:ℂ)+(r:ℂ) := by
  simp [UpperHalfPlane.coe_smul,UpperHalfPlane.σ,hm,UpperHalfPlane.num,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply]

/-- The true weight-two slash equals the affine E2 function times its determinant m. -/
lemma lpsE2AffineMatrix_slash (m : ℕ) (hm : 0<m) (r : ℝ) :
    (EisensteinSeries.E2 ∣[(2:ℤ)] lpsE2AffineMatrix m hm r)=
      (fun z : ℍ => (m:ℂ)*EisensteinSeries.E2 (lpsE2AffineMatrix m hm r • z)) := by
  funext z
  simp [ModularForm.slash_apply,UpperHalfPlane.σ,hm,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply,mul_comm]

/-- The actual affine times cusp matrix and constructed primitive column give its full-filter gcd constant. -/
lemma lpsE2Affine_cusp_tendsto (m q : ℕ) (hm : 0<m) (hq : 0<q)
    (r : ℤ) (γ : SL(2,ℤ)) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • z)) ∣[(2:ℤ)] γ)
      UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0) ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/
        ((q:ℂ)^2*(m:ℂ)^2))) := by
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) *
    Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdet : M.det.val=(m:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ))).det.val := by simp [M]
         _=(m:ℝ) := lpsE2AffineMatrix_det m hm _
  have hp : 0<M.det.val := by rw [hdet];exact_mod_cast hm
  have hqR : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have ha : M 0 0=(((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0:ℤ):ℝ)/(q:ℝ) := by
    change ((lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)):Matrix (Fin 2) (Fin 2) ℝ)*
      ((γ:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))) 0 0=_
    rw [lpsE2AffineMatrix_coe]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
    field_simp
  have hc : M 1 0=(((q:ℤ)*γ 1 0:ℤ):ℝ)/(q:ℝ) := by
    change ((lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)):Matrix (Fin 2) (Fin 2) ℝ)*
      ((γ:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))) 1 0=_
    rw [lpsE2AffineMatrix_coe]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,hqR]
  have hg := lpsE2IntegerColumn_gcd_pos M hp _ _ (q:ℝ) ha hc
  have hl := lpsE2_slash_tendsto_integer_column M hp _ _ (q:ℝ) hqR ha hc hg
  let G : ℕ := Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+r*γ 1 0) ((q:ℤ)*γ 1 0)
  have he : (EisensteinSeries.E2 ∣[(2:ℤ)] M) =
      (fun z : ℍ => (m:ℂ)*(((fun w : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • w)) ∣[(2:ℤ)] γ) z)) := by
    rw [show M=lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ))*Matrix.SpecialLinearGroup.mapGL ℝ γ from rfl,
      SlashAction.slash_mul,lpsE2AffineMatrix_slash]
    change ((fun z : ℍ => (m:ℂ)*EisensteinSeries.E2
      (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • z)) ∣[(2:ℤ)] γ)=_
    funext z
    simp only [ModularForm.SL_slash_apply]
    ring
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hqC : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
  have h := hl.const_mul (m:ℂ)⁻¹
  have hfn : (fun z : ℍ => (m:ℂ)⁻¹*(EisensteinSeries.E2 ∣[(2:ℤ)] M) z) =
      ((fun w : ℍ => EisensteinSeries.E2
        (lpsE2AffineMatrix m hm ((r:ℝ)/(q:ℝ)) • w)) ∣[(2:ℤ)] γ) := by
    rw [he]
    funext z
    simp [hmC]
  have hval : (m:ℂ)⁻¹*((G:ℂ)/(q:ℂ))^2/(M.det.val:ℂ) =
      (G:ℂ)^2/((q:ℂ)^2*(m:ℂ)^2) := by
    rw [hdet]
    simp only [Complex.ofReal_natCast]
    field_simp [hmC,hqC]
  simp only [hfn,Complex.ofReal_natCast,← mul_div_assoc] at h
  change Tendsto _ UpperHalfPlane.atImInfty
    (𝓝 ((m:ℂ)⁻¹*((G:ℂ)/(q:ℂ))^2/(M.det.val:ℂ))) at h
  rw [hval] at h
  exact h

/-- Actual affine actions identify a translation after dilation with the single affine action. -/
lemma lpsE2AffineMatrix_translation (m : ℕ) (hm : 0<m) (r : ℝ) (z : ℍ) :
    r +ᵥ (lpsE2AffineMatrix m hm 0 • z) = lpsE2AffineMatrix m hm r • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd,lpsE2AffineMatrix_action,lpsE2AffineMatrix_action]
  simp only [Complex.ofReal_zero,add_zero]
  ring

/-- The actual dilated quadratic twist is composed with the genuine affine action. -/
noncomputable def lpsQuadraticE2Dilate (q m : ℕ) [Fact q.Prime] (hm : 0<m) (z : ℍ) : ℂ :=
  lpsQuadraticE2Twist q (lpsE2AffineMatrix m hm 0 • z)

/-- Actual translation compatibility expands the dilated twist into its genuine finite E2 sum. -/
lemma lpsQuadraticE2Dilate_eq (q m : ℕ) [Fact q.Prime] (hm : 0<m) :
    lpsQuadraticE2Dilate q m hm = (fun z : ℍ =>
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          EisensteinSeries.E2 (lpsE2AffineMatrix m hm ((r.val:ℝ)/(q:ℝ)) • z)) := by
  funext z
  simp only [lpsQuadraticE2Dilate,lpsQuadraticE2Twist,lpsE2AffineMatrix_translation]

/-- Actual finite weighted full-filter limits give the entire dilated twist cusp vector as a gcd sum. -/
lemma lpsQuadraticE2Dilate_cusp_tendsto (q m : ℕ) [Fact q.Prime] (hm : 0<m)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((Int.gcd ((q:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/((q:ℂ)^2*(m:ℂ)^2)))) := by
  classical
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin q) hr =>
    (lpsE2Affine_cusp_tendsto m q hm (Fact.out : q.Prime).pos (r.val:ℤ) γ).const_mul
      (lpsQuadraticE2Character q (r.val:ZMod q)))
  have h := hs.const_mul (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
  have he : (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) = (fun z : ℍ =>
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((fun w : ℍ => EisensteinSeries.E2
            (lpsE2AffineMatrix m hm ((r.val:ℝ)/(q:ℝ)) • w)) ∣[(2:ℤ)] γ) z)) := by
    rw [lpsQuadraticE2Dilate_eq]
    funext z
    simp only [ModularForm.SL_slash_apply]
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  simpa only [Int.cast_natCast] using h

/-- Dilation by one has the actual existing quadratic twist as its underlying function. -/
lemma lpsQuadraticE2Dilate_one (q : ℕ) [Fact q.Prime] :
    lpsQuadraticE2Dilate q 1 (by decide)=lpsQuadraticE2Twist q := by
  funext z
  unfold lpsQuadraticE2Dilate
  congr 1
  apply UpperHalfPlane.ext
  rw [lpsE2AffineMatrix_action]
  simp

/-- The dilation-one specialization computes every actual cusp constant of the existing twist. -/
lemma lpsQuadraticE2Twist_cusp_gcd_tendsto (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/(q:ℂ)^2))) := by
  simpa only [lpsQuadraticE2Dilate_one,Nat.cast_one,Int.cast_one,mul_one,one_pow] using
    lpsQuadraticE2Dilate_cusp_tendsto q 1 (by decide) γ

end QEC.Coding.TannerLiftedProduct
