import QEC.Coding.ExpanderCodes.LPSOriginalDilatedModularFunction

/-!
# LPSOriginalExactStabilizer

Prove that the stabilizer of the SAME original dilated j under integral SL2
is exactly Gamma0(N), for every positive level including composite levels.
True integral Bezout triangularization at a scaled cusp yields an affine
pole of order gcd(N*a,c)^2. The determinant identity makes this gcd divide N;
if N does not divide c its square is strictly smaller than N^2. The actual
original K(0)=1 and nome limits then contradict invariance. The converse uses
the existing genuine Gamma0 invariance. No orbit classification or supplied
stabilizer, distinctness or pole-order hypothesis is used.

This internal original-family analytic closure supports the exact generated
function-field degree route motivated by pinned PK22 ex:Xpq/th:qLDPC and
the audited modular-equation route. It does not yet prove exact field degree,
an integer modular equation, ALL compact meromorphic-field identification,
a canonical proper arithmetic model, uniform good reduction or Weil bounds.
The public PK22 main theorem remains subsequent mathematics.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

/-- Actual nome of a positive integral affine transform, with the genuine exponential phase. -/
lemma lpsOriginalAffineNome (m : ℕ) (hm : 0<m) (r : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ : ℍ) : ℂ)=
      Function.Periodic.qParam 1 (τ:ℂ)^m*Function.Periodic.qParam 1 (r:ℂ) := by
  rw [lpsE2AffineMatrix_action]
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one]
  rw [show 2*Real.pi*I*((m:ℂ)*(τ:ℂ)+(r:ℂ))=
      (m:ℂ)*(2*Real.pi*I*(τ:ℂ))+2*Real.pi*I*(r:ℂ) by ring,
    Complex.exp_add,Complex.exp_nat_mul]

/-- The actual affine nome tends to zero at imaginary infinity. -/
lemma lpsOriginalAffineNomeLimit (m : ℕ) (hm : 0<m) (r : ℝ) :
    Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1
      ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
  have hq := (UpperHalfPlane.qParam_tendsto_atImInfty
    (by norm_num : (0:ℝ)<1)).pow m
  have h := hq.mul (tendsto_const_nhds (x:=Function.Periodic.qParam 1 (r:ℂ)))
  have hs : Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^m*
      Function.Periodic.qParam 1 (r:ℂ)) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [zero_pow hm.ne',zero_mul] using h
  exact hs.congr fun τ=>(lpsOriginalAffineNome m hm r τ).symm

/-- Actual pole-weighted affine pullback equals the SAME original analytic K times the remaining nome power. -/
lemma lpsOriginalAffinePolePullback (m k : ℕ) (hm : 0<m)
    (hmk : m≤k) (r : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)^k*
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ)=
        Function.Periodic.qParam 1 (τ:ℂ)^(k-m)/Function.Periodic.qParam 1 (r:ℂ)*
          lpsOriginalJQCoefficient
            (Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ)) := by
  have h := lpsOriginalJInvariant_qParam_pullback (lpsE2AffineMatrix m hm r • τ)
  rw [lpsOriginalAffineNome] at h
  have he : Function.Periodic.qParam 1 (τ:ℂ)^k=
      Function.Periodic.qParam 1 (τ:ℂ)^(k-m)*Function.Periodic.qParam 1 (τ:ℂ)^m := by
    rw [←pow_add,Nat.sub_add_cancel hmk]
  rw [he,lpsOriginalAffineNome,←h]
  field_simp [Function.Periodic.qParam_ne_zero]

/-- A genuinely smaller affine pole tends to zero after multiplication by the larger nome power. -/
lemma lpsOriginalAffineSmallerPoleLimit (m k : ℕ) (hm : 0<m)
    (hmk : m<k) (r : ℝ) :
    Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^k*
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
  have hq := (UpperHalfPlane.qParam_tendsto_atImInfty
    (by norm_num : (0:ℝ)<1)).pow (k-m)
  have hK := lpsOriginalJQCoefficient_analytic_zero.continuousAt.tendsto.comp
    (lpsOriginalAffineNomeLimit m hm r)
  have h := (hq.div_const (Function.Periodic.qParam 1 (r:ℂ))).mul hK
  rw [lpsOriginalJQCoefficient_zero] at h
  have hs : Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^(k-m)/
      Function.Periodic.qParam 1 (r:ℂ)*lpsOriginalJQCoefficient
        (Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ)))
      UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [zero_pow (Nat.sub_pos_of_lt hmk).ne',zero_div,zero_mul,Function.comp_def] using h
  exact hs.congr fun τ=>(lpsOriginalAffinePolePullback m k hm hmk.le r τ).symm

/-- True zero-versus-one limits distinguish the actual smaller affine pole from original dilated j. -/
lemma lpsOriginalAffineDistinctPole (m k : ℕ) (hm : 0<m)
    (hk : 0<k) (hmk : m<k) (r : ℝ) :
    ¬∀ τ : ℍ, lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ)=
      lpsOriginalJDilated k hk τ := by
  intro he
  have h0 := lpsOriginalAffineSmallerPoleLimit m k hm hmk r
  simp only [he] at h0
  have h1 := lpsOriginalJDilated_q_limit k hk
  exact zero_ne_one (tendsto_nhds_unique h0 h1)



/-- The actual first-column gcd divides the level by the genuine integral determinant identity. -/
lemma lpsOriginalDilationColumnGcdDvd (N : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)∣N := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h := Int.dvd_add
    (dvd_mul_of_dvd_left (Int.gcd_dvd_left ((N:ℤ)*γ 0 0) (γ 1 0)) (γ 1 1))
    (dvd_mul_of_dvd_left (Int.gcd_dvd_right ((N:ℤ)*γ 0 0) (γ 1 0)) (-(N:ℤ)*γ 0 1))
  have he : (N:ℤ)*γ 0 0*γ 1 1+γ 1 0*(-(N:ℤ)*γ 0 1)=(N:ℤ) := by
    linear_combination (N:ℤ)*hd
  rw [he] at h
  exact Int.natCast_dvd_natCast.mp h

/-- If the lower-left entry is not divisible by the level, the actual first-column gcd is strictly smaller. -/
lemma lpsOriginalDilationColumnGcdLt (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (hc : ¬(N:ℤ)∣γ 1 0) :
    Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)<N := by
  have hle := Nat.le_of_dvd hN (lpsOriginalDilationColumnGcdDvd N γ)
  apply lt_of_le_of_ne hle
  intro he
  have h := Int.gcd_dvd_right ((N:ℤ)*γ 0 0) (γ 1 0)
  rw [he] at h
  exact hc h

/-- The actual dilation first-column gcd is positive, from the genuine positive matrix determinant. -/
lemma lpsOriginalDilationColumnGcdPos (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    0<Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0) := by
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix N hN 0*Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hd : M.det.val=(N:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix N hN 0).det.val := by simp [M]
         _=(N:ℝ) := lpsE2AffineMatrix_det N hN 0
  have hp : 0<M.det.val := by rw [hd];exact_mod_cast hN
  apply lpsE2IntegerColumn_gcd_pos M hp ((N:ℤ)*γ 0 0) (γ 1 0) 1
  · simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  · simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]

/-- Actual integral Bezout triangularization at the scaled cusp identifies the transformed original j with an affine slope equal to the squared gcd. -/
lemma lpsOriginalDilatedAtScaledCusp (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    ∃ r : ℝ, ∀ σ : ℍ,
      lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant
          (lpsE2AffineMatrix ((Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0))^2)
            (pow_pos (lpsOriginalDilationColumnGcdPos N hN γ) 2) r • σ) := by
  let g : ℕ := Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)
  have hg : 0<g := lpsOriginalDilationColumnGcdPos N hN γ
  obtain ⟨a,c,hcop,ha,hc⟩ := Int.exists_gcd_one hg
  let δ := lpsE2IntegerPrimitiveColumn a c hcop
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix N hN 0*Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdetM : M.det.val=(N:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix N hN 0).det.val := by simp [M]
         _=(N:ℝ) := lpsE2AffineMatrix_det N hN 0
  have hM00 : M 0 0=((N:ℤ)*γ 0 0:ℤ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hM10 : M 1 0=(γ 1 0:ℝ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hA : (δ 0 0:ℝ)*(g:ℝ)=M 0 0 := by
    rw [hM00]
    change (a:ℝ)*(g:ℝ)=(((N:ℤ)*γ 0 0:ℤ):ℝ)
    exact_mod_cast ha.symm
  have hC : (δ 1 0:ℝ)*(g:ℝ)=M 1 0 := by
    rw [hM10]
    change (c:ℝ)*(g:ℝ)=(γ 1 0:ℝ)
    exact_mod_cast hc.symm
  let h : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹*M
  have hdδ : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have he : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast he
  have hh10 : h 1 0=0 := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 1 0=0
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    ring
  have hh00 : h 0 0=(g:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 0=(g:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    linear_combination (g:ℝ)*hdδ
  have hhdet : h.det.val=(N:ℝ) := by simp [h,hdetM]
  have hgR : (g:ℝ)≠0 := by exact_mod_cast hg.ne'
  have hh11 : h 1 1=(N:ℝ)/(g:ℝ) := by
    apply (eq_div_iff hgR).2
    have he := hhdet
    change Matrix.det (h:Matrix (Fin 2) (Fin 2) ℝ)=(N:ℝ) at he
    simpa only [Matrix.det_fin_two,hh00,hh10,mul_zero,zero_mul,sub_zero,mul_comm] using he
  let r : ℝ := h 0 1*(g:ℝ)/(N:ℝ)
  refine ⟨r,?_⟩
  intro σ
  have hp : 0<h.det.val := by rw [hhdet];exact_mod_cast hN
  have he : h • (lpsE2AffineMatrix N hN 0 • σ)=
      lpsE2AffineMatrix (g^2) (pow_pos hg 2) r • σ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hp,lpsE2AffineMatrix_action,
      UpperHalfPlane.num,UpperHalfPlane.denom,hh00,hh10,hh11,lpsE2AffineMatrix_action]
    simp only [Complex.ofReal_div,Complex.ofReal_zero,Complex.ofReal_natCast,zero_mul,
      zero_add,add_zero,Nat.cast_pow]
    have hgC : (g:ℂ)≠0 := by exact_mod_cast hg.ne'
    have hNC : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
    change ((g:ℂ)*((N:ℂ)*(σ:ℂ))+(h 0 1:ℂ))/((N:ℂ)/(g:ℂ))=
      (g:ℂ)^2*(σ:ℂ)+(h 0 1*(g:ℝ)/(N:ℝ):ℝ)
    push_cast
    field_simp [hgC,hNC]
  have hm : M=Matrix.SpecialLinearGroup.mapGL ℝ δ*h := by simp [h]
  have hγ : ∀ τ : ℍ, γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map,Matrix.of_apply]
  calc
    lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (M • (lpsE2AffineMatrix N hN 0 • σ)) := by
      simp only [lpsOriginalJDilated,M,mul_smul,hγ]
    _=lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ δ •
        (h • (lpsE2AffineMatrix N hN 0 • σ))) := by rw [hm,mul_smul]
    _=lpsOriginalJInvariant (h • (lpsE2AffineMatrix N hN 0 • σ)) :=
      lpsOriginalJInvariant_SL_invariant _ ⟨δ,rfl⟩ _
    _=_ := by rw [he]

/-- Composition of the SAME original dilated j with level dilation equals the actual square-level dilation. -/
lemma lpsOriginalJDilatedCompose (N : ℕ) (hN : 0<N) (σ : ℍ) :
    lpsOriginalJDilated N hN (lpsE2AffineMatrix N hN 0 • σ)=
      lpsOriginalJDilated (N^2) (pow_pos hN 2) σ := by
  unfold lpsOriginalJDilated
  congr 1
  apply UpperHalfPlane.ext
  simp only [lpsE2AffineMatrix_action,Complex.ofReal_zero,add_zero,Nat.cast_pow]
  ring

/-- The stabilizer of SAME original dilated j under integral SL2 is exactly Gamma0 at every positive, including composite, level. -/
lemma lpsOriginalJDilatedExactStabilizer (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    (∀ τ : ℍ,lpsOriginalJDilated N hN (γ•τ)=lpsOriginalJDilated N hN τ)↔
      γ∈CongruenceSubgroup.Gamma0 N := by
  constructor
  · intro he
    rw [CongruenceSubgroup.Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
    by_contra hc
    let g := Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)
    have hg : 0<g := lpsOriginalDilationColumnGcdPos N hN γ
    have hlt : g<N := lpsOriginalDilationColumnGcdLt N hN γ hc
    have hsq : g^2<N^2 := by nlinarith
    obtain ⟨r,hr⟩ := lpsOriginalDilatedAtScaledCusp N hN γ
    apply lpsOriginalAffineDistinctPole (g^2) (N^2) (pow_pos hg 2)
      (pow_pos hN 2) hsq r
    intro σ
    rw [←hr σ,he,lpsOriginalJDilatedCompose]
  · intro hγ τ
    exact lpsOriginalJDilated_integral_Gamma0_invariant N hN γ hγ τ

end
end QEC.Coding.TannerLiftedProduct
