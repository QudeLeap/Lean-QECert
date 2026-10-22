import QEC.Coding.ExpanderCodes.LPSIteratedEisenstein
import QEC.Coding.ExpanderCodes.LPSEisensteinDifference

/-!
# Genuine modular dilations and the common theta-level Eisenstein basis

Actual congruence divisibility constructs integral dilation conjugates, whose
true action and denominator prove invariance of f(mz). The real image of a
constructed rational matrix transports all rational cusps; genuine input bounds
and holomorphicity assemble the actual Mathlib ModularForm at level N*m.
The true nome identity and injective multiplication reindex its convergent
series. Analytic uniqueness identifies every actual coefficient at n/m and
zeros off the multiplication range, without the determinant multiplier of GL
slash.

Instantiate the closure with the genuine chi4, prime-character and iterated
Eisenstein forms. Actual divisor arithmetic raises every E2-difference divisor,
the three chi4 q-power dilations and the five prime-character two-power
dilations to Gamma0((4*q)^2), preserving their actual functions and coefficients.
Together with the existing iterated form these are the true inputs for the LPS
theta Eisenstein correction. The full theta all-cusp cancellation, CuspForm,
stronger coefficient growth, complete sparse-CSS runtime and exact PK22 theorem
remain separate proof obligations. No target modularity, series or coefficient
is supplied as an assumption; no public lifecycle is advanced.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-* Actual integer level divisibility gives inclusion of the genuine congruence subgroups. -/
lemma lpsGamma0_level_le (N L : ℕ) (hNL : N ∣ L) :
    CongruenceSubgroup.Gamma0 L ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mpr
  have hL := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) L).mp hγ
  exact (by exact_mod_cast hNL : (N:ℤ) ∣ (L:ℤ)).trans hL

/-* Restrict a genuine form to a divisible higher level using its actual invariance and cusp bounds. -/
noncomputable def lpsModularForm_raiseLevel (N L : ℕ) (hNL : N ∣ L)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ModularForm (CongruenceSubgroup.Gamma0 L : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := f
  slash_action_eq' := fun g hg => f.slash_action_eq' g
    ((Subgroup.map_mono (lpsGamma0_level_le N L hNL)) hg)
  holo' := f.holo'
  bdd_at_cusps' := fun hc => f.bdd_at_cusps'
    (hc.mono (Subgroup.map_mono (lpsGamma0_level_le N L hNL)))

/-* Raising the level preserves the actual underlying function. -/
lemma lpsModularForm_raiseLevel_apply (N L : ℕ) (hNL : N ∣ L)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsModularForm_raiseLevel N L hNL f z=f z := rfl

/-* The true weight-two affine slash of an arbitrary function includes the determinant multiplier. -/
lemma lpsFunction_affine_slash (f : ℍ→ℂ) (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (f ∣[(2:ℤ)] lpsE2AffineMatrix m hm r)=
      (fun z : ℍ => (m:ℂ)*f (lpsE2AffineMatrix m hm r • z)) := by
  ext z
  simp [ModularForm.slash_apply,UpperHalfPlane.σ,hm,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply,mul_comm]

/-* Constructed dilation action and denominator identities transport the true integral slash. -/
lemma lpsFunction_dilate_SL_slash_of_entries (f : ℍ→ℂ) (m : ℕ) (hm : 0 < m)
    (γ δ : SL(2,ℤ)) (k : ℤ) (hc : γ 1 0=(m:ℤ)*k)
    (h00 : δ 0 0=γ 0 0) (h01 : δ 0 1=(m:ℤ)*γ 0 1)
    (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    (((fun w : ℍ => f (lpsE2AffineMatrix m hm 0 • w)) ∣[(2:ℤ)] γ) z)=
      ((f ∣[(2:ℤ)] δ) (lpsE2AffineMatrix m hm 0 • z)) := by
  simp only [ModularForm.SL_slash_apply]
  rw [lpsE2DilationConjugate_action m hm γ δ k hc h00 h01 h10 h11,
    lpsE2DilationConjugate_denom m hm γ δ k hc h10 h11]

/-* Actual level divisibility constructs an integral conjugate and proves genuine dilated invariance. -/
lemma lpsModularForm_dilate_slash_gamma0 (N m : ℕ) (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 (N*m)) :
    ((fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) ∣[(2:ℤ)] γ)=
      (fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨t,ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (N*m)).mp hγ
  have hc : γ 1 0=(m:ℤ)*((N:ℤ)*t) := by
    rw [ht];push_cast;ring
  let δ := lpsE2DilationConjugate m γ ((N:ℤ)*t) hc
  have hδ : δ∈CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((N:ℤ)*t:ℤ):ZMod N)=0
    simp
  have hg : Matrix.SpecialLinearGroup.mapGL ℝ δ ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := ⟨δ,hδ,rfl⟩
  have hf : ((f:ℍ→ℂ) ∣[(2:ℤ)] δ)=(f:ℍ→ℂ) := by
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash,ModularForm.toSlashInvariantForm_coe] using
      SlashInvariantFormClass.slash_action_eq (Γ := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (k := (2:ℤ)) f (Matrix.SpecialLinearGroup.mapGL ℝ δ) hg
  funext z
  rw [lpsFunction_dilate_SL_slash_of_entries _ m hm γ δ ((N:ℤ)*t) hc rfl rfl rfl rfl,hf]

/-* The actual positive rational dilation matrix preserves the rational cusp set. -/
noncomputable def lpsDilationRationalMatrix (m : ℕ) (hm : 0 < m) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m:ℚ),0;0,1] (by
    rw [Matrix.det_fin_two];simpa using (show (m:ℚ)≠0 by exact_mod_cast hm.ne'))

/-* Its genuine real image is the affine matrix used by the underlying function. -/
lemma lpsDilationRationalMatrix_map (m : ℕ) (hm : 0 < m) :
    (lpsDilationRationalMatrix m hm).map (Rat.castHom ℝ)=lpsE2AffineMatrix m hm 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsDilationRationalMatrix,lpsE2AffineMatrix,Matrix.of_apply]

/-* Rational cusp transport and genuine input bounds prove every dilated rational-cusp bound. -/
lemma lpsModularForm_dilate_bounded_at_cusps (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) 2 := by
  have hs := lpsRationalGL_smul_cusp (lpsDilationRationalMatrix m hm) c hc
  rw [lpsDilationRationalMatrix_map] at hs
  have hsg : IsCusp (lpsE2AffineMatrix m hm 0 • c)
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr hs
  have hb : OnePoint.IsBoundedAt c ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsE2AffineMatrix m hm 0) 2 :=
    OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hsg)
  rw [lpsFunction_affine_slash] at hb
  have h := lpsCuspBounded_const_smul c _ (m:ℂ)⁻¹ hb
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have he : ((m:ℂ)⁻¹ • (fun z : ℍ => (m:ℂ)*f (lpsE2AffineMatrix m hm 0 • z)))=
      (fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) := by
    funext z
    simp [Pi.smul_apply,smul_eq_mul,hmC]
  rw [he] at h
  exact h

/-* Construct the genuine unnormalized f(mz) modular form from proved action, holomorphicity and bounds. -/
noncomputable def lpsModularForm_dilate (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ModularForm (CongruenceSubgroup.Gamma0 (N*m) : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := fun z => f (lpsE2AffineMatrix m hm 0 • z)
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash] using
      lpsModularForm_dilate_slash_gamma0 N m hm f γ hγ
  holo' := by
    apply f.holo'.comp
    apply UpperHalfPlane.mdifferentiable_smul
    rw [lpsE2AffineMatrix_det]
    exact_mod_cast hm
  bdd_at_cusps' := fun hc => lpsModularForm_dilate_bounded_at_cusps N m hm f _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))

/-* The bundled dilation keeps the actual unnormalized dilated function. -/
lemma lpsModularForm_dilate_apply (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsModularForm_dilate N m hm f z=f (lpsE2AffineMatrix m hm 0 • z) := rfl

/-* The true dilation coefficient reindexes multiples and is zero off the multiplication range. -/
noncomputable def lpsModularDilationCoefficient (a : ℕ→ℂ) (m n : ℕ) : ℂ :=
  if m∣n then a (n/m) else 0

/-* Actual nome dilation and injective reindexing prove the complete convergent dilated series. -/
lemma lpsModularForm_dilate_hasSum (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => lpsModularDilationCoefficient
      (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) m n *
        Function.Periodic.qParam 1 (z:ℂ)^n) (lpsModularForm_dilate N m hm f z) := by
  let a : ℕ→ℂ := fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)
  let g : ℕ→ℂ := fun n => lpsModularDilationCoefficient a m n *
    Function.Periodic.qParam 1 (z:ℂ)^n
  have hi : Function.Injective (fun n : ℕ => m*n) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hm hxy
  have ho : ∀ n, n∉Set.range (fun k : ℕ => m*k) → g n=0 := by
    intro n hn
    have hnd : ¬m∣n := by
      rintro ⟨k,hk⟩
      exact hn ⟨k,hk.symm⟩
    simp [g,lpsModularDilationCoefficient,hnd]
  have hp : (1:ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hs := ModularForm.hasSum_qExpansion f (by norm_num : (0:ℝ)<1) hp
    (lpsE2AffineMatrix m hm 0 • z)
  rw [lpsE2AffineMatrix_qParam] at hs
  have hcomp : HasSum (g ∘ (fun n : ℕ => m*n))
      (f (lpsE2AffineMatrix m hm 0 • z)) := by
    apply hs.congr_fun
    intro n
    have hd : m∣m*n := dvd_mul_right _ _
    have hdiv : m*n/m=n := Nat.mul_div_cancel_left n hm
    simp only [Function.comp_def,g,lpsModularDilationCoefficient,if_pos hd,hdiv,pow_mul,a]
  exact (hi.hasSum_iff ho).mp hcomp

/-* Analytic uniqueness identifies every actual dilated q-expansion coefficient. -/
lemma coeff_qExpansion_lpsModularForm_dilate (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsModularForm_dilate N m hm f))=
      lpsModularDilationCoefficient
        (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) m n := by
  have hp : (1:ℝ) ∈ (CongruenceSubgroup.Gamma0 (N*m) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  symm
  exact ModularFormClass.qExpansion_coeff_unique (by norm_num : (0:ℝ)<1) hp
    (fun z => by simpa only [smul_eq_mul] using lpsModularForm_dilate_hasSum N m hm f z) n

/-* Instantiate the genuine modular dilation with the already proved chi4 Eisenstein form. -/
noncomputable def lpsChi4E2DilateModularForm (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 (16*m) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_dilate 16 m hm lpsChi4E2TwistModularForm

/-* This actual bundled form is the existing chi4-dilated function. -/
lemma lpsChi4E2DilateModularForm_apply (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsChi4E2DilateModularForm m hm z=lpsChi4E2Dilate m hm z := rfl

/-* Actual chi4 dilation coefficients retain their divisor and character values at n/m. -/
lemma coeff_qExpansion_lpsChi4E2DilateModularForm (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4E2DilateModularForm m hm))=
      if m∣n then -24*(ArithmeticFunction.sigma 1 (n/m):ℂ)*lpsChi4E2Character ((n/m:ℕ):ZMod 4) else 0 := by
  rw [lpsChi4E2DilateModularForm,coeff_qExpansion_lpsModularForm_dilate]
  unfold lpsModularDilationCoefficient
  simp only [coeff_qExpansion_lpsChi4E2TwistModularForm]

/-* Instantiate the genuine modular dilation with the already proved prime-character form. -/
noncomputable def lpsQuadraticE2DilateModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 (q^2*m) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_dilate (q^2) m hm (lpsQuadraticE2TwistModularForm q hq2)

/-* This actual bundled form is the existing prime-character dilated function. -/
lemma lpsQuadraticE2DilateModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsQuadraticE2DilateModularForm q hq2 m hm z=lpsQuadraticE2Dilate q m hm z := rfl

/-* Actual prime-character coefficients include off-range and prime-nonunit zeros. -/
lemma coeff_qExpansion_lpsQuadraticE2DilateModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2DilateModularForm q hq2 m hm))=
      if m∣n then -24*(ArithmeticFunction.sigma 1 (n/m):ℂ)*lpsQuadraticE2Character q ((n/m:ℕ):ZMod q) else 0 := by
  rw [lpsQuadraticE2DilateModularForm,coeff_qExpansion_lpsModularForm_dilate]
  unfold lpsModularDilationCoefficient
  simp only [coeff_qExpansion_lpsQuadraticE2TwistModularForm]

/-* Instantiate the genuine modular dilation with the already proved iterated-character form. -/
noncomputable def lpsChi4PrimeE2DilateModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2*m) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_dilate ((4*q)^2) m hm (lpsChi4PrimeE2TwistModularForm q hq2)

/-* This actual bundled form is the existing double-character dilated function. -/
lemma lpsChi4PrimeE2DilateModularForm_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) (z : ℍ) :
    lpsChi4PrimeE2DilateModularForm q hq2 m hm z=lpsChi4PrimeE2Dilate q m hm z := rfl

/-* Actual iterated coefficients preserve both genuine characters and no determinant multiplier. -/
lemma coeff_qExpansion_lpsChi4PrimeE2DilateModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2DilateModularForm q hq2 m hm))=
      if m∣n then -24*(ArithmeticFunction.sigma 1 (n/m):ℂ)*
        lpsQuadraticE2Character q ((n/m:ℕ):ZMod q)*lpsChi4E2Character ((n/m:ℕ):ZMod 4) else 0 := by
  rw [lpsChi4PrimeE2DilateModularForm,coeff_qExpansion_lpsModularForm_dilate]
  unfold lpsModularDilationCoefficient
  simp only [coeff_qExpansion_lpsChi4PrimeE2TwistModularForm]

/-* The actual bounded exponents give all untwisted basis levels dividing the theta level. -/
lemma lpsThetaBasis_level_dvd (q : ℕ) (a : Fin 5) (b : Fin 3) :
    2^a.val*q^b.val ∣ (4*q)^2 := by
  have h2 : 2^a.val ∣ (2:ℕ)^4 := pow_dvd_pow 2 (by omega)
  have hq : q^b.val ∣ q^2 := pow_dvd_pow q (by omega)
  have h := mul_dvd_mul h2 hq
  norm_num only [Nat.reducePow] at h
  simpa only [mul_pow,Nat.reducePow] using h

/-* Put every actual E2 difference divisor into the genuine common theta-level form space. -/
noncomputable def lpsE2DifferenceThetaBasis (q : ℕ) [Fact q.Prime] (a : Fin 5) (b : Fin 3) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (2^a.val*q^b.val) ((4*q)^2)
    (lpsThetaBasis_level_dvd q a b)
    (lpsE2DifferenceModularForm (2^a.val*q^b.val)
      (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)))

/-* Common-level restriction preserves the actual E2-difference function. -/
lemma lpsE2DifferenceThetaBasis_apply (q : ℕ) [Fact q.Prime] (a : Fin 5) (b : Fin 3) (z : ℍ) :
    lpsE2DifferenceThetaBasis q a b z=lpsE2Difference (2^a.val*q^b.val)
      (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)) z := rfl

/-* Every untwisted common-level coefficient is the actual divisor-difference coefficient. -/
lemma coeff_qExpansion_lpsE2DifferenceThetaBasis (q : ℕ) [Fact q.Prime]
    (a : Fin 5) (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2DifferenceThetaBasis q a b))=
      lpsE2DifferenceCoefficient (2^a.val*q^b.val) n :=
  coeff_qExpansion_lpsE2DifferenceModularForm _ _ n

/-* Put the three actual chi4 dilations into the genuine common theta-level form space. -/
noncomputable def lpsChi4E2ThetaBasis (q : ℕ) [Fact q.Prime] (b : Fin 3) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (16*q^b.val) ((4*q)^2)
    (by simpa using lpsThetaBasis_level_dvd q (4:Fin 5) b)
    (lpsChi4E2DilateModularForm (q^b.val) (pow_pos (Fact.out : q.Prime).pos _))

/-* The common-level chi4 function remains the true q-power dilation. -/
lemma lpsChi4E2ThetaBasis_apply (q : ℕ) [Fact q.Prime] (b : Fin 3) (z : ℍ) :
    lpsChi4E2ThetaBasis q b z=lpsChi4E2Dilate (q^b.val) (pow_pos (Fact.out : q.Prime).pos _) z := rfl

/-* The common-level chi4 forms retain the proved reindexed Fourier coefficients. -/
lemma coeff_qExpansion_lpsChi4E2ThetaBasis (q : ℕ) [Fact q.Prime] (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4E2ThetaBasis q b))=
      if q^b.val∣n then -24*(ArithmeticFunction.sigma 1 (n/q^b.val):ℂ)*
        lpsChi4E2Character ((n/q^b.val:ℕ):ZMod 4) else 0 :=
  coeff_qExpansion_lpsChi4E2DilateModularForm _ _ n

/-* Put the five actual prime-character dilations into the genuine common theta-level form space. -/
noncomputable def lpsQuadraticE2ThetaBasis (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : Fin 5) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (q^2*2^a.val) ((4*q)^2)
    (by
      have h := lpsThetaBasis_level_dvd q a (2:Fin 3)
      change 2^a.val*q^2 ∣ (4*q)^2 at h
      simpa only [mul_comm] using h)
    (lpsQuadraticE2DilateModularForm q hq2 (2^a.val) (pow_pos (by decide) _))

/-* The common-level prime-character function remains the true two-power dilation. -/
lemma lpsQuadraticE2ThetaBasis_apply (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : Fin 5) (z : ℍ) :
    lpsQuadraticE2ThetaBasis q hq2 a z=
      lpsQuadraticE2Dilate q (2^a.val) (pow_pos (by decide) _) z := rfl

/-* The common-level prime-character forms retain every actual reindexed Fourier coefficient. -/
lemma coeff_qExpansion_lpsQuadraticE2ThetaBasis (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2ThetaBasis q hq2 a))=
      if 2^a.val∣n then -24*(ArithmeticFunction.sigma 1 (n/2^a.val):ℂ)*
        lpsQuadraticE2Character q ((n/2^a.val:ℕ):ZMod q) else 0 :=
  coeff_qExpansion_lpsQuadraticE2DilateModularForm q hq2 _ _ n

end QEC.Coding.TannerLiftedProduct
