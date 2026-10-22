import QEC.Coding.ExpanderCodes.LPSCuspHecke
import QEC.Coding.ExpanderCodes.LPSHeckePolynomial

/-!
# Exact Fourier action and prime-power recovery of the true Hecke operator

Convergent expansions, finite additive-character filtering and analytic uniqueness
prove a(T_p f,n)=a(f,p*n)+p*a(f,n/p), with the latter term zero off multiples of p.
The actual operator is complex linear. The prime-power recurrence constructs
endomorphisms equal to evaluation of the existing lpsHeckePolynomial at T_p;
their first Fourier coefficient recovers every a(f,p^r), for arbitrary cusp forms.
No eigenform assumption or supplied coefficient/bound appears.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The infinity representative is the existing genuine affine dilation matrix. -/
lemma lpsHeckeUpperGL_infty (p : ℕ) [Fact p.Prime] :
    lpsHeckeUpperGL ℝ p none=lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 := by
  apply Units.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperGL,lpsHeckeUpperMatrix,lpsE2AffineMatrix,Matrix.map_apply,Matrix.of_apply]

/-- The finite representative acts by the actual map z to (z+j)/p. -/
lemma lpsHeckeUpperGL_finite_action (p : ℕ) [Fact p.Prime] (j : Fin p) (z : ℍ) :
    ((lpsHeckeUpperGL ℝ p (some j) • z:ℍ):ℂ)=((z:ℂ)+(j.val:ℂ))/(p:ℂ) := by
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  simp only [UpperHalfPlane.coe_smul,UpperHalfPlane.σ,lpsHeckeUpperGL_det,if_pos hp]
  simp [UpperHalfPlane.num,UpperHalfPlane.denom,lpsHeckeUpperGL,lpsHeckeUpperMatrix,
    Matrix.map_apply,Matrix.of_apply]

/-- The finite representative slash multiplier is exactly 1/p in weight two. -/
lemma lpsHeckeUpperGL_finite_slash (p : ℕ) [Fact p.Prime] (j : Fin p) (f : ℍ→ℂ) :
    (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some j))=
      (fun z : ℍ => (p:ℂ)⁻¹*f (lpsHeckeUpperGL ℝ p (some j) • z)) := by
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpC : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  funext z
  simp only [ModularForm.slash_apply,UpperHalfPlane.σ,lpsHeckeUpperGL_det,if_pos hp,abs_of_pos hp]
  simp [UpperHalfPlane.denom,lpsHeckeUpperGL,lpsHeckeUpperMatrix,Matrix.map_apply,Matrix.of_apply]
  field_simp

/-- The actual translated nome splits into its finite additive phase and p-width nome. -/
lemma lpsHeckeUpperGL_finite_qParam (p : ℕ) [Fact p.Prime] (j : Fin p) (z : ℍ) :
    Function.Periodic.qParam 1 ((lpsHeckeUpperGL ℝ p (some j) • z:ℍ):ℂ)=
      ZMod.stdAddChar (j.val:ZMod p)*Function.Periodic.qParam (p:ℝ) (z:ℂ) := by
  rw [lpsHeckeUpperGL_finite_action]
  have he := ZMod.stdAddChar_coe (N:=p) (j.val:ℤ)
  rw [Int.cast_natCast] at he
  rw [he]
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one,Complex.ofReal_natCast,Int.cast_natCast]
  rw [show (2:ℂ)*Real.pi*I*(((z:ℂ)+(j.val:ℂ))/(p:ℂ))=
    (2:ℂ)*Real.pi*I*(j.val:ℂ)/(p:ℂ)+(2:ℂ)*Real.pi*I*(z:ℂ)/(p:ℂ) by ring,
    Complex.exp_add]

/-- Taking the p-th power of the p-width nome recovers the unit-width nome. -/
lemma lpsHeckeQParam_pow (p : ℕ) [Fact p.Prime] (z : ℍ) :
    Function.Periodic.qParam (p:ℝ) (z:ℂ)^p=Function.Periodic.qParam 1 (z:ℂ) := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [Function.Periodic.qParam,Complex.ofReal_natCast,Complex.ofReal_one,div_one]
  rw [←Complex.exp_nat_mul]
  congr 1
  field_simp

/-- The genuine finite additive-character sum selects precisely the multiples of p. -/
lemma lpsHeckePhaseFilter (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (∑ j : Fin p,ZMod.stdAddChar (j.val:ZMod p)^n)=if p∣n then (p:ℂ) else 0 := by
  have h := lpsChar_mask_sum p 1 (n:ℤ)
  simp only [Nat.cast_one,one_mul,Int.cast_natCast,ZMod.natCast_eq_zero_iff] at h
  rw [←h]
  apply Finset.sum_congr rfl
  intro j _
  have he := lpsChar_inflate p 1 ((j.val:ℤ)*(n:ℤ))
  simp only [Nat.cast_one,one_mul] at he
  rw [he]
  have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=p)) n (j.val:ZMod p)
  simpa only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,mul_comm] using hc.symm

/-- Finite summation of actual convergent Fourier expansions filters out nonmultiples of p. -/
lemma lpsHeckeFinite_hasSum_mask (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => if p∣n then
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        Function.Periodic.qParam (p:ℝ) (z:ℂ)^n else 0)
      ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) := by
  classical
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hs (j : Fin p) := ModularForm.hasSum_qExpansion f (by norm_num : (0:ℝ)<1) hp
    (lpsHeckeUpperGL ℝ p (some j) • z)
  have h := (hasSum_sum (s:=Finset.univ) (fun (j : Fin p) _ => hs j)).mul_left ((p:ℂ)⁻¹)
  apply h.congr_fun
  intro n
  simp_rw [lpsHeckeUpperGL_finite_qParam,mul_pow]
  rw [show (∑ j : Fin p,PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
    (ZMod.stdAddChar (j.val:ZMod p)^n*Function.Periodic.qParam (p:ℝ) (z:ℂ)^n))=
      (PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*Function.Periodic.qParam (p:ℝ) (z:ℂ)^n)*
        (∑ j : Fin p,ZMod.stdAddChar (j.val:ZMod p)^n) by
          rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring]
  rw [lpsHeckePhaseFilter]
  by_cases hn : p∣n
  · simp only [if_pos hn]
    have hpC : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp
  · simp [hn]

/-- Injective reindexing proves the actual finite part has coefficients a(p*n). -/
lemma lpsHeckeFinite_hasSum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)*
      Function.Periodic.qParam 1 (z:ℂ)^n)
      ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) := by
  let g : ℕ→ℂ := fun n => if p∣n then
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      Function.Periodic.qParam (p:ℝ) (z:ℂ)^n else 0
  have hg : HasSum g ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) :=
    lpsHeckeFinite_hasSum_mask N p f z
  have hi : Function.Injective (fun n : ℕ => p*n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hab
  have ho : ∀ n, n∉Set.range (fun k : ℕ => p*k) → g n=0 := by
    intro n hn
    have hnd : ¬p∣n := by
      rintro ⟨k,hk⟩
      exact hn ⟨k,hk.symm⟩
    simp [g,hnd]
  have h := (hi.hasSum_iff ho).mpr hg
  apply h.congr_fun
  intro n
  dsimp only [Function.comp_def,g]
  rw [if_pos (dvd_mul_right p n),pow_mul,lpsHeckeQParam_pow]

/-- The genuine affine dilation contributes exactly p times the dilation coefficient. -/
lemma lpsHeckeInfty_hasSum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => (p:ℂ)*lpsModularDilationCoefficient
      (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n *
        Function.Periodic.qParam 1 (z:ℂ)^n)
      ((p:ℂ)*f (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • z)) := by
  have h := lpsModularForm_dilate_hasSum N p (Fact.out : p.Prime).pos (f : ModularForm _ 2) z
  have hcast : ((f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) : ℍ→ℂ)=
      (f:ℍ→ℂ) := rfl
  rw [hcast] at h
  have ht := h.mul_left (p:ℂ)
  apply ht.congr_fun
  intro n
  ring

/-- The actual operator has the explicit infinity and finite weighted function values. -/
lemma lpsCuspHecke_apply (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsCuspHecke N p hNp f z =
      (p:ℂ)*f (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • z)+
        (p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z) := by
  classical
  change lpsHeckeSlashSum p (f:ℍ→ℂ) z=_
  unfold lpsHeckeSlashSum
  rw [Finset.sum_apply]
  rw [Fintype.sum_option,lpsHeckeUpperGL_infty,lpsFunction_affine_slash]
  simp_rw [lpsHeckeUpperGL_finite_slash]
  simp only [←Finset.mul_sum]

/-- The exact coefficient formula gives a convergent expansion of the actual operator. -/
lemma lpsCuspHecke_hasSum (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => (PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)+
      (p:ℂ)*lpsModularDilationCoefficient
        (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n)*
          Function.Periodic.qParam 1 (z:ℂ)^n) (lpsCuspHecke N p hNp f z) := by
  rw [lpsCuspHecke_apply]
  apply ((lpsHeckeInfty_hasSum N p f z).add (lpsHeckeFinite_hasSum N p f z)).congr_fun
  intro n
  ring

/-- Analytic uniqueness identifies every actual Hecke Fourier coefficient. -/
lemma coeff_qExpansion_lpsCuspHecke (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f))=
      PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)+
        (p:ℂ)*lpsModularDilationCoefficient
          (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) p n := by
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  symm
  exact ModularFormClass.qExpansion_coeff_unique (by norm_num : (0:ℝ)<1) hp
    (fun z => by simpa only [smul_eq_mul] using lpsCuspHecke_hasSum N p hNp f z) n

/-- The true action preserves addition. -/
lemma lpsCuspHecke_add (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspHecke N p hNp (f+g)=lpsCuspHecke N p hNp f+lpsCuspHecke N p hNp g := by
  classical
  ext z
  simp only [lpsCuspHecke_apply,FunLike.coe_add,Pi.add_apply,Finset.sum_add_distrib]
  ring

/-- Positive determinants make the actual action complex linear. -/
lemma lpsCuspHecke_smul (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (c : ℂ) :
    lpsCuspHecke N p hNp (c • f)=c • lpsCuspHecke N p hNp f := by
  classical
  ext z
  simp only [lpsCuspHecke_apply,FunLike.coe_smul,Pi.smul_apply,smul_eq_mul,←Finset.mul_sum]
  ring

/-- The genuine Hecke endomorphism with proved complex linearity. -/
noncomputable def lpsCuspHeckeLinearMap (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsCuspHecke N p hNp
  map_add' := lpsCuspHecke_add N p hNp
  map_smul' c f := lpsCuspHecke_smul N p hNp f c

/-- The exact prime-power coefficient recurrence, including the exponent-zero boundary. -/
lemma coeff_qExpansion_lpsCuspHecke_prime_power (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (r : ℕ) :
    PowerSeries.coeff (p^(r+1)) (UpperHalfPlane.qExpansion 1 f)=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f))-
        if r=0 then 0 else (p:ℂ)*PowerSeries.coeff (p^(r-1)) (UpperHalfPlane.qExpansion 1 f) := by
  rw [coeff_qExpansion_lpsCuspHecke]
  cases r with
  | zero =>
    have hd : ¬p∣1 := (Fact.out : p.Prime).not_dvd_one
    simp [lpsModularDilationCoefficient,hd]
  | succ r =>
    have hp : 0<p := (Fact.out : p.Prime).pos
    have hd : p∣p^(r+1) := by rw [pow_succ];exact dvd_mul_left p (p^r)
    have he : p^(r+1)/p=p^r := by rw [pow_succ,Nat.mul_div_cancel _ hp]
    change PowerSeries.coeff (p^(r+1+1)) (UpperHalfPlane.qExpansion 1 f)=_
    rw [lpsModularDilationCoefficient,if_pos hd,he]
    simp only [Nat.succ_ne_zero,if_false,Nat.succ_sub_one]
    rw [pow_succ,mul_comm p (p^(r+1))]
    exact (add_sub_cancel_right _ _).symm

/-- The actual recursively composed prime-power endomorphisms. -/
noncomputable def lpsHeckePrimePowerLinearMap (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : ℕ →
    Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
  | 0 => LinearMap.id
  | 1 => lpsCuspHeckeLinearMap N p hNp
  | r+2 => (lpsHeckePrimePowerLinearMap N p hNp (r+1)).comp
      (lpsCuspHeckeLinearMap N p hNp)-(p:ℂ) • lpsHeckePrimePowerLinearMap N p hNp r

/-- The first coefficient of each constructed endomorphism recovers a(p^r) for every cusp form. -/
lemma coeff_one_lpsHeckePrimePowerLinearMap (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsHeckePrimePowerLinearMap N p hNp r f))=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) := by
  have hperiod : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  induction r using Nat.twoStepInduction generalizing f with
  | zero => rfl
  | one =>
    change PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f))=_
    rw [coeff_qExpansion_lpsCuspHecke]
    have hd : ¬p∣1 := (Fact.out : p.Prime).not_dvd_one
    simp [lpsModularDilationCoefficient,hd]
  | more r ih0 ih1 =>
    change PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
      (lpsHeckePrimePowerLinearMap N p hNp (r+1) (lpsCuspHecke N p hNp f)-
        (p:ℂ) • lpsHeckePrimePowerLinearMap N p hNp r f))=_
    have hs := ModularForm.qExpansion_sub (by norm_num : (0:ℝ)<1) hperiod
        (lpsHeckePrimePowerLinearMap N p hNp (r+1) (lpsCuspHecke N p hNp f))
        ((p:ℂ) • lpsHeckePrimePowerLinearMap N p hNp r f)
    simp only [FunLike.coe_smul] at hs
    rw [hs,ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1) hperiod (p:ℂ)
        (lpsHeckePrimePowerLinearMap N p hNp r f),
      map_sub,PowerSeries.coeff_smul,ih1,ih0]
    have h := coeff_qExpansion_lpsCuspHecke_prime_power N p hNp f (r+1)
    simpa only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,Nat.add_sub_cancel,
      smul_eq_mul] using h.symm

/-- The recursive endomorphism is evaluation of the existing Hecke polynomial at the actual operator. -/
lemma lpsHeckePrimePowerLinearMap_eq_polynomial (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) :
    lpsHeckePrimePowerLinearMap N p hNp r=
      (lpsHeckePolynomial ℂ (p:ℂ) r).eval₂
        (algebraMap ℂ (Module.End ℂ (CuspForm
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
        (lpsCuspHeckeLinearMap N p hNp) := by
  induction r using Nat.twoStepInduction with
  | zero => simp only [lpsHeckePrimePowerLinearMap,lpsHeckePolynomial_zero,Polynomial.eval₂_one];rfl
  | one => simp [lpsHeckePrimePowerLinearMap]
  | more r ih0 ih1 =>
    rw [lpsHeckePrimePowerLinearMap,lpsHeckePolynomial_add_two,
      Polynomial.eval₂_sub,Polynomial.eval₂_X_mul]
    rw [Polynomial.eval₂_mul_noncomm _ _
      (fun k => Algebra.commute_algebraMap_left _ _),Polynomial.eval₂_C,←ih0,←ih1]
    rfl


end QEC.Coding.TannerLiftedProduct
