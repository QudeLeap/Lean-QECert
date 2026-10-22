import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# LPSGamma0Stabilizers

For the actual integral Gamma0 group at levels divisible by four, the determinant and true Mobius fixed-point equation force every upper-half-plane stabilizer to be plus or minus identity. No stabilizer or freeness law is assumed.
This is the noncompact analytic quotient. Cusp compactification, algebraic modular curves,
arithmetic Hecke/Frobenius correspondence and the PK22 magnitude bound remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane
noncomputable section

/-- The true fixed-point quadratic gives an exact nonnegative trace defect. -/
lemma lpsFixedPoint_trace_identity (g : GL (Fin 2) ℝ) (hdet : g.val.det=1)
    (τ : ℍ) (hfix : g • τ=τ) :
    g.val.trace^2+4*(g 1 0)^2*τ.im^2=4 := by
  have hq := (UpperHalfPlane.gl_smul_eq_self_iff_quadratic (by rw [hdet];norm_num)).mp hfix
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp [Complex.mul_re,Complex.mul_im] at hre him
  have hdiag : 2*(g 1 0)*τ.re+g 1 1-g 0 0=0 := by
    have hm : (2*(g 1 0)*τ.re+g 1 1-g 0 0)*τ.im=0 := by nlinarith [him]
    exact (mul_eq_zero.mp hm).resolve_right τ.im_ne_zero
  have hr := congrArg (fun x : ℝ => (g 1 0)*x) hre
  have hi := congrArg (fun x : ℝ => (g 1 0)*τ.re*x) hdiag
  have hs := congrArg (fun x : ℝ => x^2) hdiag
  rw [Matrix.trace_fin_two]
  rw [Matrix.det_fin_two] at hdet
  nlinarith [hr,hi,hs]

/-- The actual fixed-point equations and trace2 force the true matrix to be identity. -/
lemma lpsFixedPoint_trace_two_eq_one (g : GL (Fin 2) ℝ) (hdet : g.val.det=1)
    (htrace : g.val.trace=2) (τ : ℍ) (hfix : g • τ=τ) : g=1 := by
  have hi := lpsFixedPoint_trace_identity g hdet τ hfix
  rw [htrace] at hi
  have hz : ((g 1 0)*τ.im)^2=0 := by nlinarith [hi]
  have hm := sq_eq_zero_iff.mp hz
  have hc : g 1 0=0 := (mul_eq_zero.mp hm).resolve_right τ.im_ne_zero
  have ht := htrace
  rw [Matrix.trace_fin_two] at ht
  have hd := hdet
  rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hd
  have hdd : g 1 1=2-g 0 0 := by linarith [ht]
  rw [hdd] at hd
  have ha0 : (g 0 0-1)^2=0 := by nlinarith [hd]
  have ha : g 0 0=1 := sub_eq_zero.mp (sq_eq_zero_iff.mp ha0)
  have hd1 : g 1 1=1 := by linarith [ht]
  have hq := (UpperHalfPlane.gl_smul_eq_self_iff_quadratic (by rw [hdet];norm_num)).mp hfix
  simp only [hc,ha,hd1,Complex.ofReal_zero,Complex.ofReal_one,
    zero_mul,sub_self,zero_add,add_zero,neg_eq_zero] at hq
  have hb : g 0 1=0 := by exact_mod_cast hq
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha,hb,hc,hd1]

/-- Modulo four, a genuine determinant-one diagonal has trace two. -/
lemma lpsZModFour_trace (a d : ZMod 4) (h : a*d=1) : a+d=2 := by
  revert a d
  decide

/-- The original Gamma0 condition and determinant imply the exact mod-four trace. -/
lemma lpsGamma0_trace_sub_two_dvd (N : ℕ) (hN : 4∣N) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    (4:ℤ)∣(γ:Matrix (Fin 2) (Fin 2) ℤ).trace-2 := by
  have hNc : (N:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have h4N : (4:ℤ)∣(N:ℤ) := by exact_mod_cast hN
  have h4c := h4N.trans hNc
  have hc : (γ 1 0:ZMod 4)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h4c
  have hd := γ.det_coe
  rw [Matrix.det_fin_two] at hd
  have hz := congrArg (Int.castRingHom (ZMod 4)) hd
  change (((γ 0 0*γ 1 1-γ 0 1*γ 1 0:ℤ):ZMod 4))=1 at hz
  simp only [Int.cast_sub,Int.cast_mul,hc,mul_zero,sub_zero] at hz
  have ht := lpsZModFour_trace (γ 0 0) (γ 1 1) hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa [Matrix.trace_fin_two] using sub_eq_zero.mpr ht

/-- The true fixed-point equation and mod-four arithmetic leave only the two central traces. -/
lemma lpsGamma0_fixed_trace (N : ℕ) (hN : 4∣N) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 N) (τ : ℍ)
    (hfix : Matrix.SpecialLinearGroup.mapGL ℝ γ • τ=τ) :
    (γ:Matrix (Fin 2) (Fin 2) ℤ).trace=2 ∨
      (γ:Matrix (Fin 2) (Fin 2) ℤ).trace= -2 := by
  have hd : (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.det=1 := by
    simp only [← Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hi := lpsFixedPoint_trace_identity _ hd τ hfix
  have he : (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.trace=
      ((γ:Matrix (Fin 2) (Fin 2) ℤ).trace:ℝ) := by
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.trace_fin_two]
  rw [he] at hi
  have ht : ((γ:Matrix (Fin 2) (Fin 2) ℤ).trace:ℝ)^2≤4 := by
    nlinarith [sq_nonneg (((Matrix.SpecialLinearGroup.mapGL ℝ γ) 1 0)*τ.im)]
  have hti : (γ:Matrix (Fin 2) (Fin 2) ℤ).trace^2≤4 := by exact_mod_cast ht
  have htb : -2≤(γ:Matrix (Fin 2) (Fin 2) ℤ).trace ∧
      (γ:Matrix (Fin 2) (Fin 2) ℤ).trace≤2 := by constructor <;> nlinarith
  obtain ⟨k,hk⟩ := lpsGamma0_trace_sub_two_dvd N hN γ hγ
  omega

/-- The actual original Gamma0 fixed-point matrices are central, without any freeness input. -/
lemma lpsGamma0_fixed_mapGL (N : ℕ) (hN : 4∣N) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 N) (τ : ℍ)
    (hfix : Matrix.SpecialLinearGroup.mapGL ℝ γ • τ=τ) :
    Matrix.SpecialLinearGroup.mapGL ℝ γ=1 ∨
      Matrix.SpecialLinearGroup.mapGL ℝ γ= -1 := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hd : g.val.det=1 := by
    simp only [g,← Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have he : g.val.trace=((γ:Matrix (Fin 2) (Fin 2) ℤ).trace:ℝ) := by
    simp [g,Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.trace_fin_two]
  rcases lpsGamma0_fixed_trace N hN γ hγ τ hfix with hp|hm
  · left
    apply lpsFixedPoint_trace_two_eq_one g hd _ τ hfix
    rw [he,hp]; norm_num
  · right
    have hdn : (-g).val.det=1 := by simpa [Matrix.det_neg] using hd
    have htn : (-g).val.trace=2 := by simp [Matrix.trace_neg,he,hm]
    have hfn : -g • τ=τ := by simpa only [UpperHalfPlane.neg_smul] using hfix
    have hi := lpsFixedPoint_trace_two_eq_one (-g) hdn htn τ hfn
    exact neg_injective (by simpa using hi)

end
end QEC.Coding.TannerLiftedProduct
