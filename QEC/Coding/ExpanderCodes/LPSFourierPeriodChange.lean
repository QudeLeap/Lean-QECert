import QEC.Coding.ExpanderCodes.LPSHeckeCoefficients
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Congruence Sturm and genuine finite-dimensional Hecke spaces

Internal proof closure for the original PK22 theta route. Fourier width, actual
coset norm and level-one Sturm give a finite coefficient injection at Gamma0(N).
The finite basis and matrices describe the already proved weight-two operators.
The arithmetic spectral bound and public theorem pk-good-qldpc remain unproved;
parent #449 remains open. No spectral or finite-dimensional conclusion is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

/-- An integer change of Fourier width raises the actual nome to the unit-width nome. -/
lemma lpsQParam_integerWidth_pow (m : ℕ) (hm : 0 < m) (z : ℍ) :
    Function.Periodic.qParam (m:ℝ) (z:ℂ)^m=Function.Periodic.qParam 1 (z:ℂ) := by
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  simp only [Function.Periodic.qParam,Complex.ofReal_natCast,Complex.ofReal_one,div_one]
  rw [←Complex.exp_nat_mul]
  congr 1
  field_simp

/-- The expanded actual unit-width coefficients sum to the original modular form. -/
lemma lpsHasSum_integerWidth (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) (z : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n
      ((UpperHalfPlane.qExpansion 1 f).expand m hm.ne')*
        Function.Periodic.qParam (m:ℝ) (z:ℂ)^n) (f z) := by
  let : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods (by norm_num) h1⟩
  let g : ℕ→ℂ := fun n => PowerSeries.coeff n
    ((UpperHalfPlane.qExpansion 1 f).expand m hm.ne')*
      Function.Periodic.qParam (m:ℝ) (z:ℂ)^n
  have hi : Function.Injective (fun n : ℕ => m*n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hm hab
  have ho : ∀ n, n∉Set.range (fun a : ℕ => m*a) → g n=0 := by
    intro n hn
    have hnd : ¬m∣n := by rintro ⟨a,ha⟩;exact hn ⟨a,ha.symm⟩
    simp [g,PowerSeries.coeff_expand_of_not_dvd m hm.ne' _ hnd]
  have hf := ModularForm.hasSum_qExpansion f (by norm_num : (0:ℝ)<1) h1 z
  have hg : HasSum (g ∘ (fun n : ℕ => m*n)) (f z) := by
    apply hf.congr_fun
    intro n
    simp only [Function.comp_def,g,PowerSeries.coeff_expand_mul,pow_mul,lpsQParam_integerWidth_pow m hm]
  exact (hi.hasSum_iff ho).mp hg

/-- The actual integer-width Fourier expansion is the formal expansion of its unit-width series. -/
lemma lpsQExpansion_integerWidth (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) :
    UpperHalfPlane.qExpansion (m:ℝ) f=(UpperHalfPlane.qExpansion 1 f).expand m hm.ne' := by
  have hmΓ : (m:ℝ)∈Γ.strictPeriods := by
    simpa only [nsmul_eq_mul,mul_one] using Γ.strictPeriods.nsmul_mem h1 m
  ext n
  symm
  exact ModularFormClass.qExpansion_coeff_unique (by exact_mod_cast hm) hmΓ
    (fun z => by simpa only [smul_eq_mul] using lpsHasSum_integerWidth Γ k h1 m hm f z) n

/-- An integer change of width multiplies the actual Fourier order, including infinite order. -/
lemma lpsQExpansion_integerWidth_order (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) :
    (UpperHalfPlane.qExpansion (m:ℝ) f).order=m • (UpperHalfPlane.qExpansion 1 f).order := by
  rw [lpsQExpansion_integerWidth Γ k h1 m hm f,PowerSeries.order_expand]

end QEC.Coding.TannerLiftedProduct
