import QEC.Coding.ExpanderCodes.LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod

/-!
# Actual cyclic Fourier coefficients of the theta characteristic transform

Finite reindexing proves quadratic completion of the square and character
translation vanishing for the genuine cyclic exponential sum. The Fin-to-ZMod
bridge and absolute summability identify the characteristic transform's actual
integer Fourier expansion. At modulus `4*s*k`, translation forces support on
multiples of `2*s`; determinant one gives the exact phase of every remaining
coefficient. Reindexing this supported series cancels the rational shift and
recovers the original Jacobi theta times the actual Gauss sum.

The cyclic index ring is not a quantum-code field restriction. These are proved
finite-character and analytic identities, not assumed transformations, normalized
Gauss evaluations, or arithmetic growth. They supply the four-factor scalar law
and the subsequent finite-character Gauss-normalization proof.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Real

/-- Actual finite quadratic Fourier coefficient on a positive cyclic modulus. -/
noncomputable def lpsQuadraticFourier (N : ℕ) [NeZero N] (a n : ZMod N) : ℂ :=
  ∑ r : ZMod N, ZMod.stdAddChar (a*r^2+n*r)

/-- Translation of the finite cyclic index completes the square. -/
lemma lpsQuadraticFourier_completeSquare (N : ℕ) [NeZero N] (a t : ZMod N) :
    lpsQuadraticFourier N a (2*a*t) =
      ZMod.stdAddChar (-a*t^2) * lpsQuadraticFourier N a 0 := by
  unfold lpsQuadraticFourier
  rw [Finset.mul_sum]
  have h := Equiv.sum_comp (Equiv.addRight t) (fun r : ZMod N => ZMod.stdAddChar (-a*t^2) * ZMod.stdAddChar (a*r^2+0*r))
  rw [← h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Equiv.coe_addRight]
  ring

/-- A genuine nontrivial phase under an invariant quadratic translation forces vanishing. -/
lemma lpsQuadraticFourier_zero_of_translation (N : ℕ) [NeZero N] (a n t : ZMod N)
    (hlinear : 2*a*t=0) (hquadratic : a*t^2=0) (hn : n*t≠0) :
    lpsQuadraticFourier N a n=0 := by
  have he : ZMod.stdAddChar (n*t)≠(1:ℂ) := by
    intro h
    apply hn
    exact ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
  have hshift : ZMod.stdAddChar (n*t)*lpsQuadraticFourier N a n = lpsQuadraticFourier N a n := by
    unfold lpsQuadraticFourier
    rw [Finset.mul_sum]
    have h := Equiv.sum_comp (Equiv.addRight t) (fun r : ZMod N => ZMod.stdAddChar (a*r^2+n*r))
    rw [← h]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← AddChar.map_add_eq_mul]
    simp only [Equiv.coe_addRight]
    congr 1
    linear_combination -r*hlinear-hquadratic
  by_contra hnzero
  exact he ((mul_eq_right₀ hnzero).mp hshift)

/-- The residue equivalence agrees with the actual natural cast. -/
lemma lpsFin_cast_finEquiv (N : ℕ) [NeZero N] (r : Fin N) :
    (r.val:ZMod N) = ZMod.finEquiv N r := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => exact ZMod.natCast_zmod_val (n:=N+1) r

/-- The existing analytic residue phase is the standard cyclic additive character. -/
lemma lpsQuadraticPhase_stdAddChar (N : ℕ) [NeZero N] (a : ℤ) (r : Fin N) :
    lpsQuadraticPhase a N r = ZMod.stdAddChar ((a:ZMod N)*(ZMod.finEquiv N r)^2) := by
  rw [← lpsFin_cast_finEquiv]
  have he : (a:ZMod N)*(r.val:ZMod N)^2 = ((a*(r.val:ℤ)^2:ℤ):ZMod N) := by push_cast;rfl
  rw [he,ZMod.stdAddChar_coe]
  unfold lpsQuadraticPhase
  push_cast
  congr 1
  ring

/-- Zero frequency is the existing actual Fin-indexed Gauss sum. -/
lemma lpsQuadraticFourier_zero_eq_Gauss (N : ℕ) [NeZero N] (a : ℤ) :
    lpsQuadraticFourier N (a:ZMod N) 0 = lpsUnaryQuadraticGauss a N := by
  unfold lpsQuadraticFourier lpsUnaryQuadraticGauss
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
  intro r
  simp only [zero_mul,add_zero]
  exact lpsQuadraticPhase_stdAddChar N a r

/-- Combine the quadratic residue phase and the genuine Jacobi linear phase. -/
lemma lpsThetaGaussSum_term (a n : ℤ) (N : ℕ) [NeZero N] (r : Fin N) (z : ℂ) :
    lpsQuadraticPhase a N r * jacobiTheta₂_term n ((r.val:ℂ)/(N:ℂ)) z =
      ZMod.stdAddChar ((a:ZMod N)*(ZMod.finEquiv N r)^2+(n:ZMod N)*(ZMod.finEquiv N r)) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z) := by
  rw [← lpsFin_cast_finEquiv]
  have he : (a:ZMod N)*(r.val:ZMod N)^2+(n:ZMod N)*(r.val:ZMod N) =
      ((a*(r.val:ℤ)^2+n*(r.val:ℤ):ℤ):ZMod N) := by push_cast;rfl
  rw [he,ZMod.stdAddChar_coe]
  unfold lpsQuadraticPhase jacobiTheta₂_term
  rw [← Complex.exp_add,← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- Absolute summability permits the actual finite/infinite Fourier interchange. -/
lemma lpsThetaGaussSum_eq_quadraticFourier (a : ℤ) (N : ℕ) [NeZero N] (z : ℂ) (hz : 0 < z.im) :
    lpsThetaGaussSum a N z =
      ∑' n : ℤ, lpsQuadraticFourier N (a:ZMod N) (n:ZMod N) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*z) := by
  have hs (r : Fin N) : Summable (fun n : ℤ =>
      lpsQuadraticPhase a N r * jacobiTheta₂_term n ((r.val:ℂ)/(N:ℂ)) z) :=
    (hasSum_jacobiTheta₂_term ((r.val:ℂ)/(N:ℂ)) hz).summable.mul_left _
  unfold lpsThetaGaussSum jacobiTheta₂
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r (_ : r ∈ Finset.univ) => hs r)]
  apply tsum_congr
  intro n
  rw [lpsQuadraticFourier,Finset.sum_mul]
  apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
  intro r
  exact lpsThetaGaussSum_term a n N r z

/-- An explicit cyclic translation leaves support only on multiples of 2*s. -/
lemma lpsQuadraticFourier_even_support (N s k : ℕ) [NeZero N] (hN : N=4*s*k)
    (hk : 0 < k) (a n : ℤ) (hn : ¬ (2*(s:ℤ)) ∣ n) :
    lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) = 0 := by
  let t : ZMod N := (2*k:ℕ)
  have hc : (4:ZMod N)*(s:ZMod N)*(k:ZMod N)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (show ((4*s*k:ℕ):ZMod N)=0 by rw [← hN];exact ZMod.natCast_self N)
  have hl : 2*(((s:ℤ)*a:ℤ):ZMod N)*t=0 := by
    dsimp [t]
    push_cast
    calc
      _ = (a:ZMod N)*((4:ZMod N)*(s:ZMod N)*(k:ZMod N)) := by ring
      _ = 0 := by rw [hc,mul_zero]
  have hq : (((s:ℤ)*a:ℤ):ZMod N)*t^2=0 := by
    dsimp [t]
    push_cast
    calc
      _ = (a:ZMod N)*(k:ZMod N)*((4:ZMod N)*(s:ZMod N)*(k:ZMod N)) := by ring
      _ = 0 := by rw [hc,mul_zero]
  apply lpsQuadraticFourier_zero_of_translation N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) t hl hq
  intro he
  have ht : ((n*(2*(k:ℤ)):ℤ):ZMod N)=0 := by
    simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat,t] using he
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ht
  have hcI : (N:ℤ)=(2*(k:ℤ))*(2*(s:ℤ)) := by rw [hN];push_cast;ring
  rw [hcI,mul_comm n (2*(k:ℤ))] at hd
  have hkn : 2*(k:ℤ)≠0 := by positivity
  exact hn ((mul_dvd_mul_iff_left hkn).mp hd)

/-- Determinant one determines the remaining quadratic coefficient phase. -/
lemma lpsQuadraticFourier_det_even (N s : ℕ) [NeZero N] (a b d j : ℤ)
    (hdet : a*d-b*(N:ℤ)=1) :
    lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) ((2*(s:ℤ)*j:ℤ):ZMod N) =
      ZMod.stdAddChar (((-(s:ℤ)*d*j^2:ℤ):ZMod N))*lpsUnaryQuadraticGauss ((s:ℤ)*a) N := by
  have had : (a:ZMod N)*(d:ZMod N)=1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    simpa using h
  have hn : ((2*(s:ℤ)*j:ℤ):ZMod N)=
      2*(((s:ℤ)*a:ℤ):ZMod N)*((d*j:ℤ):ZMod N) := by
    push_cast
    calc
      _ = 2*(s:ZMod N)*((a:ZMod N)*(d:ZMod N))*(j:ZMod N) := by rw [had];ring
      _ = _ := by ring
  change lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) ((2*(s:ℤ)*j:ℤ):ZMod N) = _
  rw [hn,lpsQuadraticFourier_completeSquare,lpsQuadraticFourier_zero_eq_Gauss]
  congr 2
  push_cast
  linear_combination -(s:ZMod N)*(d:ZMod N)*(j:ZMod N)^2*had

/-- Reindex the actual supported series and cancel the exact determinant phase. -/
lemma lpsThetaGaussSum_scalar (N s k : ℕ) [NeZero N] (hs : 0 < s) (hk : 0 < k)
    (hN : N=4*s*k) (a b d : ℤ) (hdet : a*d-b*(N:ℤ)=1)
    (z : ℂ) (hz : 0 < z.im) :
    lpsThetaGaussSum ((s:ℤ)*a) N ((z+(d:ℂ)/(N:ℂ))/(2*(s:ℂ))) =
      lpsUnaryQuadraticGauss ((s:ℤ)*a) N * jacobiTheta (2*(s:ℂ)*z) := by
  let w : ℂ := (z+(d:ℂ)/(N:ℂ))/(2*(s:ℂ))
  have hw : 0 < w.im := by
    dsimp [w]
    rw [show 2*(s:ℂ)=((2*(s:ℝ):ℝ):ℂ) by push_cast;rfl,Complex.div_ofReal_im]
    simp only [Complex.add_im,Complex.div_im,Complex.intCast_im,Complex.natCast_im,
      mul_zero,zero_mul,sub_self,zero_div,add_zero]
    exact div_pos hz (by positivity)
  rw [lpsThetaGaussSum_eq_quadraticFourier _ _ _ hw]
  let f : ℤ → ℂ := fun n => lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) (n:ZMod N) *
    Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*w)
  have hi : Function.Injective (fun j : ℤ => 2*(s:ℤ)*j) := by
    intro i j he
    exact mul_left_cancel₀ (by positivity : 2*(s:ℤ)≠0) he
  have hsupport : Function.support f ⊆ Set.range (fun j : ℤ => 2*(s:ℤ)*j) := by
    intro n hn
    by_contra hnr
    have hnd : ¬(2*(s:ℤ)) ∣ n := by
      rintro ⟨j,hj⟩
      exact hnr ⟨j,hj.symm⟩
    have he := lpsQuadraticFourier_even_support N s k hN hk a n hnd
    apply hn
    dsimp [f]
    rw [he,zero_mul]
  have hr := hi.tsum_eq (f:=f) hsupport
  change (∑' n : ℤ, f n)=_
  rw [← hr,jacobiTheta,← tsum_mul_left]
  apply tsum_congr
  intro j
  dsimp only [f]
  rw [lpsQuadraticFourier_det_even N s a b d j hdet,ZMod.stdAddChar_coe]
  have he :
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*((-(s:ℤ)*d*j^2:ℤ):ℂ)/(N:ℂ)) *
        Complex.exp ((Real.pi:ℂ)*Complex.I*((2*(s:ℤ)*j:ℤ):ℂ)^2*w) =
      Complex.exp ((Real.pi:ℂ)*Complex.I*(j:ℂ)^2*(2*(s:ℂ)*z)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [w]
    push_cast
    have sn : (s:ℂ)≠0 := by exact_mod_cast ne_of_gt hs
    have cn : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
    field_simp [sn,cn]
    ring
  rw [mul_comm (Complex.exp _) (lpsUnaryQuadraticGauss _ _),mul_assoc,he]

end QEC.Coding.TannerLiftedProduct
