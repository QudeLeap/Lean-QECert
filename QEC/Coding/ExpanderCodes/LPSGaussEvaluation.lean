import QEC.Coding.ExpanderCodes.LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Actual quadratic Gauss fourth powers

Square-root fibers identify finite-field quadratic sums with Mathlib character
Gauss sums. Explicit four/eight phase values and constructed mask reductions
prove every prime-power case. A genuine CRT reindexing then proves the complete
unit fourth-power classification: N squared for odd N, minus four times N squared
for four-divisible N, and zero for twice-odd N, including the finite-sum zero and
one moduli. These are evaluations of the existing finite sums, with no assumed
Gauss value, transformation law or target coefficient.

The exact four-divisible formula normalizes the LPS theta multiplier in
LPSThetaModularForm. The cyclic ring is a frequency ring and does not restrict
the quantum-code alphabet. Strong Fourier growth and the PK22 main theorem
remain separate proof obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex

/-- Actual square-root fibers identify the quadratic additive sum with the character Gauss sum. -/
lemma lpsFiniteField_square_sum_eq_gauss (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x^2)) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  have hc (y : F) :
      ((Finset.univ.filter (fun x : F => x^2=y)).card:ℂ) =
        ((quadraticChar F y:ℤ):ℂ)+1 := by
    have h := quadraticChar_card_sqrts hF y
    simp only [Set.toFinset_ofPred] at h
    exact_mod_cast h
  rw [← Finset.sum_fiberwise' Finset.univ (fun x : F => x^2) ψ]
  simp only [Finset.sum_const,nsmul_eq_mul,hc,add_mul,one_mul]
  rw [Finset.sum_add_distrib]
  have hn : ψ≠1 := by simpa only [AddChar.mulShift_one] using hψ (one_ne_zero : (1:F)≠0)
  rw [AddChar.sum_eq_zero_of_ne_one hn,add_zero]
  rfl

/-- The genuine finite-field quadratic sum has fourth power equal to the squared field cardinality. -/
lemma lpsFiniteField_square_sum_fourth (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x^2))^4 = (Fintype.card F:ℂ)^2 := by
  classical
  let χ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hχn : χ≠1 :=
    (MulChar.ringHomComp_ne_one_iff (by exact Int.cast_injective)).mpr (quadraticChar_ne_one hF)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic F).comp _
  have hχsq : χ (-1)^2=(1:ℂ) := by
    have h := congrArg (fun f : MulChar F ℂ => f (-1)) hχq.sq_eq_one
    simpa only [MulChar.pow_apply' χ (show (2:ℕ)≠0 by decide),
      MulChar.one_apply (show IsUnit (-1:F) by simp)] using h
  rw [lpsFiniteField_square_sum_eq_gauss F hF ψ hψ,
    show (4:ℕ)=2*2 by decide,pow_mul,gaussSum_sq hχn hχq hψ,mul_pow,hχsq,one_mul]

/-- The existing cyclic quadratic sum has fourth power p squared at an odd prime. -/
lemma lpsUnaryQuadraticGauss_prime_fourth (p : ℕ) [Fact p.Prime]
    (hp2 : p≠2) (a : ℤ) (ha : (a:ZMod p)≠0) :
    lpsUnaryQuadraticGauss a p^4 = (p:ℂ)^2 := by
  let ψ := (ZMod.stdAddChar (N:=p)).mulShift (a:ZMod p)
  have hψn : ψ≠1 := ZMod.isPrimitive_stdAddChar p ha
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψn
  have hF : ringChar (ZMod p)≠2 := by rw [ZMod.ringChar_zmod_n];exact hp2
  have h := lpsFiniteField_square_sum_fourth (ZMod p) hF ψ hψ
  rw [ZMod.card] at h
  have hg : lpsUnaryQuadraticGauss a p=(∑ x : ZMod p, ψ (x^2)) := by
    rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
    simp only [zero_mul,add_zero,ψ,AddChar.mulShift_apply]
  rw [hg]
  exact h

/-- The actual linear CRT parametrization is bijective by unit cancellation and cardinality. -/
lemma lpsCRT_linear_bijective (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    Function.Bijective (fun r : Fin m × Fin n =>
      ((n*r.1.val+m*r.2.val:ℕ):ZMod (m*n))) := by
  classical
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro r s he
    have hm := congrArg (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)) he
    have hn := congrArg (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n)) he
    simp only [map_add,map_mul,map_natCast,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,
      zero_mul,add_zero,zero_add] at hm hn
    have h1 := ((ZMod.isUnit_iff_coprime n m).mpr h.symm).mul_left_cancel hm
    have h2 := ((ZMod.isUnit_iff_coprime m n).mpr h).mul_left_cancel hn
    apply Prod.ext
    · apply (ZMod.finEquiv m).injective
      simpa only [lpsFin_cast_finEquiv] using h1
    · apply (ZMod.finEquiv n).injective
      simpa only [lpsFin_cast_finEquiv] using h2
  · simp [ZMod.card]

/-- Actual character inflation splits the two CRT linear contributions. -/
lemma lpsChar_product_split (m n : ℕ) [NeZero m] [NeZero n] (x y : ℤ) :
    ZMod.stdAddChar (((n:ℤ)*x+(m:ℤ)*y:ℤ):ZMod (m*n)) =
      ZMod.stdAddChar (x:ZMod m)*ZMod.stdAddChar (y:ZMod n) := by
  rw [Int.cast_add,AddChar.map_add_eq_mul]
  rw [lpsChar_inflate_modulus (m*n) m n rfl,
    lpsChar_inflate_modulus (m*n) n m (Nat.mul_comm _ _)]

/-- The CRT quadratic cross term has zero character phase. -/
lemma lpsQuadraticChar_product_split (m n : ℕ) [NeZero m] [NeZero n]
    (a x y : ℤ) :
    ZMod.stdAddChar (((a*((n:ℤ)*x+(m:ℤ)*y)^2):ℤ):ZMod (m*n)) =
      ZMod.stdAddChar (((a*(n:ℤ)*x^2):ℤ):ZMod m)*
      ZMod.stdAddChar (((a*(m:ℤ)*y^2):ℤ):ZMod n) := by
  have hz : ((m*n:ℕ):ZMod (m*n))=0 := ZMod.natCast_self _
  have he : (((a*((n:ℤ)*x+(m:ℤ)*y)^2):ℤ):ZMod (m*n)) =
      (((n:ℤ)*(a*(n:ℤ)*x^2)+(m:ℤ)*(a*(m:ℤ)*y^2):ℤ):ZMod (m*n)) := by
    push_cast at hz ⊢
    linear_combination (2:ZMod (m*n))*(a:ZMod (m*n))*(x:ZMod (m*n))*(y:ZMod (m*n))*hz
  rw [he,lpsChar_product_split]

/-- Constructed CRT reindexing factors the genuine sum at coprime moduli. -/
lemma lpsUnaryQuadraticGauss_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ℤ) :
    lpsUnaryQuadraticGauss a (m*n) =
      lpsUnaryQuadraticGauss (a*(n:ℤ)) m * lpsUnaryQuadraticGauss (a*(m:ℤ)) n := by
  classical
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
  simp only [zero_mul,add_zero]
  let f := fun r : Fin m × Fin n => ((n*r.1.val+m*r.2.val:ℕ):ZMod (m*n))
  let g := fun r : ZMod (m*n) => ZMod.stdAddChar ((a:ZMod (m*n))*r^2)
  have hs := Fintype.sum_bijective f (lpsCRT_linear_bijective m n h)
    (fun r => g (f r)) g (fun _ => rfl)
  change (∑ r : ZMod (m*n), g r)=_
  rw [← hs]
  dsimp only [f,g]
  rw [Fintype.sum_prod_type]
  unfold lpsUnaryQuadraticGauss
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  simp_rw [lpsQuadraticPhase_stdAddChar,← lpsFin_cast_finEquiv]
  have he := lpsQuadraticChar_product_split m n a x.val y.val
  convert he using 1 <;> push_cast <;> rfl

/-- The actual modulus-four half-turn character is minus one. -/
lemma lpsChar_four_two : ZMod.stdAddChar (2:ZMod 4)= -1 := by
  have h := ZMod.stdAddChar_coe (N:=4) (2:ℤ)
  norm_num only [Int.cast_ofNat,Nat.cast_ofNat] at h
  rw [show (2:ℂ)*Real.pi*Complex.I*2/4=(Real.pi:ℂ)*Complex.I by ring] at h
  exact h.trans Complex.exp_pi_mul_I

/-- The actual modulus-eight half-turn character is minus one. -/
lemma lpsChar_eight_four : ZMod.stdAddChar (4:ZMod 8)= -1 := by
  have h := ZMod.stdAddChar_coe (N:=8) (4:ℤ)
  norm_num only [Int.cast_ofNat,Nat.cast_ofNat] at h
  rw [show (2:ℂ)*Real.pi*Complex.I*4/8=(Real.pi:ℂ)*Complex.I by ring] at h
  exact h.trans Complex.exp_pi_mul_I

/-- An odd input gives the modulus-four character square minus one. -/
lemma lpsChar_four_odd_square (a : ℤ) (ha : Odd a) :
    ZMod.stdAddChar (a:ZMod 4)^2= -1 := by
  rw [pow_two,← AddChar.map_add_eq_mul]
  have he : (a:ZMod 4)+(a:ZMod 4)=2 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (4:ZMod 4)=0 := by decide
    linear_combination (k:ZMod 4)*hz
  rw [he,lpsChar_four_two]

/-- An odd input gives the modulus-eight character fourth power minus one. -/
lemma lpsChar_eight_odd_fourth (a : ℤ) (ha : Odd a) :
    ZMod.stdAddChar (a:ZMod 8)^4= -1 := by
  have he : (4:ZMod 8)*(a:ZMod 8)=4 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (8:ZMod 8)=0 := by decide
    linear_combination (k:ZMod 8)*hz
  have h := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=8)) 4 (a:ZMod 8)
  rw [nsmul_eq_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [he,lpsChar_eight_four] at h
  exact h.symm

/-- The four actual terms give the modulus-four quadratic sum. -/
lemma lpsUnaryQuadraticGauss_four (a : ℤ) :
    lpsUnaryQuadraticGauss a 4=2+2*ZMod.stdAddChar (a:ZMod 4) := by
  unfold lpsUnaryQuadraticGauss
  simp_rw [lpsQuadraticPhase_stdAddChar]
  rw [Fin.sum_univ_four]
  have hv (r : Fin 4) : ZMod.finEquiv 4 r=(r.val:ZMod 4) := (lpsFin_cast_finEquiv 4 r).symm
  simp only [hv]
  rw [show ((0:Fin 4).val:ZMod 4)^2=0 by decide,
    show ((1:Fin 4).val:ZMod 4)^2=1 by decide,
    show ((2:Fin 4).val:ZMod 4)^2=0 by decide,
    show ((3:Fin 4).val:ZMod 4)^2=1 by decide]
  simp only [mul_zero,mul_one,AddChar.map_zero_eq_one]
  ring

/-- The actual modulus-four sum has fourth power minus four times the modulus squared. -/
lemma lpsUnaryQuadraticGauss_four_fourth (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 4^4= -4*(4:ℂ)^2 := by
  rw [lpsUnaryQuadraticGauss_four]
  have h := lpsChar_four_odd_square a ha
  linear_combination (16*ZMod.stdAddChar (a:ZMod 4)^2+64*ZMod.stdAddChar (a:ZMod 4)+80)*h

/-- The eight actual terms give the modulus-eight quadratic sum at an odd coefficient. -/
lemma lpsUnaryQuadraticGauss_eight (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 8=4*ZMod.stdAddChar (a:ZMod 8) := by
  unfold lpsUnaryQuadraticGauss
  simp_rw [lpsQuadraticPhase_stdAddChar]
  rw [Fin.sum_univ_eight]
  have hv (r : Fin 8) : ZMod.finEquiv 8 r=(r.val:ZMod 8) := (lpsFin_cast_finEquiv 8 r).symm
  simp only [hv]
  rw [show ((0:Fin 8).val:ZMod 8)^2=0 by decide,
    show ((1:Fin 8).val:ZMod 8)^2=1 by decide,
    show ((2:Fin 8).val:ZMod 8)^2=4 by decide,
    show ((3:Fin 8).val:ZMod 8)^2=1 by decide,
    show ((4:Fin 8).val:ZMod 8)^2=0 by decide,
    show ((5:Fin 8).val:ZMod 8)^2=1 by decide,
    show ((6:Fin 8).val:ZMod 8)^2=4 by decide,
    show ((7:Fin 8).val:ZMod 8)^2=1 by decide]
  have he : (a:ZMod 8)*4=4 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (8:ZMod 8)=0 := by decide
    linear_combination (k:ZMod 8)*hz
  simp only [mul_zero,mul_one,AddChar.map_zero_eq_one,he,lpsChar_eight_four]
  ring

/-- The actual modulus-eight sum has fourth power minus four times the modulus squared. -/
lemma lpsUnaryQuadraticGauss_eight_fourth (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 8^4= -4*(8:ℂ)^2 := by
  rw [lpsUnaryQuadraticGauss_eight a ha,mul_pow,lpsChar_eight_odd_fourth a ha]
  norm_num

/-- Two actual units complete the odd mask frequency with zero quadratic phase. -/
lemma lpsQuadraticFourier_odd_mask_frequency (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (a : ℤ) (ha : IsUnit (a:ZMod N))
    (h2 : IsUnit (2:ZMod N)) (j : ℤ) :
    lpsQuadraticFourier N (a:ZMod N) (((d:ℤ)*(k:ℤ)*j:ℤ):ZMod N) =
      lpsUnaryQuadraticGauss a N := by
  let u : ZMod N := ↑(ha.unit⁻¹)
  let v : ZMod N := ↑(h2.unit⁻¹)
  have had : (a:ZMod N)*u=1 := by
    have h : (ha.unit:ZMod N)*↑(ha.unit⁻¹)=1 := by simp
    simpa only [ha.unit_spec,u] using h
  have hv : (2:ZMod N)*v=1 := by
    have h : (h2.unit:ZMod N)*↑(h2.unit⁻¹)=1 := by simp
    simpa only [h2.unit_spec,v] using h
  let t : ZMod N := (d:ZMod N)*(k:ZMod N)*u*v*(j:ZMod N)
  have hn : (((d:ℤ)*(k:ℤ)*j:ℤ):ZMod N)=2*(a:ZMod N)*t := by
    dsimp [t]
    push_cast
    calc
      _ = ((2:ZMod N)*v)*((a:ZMod N)*u)*(d:ZMod N)*(k:ZMod N)*(j:ZMod N) := by
        rw [hv,had];ring
      _ = _ := by ring
  have hphase : -(a:ZMod N)*t^2=0 := by
    dsimp [t]
    calc
      _ = (-(a:ZMod N)*(k:ZMod N)*u^2*v^2*(j:ZMod N)^2)*(N:ZMod N) := by
        have hncast := congrArg (fun x : ℕ => (x:ZMod N)) hN
        push_cast at hncast
        rw [hncast]
        ring
      _ = 0 := by rw [ZMod.natCast_self,mul_zero]
  rw [hn,lpsQuadraticFourier_completeSquare,hphase,AddChar.map_zero_eq_one,one_mul,
    lpsQuadraticFourier_zero_eq_Gauss]

/-- The proved mask projection with an explicitly identified modulus. -/
lemma lpsQuadraticGauss_mask_sum_modulus (N d m : ℕ) [NeZero N] [NeZero d] [NeZero m]
    (hN : N=d*m) (a : ℤ) :
    (∑ j : Fin d, lpsQuadraticFourier N (a:ZMod N) (((m:ℤ)*j.val:ℤ):ZMod N)) =
      lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N := by
  subst N
  exact lpsQuadraticGauss_mask_sum d m a

/-- Odd square scaling follows from actual mask projection and unit completion. -/
lemma lpsUnaryQuadraticGauss_odd_square_scale (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (hd : 0 < d) (hk : 0 < k) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) (h2 : IsUnit (2:ZMod N)) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N=(d:ℂ)*lpsUnaryQuadraticGauss a N := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero k := ⟨ne_of_gt hk⟩
  have hNm : N=d*(d*k) := by rw [hN];ring
  have hmask := lpsQuadraticGauss_mask_sum_modulus N d (d*k) hNm a
  have hf (j : Fin d) :
      lpsQuadraticFourier N (a:ZMod N) ((((d*k:ℕ):ℤ)*j.val:ℤ):ZMod N) =
        lpsUnaryQuadraticGauss a N := by
    have h := lpsQuadraticFourier_odd_mask_frequency N d k hN a ha h2 j.val
    simpa only [Nat.cast_mul] using h
  simp_rw [hf] at hmask
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hmask.symm

/-- Odd square scaling and inflation remove a square factor from the actual modulus. -/
lemma lpsUnaryQuadraticGauss_odd_square_modulus (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (hd : 0 < d) (hk : 0 < k) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) (h2 : IsUnit (2:ZMod N)) :
    lpsUnaryQuadraticGauss a N=(d:ℂ)*lpsUnaryQuadraticGauss a k := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero k := ⟨ne_of_gt hk⟩
  have hi := lpsUnaryQuadraticGauss_inflate (d^2) k a
  rw [← hN] at hi
  norm_num only [Nat.cast_pow] at hi
  rw [lpsUnaryQuadraticGauss_odd_square_scale N d k hN hd hk a ha h2] at hi
  have hdC : (d:ℂ)≠0 := by exact_mod_cast ne_of_gt hd
  apply mul_left_cancel₀ hdC
  calc
    _ = (d:ℂ)^2*lpsUnaryQuadraticGauss a k := hi
    _ = _ := by ring

/-- A genuine unit maps to a unit at a dividing positive modulus. -/
lemma lpsZMod_unit_descend (N m : ℕ) [NeZero N] [NeZero m]
    (hm : m ∣ N) (a : ℤ) (ha : IsUnit (a:ZMod N)) : IsUnit (a:ZMod m) := by
  have h := ha.map (ZMod.castHom hm (ZMod m))
  simpa only [map_intCast] using h

/-- An actual modular unit yields an integer determinant-one equation. -/
lemma lpsZMod_unit_bezout (N : ℕ) [NeZero N] (a : ℤ) (ha : IsUnit (a:ZMod N)) :
    ∃ b u : ℤ, a*u-b*(N:ℤ)=1 := by
  obtain ⟨u,hu⟩ := ZMod.intCast_surjective (↑(ha.unit⁻¹):ZMod N)
  have had : (a:ZMod N)*(u:ZMod N)=1 := by
    have h : (ha.unit:ZMod N)*↑(ha.unit⁻¹)=1 := by simp
    simpa only [ha.unit_spec,← hu] using h
  have hz : ((a*u-1:ℤ):ZMod N)=0 := by
    push_cast
    rw [had]
    ring
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  refine ⟨b,u,?_⟩
  linear_combination hb

/-- A unit at an even positive modulus has an odd integer coefficient. -/
lemma lpsZMod_unit_odd_of_even_modulus (N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (a : ℤ) (ha : IsUnit (a:ZMod N)) : Odd a := by
  have hu := lpsZMod_unit_descend N 2 hN a ha
  apply Int.not_even_iff_odd.mp
  rintro ⟨k,hk⟩
  have hz : (a:ZMod 2)=0 := by
    rw [hk]
    push_cast
    rw [← two_mul,show (2:ZMod 2)=0 by decide,zero_mul]
  exact hu.ne_zero hz

/-- The two actual terms cancel for an odd coefficient. -/
lemma lpsUnaryQuadraticGauss_odd_two (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 2=0 := by
  unfold lpsUnaryQuadraticGauss
  simp_rw [lpsQuadraticPhase_stdAddChar]
  rw [Fin.sum_univ_two]
  have he : (a:ZMod 2)=1 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (2:ZMod 2)=0 := by decide
    linear_combination (k:ZMod 2)*hz
  have hchar : ZMod.stdAddChar (1:ZMod 2)= -1 := by
    have h := ZMod.stdAddChar_coe (N:=2) (1:ℤ)
    norm_num only [Int.cast_one,Nat.cast_ofNat,mul_one] at h
    rw [show (2:ℂ)*Real.pi*Complex.I/2=(Real.pi:ℂ)*Complex.I by ring] at h
    exact h.trans Complex.exp_pi_mul_I
  have hv (r : Fin 2) : ZMod.finEquiv 2 r=(r.val:ZMod 2) := (lpsFin_cast_finEquiv 2 r).symm
  simp only [hv]
  rw [show ((0:Fin 2).val:ZMod 2)^2=0 by decide,
    show ((1:Fin 2).val:ZMod 2)^2=1 by decide]
  simp only [mul_zero,mul_one,he,AddChar.map_zero_eq_one,hchar,add_neg_cancel]

/-- Odd square reduction proves the fourth-power value at every odd prime power. -/
lemma lpsUnaryQuadraticGauss_odd_prime_pow_fourth (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (p^e))) :
    lpsUnaryQuadraticGauss a (p^e)^4=((p^e:ℕ):ℂ)^2 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  induction e using Nat.twoStepInduction generalizing a with
  | zero => simp only [pow_zero,lpsUnaryQuadraticGauss_one,Nat.cast_one,one_pow]
  | one =>
    have ha' : IsUnit (a:ZMod p) :=
      Eq.mp (congrArg (fun N : ℕ => IsUnit (a:ZMod N)) (pow_one p)) ha
    simpa only [pow_one] using lpsUnaryQuadraticGauss_prime_fourth p hp2 a ha'.ne_zero
  | more e ih0 ih1 =>
    have hN : p^(e+2)=p^2*p^e := by rw [pow_add];ring
    have hodd : Odd (p^(e+2)) := (hp.odd_of_ne_two hp2).pow
    have h2 : IsUnit (2:ZMod (p^(e+2))) :=
      (ZMod.isUnit_iff_coprime 2 _).mpr hodd.coprime_two_left
    have hs := lpsUnaryQuadraticGauss_odd_square_modulus (p^(e+2)) p (p^e) hN
      hp.pos (pow_pos hp.pos e) a ha h2
    have hu := lpsZMod_unit_descend (p^(e+2)) (p^e)
      (by rw [hN];exact dvd_mul_left _ _) a ha
    rw [hs,mul_pow,ih0 a hu]
    norm_num only [Nat.cast_pow]
    rw [pow_add]
    ring

/-- The actual four/eight bases and square reduction prove every higher two-power value. -/
lemma lpsUnaryQuadraticGauss_two_pow_fourth (e : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod (2^(e+2)))) :
    lpsUnaryQuadraticGauss a (2^(e+2))^4= -4*((2^(e+2):ℕ):ℂ)^2 := by
  induction e using Nat.twoStepInduction generalizing a with
  | zero =>
    have ho := lpsZMod_unit_odd_of_even_modulus 4 (by decide) a ha
    exact lpsUnaryQuadraticGauss_four_fourth a ho
  | one =>
    have ho := lpsZMod_unit_odd_of_even_modulus 8 (by decide) a ha
    exact lpsUnaryQuadraticGauss_eight_fourth a ho
  | more e ih0 ih1 =>
    have hN : 2^(e+2+2)=4*2^2*2^e := by rw [pow_add,pow_add];ring
    have hOld : 4*2^e=2^(e+2) := by rw [pow_add];ring
    obtain ⟨b,u,hdet⟩ := lpsZMod_unit_bezout (2^(e+2+2)) a ha
    rw [hN] at hdet
    have hs := lpsUnaryQuadraticGauss_square_modulus 2 (2^e) (by decide)
      (by positivity) a b u hdet
    rw [← hN,hOld] at hs
    have hd : 2^(e+2) ∣ 2^(e+2+2) := by
      conv_rhs => rw [pow_add]
      exact Nat.dvd_mul_right (2^(e+2)) (2^2)
    have hu := lpsZMod_unit_descend (2^(e+2+2)) (2^(e+2)) hd a ha
    rw [hs,mul_pow,ih0 a hu]
    norm_num only [Nat.cast_ofNat,Nat.cast_pow]
    rw [pow_add,pow_add]
    ring

/-- The residue class of the modulus determines the actual unit fourth-power factor. -/
def lpsGaussFourthFactor (N : ℕ) : ℤ :=
  if N%2=1 then 1 else if N%4=0 then -4 else 0

/-- The residue factor multiplies at coprime moduli because both cannot be even. -/
lemma lpsGaussFourthFactor_coprime_mul (m n : ℕ) (h : m.Coprime n) :
    lpsGaussFourthFactor (m*n)=lpsGaussFourthFactor m*lpsGaussFourthFactor n := by
  have hcommon : ¬(m%2=0 ∧ n%2=0) := by
    rintro ⟨hm,hn⟩
    have hd : 2 ∣ Nat.gcd m n := Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero hm) (Nat.dvd_of_mod_eq_zero hn)
    rw [h.gcd_eq_one] at hd
    norm_num at hd
  have hm2 : m%2=(m%4)%2 := (Nat.mod_mod_of_dvd m (show 2 ∣ 4 by decide)).symm
  have hn2 : n%2=(n%4)%2 := (Nat.mod_mod_of_dvd n (show 2 ∣ 4 by decide)).symm
  have hml : m%4 < 4 := Nat.mod_lt _ (by decide)
  have hnl : n%4 < 4 := Nat.mod_lt _ (by decide)
  unfold lpsGaussFourthFactor
  rw [Nat.mul_mod m n 2,Nat.mul_mod m n 4]
  simp only [hm2,hn2]
  rw [hm2,hn2] at hcommon
  generalize hm : m%4=x at hml hcommon ⊢
  generalize hn : n%4=y at hnl hcommon ⊢
  interval_cases x <;> interval_cases y <;> norm_num at hcommon
  all_goals norm_num

/-- Both prime-power evaluations agree with the residue factor, including exponents zero and one. -/
lemma lpsGaussFourthFactor_prime_pow (p e : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsUnit (a:ZMod (p^e))) :
    lpsUnaryQuadraticGauss a (p^e)^4=
      (lpsGaussFourthFactor (p^e):ℂ)*((p^e:ℕ):ℂ)^2 := by
  by_cases hp2 : p=2
  · subst p
    rcases e with _ | (_ | e)
    · simp [lpsGaussFourthFactor,lpsUnaryQuadraticGauss_one]
    · have ho := lpsZMod_unit_odd_of_even_modulus 2 (by decide) a ha
      simp [lpsGaussFourthFactor,lpsUnaryQuadraticGauss_odd_two a ho]
    · have hd4 : 4 ∣ 2^(e+2) := ⟨2^e,by rw [pow_add];ring⟩
      have hd2 : 2 ∣ 2^(e+2) := dvd_trans (show 2 ∣ 4 by decide) hd4
      simp only [lpsGaussFourthFactor,Nat.mod_eq_zero_of_dvd hd2,
        Nat.mod_eq_zero_of_dvd hd4,if_neg (by decide : ¬ (0:ℕ)=1),ite_true,
        Int.cast_neg,Int.cast_ofNat]
      exact lpsUnaryQuadraticGauss_two_pow_fourth e a ha
  · have ho : Odd (p^e) := (hp.odd_of_ne_two hp2).pow
    simp only [lpsGaussFourthFactor,Nat.odd_iff.mp ho,ite_true,Int.cast_one,one_mul]
    exact lpsUnaryQuadraticGauss_odd_prime_pow_fourth p hp hp2 e a ha

/-- Prime-power induction and actual CRT prove the complete fourth-power classification. -/
lemma lpsUnaryQuadraticGauss_fourth_classified (N : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) :
    lpsUnaryQuadraticGauss a N^4=(lpsGaussFourthFactor N:ℂ)*(N:ℂ)^2 := by
  induction N using Nat.recOnPrimeCoprime generalizing a with
  | zero => simp [lpsUnaryQuadraticGauss,lpsGaussFourthFactor]
  | prime_pow p e hp => exact lpsGaussFourthFactor_prime_pow p e hp a ha
  | coprime m n hm hn hcop ihm ihn =>
    let : NeZero m := ⟨by omega⟩
    let : NeZero n := ⟨by omega⟩
    have haM := lpsZMod_unit_descend (m*n) m (Nat.dvd_mul_right _ _) a ha
    have haN := lpsZMod_unit_descend (m*n) n (Nat.dvd_mul_left _ _) a ha
    have hum : IsUnit (((a*(n:ℤ):ℤ):ZMod m)) := by
      simpa only [Int.cast_mul,Int.cast_natCast] using
        haM.mul ((ZMod.isUnit_iff_coprime n m).mpr hcop.symm)
    have hun : IsUnit (((a*(m:ℤ):ℤ):ZMod n)) := by
      simpa only [Int.cast_mul,Int.cast_natCast] using
        haN.mul ((ZMod.isUnit_iff_coprime m n).mpr hcop)
    rw [lpsUnaryQuadraticGauss_coprime_mul m n hcop a,mul_pow,
      ihm (a*(n:ℤ)) hum,ihn (a*(m:ℤ)) hun,lpsGaussFourthFactor_coprime_mul m n hcop]
    push_cast
    ring

/-- A modulus divisible by four gives the exact unit fourth power minus four times N squared. -/
lemma lpsUnaryQuadraticGauss_fourth (N : ℕ) (hN : 4 ∣ N) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) :
    lpsUnaryQuadraticGauss a N^4= -4*(N:ℂ)^2 := by
  have h := lpsUnaryQuadraticGauss_fourth_classified N a ha
  have hd2 : 2 ∣ N := dvd_trans (show 2 ∣ 4 by decide) hN
  simpa only [lpsGaussFourthFactor,Nat.mod_eq_zero_of_dvd hd2,
    Nat.mod_eq_zero_of_dvd hN,if_neg (by decide : ¬ (0:ℕ)=1),ite_true,
    Int.cast_neg,Int.cast_ofNat] using h

end QEC.Coding.TannerLiftedProduct
