import QEC.Coding.ExpanderCodes.LPSThetaModularForm
import QEC.Coding.ExpanderCodes.LPSModularDilation

/-!
# Local factors of the actual standard theta cusp product

Unit-square reindexing, genuine Gauss CRT, prime-power recurrences and the
modulus-four phase compute the actual local Gauss factors. These internal
arithmetic results support the all-cusp theta Eisenstein comparison; they do
not assert its completion, a coefficient growth bound or the PK22 main theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- Multiplication by an actual unit reindexes the quadratic Gauss sum by its square. -/
lemma lpsUnaryQuadraticGauss_unit_square (N : ℕ) [NeZero N] (a d : ℤ)
    (hd : IsUnit (d:ZMod N)) :
    lpsUnaryQuadraticGauss (a*d^2) N=lpsUnaryQuadraticGauss a N := by
  rw [←lpsQuadraticFourier_zero_eq_Gauss,←lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier,lpsQuadraticFourier]
  simp only [zero_mul,add_zero]
  apply Fintype.sum_bijective (fun x : ZMod N => (hd.unit:ZMod N)*x)
    hd.unit.mulLeft_bijective
  intro x
  rw [hd.unit_spec]
  congr 1
  push_cast
  ring

/-- The finite-field quadratic Gauss sum is the actual quadratic character times the standard Gauss sum. -/
lemma lpsUnaryQuadraticGauss_prime_eq_character (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : ℤ) (ha : (a:ZMod q)≠0) :
    lpsUnaryQuadraticGauss a q=lpsQuadraticE2Character q (a:ZMod q)*
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
  let ψ := (ZMod.stdAddChar (N:=q)).mulShift (a:ZMod q)
  have hψn : ψ≠1 := ZMod.isPrimitive_stdAddChar q ha
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψn
  have hF : ringChar (ZMod q)≠2 := by rw [ZMod.ringChar_zmod_n];exact hq2
  have h := lpsFiniteField_square_sum_eq_gauss (ZMod q) hF ψ hψ
  have hg : lpsUnaryQuadraticGauss a q=(∑ x : ZMod q,ψ (x^2)) := by
    rw [←lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
    simp only [zero_mul,add_zero,ψ,AddChar.mulShift_apply]
  rw [hg,h]
  change gaussSum (lpsQuadraticE2Character q) ((ZMod.stdAddChar (N:=q)).mulShift (a:ZMod q))=_
  have hu : IsUnit (a:ZMod q) := isUnit_iff_ne_zero.mpr ha
  have hs := gaussSum_mulShift_eq (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) hu.unit
  have hchi : (lpsQuadraticE2Character q).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)
  rw [hchi.inv] at hs
  simpa only [hu.unit_spec] using hs

/-- A residue prime congruent to one modulo four has quadratic character one at minus one. -/
lemma lpsQuadraticE2Character_neg_one (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsQuadraticE2Character q (-1:ZMod q)=1 := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hF : ringChar (ZMod q)≠2 := by rw [ZMod.ringChar_zmod_n];exact hq2
  have h := quadraticChar_neg_one (F:=ZMod q) hF
  rw [ZMod.card,ZMod.χ₄_nat_one_mod_four hq4] at h
  simp [lpsQuadraticE2Character,MulChar.ringHomComp_apply,h]

/-- The genuine standard quadratic Gauss sum has square equal to the residue prime. -/
lemma lpsQuadraticE2Gauss_sq (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))^2=(q:ℂ) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have h := gaussSum_sq (lpsQuadraticE2Character_ne_one q hq2)
    ((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)) (ZMod.isPrimitive_stdAddChar q)
  rw [ZMod.card,lpsQuadraticE2Character_neg_one q hq4,one_mul] at h
  exact h

/-- The actual product of the four unary Gauss factors in the standard theta cusp constant. -/
noncomputable def lpsThetaCuspGaussProduct (q : ℕ) (a : ℤ) (N : ℕ) : ℂ :=
  lpsUnaryQuadraticGauss a N*lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) N^3

/-- The genuine Gauss CRT formula factors the four-variable cusp product at coprime moduli. -/
lemma lpsThetaCuspGaussProduct_coprime_mul (q m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ℤ) :
    lpsThetaCuspGaussProduct q a (m*n)=
      lpsThetaCuspGaussProduct q (a*(n:ℤ)) m *
        lpsThetaCuspGaussProduct q (a*(m:ℤ)) n := by
  simp only [lpsThetaCuspGaussProduct,lpsUnaryQuadraticGauss_coprime_mul m n h]
  rw [show 4*(q:ℤ)^2*a*(n:ℤ)=4*(q:ℤ)^2*(a*(n:ℤ)) by ring,
    show 4*(q:ℤ)^2*a*(m:ℤ)=4*(q:ℤ)^2*(a*(m:ℤ)) by ring]
  ring

/-- An odd cofactor coprime to twice the residue prime contributes its modulus squared. -/
lemma lpsThetaCuspGaussProduct_odd_unit (q N : ℕ) [NeZero N] (hN : Odd N)
    (a : ℤ) (ha : IsUnit (a:ZMod N)) (hq : IsUnit ((2*q:ℕ):ZMod N)) :
    lpsThetaCuspGaussProduct q a N=(N:ℂ)^2 := by
  have he : 4*(q:ℤ)^2*a=a*((2*q:ℕ):ℤ)^2 := by push_cast;ring
  rw [lpsThetaCuspGaussProduct,he,lpsUnaryQuadraticGauss_unit_square N a ((2*q:ℕ):ℤ) (by exact_mod_cast hq)]
  rw [show lpsUnaryQuadraticGauss a N*lpsUnaryQuadraticGauss a N^3=lpsUnaryQuadraticGauss a N^4 by ring,
    lpsUnaryQuadraticGauss_fourth_classified N a ha]
  simp [lpsGaussFourthFactor,Nat.odd_iff.mp hN]

/-- The modulus-one boundary contributes one to the actual theta Gauss product. -/
lemma lpsThetaCuspGaussProduct_one (q : ℕ) (a : ℤ) :
    lpsThetaCuspGaussProduct q a 1=1 := by
  simp [lpsThetaCuspGaussProduct,lpsUnaryQuadraticGauss_one]

/-- At the residue prime the actual theta Gauss product retains its quadratic character factor. -/
lemma lpsThetaCuspGaussProduct_prime (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : ℤ) (ha : (a:ZMod q)≠0) :
    lpsThetaCuspGaussProduct q a q=(q:ℂ)^3*lpsQuadraticE2Character q (a:ZMod q)*
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
  have hz : lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) q=(q:ℂ) := by
    have h := lpsUnaryQuadraticGauss_inflate q 1 (4*(q:ℤ)*a)
    have he : 4*(q:ℤ)*a*(q:ℤ)=4*(q:ℤ)^2*a := by ring
    simpa only [he,mul_one,lpsUnaryQuadraticGauss_one] using h
  rw [lpsThetaCuspGaussProduct,hz,lpsUnaryQuadraticGauss_prime_eq_character q hq2 a ha]
  ring

/-- At higher residue-prime powers the actual theta product is prime cubed times modulus squared. -/
lemma lpsThetaCuspGaussProduct_prime_pow_ge_two (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (q^(e+2)))) :
    lpsThetaCuspGaussProduct q a (q^(e+2))=(q:ℂ)^3*((q^(e+2):ℕ):ℂ)^2 := by
  have hodd : Odd (q^(e+2)) := ((Fact.out : q.Prime).odd_of_ne_two hq2).pow
  have h2 : IsUnit (2:ZMod (q^(e+2))) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr hodd.coprime_two_left
  have hN : q^(e+2)=q^2*q^e := by rw [pow_add];ring
  have hs := lpsUnaryQuadraticGauss_odd_square_scale (q^(e+2)) q (q^e) hN
    (Fact.out : q.Prime).pos (pow_pos (Fact.out : q.Prime).pos _) a ha h2
  have he : 4*(q:ℤ)^2*a=(a*(q:ℤ)^2)*(2:ℤ)^2 := by ring
  rw [lpsThetaCuspGaussProduct,he,lpsUnaryQuadraticGauss_unit_square _ (a*(q:ℤ)^2) 2 (by exact_mod_cast h2),hs]
  rw [show lpsUnaryQuadraticGauss a (q^(e+2))*((q:ℂ)*lpsUnaryQuadraticGauss a (q^(e+2)))^3=
      (q:ℂ)^3*lpsUnaryQuadraticGauss a (q^(e+2))^4 by ring]
  rw [lpsUnaryQuadraticGauss_odd_prime_pow_fourth q (Fact.out : q.Prime) hq2 (e+2) a ha]

/-- A unit first column at modulus two makes the actual theta Gauss product zero. -/
lemma lpsThetaCuspGaussProduct_two (q : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod 2)) :
    lpsThetaCuspGaussProduct q a 2=0 := by
  have ho := lpsZMod_unit_odd_of_even_modulus 2 (by decide) a ha
  rw [lpsThetaCuspGaussProduct,lpsUnaryQuadraticGauss_odd_two a ho,zero_mul]

/-- Inflation computes the three scaled Gauss factors at modulus four. -/
lemma lpsThetaCuspGaussProduct_four (q : ℕ) (a : ℤ) :
    lpsThetaCuspGaussProduct q a 4=64*lpsUnaryQuadraticGauss a 4 := by
  have hz : lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) 4=4 := by
    have h := lpsUnaryQuadraticGauss_inflate 4 1 ((q:ℤ)^2*a)
    have he : (q:ℤ)^2*a*(4:ℤ)=4*(q:ℤ)^2*a := by ring
    simpa only [he,mul_one,lpsUnaryQuadraticGauss_one,Nat.cast_ofNat] using h
  rw [lpsThetaCuspGaussProduct,hz]
  ring

/-- At modulus eight the scaled odd Gauss factor makes the actual theta product zero. -/
lemma lpsThetaCuspGaussProduct_eight (q : ℕ) (hq : Odd q) (a : ℤ)
    (ha : IsUnit (a:ZMod 8)) : lpsThetaCuspGaussProduct q a 8=0 := by
  have ho := lpsZMod_unit_odd_of_even_modulus 8 (by decide) a ha
  have hqo : Odd ((q:ℤ)^2*a) := by
    exact (show Odd (q:ℤ) by exact_mod_cast hq).pow.mul ho
  have hz : lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) 8=0 := by
    have h := lpsUnaryQuadraticGauss_inflate 4 2 ((q:ℤ)^2*a)
    rw [lpsUnaryQuadraticGauss_odd_two _ hqo,mul_zero] at h
    have he : (q:ℤ)^2*a*(4:ℤ)=4*(q:ℤ)^2*a := by ring
    norm_num only [Nat.cast_ofNat] at h
    rw [show (q:ℤ)^2*a*4=4*(q:ℤ)^2*a by ring] at h
    exact h
  rw [lpsThetaCuspGaussProduct,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero]

/-- At higher powers of two the actual theta product is minus thirty-two times modulus squared. -/
lemma lpsThetaCuspGaussProduct_two_pow_ge_four (q : ℕ) (hq : Odd q)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (2^(e+4)))) :
    lpsThetaCuspGaussProduct q a (2^(e+4))= -32*((2^(e+4):ℕ):ℂ)^2 := by
  have hc : q.Coprime (2^(e+4)) := hq.coprime_two_right.pow_right _
  have hu : IsUnit ((q:ℤ):ZMod (2^(e+4))) := by
    exact_mod_cast (ZMod.isUnit_iff_coprime q (2^(e+4))).mpr hc
  have hN : 2^(e+4)=4*2^2*2^e := by rw [pow_add];ring
  obtain ⟨b,u,hd⟩ := lpsZMod_unit_bezout (2^(e+4)) a ha
  have hs := lpsUnaryQuadraticGauss_square_scale (2^(e+4)) 2 (2^e) hN
    (by decide) (by positivity) a b u hd
  norm_num only [Nat.cast_ofNat] at hs
  have he : 4*(q:ℤ)^2*a=(a*(2:ℤ)^2)*(q:ℤ)^2 := by ring
  rw [lpsThetaCuspGaussProduct,he,lpsUnaryQuadraticGauss_unit_square _ (a*(2:ℤ)^2) q hu]
  rw [show a*(2:ℤ)^2=a*4 by ring,hs]
  rw [show lpsUnaryQuadraticGauss a (2^(e+4))*((2:ℂ)*lpsUnaryQuadraticGauss a (2^(e+4)))^3=
      8*lpsUnaryQuadraticGauss a (2^(e+4))^4 by ring]
  have hf := lpsUnaryQuadraticGauss_two_pow_fourth (e+2) a ha
  rw [show e+2+2=e+4 by omega] at hf
  rw [hf]
  ring

/-- The primitive modulus-four additive phase at a unit is the actual Gauss sum times its character. -/
lemma lpsChi4UnitPhase (d : ZMod 4) (hd : IsUnit d) :
    2*ZMod.stdAddChar d=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character d := by
  have hzero : ¬IsUnit (0:ZMod 4) := by decide
  have htwo : ¬IsUnit (2:ZMod 4) := by decide
  fin_cases d
  · change IsUnit (0:ZMod 4) at hd
    exact False.elim (hzero hd)
  · change 2*ZMod.stdAddChar (1:ZMod 4)=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character 1
    rw [lpsChi4E2Character_values.2.1,lpsChi4E2Gauss_eq,mul_one]
  · change IsUnit (2:ZMod 4) at hd
    exact False.elim (htwo hd)
  · change 2*ZMod.stdAddChar (3:ZMod 4)=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character 3
    rw [lpsChi4E2Character_values.2.2.2,lpsChi4E2Gauss_eq,lpsChi4Phase_three]
    ring

/-- The modulus-four theta product is expressed through the actual additive phase and character. -/
lemma lpsThetaCuspGaussProduct_four_character (q : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod 4)) :
    lpsThetaCuspGaussProduct q a 4=16*(8+4*
      gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character (a:ZMod 4)) := by
  rw [lpsThetaCuspGaussProduct_four,lpsUnaryQuadraticGauss_four]
  have h := lpsChi4UnitPhase (a:ZMod 4) ha
  linear_combination 64*h

end QEC.Coding.TannerLiftedProduct
