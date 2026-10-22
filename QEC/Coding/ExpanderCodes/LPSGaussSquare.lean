import QEC.Coding.ExpanderCodes.LPSThetaFourier

/-!
# Actual square scaling of finite quadratic Gauss sums

Primitive character orthogonality and explicit finite residue blocks prove the
exact mask projection, including nonunit coefficients. Determinant one then
completes every mask frequency with zero phase when the modulus is divisible by
four times the scaling square. This proves perfect-square coefficient scaling.
Actual coefficient/modulus inflation also removes square factors from the
modulus, supplying the arithmetic reduction for Gauss fourth-power evaluation.

These are identities of the existing finite Gauss sums, with no assumed value,
target coefficient, or transformation law. The cyclic frequency ring does not
restrict the quantum-code alphabet. General fourth-power evaluation, modularity,
strong Fourier growth and the PK22 main theorem remain separate obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Real

/-- The determinant unit completes each mask frequency with zero quadratic phase. -/
lemma lpsQuadraticFourier_mask_frequency (N d k : ℕ) [NeZero N]
    (hN : N=4*d^2*k) (a b u j : ℤ) (hdet : a*u-b*(N:ℤ)=1) :
    lpsQuadraticFourier N (a:ZMod N) ((4*(d:ℤ)*(k:ℤ)*j:ℤ):ZMod N) =
      lpsUnaryQuadraticGauss a N := by
  have had : (a:ZMod N)*(u:ZMod N)=1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    simpa using h
  let t : ZMod N := ((2*(d:ℤ)*(k:ℤ)*u*j:ℤ):ZMod N)
  have hn : ((4*(d:ℤ)*(k:ℤ)*j:ℤ):ZMod N)=2*(a:ZMod N)*t := by
    dsimp [t]
    push_cast
    linear_combination -(4:ZMod N)*(d:ZMod N)*(k:ZMod N)*(j:ZMod N)*had
  have hphase : -(a:ZMod N)*t^2=0 := by
    dsimp [t]
    push_cast
    calc
      _ = (-(a:ZMod N)*(k:ZMod N)*(u:ZMod N)^2*(j:ZMod N)^2)*(N:ZMod N) := by
        rw [hN]
        push_cast
        ring
      _ = 0 := by rw [ZMod.natCast_self,mul_zero]
  rw [hn,lpsQuadraticFourier_completeSquare,hphase,AddChar.map_zero_eq_one,one_mul,
    lpsQuadraticFourier_zero_eq_Gauss]

/-- Inflating the modulus and argument by the same factor preserves the actual character. -/
lemma lpsChar_inflate (d m : ℕ) [NeZero d] [NeZero m] (x : ℤ) :
    ZMod.stdAddChar (((m:ℤ)*x:ℤ):ZMod (d*m)) =
      ZMod.stdAddChar (x:ZMod d) := by
  rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hm : (m:ℂ)≠0 := by exact_mod_cast NeZero.ne m
  field_simp

/-- Character inflation with an explicitly identified modulus. -/
lemma lpsChar_inflate_modulus (N d m : ℕ) [NeZero N] [NeZero d] [NeZero m]
    (hN : N=d*m) (x : ℤ) :
    ZMod.stdAddChar (((m:ℤ)*x:ℤ):ZMod N) = ZMod.stdAddChar (x:ZMod d) := by
  subst N
  exact lpsChar_inflate d m x

/-- Actual residue blocks reindex the complete cyclic sum. -/
lemma lpsZMod_sum_blocks (d m : ℕ) [NeZero d] [NeZero m] (f : ZMod (d*m) → ℂ) :
    (∑ r : ZMod (d*m), f r) =
      ∑ i : Fin d, ∑ j : Fin m, f ((j.val+m*i.val:ℕ):ZMod (d*m)) := by
  classical
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (finProdFinEquiv.trans (ZMod.finEquiv (d*m)).toEquiv)
  intro r
  change f ((r.2.val+m*r.1.val:ℕ):ZMod (d*m)) =
    f (ZMod.finEquiv (d*m) (finProdFinEquiv r))
  exact congrArg f (lpsFin_cast_finEquiv (d*m) (finProdFinEquiv r))

/-- Primitive character orthogonality evaluates the finite divisibility mask. -/
lemma lpsChar_mask_sum (d m : ℕ) [NeZero d] [NeZero m] (r : ℤ) :
    (∑ j : Fin d, ZMod.stdAddChar (((m:ℤ)*j.val*r:ℤ):ZMod (d*m))) =
      if (r:ZMod d)=0 then (d:ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift (r:ZMod d) (ZMod.isPrimitive_stdAddChar d)
  rw [ZMod.card] at h
  push_cast at h
  rw [← h]
  apply Fintype.sum_equiv (ZMod.finEquiv d).toEquiv
  intro j
  rw [show ((m:ℤ)*j.val*r:ℤ)=(m:ℤ)*(j.val*r) by ring,lpsChar_inflate]
  change ZMod.stdAddChar (((j.val:ℤ)*r:ℤ):ZMod d) =
    ZMod.stdAddChar (ZMod.finEquiv d j*(r:ZMod d))
  rw [← lpsFin_cast_finEquiv]
  push_cast
  rfl

/-- A scaled quadratic phase is periodic across the actual residue blocks. -/
lemma lpsQuadratic_scaled_period (d m : ℕ) [NeZero d] [NeZero m]
    (a r i : ℤ) :
    ZMod.stdAddChar (((a*(d:ℤ)^2*(r+(m:ℤ)*i)^2):ℤ):ZMod (d*m)) =
      ZMod.stdAddChar (((a*(d:ℤ)^2*r^2):ℤ):ZMod (d*m)) := by
  congr 1
  have hz : (((d:ℤ)*(m:ℤ):ℤ):ZMod (d*m)) = 0 := by
    push_cast
    exact_mod_cast ZMod.natCast_self (d*m)
  calc
    _ = (((a*(d:ℤ)^2*r^2):ℤ):ZMod (d*m)) +
        (((a*(d:ℤ)*(2*r*i+(m:ℤ)*i^2)):ℤ):ZMod (d*m))*
        (((d:ℤ)*(m:ℤ):ℤ):ZMod (d*m)) := by push_cast;ring
    _ = _ := by rw [hz,mul_zero,add_zero]

/-- Interchanging block sizes exposes the residue modulo the scaling factor. -/
lemma lpsZMod_sum_residue_blocks (d m : ℕ) [NeZero d] [NeZero m]
    (f : ZMod (d*m) → ℂ) :
    (∑ r : ZMod (d*m), f r) =
      ∑ i : Fin m, ∑ j : Fin d, f ((j.val+d*i.val:ℕ):ZMod (d*m)) := by
  classical
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv
    (finProdFinEquiv.trans ((finCongr (Nat.mul_comm m d)).trans
      (ZMod.finEquiv (d*m)).toEquiv))
  intro r
  change f ((r.2.val+d*r.1.val:ℕ):ZMod (d*m)) =
    f (ZMod.finEquiv (d*m) ((finCongr (Nat.mul_comm m d)) (finProdFinEquiv r)))
  rw [← lpsFin_cast_finEquiv]
  rfl

/-- Each residue block contributes the same genuinely scaled quadratic sum. -/
lemma lpsQuadraticGauss_scaled_blocks (d m : ℕ) [NeZero d] [NeZero m]
    (a : ℤ) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) (d*m) =
      (d:ℂ) * ∑ r : Fin m,
        ZMod.stdAddChar (((a*(d:ℤ)^2*(r.val:ℤ)^2):ℤ):ZMod (d*m)) := by
  classical
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier,lpsZMod_sum_blocks]
  simp only [zero_mul,add_zero]
  have h (i : Fin d) (r : Fin m) :
      ZMod.stdAddChar ((((a*(d:ℤ)^2):ℤ):ZMod (d*m))*((r.val+m*i.val:ℕ):ZMod (d*m))^2) =
      ZMod.stdAddChar (((a*(d:ℤ)^2*(r.val:ℤ)^2):ℤ):ZMod (d*m)) := by
    have he := lpsQuadratic_scaled_period d m a r.val i.val
    convert he using 1
    push_cast
    rfl
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- The finite character mask projects the actual Gauss sum onto scaled residues. -/
lemma lpsQuadraticGauss_mask_sum (d m : ℕ) [NeZero d] [NeZero m]
    (a : ℤ) :
    (∑ j : Fin d, lpsQuadraticFourier (d*m) (a:ZMod (d*m))
      (((m:ℤ)*j.val:ℤ):ZMod (d*m))) =
      lpsUnaryQuadraticGauss (a*(d:ℤ)^2) (d*m) := by
  classical
  unfold lpsQuadraticFourier
  rw [Finset.sum_comm]
  simp_rw [AddChar.map_add_eq_mul,← Finset.mul_sum]
  have h (r : ZMod (d*m)) :
      (∑ j : Fin d, ZMod.stdAddChar
        ((((m:ℤ)*j.val:ℤ):ZMod (d*m))*r)) =
      if (r.val:ZMod d)=0 then (d:ℂ) else 0 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val r]
    have he := lpsChar_mask_sum d m r.val
    convert he using 1 <;> push_cast <;> rfl
  simp_rw [h]
  rw [lpsZMod_sum_residue_blocks,lpsQuadraticGauss_scaled_blocks]
  have hr (i : Fin m) (r : Fin d) :
      ((((r.val+d*i.val:ℕ):ZMod (d*m)).val):ZMod d)=(r.val:ZMod d) := by
    -- The chosen residue is below d*m, so the outer cast has this actual value.
    have hlt : r.val+d*i.val < d*m := by
      calc
        r.val+d*i.val < d+d*i.val := Nat.add_lt_add_right r.isLt _
        _ = d*(i.val+1) := by ring
        _ ≤ d*m := Nat.mul_le_mul_left d i.isLt
    rw [ZMod.val_natCast_of_lt hlt]
    simp
  simp_rw [hr]
  have hz (r : Fin d) : (r.val:ZMod d)=0 ↔ r=0 := by
    rw [lpsFin_cast_finEquiv]
    rw [← (ZMod.finEquiv d).map_zero]
    exact (ZMod.finEquiv d).injective.eq_iff
  simp_rw [hz]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,Fin.val_zero,
    zero_add,Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- Perfect-square scaling follows from the actual mask projection and completed square. -/
lemma lpsUnaryQuadraticGauss_square_scale (N d k : ℕ) [NeZero N]
    (hN : N=4*d^2*k) (hd : 0 < d) (hk : 0 < k)
    (a b u : ℤ) (hdet : a*u-b*(N:ℤ)=1) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N =
      (d:ℂ)*lpsUnaryQuadraticGauss a N := by
  let m := 4*d*k
  have hm : 0 < m := by dsimp [m];positivity
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero m := ⟨ne_of_gt hm⟩
  have hNm : N=d*m := by dsimp [m];rw [hN];ring
  have hdetm : a*u-b*((d*m:ℕ):ℤ)=1 := by rw [← hNm];exact hdet
  have hmask := lpsQuadraticGauss_mask_sum d m a
  have hf (j : Fin d) :
      lpsQuadraticFourier (d*m) (a:ZMod (d*m)) (((m:ℤ)*j.val:ℤ):ZMod (d*m)) =
        lpsUnaryQuadraticGauss a (d*m) := by
    have h := lpsQuadraticFourier_mask_frequency (d*m) d k (hNm.symm.trans hN) a b u j.val hdetm
    simpa only [m,Nat.cast_mul,Nat.cast_ofNat] using h
  simp_rw [hf] at hmask
  rw [hNm]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hmask.symm

/-- Coefficient and modulus inflation repeat each actual lower-modulus phase. -/
lemma lpsUnaryQuadraticGauss_inflate (m n : ℕ) [NeZero m] [NeZero n]
    (a : ℤ) :
    lpsUnaryQuadraticGauss (a*(m:ℤ)) (m*n) =
      (m:ℂ)*lpsUnaryQuadraticGauss a n := by
  classical
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier,lpsZMod_sum_blocks]
  simp only [zero_mul,add_zero]
  have h (i : Fin m) (r : Fin n) :
      ZMod.stdAddChar ((((a*(m:ℤ)):ℤ):ZMod (m*n))*((r.val+n*i.val:ℕ):ZMod (m*n))^2) =
        ZMod.stdAddChar ((a:ZMod n)*(r.val:ZMod n)^2) := by
    have he : (((a*(m:ℤ)):ℤ):ZMod (m*n))*((r.val+n*i.val:ℕ):ZMod (m*n))^2 =
        (((m:ℤ)*(a*(r.val:ℤ)^2):ℤ):ZMod (m*n)) := by
      have hz : ((m*n:ℕ):ZMod (m*n))=0 := ZMod.natCast_self _
      push_cast at hz ⊢
      linear_combination (a:ZMod (m*n))*(i.val:ZMod (m*n))*
        (2*(r.val:ZMod (m*n))+(n:ZMod (m*n))*(i.val:ZMod (m*n)))*hz
    rw [he]
    have hi := lpsChar_inflate_modulus (m*n) n m (Nat.mul_comm _ _) (a*(r.val:ℤ)^2)
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_natCast] using hi
  simp_rw [h]
  rw [Finset.sum_const]
  simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro r
  simp only [zero_mul,add_zero]
  change ZMod.stdAddChar ((a:ZMod n)*(r.val:ZMod n)^2) =
    ZMod.stdAddChar ((a:ZMod n)*(ZMod.finEquiv n r)^2)
  rw [← lpsFin_cast_finEquiv]

/-- Square scaling and inflation remove a square factor from the actual modulus. -/
lemma lpsUnaryQuadraticGauss_square_modulus (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (a b u : ℤ) (hdet : a*u-b*((4*d^2*k:ℕ):ℤ)=1) :
    lpsUnaryQuadraticGauss a (4*d^2*k) =
      (d:ℂ)*lpsUnaryQuadraticGauss a (4*k) := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero k := ⟨ne_of_gt hk⟩
  have hi := lpsUnaryQuadraticGauss_inflate (d^2) (4*k) a
  have hm : d^2*(4*k)=4*d^2*k := by ring
  rw [hm] at hi
  norm_num only [Nat.cast_pow] at hi
  have hs := lpsUnaryQuadraticGauss_square_scale (4*d^2*k) d k rfl hd hk a b u hdet
  rw [hs] at hi
  have hdC : (d:ℂ)≠0 := by exact_mod_cast ne_of_gt hd
  apply mul_left_cancel₀ hdC
  calc
    _ = (d:ℂ)^2*lpsUnaryQuadraticGauss a (4*k) := hi
    _ = _ := by ring

end QEC.Coding.TannerLiftedProduct
