import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Genuine determinant-p Hecke representatives

For prime p away from Gamma0(N), actual integral matrices factor into the p+1
standard upper triangular representatives. The representative index is unique;
right multiplication by Gamma0 gives a proved finite permutation. Explicit
integral matrices also put every representative in the same Gamma0 double coset.
Rational and real GL realizations preserve the actual matrix products.
These internal arithmetic proofs supply the genuine cusp Hecke action.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- Finite-field determinant zero constructs the unique finite-column ratio and integral divisibility. -/
lemma lpsHeckeFiniteColumn (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=(p:ℤ))
    (hcol : (A 0 0 : ZMod p)≠0 ∨ (A 1 0 : ZMod p)≠0) :
    ∃ j : Fin p, (p:ℤ) ∣ A 0 1-A 0 0*(j.val:ℤ) ∧
      (p:ℤ) ∣ A 1 1-A 1 0*(j.val:ℤ) := by
  have hd : (A 0 0 : ZMod p)*(A 1 1 : ZMod p)-
      (A 0 1 : ZMod p)*(A 1 0 : ZMod p)=0 := by
    have h := congrArg (fun x : ℤ => (x : ZMod p)) hA
    simpa [Matrix.det_fin_two] using h
  rcases hcol with ha | hc
  · let u : ZMod p := (A 0 1 : ZMod p)/(A 0 0 : ZMod p)
    let j : Fin p := ⟨u.val,ZMod.val_lt u⟩
    have hj : (j.val : ZMod p)=u := ZMod.natCast_zmod_val u
    refine ⟨j,?_,?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      ring
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      linear_combination hd
  · let u : ZMod p := (A 1 1 : ZMod p)/(A 1 0 : ZMod p)
    let j : Fin p := ⟨u.val,ZMod.val_lt u⟩
    have hj : (j.val : ZMod p)=u := ZMod.natCast_zmod_val u
    refine ⟨j,?_,?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      linear_combination -hd
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hj]
      dsimp [u]
      field_simp
      ring

/-- The actual integral p+1 upper triangular representative matrices. -/
def lpsHeckeUpperMatrix (p : ℕ) : Option (Fin p)→Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p:ℤ),0;0,1]
  | some j => !![1,(j.val:ℤ);0,(p:ℤ)]

/-- Every actual representative has determinant p. -/
lemma lpsHeckeUpperMatrix_det (p : ℕ) (j : Option (Fin p)) :
    (lpsHeckeUpperMatrix p j).det=(p:ℤ) := by
  cases j <;> simp [lpsHeckeUpperMatrix,Matrix.det_fin_two]

/-- Exact integral finite-column factorization by division of proved multiples of p. -/
lemma lpsHeckeFactorFinite (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin p)
    (h0 : (p:ℤ) ∣ A 0 1-A 0 0*(j.val:ℤ))
    (h1 : (p:ℤ) ∣ A 1 1-A 1 0*(j.val:ℤ)) :
    A= !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
      A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)] * lpsHeckeUpperMatrix p (some j) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,
      Int.ediv_mul_cancel h0,Int.ediv_mul_cancel h1]

/-- Exact integral infinity-column factorization when p divides both first-column entries. -/
lemma lpsHeckeFactorInfinity (p : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (h0 : (p:ℤ) ∣ A 0 0) (h1 : (p:ℤ) ∣ A 1 0) :
    A= !![A 0 0/(p:ℤ),A 0 1;A 1 0/(p:ℤ),A 1 1] * lpsHeckeUpperMatrix p none := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,
      Int.ediv_mul_cancel h0,Int.ediv_mul_cancel h1]

/-- Every integral determinant-p matrix factors through an actual SL2(Z) matrix and a standard representative. -/
lemma lpsHeckeFactorSL (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det=(p:ℤ)) :
    ∃ (j : Option (Fin p)) (δ : SL(2,ℤ)), A=(δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j := by
  have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hh (D : Matrix (Fin 2) (Fin 2) ℤ) (j : Option (Fin p))
      (h : A=D*lpsHeckeUpperMatrix p j) : D.det=1 := by
    have hd := congrArg Matrix.det h
    rw [hA,Matrix.det_mul,lpsHeckeUpperMatrix_det] at hd
    apply mul_right_cancel₀ hp
    simpa only [one_mul] using hd.symm
  by_cases h0 : (A 0 0 : ZMod p)=0
  · by_cases h1 : (A 1 0 : ZMod p)=0
    · let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0/(p:ℤ),A 0 1;A 1 0/(p:ℤ),A 1 1]
      have he := lpsHeckeFactorInfinity p A
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1)
      exact ⟨none,⟨D,hh D none he⟩,he⟩
    · obtain ⟨j,hj0,hj1⟩ := lpsHeckeFiniteColumn p A hA (Or.inr h1)
      let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
        A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)]
      have he := lpsHeckeFactorFinite p A j hj0 hj1
      exact ⟨some j,⟨D,hh D (some j) he⟩,he⟩
  · obtain ⟨j,hj0,hj1⟩ := lpsHeckeFiniteColumn p A hA (Or.inl h0)
    let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
      A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)]
    have he := lpsHeckeFactorFinite p A j hj0 hj1
    exact ⟨some j,⟨D,hh D (some j) he⟩,he⟩

/-- Coprimality transfers the true lower-left divisibility to the constructed SL2 factor. -/
lemma lpsHeckeFactorGamma0 (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det=(p:ℤ)) (hc : (N:ℤ) ∣ A 1 0) :
    ∃ (j : Option (Fin p)) (δ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧
      A=(δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j := by
  obtain ⟨j,δ,he⟩ := lpsHeckeFactorSL p A hA
  refine ⟨j,δ,?_,he⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  have hz : (A 1 0 : ZMod N)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hc
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) he
  cases j with
  | none =>
    simp [Matrix.mul_apply,Fin.sum_univ_two,lpsHeckeUpperMatrix] at h
    have hZ := congrArg (fun x : ℤ => (x : ZMod N)) h
    push_cast at hZ
    rw [hz] at hZ
    exact ((ZMod.isUnit_iff_coprime p N).mpr hNp).mul_left_eq_zero.mp hZ.symm
  | some j =>
    simp [Matrix.mul_apply,Fin.sum_univ_two,lpsHeckeUpperMatrix] at h
    simpa only [h] using hz

/-- Explicit integral Gamma0 factors put every representative in the same double coset. -/
lemma lpsHeckeUpperMatrix_doubleCoset (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    ∃ (δ γ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧ γ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i=(δ:Matrix (Fin 2) (Fin 2) ℤ)*
        lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ) := by
  cases i with
  | none => exact ⟨1,1,(CongruenceSubgroup.Gamma0 N).one_mem,
      (CongruenceSubgroup.Gamma0 N).one_mem,by simp⟩
  | some j =>
    have hNu : IsUnit (N:ZMod p) := (ZMod.isUnit_iff_coprime N p).mpr hNp.symm
    have hN : (N:ZMod p)≠0 := hNu.ne_zero
    let k : ℤ := ((j.val:ZMod p)-(N:ZMod p)⁻¹).val
    have hk : (k:ZMod p)=(j.val:ZMod p)-(N:ZMod p)⁻¹ := by
      dsimp [k]
      exact_mod_cast ZMod.natCast_zmod_val ((j.val:ZMod p)-(N:ZMod p)⁻¹)
    let γ : SL(2,ℤ) := ⟨!![1,k;(N:ℤ),1+(N:ℤ)*k],by simp [Matrix.det_fin_two];ring⟩
    have hγ : γ∈CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [γ]
    let A := lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ)
    have hAe : A= !![(p:ℤ),(p:ℤ)*k;(N:ℤ),1+(N:ℤ)*k] := by
      ext r c
      fin_cases r <;> fin_cases c <;>
        simp [A,γ,lpsHeckeUpperMatrix]
    have h0 : (p:ℤ)∣A 0 1-A 0 0*(j.val:ℤ) := by
      rw [hAe]
      change (p:ℤ)∣(p:ℤ)*k-(p:ℤ)*(j.val:ℤ)
      exact dvd_sub (dvd_mul_right _ _) (dvd_mul_right _ _)
    have h1 : (p:ℤ)∣A 1 1-A 1 0*(j.val:ℤ) := by
      rw [hAe]
      change (p:ℤ)∣1+(N:ℤ)*k-(N:ℤ)*(j.val:ℤ)
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hk]
      field_simp
      ring
    let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
      A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)]
    have he := lpsHeckeFactorFinite p A j h0 h1
    have hDA : D.det=1 := by
      have hd := congrArg Matrix.det he
      have hA : A.det=(p:ℤ) := by
        simp [A,Matrix.det_mul,lpsHeckeUpperMatrix_det,Matrix.SpecialLinearGroup.det_coe]
      rw [hA,Matrix.det_mul,lpsHeckeUpperMatrix_det] at hd
      have hpZ : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      apply mul_right_cancel₀ hpZ
      simpa only [one_mul] using hd.symm
    let δ : SL(2,ℤ) := ⟨D,hDA⟩
    have hδ : δ∈CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      have hD : D 1 0=(N:ℤ) := by
        simp [D,hAe]
      simp [δ,hD]
    refine ⟨δ⁻¹,γ,(CongruenceSubgroup.Gamma0 N).inv_mem hδ,hγ,?_⟩
    have hi : ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*(δ:Matrix (Fin 2) (Fin 2) ℤ)=1 := by
      rw [←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
    calc
      lpsHeckeUpperMatrix p (some j)=((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*
          ((δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (some j)) := by
            rw [←Matrix.mul_assoc,hi,Matrix.one_mul]
      _=((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*A :=
        congrArg (fun M => ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*M) he.symm
      _=_ := (Matrix.mul_assoc _ _ _).symm

/-- Integral factors cannot identify distinct standard representative indices. -/
lemma lpsHeckeUpperMatrix_index_unique (p : ℕ) [Fact p.Prime]
    (i j : Option (Fin p)) (D : Matrix (Fin 2) (Fin 2) ℤ)
    (h : lpsHeckeUpperMatrix p i=D*lpsHeckeUpperMatrix p j) : i=j := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h10 h11
      have hz := congrArg (fun x : ℤ => (x : ZMod p)) h11
      simp [←h10] at hz
  | some i =>
    cases j with
    | none =>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00
      have hz := congrArg (fun x : ℤ => (x : ZMod p)) h00
      simp at hz
    | some j =>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01
      have hz := congrArg (fun x : ℤ => (x : ZMod p)) h01
      have he : (i.val : ZMod p)=(j.val : ZMod p) := by
        simpa [←h00] using hz
      have hv := congrArg ZMod.val he
      have hij : i=j := Fin.ext (by
        simpa only [ZMod.val_cast_of_lt i.isLt,ZMod.val_cast_of_lt j.isLt] using hv)
      exact congrArg some hij

/-- Actual right multiplication by Gamma0 factors through another standard representative. -/
lemma lpsHeckeRightFactor (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    ∃ (j : Option (Fin p)) (δ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
        (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j := by
  apply lpsHeckeFactorGamma0 N p hNp
  · rw [Matrix.det_mul,lpsHeckeUpperMatrix_det,γ.det_coe,mul_one]
  · have hc : (N:ℤ) ∣ γ 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
        (CongruenceSubgroup.Gamma0_mem.mp hγ)
    cases i with
    | none => simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using hc
    | some i =>
      simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using dvd_mul_of_dvd_right hc (p:ℤ)

/-- The representative index selected from the proved right factorization. -/
noncomputable def lpsHeckeRightIndex (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) : Option (Fin p) :=
  (lpsHeckeRightFactor N p hNp γ hγ i).choose

/-- The selected index has a genuine integral Gamma0 factor. -/
lemma lpsHeckeRightIndex_spec (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    ∃ δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
        (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i) :=
  (lpsHeckeRightFactor N p hNp γ hγ i).choose_spec

/-- Right multiplication by the inverse recovers the original representative index. -/
lemma lpsHeckeRightIndex_inverse (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ)
      (lpsHeckeRightIndex N p hNp γ hγ i)=i := by
  let j := lpsHeckeRightIndex N p hNp γ hγ i
  let k := lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ) j
  obtain ⟨δ,_hδ,hf⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
  obtain ⟨ε,_hε,hb⟩ := lpsHeckeRightIndex_spec N p hNp γ⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem hγ) j
  have he : lpsHeckeUpperMatrix p i=
      ((δ*ε:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p k := by
    calc
      lpsHeckeUpperMatrix p i=
          (lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ))*((γ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one,Matrix.mul_one]
      _ = _ := by
        dsimp only [j,k] at hb ⊢
        rw [hf,Matrix.mul_assoc,hb,←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul]
  exact (lpsHeckeUpperMatrix_index_unique p i k _ he).symm

/-- The actual right-index map is a permutation of the finite representative set. -/
lemma lpsHeckeRightIndex_bijective (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    Function.Bijective (lpsHeckeRightIndex N p hNp γ hγ) := by
  have hl : Function.LeftInverse
      (lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ))
      (lpsHeckeRightIndex N p hNp γ hγ) := lpsHeckeRightIndex_inverse N p hNp γ hγ
  have hr : Function.RightInverse
      (lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ))
      (lpsHeckeRightIndex N p hNp γ hγ) := by
    intro i
    simpa only [inv_inv] using lpsHeckeRightIndex_inverse N p hNp γ⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem hγ) i
  exact ⟨hl.injective,hr.surjective⟩

/-- Actual invertible representative matrices over any characteristic-zero field. -/
noncomputable def lpsHeckeUpperGL (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) : GL (Fin 2) R :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((lpsHeckeUpperMatrix p i).map (Int.castRingHom R)) (by
      rw [Int.coe_castRingHom,←Int.cast_det,lpsHeckeUpperMatrix_det]
      exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- The GL matrix has exactly the integral representative entries after casting. -/
lemma lpsHeckeUpperGL_coe (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL R p i : Matrix (Fin 2) (Fin 2) R)=
      (lpsHeckeUpperMatrix p i).map (Int.castRingHom R) := rfl

/-- The GL representative has determinant p. -/
lemma lpsHeckeUpperGL_det (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL R p i).det.val=(p:R) := by
  change ((lpsHeckeUpperGL R p i : Matrix (Fin 2) (Fin 2) R).det)=_
  rw [lpsHeckeUpperGL_coe,Int.coe_castRingHom,←Int.cast_det,lpsHeckeUpperMatrix_det]
  simp

/-- The real representative is the actual real image of its rational matrix. -/
lemma lpsHeckeUpperGL_rat_real (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL ℚ p i).map (Rat.castHom ℝ)=lpsHeckeUpperGL ℝ p i := by
  apply Units.ext
  ext r c
  simp [Matrix.GeneralLinearGroup.map_apply,lpsHeckeUpperGL,Matrix.map_apply]

/-- Integral factor equality transfers to the actual GL products. -/
lemma lpsHeckeRightFactorGL (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i j : Option (Fin p)) (γ δ : SL(2,ℤ))
    (h : lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j) :
    lpsHeckeUpperGL R p i*Matrix.SpecialLinearGroup.mapGL R γ=
      Matrix.SpecialLinearGroup.mapGL R δ*lpsHeckeUpperGL R p j := by
  apply Units.ext
  change (lpsHeckeUpperMatrix p i).map (Int.castRingHom R)*
      (γ:Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R)=
    (δ:Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R)*
      (lpsHeckeUpperMatrix p j).map (Int.castRingHom R)
  simpa only [Matrix.map_mul] using congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom R)) h


end QEC.Coding.TannerLiftedProduct
