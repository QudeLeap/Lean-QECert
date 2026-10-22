import QEC.Coding.ExpanderCodes.LPSHeckeRepresentatives
import QEC.Coding.ExpanderCodes.LPSEisensteinDifference

/-!
# Actual integral Hecke intersections and dilation conjugacy

Entrywise integral divisibility characterizes both original Hecke intersections. Actual real GL equalities prove the two-way dilation conjugacy. No finite cover, adjunction or arithmetic spectral estimate is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

/-- The actual infinity representative conjugates Gamma0(Np) to an integral Gamma0(N) matrix. -/
lemma lpsHeckeIntersection_conjugateMatrix (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p none * (γ:Matrix (Fin 2) (Fin 2) ℤ) =
        (δ:Matrix (Fin 2) (Fin 2) ℤ) * lpsHeckeUpperMatrix p none := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨t,ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (N*p)).mp hγ
  have hc : γ 1 0 = (p:ℤ)*((N:ℤ)*t) := by
    rw [ht]
    push_cast
    ring
  let δ := lpsE2DilationConjugate p γ ((N:ℤ)*t) hc
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((N:ℤ)*t:ℤ):ZMod N)=0
    simp
  refine ⟨δ,hδ,?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,δ,lpsE2DilationConjugate,hc,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,mul_comm]

/-- The integral dilation conjugate gives the exact equality of the original real GL products. -/
lemma lpsHeckeIntersection_conjugate (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersection_conjugateMatrix N p γ hγ
  exact ⟨δ,hδ,lpsHeckeRightFactorGL ℝ p none none γ δ he⟩

/-- The true real GL conjugacy forces original lower-left Np divisibility. -/
lemma lpsHeckeIntersection_of_conjugate (N p : ℕ) [Fact p.Prime]
    (γ δ : SL(2,ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N)
    (he : lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none) :
    γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by
  have hr := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0) he
  have hz : γ 1 0 = (δ 1 0)*(p:ℤ) := by
    have hh : (γ 1 0 : ℝ)=(δ 1 0 : ℝ)*(p:ℝ) := by
      simpa [lpsHeckeUpperGL,lpsHeckeUpperMatrix,Matrix.SpecialLinearGroup.mapGL,
        Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using hr
    exact_mod_cast hh
  rw [CongruenceSubgroup.Gamma0_mem] at hδ ⊢
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) N).mp hδ
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (N*p)).mpr
  obtain ⟨t,ht⟩ := hd
  refine ⟨t,?_⟩
  rw [hz,ht]
  push_cast
  ring

/-- Original Gamma0(Np) membership is exactly the true infinity-representative conjugacy criterion. -/
lemma lpsHeckeIntersection_iff (N p : ℕ) [Fact p.Prime] (γ : SL(2,ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 (N*p) ↔
      ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
        lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
          Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  constructor
  · exact lpsHeckeIntersection_conjugate N p γ
  · rintro ⟨δ,hδ,he⟩
    exact lpsHeckeIntersection_of_conjugate N p γ δ hδ he

/-- The actual integral upper-right congruence subgroup, used by the conjugate intersection. -/
def lpsUpperCongruence (p : ℕ) : Subgroup SL(2,ℤ) where
  carrier := {γ | (γ 0 1 : ZMod p)=0}
  one_mem' := by simp
  mul_mem' {γ} {δ} hγ hδ := by
    change (γ 0 1:ZMod p)=0 at hγ
    change (δ 0 1:ZMod p)=0 at hδ
    change (((γ*δ:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p)=0
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hγ,hδ]
  inv_mem' {γ} hγ := by
    change (γ 0 1:ZMod p)=0 at hγ
    change (γ⁻¹ 0 1:ZMod p)=0
    simpa [Matrix.SpecialLinearGroup.SL2_inv_expl] using hγ

/-- The true second Hecke intersection imposes original level and upper-right p divisibility. -/
def lpsHeckeConjugateIntersection (N p : ℕ) : Subgroup SL(2,ℤ) :=
  CongruenceSubgroup.Gamma0 N ⊓ lpsUpperCongruence p

/-- The second intersection has exactly its original level and integer upper-right divisibility. -/
lemma lpsHeckeConjugateIntersection_mem (N p : ℕ) (γ : SL(2,ℤ)) :
    γ ∈ lpsHeckeConjugateIntersection N p ↔
      γ ∈ CongruenceSubgroup.Gamma0 N ∧ (p:ℤ) ∣ γ 0 1 := by
  change (γ ∈ CongruenceSubgroup.Gamma0 N ∧ (γ 0 1:ZMod p)=0) ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The zero finite representative has a genuine integral factor for every second-intersection matrix. -/
lemma lpsHeckeConjugateIntersection_factorMatrix (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ lpsHeckeConjugateIntersection N p) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p (some ⟨0,(Fact.out:p.Prime).pos⟩) *
          (γ:Matrix (Fin 2) (Fin 2) ℤ) =
        (δ:Matrix (Fin 2) (Fin 2) ℤ) *
          lpsHeckeUpperMatrix p (some ⟨0,(Fact.out:p.Prime).pos⟩) := by
  obtain ⟨hγN,t,ht⟩ := (lpsHeckeConjugateIntersection_mem N p γ).mp hγ
  have hd : Matrix.det !![γ 0 0,t;(p:ℤ)*γ 1 0,γ 1 1]=1 := by
    have hd := γ.det_coe
    rw [Matrix.det_fin_two] at hd ⊢
    change γ 0 0*γ 1 1-t*((p:ℤ)*γ 1 0)=1
    change γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 at hd
    rw [ht] at hd
    linear_combination hd
  let δ : SL(2,ℤ) := ⟨!![γ 0 0,t;(p:ℤ)*γ 1 0,γ 1 1],hd⟩
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((p:ℤ)*γ 1 0:ℤ):ZMod N)=0
    simp [CongruenceSubgroup.Gamma0_mem.mp hγN]
  refine ⟨δ,hδ,?_⟩
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperMatrix,δ,ht,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,mul_comm]

/-- An actual real factor of the zero finite representative forces upper-right p divisibility. -/
lemma lpsHeckeConjugateIntersection_of_factor (N p : ℕ) [Fact p.Prime]
    (γ δ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (he : lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) *
        Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ *
        lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) :
    γ ∈ lpsHeckeConjugateIntersection N p := by
  rw [lpsHeckeConjugateIntersection_mem]
  refine ⟨hγ,δ 0 1,?_⟩
  have hr := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) he
  have hh : (γ 0 1 : ℝ)=(δ 0 1 : ℝ)*(p:ℝ) := by
    simpa [lpsHeckeUpperGL,lpsHeckeUpperMatrix,Matrix.SpecialLinearGroup.mapGL,
      Matrix.map_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply] using hr
  exact_mod_cast hh.trans (mul_comm _ _)

/-- Original level Np divisibility implies original level N divisibility. -/
lemma lpsGamma0_product_le (N p : ℕ) :
    CongruenceSubgroup.Gamma0 (N*p) ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr
  exact dvd_trans (by exact_mod_cast Nat.dvd_mul_right N p)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (N*p)).mp hγ)

/-- Every original Gamma0(Np) matrix conjugates into the true upper-right intersection. -/
lemma lpsHeckeIntersection_conjugate_upper (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ lpsHeckeConjugateIntersection N p ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersection_conjugateMatrix N p γ hγ
  refine ⟨δ,(lpsHeckeConjugateIntersection_mem N p δ).mpr ⟨hδ,?_⟩,
    lpsHeckeRightFactorGL ℝ p none none γ δ he⟩
  have hb := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) he
  refine ⟨γ 0 1,?_⟩
  simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using hb.symm

/-- Every true upper-right intersection matrix is the actual conjugate of a Gamma0(Np) matrix. -/
lemma lpsHeckeConjugateIntersection_conjugate (N p : ℕ) [Fact p.Prime]
    (δ : SL(2,ℤ)) (hδ : δ ∈ lpsHeckeConjugateIntersection N p) :
    ∃γ : SL(2,ℤ),γ ∈ CongruenceSubgroup.Gamma0 (N*p) ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by
  obtain ⟨γ,_hγ,he⟩ := lpsHeckeConjugateIntersection_factorMatrix N p δ hδ
  have hc := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) he
  have hz : γ 1 0=(p:ℤ)*δ 1 0 := by
    simpa [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] using hc.symm
  have hdN := (lpsHeckeConjugateIntersection_mem N p δ).mp hδ |>.1
  rw [CongruenceSubgroup.Gamma0_mem] at hdN
  obtain ⟨t,ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hdN
  have hγNp : γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (N*p)).mpr
    refine ⟨t,?_⟩
    rw [hz,ht]
    push_cast
    ring
  refine ⟨γ,hγNp,?_⟩
  have hmatrix : lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p none := by
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 0) he
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 1) he
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1) he
    simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h11
    have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
    have hd : γ 1 1=δ 1 1 := mul_left_cancel₀ hp (by simpa only [mul_comm] using h11.symm)
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two,←h00,h01,hz,hd,mul_comm]
  exact lpsHeckeRightFactorGL ℝ p none none γ δ hmatrix

end
end QEC.Coding.TannerLiftedProduct
