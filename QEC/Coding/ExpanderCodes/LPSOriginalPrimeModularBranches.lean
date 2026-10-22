import QEC.Coding.ExpanderCodes.LPSOriginalIntegerAffineModel
import QEC.Coding.ExpanderCodes.LPSHeckeCosetCover
import QEC.Coding.ExpanderCodes.LPSHeckeCoefficients

/-!
# Original prime modular-equation branches

The genuine integral-SL representatives yield the p+1 distinct roots of the same
original monic integer modular polynomial. Its holomorphic and pointwise products
are derived from the exact original stabilizer, not from a supplied branch law.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

lemma lpsOriginalIntegralSLAction_eq (g : SL(2,ℤ)) (τ : ℍ) :
    g • τ = Matrix.SpecialLinearGroup.mapGL ℝ g • τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_smul_of_det_pos (by simp)]
  simp [UpperHalfPlane.num,UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix,Matrix.map,Matrix.of_apply]

lemma lpsOriginalJInvariant_integralSL (g : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalJInvariant (g • τ)=lpsOriginalJInvariant τ := by
  rw [lpsOriginalIntegralSLAction_eq]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨g,rfl⟩ τ

lemma lpsOriginalGamma0OneTop : CongruenceSubgroup.Gamma0 1=⊤ := by
  ext γ
  simp only [CongruenceSubgroup.Gamma0_mem,Subgroup.mem_top,iff_true]
  exact Subsingleton.elim _ _

lemma lpsOriginalPrimeGamma0CosetDegree (p : ℕ) [Fact p.Prime] :
    Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)=p+1 := by
  have hone : (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ))=𝒮ℒ := by
    change (CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)=_
    rw [lpsOriginalGamma0OneTop,MonoidHom.range_eq_map]
  change (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ=p+1
  rw [←hone]
  change ((CongruenceSubgroup.Gamma0 p).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
    ((CongruenceSubgroup.Gamma0 1).map (Matrix.SpecialLinearGroup.mapGL ℝ))=p+1
  rw [Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective]
  simpa only [Subgroup.relIndex, one_mul] using lpsHeckeIntersection_index 1 p (Nat.coprime_one_right p)

lemma lpsOriginalPrimeIntegerPolynomial_degree (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).natDegree=p+1 := by
  rw [lpsOriginalIntegerPolynomial_degree,lpsOriginalPrimeGamma0CosetDegree]

def lpsOriginalPrimeBranch (p : ℕ) [Fact p.Prime]
    (m : Option (Fin p)) (τ : ℍ) : ℂ :=
  lpsOriginalJInvariant (lpsHeckeUpperGL ℝ p m • τ)

lemma lpsOriginalPrimeBranch_infty (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    lpsOriginalPrimeBranch p none τ=lpsOriginalJDilated p (Fact.out : p.Prime).pos τ := by
  rw [lpsOriginalPrimeBranch,lpsHeckeUpperGL_infty]
  rfl

lemma lpsOriginalPrimeBranch_finite_point (p : ℕ) [Fact p.Prime] (m : Fin p) (τ : ℍ) :
    ((lpsHeckeUpperGL ℝ p (some m) • τ:ℍ):ℂ)=
      ((τ:ℂ)+(m.val:ℂ))/(p:ℂ) :=
  lpsHeckeUpperGL_finite_action p m τ


def lpsOriginalPrimeBranchSL (p : ℕ) (i : Option (Fin p)) : SL(2,ℤ) :=
  match i with
  | none => 1
  | some m => ⟨!![0,-1;1,(m.val:ℤ)],by simp [Matrix.det_fin_two]⟩

lemma lpsOriginalPrimeBranchSL_none (p : ℕ) :
    lpsOriginalPrimeBranchSL p none=1 := rfl

lemma lpsOriginalPrimeBranchSL_finite_matrix (p : ℕ) (m : Fin p) :
    (lpsOriginalPrimeBranchSL p (some m) : Matrix (Fin 2) (Fin 2) ℤ)=
      !![0,-1;1,(m.val:ℤ)] := rfl

lemma lpsOriginalPrimeBranchSL_finite_coe (p : ℕ) (m : Fin p) (τ : ℍ) :
    ((lpsOriginalPrimeBranchSL p (some m) • τ : ℍ) : ℂ)=
      -1/((τ:ℂ)+(m.val:ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [lpsOriginalPrimeBranchSL_finite_matrix,Matrix.of_apply]

lemma lpsOriginalPrimeBranchSL_finite_dilation (p : ℕ) [Fact p.Prime]
    (m : Fin p) (τ : ℍ) :
    lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 •
      (lpsOriginalPrimeBranchSL p (some m) • τ)=
      ModularGroup.S • (lpsHeckeUpperGL ℝ p (some m) • τ) := by
  apply UpperHalfPlane.ext
  rw [lpsOriginalJDilated_coe,lpsOriginalPrimeBranchSL_finite_coe,
    UpperHalfPlane.modular_S_smul]
  change (p:ℂ)*(-1/((τ:ℂ)+(m.val:ℂ)))=
    (-((lpsHeckeUpperGL ℝ p (some m) • τ : ℍ) : ℂ))⁻¹
  rw [lpsHeckeUpperGL_finite_action]
  rw [inv_neg,inv_div]
  simp only [div_eq_mul_inv]
  ring

lemma lpsOriginalPrimeBranchSL_function (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    lpsOriginalJDilated p (Fact.out : p.Prime).pos
      (lpsOriginalPrimeBranchSL p i • τ)=lpsOriginalPrimeBranch p i τ := by
  cases i with
  | none => simp only [lpsOriginalPrimeBranchSL,one_smul,lpsOriginalPrimeBranch_infty]
  | some m =>
    rw [lpsOriginalJDilated,lpsOriginalPrimeBranchSL_finite_dilation]
    exact lpsOriginalJInvariant_integralSL ModularGroup.S _

def lpsOriginalPrimeBranchInverseRealSL (p : ℕ) (i : Option (Fin p)) : 𝒮ℒ :=
  ⟨Matrix.SpecialLinearGroup.mapGL ℝ (lpsOriginalPrimeBranchSL p i)⁻¹,⟨_,rfl⟩⟩

def lpsOriginalPrimeBranchHolomorphic (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) : LPSOriginalHolomorphicRing :=
  lpsOriginalHolomorphicPullback (lpsOriginalPrimeBranchInverseRealSL p i)
    (lpsOriginalJNHolomorphic p (Fact.out : p.Prime).pos)

lemma lpsOriginalPrimeBranchHolomorphic_apply (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    (lpsOriginalPrimeBranchHolomorphic p i).val τ=lpsOriginalPrimeBranch p i τ := by
  change lpsOriginalJDilated p (Fact.out : p.Prime).pos
    ((Matrix.SpecialLinearGroup.mapGL ℝ (lpsOriginalPrimeBranchSL p i)⁻¹)⁻¹ • τ)=_
  rw [← map_inv,inv_inv,← lpsOriginalIntegralSLAction_eq]
  exact lpsOriginalPrimeBranchSL_function p i τ

lemma lpsOriginalPrimeBranchSL_lower_left (p : ℕ) (i j : Option (Fin p)) :
    (lpsOriginalPrimeBranchSL p i * (lpsOriginalPrimeBranchSL p j)⁻¹) 1 0=
      match i,j with
      | none,none => 0
      | none,some _ => -1
      | some _,none => 1
      | some m,some n => (n.val:ℤ)-(m.val:ℤ) := by
  cases i <;> cases j <;>
    simp [lpsOriginalPrimeBranchSL_none,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,lpsOriginalPrimeBranchSL_finite_matrix,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]

lemma lpsOriginalPrimeBranchSL_mem_iff (p : ℕ) [Fact p.Prime]
    (i j : Option (Fin p)) :
    lpsOriginalPrimeBranchSL p i * (lpsOriginalPrimeBranchSL p j)⁻¹ ∈
      CongruenceSubgroup.Gamma0 p ↔ i=j := by
  rw [CongruenceSubgroup.Gamma0_mem,lpsOriginalPrimeBranchSL_lower_left]
  cases i with
  | none => cases j <;> simp
  | some m =>
    cases j with
    | none => simp
    | some n =>
      simp only [Int.cast_sub,Int.cast_natCast,Option.some.injEq,sub_eq_zero]
      constructor
      · intro he
        apply Fin.ext
        have hv:=congrArg ZMod.val he
        simpa only [ZMod.val_natCast_of_lt m.isLt,ZMod.val_natCast_of_lt n.isLt]
          using hv.symm
      · rintro rfl
        rfl

lemma lpsOriginalPrimeBranchHolomorphic_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalPrimeBranchHolomorphic p) := by
  intro i j h
  have he (τ : ℍ) :
      lpsOriginalJDilated p (Fact.out : p.Prime).pos
        (lpsOriginalPrimeBranchSL p i • τ)=
      lpsOriginalJDilated p (Fact.out : p.Prime).pos
        (lpsOriginalPrimeBranchSL p j • τ) := by
    simpa only [lpsOriginalPrimeBranchSL_function,lpsOriginalPrimeBranchHolomorphic_apply]
      using congrArg (fun f : LPSOriginalHolomorphicRing => f.val τ) h
  apply (lpsOriginalPrimeBranchSL_mem_iff p i j).mp
  apply (lpsOriginalJDilatedExactStabilizer p (Fact.out : p.Prime).pos _).mp
  intro τ
  simpa only [mul_smul,smul_inv_smul] using
    he ((lpsOriginalPrimeBranchSL p j)⁻¹ • τ)

lemma lpsOriginalPrimeIntegerPolynomial_branchRoot (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalPrimeBranch p i τ)=0 := by
  have h:=lpsOriginalIntegerPolynomial_root p (Fact.out : p.Prime).pos
    (lpsOriginalPrimeBranchSL p i • τ)
  rw [lpsOriginalJInvariant_integralSL,lpsOriginalPrimeBranchSL_function] at h
  exact h

lemma lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      lpsOriginalJHolomorphicEvalZ (lpsOriginalPrimeBranchHolomorphic p i)=0 := by
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalZ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ (P.map (algebraMap ℤ ℚ))).val τ=
      (P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [lpsOriginalJHolomorphicEvalQ_apply,Polynomial.eval_map,Polynomial.eval₂_map]
    congr 1
  have h := Polynomial.hom_eval₂ (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos)
    lpsOriginalJHolomorphicEvalZ e (lpsOriginalPrimeBranchHolomorphic p i)
  rw [hc] at h
  have hb : e (lpsOriginalPrimeBranchHolomorphic p i)=lpsOriginalPrimeBranch p i τ :=
    lpsOriginalPrimeBranchHolomorphic_apply p i τ
  rw [hb] at h
  exact h.trans (lpsOriginalPrimeIntegerPolynomial_branchRoot p i τ)

def lpsOriginalPrimeFractionBranch (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) : LPSOriginalHolomorphicFractionField :=
  algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
    (lpsOriginalPrimeBranchHolomorphic p i)

lemma lpsOriginalPrimeFractionBranch_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalPrimeFractionBranch p) :=
  (IsFractionRing.injective LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField).comp (lpsOriginalPrimeBranchHolomorphic_injective p)

lemma lpsOriginalPrimeIntegerPolynomial_fractionProduct (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ)=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalPrimeFractionBranch p i)) := by
  classical
  let f:=algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  let P:=(lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (f.comp lpsOriginalJHolomorphicEvalZ)
  have hP:P.Monic:=(lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _
  have hr (i : Option (Fin p)) : P.eval (lpsOriginalPrimeFractionBranch p i)=0 := by
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ (f.comp lpsOriginalJHolomorphicEvalZ)
      (f (lpsOriginalPrimeBranchHolomorphic p i))
      (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos)=0
    rw [← Polynomial.hom_eval₂,lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot,map_zero]
  have hd:P.natDegree=p+1 := by
    dsimp only [P]
    have hf : Function.Injective (f.comp lpsOriginalJHolomorphicEvalZ) := by
      intro P Q h
      exact lpsOriginalJHolomorphicEvalZ_injective
        ((IsFractionRing.injective LPSOriginalHolomorphicRing
          LPSOriginalHolomorphicFractionField) h)
    rw [Polynomial.natDegree_map_eq_of_injective hf,
      lpsOriginalPrimeIntegerPolynomial_degree]
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_X_sub_C (lpsOriginalPrimeFractionBranch p) Finset.univ) hP
  · exact Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C (lpsOriginalPrimeFractionBranch_injective p))
      (fun i=>Polynomial.dvd_iff_isRoot.mpr (hr i))
  · rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,hd]
    simp

lemma lpsOriginalPrimeIntegerPolynomial_holomorphicProduct (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map lpsOriginalJHolomorphicEvalZ=
      ∏ i : Option (Fin p),
        (Polynomial.X-Polynomial.C (lpsOriginalPrimeBranchHolomorphic p i)) := by
  classical
  apply Polynomial.map_injective
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
  rw [Polynomial.map_map,Polynomial.map_prod]
  simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    lpsOriginalPrimeFractionBranch] using lpsOriginalPrimeIntegerPolynomial_fractionProduct p

lemma lpsOriginalPrimeIntegerPolynomial_pointwiseProduct
    (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)))=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalPrimeBranch p i τ)) := by
  classical
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalZ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ (P.map (algebraMap ℤ ℚ))).val τ=
      (P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [lpsOriginalJHolomorphicEvalQ_apply,Polynomial.eval_map,Polynomial.eval₂_map]
    congr 1
  have h:=congrArg (Polynomial.map e) (lpsOriginalPrimeIntegerPolynomial_holomorphicProduct p)
  rw [Polynomial.map_map,hc,Polynomial.map_prod] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  have hb : e (lpsOriginalPrimeBranchHolomorphic p i)=lpsOriginalPrimeBranch p i τ :=
    lpsOriginalPrimeBranchHolomorphic_apply p i τ
  rw [hb]

end
end QEC.Coding.TannerLiftedProduct
