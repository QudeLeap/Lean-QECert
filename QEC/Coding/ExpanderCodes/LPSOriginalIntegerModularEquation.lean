import QEC.Coding.ExpanderCodes.LPSOriginalExactFunctionFieldDegree
import QEC.Coding.ExpanderCodes.LPSOriginalExactStabilizer
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerQExpansion
import QEC.Coding.ExpanderCodes.LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# LPSOriginalIntegerModularEquation

The SAME original j and jN satisfy a monic integer modular equation of the
actual Gamma0 coset degree, at every positive level including 16*q^2.
Exact rational field degree identifies the genuine inverse-coset product.
Integral Bezout reduction, rational root-of-unity cusp phases, true Taylor
expansions and triangular coefficient recovery prove integer coefficients.
Both polynomial layers are lifted faithfully and their original root law is
proved. The final theorem assumes no equation, integrality, degree or model.

This internal closure follows the original modular-equation route motivated
by pinned PK22 ex:Xpq/th:qLDPC. ALL compact meromorphic-field identification,
canonical proper arithmetic models, uniform good reduction, geometric
Hecke/Frobenius/Weil and the unconditional PK22 main theorem remain subsequent
mathematics. No public theorem or source claim is registered here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

/-- Exact rational minimal-polynomial degree from the proved SAME generated-field degree. -/
lemma lpsOriginalJNMinpolyDegreeQ (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (minpoly (FractionRing (Polynomial ℚ))
      (lpsOriginalJNInFractionField N hN)).natDegree =
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integralQ N hN)]
  exact lpsOriginalGeneratedFunctionFieldQ_finrank_eq N hN

/-- Uniqueness of a monic rational annihilator within the actual coset degree. -/
lemma lpsOriginalJNMonicAnnihilatorUniqueQ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ P : Polynomial (FractionRing (Polynomial ℚ)), P.Monic →
      P.natDegree ≤ Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) →
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P = 0 →
      P = minpoly (FractionRing (Polynomial ℚ))
        (lpsOriginalJNInFractionField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro P hP hd he
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (lpsOriginalJNInFractionField_integralQ N hN)) hP
    (minpoly.dvd (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) he)
  rw [lpsOriginalJNMinpolyDegreeQ N hN]
  exact hd

/-- The actual rational minimal polynomial becomes the complete genuine inverse-coset product. -/
lemma lpsOriginalJNMinpolyCosetProductQ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)).map
        lpsOriginalJFractionEmbeddingQ =
      ∏ x : (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
        (Polynomial.X - Polynomial.C (lpsOriginalCosetFractionRoot N hN x)) := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let Q := minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)
  let P := Q.map lpsOriginalJFractionEmbeddingQ
  have hP : P.Monic := (minpoly.monic (lpsOriginalJNInFractionField_integralQ N hN)).map _
  have hroot : ∀ x : (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
      P.eval (lpsOriginalCosetFractionRoot N hN x) = 0 := by
    intro x
    dsimp only [P]
    rw [Polynomial.eval_map]
    change Polynomial.aeval
      (lpsOriginalFractionPullbackQ x.out (lpsOriginalJNInFractionField N hN)) Q = 0
    exact lpsOriginalFractionPullback_minpolyRootQ N hN x.out
  have hd : P.natDegree = Fintype.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [Polynomial.natDegree_map]
    exact (lpsOriginalJNMinpolyDegreeQ N hN).trans Nat.card_eq_fintype_card
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_X_sub_C (lpsOriginalCosetFractionRoot N hN) Finset.univ) hP
  · exact Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C (lpsOriginalCosetFractionRoot_injective N hN))
      (fun x => Polynomial.dvd_iff_isRoot.mpr (hroot x))
  · rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, hd]




/-- Actual pointwise rational relation descends to an annihilator in the ambient fraction field. -/
lemma lpsOriginalRationalRelation_fractionRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval (lpsOriginalJNInFractionField N hN)
      (Φ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))=0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [Polynomial.aeval_def,Polynomial.eval₂_map]
  have hc : (algebraMap (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField).comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalQ := by
    apply RingHom.ext
    intro Q
    exact lpsOriginalJFractionEmbeddingQ_polynomial Q
  rw [hc]
  have hzero : Φ.eval₂ lpsOriginalJHolomorphicEvalQ
      (lpsOriginalJNHolomorphic N hN)=0 := by
    apply Subtype.ext
    funext τ
    let e : LPSOriginalHolomorphicRing →+* ℂ :=
      { toFun f := f.val τ
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl }
    have hj : e.comp lpsOriginalJHolomorphicEvalQ=
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) := by
      apply RingHom.ext
      intro Q
      change (lpsOriginalJHolomorphicEvalQ Q).val τ=
        (Q.map (algebraMap ℚ ℂ)).eval (lpsOriginalJInvariant τ)
      rw [Polynomial.eval_map]
      exact lpsOriginalJHolomorphicEvalQ_apply Q τ
    have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEvalQ e
      (lpsOriginalJNHolomorphic N hN)
    rw [hj] at h
    exact h.trans (hroot τ)
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEvalQ
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic N hN)
  rw [hzero,map_zero] at h
  exact h.symm

/-- Faithful localization identifies the actual rational relation with the complete holomorphic coset product. -/
lemma lpsOriginalRationalRelation_holomorphicProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hdeg : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0) :
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    Φ.map lpsOriginalJHolomorphicEvalQ =
      ∏ x : (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
        (Polynomial.X-Polynomial.C
          (lpsOriginalHolomorphicPullback x.out (lpsOriginalJNHolomorphic N hN))) := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  have hm := lpsOriginalJNMonicAnnihilatorUniqueQ N hN
    (Φ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
    (hΦ.map _) (Polynomial.natDegree_map_le.trans hdeg.le)
    (lpsOriginalRationalRelation_fractionRoot N hN Φ hroot)
  have hc : lpsOriginalJFractionEmbeddingQ.comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalQ := by
    apply RingHom.ext
    intro P
    exact lpsOriginalJFractionEmbeddingQ_polynomial P
  have h := congrArg (Polynomial.map lpsOriginalJFractionEmbeddingQ) hm
  rw [Polynomial.map_map,hc,
    lpsOriginalJNMinpolyCosetProductQ N hN] at h
  apply Polynomial.map_injective
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
  rw [Polynomial.map_map,Polynomial.map_prod]
  convert h using 1
  apply Finset.prod_congr rfl
  intro x _hx
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    lpsOriginalCosetFractionRoot,lpsOriginalJNInFractionField,
    lpsOriginalFractionPullbackRing_localization]

/-- Pointwise polynomial identity with every genuine inverse left-coset branch. -/
lemma lpsOriginalRationalRelation_pointwiseProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hdeg : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0)
    (τ : ℍ) :
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
      ∏ x : (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
        (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalQ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ P).val τ=
      (P.map (algebraMap ℚ ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.eval_map]
    exact lpsOriginalJHolomorphicEvalQ_apply P τ
  have h := congrArg (Polynomial.map e)
    (lpsOriginalRationalRelation_holomorphicProduct N hN Φ hΦ hdeg hroot)
  rw [Polynomial.map_map,hc,Polynomial.map_prod] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro x _hx
  rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  rfl

/-- Existence of the actual rational monic polynomial with complete coset-product identity. -/
lemma lpsOriginalJ_jN_rational_coset_product
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    ∃ Φ : Polynomial (Polynomial ℚ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
        ∏ x : (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
          (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))) := by
  obtain ⟨Φ,hΦ,hd,hr⟩ := lpsOriginalJ_jN_rational_monic_relation N hN
  exact ⟨Φ,hΦ,hd,lpsOriginalRationalRelation_pointwiseProduct N hN Φ hΦ hd hr⟩


/-- Integral Bezout matrix reduction proves a rational affine cusp shift for the SAME original branch. -/
lemma lpsOriginalDilatedAtScaledCuspRational (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    ∃ r : ℚ, ∀ σ : ℍ,
      lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant
          (lpsE2AffineMatrix ((Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0))^2)
            (pow_pos (lpsOriginalDilationColumnGcdPos N hN γ) 2) (r:ℝ) • σ) := by
  let g : ℕ := Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)
  have hg : 0<g := lpsOriginalDilationColumnGcdPos N hN γ
  obtain ⟨a,c,hcop,ha,hc⟩ := Int.exists_gcd_one hg
  let δ := lpsE2IntegerPrimitiveColumn a c hcop
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix N hN 0*Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdetM : M.det.val=(N:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix N hN 0).det.val := by simp [M]
         _=(N:ℝ) := lpsE2AffineMatrix_det N hN 0
  have hM00 : M 0 0=((N:ℤ)*γ 0 0:ℤ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hM10 : M 1 0=(γ 1 0:ℝ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hA : (δ 0 0:ℝ)*(g:ℝ)=M 0 0 := by
    rw [hM00]
    change (a:ℝ)*(g:ℝ)=(((N:ℤ)*γ 0 0:ℤ):ℝ)
    exact_mod_cast ha.symm
  have hC : (δ 1 0:ℝ)*(g:ℝ)=M 1 0 := by
    rw [hM10]
    change (c:ℝ)*(g:ℝ)=(γ 1 0:ℝ)
    exact_mod_cast hc.symm
  let h : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹*M
  have hdδ : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have he : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast he
  have hh10 : h 1 0=0 := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 1 0=0
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    ring
  have hh00 : h 0 0=(g:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 0=(g:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    linear_combination (g:ℝ)*hdδ
  have hhdet : h.det.val=(N:ℝ) := by simp [h,hdetM]
  have hgR : (g:ℝ)≠0 := by exact_mod_cast hg.ne'
  have hh11 : h 1 1=(N:ℝ)/(g:ℝ) := by
    apply (eq_div_iff hgR).2
    have he := hhdet
    change Matrix.det (h:Matrix (Fin 2) (Fin 2) ℝ)=(N:ℝ) at he
    simpa only [Matrix.det_fin_two,hh00,hh10,mul_zero,zero_mul,sub_zero,mul_comm] using he
  let b : ℤ := δ 1 1*((N:ℤ)*γ 0 1)-δ 0 1*γ 1 1
  have hh01 : h 0 1=(b:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 1=(b:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [M,b,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,
      Matrix.vecHead,Matrix.vecTail,sub_eq_add_neg]
  let r : ℚ := (b:ℚ)*(g:ℚ)/(N:ℚ)
  have hr : (r:ℝ)=h 0 1*(g:ℝ)/(N:ℝ) := by
    rw [hh01]
    simp only [r,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_natCast]
  refine ⟨r,?_⟩
  intro σ
  have hp : 0<h.det.val := by rw [hhdet];exact_mod_cast hN
  have he : h • (lpsE2AffineMatrix N hN 0 • σ)=
      lpsE2AffineMatrix (g^2) (pow_pos hg 2) (r:ℝ) • σ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hp,lpsE2AffineMatrix_action,
      UpperHalfPlane.num,UpperHalfPlane.denom,hh00,hh10,hh11,lpsE2AffineMatrix_action]
    simp only [Complex.ofReal_div,Complex.ofReal_zero,Complex.ofReal_natCast,zero_mul,
      zero_add,add_zero,Nat.cast_pow]
    have hgC : (g:ℂ)≠0 := by exact_mod_cast hg.ne'
    have hNC : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
    rw [hr]
    change ((g:ℂ)*((N:ℂ)*(σ:ℂ))+(h 0 1:ℂ))/((N:ℂ)/(g:ℂ))=
      (g:ℂ)^2*(σ:ℂ)+(h 0 1*(g:ℝ)/(N:ℝ):ℝ)
    push_cast
    field_simp [hgC,hNC]
  have hm : M=Matrix.SpecialLinearGroup.mapGL ℝ δ*h := by simp [h]
  have hγ : ∀ τ : ℍ, γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map,Matrix.of_apply]
  calc
    lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (M • (lpsE2AffineMatrix N hN 0 • σ)) := by
      simp only [lpsOriginalJDilated,M,mul_smul,hγ]
    _=lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ δ •
        (h • (lpsE2AffineMatrix N hN 0 • σ))) := by rw [hm,mul_smul]
    _=lpsOriginalJInvariant (h • (lpsE2AffineMatrix N hN 0 • σ)) :=
      lpsOriginalJInvariant_SL_invariant _ ⟨δ,rfl⟩ _
    _=_ := by rw [he]

/-- Every actual integral SL branch has a positive affine slope at most N squared and a rational shift. -/
lemma lpsOriginalSLAtScaledCuspRational (N : ℕ) (hN : 0<N) (g : 𝒮ℒ) :
    ∃ m : ℕ, ∃ hm : 0<m, ∃ r : ℚ, m≤N^2 ∧ ∀ σ : ℍ,
      lpsOriginalJDilated N hN (g.val • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • σ) := by
  obtain ⟨γ,hγ⟩ := g.property
  have ha : ∀ τ : ℍ,γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map,Matrix.of_apply]
  obtain ⟨r,hr⟩ := lpsOriginalDilatedAtScaledCuspRational N hN γ
  have hg := lpsOriginalDilationColumnGcdPos N hN γ
  have hle := Nat.le_of_dvd hN (lpsOriginalDilationColumnGcdDvd N γ)
  refine ⟨_,pow_pos hg 2,r,by nlinarith,?_⟩
  intro σ
  rw [←hγ,←ha]
  exact hr σ


/-- Actual analytic Taylor expansion respects constant rescaling. -/
lemma lpsOriginalTaylorSeries_comp_const_mul
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    lpsOriginalTaylorSeries (fun q => f (c*q)) =
      PowerSeries.rescale c (lpsOriginalTaylorSeries f) := by
  let S := PowerSeries.rescale c (lpsOriginalTaylorSeries f)
  have ht : Tendsto (fun q : ℂ => c*q) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds (x := c)).mul (tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 0) (𝓝 0))
  have he := hasFPowerSeriesAt_iff.mp hf.hasFPowerSeriesAt
  have hex : HasFPowerSeriesAt (fun q : ℂ => f (c*q))
      (FormalMultilinearSeries.ofScalars ℂ (fun n => S.coeff n)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ht.eventually he] with q hq
    simp only [zero_add, FormalMultilinearSeries.coeff_ofScalars] at hq ⊢
    convert hq using 1
    funext n
    simp only [S, PowerSeries.coeff_rescale, lpsOriginalTaylorSeries_coeff,
      smul_eq_mul]
    ring
  have h := hex.eq_formalMultilinearSeries hex.analyticAt.hasFPowerSeriesAt
  ext n
  have heq := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  simpa only [FormalMultilinearSeries.coeff_ofScalars, lpsOriginalTaylorSeries_coeff,
    div_eq_mul_inv, mul_comm] using heq.symm

/-- The rational nome phase is an actual root of unity and hence an algebraic integer. -/
lemma lpsOriginalRationalNomePhase_integral (r : ℚ) :
    IsIntegral ℤ (Function.Periodic.qParam 1 (r : ℂ)) := by
  change IsIntegral ℤ (Complex.exp (2*Real.pi*I*(r : ℂ)/1))
  rw [div_one]
  exact (Complex.isPrimitiveRoot_exp_rat r).isIntegral r.den_pos

/-- Every coefficient of the actual phase-rescaled integer j series is an algebraic integer. -/
lemma lpsOriginalPhaseKSeries_coeff_integral (r : ℚ) (n : ℕ) :
    IsIntegral ℤ ((PowerSeries.rescale (Function.Periodic.qParam 1 (r : ℂ))
      (PowerSeries.map (algebraMap ℤ ℂ) lpsOriginalJZSeries)).coeff n) := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
  exact ((lpsOriginalRationalNomePhase_integral r).pow n).mul
    (isIntegral_algebraMap (R := ℤ) (A := ℂ))

/-- Actual Taylor coefficients of the positive-power affine j numerator are algebraic integers. -/
lemma lpsOriginalAffineKSeries_coeff_integral
    (r : ℚ) (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    IsIntegral ℤ ((lpsOriginalTaylorSeries
      (fun q : ℂ => lpsOriginalJQCoefficient
        (Function.Periodic.qParam 1 (r : ℂ)*q^m))).coeff n) := by
  have hf : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r : ℂ)*q)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq (by fun_prop) (by simp)
  rw [lpsOriginalTaylorSeries_comp_pow hf m hm,
    lpsOriginalTaylorSeries_comp_const_mul lpsOriginalJQCoefficient_analytic_zero,
    ← lpsOriginalJZSeries_mapC]
  by_cases hn : m ∣ n
  · obtain ⟨k,rfl⟩ := hn
    rw [PowerSeries.coeff_expand_mul]
    exact lpsOriginalPhaseKSeries_coeff_integral r k
  · rw [PowerSeries.coeff_expand_of_not_dvd m hm _ hn]
    exact isIntegral_zero


/-- The inverse rational nome phase is an algebraic integer via the opposite rational phase. -/
lemma lpsOriginalRationalNomePhase_inv_integral (r : ℚ) :
    IsIntegral ℤ ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) := by
  have he : Function.Periodic.qParam 1 ((-r:ℚ):ℂ)=
      (Function.Periodic.qParam 1 (r:ℂ))⁻¹ := by
    simp only [Function.Periodic.qParam,Rat.cast_neg,Complex.ofReal_one,div_one,
      mul_neg,Complex.exp_neg]
  rw [←he]
  exact lpsOriginalRationalNomePhase_integral (-r)

/-- Concrete analytic affine cusp numerator obtained by clearing a bounded actual pole. -/
def lpsOriginalClearedAffineCusp (B m : ℕ) (r : ℚ) (q : ℂ) : ℂ :=
  q^(B-m)/Function.Periodic.qParam 1 (r:ℂ)*
    lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (r:ℂ)*q^m)

/-- The actual cleared affine cusp function is analytic at zero. -/
lemma lpsOriginalClearedAffineCusp_analytic (B m : ℕ) (hm : m≠0) (r : ℚ) :
    AnalyticAt ℂ (lpsOriginalClearedAffineCusp B m r) 0 := by
  have hf : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q^m)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (analyticAt_const.mul (lpsOriginalPower_analytic m)) (by simp [hm])
  exact ((lpsOriginalPower_analytic _).div_const).mul hf

/-- Exact Taylor identity for the actual cleared affine cusp function. -/
lemma lpsOriginalClearedAffineCusp_taylor (B m : ℕ) (hm : m≠0) (r : ℚ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B m r)=
      PowerSeries.C ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) *
        (PowerSeries.X^(B-m)*lpsOriginalTaylorSeries
          (fun q : ℂ=>lpsOriginalJQCoefficient
            (Function.Periodic.qParam 1 (r:ℂ)*q^m))) := by
  have hf : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q^m)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (analyticAt_const.mul (lpsOriginalPower_analytic m)) (by simp [hm])
  have he : lpsOriginalClearedAffineCusp B m r=
      fun q : ℂ=>(Function.Periodic.qParam 1 (r:ℂ))⁻¹ *
        (q^(B-m)*lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (r:ℂ)*q^m)) := by
    funext q
    dsimp only [lpsOriginalClearedAffineCusp]
    ring
  rw [he,lpsOriginalTaylorSeries_const_mul]
  change PowerSeries.C _ * lpsOriginalTaylorSeries
    ((fun q : ℂ=>q^(B-m)) * (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q^m))) = _
  rw [lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic _) hf,
    lpsOriginalTaylorSeries_qpow]

/-- Every actual cleared affine cusp Taylor coefficient is an algebraic integer. -/
lemma lpsOriginalClearedAffineCusp_integral_coeff
    (B m : ℕ) (hm : m≠0) (r : ℚ) (n : ℕ) :
    IsIntegral ℤ ((lpsOriginalTaylorSeries
      (lpsOriginalClearedAffineCusp B m r)).coeff n) := by
  rw [lpsOriginalClearedAffineCusp_taylor B m hm r,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  split_ifs
  · exact (lpsOriginalRationalNomePhase_inv_integral r).mul
      (lpsOriginalAffineKSeries_coeff_integral r m hm _)
  · rw [mul_zero]
    exact isIntegral_zero

/-- True nome pullback of the cleared affine function equals the original affine j branch times the pole weight. -/
lemma lpsOriginalClearedAffineCusp_pullback
    (B m : ℕ) (hm : 0<m) (hmB : m≤B) (r : ℚ) (σ : ℍ) :
    lpsOriginalClearedAffineCusp B m r
        (Function.Periodic.qParam 1 (σ:ℂ))=
      Function.Periodic.qParam 1 (σ:ℂ)^B *
        lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • σ) := by
  rw [lpsOriginalAffinePolePullback m B hm hmB (r:ℝ) σ,lpsOriginalAffineNome]
  simp only [lpsOriginalClearedAffineCusp,Complex.ofReal_ratCast,mul_comm]


/-- Finite convolution preserves coefficientwise algebraic integrality of actual power series. -/
lemma lpsOriginalIntegralSeries_mul (A B : PowerSeries ℂ)
    (hA : ∀ n, IsIntegral ℤ (A.coeff n))
    (hB : ∀ n, IsIntegral ℤ (B.coeff n)) (n : ℕ) :
    IsIntegral ℤ ((A*B).coeff n) := by
  rw [PowerSeries.coeff_mul]
  exact IsIntegral.sum _ (fun i _ => (hA i.1).mul (hB i.2))

/-- Every actual power of a coefficientwise integral series remains coefficientwise integral. -/
lemma lpsOriginalIntegralSeries_pow (K : PowerSeries ℂ)
    (hK : ∀ n, IsIntegral ℤ (K.coeff n)) (i n : ℕ) :
    IsIntegral ℤ ((K^i).coeff n) := by
  induction i generalizing n with
  | zero =>
      simp only [pow_zero,PowerSeries.coeff_one]
      split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  | succ i hi =>
      rw [pow_succ]
      exact lpsOriginalIntegralSeries_mul (K^i) K hi hK n

/-- Actual polynomial cusp-clearing series with triangular pole orders. -/
def lpsOriginalClearedUnivariateSeries
    (N D : ℕ) (K : PowerSeries ℂ) (p : Polynomial ℂ) : PowerSeries ℂ :=
  ∑ i ∈ Finset.range (D+1),
    PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i

/-- Exact coefficient formula for each actual cusp-clearing summand. -/
lemma lpsOriginalClearedUnivariateTerm_coeff
    (N D : ℕ) (K : PowerSeries ℂ) (p : Polynomial ℂ) (i t : ℕ) :
    (PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i).coeff t =
      p.coeff i * if N*(D-i)≤t then (K^i).coeff (t-N*(D-i)) else 0 := by
  rw [mul_assoc,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']

/-- Descending triangular coefficient recovery proves polynomial coefficients integral from the actual cleared series. -/
lemma lpsOriginalClearedUnivariateSeries_integral_coeff
    (N D : ℕ) (hN : 0<N) (K : PowerSeries ℂ) (p : Polynomial ℂ)
    (hd : p.natDegree≤D) (hK0 : K.constantCoeff=1)
    (hK : ∀ n, IsIntegral ℤ (K.coeff n))
    (hc : ∀ n, IsIntegral ℤ
      ((lpsOriginalClearedUnivariateSeries N D K p).coeff n)) :
    ∀ n, IsIntegral ℤ (p.coeff n) := by
  classical
  have hind : ∀ k : ℕ, ∀ n : ℕ, n≤D → D-n=k → IsIntegral ℤ (p.coeff n) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hn hk
      let S := (Finset.range (D+1)).erase n
      let t := N*(D-n)
      let f := fun i : ℕ =>
        (PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i).coeff t
      have hf : ∀ i∈S, IsIntegral ℤ (f i) := by
        intro i hi
        have hiD : i≤D := by
          have := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
          omega
        have hin : i≠n := (Finset.mem_erase.mp hi).1
        dsimp only [f]
        rw [lpsOriginalClearedUnivariateTerm_coeff]
        by_cases hit : i<n
        · have he : ¬N*(D-i)≤t := by
            dsimp only [t]
            exact not_le_of_gt (Nat.mul_lt_mul_of_pos_left (by omega : D-n<D-i) hN)
          rw [if_neg he,mul_zero]
          exact isIntegral_zero
        · have hni : n < i := by omega
          have hp := ih (D-i) (by omega) i hiD rfl
          split_ifs
          · exact hp.mul (lpsOriginalIntegralSeries_pow K hK i _)
          · simpa only [mul_zero] using (isIntegral_zero : IsIntegral ℤ (0:ℂ))
      have hsum : IsIntegral ℤ (∑ i∈S, f i) := IsIntegral.sum f hf
      have hfn : f n=p.coeff n := by
        dsimp only [f,t]
        rw [lpsOriginalClearedUnivariateTerm_coeff,if_pos le_rfl,Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow,hK0,one_pow,mul_one]
      have he : (lpsOriginalClearedUnivariateSeries N D K p).coeff t =
          (∑ i∈S, f i)+p.coeff n := by
        rw [lpsOriginalClearedUnivariateSeries,map_sum]
        exact (Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega))).symm.trans
          (congrArg ((∑ i∈S, f i)+ ·) hfn)
      have h := (hc t).sub hsum
      rw [he,add_sub_cancel_left] at h
      exact h
  intro n
  by_cases hn : n≤D
  · exact hind (D-n) n hn rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree<n)]
    exact isIntegral_zero

/-- A rational algebraic integer in the faithful complex embedding is an actual integer. -/
lemma lpsOriginalRationalIntegral_isInteger (a : ℚ)
    (ha : IsIntegral ℤ (a:ℂ)) : ∃ z : ℤ, (z:ℚ)=a := by
  have hq : IsIntegral ℤ a :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp ha
  simpa only [algebraMap_int_eq,Int.coe_castRingHom] using
    (IsIntegrallyClosed.isIntegral_iff.mp hq)


/-- Actual subring of complex functions analytic at zero, with all ring closure proofs. -/
def lpsOriginalCuspAnalyticSubring : Subring (ℂ→ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' hf hg := hf.add hg
  neg_mem' hf := hf.neg
  mul_mem' hf hg := hf.mul hg

/-- Actual Taylor ring homomorphism on the analytic subring. -/
def lpsOriginalCuspTaylorRingHom :
    lpsOriginalCuspAnalyticSubring →+* PowerSeries ℂ where
  toFun f := lpsOriginalTaylorSeries f.val
  map_zero' := lpsOriginalTaylorSeries_zero
  map_one' := lpsOriginalTaylorSeries_one
  map_add' f g := lpsOriginalTaylorSeries_add f.property g.property
  map_mul' f g := lpsOriginalTaylorSeries_mul f.property g.property

/-- Actual evaluation ring homomorphism on the analytic subring. -/
def lpsOriginalCuspEvaluateRingHom (q : ℂ) :
    lpsOriginalCuspAnalyticSubring →+* ℂ where
  toFun f := f.val q
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Every polynomial and Taylor coefficient of an actual finite root product is integral, via the integral closure subring. -/
lemma lpsOriginalIntegralCosetProduct_coeff {ι : Type*}
    (s : Finset ι) (f : ι→PowerSeries ℂ)
    (hf : ∀ i∈s, ∀ n, IsIntegral ℤ ((f i).coeff n)) (k n : ℕ) :
    IsIntegral ℤ (((∏ i∈s, (Polynomial.X-Polynomial.C (f i))).coeff k).coeff n) := by
  classical
  let T : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  let A : ι→PowerSeries T := fun i =>
    if hi : i∈s then (f i).toSubring T (hf i hi) else 0
  have hA : ∀ i∈s, (A i).map T.subtype=f i := by
    intro i hi
    simp only [A,dif_pos hi]
    ext n
    simp [PowerSeries.toSubring,PowerSeries.coeff_map]
  have he : ∏ i∈s, (Polynomial.X-Polynomial.C (f i))=
      (∏ i∈s, (Polynomial.X-Polynomial.C (A i))).map (PowerSeries.map T.subtype) := by
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,hA i hi]
  rw [he,Polynomial.coeff_map,PowerSeries.coeff_map]
  exact (((∏ i∈s, (Polynomial.X-Polynomial.C (A i))).coeff k).coeff n).property

/-- Actual scaleRoots identity for the finite product of linear root factors. -/
lemma lpsOriginalScaleRootsCosetProduct {ι : Type*}
    (s : Finset ι) (f : ι→ℂ) (r : ℂ) :
    (∏ i∈s, (Polynomial.X-Polynomial.C (f i))).scaleRoots r=
      ∏ i∈s, (Polynomial.X-Polynomial.C (f i*r)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      Polynomial.mul_scaleRoots_of_noZeroDivisors,Polynomial.X_sub_C_scaleRoots,ih]

/-- Actual Taylor expansion respects subtraction of analytic functions. -/
lemma lpsOriginalTaylorSeries_sub {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    lpsOriginalTaylorSeries (f-g)=lpsOriginalTaylorSeries f-lpsOriginalTaylorSeries g := by
  ext n
  simp only [lpsOriginalTaylorSeries_coeff,map_sub,
    iteratedDeriv_sub hf.contDiffAt hg.contDiffAt,mul_sub]

/-- Equal analytic germs have equal actual Taylor series. -/
lemma lpsOriginalTaylorSeries_eq_of_germ {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : f=ᶠ[nhds 0]g) : lpsOriginalTaylorSeries f=lpsOriginalTaylorSeries g := by
  have hz : f-g=ᶠ[nhds 0](0:ℂ→ℂ) := by
    filter_upwards [hfg] with q hq
    simp only [Pi.sub_apply,hq,sub_self,Pi.zero_apply]
  have h := (lpsOriginalTaylorSeries_zero_iff_germ (hf.sub hg)).mpr hz
  rw [lpsOriginalTaylorSeries_sub hf hg] at h
  exact sub_eq_zero.mp h



/-- Concrete polynomial cusp-clearing function for the SAME actual j numerator. -/
def lpsOriginalClearedUnivariateCusp
    (N D : ℕ) (p : Polynomial ℂ) : ℂ→ℂ :=
  ∑ i∈Finset.range (D+1), fun q : ℂ =>
    p.coeff i*q^(N*(D-i))*lpsOriginalJQCoefficient (q^N)^i

/-- Analyticity of the actual polynomial cusp-clearing function. -/
lemma lpsOriginalClearedUnivariateCusp_analytic
    (N D : ℕ) (hN : N≠0) (p : Polynomial ℂ) :
    AnalyticAt ℂ (lpsOriginalClearedUnivariateCusp N D p) 0 := by
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  exact (Finset.range (D+1)).analyticAt_sum fun i _ =>
    (analyticAt_const.mul (lpsOriginalPower_analytic _)).mul (hKN.pow i)

/-- Exact Taylor identity of the actual polynomial cusp-clearing function. -/
lemma lpsOriginalClearedUnivariateCusp_taylor
    (N D : ℕ) (hN : N≠0) (p : Polynomial ℂ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedUnivariateCusp N D p)=
      lpsOriginalClearedUnivariateSeries N D
        (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))) p := by
  classical
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  rw [lpsOriginalClearedUnivariateCusp,lpsOriginalTaylorSeries_sum
    (Finset.range (D+1))
    (fun i=>fun q : ℂ=>p.coeff i*q^(N*(D-i))*lpsOriginalJQCoefficient (q^N)^i)
    (fun i _ => (analyticAt_const.mul (lpsOriginalPower_analytic _)).mul (hKN.pow i))]
  unfold lpsOriginalClearedUnivariateSeries
  apply Finset.sum_congr rfl
  intro i _hi
  change lpsOriginalTaylorSeries
    ((fun q : ℂ=>p.coeff i*q^(N*(D-i))) *
      ((fun q : ℂ=>lpsOriginalJQCoefficient (q^N))^i))=_
  have hf : AnalyticAt ℂ (fun q : ℂ=>p.coeff i*q^(N*(D-i))) 0 :=
    analyticAt_const.mul (lpsOriginalPower_analytic _)
  rw [lpsOriginalTaylorSeries_mul hf
      (hKN.pow i),lpsOriginalTaylorSeries_const_mul,lpsOriginalTaylorSeries_qpow,
      lpsOriginalTaylorSeries_pow hKN]

/-- True nome pullback evaluates the SAME polynomial at the original dilated j function. -/
lemma lpsOriginalClearedUnivariateCusp_pullback
    (N D : ℕ) (hN : 0<N) (p : Polynomial ℂ) (hd : p.natDegree≤D) (σ : ℍ) :
    lpsOriginalClearedUnivariateCusp N D p
        (Function.Periodic.qParam 1 (σ:ℂ))=
      Function.Periodic.qParam 1 (σ:ℂ)^(N*D) *
        p.eval (lpsOriginalJDilated N hN σ) := by
  classical
  rw [Polynomial.eval_eq_sum_range' (n:=D+1) (by omega),Finset.mul_sum]
  simp only [lpsOriginalClearedUnivariateCusp,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hiD : i≤D := by have := Finset.mem_range.mp hi;omega
  rw [←lpsOriginalJDilated_qParam_pullback N hN σ,mul_pow,←pow_mul]
  calc
    _=p.coeff i*Function.Periodic.qParam 1 (σ:ℂ)^(N*(D-i)+N*i)*
        lpsOriginalJDilated N hN σ^i := by rw [pow_add];ring
    _=_ := by rw [←Nat.mul_add,Nat.sub_add_cancel hiD];ring




/-- The actual complete rational coset product constructs an integral analytic cleared coefficient. -/
lemma lpsOriginalRationalCosetCoefficient_clearedCusp
    (N : ℕ) [NeZero N] (hN : 0<N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hd : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hp : letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
      ∀ τ : ℍ, Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
        ∏ x : (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
          (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))))
    (k : ℕ) :
    ∃ G : lpsOriginalCuspAnalyticSubring,
      (∀ n, IsIntegral ℤ ((lpsOriginalCuspTaylorRingHom G).coeff n)) ∧
      ∀ σ : ℍ, G.val (Function.Periodic.qParam 1 (σ:ℂ))=
        Function.Periodic.qParam 1 (σ:ℂ)^(N^2*(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)-k)) *
          ((Φ.coeff k).map (algebraMap ℚ ℂ)).eval (lpsOriginalJDilated N hN σ) := by
  classical
  let I := 𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ
  let := Fintype.ofFinite I
  choose m hm r hle hr using
    (fun x : I => lpsOriginalSLAtScaledCuspRational N hN x.out⁻¹)
  let A : I→lpsOriginalCuspAnalyticSubring := fun x =>
    ⟨lpsOriginalClearedAffineCusp (N^2) (m x) (r x),
      lpsOriginalClearedAffineCusp_analytic (N^2) (m x) (hm x).ne' (r x)⟩
  let S : Polynomial lpsOriginalCuspAnalyticSubring :=
    ∏ x : I, (Polynomial.X-Polynomial.C (A x))
  let G := S.coeff k
  refine ⟨G,?_,?_⟩
  · intro n
    change IsIntegral ℤ ((lpsOriginalCuspTaylorRingHom (S.coeff k)).coeff n)
    rw [←Polynomial.coeff_map]
    simp only [S,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    apply lpsOriginalIntegralCosetProduct_coeff
    intro x _hx j
    exact lpsOriginalClearedAffineCusp_integral_coeff
      (N^2) (m x) (hm x).ne' (r x) j
  · intro σ
    let q := Function.Periodic.qParam 1 (σ:ℂ)
    let τ := lpsE2AffineMatrix N hN 0 • σ
    let e := lpsOriginalCuspEvaluateRingHom q
    have ha : ∀ x : I, e (A x)=q^(N^2)*
        lpsOriginalJDilated N hN (x.out.val⁻¹•τ) := by
      intro x
      change lpsOriginalClearedAffineCusp (N^2) (m x) (r x) q=_
      rw [lpsOriginalClearedAffineCusp_pullback (N^2) (m x) (hm x) (hle x) (r x) σ]
      exact congrArg (q^(N^2)* ·) (hr x σ).symm
    let f := (Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ))
    have hdegree : (Φ.map f).natDegree=Nat.card I := by
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _
        (by rw [hΦ.leadingCoeff,map_one];exact one_ne_zero),hd]
    have hscale := congrArg (fun P : Polynomial ℂ => P.scaleRoots (q^(N^2))) (hp τ)
    rw [lpsOriginalScaleRootsCosetProduct] at hscale
    have hS : S.map e=(Φ.map f).scaleRoots (q^(N^2)) := by
      rw [hscale]
      simp only [S,Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro x _hx
      rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,ha]
      rw [mul_comm (q^(N^2))]
    have hc := congrArg (fun P : Polynomial ℂ=>P.coeff k) hS
    rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,hdegree,Polynomial.coeff_map] at hc
    change G.val q=((Φ.coeff k).map (algebraMap ℚ ℂ)).eval
      (lpsOriginalJInvariant τ)*(q^(N^2))^(Nat.card I-k) at hc
    rw [←pow_mul] at hc
    exact hc.trans (mul_comm _ _)



/-- True nome-germ comparison and triangular recovery prove every actual rational modular coefficient integral. -/
lemma lpsOriginalRationalCosetCoefficient_integral
    (N : ℕ) [NeZero N] (hN : 0<N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hd : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hp : letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
      ∀ τ : ℍ, Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
        ∏ x : (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
          (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))))
    (k n : ℕ) : IsIntegral ℤ (((Φ.coeff k).coeff n:ℚ):ℂ) := by
  classical
  let d := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let p := (Φ.coeff k).map (algebraMap ℚ ℂ)
  let D := p.natDegree+N^2*d
  let E := N*D-N^2*(d-k)
  have hD : p.natDegree≤D := Nat.le_add_right _ _
  have hE : N^2*(d-k)≤N*D := by
    calc N^2*(d-k)≤N^2*d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
         _≤D := Nat.le_add_left _ _
         _≤N*D := by nlinarith
  obtain ⟨G,hG,hNomeG⟩ :=
    lpsOriginalRationalCosetCoefficient_clearedCusp N hN Φ hΦ hd hp k
  let F := lpsOriginalClearedUnivariateCusp N D p
  let H : ℂ→ℂ := fun q=>q^E*G.val q
  have hF : AnalyticAt ℂ F 0 :=
    lpsOriginalClearedUnivariateCusp_analytic N D hN.ne' p
  have hH : AnalyticAt ℂ H 0 := (lpsOriginalPower_analytic E).mul G.property
  have hNome : ∀ σ : ℍ, F (Function.Periodic.qParam 1 (σ:ℂ))=
      H (Function.Periodic.qParam 1 (σ:ℂ)) := by
    intro σ
    dsimp only [F]
    rw [lpsOriginalClearedUnivariateCusp_pullback N D hN p hD σ]
    dsimp only [H]
    rw [hNomeG σ]
    rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hE]
  have hDisk : ∀ q : ℂ, ‖q‖<1 → q≠0 → F q=H q := by
    intro q hq hq0
    let σ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqσ : Function.Periodic.qParam 1 (σ:ℂ)=q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    simpa only [hqσ] using hNome σ
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖<1 :=
    (isOpen_lt (continuous_norm : Continuous (fun q : ℂ=>‖q‖)) continuous_const).mem_nhds
      (by norm_num : ‖(0:ℂ)‖<1)
  have hePunctured : F=ᶠ[𝓝[≠] (0:ℂ)]H := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
    exact hDisk q hq hq0
  have h0 : F 0=H 0 := tendsto_nhds_unique_of_eventuallyEq
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hePunctured
  have he : F=ᶠ[𝓝 0]H := by
    filter_upwards [hsmall] with q hq
    by_cases hq0 : q=0
    · subst q;exact h0
    · exact hDisk q hq hq0
  have hTaylor := lpsOriginalTaylorSeries_eq_of_germ hF hH he
  have hHT : lpsOriginalTaylorSeries H=PowerSeries.X^E*lpsOriginalCuspTaylorRingHom G := by
    change lpsOriginalTaylorSeries ((fun q : ℂ=>q^E)*G.val)=_
    rw [lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic E) G.property,
      lpsOriginalTaylorSeries_qpow]
    rfl
  have hc : ∀ t, IsIntegral ℤ ((lpsOriginalClearedUnivariateSeries N D
      (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))) p).coeff t) := by
    intro t
    rw [←lpsOriginalClearedUnivariateCusp_taylor N D hN.ne' p,hTaylor,hHT,
      PowerSeries.coeff_X_pow_mul']
    split_ifs
    · exact hG _
    · exact isIntegral_zero
  have hK0 : (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))).constantCoeff=1 := by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,lpsOriginalTaylorSeries_coeff]
    simp [hN.ne',lpsOriginalJQCoefficient_zero]
  have hK : ∀ t, IsIntegral ℤ ((lpsOriginalTaylorSeries
      (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))).coeff t) := by
    intro t
    have hphase : Function.Periodic.qParam 1 ((0:ℚ):ℂ)=1 := by
      simp [Function.Periodic.qParam]
    simpa only [hphase,one_mul] using
      lpsOriginalAffineKSeries_coeff_integral 0 N hN.ne' t
  have hall := lpsOriginalClearedUnivariateSeries_integral_coeff N D hN
    _ p hD hK0 hK hc
  simpa only [p,Polynomial.coeff_map,eq_ratCast] using hall n




/-- The complete original integer monic modular equation, at exact coset degree, for every positive composite or prime level. -/
lemma lpsOriginalJ_jN_integer_monic_relation
    (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Ψ : Polynomial (Polynomial ℤ), Ψ.Monic ∧
      Ψ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, Ψ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  classical
  obtain ⟨Φ,hΦ,hd,hr⟩ := lpsOriginalJ_jN_rational_monic_relation N hN
  have hp := lpsOriginalRationalRelation_pointwiseProduct N hN Φ hΦ hd hr
  have hLift : Φ ∈ Polynomial.lifts (Polynomial.mapRingHom (algebraMap ℤ ℚ)) := by
    apply (Polynomial.lifts_iff_coeff_lifts Φ).mpr
    intro k
    apply (Polynomial.mem_lifts (Φ.coeff k)).mp
    apply (Polynomial.lifts_iff_coeff_lifts (Φ.coeff k)).mpr
    intro n
    obtain ⟨z,hz⟩ := lpsOriginalRationalIntegral_isInteger ((Φ.coeff k).coeff n)
      (lpsOriginalRationalCosetCoefficient_integral N hN Φ hΦ hd hp k n)
    refine ⟨z,?_⟩
    change (z:ℚ)=(Φ.coeff k).coeff n
    exact hz
  obtain ⟨Ψ,hΨ⟩ := (Polynomial.mem_lifts Φ).mp hLift
  have hInt : Function.Injective (algebraMap ℤ ℚ) := by
    intro z w h
    change (z:ℚ)=(w:ℚ) at h
    exact_mod_cast h
  have hf : Function.Injective (Polynomial.mapRingHom (algebraMap ℤ ℚ)) :=
    Polynomial.map_injective _ hInt
  have hmonic : Ψ.Monic := Polynomial.monic_of_injective hf (by rw [hΨ];exact hΦ)
  have hdegree : Ψ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [←Polynomial.natDegree_map_eq_of_injective hf Ψ,hΨ,hd]
  refine ⟨Ψ,hmonic,hdegree,?_⟩
  intro τ
  have hc : (((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ))).comp
      (Polynomial.mapRingHom (algebraMap ℤ ℚ)))=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change ((P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).eval
      (lpsOriginalJInvariant τ)=(P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.map_map]
    have he : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)=Int.castRingHom ℂ := by
      apply RingHom.ext
      intro z
      simp only [RingHom.comp_apply,algebraMap_int_eq,Int.coe_castRingHom,map_intCast]
    rw [he]
  have h := hr τ
  rw [←hΨ,Polynomial.eval₂_map,hc] at h
  exact h


end
end QEC.Coding.TannerLiftedProduct
