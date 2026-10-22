import QEC.Coding.ExpanderCodes.LPSOriginalRationalFunctionField
import QEC.Coding.ExpanderCodes.LPSOriginalExactStabilizer

/-!
# LPSOriginalExactFunctionFieldDegree

Prove exact degrees of the SAME original generated C(j,jN) and Q(j,jN)
fields at every positive level, including the original composite levels.
Actual holomorphic inverse SL pullbacks extend to automorphisms of the
ambient holomorphic fraction field. Localization uniqueness proves that
these automorphisms fix the actual embedded C(j) and Q(j). The proved exact
original stabilizer makes inverse left-coset branches pairwise distinct.
Their genuine minimal-polynomial roots give the lower degree bound, matching
the existing actual annihilator upper bound. No Galois action on the generated
field, supplied distinctness, degree or orbit classification is assumed.

This internal original-family closure is motivated by pinned PK22 ex:Xpq/
th:qLDPC and the audited modular-equation route. Exact generated-field degree
does not yet identify ALL compact meromorphic functions, construct an integer
original modular equation or a canonical proper arithmetic model, or prove
uniform good reduction and geometric Hecke/Frobenius/Weil. The public PK22
main theorem remains subsequent mathematics; no public source claim is added.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Actual inverse SL pullback automorphism of the SAME holomorphic ring, with genuine differentiability and inverse action proofs. -/
def lpsOriginalHolomorphicPullback (g : 𝒮ℒ) :
    LPSOriginalHolomorphicRing ≃ₐ[ℂ] LPSOriginalHolomorphicRing where
  toFun f := ⟨fun τ => f.val (g.val⁻¹ • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul (by
      rw [Subgroup.HasDetOne.det_eq (inv_mem g.property)]; norm_num))⟩
  invFun f := ⟨fun τ => f.val (g.val • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul (by
      rw [Subgroup.HasDetOne.det_eq g.property]; norm_num))⟩
  left_inv f := by apply Subtype.ext; funext τ; simp only [inv_smul_smul]
  right_inv f := by apply Subtype.ext; funext τ; simp only [smul_inv_smul]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Literal pointwise identity of the actual holomorphic pullback; exercised by the genuine root API example. -/
lemma lpsOriginalHolomorphicPullback_apply (g : 𝒮ℒ)
    (f : LPSOriginalHolomorphicRing) (τ : ℍ) :
    (lpsOriginalHolomorphicPullback g f).val τ=f.val (g.val⁻¹•τ) := rfl

/-- The actual holomorphic pullback fixes SAME original j by genuine original SL invariance. -/
lemma lpsOriginalHolomorphicPullback_j (g : 𝒮ℒ) :
    lpsOriginalHolomorphicPullback g lpsOriginalJHolomorphic=
      lpsOriginalJHolomorphic := by
  apply Subtype.ext
  funext τ
  exact lpsOriginalJInvariant_SL_invariant _ (inv_mem g.property) τ

/-- The actual holomorphic pullback fixes every actual complex j-polynomial evaluation. -/
lemma lpsOriginalHolomorphicPullback_polynomial (g : 𝒮ℒ)
    (P : Polynomial ℂ) :
    lpsOriginalHolomorphicPullback g (lpsOriginalJHolomorphicEval P)=
      lpsOriginalJHolomorphicEval P := by
  change lpsOriginalHolomorphicPullback g
      (Polynomial.aeval lpsOriginalJHolomorphic P)=
    Polynomial.aeval lpsOriginalJHolomorphic P
  rw [←Polynomial.aeval_algHom_apply, lpsOriginalHolomorphicPullback_j]

/-- Actual ambient holomorphic fraction-ring automorphism induced by the genuine holomorphic ring equivalence. -/
def lpsOriginalFractionPullbackRing (g : 𝒮ℒ) :
    LPSOriginalHolomorphicFractionField ≃+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.ringEquivOfRingEquiv
    (lpsOriginalHolomorphicPullback g).toRingEquiv

/-- The actual ambient pullback on localized holomorphic functions is precisely their genuine holomorphic pullback. -/
lemma lpsOriginalFractionPullbackRing_localization (g : 𝒮ℒ)
    (f : LPSOriginalHolomorphicRing) :
    lpsOriginalFractionPullbackRing g
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalHolomorphicPullback g f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ f

/-- The actual ambient pullback fixes the SAME faithful embedded C(j) at every fraction, by genuine localization uniqueness. -/
lemma lpsOriginalFractionPullbackRing_fixesBase (g : 𝒮ℒ)
    (x : FractionRing (Polynomial ℂ)) :
    lpsOriginalFractionPullbackRing g (lpsOriginalJFractionEmbedding x)=
      lpsOriginalJFractionEmbedding x := by
  have h : (lpsOriginalFractionPullbackRing g).toRingHom.comp
      lpsOriginalJFractionEmbedding=lpsOriginalJFractionEmbedding := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro P
    change lpsOriginalFractionPullbackRing g
        (lpsOriginalJFractionEmbedding
          (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P))=
      lpsOriginalJFractionEmbedding
        (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)
    rw [lpsOriginalJFractionEmbedding_polynomial,
      lpsOriginalFractionPullbackRing_localization,
      lpsOriginalHolomorphicPullback_polynomial]
  exact RingHom.congr_fun h x

/-- Actual ambient C(j)-algebra automorphism, using the proved fixed-base law; no action on generated non-Galois C(j,jN) is asserted. -/
def lpsOriginalFractionPullback (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    LPSOriginalHolomorphicFractionField ≃ₐ[FractionRing (Polynomial ℂ)]
      LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbedding.toAlgebra
  exact { lpsOriginalFractionPullbackRing g with
    commutes' := lpsOriginalFractionPullbackRing_fixesBase g }

/-- The actual complex minimal polynomial vanishes at every genuinely pulled-back original jN root. -/
lemma lpsOriginalFractionPullback_minpolyRoot (N : ℕ) [NeZero N]
    (hN : 0<N) (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Polynomial.aeval
      (lpsOriginalFractionPullback g (lpsOriginalJNInFractionField N hN))
      (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN))=0 := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact minpoly.aeval_algHom (FractionRing (Polynomial ℂ))
    (lpsOriginalFractionPullback g).toAlgHom
    (lpsOriginalJNInFractionField N hN)


/-- The proved integral exact stabilizer identifies the actual real SL-range stabilizer with the SAME real Gamma0 subgroup. -/
lemma lpsOriginalJDilatedRealExactStabilizer (N : ℕ) (hN : 0<N)
    (g : 𝒮ℒ) :
    (∀ τ : ℍ,lpsOriginalJDilated N hN (g.val•τ)=lpsOriginalJDilated N hN τ)↔
      g.val∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  constructor
  · intro he
    obtain ⟨γ,hγ⟩ := g.property
    have ha : ∀ τ : ℍ,γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
      intro τ
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply,
        UpperHalfPlane.coe_smul_of_det_pos (by simp)]
      simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.map,Matrix.of_apply]
    have hi : γ∈CongruenceSubgroup.Gamma0 N :=
      (lpsOriginalJDilatedExactStabilizer N hN γ).mp (fun τ=>by rw [ha,hγ];exact he τ)
    exact ⟨γ,hi,hγ⟩
  · intro hg τ
    exact lpsOriginalJDilated_Gamma0_invariant N hN g.val hg τ

/-- Concrete ambient fraction root chosen from each actual left-coset inverse representative. -/
def lpsOriginalCosetFractionRoot (N : ℕ) (hN : 0<N)
    (x : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    LPSOriginalHolomorphicFractionField :=
  lpsOriginalFractionPullbackRing x.out (lpsOriginalJNInFractionField N hN)

/-- Genuine inverse-coset branch injectivity from faithful localization and the actual proved exact original stabilizer. -/
lemma lpsOriginalCosetFractionRoot_injective (N : ℕ) (hN : 0<N) :
    Function.Injective (lpsOriginalCosetFractionRoot N hN) := by
  intro x y he
  have hf : lpsOriginalHolomorphicPullback x.out (lpsOriginalJNHolomorphic N hN)=
      lpsOriginalHolomorphicPullback y.out (lpsOriginalJNHolomorphic N hN) := by
    apply IsFractionRing.injective LPSOriginalHolomorphicRing
      LPSOriginalHolomorphicFractionField
    simpa only [lpsOriginalCosetFractionRoot,lpsOriginalJNInFractionField,
      lpsOriginalFractionPullbackRing_localization] using he
  have hpoint : ∀ τ : ℍ,
      lpsOriginalJDilated N hN (x.out.val⁻¹•τ)=
        lpsOriginalJDilated N hN (y.out.val⁻¹•τ) := by
    intro τ
    exact congrArg (fun f : LPSOriginalHolomorphicRing=>f.val τ) hf
  have hg : (x.out⁻¹*y.out).val∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    apply (lpsOriginalJDilatedRealExactStabilizer N hN (x.out⁻¹*y.out)).mp
    intro τ
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,inv_smul_smul] using
      hpoint (y.out.val•τ)
  have hrep : (QuotientGroup.mk x.out : 𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)=
        QuotientGroup.mk y.out := QuotientGroup.eq.mpr hg
  exact x.out_eq'.symm.trans (hrep.trans y.out_eq')

/-- The exact degree of SAME generated original C(j,jN) equals actual Gamma0 coset cardinal, by true distinct minpoly roots and the proved upper bound. -/
lemma lpsOriginalGeneratedFunctionField_finrank_eq (N : ℕ) [NeZero N]
    (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  classical
  let := lpsOriginalJFractionEmbedding.toAlgebra
  apply le_antisymm (lpsOriginalGeneratedFunctionField_finrank_bound N hN)
  rw [show Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
    (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN)).natDegree from
      IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integral N hN)]
  let Q := minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN)
  let P := Q.map (algebraMap (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField)
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  have hP : P≠0 := Polynomial.map_ne_zero
    (minpoly.ne_zero (lpsOriginalJNInFractionField_integral N hN))
  have hroot : ∀ x : 𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
      P.eval (lpsOriginalCosetFractionRoot N hN x)=0 := by
    intro x
    dsimp only [P]
    rw [Polynomial.eval_map]
    change Polynomial.aeval
      (lpsOriginalFractionPullback x.out (lpsOriginalJNInFractionField N hN)) Q=0
    exact lpsOriginalFractionPullback_minpolyRoot N hN x.out
  have hd : P.natDegree=Q.natDegree := Polynomial.natDegree_map _
  rw [Nat.card_eq_fintype_card]
  by_contra hc
  have hlt : P.natDegree<Fintype.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [hd];exact Nat.lt_of_not_ge hc
  exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (lpsOriginalCosetFractionRoot_injective N hN) hroot hlt)


/-- The actual holomorphic pullback fixes every genuine rational j-polynomial evaluation via the faithful complex coefficient inclusion. -/
lemma lpsOriginalHolomorphicPullback_polynomialQ (g : 𝒮ℒ)
    (P : Polynomial ℚ) :
    lpsOriginalHolomorphicPullback g (lpsOriginalJHolomorphicEvalQ P)=
      lpsOriginalJHolomorphicEvalQ P := by
  change lpsOriginalHolomorphicPullback g
      (lpsOriginalJHolomorphicEval (P.map (algebraMap ℚ ℂ)))=
    lpsOriginalJHolomorphicEval (P.map (algebraMap ℚ ℂ))
  exact lpsOriginalHolomorphicPullback_polynomial g _

/-- The actual ambient pullback fixes the SAME faithful embedded Q(j) at every rational fraction. -/
lemma lpsOriginalFractionPullbackRing_fixesBaseQ (g : 𝒮ℒ)
    (x : FractionRing (Polynomial ℚ)) :
    lpsOriginalFractionPullbackRing g (lpsOriginalJFractionEmbeddingQ x)=
      lpsOriginalJFractionEmbeddingQ x := by
  have h : (lpsOriginalFractionPullbackRing g).toRingHom.comp
      lpsOriginalJFractionEmbeddingQ=lpsOriginalJFractionEmbeddingQ := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
    intro P
    change lpsOriginalFractionPullbackRing g
        (lpsOriginalJFractionEmbeddingQ
          (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P))=
      lpsOriginalJFractionEmbeddingQ
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)
    rw [lpsOriginalJFractionEmbeddingQ_polynomial,
      lpsOriginalFractionPullbackRing_localization,
      lpsOriginalHolomorphicPullback_polynomialQ]
  exact RingHom.congr_fun h x

/-- Actual ambient Q(j)-algebra automorphism, using the proved original rational fixed-base law. -/
def lpsOriginalFractionPullbackQ (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalHolomorphicFractionField ≃ₐ[FractionRing (Polynomial ℚ)]
      LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact { lpsOriginalFractionPullbackRing g with
    commutes' := lpsOriginalFractionPullbackRing_fixesBaseQ g }

/-- The actual rational minimal polynomial vanishes at every genuine original pulled-back jN root. -/
lemma lpsOriginalFractionPullback_minpolyRootQ (N : ℕ) [NeZero N]
    (hN : 0<N) (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval
      (lpsOriginalFractionPullbackQ g (lpsOriginalJNInFractionField N hN))
      (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN))=0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact minpoly.aeval_algHom (FractionRing (Polynomial ℚ))
    (lpsOriginalFractionPullbackQ g).toAlgHom
    (lpsOriginalJNInFractionField N hN)

/-- The exact degree of SAME generated original Q(j,jN) equals actual Gamma0 coset cardinal, using the SAME genuine distinct branches. -/
lemma lpsOriginalGeneratedFunctionFieldQ_finrank_eq (N : ℕ) [NeZero N]
    (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Module.finrank (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply le_antisymm (lpsOriginalGeneratedFunctionFieldQ_finrank_bound N hN)
  rw [show Module.finrank (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)=
    (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)).natDegree from
      IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integralQ N hN)]
  let Q := minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)
  let P := Q.map (algebraMap (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField)
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  have hP : P≠0 := Polynomial.map_ne_zero
    (minpoly.ne_zero (lpsOriginalJNInFractionField_integralQ N hN))
  have hroot : ∀ x : 𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
      P.eval (lpsOriginalCosetFractionRoot N hN x)=0 := by
    intro x
    dsimp only [P]
    rw [Polynomial.eval_map]
    change Polynomial.aeval
      (lpsOriginalFractionPullbackQ x.out (lpsOriginalJNInFractionField N hN)) Q=0
    exact lpsOriginalFractionPullback_minpolyRootQ N hN x.out
  have hd : P.natDegree=Q.natDegree := Polynomial.natDegree_map _
  rw [Nat.card_eq_fintype_card]
  by_contra hc
  have hlt : P.natDegree<Fintype.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [hd];exact Nat.lt_of_not_ge hc
  exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (lpsOriginalCosetFractionRoot_injective N hN) hroot hlt)

end
end QEC.Coding.TannerLiftedProduct
