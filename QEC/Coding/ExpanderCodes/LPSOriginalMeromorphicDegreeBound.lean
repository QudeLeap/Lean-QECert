import QEC.Coding.ExpanderCodes.LPSOriginalMeromorphicModularRatio

/-!
# Actual finite-coset norm and all-meromorphic degree bounds

This module belongs to the source-grounded original LPS analytic proof closure.
Milne, *Modular Functions and Modular Forms*, Theorem 6.1 (PDF85 / printed82)
and Propositions 1.16–1.18 motivate the genuine function-field degree argument.
The filled original Gamma0(N) manifold statements retain their proved scope
4 divides N, including the actual theta levels 16*q_graph^2.

The all-meromorphic objects use actual chartwise-meromorphic representatives
and genuine germ equality. They are never defined as the generated C(j,j_N).
The public arbitrary-field/all-rate PK22 theorem, arithmetic normalization,
uniform good reduction and geometric Weil estimate remain further proof work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- The actual original Gamma0 cosets inside the genuine integral modular group. -/
abbrev LPSOriginalMeromorphicCosets (N : ℕ) := 𝒮ℒ ⧸
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ

/-- Actual original-level modular forms of weight 12k. -/
abbrev LPSOriginalMeromorphicLevelForm (N k : ℕ) :=
  ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((k : ℤ)*12)

/-- The genuine finite-coset modular norm of the actual form A-cB. -/
def lpsOriginalMeromorphicRatioNorm
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    ModularForm 𝒮ℒ (12*((k * Nat.card (LPSOriginalMeromorphicCosets N) : ℕ) : ℤ)) :=
  (ModularForm.norm 𝒮ℒ (A-c • B)).mcast (by push_cast; ring)

/-- Actual quotient-function linearity for the same-weight input A-cB. -/
lemma lpsOriginalMeromorphicRatioNorm_quotient
    (N : ℕ) (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc (A-c • B) q τ =
      SlashInvariantForm.quotientFunc A q τ - c * SlashInvariantForm.quotientFunc B q τ := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hd : (g.val⁻¹).det=1 := Subgroup.HasDetOne.det_eq (inv_mem g.property)
    have hp : 0 < (g.val⁻¹).det.val := by rw [hd]; norm_num
    simp only [SlashInvariantForm.quotientFunc_mk,FunLike.coe_sub,FunLike.coe_smul,
      ModularForm.slash_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,UpperHalfPlane.σ,
      if_pos hp,ContinuousAlgEquiv.refl_apply]
    ring

/-- The literal polynomial product over the actual original cosets. -/
def lpsOriginalMeromorphicRatioCosetPolynomial
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) : Polynomial ℂ := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  exact ∏ q : LPSOriginalMeromorphicCosets N,
    (Polynomial.C (SlashInvariantForm.quotientFunc A q τ) -
      Polynomial.X * Polynomial.C (SlashInvariantForm.quotientFunc B q τ))

/-- The actual coset product evaluates to the genuine modular-form norm. -/
lemma lpsOriginalMeromorphicRatioCosetPolynomial_eval
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (c : ℂ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).eval c =
      lpsOriginalMeromorphicRatioNorm N k A B c τ := by
  classical
  simp only [lpsOriginalMeromorphicRatioCosetPolynomial,Polynomial.eval_prod,
    Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    lpsOriginalMeromorphicRatioNorm,ModularForm.mcast_apply,ModularForm.coe_norm,
    Finset.prod_apply,lpsOriginalMeromorphicRatioNorm_quotient]

/-- The actual polynomial degree is at most the genuine original coset cardinal. -/
lemma lpsOriginalMeromorphicRatioCosetPolynomial_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).natDegree ≤
      Nat.card (LPSOriginalMeromorphicCosets N) := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  unfold lpsOriginalMeromorphicRatioCosetPolynomial
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _q : LPSOriginalMeromorphicCosets N, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- The actual level-one j-polynomial of the genuine same-weight norm. -/
def lpsOriginalMeromorphicRatioNormCoefficient
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    Polynomial ℂ := Classical.choose
      (lpsOriginalLevelOne_unique_polynomial_j (k*Nat.card (LPSOriginalMeromorphicCosets N))
        (lpsOriginalMeromorphicRatioNorm N k A B c)).exists

/-- The actual j-polynomial has bounded degree and exactly recovers the genuine norm. -/
lemma lpsOriginalMeromorphicRatioNormCoefficient_spec
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    (lpsOriginalMeromorphicRatioNormCoefficient N k A B c).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) ∧ ∀ τ : ℍ,
    lpsOriginalMeromorphicRatioNorm N k A B c τ =
      ModularForm.discriminant τ ^ (k * Nat.card (LPSOriginalMeromorphicCosets N)) *
        (lpsOriginalMeromorphicRatioNormCoefficient N k A B c).eval (lpsOriginalJInvariant τ) :=
  Classical.choose_spec
    (lpsOriginalLevelOne_unique_polynomial_j (k*Nat.card (LPSOriginalMeromorphicCosets N))
      (lpsOriginalMeromorphicRatioNorm N k A B c)).exists

/-- Construct the fixed nested polynomial from actual norm coefficients and genuine interpolation. -/
def lpsOriginalMeromorphicRatioEquation
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) :
    Polynomial (Polynomial ℂ) := by
  classical
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  exact ∑ i : Fin (r+1),
    Polynomial.C (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)) *
      (Lagrange.basis (Finset.univ : Finset (Fin (r+1))) (fun j => (j.val : ℂ)) i).map Polynomial.C

/-- Specialization of the constructed equation is the actual Lagrange interpolant. -/
lemma lpsOriginalMeromorphicRatioEquation_map
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (x : ℂ) :
    (lpsOriginalMeromorphicRatioEquation N k A B).map (Polynomial.evalRingHom x) =
      Lagrange.interpolate
        (Finset.univ : Finset (Fin (Nat.card (LPSOriginalMeromorphicCosets N)+1)))
        (fun i => (i.val : ℂ))
        (fun i => (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)).eval x) := by
  classical
  have hc : (Polynomial.evalRingHom x).comp (Polynomial.C : ℂ →+* Polynomial ℂ) =
      RingHom.id ℂ := by
    ext z
    exact Polynomial.eval_C
  simp only [lpsOriginalMeromorphicRatioEquation,Polynomial.map_sum,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_map,hc,Polynomial.map_id,
    Lagrange.interpolate_apply,Polynomial.coe_evalRingHom]

/-- The genuine Delta power times the constructed equation recovers the literal coset product. -/
lemma lpsOriginalMeromorphicRatioEquation_recovery
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    Polynomial.C (ModularForm.discriminant τ ^
      (k*Nat.card (LPSOriginalMeromorphicCosets N))) *
        (lpsOriginalMeromorphicRatioEquation N k A B).map
          (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) =
      lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ := by
  classical
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  let d := ModularForm.discriminant τ ^ (k*r)
  rw [lpsOriginalMeromorphicRatioEquation_map]
  have hm : Polynomial.C d * Lagrange.interpolate (Finset.univ : Finset (Fin (r+1)))
      (fun i => (i.val : ℂ))
      (fun i => (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)).eval
        (lpsOriginalJInvariant τ)) =
      Lagrange.interpolate (Finset.univ : Finset (Fin (r+1))) (fun i => (i.val : ℂ))
        (fun i => d * (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)).eval
          (lpsOriginalJInvariant τ)) := by
    simp only [Lagrange.interpolate_apply,Finset.mul_sum,Polynomial.C_mul,mul_assoc]
  rw [hm]
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _
    (lpsOriginalModularInterpolationNodes_injective r).injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    have hh := Nat.lt_succ_of_le
      (lpsOriginalMeromorphicRatioCosetPolynomial_degree N k A B τ)
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast hh
  · intro i hi
    rw [lpsOriginalMeromorphicRatioCosetPolynomial_eval]
    exact (lpsOriginalMeromorphicRatioNormCoefficient_spec N k A B (i.val : ℂ)).2 τ

/-- The constructed equation has degree at most the actual original coset cardinal. -/
lemma lpsOriginalMeromorphicRatioEquation_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A B).natDegree ≤
      Nat.card (LPSOriginalMeromorphicCosets N) := by
  classical
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  unfold lpsOriginalMeromorphicRatioEquation
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  apply Polynomial.natDegree_mul_le.trans
  have hb := Lagrange.natDegree_basis
    (lpsOriginalModularInterpolationNodes_injective r).injOn (Finset.mem_univ i)
  have hm := Polynomial.natDegree_map_le (p := Lagrange.basis
    (Finset.univ : Finset (Fin (r+1))) (fun j => (j.val : ℂ)) i)
    (f := Polynomial.C)
  simpa only [Polynomial.natDegree_C,zero_add,Finset.card_univ,Fintype.card_fin,
    Nat.add_sub_cancel] using hm.trans hb.le

/-- The actual identity-coset factor makes every represented meromorphic function a root. -/
lemma lpsOriginalMeromorphicRatioEquation_root
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (f : ℍ → ℂ) (hf : ∀ τ, A τ = B τ * f τ) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioEquation N k A B).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (f τ) = 0 := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  have hc : (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).eval (f τ) = 0 := by
    rw [lpsOriginalMeromorphicRatioCosetPolynomial_eval]
    simp only [lpsOriginalMeromorphicRatioNorm,ModularForm.mcast_apply,
      ModularForm.coe_norm,Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟦(1 : 𝒮ℒ)⟧))
    simp [SlashInvariantForm.quotientFunc_mk,hf τ,mul_comm]
  have h := congrArg (fun P : Polynomial ℂ => P.eval (f τ))
    (lpsOriginalMeromorphicRatioEquation_recovery N k A B τ)
  rw [Polynomial.eval_mul,Polynomial.eval_C,hc,Polynomial.eval_map] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))

/-- A nonzero actual denominator forces a genuine nonzero constructed equation. -/
lemma lpsOriginalMeromorphicRatioEquation_nonzero
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (hB : B ≠ 0) :
    lpsOriginalMeromorphicRatioEquation N k A B ≠ 0 := by
  obtain ⟨c,hc⟩ : ∃ c : ℂ, A-c • B ≠ 0 := by
    by_cases hA : A = 0
    · refine ⟨1,?_⟩
      simpa [hA] using hB
    · refine ⟨0,?_⟩
      simpa using hA
  intro hzero
  have hnorm : lpsOriginalMeromorphicRatioNorm N k A B c ≠ 0 := by
    exact ModularForm.mcast_eq_zero_iff _ rfl _ |>.not.mpr
      (ModularForm.norm_ne_zero 𝒮ℒ (by
        intro hzero
        apply hc
        ext τ
        exact congr_fun hzero τ))
  apply hnorm
  ext τ
  have h := congrArg (fun P : Polynomial ℂ => P.eval c)
    (lpsOriginalMeromorphicRatioEquation_recovery N k A B τ)
  rw [hzero,Polynomial.map_zero,mul_zero,Polynomial.eval_zero,
    lpsOriginalMeromorphicRatioCosetPolynomial_eval] at h
  exact h.symm

/-- Every actual filled-curve meromorphic function has a nonzero original j equation of bounded degree. -/
lemma lpsOriginalFilledMeromorphic_exists_nested_annihilator
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ ≠ 0 ∧
      Φ.natDegree ≤ Nat.card (LPSOriginalMeromorphicCosets N) ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (F (Sum.inl ⟦τ⟧)) = 0 := by
  obtain ⟨k,A,B,hB,hAB⟩ := lpsOriginalFilledMeromorphic_exists_modular_ratio N hN F hF
  exact ⟨lpsOriginalMeromorphicRatioEquation N k A B,
    lpsOriginalMeromorphicRatioEquation_nonzero N k A B hB,
    lpsOriginalMeromorphicRatioEquation_degree N k A B,
    lpsOriginalMeromorphicRatioEquation_root N k A B _ hAB⟩

/-- The faithful SAME C(j) embedding into the entire actual meromorphic restriction field. -/
def lpsOriginalFullMeromorphicJFractionEmbedding
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    FractionRing (Polynomial ℂ) →+* lpsOriginalFilledMeromorphicRestrictionSubfield N hN where
  toFun r := ⟨lpsOriginalHolomorphicFractionToMeromorphicGerm (lpsOriginalJFractionEmbedding r),
    lpsOriginalFilledMeromorphicRestriction_j_fraction_mem N hN r⟩
  map_one' := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_one)
  map_mul' r s := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_mul r s)
  map_zero' := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_zero)
  map_add' r s := Subtype.ext ((lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    lpsOriginalJFractionEmbedding).map_add r s)

/-- Literal original j-polynomial evaluation in actual complex-valued functions. -/
def lpsOriginalMeromorphicJFunctionCoefficient : Polynomial ℂ →+* (ℂ → ℂ) where
  toFun P z := P.eval (lpsOriginalJInvariant (UpperHalfPlane.ofComplex z))
  map_one' := by funext z;exact Polynomial.eval_one
  map_mul' P Q := by funext z;exact Polynomial.eval_mul
  map_zero' := by funext z;exact Polynomial.eval_zero
  map_add' P Q := by funext z;exact Polynomial.eval_add

/-- Actual function-valued nested evaluation agrees with literal pointwise evaluation. -/
lemma lpsOriginalMeromorphicJFunctionCoefficient_eval₂
    (Φ : Polynomial (Polynomial ℂ)) (f : ℂ → ℂ) (z : ℂ) :
    (Φ.eval₂ lpsOriginalMeromorphicJFunctionCoefficient f) z =
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant (UpperHalfPlane.ofComplex z)))
        (f z) := by
  induction Φ using Polynomial.induction_on' with
  | add Φ Ψ hΦ hΨ =>
    simp only [Polynomial.eval₂_add,Pi.add_apply,hΦ,hΨ]
  | monomial n P =>
    simp only [Polynomial.eval₂_monomial,Pi.mul_apply,Pi.pow_apply]
    rfl

/-- The faithful C(j) map on polynomials recovers literal original j germs. -/
lemma lpsOriginalFullMeromorphicJFractionEmbedding_polynomial
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (P : Polynomial ℂ) :
    (lpsOriginalFullMeromorphicJFractionEmbedding N hN
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)).val.val =
      Filter.Germ.coeRingHom (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
        (lpsOriginalMeromorphicJFunctionCoefficient P) := by
  change (lpsOriginalHolomorphicFractionToMeromorphicGerm
    (lpsOriginalJFractionEmbedding (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P))).val = _
  rw [lpsOriginalJFractionEmbedding_polynomial,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun z => lpsOriginalJHolomorphicEval_apply P
    (UpperHalfPlane.ofComplex z))

/-- The true pointwise equation descends to the actual original meromorphic germ field. -/
lemma lpsOriginalFilledMeromorphic_nested_annihilator_germ
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (Φ : Polynomial (Polynomial ℂ))
    (hΦ : ∀ τ : ℍ, Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (F (Sum.inl ⟦τ⟧)) = 0) :
    Φ.eval₂ ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))))
      (lpsOriginalFilledMeromorphicRestriction N hN F hF) = 0 := by
  let e := (lpsOriginalMeromorphicGermSubring UpperHalfPlane.upperHalfPlaneSet).subtype.comp
    (lpsOriginalFilledMeromorphicRestrictionSubfield N hN).subtype
  let g : (ℂ → ℂ) →+* Filter.Germ (Filter.codiscreteWithin
      UpperHalfPlane.upperHalfPlaneSet) ℂ :=
    Filter.Germ.coeRingHom (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
  have hc : e.comp ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))) =
      g.comp lpsOriginalMeromorphicJFunctionCoefficient := by
    apply RingHom.ext
    intro P
    exact lpsOriginalFullMeromorphicJFractionEmbedding_polynomial N hN P
  have hfun : Φ.eval₂ lpsOriginalMeromorphicJFunctionCoefficient
      (lpsOriginalFilledMeromorphicPullback N F) = 0 := by
    funext z
    rw [lpsOriginalMeromorphicJFunctionCoefficient_eval₂]
    exact hΦ (UpperHalfPlane.ofComplex z)
  have he := Polynomial.hom_eval₂ Φ
    ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))) e
    (lpsOriginalFilledMeromorphicRestriction N hN F hF)
  rw [hc] at he
  have hx : e (lpsOriginalFilledMeromorphicRestriction N hN F hF) =
      g (lpsOriginalFilledMeromorphicPullback N F) := rfl
  rw [hx,←Polynomial.hom_eval₂,hfun,map_zero] at he
  apply Subtype.ext
  apply Subtype.ext
  exact he

/-- Every element of the entire actual restriction field has a monic bounded-degree C(j) annihilator. -/
lemma lpsOriginalFullMeromorphic_bounded_annihilator
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ x : lpsOriginalFilledMeromorphicRestrictionSubfield N hN,
      ∃ P : Polynomial (FractionRing (Polynomial ℂ)), P.Monic ∧
        P.natDegree ≤ Nat.card (LPSOriginalMeromorphicCosets N) ∧ Polynomial.aeval x P = 0 := by
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  intro x
  obtain ⟨F,hF,hx⟩ := x.property
  have heq : x = lpsOriginalFilledMeromorphicRestriction N hN F hF := by
    apply Subtype.ext
    apply Subtype.ext
    exact hx
  obtain ⟨Φ,hΦ,hdeg,hroot⟩ :=
    lpsOriginalFilledMeromorphic_exists_nested_annihilator N hN F hF
  let Q := Φ.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  have hQ : Q ≠ 0 := by
    intro hz
    apply hΦ
    apply Polynomial.map_injective (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
      (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
    simpa only [Polynomial.map_zero] using hz
  have hzero : Polynomial.aeval x Q = 0 := by
    rw [heq,Polynomial.aeval_def,Polynomial.eval₂_map]
    exact lpsOriginalFilledMeromorphic_nested_annihilator_germ N hN F hF Φ hroot
  refine ⟨Q * Polynomial.C (Q.leadingCoeff)⁻¹,
    Polynomial.monic_mul_leadingCoeff_inv hQ,?_,?_⟩
  · exact Polynomial.natDegree_mul_le.trans
      (by simpa only [Polynomial.natDegree_C,add_zero] using
        (Polynomial.natDegree_map_le.trans hdeg))
  · rw [map_mul,hzero,zero_mul]

end
end QEC.Coding.TannerLiftedProduct
