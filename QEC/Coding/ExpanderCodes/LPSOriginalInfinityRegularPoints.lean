import QEC.Coding.ExpanderCodes.LPSOriginalReciprocalFieldIntegral
import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationLocalRings

/-!
# Actual reciprocal regular points and coordinates

Construct the actual inverse-j regular-point domain, base polynomial map and coordinate from existing infinity evaluations. Prove base evaluation, interior inverse-j values and actual cusp zero values without an assumed germ-field inverse law.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Global point injectivity, differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityRegularPointsDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local instance LPSOriginalInfinityRegularPointsDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalInfinityRegularPointsDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalInfinityRegularPointsDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- Actual filled-curve points where the existing inverse-j germ order is nonnegative. -/
def lpsOriginalInfinityRegularPoints : Type :=
  {x : LPSOriginalFilledCurve N // 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
    (algebraMap P K Polynomial.X)⁻¹}
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

/-- Map the actual reciprocal polynomial base into the independently defined infinity integral closure. -/
def lpsOriginalInfinityPolynomialChartMap : P →+* R := by
  letI : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  exact algebraMap P R

omit [NeZero N] in
/-- The constructed integral-closure base map retains the literal same-field reciprocal polynomial value. -/
lemma lpsOriginalInfinityPolynomialChartMap_value (p : P) :
    (lpsOriginalInfinityPolynomialChartMap N hpos p).val =
      lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p := rfl

/-- Evaluate the actual reciprocal base coordinate at the existing genuine infinity point evaluation. -/
def lpsOriginalInfinityCoordinate (x : S) : ℂ :=
  lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
    (lpsOriginalInfinityPolynomialChartMap N hpos Polynomial.X)

/-- Every actual base polynomial evaluates at the constructed genuine point coordinate. -/
lemma lpsOriginalInfinityEvaluation_polynomial (x : S) (p : P) :
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
      (lpsOriginalInfinityPolynomialChartMap N hpos p) =
        p.eval (lpsOriginalInfinityCoordinate N hpos hN x) := by
  let E := lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
  have hh : E.comp (lpsOriginalInfinityPolynomialChartMap N hpos) =
      Polynomial.evalRingHom (lpsOriginalInfinityCoordinate N hpos hN x) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_C]
      have hc : lpsOriginalInfinityPolynomialChartMap N hpos (Polynomial.C c) =
          lpsOriginalComplexInfinityConstantRingHom N hpos c := by
        apply Subtype.ext
        rw [lpsOriginalInfinityPolynomialChartMap_value,
          lpsOriginalInfinityConstantChart_value,lpsOriginalReciprocalFieldPolynomialMap_eval]
        simp
      rw [hc]
      exact lpsOriginalInfinityNormalChartEvaluation_constant N hpos hN x.val x.property c
    · simp only [RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_X]
      rfl
  exact RingHom.congr_fun hh p

/-- Actual inverse-j regularity excludes interior j zeros by positive finite j order. -/
lemma lpsOriginalInfinityRegular_interior_nonzero
    (x : Q) (hx : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X)⁻¹) : lpsOriginalFilledJ N (Sum.inl x) ≠ 0 := by
  intro hz
  have hp : 0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X) := by
    simpa only [map_zero,sub_zero] using lpsOriginalFieldJ_sub_constant_order_pos N hpos hN 0 x hz
  have hjne : algebraMap P K Polynomial.X ≠ 0 := by
    simpa only [map_zero,sub_zero] using lpsOriginalFieldJ_sub_constant_ne_zero N hpos 0
  have ht := lpsOriginalFieldLocalOrder_ne_top N hN hpos (Sum.inl x) _ hjne
  lift lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X)
    to ℤ using ht with k hk
  have hkpos : 0 < k := by exact_mod_cast hp
  rw [AddValuation.map_inv,←hk,←WithTop.LinearOrderedAddCommGroup.coe_neg] at hx
  have hkneg : 0 ≤ -k := by exact_mod_cast hx
  omega

/-- At genuine interior j-nonzero points the actual infinity coordinate equals the inverse j value. -/
lemma lpsOriginalInfinityCoordinate_interior (x : Q)
    (hx : lpsOriginalFilledJ N (Sum.inl x) ≠ 0) :
    lpsOriginalInfinityCoordinate N hpos hN
      ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩ =
        (lpsOriginalFilledJ N (Sum.inl x))⁻¹ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let e := lpsOriginalFilledInteriorChart N hN x
  let z := e (Sum.inl x)
  have hcenter : lpsOriginalLocalChartCenter N hN (Sum.inl x) = z := rfl
  have hs := lpsOriginalFilledInteriorChart_mem N hN x
  have ha := lpsOriginalFilledJ_interior_analytic N hN x z (e.map_source hs)
  let A : (AddValuation.toValuation (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN (Sum.inl x)))).integer :=
    ⟨lpsOriginalFieldToLocal N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X),by
      change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X)
      exact lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x⟩
  let B : (AddValuation.toValuation (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN (Sum.inl x)))).integer :=
    lpsOriginalInfinityNormalChartToMeromorphicInteger N hpos hN (Sum.inl x)
    (lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx)
    (lpsOriginalInfinityPolynomialChartMap N hpos Polynomial.X)
  have hB : B.val = lpsOriginalFieldToLocal N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X)⁻¹ := by
    change lpsOriginalFieldToLocal N hN hpos (Sum.inl x)
      (lpsOriginalInfinityPolynomialChartMap N hpos Polynomial.X).val = _
    rw [lpsOriginalInfinityPolynomialChartMap_value,
      lpsOriginalReciprocalFieldPolynomialMap_eval,Polynomial.eval₂_X]
  have hjne : algebraMap P K Polynomial.X ≠ 0 := by
    simpa only [map_zero,sub_zero] using lpsOriginalFieldJ_sub_constant_ne_zero N hpos 0
  have hm : A*B = 1 := by
    apply Subtype.ext
    change lpsOriginalFieldToLocal N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X) * B.val = 1
    rw [hB,←map_mul,mul_inv_cancel₀ hjne,map_one]
  have hAval : meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN (Sum.inl x)) A = lpsOriginalFilledJ N (Sum.inl x) := by
    have he : meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN (Sum.inl x)) A =
        lpsOriginalFilledJ N (e.symm (lpsOriginalLocalChartCenter N hN (Sum.inl x))) := by
      apply meromorphicNoPoleEvaluation_rep _ _ (fun w => lpsOriginalFilledJ N (e.symm w))
        (by simpa only [hcenter] using ha)
      change (lpsOriginalFieldToLocal N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X)).val = _
      rw [lpsOriginalFieldToLocal_j]
      rfl
    have hpoint : e.symm (lpsOriginalLocalChartCenter N hN (Sum.inl x)) = Sum.inl x := by
      rw [hcenter]
      exact e.left_inv hs
    rwa [hpoint] at he
  have hmul : lpsOriginalFilledJ N (Sum.inl x) *
      lpsOriginalInfinityCoordinate N hpos hN
        ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩ = 1 := by
    have h := congrArg (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN (Sum.inl x))) hm
    rw [map_mul,map_one,hAval] at h
    exact h
  calc
    _ = lpsOriginalInfinityCoordinate N hpos hN
      ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩ *
        (lpsOriginalFilledJ N (Sum.inl x) * (lpsOriginalFilledJ N (Sum.inl x))⁻¹) := by
          rw [mul_inv_cancel₀ hx,mul_one]
    _ = (lpsOriginalFilledJ N (Sum.inl x) *
      lpsOriginalInfinityCoordinate N hpos hN
        ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩) *
        (lpsOriginalFilledJ N (Sum.inl x))⁻¹ := by ring
    _ = _ := by rw [hmul,one_mul]

/-- The actual negative cusp-width order of j gives strictly positive inverse-j order at every cusp. -/
lemma lpsOriginalFieldJ_inverse_cusp_order_positive (c : C) :
    0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c)
      (algebraMap P K Polynomial.X)⁻¹ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  have hj : lpsOriginalFieldLocalOrder N hN hpos (Sum.inr c)
      (algebraMap P K Polynomial.X) =
        (-(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c) : ℤ) : WithTop ℤ) := by
    rw [lpsOriginalFieldLocalOrder_value,lpsOriginalFieldToLocal_j]
    change meromorphicOrderAt
      (lpsOriginalFilledJ N ∘ (lpsOriginalFilledCuspChart N c).symm)
      (lpsOriginalFilledCuspChart N c (Sum.inr c)) = _
    rw [lpsOriginalFilledCuspChart_cusp]
    exact lpsOriginalFilledJ_cusp_order N c
  rw [AddValuation.map_inv,hj]
  simp only [←WithTop.LinearOrderedAddCommGroup.coe_neg,neg_neg]
  exact_mod_cast lpsOriginalCuspWidthNat_positive N (lpsOriginalCuspRepresentative N c)

/-- The actual infinity coordinate is zero at every genuine cusp because inverse j has positive order. -/
lemma lpsOriginalInfinityCoordinate_cusp (c : C) :
    lpsOriginalInfinityCoordinate N hpos hN
      ⟨Sum.inr c,lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c⟩ = 0 := by
  apply (lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN _ _ _).mpr
  rw [lpsOriginalInfinityPolynomialChartMap_value,
    lpsOriginalReciprocalFieldPolynomialMap_eval]
  simpa only [Polynomial.eval₂_X] using
    lpsOriginalFieldJ_inverse_cusp_order_positive N hpos hN c

end
end QEC.Coding.TannerLiftedProduct
