import QEC.Coding.ExpanderCodes.LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# LPSOriginalFunctionField

Construct the actual ring of holomorphic functions on the original upper half
plane. The analytic identity theorem proves that it has no zero divisors.
Bundle the SAME original j and jN with their proved holomorphy; faithful
polynomial evaluation at j embeds C[X] and then its fraction field C(X).
The proved original monic modular equation makes the actual jN integral.
Inside this actual holomorphic fraction field, adjoin precisely jN over
the embedded C(j). Its genuine minimal polynomial divides the constructed
annihilator, giving finite dimensionality and the actual coset-degree upper
bound for every positive level, including composite original theta levels.

This generated C(j,jN) field has not yet been identified with ALL meromorphic
functions on the SAME compact original quotient. Exact minimal degree,
integral coefficients, rational descent, arithmetic normalization, uniform
good reduction, geometric Hecke/Frobenius/Weil and the unconditional public
PK22 theorem remain subsequent mathematics. The internal bridge is motivated
by pinned PK22 main.tex ex:Xpq/th:qLDPC and the audited original modular-curve
normalization route; no new public source claim is introduced.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Actual complex subalgebra of genuinely holomorphic functions on the same upper half plane. -/
def lpsOriginalHolomorphicSubalgebra : Subalgebra ℂ (ℍ→ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  algebraMap_mem' c := (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : ℍ => c) from mdifferentiable_const)

/-- Actual underlying ring of that concrete holomorphic subalgebra. -/
abbrev LPSOriginalHolomorphicRing := ↥lpsOriginalHolomorphicSubalgebra

/-- No zero divisors from the genuine upper-half-plane analytic identity theorem. -/
instance lpsOriginalHolomorphicRing_noZeroDivisors :
    NoZeroDivisors LPSOriginalHolomorphicRing where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    have he : f.val*g.val=0 := congrArg Subtype.val h
    exact ((UpperHalfPlane.mul_eq_zero_iff f.property g.property).mp he).imp
      (fun hf => Subtype.ext hf) (fun hg => Subtype.ext hg)

/-- Actual integral domain instance obtained from the proved no-zero-divisor property. -/
instance lpsOriginalHolomorphicRing_isDomain :
    IsDomain LPSOriginalHolomorphicRing := NoZeroDivisors.to_isDomain _

/-- SAME actual original j bundled with its already proved holomorphy. -/
def lpsOriginalJHolomorphic : LPSOriginalHolomorphicRing :=
  ⟨lpsOriginalJInvariant,lpsOriginalJInvariant_holomorphic⟩

/-- SAME actual original jN bundled with its already proved holomorphy for every positive N. -/
def lpsOriginalJNHolomorphic (N : ℕ) (hN : 0<N) :
    LPSOriginalHolomorphicRing :=
  ⟨lpsOriginalJDilated N hN,lpsOriginalJDilated_holomorphic N hN⟩

/-- Actual polynomial evaluation at SAME original j into the genuine holomorphic ring. -/
def lpsOriginalJHolomorphicEval : Polynomial ℂ →ₐ[ℂ] LPSOriginalHolomorphicRing :=
  Polynomial.aeval lpsOriginalJHolomorphic

/-- Literal pointwise polynomial evaluation equality for that actual map. -/
lemma lpsOriginalJHolomorphicEval_apply (P : Polynomial ℂ) (τ : ℍ) :
    (lpsOriginalJHolomorphicEval P).val τ=P.eval (lpsOriginalJInvariant τ) := by
  simp only [lpsOriginalJHolomorphicEval,Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_fn_apply,Polynomial.coe_aeval_eq_eval]
  rfl

/-- Actual injectivity from faithful SAMEj polynomial evaluation. -/
lemma lpsOriginalJHolomorphicEval_injective :
    Function.Injective lpsOriginalJHolomorphicEval := by
  intro P Q h
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  have he := congrArg (fun f : LPSOriginalHolomorphicRing => f.val τ) h
  simpa only [lpsOriginalJHolomorphicEval_apply,lpsOriginalJPolynomialEvalHom_apply] using he

/-- Actual original jN is integral over the image of C[j], using the proved monic original relation. -/
lemma lpsOriginalJNHolomorphic_integral (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalJHolomorphicEval.toRingHom.IsIntegralElem
      (lpsOriginalJNHolomorphic N hN) := by
  obtain ⟨Φ,hΦ,_,hroot⟩ := lpsOriginalJ_jN_monic_relation N hN
  refine ⟨Φ,hΦ,?_⟩
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+*ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEval.toRingHom=
      Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
    apply RingHom.ext
    intro P
    exact lpsOriginalJHolomorphicEval_apply P τ
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEval.toRingHom e
    (lpsOriginalJNHolomorphic N hN)
  rw [hc] at h
  exact h.trans (hroot τ)

/-- Actual fraction field of the proved genuine holomorphic integral domain. -/
abbrev LPSOriginalHolomorphicFractionField := FractionRing LPSOriginalHolomorphicRing

/-- Faithful fraction-field embedding of C(X) through actual polynomial evaluation at SAMEj. -/
def lpsOriginalJFractionEmbedding :
    FractionRing (Polynomial ℂ) →+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.lift (g:=(algebraMap LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField).comp lpsOriginalJHolomorphicEval.toRingHom)
    ((IsFractionRing.injective LPSOriginalHolomorphicRing
      LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEval_injective)

/-- Actual fraction embedding on every polynomial equals genuine j evaluation followed by localization. -/
lemma lpsOriginalJFractionEmbedding_polynomial (P : Polynomial ℂ) :
    lpsOriginalJFractionEmbedding (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEval P) :=
  IsFractionRing.lift_algebraMap _ P

/-- SAME original jN element in the actual holomorphic fraction field. -/
def lpsOriginalJNInFractionField (N : ℕ) (hN : 0<N) :
    LPSOriginalHolomorphicFractionField :=
  algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
    (lpsOriginalJNHolomorphic N hN)

/-- Actual intermediate field adjoining precisely SAME original jN over the faithful C(j) embedding. -/
def lpsOriginalGeneratedFunctionField (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    IntermediateField (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbedding.toAlgebra
  exact IntermediateField.adjoin (FractionRing (Polynomial ℂ))
    {lpsOriginalJNInFractionField N hN}

/-- Actual mapped monic annihilator of SAME original jN, bounded by the true coset cardinal. -/
lemma lpsOriginalJNInFractionField_annihilator (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∃ P : Polynomial (FractionRing (Polynomial ℂ)), P.Monic ∧
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P=0 := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  obtain ⟨Φ,hΦ,hdeg,hroot⟩ := lpsOriginalJ_jN_monic_relation N hN
  let P := Φ.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  refine ⟨P,hΦ.map _,Polynomial.natDegree_map_le.trans hdeg.le,?_⟩
  rw [Polynomial.aeval_def,Polynomial.eval₂_map]
  have hc : (algebraMap (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEval.toRingHom := by
    apply RingHom.ext
    intro Q
    exact lpsOriginalJFractionEmbedding_polynomial Q
  rw [hc]
  have hzero : Φ.eval₂ lpsOriginalJHolomorphicEval.toRingHom
      (lpsOriginalJNHolomorphic N hN)=0 := by
    apply Subtype.ext
    funext τ
    let e : LPSOriginalHolomorphicRing →+*ℂ :=
      { toFun f := f.val τ
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl }
    have hj : e.comp lpsOriginalJHolomorphicEval.toRingHom=
        Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
      apply RingHom.ext
      intro Q
      exact lpsOriginalJHolomorphicEval_apply Q τ
    have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEval.toRingHom e
      (lpsOriginalJNHolomorphic N hN)
    rw [hj] at h
    exact h.trans (hroot τ)
  have h := Polynomial.hom_eval₂ Φ lpsOriginalJHolomorphicEval.toRingHom
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic N hN)
  rw [hzero,map_zero] at h
  exact h.symm

/-- Actual integrality of SAME original jN over the embedded C(j) fraction field. -/
lemma lpsOriginalJNInFractionField_integral (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    IsIntegral (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  obtain ⟨P,hP,_,he⟩ := lpsOriginalJNInFractionField_annihilator N hN
  exact ⟨P,hP,he⟩

/-- Actual finite dimensionality of the literally generated SAME C(j,jN) field. -/
lemma lpsOriginalGeneratedFunctionField_finiteDimensional (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact IntermediateField.adjoin.finiteDimensional
    (lpsOriginalJNInFractionField_integral N hN)

/-- Actual generated-field degree upper bound via its genuine minimal polynomial dividing the proved monic annihilator. -/
lemma lpsOriginalGeneratedFunctionField_finrank_bound (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [show Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
    (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN)).natDegree from
      IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integral N hN)]
  obtain ⟨P,hP,hd,he⟩ := lpsOriginalJNInFractionField_annihilator N hN
  exact (Polynomial.natDegree_le_of_dvd
    (minpoly.dvd (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN) he)
    hP.ne_zero).trans hd

end
end QEC.Coding.TannerLiftedProduct
