import QEC.Coding.ExpanderCodes.LPSOriginalGaussLocalOrder
import QEC.Coding.ExpanderCodes.LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Normalization of the original bad-prime Gauss order

The rational coordinate is not a prime power, so the inseparable Kronecker
factor is irreducible of degree p. Its coprime product with the linear factor
is squarefree of degree p+1. The actual prime modular polynomial inherits
this reduction. Thus the actual prime-level Gauss order at its bad prime has
reduced generic special fibre. Reduced closed fibres make a finite domain
algebra over a Dedekind domain Dedekind; applying this proves the actual order
integrally closed. Its canonical equivalence with the integral closure in the
original generated function field preserves j_p and transports reducedness.

Internal derived arithmetic prerequisite of the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (484–486) and th:qLDPC (231–238).
The separable-extension non-power lemmas supply the next composite-level
N*p branch calculation over the coprime-level residue function field.
No global good reduction, normalized component degree or multiplicity,
Frobenius plus Verschiebung cycle identity, Weil bound, full-level spectrum
or exact quantum family is claimed. Parent issue449 remains OPEN and
pk-good-qldpc remains lean.proved=false.
-/
namespace QEC.Coding.AlgebraicGeometry
noncomputable section

lemma ratFunc_intDegree_pow_of_ne_zero
    (K : Type*) [Field K] (u : RatFunc K) (hu : u ≠ 0) (n : ℕ) :
    RatFunc.intDegree (u^n) = (n : ℤ) * RatFunc.intDegree u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,RatFunc.intDegree_mul (pow_ne_zero n hu) hu,ih]
    push_cast
    ring

lemma ratFunc_coordinate_not_prime_power
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) (u : RatFunc K) :
    u^p ≠ RatFunc.X := by
  intro heq
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := by
    intro h
    have hd := congrArg RatFunc.intDegree h
    simp at hd
  have hu : u ≠ 0 := by
    intro h
    apply hX
    rw [← heq,h,zero_pow hp.ne_zero]
  have hd := congrArg RatFunc.intDegree heq
  rw [ratFunc_intDegree_pow_of_ne_zero K u hu p,RatFunc.intDegree_X] at hd
  have hdiv : (p : ℤ) ∣ (1 : ℤ) := ⟨RatFunc.intDegree u,hd.symm⟩
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)

lemma ratFunc_prime_coordinate_polynomial_irreducible
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    Irreducible ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X) :=
  _root_.X_pow_sub_C_irreducible_of_prime hp
    (ratFunc_coordinate_not_prime_power K p hp)

lemma ratFunc_prime_coordinate_quotient_finrank
    (K : Type*) [Field K] (p : ℕ) :
    Module.finrank (RatFunc K)
      (AdjoinRoot ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)) = p := by
  calc
    _ = ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X).natDegree :=
      finrank_quotient_span_eq_natDegree
    _ = p := Polynomial.natDegree_X_pow_sub_C

lemma prime_residue_coordinate_polynomial_irreducible
    (p : ℕ) [Fact p.Prime] :
    Irreducible ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p -
      Polynomial.C RatFunc.X) :=
  ratFunc_prime_coordinate_polynomial_irreducible (ZMod p) p Fact.out

lemma prime_residue_coordinate_quotient_finrank
    (p : ℕ) [Fact p.Prime] :
    Module.finrank (RatFunc (ZMod p))
      (AdjoinRoot ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p -
        Polynomial.C RatFunc.X)) = p :=
  ratFunc_prime_coordinate_quotient_finrank (ZMod p) p

lemma ratFunc_kronecker_factors_coprime
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    IsCoprime ((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p))
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X) := by
  apply IsCoprime.symm
  apply (ratFunc_prime_coordinate_polynomial_irreducible K p hp).coprime_iff_not_dvd.mpr
  intro hdiv
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv
    (Polynomial.X_sub_C_ne_zero ((RatFunc.X : RatFunc K)^p))
  rw [Polynomial.natDegree_X_pow_sub_C,Polynomial.natDegree_X_sub_C] at hdeg
  exact (Nat.not_le_of_gt hp.one_lt) hdeg

lemma ratFunc_kronecker_product_squarefree
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    Squarefree (((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)) := by
  apply squarefree_mul_iff.mpr
  exact ⟨(ratFunc_kronecker_factors_coprime K p hp).isRelPrime,
    (Polynomial.prime_X_sub_C ((RatFunc.X : RatFunc K)^p)).irreducible.squarefree,
    (ratFunc_prime_coordinate_polynomial_irreducible K p hp).squarefree⟩

lemma ratFunc_kronecker_quotient_reduced
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    IsReduced (AdjoinRoot (((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X))) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact isRadical_iff_span_singleton.mp
    (ratFunc_kronecker_product_squarefree K p hp).isRadical

lemma ratFunc_kronecker_quotient_finrank
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    Module.finrank (RatFunc K)
      (AdjoinRoot (((Polynomial.X : Polynomial (RatFunc K)) -
        Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
        ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X))) = p+1 := by
  calc
    _ = (((Polynomial.X : Polynomial (RatFunc K)) -
        Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
        ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)).natDegree :=
      finrank_quotient_span_eq_natDegree
    _ = p+1 := by
      rw [Polynomial.natDegree_mul
      (Polynomial.X_sub_C_ne_zero ((RatFunc.X : RatFunc K)^p))
      (Polynomial.X_pow_sub_C_ne_zero hp.pos RatFunc.X),
    Polynomial.natDegree_X_sub_C,Polynomial.natDegree_X_pow_sub_C,Nat.add_comm]


/-- A separable extension cannot create a missing p-th root in characteristic p. -/
lemma separable_extension_not_prime_power
    (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    (p : ℕ) [ExpChar K p] (a : K) (ha : ∀ b : K, b^p ≠ a) (u : E) :
    u^p ≠ algebraMap K E a := by
  intro heq
  have hadj : IntermediateField.adjoin K {u} = ⊥ := by
    rw [IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' K E u p]
    exact IntermediateField.adjoin_simple_eq_bot_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨a,heq.symm⟩)
  obtain ⟨b,hb⟩ := IntermediateField.mem_bot.mp
    (IntermediateField.adjoin_simple_eq_bot_iff.mp hadj)
  apply ha b
  apply (algebraMap K E).injective
  rw [map_pow,hb]
  exact heq

lemma ratFunc_coordinate_not_prime_power_in_separable_extension
    (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E]
    (p : ℕ) [ExpChar (RatFunc K) p] (hp : p.Prime) (u : E) :
    u^p ≠ algebraMap (RatFunc K) E RatFunc.X :=
  separable_extension_not_prime_power (RatFunc K) E p RatFunc.X
    (ratFunc_coordinate_not_prime_power K p hp) u

lemma ratFunc_prime_coordinate_irreducible_in_separable_extension
    (K E : Type*) [Field K] [Field E] [Algebra (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E]
    (p : ℕ) [ExpChar (RatFunc K) p] (hp : p.Prime) :
    Irreducible ((Polynomial.X : Polynomial E)^p -
      Polynomial.C (algebraMap (RatFunc K) E RatFunc.X)) :=
  _root_.X_pow_sub_C_irreducible_of_prime hp
    (ratFunc_coordinate_not_prime_power_in_separable_extension K E p hp)

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalPrimeModularPolynomialModFraction_ratFunc
    (p : ℕ) [Fact p.Prime] :
    (lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p).map
      ((RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm.toRingHom) =
      ((Polynomial.X : Polynomial (RatFunc (ZMod p))) -
        Polynomial.C ((RatFunc.X : RatFunc (ZMod p))^p)) *
      ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p - Polynomial.C RatFunc.X) := by
  have hx : (RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm.toRingHom
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) =
      (RatFunc.X : RatFunc (ZMod p)) := by
    change RatFunc.ofFractionRing
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) = _
    rw [RatFunc.ofFractionRing_algebraMap,RatFunc.algebraMap_X]
  rw [lpsOriginalModularPolynomialModFraction,← Polynomial.map_map,
    lpsOriginalPrimeIntegerPolynomial_Kronecker]
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    Polynomial.map_pow,map_pow,hx]

lemma lpsOriginalPrimeModularPolynomialModFraction_squarefree
    (p : ℕ) [Fact p.Prime] :
    Squarefree (lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p) := by
  let e : Polynomial (FractionRing (Polynomial (ZMod p))) ≃+*
      Polynomial (RatFunc (ZMod p)) := Polynomial.mapEquiv (RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm
  have hs : Squarefree (e
      (lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p)) := by
    change Squarefree ((lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p).map
      (RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm.toRingHom)
    rw [lpsOriginalPrimeModularPolynomialModFraction_ratFunc]
    exact QEC.Coding.AlgebraicGeometry.ratFunc_kronecker_product_squarefree (ZMod p) p Fact.out
  intro x hx
  apply (MulEquiv.isUnit_map e).mp
  apply hs (e x)
  simpa only [map_mul] using map_dvd e hx

/-- The actual bad-level prime residue polynomial is squarefree, although inseparable. -/
lemma lpsOriginalPrimeGaussPolynomial_residue_squarefree
    (p : ℕ) [Fact p.Prime] :
    Squarefree ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p))) := by
  let e := Polynomial.mapEquiv (lpsOriginalGaussResidueEquiv p)
  have hs : Squarefree (e ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p)))) := by
    change Squarefree (((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p))).map (lpsOriginalGaussResidueEquiv p).toRingHom)
    rw [lpsOriginalGaussPolynomial_residueDiagram]
    exact lpsOriginalPrimeModularPolynomialModFraction_squarefree p
  intro x hx
  apply (MulEquiv.isUnit_map e).mp
  apply hs (e x)
  simpa only [map_mul] using map_dvd e hx

lemma lpsOriginalPrimeGaussResidueAdjoinRoot_reduced
    (p : ℕ) [Fact p.Prime] :
    IsReduced (AdjoinRoot ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p)))) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact isRadical_iff_span_singleton.mp
    (lpsOriginalPrimeGaussPolynomial_residue_squarefree p).isRadical


/-- The original prime-level Gauss order has a reduced generic special fibre. -/
lemma lpsOriginalPrimeGaussAffineOrder_specialFiber_reduced
    (p : ℕ) [Fact p.Prime] :
    IsReduced (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))) := by
  let := lpsOriginalPrimeGaussResidueAdjoinRoot_reduced p
  let e : (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))) ≃+*
      AdjoinRoot ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
        (IsLocalRing.residue (LPSOriginalGaussBase p))) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p))
      (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p)
  exact isReduced_of_injective e e.injective

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.AlgebraicGeometry
noncomputable section

/-- Reduced closed fibres suffice for a finite domain over a Dedekind domain to be normal.
The local-DVR argument adapts Thomas Browning's Apache-2.0 Mathlib proof in
`Mathlib/RingTheory/Unramified/Dedekind.lean`, using reduced fibres in place of
formal unramifiedness. -/
lemma finite_dedekind_domain_of_reduced_maximal_fibres
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B]
    (hf : ∀ (p : Ideal A) [p.IsMaximal], IsReduced (B ⧸ p.map (algebraMap A B))) :
    IsDedekindDomain B := by
  let : IsDedekindDomainDvr B :=
    { __ := IsNoetherianRing.of_finite A B
      is_dvr_at_nonzero_prime := by
        intro q hq hqp
        let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
        suffices q'.IsPrincipal from
          ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
            (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
        let p := q.under A
        let := Localization.AtPrime.algebraOfLiesOver p q
        have : p.IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
        let : Field (A ⧸ p) := Ideal.Quotient.field p
        have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
        suffices q' = (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) by
          rw [this, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
            IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
            ← Ideal.map_map]
          infer_instance
        rw [← ((Ideal.isRadical_iff_quotient_reduced _).mpr (hf p)).radical,
          IsLocalization.map_radical q.primeCompl,
          IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
          Localization.AtPrime.map_eq_maximalIdeal]
        rw [Ideal.minimalPrimes_eq_comap]
        exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
          IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩ }
  infer_instance

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalPrimeGaussAffineOrder_dedekind
    (p : ℕ) [Fact p.Prime] :
    IsDedekindDomain (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) := by
  let := lpsOriginalGaussBase_dvr p
  let := lpsOriginalGaussAffineOrder_domain p (Fact.out : p.Prime).pos p
  let : Module.Finite (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) :=
    ((lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _).finite_adjoinRoot
  apply QEC.Coding.AlgebraicGeometry.finite_dedekind_domain_of_reduced_maximal_fibres
    (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
  intro m hm
  rw [IsLocalRing.eq_maximalIdeal hm]
  exact lpsOriginalPrimeGaussAffineOrder_specialFiber_reduced p

lemma lpsOriginalPrimeGaussAffineOrder_integrallyClosed
    (p : ℕ) [Fact p.Prime] :
    IsIntegrallyClosed (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) := by
  let := lpsOriginalPrimeGaussAffineOrder_dedekind p
  infer_instance

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalPrimeGaussAffineOrder_isIntegralClosure
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    IsIntegralClosure (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  let := lpsOriginalGaussAffineOrder_domain p (Fact.out : p.Prime).pos p
  let := lpsOriginalGaussAffineGenerated_isFractionRing p (Fact.out : p.Prime).pos p
  let := lpsOriginalPrimeGaussAffineOrder_integrallyClosed p
  let : Module.Finite (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) :=
    ((lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _).finite_adjoinRoot
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := .of_algebraMap_eq' rfl
  infer_instance

def lpsOriginalPrimeGaussNormalizationEquiv
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p ≃ₐ[LPSOriginalGaussBase p]
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  letI : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := .of_algebraMap_eq' rfl
  letI := lpsOriginalPrimeGaussAffineOrder_isIntegralClosure p
  exact IsIntegralClosure.equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))

lemma lpsOriginalPrimeGaussNormalizationEquiv_root
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    ((lpsOriginalPrimeGaussNormalizationEquiv p
      (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))).val.val) =
      lpsOriginalJNInFractionField p (Fact.out : p.Prime).pos := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := .of_algebraMap_eq' rfl
  let := lpsOriginalPrimeGaussAffineOrder_isIntegralClosure p
  have he := IsIntegralClosure.algebraMap_equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))
    (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))
  change (lpsOriginalPrimeGaussNormalizationEquiv p
    (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))).val = _ at he
  exact (congrArg Subtype.val he).trans (lpsOriginalGaussAffineToGenerated_root p (Fact.out : p.Prime).pos p)

end
end QEC.Coding.TannerLiftedProduct

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

/-- The same actual prime-level normalization retains a reduced generic special fibre. -/
lemma lpsOriginalPrimeGaussNormalization_specialFiber_reduced
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    letI : CommRing (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) := inferInstance
    letI : Ring (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) := CommRing.toRing
    letI : Semiring (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) :=
      (inferInstance : CommRing (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))).toCommSemiring.toSemiring
    IsReduced (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (integralClosure (LPSOriginalGaussBase p)
            (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p)
        (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p
  let D := integralClosure A (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)
  let : CommRing D := inferInstance
  let : Ring D := CommRing.toRing
  let : Semiring D := (inferInstance : CommRing D).toCommSemiring.toSemiring
  let m := IsLocalRing.maximalIdeal A
  let e : B ≃ₐ[A] D := lpsOriginalPrimeGaussNormalizationEquiv p
  have he : e.toRingHom.comp (algebraMap A B) = algebraMap A D := by
    apply RingHom.ext
    exact e.commutes
  have hi : m.map (algebraMap A D) =
      (m.map (algebraMap A B)).map e.toRingHom := by
    rw [Ideal.map_map,he]
  let q : B ⧸ m.map (algebraMap A B) ≃+* D ⧸ m.map (algebraMap A D) :=
    Ideal.quotientEquiv _ _ e.toRingEquiv hi
  let := lpsOriginalPrimeGaussAffineOrder_specialFiber_reduced p
  exact isReduced_of_injective q.symm q.symm.injective

end
end QEC.Coding.TannerLiftedProduct
