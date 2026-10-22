import QEC.Coding.ExpanderCodes.LPSOriginalPrimeIntegralHeckeRelation
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Original relative prime modular polynomial

For 4 ∣ N and p coprime to N, the literal integer modular polynomial evaluated
at the SAME original j_N is the minimal polynomial of actual j_Np over
Q(j,j_N). Its degree is p+1. The canonical AdjoinRoot presentation retains
both the actual root coordinate and every lower-level field coefficient.
The minimal-polynomial identity follows from the proved analytic Hecke root
and actual relative field degree; neither conclusion is an input hypothesis.

These are internal derived prerequisites of the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (lines484–486). They are not separately
stated public claims of that passage. The exact public th:qLDPC (lines231–238),
node pk-good-qldpc and parent issue449 remain unproved. No special-fibre
multiplicity/cycle identity, smooth good reduction, Weil/spectral estimate or
arbitrary-finite-field/every-rate explicit quantum family is proved here.
-/
namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalPrimeProductJN_minpoly_natDegree
    (N p : ℕ) [NeZero N] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (minpoly (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalJNInFractionField (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos))).natDegree = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  have hl := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have he : (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) = (minpoly K x).natDegree := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hl]
    change Module.finrank K (IntermediateField.extendScalars
      (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from hl)) = _
    rw [IntermediateField.extendScalars_adjoin]
    exact IntermediateField.adjoin.finrank hx
  exact he.symm.trans (lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN)

def lpsOriginalPrimeRelativeCoefficientMap (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalIntegerNormalJN N hN).val

def lpsOriginalPrimeRelativeModularPolynomial
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerPolynomial p hp).map
    (lpsOriginalPrimeRelativeCoefficientMap N hN)

lemma lpsOriginalPrimeRelativeModularPolynomial_monic
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalPrimeRelativeModularPolynomial N p hN hp).Monic := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerPolynomial_monic p hp).map _

lemma lpsOriginalPrimeRelativeCoefficientMap_ambient
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).val.toRingHom.comp
      (lpsOriginalPrimeRelativeCoefficientMap N hN) =
      lpsOriginalJNIntegerFractionEval N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    have hz : Polynomial.C z = (z : Polynomial ℤ) := by simp
    rw [hz, map_intCast, map_intCast]
  · simp only [RingHom.comp_apply, lpsOriginalPrimeRelativeCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [lpsOriginalJNIntegerFractionEval_X]
    exact lpsOriginalIntegerNormalJN_coe N hN

lemma lpsOriginalPrimeRelativeModularPolynomial_root
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalPrimeRelativeModularPolynomial N p hN hp) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [Polynomial.aeval_def, lpsOriginalPrimeRelativeModularPolynomial,
    Polynomial.eval₂_map]
  change (lpsOriginalIntegerPolynomial p hp).eval₂
    ((lpsOriginalGeneratedFunctionFieldQ N hN).val.toRingHom.comp
      (lpsOriginalPrimeRelativeCoefficientMap N hN))
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0
  rw [lpsOriginalPrimeRelativeCoefficientMap_ambient,
    lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot]

lemma lpsOriginalPrimeRelativeModularPolynomial_natDegree
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos).natDegree = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (lpsOriginalPrimeRelativeCoefficientMap N hN)).natDegree = _
  rw [(lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).natDegree_map,
    lpsOriginalPrimeIntegerPolynomial_degree]

lemma lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalPrimeRelativeModularPolynomial N p hN (Fact.out : p.Prime).pos =
      minpoly (lpsOriginalGeneratedFunctionFieldQ N hN)
        (lpsOriginalJNInFractionField (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx)
    (lpsOriginalPrimeRelativeModularPolynomial_monic N p hN (Fact.out : p.Prime).pos)
    (minpoly.dvd K x (lpsOriginalPrimeRelativeModularPolynomial_root N p hN
      (Fact.out : p.Prime).pos))
  rw [lpsOriginalPrimeRelativeModularPolynomial_natDegree,
    lpsOriginalPrimeProductJN_minpoly_natDegree N p hNp h4N hN]

lemma lpsOriginalPrimeRelativeModularPolynomial_irreducible
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Irreducible (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN]
  exact minpoly.irreducible ((lpsOriginalJNInFractionField_integralQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top)

/-- Canonical original relative field presentation; not an abstract replacement field. -/
def lpsOriginalPrimeRelativeAdjoinRootEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos) ≃+*
        lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  let h := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p) (dvd_mul_right N p)
    h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  change AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
    (Fact.out : p.Prime).pos) ≃+* IntermediateField.extendScalars
      (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from h)
  exact ((AdjoinRoot.algEquivOfEq K _ _
    (lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN)).trans
    ((IntermediateField.adjoinRootEquivAdjoin K hx).trans
      (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin
        (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from h)).symm))).toRingEquiv

lemma lpsOriginalPrimeRelativeAdjoinRootEquiv_root_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
      (AdjoinRoot.root (lpsOriginalPrimeRelativeModularPolynomial N p hN
        (Fact.out : p.Prime).pos)) : lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :
            LPSOriginalHolomorphicFractionField) =
      lpsOriginalJNInFractionField (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  let h := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p) (dvd_mul_right N p)
    h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  change ((IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin
      (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from h)).symm)
    ((IntermediateField.adjoinRootEquivAdjoin K hx)
      ((AdjoinRoot.algEquivOfEq K _ _
        (lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN))
        (AdjoinRoot.root _))) : LPSOriginalHolomorphicFractionField) = x
  rw [AdjoinRoot.algEquivOfEq_root, IntermediateField.adjoinRootEquivAdjoin_apply_root]
  rfl

/-- Generic coefficient identity for the canonical simple-extension presentation. -/
lemma lpsOriginalRelativeAdjoinRootPresentation_base_coe
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : E)
    (h : K ≤ IntermediateField.adjoin F {x}) (P : Polynomial K)
    (hP : P = minpoly K x) (hx : IsIntegral K x) (c : K) :
    (((AdjoinRoot.algEquivOfEq K P _ hP).trans
      ((IntermediateField.adjoinRootEquivAdjoin K hx).trans
        (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin h).symm))).toRingEquiv
      (algebraMap K (AdjoinRoot P) c) : E) = c := by
  change (((AdjoinRoot.algEquivOfEq K P _ hP).trans
      ((IntermediateField.adjoinRootEquivAdjoin K hx).trans
        (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin h).symm)))
      (algebraMap K (AdjoinRoot P) c) : E) = c
  rw [AlgEquiv.commutes]
  rfl

/-- The presentation sends every lower-level field coefficient to its actual inclusion. -/
lemma lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ c : lpsOriginalGeneratedFunctionFieldQ N hN,
    ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
      (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
        (AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
          (Fact.out : p.Prime).pos)) c) : lpsOriginalGeneratedFunctionFieldQ (N*p)
            (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :
              LPSOriginalHolomorphicFractionField) = c := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro c
  exact lpsOriginalRelativeAdjoinRootPresentation_base_coe
    (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    (lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p) (dvd_mul_right N p)
      h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    (lpsOriginalPrimeRelativeModularPolynomial N p hN (Fact.out : p.Prime).pos)
    (lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN)
    ((lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top) c

end
end QEC.Coding.TannerLiftedProduct
