import QEC.Coding.Core.Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# The full-length prime-field Reed--Solomon layer used by KT19

This file formalizes the concrete full evaluation code over `ZMod p`.  The
coordinate set is the field itself.  Thus the code is the image of genuine
polynomial evaluation, rather than a record carrying dimension, duality, or
product facts as fields.

The companion puncturing and shortening construction is deliberately kept in
`KT19PuncturedReedSolomon`.
-/

noncomputable section

namespace QEC
namespace Coding
namespace KT19ReedSolomon

open scoped BigOperators

/-- The source-side admissibility inequalities for the KT19 prime-field
family.  The non-strict product inequality is the corrected project contract
for the source theorem. -/
def Admissible (p l k : Nat) : Prop :=
  Nat.Prime p ∧ 1 ≤ k ∧ k ≤ l ∧ l ≤ p ∧ 3 * l ≤ p + 1

/-- Evaluate a polynomial at every element of the prime field. -/
def evaluationMap (p : Nat) (polynomial : Polynomial (ZMod p)) :
    Word (ZMod p) (ZMod p) :=
  fun point => polynomial.eval point

/-- Evaluation restricted to polynomials of degree strictly less than `l`. -/
def evaluationLinearMap (p l : Nat) :
    Polynomial.degreeLT (ZMod p) l →ₗ[ZMod p] Word (ZMod p) (ZMod p) where
  toFun polynomial := evaluationMap p polynomial.1
  map_add' left right := by
    funext point
    simp [evaluationMap]
  map_smul' scalar polynomial := by
    funext point
    simp [evaluationMap, Algebra.smul_def]

@[simp]
theorem evaluationLinearMap_apply (p l : Nat)
    (polynomial : Polynomial.degreeLT (ZMod p) l) (point : ZMod p) :
    evaluationLinearMap p l polynomial point = polynomial.1.eval point :=
  rfl

/-- Evaluation commutes with polynomial multiplication, coordinate by
coordinate. -/
def coordinatewiseProduct {p : Nat}
    (left right : Word (ZMod p) (ZMod p)) : Word (ZMod p) (ZMod p) :=
  fun point => left point * right point

theorem evaluationMap_mul (p : Nat)
    (left right : Polynomial (ZMod p)) :
    evaluationMap p (left * right) =
      coordinatewiseProduct (evaluationMap p left) (evaluationMap p right) := by
  funext point
  simp [evaluationMap, coordinatewiseProduct]

/-- A product of degree-bounded polynomials has the expected strict degree
bound.  This is the algebraic input behind codeword-product containment. -/
private theorem mul_mem_degreeLT (p l m : Nat) [Fact p.Prime]
    (left : Polynomial.degreeLT (ZMod p) l)
    (right : Polynomial.degreeLT (ZMod p) m) :
    left.1 * right.1 ∈ Polynomial.degreeLT (ZMod p) (l + m - 1) := by
  by_cases hleft : left.1 = 0
  · simp [hleft]
  by_cases hright : right.1 = 0
  · simp [hright]
  have hleftDegree : left.1.natDegree < l := by
    have hdegree := Polynomial.mem_degreeLT.mp left.2
    rw [Polynomial.degree_eq_natDegree hleft] at hdegree
    exact_mod_cast hdegree
  have hrightDegree : right.1.natDegree < m := by
    have hdegree := Polynomial.mem_degreeLT.mp right.2
    rw [Polynomial.degree_eq_natDegree hright] at hdegree
    exact_mod_cast hdegree
  rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree (mul_ne_zero hleft hright),
    Polynomial.natDegree_mul hleft hright]
  exact_mod_cast (show left.1.natDegree + right.1.natDegree < l + m - 1 by omega)

/-- Evaluation on all `p` field points is injective below degree `p`. -/
theorem evaluationLinearMap_injective (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) : Function.Injective (evaluationLinearMap p l) := by
  intro left right hevaluation
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (Finset.univ : Finset (ZMod p))
  · have hdegree := Polynomial.mem_degreeLT.mp left.2
    exact hdegree.trans_le (by simpa [ZMod.card] using hlp)
  · have hdegree := Polynomial.mem_degreeLT.mp right.2
    exact hdegree.trans_le (by simpa [ZMod.card] using hlp)
  · intro point _
    exact congrFun hevaluation point

/-- Full-length interpolation: evaluation of degree-`< p` polynomials is a
linear equivalence onto all words indexed by `ZMod p`. -/
noncomputable def fullEvaluationLinearEquiv (p : Nat) [Fact p.Prime] :
    Polynomial.degreeLT (ZMod p) p ≃ₗ[ZMod p] Word (ZMod p) (ZMod p) := by
  apply LinearEquiv.ofBijective (evaluationLinearMap p p)
  refine ⟨evaluationLinearMap_injective p p le_rfl, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
  · exact evaluationLinearMap_injective p p le_rfl
  · rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis (ZMod p) p),
      Fintype.card_fin, Module.finrank_fintype_fun_eq_card, ZMod.card]

/-- The concrete full-length Reed--Solomon code. -/
def reedSolomonCode (p l : Nat) [Fact p.Prime] : LinearCode (ZMod p) (ZMod p) where
  carrier := LinearMap.range (evaluationLinearMap p l)

@[simp]
theorem mem_reedSolomonCode (p l : Nat) [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) :
    word ∈ (reedSolomonCode p l).carrier ↔
      ∃ polynomial : Polynomial.degreeLT (ZMod p) l,
        evaluationLinearMap p l polynomial = word := by
  simp [reedSolomonCode]

/-- Every bounded polynomial evaluation is a codeword. -/
theorem evaluation_mem_reedSolomonCode (p l : Nat) [Fact p.Prime]
    (polynomial : Polynomial.degreeLT (ZMod p) l) :
    evaluationLinearMap p l polynomial ∈ (reedSolomonCode p l).carrier :=
  (mem_reedSolomonCode p l _).2 ⟨polynomial, rfl⟩

/-- The dimension of the actual evaluation code is the number of independent
coefficients, whenever its degree bound fits in the field. -/
theorem reedSolomonCode_dimension (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) : Dimension (reedSolomonCode p l) = l := by
  change Module.finrank (ZMod p) (LinearMap.range (evaluationLinearMap p l)) = l
  rw [LinearMap.finrank_range_of_inj (evaluationLinearMap_injective p l hlp),
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis (ZMod p) l), Fintype.card_fin]

/-- The span of coordinatewise products of codewords.  This is defined from
the actual products, not from a claimed degree or duality parameter. -/
def coordinatewiseProductCode {p : Nat} [Fact p.Prime]
    (left right : LinearCode (ZMod p) (ZMod p)) : LinearCode (ZMod p) (ZMod p) where
  carrier := Submodule.span (ZMod p)
    {word | ∃ x ∈ left.carrier, ∃ y ∈ right.carrier,
      coordinatewiseProduct x y = word}

/-- Products of evaluations have the evaluation of the polynomial product. -/
private theorem evaluationLinearMap_mul (p l m : Nat) [Fact p.Prime]
    (left : Polynomial.degreeLT (ZMod p) l)
    (right : Polynomial.degreeLT (ZMod p) m) :
    coordinatewiseProduct (evaluationLinearMap p l left) (evaluationLinearMap p m right) =
      evaluationLinearMap p (l + m - 1) ⟨left.1 * right.1,
        mul_mem_degreeLT p l m left right⟩ := by
  funext point
  simp [coordinatewiseProduct, evaluationMap]

/-- The degree calculation gives containment of the actual product code in a
larger Reed--Solomon evaluation code. -/
theorem reedSolomonCode_product_le (p l m : Nat) [Fact p.Prime] :
    (coordinatewiseProductCode (reedSolomonCode p l) (reedSolomonCode p m)).carrier ≤
      (reedSolomonCode p (l + m - 1)).carrier := by
  rw [coordinatewiseProductCode]
  apply Submodule.span_le.2
  rintro word ⟨x, hx, y, hy, rfl⟩
  rcases (mem_reedSolomonCode p l x).1 hx with ⟨left, rfl⟩
  rcases (mem_reedSolomonCode p m y).1 hy with ⟨right, rfl⟩
  rw [evaluationLinearMap_mul]
  exact evaluation_mem_reedSolomonCode p (l + m - 1) _

/-- Sums of evaluations of polynomials of degree below `p - 1` vanish over
the whole prime field.  The proof expands the polynomial in the canonical
degree-LT coefficient equivalence and applies Mathlib's finite-field power
sum theorem termwise. -/
private theorem sum_evaluation_eq_zero (p : Nat) [Fact p.Prime]
    (polynomial : Polynomial.degreeLT (ZMod p) (p - 1)) :
    ∑ point : ZMod p, polynomial.1.eval point = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_degreeLTEquiv polynomial.2]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro exponent _
  rw [← Finset.mul_sum]
  have hsum : ∑ point : ZMod p, point ^ (exponent : Nat) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) (exponent : Nat)
      (by simpa [ZMod.card] using exponent.isLt)
  rw [hsum, mul_zero]

/-- Complementary degree bounds are orthogonal under the literal dot product
on all prime-field coordinates. -/
private theorem reedSolomonCode_le_dual_complementary (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) :
    (reedSolomonCode p (p - l)).carrier ≤ (reedSolomonCode p l).dual.carrier := by
  intro word hword
  refine ((reedSolomonCode p l).mem_dual word).2 ?_
  intro other hother
  rcases (mem_reedSolomonCode p (p - l) word).1 hword with ⟨left, rfl⟩
  rcases (mem_reedSolomonCode p l other).1 hother with ⟨right, rfl⟩
  rw [wordPairing_apply]
  change ∑ point : ZMod p,
    coordinatewiseProduct (evaluationLinearMap p (p - l) left)
      (evaluationLinearMap p l right) point = 0
  rw [evaluationLinearMap_mul p (p - l) l left right]
  have hbound : p - l + l - 1 = p - 1 := by omega
  let product : Polynomial.degreeLT (ZMod p) (p - 1) :=
    ⟨left.1 * right.1, by
      rw [← hbound]
      exact mul_mem_degreeLT p (p - l) l left right⟩
  change ∑ point : ZMod p, (left.1 * right.1).eval point = 0
  exact sum_evaluation_eq_zero p product

/-- The Euclidean dual of the full-length degree-`< l` code is exactly the
degree-`< p-l` full-length Reed--Solomon code. -/
theorem reedSolomonCode_dual (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) :
    (reedSolomonCode p l).dual.carrier = (reedSolomonCode p (p - l)).carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact reedSolomonCode_le_dual_complementary p l hlp
  · change Dimension (reedSolomonCode p (p - l)) = Dimension (reedSolomonCode p l).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      reedSolomonCode_dimension p l hlp,
      reedSolomonCode_dimension p (p - l) (Nat.sub_le _ _)]
    change p - l = Fintype.card (ZMod p) - l
    simp [ZMod.card]

/-- The source-correct product condition implies that the product of the
degree-`< l` code lies in its exact Euclidean dual. -/
theorem reedSolomonCode_product_le_dual (p l : Nat) [Fact p.Prime]
    (hproduct : 3 * l ≤ p + 1) :
    (coordinatewiseProductCode (reedSolomonCode p l) (reedSolomonCode p l)).carrier ≤
      (reedSolomonCode p l).dual.carrier := by
  rw [reedSolomonCode_dual p l (by omega)]
  refine (reedSolomonCode_product_le p l l).trans ?_
  have hdegree : l + l - 1 ≤ p - l := by omega
  intro word hword
  rcases (mem_reedSolomonCode p (l + l - 1) word).1 hword with ⟨polynomial, rfl⟩
  exact evaluation_mem_reedSolomonCode p (p - l)
    ⟨polynomial.1, Polynomial.mem_degreeLT.mpr
      ((Polynomial.mem_degreeLT.mp polynomial.2).trans_le (by exact_mod_cast hdegree))⟩

end KT19ReedSolomon
end Coding
end QEC
