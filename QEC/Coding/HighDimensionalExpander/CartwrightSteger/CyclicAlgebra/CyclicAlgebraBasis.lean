import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.InfinityLattice
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.Core

/-!
# A construction-owned basis of the Cartwright--Steger cyclic algebra

The matrices `e_i z^k`, where `e_i` runs through the fixed constant-field
basis and `0 ≤ k < d`, form an `F_q(y)`-basis of the constructed cyclic
algebra.  This file proves linear independence, the Frobenius-twisted
multiplication law including the carry factor `1+y`, closure of their span,
and containment of every generator used by `Algebra.adjoin` (including
`z⁻¹`).  Thus the spanning result does not assume a cyclic presentation.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def functionFieldCyclicBasisVector
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    CyclicAlgebra P r :=
  ⟨splittingCyclicBasisVector P r p,
    (CyclicAlgebra P r).mul_mem
      (constantMatrix_mem_cyclicAlgebra P r (constantBasis P r p.1))
      ((CyclicAlgebra P r).pow_mem
        (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) p.2)⟩

@[simp] theorem functionFieldCyclicBasisVector_coe
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (functionFieldCyclicBasisVector P r p :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) =
      splittingCyclicBasisVector P r p := rfl

theorem functionFieldCyclicBasisVector_linearIndependent
    (P : BasePrime) (r : Rank) :
    LinearIndependent (FunctionField P)
      (functionFieldCyclicBasisVector P r) := by
  apply LinearIndependent.of_comp (CyclicAlgebra P r).val.toLinearMap
  exact
    (splittingCyclicBasisVector_linearIndependent P r).restrict_scalars
      (show Function.Injective (fun a : FunctionField P =>
          a • (1 : SplittingFunctionField P r)) by
        intro a b h
        have hab : a = b := by simpa [Algebra.smul_def] using h
        apply functionFieldEmbedding_injective P r
        exact congrArg (functionFieldEmbedding P r) hab)

noncomputable def functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    Submodule (FunctionField P) (CyclicAlgebra P r) :=
  Submodule.span (FunctionField P)
    (Set.range (functionFieldCyclicBasisVector P r))

theorem functionFieldEmbedding_C
    (P : BasePrime) (r : Rank) (a : BaseField P) :
    functionFieldEmbedding P r (RatFunc.C a) =
      RatFunc.C (algebraMap (BaseField P) (ConstantExtension P r) a) := by
  rw [show (RatFunc.C a : FunctionField P) =
      algebraMap (PolynomialRing P) (FunctionField P) (Polynomial.C a) /
        algebraMap (PolynomialRing P) (FunctionField P) 1 by simp,
    show (RatFunc.C (algebraMap (BaseField P) (ConstantExtension P r) a) :
        SplittingFunctionField P r) =
      algebraMap (Polynomial (ConstantExtension P r))
          (SplittingFunctionField P r)
          (Polynomial.C (algebraMap (BaseField P) (ConstantExtension P r) a)) /
        algebraMap (Polynomial (ConstantExtension P r))
          (SplittingFunctionField P r) 1 by simp]
  unfold functionFieldEmbedding
  dsimp only
  rw [RatFunc.coe_mapRingHom_eq_coe_map]
  rw [RatFunc.map_apply_div]
  simp

theorem constantMatrix_baseField_smul_functionField
    (P : BasePrime) (r : Rank) (a : BaseField P)
    (c : ConstantExtension P r) :
    constantMatrix P r (a • c) =
      (algebraMap (BaseField P) (FunctionField P) a) •
        constantMatrix P r c := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [constantMatrix, Algebra.smul_def]
    left
    have hfix (n : ℕ) :
        ((⇑(constantFrobenius P r).symm)^[n])
            (algebraMap (BaseField P) (ConstantExtension P r) a) =
          algebraMap (BaseField P) (ConstantExtension P r) a := by
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply,
            (constantFrobenius P r).symm.commutes a, ih]
    rw [hfix i]
    exact (functionFieldEmbedding_C P r a).symm
  · simp [constantMatrix, hij, Algebra.smul_def]

/-- Expansion of a constant cyclic monomial in the fixed function-field
cyclic basis. -/
theorem constantCyclicMonomial_eq_sum_basis
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) =
      ∑ j, algebraMap (BaseField P) (FunctionField P)
          ((constantBasis P r).repr c j) •
            functionFieldCyclicBasisVector P r (j, ⟨k, hk⟩) := by
  apply Subtype.ext
  change constantMatrix P r c * cyclicGeneratorMatrix P r ^ k =
    (CyclicAlgebra P r).val
      (∑ j, algebraMap (BaseField P) (FunctionField P)
        ((constantBasis P r).repr c j) •
          functionFieldCyclicBasisVector P r (j, ⟨k, hk⟩))
  rw [map_sum]
  simp only [map_smul]
  conv_lhs => rw [← (constantBasis P r).sum_repr c]
  rw [← constantMatrixEmbedding_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [constantMatrixEmbedding_apply,
    constantMatrix_baseField_smul_functionField, smul_mul_assoc]
  rfl

theorem constantCyclicMonomial_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    ⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
      (CyclicAlgebra P r).mul_mem
        (constantMatrix_mem_cyclicAlgebra P r c)
        ((CyclicAlgebra P r).pow_mem
          (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ ∈
      functionFieldCyclicSpan P r := by
  rw [constantCyclicMonomial_eq_sum_basis P r c k hk]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(j, ⟨k, hk⟩), rfl⟩

theorem onePlusY_eq_functionField_smul_one
    (P : BasePrime) (r : Rank) :
    onePlusY P r =
      (algebraMap (FunctionField P) (SplittingFunctionField P r)
        (1 + RatFunc.X)) • (1 : SplittingFunctionField P r) := by
  change 1 + RatFunc.X = functionFieldEmbedding P r (1 + RatFunc.X) * 1
  rw [map_add, map_one, functionFieldEmbedding_X]
  simp

/-- Frobenius-twisted product of two constant cyclic monomials, before
reducing the exponent modulo the matrix rank. -/
theorem constantCyclicMonomial_mul_eq
    (P : BasePrime) (r : Rank)
    (c d : ConstantExtension P r) (k l : ℕ) :
    (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) *
        (constantMatrix P r d * cyclicGeneratorMatrix P r ^ l) =
      constantMatrix P r (c * (constantFrobenius P r ^ k) d) *
        cyclicGeneratorMatrix P r ^ (k + l) := by
  calc
    _ = constantMatrix P r c *
        (cyclicGeneratorMatrix P r ^ k * constantMatrix P r d) *
        cyclicGeneratorMatrix P r ^ l := by group
    _ = constantMatrix P r c *
        (constantMatrix P r ((constantFrobenius P r ^ k) d) *
          cyclicGeneratorMatrix P r ^ k) *
        cyclicGeneratorMatrix P r ^ l := by
          rw [cyclicGeneratorMatrix_pow_mul_constantMatrix]
    _ = (constantMatrix P r c *
        constantMatrix P r ((constantFrobenius P r ^ k) d)) *
        (cyclicGeneratorMatrix P r ^ k *
          cyclicGeneratorMatrix P r ^ l) := by group
    _ = _ := by
      change (constantMatrixEmbedding P r c *
          constantMatrixEmbedding P r ((constantFrobenius P r ^ k) d)) *
          (cyclicGeneratorMatrix P r ^ k *
            cyclicGeneratorMatrix P r ^ l) = _
      rw [← map_mul, ← pow_add]
      rfl

theorem constantCyclicMonomial_mul_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank)
    (c d : ConstantExtension P r)
    (k l : ℕ) (hk : k < r.matrixRank) (hl : l < r.matrixRank) :
    (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r c)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
      CyclicAlgebra P r) *
      ⟨constantMatrix P r d * cyclicGeneratorMatrix P r ^ l,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r d)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) l)⟩ ∈
        functionFieldCyclicSpan P r := by
  let e : ConstantExtension P r :=
    c * (constantFrobenius P r ^ k) d
  have hproduct :
      (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) *
          (constantMatrix P r d * cyclicGeneratorMatrix P r ^ l) =
        constantMatrix P r e * cyclicGeneratorMatrix P r ^ (k + l) :=
    constantCyclicMonomial_mul_eq P r c d k l
  by_cases hsum : k + l < r.matrixRank
  · have hmem := constantCyclicMonomial_mem_functionFieldCyclicSpan
      P r e (k + l) hsum
    have heq :
        (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r c)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
          CyclicAlgebra P r) *
          ⟨constantMatrix P r d * cyclicGeneratorMatrix P r ^ l,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r d)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) l)⟩ =
        ⟨constantMatrix P r e * cyclicGeneratorMatrix P r ^ (k + l),
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r e)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) (k + l))⟩ := by
      apply Subtype.ext
      exact hproduct
    rw [heq]
    exact hmem
  · have hrank : 0 < r.matrixRank :=
      lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
    let j := k + l - r.matrixRank
    have hj : j < r.matrixRank := by omega
    have hsumEq : k + l = r.matrixRank + j := by omega
    let a : FunctionField P := 1 + RatFunc.X
    have hmatrix : constantMatrix P r e *
          cyclicGeneratorMatrix P r ^ (k + l) =
        a • (constantMatrix P r e * cyclicGeneratorMatrix P r ^ j) := by
      rw [hsumEq, cyclicGeneratorMatrix_pow_rank_add]
      rw [Matrix.mul_smul]
      rw [onePlusY_eq_functionField_smul_one]
      simp only [a, Algebra.smul_def, map_add, map_one]
      congr 1
      rw [IsScalarTower.algebraMap_apply
        (FunctionField P) (SplittingFunctionField P r)
        (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r))]
      simp
    have hmem := constantCyclicMonomial_mem_functionFieldCyclicSpan
      P r e j hj
    have hscalarMem := (functionFieldCyclicSpan P r).smul_mem a hmem
    have heq :
        (⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ k,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r c)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) k)⟩ :
          CyclicAlgebra P r) *
          ⟨constantMatrix P r d * cyclicGeneratorMatrix P r ^ l,
            (CyclicAlgebra P r).mul_mem
              (constantMatrix_mem_cyclicAlgebra P r d)
              ((CyclicAlgebra P r).pow_mem
                (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) l)⟩ =
        a • ⟨constantMatrix P r e * cyclicGeneratorMatrix P r ^ j,
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r e)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) j)⟩ := by
      apply Subtype.ext
      exact hproduct.trans hmatrix
    rw [heq]
    exact hscalarMem

theorem functionFieldCyclicSpan_mul_mem
    (P : BasePrime) (r : Rank) (x y : CyclicAlgebra P r)
    (hx : x ∈ functionFieldCyclicSpan P r)
    (hy : y ∈ functionFieldCyclicSpan P r) :
    x * y ∈ functionFieldCyclicSpan P r := by
  let S := functionFieldCyclicSpan P r
  refine Submodule.span_induction
    (p := fun x _ => ∀ y, y ∈ S → x * y ∈ S)
    ?basisX ?zeroX ?addX ?smulX hx y hy
  · intro x hxRange
    obtain ⟨p, rfl⟩ := hxRange
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ => functionFieldCyclicBasisVector P r p * y ∈ S)
      ?basisY ?zeroY ?addY ?smulY hy
    · intro y hyRange
      obtain ⟨q, rfl⟩ := hyRange
      exact constantCyclicMonomial_mul_mem_functionFieldCyclicSpan
        P r (constantBasis P r p.1) (constantBasis P r q.1)
        p.2 q.2 p.2.isLt q.2.isLt
    · simp [S]
    · intro a b _ _ ha hb
      rw [mul_add]
      exact S.add_mem ha hb
    · intro a z _ hz
      rw [mul_smul_comm]
      exact S.smul_mem a hz
  · intro y _
    simp [S]
  · intro a b _ _ ha hb y hy
    rw [add_mul]
    exact S.add_mem (ha y hy) (hb y hy)
  · intro a z _ hz y hy
    rw [smul_mul_assoc]
    exact S.smul_mem a (hz y hy)

theorem one_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    (1 : CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan
    P r 1 0 (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have hone :
      (1 : CyclicAlgebra P r) =
        ⟨constantMatrix P r 1 * cyclicGeneratorMatrix P r ^ 0,
          (CyclicAlgebra P r).mul_mem
            (constantMatrix_mem_cyclicAlgebra P r 1)
            ((CyclicAlgebra P r).pow_mem
              (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 0)⟩ := by
    apply Subtype.ext
    simp [← constantMatrixEmbedding_apply]
  rw [hone]
  exact h

noncomputable def functionFieldCyclicSpanSubalgebra
    (P : BasePrime) (r : Rank) :
    Subalgebra (FunctionField P) (CyclicAlgebra P r) where
  carrier := functionFieldCyclicSpan P r
  zero_mem' := (functionFieldCyclicSpan P r).zero_mem
  one_mem' := one_mem_functionFieldCyclicSpan P r
  add_mem' := (functionFieldCyclicSpan P r).add_mem
  mul_mem' := by
    intro a b ha hb
    exact functionFieldCyclicSpan_mul_mem P r a b ha hb
  algebraMap_mem' a := by
    have h := (functionFieldCyclicSpan P r).smul_mem a
      (one_mem_functionFieldCyclicSpan P r)
    simpa [Algebra.smul_def] using h

theorem constantMatrix_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (⟨constantMatrix P r c, constantMatrix_mem_cyclicAlgebra P r c⟩ :
      CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan P r c 0
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have heq :
      (⟨constantMatrix P r c, constantMatrix_mem_cyclicAlgebra P r c⟩ :
        CyclicAlgebra P r) =
      ⟨constantMatrix P r c * cyclicGeneratorMatrix P r ^ 0,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r c)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 0)⟩ := by
    apply Subtype.ext
    simp
  rw [heq]
  exact h

theorem cyclicGeneratorMatrix_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorMatrix P r,
        cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) ∈
      functionFieldCyclicSpan P r := by
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan P r 1 1
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r))
  have heq :
      (⟨cyclicGeneratorMatrix P r,
        cyclicGeneratorMatrix_mem_cyclicAlgebra P r⟩ : CyclicAlgebra P r) =
      ⟨constantMatrix P r 1 * cyclicGeneratorMatrix P r ^ 1,
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r 1)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) 1)⟩ := by
    apply Subtype.ext
    simp [← constantMatrixEmbedding_apply]
  rw [heq]
  exact h

theorem functionFieldEmbedding_onePlusY
    (P : BasePrime) (r : Rank) :
    functionFieldEmbedding P r (1 + RatFunc.X) = onePlusY P r := by
  rw [map_add, map_one, functionFieldEmbedding_X]
  rfl

theorem onePlusYInv_smul_eq_functionField_smul
    (P : BasePrime) (r : Rank)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    (onePlusY P r)⁻¹ • M =
      ((1 + RatFunc.X : FunctionField P)⁻¹) • M := by
  have hscalar : functionFieldEmbedding P r
      ((1 + RatFunc.X : FunctionField P)⁻¹) = (onePlusY P r)⁻¹ := by
    rw [map_inv₀, functionFieldEmbedding_onePlusY]
  simp only [Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply
    (FunctionField P) (SplittingFunctionField P r)
    (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))]
  change (algebraMap (SplittingFunctionField P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))) (onePlusY P r)⁻¹ =
    (algebraMap (SplittingFunctionField P r)
      (Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)))
      (functionFieldEmbedding P r ((1 + RatFunc.X : FunctionField P)⁻¹))
  rw [hscalar]

theorem cyclicGeneratorInverseMatrix_mem_functionFieldCyclicSpan
    (P : BasePrime) (r : Rank) :
    (⟨cyclicGeneratorInverseMatrix P r,
        cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩ :
      CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r := by
  have hrank : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hpred : r.matrixRank - 1 < r.matrixRank := by omega
  have h := constantCyclicMonomial_mem_functionFieldCyclicSpan P r 1
    (r.matrixRank - 1) hpred
  let a : FunctionField P := (1 + RatFunc.X)⁻¹
  have hsmul := (functionFieldCyclicSpan P r).smul_mem a h
  have heq :
      (⟨cyclicGeneratorInverseMatrix P r,
        cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r⟩ :
        CyclicAlgebra P r) =
      a • ⟨constantMatrix P r 1 *
          cyclicGeneratorMatrix P r ^ (r.matrixRank - 1),
        (CyclicAlgebra P r).mul_mem
          (constantMatrix_mem_cyclicAlgebra P r 1)
          ((CyclicAlgebra P r).pow_mem
            (cyclicGeneratorMatrix_mem_cyclicAlgebra P r)
            (r.matrixRank - 1))⟩ := by
    apply Subtype.ext
    change cyclicGeneratorInverseMatrix P r =
      a • (constantMatrix P r 1 *
        cyclicGeneratorMatrix P r ^ (r.matrixRank - 1))
    calc
      cyclicGeneratorInverseMatrix P r =
          (onePlusY P r)⁻¹ •
            cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) :=
        cyclicGeneratorInverseMatrix_eq_inv_smul_pow_pred P r
      _ = a • cyclicGeneratorMatrix P r ^ (r.matrixRank - 1) := by
        simpa only [a] using onePlusYInv_smul_eq_functionField_smul P r
          (cyclicGeneratorMatrix P r ^ (r.matrixRank - 1))
      _ = _ := by simp [a, ← constantMatrixEmbedding_apply]
  simpa only [heq] using hsmul

theorem functionFieldCyclicSpan_eq_top
    (P : BasePrime) (r : Rank) :
    functionFieldCyclicSpan P r = ⊤ := by
  apply top_unique
  intro x _
  apply Algebra.adjoin_induction
    (R := FunctionField P)
    (s := Set.range (constantMatrix P r) ∪
      {cyclicGeneratorMatrix P r, cyclicGeneratorInverseMatrix P r})
    (p := fun M hM =>
      (⟨M, hM⟩ : CyclicAlgebra P r) ∈ functionFieldCyclicSpan P r)
  · intro M hM
    rcases hM with hM | hM
    · obtain ⟨c, rfl⟩ := hM
      exact constantMatrix_mem_functionFieldCyclicSpan P r c
    · rcases hM with (rfl | hM)
      · exact cyclicGeneratorMatrix_mem_functionFieldCyclicSpan P r
      · rw [Set.mem_singleton_iff] at hM
        subst M
        exact cyclicGeneratorInverseMatrix_mem_functionFieldCyclicSpan P r
  · intro a
    exact (functionFieldCyclicSpanSubalgebra P r).algebraMap_mem a
  · intro M N hM hN hMi hNi
    exact (functionFieldCyclicSpanSubalgebra P r).add_mem hMi hNi
  · intro M N hM hN hMi hNi
    exact (functionFieldCyclicSpanSubalgebra P r).mul_mem hMi hNi

noncomputable def functionFieldCyclicBasis
    (P : BasePrime) (r : Rank) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (FunctionField P) (CyclicAlgebra P r) :=
  Module.Basis.mk (functionFieldCyclicBasisVector_linearIndependent P r)
    (by
      change (⊤ : Submodule (FunctionField P) (CyclicAlgebra P r)) ≤
        functionFieldCyclicSpan P r
      rw [functionFieldCyclicSpan_eq_top])

@[simp] theorem functionFieldCyclicBasis_apply
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    functionFieldCyclicBasis P r p =
      functionFieldCyclicBasisVector P r p := by
  simp [functionFieldCyclicBasis]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
