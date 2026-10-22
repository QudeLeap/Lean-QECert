import QEC.Coding.ExpanderCodes.ProductExpansionPairProbability
import QEC.Coding.ExpanderCodes.TannerTranspose

/-!
# Semantic Tanner rate and distance bridge

This module carries the attained algebraic CSS distance and the local-dimension
rate ratio to the actual finite-qudit Tanner presentation.  Random local-pair
construction and asymptotic parameter selection remain separate.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u

variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

noncomputable local instance : DecidableEq F := Classical.decEq F
noncomputable local instance : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _

omit [Fintype F] [DecidableEq W] in
/-- Maximal row rank makes the transpose generator map injective. -/
theorem transpose_mulVec_injective_of_rank_eq_card_rows
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R) :
    Function.Injective (fun u : Word F R => h.transpose.mulVec u) := by
  classical
  let T := Matrix.toLin' h.transpose
  have hRange : Module.finrank F (LinearMap.range T) = Fintype.card R := by
    change h.transpose.rank = Fintype.card R
    rw [Matrix.rank_transpose, hRank]
  have hNullity := T.finrank_range_add_finrank_ker
  have hNullity' : Module.finrank F (LinearMap.range T) +
      Module.finrank F (LinearMap.ker T) = Fintype.card R := by
    simpa using hNullity
  have hKer : Module.finrank F (LinearMap.ker T) = 0 := by omega
  have hKerBot : LinearMap.ker T = ⊥ := Submodule.finrank_eq_zero.mp hKer
  apply LinearMap.ker_eq_bot.mp hKerBot

/-- Positive Tanner middle-homology dimension makes at least one CSS logical
sector nonempty, so its algebraic CSS minimum is attained. -/
theorem exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology) :
    ∃ dCSS : Nat,
      AlgebraicCSSMinimumDistance
        (chainComplex label h h').firstCoboundaryCheckCode
        (chainComplex label h h').middleBoundaryCode dCSS := by
  classical
  let K := chainComplex label h h'
  obtain ⟨q, hq⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := F)).mp hPositive
  let zClass : K.pureZLogicalQuotient :=
    K.pureZLogicalQuotientEquivMiddleHomology.symm q
  have hzClass : zClass ≠ 0 := by
    intro hz
    apply hq
    have := congrArg K.pureZLogicalQuotientEquivMiddleHomology hz
    simpa [zClass] using this
  obtain ⟨z, hz⟩ :=
    K.middleBoundaryInFirstCoboundaryDual.mkQ_surjective zClass
  have hzQuotient : K.middleBoundaryInFirstCoboundaryDual.mkQ z ≠ 0 := by
    rw [hz]
    exact hzClass
  have hzNot : (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) ∉
      K.middleBoundaryCode.carrier := by
    intro hzMem
    apply hzQuotient
    apply (Submodule.Quotient.mk_eq_zero _).2
    change (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) ∈
        K.middleBoundaryCode.carrier
    exact hzMem
  apply exists_algebraicCSSMinimumDistance_of_exists_logical
  exact ⟨z, Or.inr ⟨z.2, hzNot⟩⟩

/-- The attained algebraic CSS minimum lower-bounds the actual semantic
distance of the Tanner finite-qudit presentation. -/
theorem algebraicCSSMinimumDistance_le_semanticPresentation_distance
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (dCSS : Nat)
    (hMinimum : AlgebraicCSSMinimumDistance
      (chainComplex label h h').firstCoboundaryCheckCode
      (chainComplex label h h').middleBoundaryCode dCSS) :
    dCSS ≤ (semanticPresentation label h h').distance := by
  classical
  rw [(semanticPresentation label h h').distance_eq_semanticQuditDistance]
  exact QEC.Coding.FiniteFieldPauli.algebraicCSSMinimumDistance_le_semanticQuditDistance
    (chainComplex label h h').firstCoboundaryCheckCode
    (chainComplex label h h').middleBoundaryCode
    (chainComplex label h h').firstCoboundaryCheckCode_le_middleBoundaryCode_dual
    dCSS hMinimum

/-- The source local-dimension ratio is already a rate bound for the actual
semantic Tanner presentation. -/
theorem rate_le_semanticPresentation_encodedQudits_of_local_ratio
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    rate * ((semanticPresentation label h h').blockLength : ℝ) ≤
      ((semanticPresentation label h h').encodedQudits : ℝ) := by
  change rate * Fintype.card
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) ≤
    (Module.finrank F (chainComplex label h h').middleHomology : ℝ)
  exact rate_le_finrank_middleHomology_of_local_ratio label h h' rate hRatio

/-- A positive requested rate and the local-dimension ratio force the Tanner
middle homology, hence the encoded semantic space, to be nontrivial. -/
theorem finrank_middleHomology_pos_of_local_ratio
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hW : 0 < Fintype.card W)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    0 < Module.finrank F (chainComplex label h h').middleHomology := by
  have hCardQ : 0 < Fintype.card
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) := by
    rw [card_qubitIndex]
    have hCardG : 0 < Fintype.card G := Fintype.card_pos
    positivity
  have hRate := rate_le_finrank_middleHomology_of_local_ratio
    label h h' rate hRatio
  have hLeftPositive : 0 < rate *
      (Fintype.card
        (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) : ℝ) :=
    mul_pos hRatePositive (Nat.cast_pos.mpr hCardQ)
  have hReal : 0 < (Module.finrank F
      (chainComplex label h h').middleHomology : ℝ) :=
    hLeftPositive.trans_le hRate
  exact_mod_cast hReal

/-- The deterministic PK22 hypotheses give the same graph-radius lower bound
on the actual semantic finite-qudit distance whenever the Tanner product has
positive encoded dimension. -/
theorem semanticPresentation_distance_ge_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (hHomologyPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology) :
    radius / (2 * Fintype.card W) + 1 ≤
      (semanticPresentation label h h').distance := by
  obtain ⟨dCSS, hMinimum⟩ :=
    exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
      label h h' hHomologyPositive
  have hInjective :=
    transpose_mulVec_injective_of_rank_eq_card_rows h hRank
  have h'Injective :=
    transpose_mulVec_injective_of_rank_eq_card_rows h' h'Rank
  exact (algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
    label h h' hRank h'Injective h'Rank hInjective
    d m s beta hProductExpand hProductExpandReverse
    hDistance hDistanceReverse hLength hTwo hFour hDistanceScale
    hRectangleScale hBudget radius lambda hLambda hBase
    hVerticalThreshold hEdgeThreshold hFaceThreshold dCSS hMinimum).trans
      (algebraicCSSMinimumDistance_le_semanticPresentation_distance
        label h h' dCSS hMinimum)

end QEC.Coding.TannerLiftedProduct
