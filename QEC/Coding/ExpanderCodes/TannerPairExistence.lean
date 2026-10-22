import QEC.Coding.ExpanderCodes.LocalParameterSelection

/-!
# Finite PK22 local pairs and semantic Tanner distance

This module converts coarse finite bad-event budgets to the exact local-pair
hypotheses and joins the simultaneous pair theorem to the semantic Tanner
rate and distance bridge. All graph expansion and numerical assumptions remain
explicit.
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

/-- Four weighted binomial budgets and two coarse rectangle budgets imply the
exact six finite inequalities consumed by the simultaneous two-orientation
local-pair theorem.  The auxiliary base `L` is free and can later be chosen
to optimize the linear exponent. -/
theorem exactPairFactors_of_weighted
    (w r r' d m s k q L : Nat) (hd : d ≤ w) (hL : 0 < L)
    (hFirstKernel :
      6 * (q + L) ^ w < q ^ r * L ^ (w - d))
    (hFirstImage :
      (6 * q ^ r) * (q + L) ^ w < q ^ w * L ^ (w - d))
    (hSecondKernel :
      6 * (q + L) ^ w < q ^ r' * L ^ (w - d))
    (hSecondImage :
      (6 * q ^ r') * (q + L) ^ w < q ^ w * L ^ (w - d))
    (hForwardRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r))
    (hReverseRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r')) :
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r) ∧
    (6 * (q ^ r *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r') ∧
    (6 * (q ^ r' *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r)) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r')) := by
  have hRectangle := rectangleFactor_le_coarse w m s q
  constructor
  · exact lowWeightFactor_lt_of_scaled_add_pow
      w d q L 6 (q ^ r) hd hL hFirstKernel
  constructor
  · simpa [mul_assoc] using lowWeightFactor_lt_of_scaled_add_pow
      w d q L (6 * q ^ r) (q ^ w) hd hL hFirstImage
  constructor
  · exact lowWeightFactor_lt_of_scaled_add_pow
      w d q L 6 (q ^ r') hd hL hSecondKernel
  constructor
  · simpa [mul_assoc] using lowWeightFactor_lt_of_scaled_add_pow
      w d q L (6 * q ^ r') (q ^ w) hd hL hSecondImage
  constructor
  · exact (Nat.mul_le_mul_left 6 hRectangle).trans_lt hForwardRectangle
  · exact (Nat.mul_le_mul_left 6 hRectangle).trans_lt hReverseRectangle

/-- Six coarse power inequalities imply the exact six finite inequalities
consumed by the simultaneous two-orientation local-pair theorem. -/
theorem exactPairFactors_of_coarse
    (w r r' d m s k q : Nat) (hq : 0 < q)
    (hFirstKernel : 6 * coarseLowWeightFactor w d q < q ^ r)
    (hFirstImage :
      6 * (q ^ r * coarseLowWeightFactor w d q) < q ^ w)
    (hSecondKernel : 6 * coarseLowWeightFactor w d q < q ^ r')
    (hSecondImage :
      6 * (q ^ r' * coarseLowWeightFactor w d q) < q ^ w)
    (hForwardRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r))
    (hReverseRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r')) :
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r) ∧
    (6 * (q ^ r *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r') ∧
    (6 * (q ^ r' *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r)) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r')) := by
  have hLow := lowWeightFactor_le_coarse w d q hq
  have hRectangle := rectangleFactor_le_coarse w m s q
  constructor
  · exact (Nat.mul_le_mul_left 6 hLow).trans_lt hFirstKernel
  constructor
  · exact (Nat.mul_le_mul_left 6
      (Nat.mul_le_mul_left (q ^ r) hLow)).trans_lt hFirstImage
  constructor
  · exact (Nat.mul_le_mul_left 6 hLow).trans_lt hSecondKernel
  constructor
  · exact (Nat.mul_le_mul_left 6
      (Nat.mul_le_mul_left (q ^ r') hLow)).trans_lt hSecondImage
  constructor
  · exact (Nat.mul_le_mul_left 6 hRectangle).trans_lt hForwardRectangle
  · exact (Nat.mul_le_mul_left 6 hRectangle).trans_lt hReverseRectangle

set_option maxHeartbeats 1200000 in
/-- The simultaneous random local-code package, together with one expanding
labelled double cover, produces Tanner lifted products whose attained
algebraic CSS distance is at least the graph radius divided by `2 |W|`.

The theorem deliberately leaves the local dimensions and numerical
inequalities explicit.  Choosing them uniformly and supplying a cofinal graph
family is the final asymptotic construction step. -/
theorem exists_localPair_with_semanticRateAndDistance
    (label : W → G)
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * (2 * m) ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W)
          (Fintype.card W - 2 * m)) ^ 2 *
        (s * (((Fintype.card W - 2 * m) *
          (Fintype.card W - 2 * m) + 1) ^ s) *
          (Nat.card F) ^ (2 * (2 * m) * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W)
          (Fintype.card W - 2 * m)) ^ 2 *
        (s * (((Fintype.card W - 2 * m) *
          (Fintype.card W - 2 * m) + 1) ^ s) *
          (Nat.card F) ^ (2 * (2 * m) * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R'))
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R'))
    (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      rate * ((semanticPresentation label h h').blockLength : ℝ) ≤
        ((semanticPresentation label h h').encodedQudits : ℝ) ∧
      radius / (2 * Fintype.card W) + 1 ≤
        (semanticPresentation label h h').distance := by
  obtain ⟨h, h', hRank, h'Rank, hDistance, _hImageDistance,
      hDistanceReverse, _hImageDistanceReverse,
      hProductExpand, hProductExpandReverse⟩ :=
    ProductExpansion.exists_bidirectional_productExpanding_pair
      (F := F) (W := W) (R := R) (R' := R')
      d s (2 * m) k hPositive hLength hSmallM hRankTarget
      hFirstKernelFactor hFirstImageFactor hSecondKernelFactor
      hSecondImageFactor hForwardRectangleFactor hReverseRectangleFactor
  have hRate :=
    rate_le_semanticPresentation_encodedQudits_of_local_ratio
      label h h' rate hRatio
  refine ⟨h, h', hRank, h'Rank, hRate, ?_⟩
  have hHomologyPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology :=
    finrank_middleHomology_pos_of_local_ratio
      label h h' rate hRatePositive (by omega) hRatio
  apply semanticPresentation_distance_ge_of_doubleCoverExpansion
    label h h' hRank h'Rank
    d m s ((d : ℝ) / (3 * (Fintype.card W : ℝ)))
  · exact hProductExpand
  · exact hProductExpandReverse
  · exact hDistance
  · exact hDistanceReverse
  · exact hLength
  · omega
  · exact hFour
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambda
  · exact hBase
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold
  · exact hHomologyPositive

end QEC.Coding.TannerLiftedProduct
