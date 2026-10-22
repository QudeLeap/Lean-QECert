import QEC.Coding.ExpanderCodes.LPSFamily
import QEC.Coding.ExpanderCodes.TannerFamily

/-!
# Semantic code families from the variable-prime LPS graphs

This module connects the concrete LPS labels to the semantic Tanner
lifted-product family.  Jacobi's four-square count is used only to identify
the quaternion directions with `Fin (p + 1)`; locality, cofinality, and the
rate estimate are then derived by the generic Tanner-family theorems.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ} {F R R' : Type}
variable [Field F] [Fintype F]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

noncomputable local instance : DecidableEq F := Classical.decEq F
noncomputable local instance (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    DecidableEq (LPSVertexGroup hp hp4 n) :=
  Classical.decEq _
noncomputable local instance (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    DecidableEq
      (FamilyQubitIndex (W := Fin (p + 1)) (R := R) (R' := R')
        (G := LPSVertexGroup hp hp4) n) :=
  Classical.decEq _

/-- The semantic Tanner lifted-product family carried by the reindexed LPS
labels.  Its index is the residue-prime sequence parameter `n`. -/
noncomputable def lpsSemanticFamily
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1)
    (h : Matrix R (Fin (p + 1)) F)
    (h' : Matrix R' (Fin (p + 1)) F) :=
  semanticFamily
    (lpsFinQuaternionFamilyLabel hp hp4 hCount) h h'
    (by simp) (lpsVertexGroup_card_cofinal hp hp4)

/-- Every LPS semantic family has one locality bound independent of the
residue-prime index. -/
theorem lpsSemanticFamily_hasUniformLDPC
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1)
    (h : Matrix R (Fin (p + 1)) F)
    (h' : Matrix R' (Fin (p + 1)) F) :
    QEC.QLDPC.HasUniformLDPC
      (lpsSemanticFamily hp hp4 hCount h h') := by
  exact semanticFamily_hasUniformLDPC
    (lpsFinQuaternionFamilyLabel hp hp4 hCount) h h'
    (by simp) (lpsVertexGroup_card_cofinal hp hp4)

/-- The local dimension ratio supplies the requested asymptotic rate for the
actual cofinal LPS semantic family. -/
theorem lpsSemanticFamily_hasEventualRateAtLeast_of_local_ratio
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1)
    (h : Matrix R (Fin (p + 1)) F)
    (h' : Matrix R' (Fin (p + 1)) F)
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * (p + 1) ≤
        (1 - rate) *
          (((p + 1 : ℕ) : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRateAtLeast
      (lpsSemanticFamily hp hp4 hCount h h') rate := by
  apply semanticFamily_hasEventualRateAtLeast_of_local_ratio
    (lpsFinQuaternionFamilyLabel hp hp4 hCount) h h'
    (by simp) (lpsVertexGroup_card_cofinal hp hp4)
  simpa using hRatio

end QEC.Coding.TannerLiftedProduct
