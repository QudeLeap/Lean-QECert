import QEC.Coding.QuantumTanner.SquareGraph
import QEC.Coding.ExpanderCodes.MixingDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exceptional local views

The finite edge-counting step in [LZ22, Claim claim:Se]. The mixing estimate
is explicitly a property of the actual square graph. No spectral estimate is
inferred from the abstract square-complex incidence interface alone.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- Actual exceptional vertices obey the high-degree estimate when the full
same-side square multigraph has the stated mixing bound. -/
theorem exceptionalVertices_card_bound_of_mixing
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) (threshold spectral : ℝ)
    (hThreshold : 0 < threshold) (hCutoff : threshold ≤ cutoff)
    (hSpectral : 0 ≤ spectral)
    (hMixing : HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) spectral)
    (hSmall : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤ threshold * Fintype.card G) :
    threshold ^ 2 * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      4 * spectral ^ 2 * (X.activeVerticesOnSide side x).card := by
  apply highDegree_card_bound_of_mixing (X.squareGraph side)
    (Fintype.card A * Fintype.card B) spectral threshold hSpectral hThreshold hMixing
    (X.exceptionalVerticesOnSide side x cutoff) (X.activeVerticesOnSide side x) ?_ hSmall
  have hActual : (cutoff : ℝ) * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      (crossCount (X.squareGraph side) (X.exceptionalVerticesOnSide side x cutoff)
        (X.activeVerticesOnSide side x) : ℝ) := by
    exact_mod_cast X.exceptional_card_mul_cutoff_le_crossCount side x cutoff
  exact (mul_le_mul_of_nonneg_right hCutoff (Nat.cast_nonneg _)).trans hActual

/-- The source's `64 / Delta^(1 - 2 epsilon)` exceptional-vertex estimate,
with the real threshold interpreted by its exact integer ceiling.
The mixing assumption concerns this complex's actual square multigraph. -/
theorem exceptionalVertices_card_bound_source
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (Delta : Nat) (epsilon : ℝ)
    (hDelta : 0 < Delta) (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hMixing : HasExpanderMixingBound (X.squareGraph side) (Delta * Delta)
      (4 * (Delta : ℝ)))
    (hSmall : ((X.activeVerticesOnSide side x).card : ℝ) ≤
      Fintype.card G / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon))) :
    ((X.exceptionalVerticesOnSide side x
      (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))).card : ℝ) ≤
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        (X.activeVerticesOnSide side x).card := by
  have hD : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hT : 0 < (Delta : ℝ) ^ (3 / 2 - epsilon) := Real.rpow_pos_of_pos hD _
  have hProduct : (Delta : ℝ) ^ (3 / 2 - epsilon) *
      (Delta : ℝ) ^ (1 / 2 + epsilon) = (Delta : ℝ) ^ 2 := by
    rw [← Real.rpow_add hD, show (3 / 2 - epsilon) + (1 / 2 + epsilon) =
      (2 : ℝ) by ring]
    norm_num
  have hDensity : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤
      (Delta : ℝ) ^ (3 / 2 - epsilon) * Fintype.card G := by
    have hScaled := (le_div_iff₀ (by positivity :
      0 < 4 * (Delta : ℝ) ^ (1 / 2 + epsilon))).mp hSmall
    have hMult := mul_le_mul_of_nonneg_left hScaled hT.le
    rw [hA, hB, Nat.cast_mul]
    nlinarith [hProduct, (Nat.cast_nonneg (X.activeVerticesOnSide side x).card :
      (0 : ℝ) ≤ (X.activeVerticesOnSide side x).card)]
  have hBound := X.exceptionalVertices_card_bound_of_mixing side x
    (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))
    ((Delta : ℝ) ^ (3 / 2 - epsilon)) (4 * (Delta : ℝ)) hT
    (Nat.le_ceil _) (by positivity) (by simpa [hA, hB] using hMixing) hDensity
  have hSquare : ((Delta : ℝ) ^ (3 / 2 - epsilon)) ^ 2 =
      (Delta : ℝ) ^ 2 * (Delta : ℝ) ^ (1 - 2 * epsilon) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_natCast _ 2,
      ← Real.rpow_add hD]
    congr 1
    ring
  rw [hSquare] at hBound
  have hReduced : (Delta : ℝ) ^ (1 - 2 * epsilon) *
      (X.exceptionalVerticesOnSide side x
        (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))).card ≤
      64 * (X.activeVerticesOnSide side x).card := by
    apply le_of_mul_le_mul_left (a := (Delta : ℝ) ^ 2) ?_ (by positivity)
    nlinarith [hBound]
  have hDen : 0 < (Delta : ℝ) ^ (1 - 2 * epsilon) := Real.rpow_pos_of_pos hD _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hDen).mpr
  nlinarith [hReduced]

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
