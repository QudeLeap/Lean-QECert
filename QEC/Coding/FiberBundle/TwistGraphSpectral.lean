import QEC.Coding.FiberBundle.TwistGraphMixing
import Mathlib.Data.Nat.Dist

/-!
# Squared expander mixing for the HHO20 twist graph

The usual Expander Mixing Lemma contains a square root.  For the finite
integer-valued twist graph it is more robust to clear all denominators and
square the inequality.  `HasHHO20SquaredExpanderMixing` is exactly that form
for normalized second-eigenvalue bound `1 / 50000`.

This module proves, without any analytic assumptions, that the single squared
mixing event implies both oriented-edge estimates consumed by
`HasHHO20EdgeMixing`.  A later probability module must establish the squared
event for a twist sample selected from `RandomTwist.distribution`.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators

/--
Integer-cleared squared Expander Mixing Lemma with normalized spectral
constant `kappa ≤ 1 / 50000`.

For oriented edge count `E(A,B)` in the `2 * typeCount`-regular undirected
twist multigraph, the unsquared normalized discrepancy is

`|ell * E(A,B) - 2 * typeCount * |A| * |B||`.
-/
def HasHHO20SquaredExpanderMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ left right : Finset (ZMod ell),
    (50000 *
        Nat.dist
          (ell * neighborEdgeCount twistSample left right)
          (2 * typeCount * left.card * right.card)) ^ 2 ≤
      (2 * typeCount) ^ 2 *
        left.card * (ell - left.card) *
        right.card * (ell - right.card)

/--
For complementary nonheavy/heavy sets, the square-root variance term is
exactly `|nonheavy| * |heavy|`.
-/
theorem complementary_discrepancy_bound
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hSquared : HasHHO20SquaredExpanderMixing twistSample) :
    50000 *
        Nat.dist
          (ell *
            neighborEdgeCount twistSample
              (nonheavyLayerSet Delta w) (heavyLayerSet Delta w))
          (2 * typeCount *
            (nonheavyLayerSet Delta w).card *
            (heavyLayerSet Delta w).card) ≤
      2 * typeCount *
        (nonheavyLayerSet Delta w).card *
        (heavyLayerSet Delta w).card := by
  let nonheavyCount := (nonheavyLayerSet Delta w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let discrepancy :=
    Nat.dist
      (ell *
        neighborEdgeCount twistSample
          (nonheavyLayerSet Delta w) (heavyLayerSet Delta w))
      (2 * typeCount * nonheavyCount * heavyCount)
  have hCard : nonheavyCount + heavyCount = ell := by
    calc
      _ = (nonheavyLayerSet Delta w ∪ heavyLayerSet Delta w).card := by
        rw [Finset.card_union_of_disjoint
          (disjoint_nonheavyLayerSet_heavyLayerSet Delta w)]
      _ = ell := by
        rw [nonheavyLayerSet_union_heavyLayerSet]
        simp
  have hSubNonheavy : ell - nonheavyCount = heavyCount := by omega
  have hSubHeavy : ell - heavyCount = nonheavyCount := by omega
  have hsq := hSquared
    (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
  have hRhs :
      (2 * typeCount) ^ 2 *
          nonheavyCount * (ell - nonheavyCount) *
          heavyCount * (ell - heavyCount) =
        (2 * typeCount * nonheavyCount * heavyCount) ^ 2 := by
    rw [hSubNonheavy, hSubHeavy]
    ring
  change 50000 * discrepancy ≤
    2 * typeCount * nonheavyCount * heavyCount
  change (50000 * discrepancy) ^ 2 ≤
    (2 * typeCount) ^ 2 *
      nonheavyCount * (ell - nonheavyCount) *
      heavyCount * (ell - heavyCount) at hsq
  rw [hRhs] at hsq
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp hsq

/--
In the heavy case, the variance term for `(H,L)` is at most
`sqrt(1001) * ell * |H| < 32 * ell * |H|`; after including degree `2k`,
the cleared discrepancy is bounded by `64 * k * ell * |H|`.
-/
theorem heavy_light_discrepancy_bound
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hSquared : HasHHO20SquaredExpanderMixing twistSample)
    (hcase :
      (mediumLayerSet Delta w).card <
        1000 * (heavyLayerSet Delta w).card) :
    50000 *
        Nat.dist
          (ell *
            neighborEdgeCount twistSample
              (heavyLayerSet Delta w) (lightLayerSet Delta w))
          (2 * typeCount *
            (heavyLayerSet Delta w).card *
            (lightLayerSet Delta w).card) ≤
      64 * typeCount * ell * (heavyLayerSet Delta w).card := by
  let lightCount := (lightLayerSet Delta w).card
  let mediumCount := (mediumLayerSet Delta w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let discrepancy :=
    Nat.dist
      (ell *
        neighborEdgeCount twistSample
          (heavyLayerSet Delta w) (lightLayerSet Delta w))
      (2 * typeCount * heavyCount * lightCount)
  have hPartition :
      lightCount + mediumCount + heavyCount = ell :=
    card_light_add_medium_add_heavy Delta w
  have hLightLe : lightCount ≤ ell := by omega
  have hHeavyLe : heavyCount ≤ ell := by omega
  have hSubLight : ell - lightCount = mediumCount + heavyCount := by omega
  have hSubLightBound : ell - lightCount ≤ 1001 * heavyCount := by
    rw [hSubLight]
    omega
  have hSubHeavy : ell - heavyCount ≤ ell := Nat.sub_le _ _
  have hVariance :
      heavyCount * (ell - heavyCount) *
          lightCount * (ell - lightCount) ≤
        heavyCount * ell * ell * (1001 * heavyCount) := by
    gcongr
  have hsq := hSquared
    (heavyLayerSet Delta w) (lightLayerSet Delta w)
  change (50000 * discrepancy) ^ 2 ≤
    (2 * typeCount) ^ 2 *
      heavyCount * (ell - heavyCount) *
      lightCount * (ell - lightCount) at hsq
  have hsq' :
      (50000 * discrepancy) ^ 2 ≤
        (64 * typeCount * ell * heavyCount) ^ 2 := by
    calc
      _ ≤ (2 * typeCount) ^ 2 *
          (heavyCount * ell * ell * (1001 * heavyCount)) :=
        hsq.trans (by
          simpa only [Nat.mul_assoc] using
            Nat.mul_le_mul_left ((2 * typeCount) ^ 2) hVariance)
      _ = 4004 * (typeCount * ell * heavyCount) ^ 2 := by ring
      _ ≤ 4096 * (typeCount * ell * heavyCount) ^ 2 :=
        Nat.mul_le_mul_right
          ((typeCount * ell * heavyCount) ^ 2) (by omega)
      _ = (64 * typeCount * ell * heavyCount) ^ 2 := by ring
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp hsq'

/--
Squared expander mixing implies the two numerical edge estimates used by the
deterministic HHO20 proof.
-/
theorem hasHHO20EdgeMixing_of_squaredExpanderMixing
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hSquared : HasHHO20SquaredExpanderMixing twistSample) :
    HasHHO20EdgeMixing Delta twistSample := by
  intro w hHeavySmall hLightLarge
  let nonheavyCount := (nonheavyLayerSet Delta w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let lightCount := (lightLayerSet Delta w).card
  let nonheavyHeavyEdges :=
    neighborEdgeCount twistSample
      (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
  let heavyLightEdges :=
    neighborEdgeCount twistSample
      (heavyLayerSet Delta w) (lightLayerSet Delta w)
  have hComplement :=
    complementary_discrepancy_bound
      Delta twistSample w hSquared
  have hUpper :
      10 * ell * nonheavyHeavyEdges ≤
        22 * typeCount * nonheavyCount * heavyCount := by
    let expected := 2 * typeCount * nonheavyCount * heavyCount
    let observed := ell * nonheavyHeavyEdges
    let error := Nat.dist observed expected
    have hObserved : observed ≤ expected + error :=
      Nat.dist_tri_right' observed expected
    have hError : 50000 * error ≤ expected := by
      exact hComplement
    have hScaled :
        50000 * observed ≤
          100002 * (typeCount * nonheavyCount * heavyCount) := by
      calc
        50000 * observed ≤ 50000 * (expected + error) :=
          Nat.mul_le_mul_left 50000 hObserved
        _ = 50000 * expected + 50000 * error := by ring
        _ ≤ 50000 * expected + expected :=
          Nat.add_le_add_left hError (50000 * expected)
        _ = 100002 * (typeCount * nonheavyCount * heavyCount) := by
          dsimp only [expected]
          ring
    have hGrouped :
        10 * observed ≤
          22 * (typeCount * nonheavyCount * heavyCount) := by
      omega
    simpa only [observed, Nat.mul_assoc] using hGrouped
  refine ⟨hUpper, ?_⟩
  intro hcase
  have hDeviation :=
    heavy_light_discrepancy_bound
      Delta twistSample w hSquared hcase
  let observed := ell * heavyLightEdges
  let expected := 2 * typeCount * heavyCount * lightCount
  let error := Nat.dist observed expected
  let scale := typeCount * ell * heavyCount
  have hExpected : expected ≤ observed + error :=
    Nat.dist_tri_right observed expected
  have hError : 50000 * error ≤ 64 * scale := by
    simpa only [error, scale, observed, expected, heavyLightEdges,
      heavyCount, lightCount, Nat.mul_assoc] using hDeviation
  have hExpectedScaled :
      50000 * expected ≤ 50000 * observed + 64 * scale := by
    calc
      50000 * expected ≤ 50000 * (observed + error) :=
        Nat.mul_le_mul_left 50000 hExpected
      _ = 50000 * observed + 50000 * error := by ring
      _ ≤ 50000 * observed + 64 * scale :=
        Nat.add_le_add_left hError (50000 * observed)
  have hLightScaled :
      99990 * scale ≤ 50000 * expected := by
    calc
      99990 * scale =
          (10 * typeCount * heavyCount) * (9999 * ell) := by
        dsimp only [scale]
        ring
      _ ≤ (10 * typeCount * heavyCount) * (10000 * lightCount) :=
        Nat.mul_le_mul_left (10 * typeCount * heavyCount) hLightLarge
      _ = 50000 * expected := by
        dsimp only [expected]
        ring
  have hMain :
      99926 * scale ≤ 50000 * observed := by
    omega
  have hTargetScaled :
      (50 * ell) * (1998 * typeCount * heavyCount) ≤
        (50 * ell) * (1000 * heavyLightEdges) := by
    calc
      _ = 99900 * scale := by
        dsimp only [scale]
        ring
      _ ≤ 99926 * scale :=
        Nat.mul_le_mul_right scale (by omega)
      _ ≤ 50000 * observed := hMain
      _ = (50 * ell) * (1000 * heavyLightEdges) := by
        dsimp only [observed]
        ring
  exact Nat.le_of_mul_le_mul_left hTargetScaled
    (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne ell)))

end QEC.Coding.FiberBundle.TwistGraph
