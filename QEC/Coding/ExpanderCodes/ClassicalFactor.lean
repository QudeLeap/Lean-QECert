import QEC.Coding.ExpanderCodes.AlmostLinear
import QEC.Coding.ExpanderCodes.ClassicalRowReduction

/-!
# Classical LDPC factors extracted from PK20 Proposition 1

The matrix supplied by PK20 Proposition 1 is also a parity-check matrix for
an asymptotically good classical quasi-cyclic LDPC code.  This file records
that consequence in the finite language consumed by the two EKZ products.
Dependent parity checks are deleted by `ClassicalRowReduction`; this makes
the boundary surjective without changing its kernel or its distance and
without increasing locality.

No second probabilistic or coding-theoretic premise is introduced here.
-/

namespace QEC.Coding.ExpanderCodes.PK20

open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.DistanceBalancing

/-- The integral relative-radius lower bound furnished by Proposition 1. -/
def classicalDistanceLowerBound
    (bitCount radiusNumerator radiusDenominator : Nat) : Nat :=
  radiusNumerator * bitCount / radiusDenominator

/-- A nonzero kernel word must lie outside the relative expansion ball. -/
theorem classicalDistanceAtLeast_of_relativeExpansion
    {bit check : Type}
    [Fintype bit] [DecidableEq bit]
    [Fintype check] [DecidableEq check]
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hExpansionNumerator : 0 < expansionNumerator)
    (hExpansion : Y.SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator) :
    ClassicalDistanceAtLeast (LinearMap.toMatrix' Y)
      (classicalDistanceLowerBound (Fintype.card bit)
        radiusNumerator radiusDenominator) := by
  intro x hx hne
  rw [Matrix.toLin'_toMatrix'] at hx
  by_contra hSmall
  have hWeightLe : HammingWeight x ≤
      classicalDistanceLowerBound (Fintype.card bit)
        radiusNumerator radiusDenominator := by omega
  have hRadius : radiusDenominator * HammingWeight x ≤
      radiusNumerator * Fintype.card bit := by
    exact (Nat.mul_le_mul_left radiusDenominator hWeightLe).trans
      (Nat.mul_div_le _ _)
  have hExpanded := hExpansion.2.2 x hRadius
  rw [hx, HammingWeight_zero, Nat.mul_zero] at hExpanded
  have hWeightZero : HammingWeight x = 0 := by
    rcases Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hExpanded) with
      hNumeratorZero | hWeightZero
    · exact (Nat.ne_of_gt hExpansionNumerator hNumeratorZero).elim
    · exact hWeightZero
  exact hne ((HammingWeight_eq_zero_iff x).mp hWeightZero)

/-- Coordinate formula for the transpose, kept local to the classical-factor
bridge so that this file does not depend on the later LPS Tanner module. -/
private theorem wordLinearMapTranspose_apply_eq_sum_classicalFactor
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
    (y : Word (ZMod 2) κ) (i : ι) :
    wordLinearMapTranspose P y i =
      ∑ k : κ, y k * P (canonicalBasisWord i) k := by
  classical
  rw [wordLinearMapTranspose]
  rfl

private theorem canonicalBasisWord_eq_single_classicalFactor
    {I : Type} [DecidableEq I] (i : I) :
    canonicalBasisWord (F := ZMod 2) i = Pi.single i 1 := by
  classical
  ext i'
  by_cases hi : i = i'
  · subst i'
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, hi]

private theorem tannerAction_canonicalBasisWord_apply
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (c : aCol) (gi : G) (r : aRow) (go : G) :
    PKDistance.tannerAction A (canonicalBasisWord (c, gi)) (r, go) =
      LiftedProduct.rightRegularMatrix (A r c) go gi := by
  rw [canonicalBasisWord_eq_single_classicalFactor,
    PKDistance.tannerAction_apply, Fintype.sum_eq_single c]
  · rw [Fintype.sum_eq_single gi]
    · simp
    · intro g hne
      simp [hne]
  · intro c' hne
    simp [hne]

/-- Transposition of the quasi-cyclic Tanner matrix is the Tanner action of
the star-transposed group-algebra matrix. -/
theorem wordLinearMapTranspose_tannerAction
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) :
    wordLinearMapTranspose (PKDistance.tannerAction A) =
      PKDistance.tannerAction (LiftedProduct.starTranspose A) := by
  apply LinearMap.ext
  intro y
  funext p
  rcases p with ⟨c, gi⟩
  rw [wordLinearMapTranspose_apply_eq_sum_classicalFactor,
    Fintype.sum_prod_type]
  conv_rhs => rw [PKDistance.tannerAction_apply]
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro go _hgo
  rw [tannerAction_canonicalBasisWord_apply]
  rw [show LiftedProduct.rightRegularMatrix
      (LiftedProduct.starTranspose A c r) gi go =
        LiftedProduct.rightRegularMatrix (A r c) go gi by
    exact congrFun (congrFun
      (LiftedProduct.rightRegularMatrix_starTranspose_entry A r c) gi) go]
  exact mul_comm _ _

/-- Exact finite package for one classical factor used by PK20 Theorem 2.
The factor is a row-reduction of the Proposition 1 Tanner boundary. -/
def ClassicalFactorCertificate
    {bit check : Type}
    [Fintype bit] [DecidableEq bit]
    [Fintype check] [DecidableEq check]
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (distance locality : Nat) : Prop :=
  Function.Surjective (ClassicalRowReduction.reducedBoundary Y) ∧
    ClassicalDistanceAtLeast
      (LinearMap.toMatrix' (ClassicalRowReduction.reducedBoundary Y))
      distance ∧
    Module.finrank (ZMod 2)
        (LinearMap.ker (ClassicalRowReduction.reducedBoundary Y)) ≥
      Fintype.card bit - Fintype.card check ∧
    (∀ b, HammingWeight
      (wordLinearMapTranspose (ClassicalRowReduction.reducedBoundary Y)
        (Pi.single b 1)) ≤ locality) ∧
    (∀ a, HammingWeight
      (ClassicalRowReduction.reducedBoundary Y (Pi.single a 1)) ≤ locality)

/-- The Proposition 1 Tanner matrix gives a surjective, constant-locality,
linear-distance classical boundary after deleting dependent rows. -/
theorem classicalFactorCertificate_of_propositionOne_output
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (w radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hForwardWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hForwardRelative :
      (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator) :
    ClassicalFactorCertificate (PKDistance.tannerAction A)
      (classicalDistanceLowerBound
        (Fintype.card (aCol × Cyclic.CyclicGroup q))
        radiusNumerator radiusDenominator) w := by
  let Y := PKDistance.tannerAction A
  have hDistance : ClassicalDistanceAtLeast (LinearMap.toMatrix' Y)
      (classicalDistanceLowerBound
        (Fintype.card (aCol × Cyclic.CyclicGroup q))
        radiusNumerator radiusDenominator) :=
    classicalDistanceAtLeast_of_relativeExpansion Y
      hExpansionNumerator hForwardRelative
  have hKernelRank : Fintype.card (aCol × Cyclic.CyclicGroup q) -
        Fintype.card (aRow × Cyclic.CyclicGroup q) ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y) := by
    have hRankNullity := Y.finrank_range_add_finrank_ker
    have hRange := Submodule.finrank_le (LinearMap.range Y)
    simp only [Module.finrank_pi, ZMod.card] at hRankNullity hRange
    omega
  refine ⟨ClassicalRowReduction.reducedBoundary_surjective Y,
    ClassicalRowReduction.classicalDistanceAtLeast_reducedBoundary Y hDistance,
    ?_, ?_, ?_⟩
  · rw [ClassicalRowReduction.finrank_ker_reducedBoundary]
    exact hKernelRank
  · apply ClassicalRowReduction.reducedBoundary_rowWeight Y
    intro b
    rw [wordLinearMapTranspose_tannerAction A]
    exact hTransposeWeight b
  · intro a
    exact (ClassicalRowReduction.reducedBoundary_columnWeight Y a).trans
      (hForwardWeight a)

end QEC.Coding.ExpanderCodes.PK20
