import QEC.Coding.BalancedProduct.PKDistance
import QEC.Coding.BalancedProduct.CyclicLocality
import QEC.Coding.BalancedProduct.CyclicDimension

/-!
# PK20 almost-linear lifted-product distance

This module closes the finite distance argument of PK20, Proposition 2.  The
probabilistic quasi-cyclic expanding-matrix family from PK20, Proposition 1 is
kept as the single explicitly marked external input of the eventual family
theorem; no code parameter or distance conclusion is stored in that input.

The first results below combine the already proved Case 1 and Case 2 estimates
for every nonzero homology or cohomology class.  In particular, they concern
the full stabilizer chain complex, not only the horizontal subsystem used by
the BE20 specialization.
-/

namespace QEC.Coding.ExpanderCodes.PK20

open QEC.Coding
open QEC.Coding.BalancedProduct

/-! ## The single external boundary -/

/--
The owner-approved external boundary for [PK20, Proposition 1], specialized
to the value `ε = 1/2` used in the proof of Theorem 1.

The witnesses are exactly construction data from the proposition and its
proof: fixed positive expansion constants and Tanner degree, followed at each
lift size by a logarithmic-size base Tanner matrix.  The row-count identity is
the source construction `m = 2 floor(w / 4) n`; it records how the matrix is
built, rather than accepting a later rank or code-parameter conclusion.

The two relative expansion statements are the binary block expansion of `A`
and of its star-transpose.  The latter is the block transpose occurring in the
source proof.  This proposition contains no lifted-product code, homology,
distance, dimension, locality, or asymptotic-family conclusion.
-/
def PropositionOneExpandingMatrixFamily : Prop :=
  ∃ (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat),
    4 ≤ w ∧
    0 < gamma ∧
    0 < radiusNumerator ∧
    0 < radiusDenominator ∧
    0 < expansionNumerator ∧
    0 < expansionDenominator ∧
    ∀ (ell : Nat) [NeZero ell], 1 < ell →
      ∃ (n m : Nat)
        (A : Matrix (Fin m) (Fin (w * n))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup ell))),
        m = 2 * (w / 4) * n ∧
        gamma * Nat.log 2 ell ≤ n ∧
        n ≤ gamma * (Nat.log 2 ell + 1) ∧
        (∀ i : Fin (w * n) × Cyclic.CyclicGroup ell,
          HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w) ∧
        (∀ i : Fin m × Cyclic.CyclicGroup ell,
          HammingWeight
            (PKDistance.tannerAction (LiftedProduct.starTranspose A)
              (Pi.single i 1)) ≤ w) ∧
        (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
          radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator ∧
        (PKDistance.tannerAction
          (LiftedProduct.starTranspose A)).SmallSetExpandingAtRelativeRadius
            radiusNumerator radiusDenominator
            expansionNumerator expansionDenominator

/-- Turn the relative-radius conclusion of PK20 Proposition 1 into any
absolute-radius instance needed by Proposition 2.  The only extra premise is
the displayed arithmetic containment of Hamming balls. -/
theorem smallSetExpanding_of_relativeRadius
    {F ι κ : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    {radius radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hExpansion : f.SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator)
    (hRadius : radiusDenominator * radius ≤
      radiusNumerator * Fintype.card ι) :
    f.SmallSetExpanding radius expansionNumerator expansionDenominator := by
  refine ⟨hExpansion.2.1, ?_⟩
  intro x hx
  exact hExpansion.2.2 x <|
    (Nat.mul_le_mul_left radiusDenominator hx).trans hRadius

/-- PK20 Proposition 2 for ordinary middle homology.  The two expansion
hypotheses are the source's Case 1 quotient-distance radius and Case 2
primitive-crossing radius. -/
theorem middleHomologyDistanceAtLeast_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (distanceLowerBound w threshold expansionRadius
      expansionNumerator expansionDenominator lowerBound : Nat)
    (hDistancePositive : 0 < distanceLowerBound)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (PKDistance.tannerAction A).SmallSetExpanding
        (q * distanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (PKDistance.tannerAction A).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * distanceLowerBound) threshold) :
    MiddleHomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound := by
  intro z hz hzNotBoundary
  let projected := HorizontalSubsystem.horizontalHomologyProjection A
    (Cyclic.cyclicGenerator q)
    ((LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩)
  by_cases hProjected : projected ≠ 0
  · obtain ⟨actualDistance, hMinimum⟩ :=
      PKDistance.exists_quotientMinimumDistance_of_middleHomology_ne_zero A
        projected hProjected
    have hDistanceLower : distanceLowerBound ≤ actualDistance := by
      apply PKDistance.quotientMinimumDistance_ge_of_smallSetExpanding
        A hMinimum hExpansionNumeratorPositive
      simpa [Cyclic.CyclicGroup, ZMod.card] using hCaseOneExpansion
    have hCaseOne :=
      PKDistance.nonzero_horizontalClass_caseOne_weight_bound_distanceLowerBound
        q A z hz hMinimum hDistanceLower hProjected
          expansionNumerator expansionDenominator hDistancePositive
            hCaseOneExpansion
    have hScaled := hLowerBound.trans <| calc
      expansionNumerator * min (q * distanceLowerBound) threshold ≤
          expansionNumerator * (q * distanceLowerBound) :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := hCaseOne
    have hCoefficientPositive :
        0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
      exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
    exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive
  · have hProjectedZero : projected = 0 := not_ne_iff.mp hProjected
    have hCaseTwo := PKDistance.zero_horizontalClass_caseTwo_weight_bound
      q hq A z hz hzNotBoundary hProjectedZero
        w threshold expansionRadius expansionNumerator expansionDenominator
          hw hthreshold hThresholdScale hColumnWeight hRadius hCaseTwoExpansion
    have hScaled := hLowerBound.trans <| calc
      expansionNumerator * min (q * distanceLowerBound) threshold ≤
          expansionNumerator * threshold :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := hCaseTwo
    have hCoefficientPositive :
        0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
      exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
    exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

/-- Inverse-orientation form of the full PK20 homology-distance argument.
This is the form reached after dualizing a cocycle of `LP(A,1+x)`. -/
theorem middleHomologyDistanceAtLeast_invGenerator_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (distanceLowerBound w threshold expansionRadius
      expansionNumerator expansionDenominator lowerBound : Nat)
    (hDistancePositive : 0 < distanceLowerBound)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (PKDistance.tannerAction A).SmallSetExpanding
        (q * distanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (PKDistance.tannerAction A).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * distanceLowerBound) threshold) :
    MiddleHomologyDistanceAtLeast
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹))
      lowerBound := by
  intro z hz hzNotBoundary
  let projected := HorizontalSubsystem.horizontalHomologyProjection A
    (Cyclic.cyclicGenerator q)⁻¹
    ((LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ ⟨z, hz⟩)
  by_cases hProjected : projected ≠ 0
  · obtain ⟨actualDistance, hMinimum⟩ :=
      PKDistance.exists_quotientMinimumDistance_of_middleHomology_ne_zero A
        projected hProjected
    have hDistanceLower : distanceLowerBound ≤ actualDistance := by
      apply PKDistance.quotientMinimumDistance_ge_of_smallSetExpanding
        A hMinimum hExpansionNumeratorPositive
      simpa [Cyclic.CyclicGroup, ZMod.card] using hCaseOneExpansion
    have hCaseOne :=
      PKDistance.nonzero_horizontalClass_caseOne_invGenerator_weight_bound_distanceLowerBound
        q A z hz hMinimum hDistanceLower hProjected
          expansionNumerator expansionDenominator hDistancePositive
            hCaseOneExpansion
    have hScaled := hLowerBound.trans <| calc
      expansionNumerator * min (q * distanceLowerBound) threshold ≤
          expansionNumerator * (q * distanceLowerBound) :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := hCaseOne
    have hCoefficientPositive :
        0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
      exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
    exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive
  · have hProjectedZero : projected = 0 := not_ne_iff.mp hProjected
    have hCaseTwo :=
      PKDistance.zero_horizontalClass_caseTwo_invGenerator_weight_bound
        q hq A z hz hzNotBoundary hProjectedZero
          w threshold expansionRadius expansionNumerator expansionDenominator
            hw hthreshold hThresholdScale hColumnWeight hRadius hCaseTwoExpansion
    have hScaled := hLowerBound.trans <| calc
      expansionNumerator * min (q * distanceLowerBound) threshold ≤
          expansionNumerator * threshold :=
        Nat.mul_le_mul_left expansionNumerator (Nat.min_le_right _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := hCaseTwo
    have hCoefficientPositive :
        0 < max (2 * expansionNumerator) (4 * expansionDenominator) := by
      exact lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
    exact Nat.le_of_mul_le_mul_left hScaled hCoefficientPositive

/-- PK20 Proposition 2 for ordinary middle cohomology, obtained by the proved
star-transpose duality and the inverse-orientation homology theorem. -/
theorem middleCohomologyDistanceAtLeast_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (distanceLowerBound w threshold expansionRadius
      expansionNumerator expansionDenominator lowerBound : Nat)
    (hDistancePositive : 0 < distanceLowerBound)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (PKDistance.tannerAction
        (LiftedProduct.starTranspose A)).SmallSetExpanding
          (q * distanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (PKDistance.tannerAction
        (LiftedProduct.starTranspose A)).SmallSetExpanding
          expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * distanceLowerBound) threshold) :
    MiddleCohomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound := by
  intro z hz hzNotCoboundary
  let D := Cyclic.data q A
  let dualZ := LiftedProductDuality.swapWord z
  have hzDual : dualZ ∈
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier := by
    exact PKDistance.dualCycle_mem_invGenerator_middleCycleCode q A z hz
  have hzDualNotBoundary : dualZ ∉
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier := by
    intro hBoundary
    apply hzNotCoboundary
    exact LiftedProductDuality.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
      D z (by
        change dualZ ∈
          (LiftedProduct.chainComplex
            (LiftedProductDuality.dualData D)).middleBoundaryCode.carrier
        simpa only [D, Cyclic.data,
          LiftedProductDuality.dualData_cyclicLiftedProductData] using hBoundary)
  have hDual := middleHomologyDistanceAtLeast_invGenerator_of_expansion
    q hq (LiftedProduct.starTranspose A)
      distanceLowerBound w threshold expansionRadius
        expansionNumerator expansionDenominator lowerBound
      hDistancePositive hExpansionNumeratorPositive hw hthreshold
        hThresholdScale hColumnWeight hRadius hCaseOneExpansion
          hCaseTwoExpansion hLowerBound
  have hWeight := hDual dualZ hzDual hzDualNotBoundary
  rw [LiftedProductDuality.HammingWeight_swapWord] at hWeight
  exact hWeight

/-! ## Finite Proposition 1 to Proposition 2 handoff -/

/--
The complete finite handoff from the output vocabulary of PK20 Proposition 1
to the source-valid, local, two-sector distance conclusion of Proposition 2.
All premises after the two relative expansion statements are elementary
containments of the absolute Hamming balls used by the two cases; they will be
discharged from the construction scales in the family assembly below.
-/
theorem finite_distance_locality_of_relativeExpansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (forwardDistance transposeDistance w threshold
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator lowerBound : Nat)
    (hForwardDistancePositive : 0 < forwardDistance)
    (hTransposeDistancePositive : 0 < transposeDistance)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hForwardWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hForwardRelative :
      (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator)
    (hTransposeRelative :
      (PKDistance.tannerAction
        (LiftedProduct.starTranspose A)).SmallSetExpandingAtRelativeRadius
          radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator)
    (hForwardCaseOneRadius :
      radiusDenominator * (q * forwardDistance) ≤
        radiusNumerator *
          Fintype.card (aCol × Cyclic.CyclicGroup q))
    (hForwardCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (aCol × Cyclic.CyclicGroup q))
    (hTransposeCaseOneRadius :
      radiusDenominator * (q * transposeDistance) ≤
        radiusNumerator *
          Fintype.card (aRow × Cyclic.CyclicGroup q))
    (hTransposeCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (aRow × Cyclic.CyclicGroup q))
    (hForwardLower :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * forwardDistance) threshold)
    (hTransposeLower :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * transposeDistance) threshold) :
    (LiftedProduct.binaryCSSCode (Cyclic.data q A)).stabilizer.IsSourceValidBinary ∧
      BoundedLocality
        (LiftedProduct.boundaryIncidence
          (Cyclic.data q A)).localityProfile (w + 2) ∧
      MiddleHomologyDistanceAtLeast
        (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound ∧
      MiddleCohomologyDistanceAtLeast
        (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound := by
  have hForwardCaseOne := smallSetExpanding_of_relativeRadius
    (PKDistance.tannerAction A) hForwardRelative hForwardCaseOneRadius
  have hForwardCaseTwo := smallSetExpanding_of_relativeRadius
    (PKDistance.tannerAction A) hForwardRelative hForwardCaseTwoRadius
  have hTransposeCaseOne := smallSetExpanding_of_relativeRadius
    (PKDistance.tannerAction (LiftedProduct.starTranspose A))
      hTransposeRelative hTransposeCaseOneRadius
  have hTransposeCaseTwo := smallSetExpanding_of_relativeRadius
    (PKDistance.tannerAction (LiftedProduct.starTranspose A))
      hTransposeRelative hTransposeCaseTwoRadius
  refine ⟨LiftedProduct.binaryCSSCode_stabilizer_isSourceValidBinary
      (Cyclic.data q A), ?_, ?_, ?_⟩
  · simpa only [Cyclic.data, Nat.max_self] using
      (CyclicLocality.boundaryIncidence_boundedLocality_of_tannerAction_bounds
        A (Cyclic.cyclicGenerator q) hForwardWeight hTransposeWeight)
  · exact middleHomologyDistanceAtLeast_of_expansion q hq A
      forwardDistance w threshold threshold
        expansionNumerator expansionDenominator lowerBound
      hForwardDistancePositive hExpansionNumeratorPositive hw hthreshold
        hThresholdScale hForwardWeight (by rfl) hForwardCaseOne
          hForwardCaseTwo hForwardLower
  · exact middleCohomologyDistanceAtLeast_of_expansion q hq A
      transposeDistance w threshold threshold
        expansionNumerator expansionDenominator lowerBound
      hTransposeDistancePositive hExpansionNumeratorPositive hw hthreshold
        hThresholdScale hTransposeWeight (by rfl) hTransposeCaseOne
          hTransposeCaseTwo hTransposeLower

/-! ## Finite dimension bounds -/

/-- The quotient Tanner kernel injects at the level of dimensions into the
full odd cyclic lifted product.  Rank-nullity therefore supplies the lower
half of the source dimension estimate without a rank assumption on `A(1)`. -/
theorem card_sub_card_le_finrank_middleHomology
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol - Fintype.card aRow ≤
      Module.finrank (ZMod 2)
        (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology := by
  have hRankNullity :=
    (HorizontalSubsystem.quotientBoundary A).finrank_range_add_finrank_ker
  have hRangeLe :
      Module.finrank (ZMod 2)
          (LinearMap.range (HorizontalSubsystem.quotientBoundary A)) ≤
        Module.finrank (ZMod 2) (Word (ZMod 2) aRow) :=
    Submodule.finrank_le _
  have hQuotient : Fintype.card aCol - Fintype.card aRow ≤
      Module.finrank (ZMod 2)
        (HorizontalSubsystem.quotientTannerComplex A).middleHomology := by
    rw [HorizontalSubsystem.finrank_quotientTannerComplex_middleHomology_eq_ker]
    have hDomain :
        Module.finrank (ZMod 2) (Word (ZMod 2) aCol) =
          Fintype.card aCol := by simp
    have hCodomain :
        Module.finrank (ZMod 2) (Word (ZMod 2) aRow) =
          Fintype.card aRow := by simp
    rw [hDomain] at hRankNullity
    rw [hCodomain] at hRangeLe
    omega
  exact hQuotient.trans <|
    LinearMap.finrank_le_finrank_of_surjective
      (HorizontalSubsystem.horizontalHomologyProjection_surjective
        A (Cyclic.cyclicGenerator q)
          (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd))

/-- Exact finite dimension window used by PK20 Theorem 1.  Its lower half is
the quotient-Tanner injection and its upper half is forced by the two cyclic
`1+x` blocks; neither bound is included in Proposition 1. -/
theorem finrank_middleHomology_bounds
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol - Fintype.card aRow ≤
        Module.finrank (ZMod 2)
          (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ∧
      Module.finrank (ZMod 2)
          (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ≤
        Fintype.card aCol + Fintype.card aRow :=
  ⟨card_sub_card_le_finrank_middleHomology q hOdd A,
    CyclicDimension.finrank_middleHomology_le_card_add_card q A⟩

/-! ## Exact finite PK20 Theorem 1 certificates -/

/-- There is a nontrivial middle cocycle of weight at most `d`.  Together
with `MiddleCohomologyDistanceAtLeast`, this is the exact finite replacement
for an equality assertion about the X distance. -/
def MiddleCohomologyDistanceAtMost
    {F i0 i1 i2 : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype i0] [Fintype i1] [Fintype i2]
    (K : ChainComplexData F (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) : Prop :=
  ∃ z : Word F i1,
    z ∈ K.middleCocycleCode.carrier ∧
    z ∉ K.firstCoboundaryCheckCode.carrier ∧
    HammingWeight z ≤ d

private theorem exists_standardBasis_not_coboundary
    {G aRow aCol : Type}
    [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (hCard : Fintype.card aRow < Fintype.card aCol) :
    ∃ c : aCol, (Pi.single c 1 : Word (ZMod 2) aCol) ∉
      (HorizontalSubsystem.quotientTannerComplex A).firstCoboundaryCheckCode.carrier := by
  by_contra h
  push_neg at h
  have hTop :
      (HorizontalSubsystem.quotientTannerComplex A).firstCoboundaryCheckCode.carrier =
        ⊤ := by
    apply (Submodule.eq_top_iff_forall_basis_mem
      (Pi.basisFun (ZMod 2) aCol)).2
    intro c
    simpa using h c
  have hRangeLe : Module.finrank (ZMod 2)
      (HorizontalSubsystem.quotientTannerComplex A).firstCoboundaryCheckCode.carrier ≤
      Fintype.card aRow := by
    change Module.finrank (ZMod 2)
        (LinearMap.range
          (wordLinearMapTranspose (HorizontalSubsystem.quotientBoundary A))) ≤ _
    calc
      Module.finrank (ZMod 2)
          (LinearMap.range
            (wordLinearMapTranspose (HorizontalSubsystem.quotientBoundary A))) ≤
          Module.finrank (ZMod 2) (Word (ZMod 2) aRow) :=
        LinearMap.finrank_range_le _
      _ = Fintype.card aRow := by simp
  rw [hTop] at hRangeLe
  simp at hRangeLe
  omega

private theorem wordLinearMapTranspose_apply_eq_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
    (y : Word (ZMod 2) κ) (i : ι) :
    wordLinearMapTranspose P y i =
      ∑ k : κ, y k * P (canonicalBasisWord i) k := by
  classical
  rw [wordLinearMapTranspose]
  rfl

private theorem HammingWeight_transpose_horizontalAugmentation_single
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (c : aCol) :
    HammingWeight
        (wordLinearMapTranspose
          (HorizontalSubsystem.horizontalAugmentation
            (aRow := aRow) (aCol := aCol) (G := G))
          (Pi.single c 1)) =
      Fintype.card G := by
  classical
  have hTranspose :
      wordLinearMapTranspose
          (HorizontalSubsystem.horizontalAugmentation
            (aRow := aRow) (aCol := aCol) (G := G)) =
        HorizontalSubsystem.horizontalConstant := by
    apply LinearMap.ext
    intro z
    funext q
    cases q with
    | inl p =>
        rcases p with ⟨c', u, g⟩
        cases u
        rw [wordLinearMapTranspose_apply_eq_sum]
        rw [HorizontalSubsystem.horizontalConstant_inl]
        simp_rw [HorizontalSubsystem.horizontalAugmentation_apply]
        unfold canonicalBasisWord
        rw [Finset.sum_eq_single c']
        · rw [Finset.sum_eq_single g]
          · simp
          · intro b _ hb
            simp [Pi.single_apply, hb]
          · simp
        · intro k _ hk
          simp [Pi.single_apply, hk]
        · simp
    | inr p =>
        rcases p with ⟨r, u, g⟩
        cases u
        rw [wordLinearMapTranspose_apply_eq_sum]
        rw [HorizontalSubsystem.horizontalConstant_inr]
        simp_rw [HorizontalSubsystem.horizontalAugmentation_apply]
        unfold canonicalBasisWord
        simp [Pi.single_apply]
  rw [hTranspose]
  rw [HammingWeight_eq_card_hammingSupport]
  let supportFinset :
      Finset (LiftedProduct.QubitIndex aRow aCol Unit Unit G) :=
    Finset.univ.filter (fun q =>
      ∃ u : Unit, ∃ g : G, q = Sum.inl (c, u, g))
  have hSupport : hammingSupport
      (HorizontalSubsystem.horizontalConstant
        (aRow := aRow) (aCol := aCol) (G := G)
        (Pi.single c 1)) =
      supportFinset := by
    ext q
    simp only [hammingSupport, supportFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases q with
    | inl p =>
        rcases p with ⟨c', u, g⟩
        cases u
        by_cases hcc : c' = c
        · subst c'
          rw [HorizontalSubsystem.horizontalConstant_inl]
          simp
        · rw [HorizontalSubsystem.horizontalConstant_inl]
          simp [hcc]
    | inr p =>
        rcases p with ⟨r, u, g⟩
        cases u
        rw [HorizontalSubsystem.horizontalConstant_inr]
        simp
  rw [hSupport]
  let f : G → supportFinset := fun g =>
      ⟨(Sum.inl (c, (), g) :
        LiftedProduct.QubitIndex aRow aCol Unit Unit G), by
          dsimp [supportFinset]
          simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g h hEq
      simpa [f] using congrArg
        (fun q : supportFinset => match q.1 with
          | Sum.inl p => p.2.2
          | Sum.inr p => p.2.2) hEq
    · rintro ⟨q, hq⟩
      dsimp [supportFinset] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rcases hq with ⟨u, g, rfl⟩
      cases u
      exact ⟨g, by simp [f, supportFinset]⟩
  let e : G ≃ supportFinset := Equiv.ofBijective f hf
  calc
    supportFinset.card = Fintype.card supportFinset :=
      (Fintype.card_coe supportFinset).symm
    _ = Fintype.card G := (Fintype.card_congr e).symm

/-- PK20 Lemma `lm:LP-simple-cws` in the specialization used for the upper
distance bound: if the quotient matrix has fewer rows than columns, an actual
nontrivial cocycle of the lifted product has weight exactly the cyclic lift.
This is derived from the constant/augmentation chain-map splitting and is not
part of Proposition 1. -/
theorem middleCohomologyDistanceAtMost_lift
    {G aRow aCol : Type}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (x : G) (hOdd : Odd (Fintype.card G))
    (hCard : Fintype.card aRow < Fintype.card aCol) :
    MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.liftedProductData A x))
      (Fintype.card G) := by
  obtain ⟨c, hc⟩ := exists_standardBasis_not_coboundary A hCard
  let e : Word (ZMod 2) aCol := Pi.single c 1
  have heCocycle : e ∈
      (HorizontalSubsystem.quotientTannerComplex A).middleCocycleCode.carrier := by
    rw [(HorizontalSubsystem.quotientTannerComplex A).mem_middleCocycleCode_iff]
    simp [HorizontalSubsystem.quotientTannerComplex,
      wordLinearMapTranspose_zero]
  let eCocycle :
      (HorizontalSubsystem.quotientTannerComplex A).middleCocycleCode.carrier :=
    ⟨e, heCocycle⟩
  let f := HorizontalSubsystem.augmentationChainMap A x
  let s := HorizontalSubsystem.constantChainMap A x
  let z := wordLinearMapTranspose f.map1 e
  have hzCocycle : z ∈
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).middleCocycleCode.carrier :=
    (f.mapMiddleCocycle eCocycle).2
  have heClassNe :
      (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
        eCocycle ≠ 0 := by
    intro hzero
    apply hc
    change eCocycle ∈
      (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles
    exact (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hzNotCoboundary : z ∉
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A x)).firstCoboundaryCheckCode.carrier := by
    intro hzBoundary
    have hzClassZero :
        (LiftedProduct.chainComplex
          (Cyclic.liftedProductData A x)).middleCoboundaryInCocycles.mkQ
            (f.mapMiddleCocycle eCocycle) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hzBoundary
    apply heClassNe
    have hComposition := ThreeTermChainMap.inducedMiddleCohomology_comp f s
    have hSplit : (f.comp s).inducedMiddleCohomology = LinearMap.id := by
      apply LinearMap.ext
      intro y
      change (f.comp s).inducedMiddleCohomology y = y
      obtain ⟨representative, rfl⟩ :=
        (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ_surjective y
      rw [ThreeTermChainMap.inducedMiddleCohomology_mk]
      congr 1
      apply Subtype.ext
      change wordLinearMapTranspose ((f.comp s).map1) representative.1 =
        representative.1
      rw [ThreeTermChainMap.comp_map1]
      have hMap1 : f.map1.comp s.map1 =
          (LinearMap.id : Word (ZMod 2) aCol →ₗ[ZMod 2]
            Word (ZMod 2) aCol) := by
        dsimp [f, s, HorizontalSubsystem.augmentationChainMap,
          HorizontalSubsystem.constantChainMap]
        exact HorizontalSubsystem.horizontalAugmentation_comp_horizontalConstant_of_odd
          (aRow := aRow) hOdd
      rw [hMap1, wordLinearMapTranspose_id]
      rfl
    calc
      (HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
          eCocycle =
          (f.comp s).inducedMiddleCohomology
            ((HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
              eCocycle) := by rw [hSplit]; rfl
      _ = s.inducedMiddleCohomology
          (f.inducedMiddleCohomology
            ((HorizontalSubsystem.quotientTannerComplex A).middleCoboundaryInCocycles.mkQ
              eCocycle)) := by rw [hComposition]; rfl
      _ = 0 := by rw [ThreeTermChainMap.inducedMiddleCohomology_mk, hzClassZero, map_zero]
  refine ⟨z, hzCocycle, hzNotCoboundary, ?_⟩
  change HammingWeight
      (wordLinearMapTranspose
        (HorizontalSubsystem.horizontalAugmentation
          (aRow := aRow) (aCol := aCol) (G := G)) e) ≤ _
  rw [show e = Pi.single c 1 by rfl,
    HammingWeight_transpose_horizontalAugmentation_single]

/-- The canonical block length of `LP(A,1+x)` in the PK20 specialization. -/
def blockLength
    {aRow aCol : Type} [Fintype aRow] [Fintype aCol]
    (q : Nat) [NeZero q]
    (_A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) : Nat :=
  Fintype.card
    (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q))

/-- The certified common lower bound on the two CSS logical distances. -/
def certifiedDistanceLowerBound
    (q w radiusDenominator expansionNumerator expansionDenominator : Nat) : Nat :=
  let threshold := q / (2 * w * radiusDenominator)
  expansionNumerator * threshold /
    max (2 * expansionNumerator) (4 * expansionDenominator)

/--
Exact finite output used to assemble PK20 Theorem 1.  The displayed `K`
window is the integral form of `K = Theta(n)`, while the final inequality is
the source's `Omega(q)` distance bound with every constant exposed.  Together
with `N = q(wn+m)` and `n = Theta(log q)`, these are the construction-indexed
integer statements behind `K = Theta(log N)` and `D = Omega(N/log N)`.

This is a conclusion certificate, never an input premise.
-/
def FirstFamilyMember
    (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m : Nat)
    [NeZero q]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) : Prop :=
  let K := Module.finrank (ZMod 2)
    (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology
  let d := certifiedDistanceLowerBound q w radiusDenominator
    expansionNumerator expansionDenominator
  Odd q ∧
    m = 2 * (w / 4) * n ∧
    gamma * Nat.log 2 q ≤ n ∧
    n ≤ gamma * (Nat.log 2 q + 1) ∧
    blockLength q A = q * (w * n + m) ∧
    w * n - m ≤ K ∧
    K ≤ w * n + m ∧
    (LiftedProduct.binaryCSSCode (Cyclic.data q A)).stabilizer.IsSourceValidBinary ∧
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.data q A)).localityProfile (w + 2) ∧
    MiddleHomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) d ∧
    MiddleCohomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) d ∧
    MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.data q A)) q ∧
    max (2 * expansionNumerator) (4 * expansionDenominator) * d ≤
      expansionNumerator * (q / (2 * w * radiusDenominator))

private theorem one_le_of_pos {a : Nat} (ha : 0 < a) : 1 ≤ a := ha

/-- Complete finite construction from the raw output of PK20 Proposition 1.
The two elementary scale conditions merely say that the selected cyclic lift
is beyond the fixed constants of that proposition; the family assembly below
selects such odd lifts cofinally. -/
theorem firstFamilyMember_of_propositionOne_output
    (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m : Nat)
    [NeZero q]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (hw4 : 4 ≤ w)
    (hgamma : 0 < gamma)
    (hRadiusNumerator : 0 < radiusNumerator)
    (hRadiusDenominator : 0 < radiusDenominator)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hExpansionDenominator : 0 < expansionDenominator)
    (hqOdd : Odd q)
    (hm : m = 2 * (w / 4) * n)
    (hnLower : gamma * Nat.log 2 q ≤ n)
    (hnUpper : n ≤ gamma * (Nat.log 2 q + 1))
    (hDenominatorLeN : radiusDenominator ≤ n)
    (hLiftLarge : 2 * w * radiusDenominator ≤ q)
    (hForwardWeight : ∀ i : Fin (w * n) × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : Fin m × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hForwardRelative :
      (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator)
    (hTransposeRelative :
      (PKDistance.tannerAction
        (LiftedProduct.starTranspose A)).SmallSetExpandingAtRelativeRadius
          radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator) :
    FirstFamilyMember w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A := by
  have hqTwo : 2 ≤ q := by
    have hwOne : 1 ≤ w := one_le_of_pos (lt_of_lt_of_le (by norm_num) hw4)
    have hDenominatorOne : 1 ≤ radiusDenominator := one_le_of_pos hRadiusDenominator
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hwOne) hDenominatorOne).trans
      hLiftLarge
  have hLogPositive : 0 < Nat.log 2 q := by
    exact Nat.log_pos (by norm_num) hqTwo
  have hnPositive : 0 < n := by
    have := Nat.mul_pos hgamma hLogPositive
    omega
  have hwPositive : 0 < w := lt_of_lt_of_le (by norm_num) hw4
  have hwDiv : 1 ≤ w / 4 := Nat.le_div_iff_mul_le (by norm_num) |>.2 (by simpa using hw4)
  have hmPositive : 0 < m := by
    rw [hm]
    positivity
  have hDenominatorLeM : radiusDenominator ≤ m := by
    rw [hm]
    nlinarith
  let threshold := q / (2 * w * radiusDenominator)
  let coefficient := max (2 * expansionNumerator) (4 * expansionDenominator)
  let d := expansionNumerator * threshold / coefficient
  have hDivisorPositive : 0 < 2 * w * radiusDenominator := by positivity
  have hThresholdPositive : 0 < threshold := by
    exact Nat.div_pos hLiftLarge hDivisorPositive
  have hThresholdScale : 2 * w * threshold ≤ q := by
    calc
      2 * w * threshold ≤ (2 * w * threshold) * radiusDenominator := by
        exact Nat.le_mul_of_pos_right _ hRadiusDenominator
      _ = (2 * w * radiusDenominator) * threshold := by ring
      _ ≤ q := Nat.mul_div_le q (2 * w * radiusDenominator)
  have hForwardCaseOneRadius :
      radiusDenominator * (q * 1) ≤
        radiusNumerator *
          Fintype.card (Fin (w * n) × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    have hbase : radiusDenominator ≤ radiusNumerator * (w * n) := by
      calc
        radiusDenominator ≤ n := hDenominatorLeN
        _ ≤ radiusNumerator * (w * n) := by
          simpa [Nat.mul_assoc] using
            (Nat.le_mul_of_pos_left n
              (Nat.mul_pos hRadiusNumerator hwPositive))
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right q hbase
  have hTransposeCaseOneRadius :
      radiusDenominator * (q * 1) ≤
        radiusNumerator *
          Fintype.card (Fin m × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    have hbase : radiusDenominator ≤ radiusNumerator * m := by
      exact hDenominatorLeM.trans
        (Nat.le_mul_of_pos_left m hRadiusNumerator)
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right q hbase
  have hRadiusTimesThreshold : radiusDenominator * threshold ≤ q := by
    calc
      radiusDenominator * threshold ≤
          (2 * w) * (radiusDenominator * threshold) := by
        exact Nat.le_mul_of_pos_left _ (by positivity)
      _ = (2 * w * radiusDenominator) * threshold := by ring
      _ ≤ q := Nat.mul_div_le q (2 * w * radiusDenominator)
  have hForwardCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (Fin (w * n) × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    calc
      radiusDenominator * threshold ≤ q := hRadiusTimesThreshold
      _ ≤ radiusNumerator * ((w * n) * q) := by
        simpa [Nat.mul_assoc] using
          (Nat.le_mul_of_pos_left q
            (Nat.mul_pos hRadiusNumerator (Nat.mul_pos hwPositive hnPositive)))
  have hTransposeCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (Fin m × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    calc
      radiusDenominator * threshold ≤ q := hRadiusTimesThreshold
      _ ≤ radiusNumerator * (m * q) := by
        simpa [Nat.mul_assoc] using
          (Nat.le_mul_of_pos_left q
            (Nat.mul_pos hRadiusNumerator hmPositive))
  have hCoefficientPositive : 0 < coefficient := by
    exact lt_of_lt_of_le (by positivity) (Nat.le_max_left _ _)
  have hLower : coefficient * d ≤
      expansionNumerator * min (q * 1) threshold := by
    have hThresholdLeQ : threshold ≤ q :=
      (Nat.div_le_self q _)
    simp only [mul_one, Nat.min_eq_right hThresholdLeQ]
    exact Nat.mul_div_le _ _
  have hFinite := finite_distance_locality_of_relativeExpansion
    q hqTwo A 1 1 w threshold
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator d
    (by norm_num) (by norm_num) hExpansionNumerator hwPositive
      hThresholdPositive hThresholdScale hForwardWeight hTransposeWeight
      hForwardRelative hTransposeRelative hForwardCaseOneRadius
      hForwardCaseTwoRadius hTransposeCaseOneRadius
      hTransposeCaseTwoRadius hLower hLower
  have hDimension := finrank_middleHomology_bounds q hqOdd A
  unfold FirstFamilyMember
  dsimp only
  have hRowsLtColumns : m < w * n := by
    rw [hm]
    have hFactor : 2 * (w / 4) < w := by omega
    simpa [Nat.mul_assoc] using
      (Nat.mul_lt_mul_of_pos_right hFactor hnPositive)
  have hUpperRaw := middleCohomologyDistanceAtMost_lift A
    (Cyclic.cyclicGenerator q)
    (by simpa [Cyclic.CyclicGroup, ZMod.card] using hqOdd)
    (by simpa using hRowsLtColumns)
  have hUpper : MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.data q A)) q := by
    simpa [Cyclic.data, Cyclic.CyclicGroup, ZMod.card] using hUpperRaw
  refine ⟨hqOdd, hm, hnLower, hnUpper, ?_, ?_, ?_, hFinite.1,
    hFinite.2.1, hFinite.2.2.1, hFinite.2.2.2, hUpper, ?_⟩
  · simpa [blockLength] using
      (Cyclic.card_qubitIndex (aRow := Fin m) (aCol := Fin (w * n)) q)
  · simpa using hDimension.1
  · simpa using hDimension.2
  · have hThresholdLeQ : threshold ≤ q := Nat.div_le_self q _
    simpa [certifiedDistanceLowerBound, threshold, coefficient, d,
      Nat.min_eq_right hThresholdLeQ] using hLower

/-- Cofinal exact family statement for PK20 Theorem 1.  The constants are
chosen once; only the odd cyclic lift and the Proposition 1 matrix vary. -/
def FirstAlmostLinearFamily : Prop :=
  ∃ (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat),
    4 ≤ w ∧
    0 < gamma ∧
    0 < radiusNumerator ∧
    0 < radiusDenominator ∧
    0 < expansionNumerator ∧
    0 < expansionDenominator ∧
    ∀ B : Nat,
      ∃ (q n m : Nat) (_hq : NeZero q)
        (A : Matrix (Fin m) (Fin (w * n))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))),
        B < q ∧
        FirstFamilyMember w gamma radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator q n m A

/-- A concrete cofinal odd lift large enough for all fixed constants. -/
def familyLift
    (w radiusDenominator B : Nat) : Nat :=
  2 * (B + 2 ^ radiusDenominator + 2 * w * radiusDenominator) + 1

theorem familyLift_odd (w radiusDenominator B : Nat) :
    Odd (familyLift w radiusDenominator B) := by
  exact odd_two_mul_add_one _

theorem familyLift_gt (w radiusDenominator B : Nat) :
    B < familyLift w radiusDenominator B := by
  unfold familyLift
  have hB : B ≤ B + 2 ^ radiusDenominator + 2 * w * radiusDenominator := by
    exact (Nat.le_add_right B (2 ^ radiusDenominator)).trans
      (Nat.le_add_right _ (2 * w * radiusDenominator))
  have hDouble : B + 2 ^ radiusDenominator + 2 * w * radiusDenominator ≤
      2 * (B + 2 ^ radiusDenominator + 2 * w * radiusDenominator) := by
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  exact lt_of_le_of_lt (hB.trans hDouble) (Nat.lt_succ_self _)

theorem two_pow_radiusDenominator_le_familyLift
    (w radiusDenominator B : Nat) :
    2 ^ radiusDenominator ≤ familyLift w radiusDenominator B := by
  unfold familyLift
  have hTerm : 2 ^ radiusDenominator ≤
      B + 2 ^ radiusDenominator + 2 * w * radiusDenominator := by
    exact (Nat.le_add_left _ B).trans
      (Nat.le_add_right _ (2 * w * radiusDenominator))
  exact hTerm.trans
    ((Nat.le_mul_of_pos_left _ (by norm_num)).trans (Nat.le_succ _))

theorem liftScale_le_familyLift
    (w radiusDenominator B : Nat) :
    2 * w * radiusDenominator ≤ familyLift w radiusDenominator B := by
  unfold familyLift
  have hTerm : 2 * w * radiusDenominator ≤
      B + 2 ^ radiusDenominator + 2 * w * radiusDenominator :=
    Nat.le_add_left _ _
  exact hTerm.trans
    ((Nat.le_mul_of_pos_left _ (by norm_num)).trans (Nat.le_succ _))

/-- Proposition 1 alone supplies the complete first PK20 family. -/
theorem firstAlmostLinearFamily_of_propositionOne
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    FirstAlmostLinearFamily := by
  rcases hPropositionOne with
    ⟨w, gamma, radiusNumerator, radiusDenominator,
      expansionNumerator, expansionDenominator,
      hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
      hExpansionNumerator, hExpansionDenominator, hMatrices⟩
  refine ⟨w, gamma, radiusNumerator, radiusDenominator,
    expansionNumerator, expansionDenominator,
    hw4, hgamma, hRadiusNumerator, hRadiusDenominator,
    hExpansionNumerator, hExpansionDenominator, ?_⟩
  intro B
  let q := familyLift w radiusDenominator B
  have hqOdd : Odd q := familyLift_odd w radiusDenominator B
  have hqTwo : 1 < q := by
    unfold q familyLift
    have hPowPositive : 0 < 2 ^ radiusDenominator := pow_pos (by norm_num) _
    omega
  letI : NeZero q := ⟨by omega⟩
  obtain ⟨n, m, A, hm, hnLower, hnUpper,
      hForwardWeight, hTransposeWeight,
      hForwardRelative, hTransposeRelative⟩ := hMatrices q hqTwo
  have hDenominatorLog : radiusDenominator ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact two_pow_radiusDenominator_le_familyLift w radiusDenominator B
  have hDenominatorLeN : radiusDenominator ≤ n := by
    have hGammaOne : 1 ≤ gamma := hgamma
    calc
      radiusDenominator ≤ Nat.log 2 q := hDenominatorLog
      _ ≤ gamma * Nat.log 2 q := Nat.le_mul_of_pos_left _ hgamma
      _ ≤ n := hnLower
  have hLiftLarge : 2 * w * radiusDenominator ≤ q :=
    liftScale_le_familyLift w radiusDenominator B
  refine ⟨q, n, m, inferInstance, A, familyLift_gt w radiusDenominator B, ?_⟩
  exact firstFamilyMember_of_propositionOne_output
    w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A
    hw4 hgamma hRadiusNumerator hRadiusDenominator
      hExpansionNumerator hExpansionDenominator hqOdd hm hnLower hnUpper
      hDenominatorLeN hLiftLarge hForwardWeight hTransposeWeight
      hForwardRelative hTransposeRelative

end QEC.Coding.ExpanderCodes.PK20
