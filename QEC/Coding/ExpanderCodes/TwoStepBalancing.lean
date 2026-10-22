import QEC.Coding.BalancedProduct.HorizontalSubsystem
import QEC.Coding.CodeReduction.DistanceBalancing.Dimension
import QEC.Coding.CodeReduction.DistanceBalancing.Locality

/-!
# The two EKZ products used by PK20 Theorem 2

PK20 first tensors the almost-linear quantum complex with a good classical
code, dualizes, tensors once more, and dualizes back.  This file packages that
finite operation and proves its distance, dimension, locality, and source
validity consequences from the already proved EKZ20 Theorem 2.3 slice.

It does not choose the classical codes or assert an asymptotic exponent.
-/

namespace QEC.Coding.ExpanderCodes.PK20

open QEC.Coding
open QEC.Coding.DistanceBalancing

universe u

variable {xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype bitOne] [DecidableEq bitOne]
variable [Fintype checkOne] [DecidableEq checkOne]
variable [Fintype bitTwo] [DecidableEq bitTwo]
variable [Fintype checkTwo] [DecidableEq checkTwo]

noncomputable def firstBalancingData
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne) :=
  Data.ofComplexes X Y

abbrev FirstC0 (xZero xOne bitOne checkOne : Type u) :=
  C0Index xZero xOne bitOne checkOne
abbrev FirstQubit (xOne xTwo bitOne checkOne : Type u) :=
  QubitIndex xOne xTwo bitOne checkOne
abbrev FirstC2 (xTwo bitOne : Type u) := C2Index xTwo bitOne

noncomputable def firstBalancedComplex
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne) :=
  chainComplex (firstBalancingData X Y)

noncomputable def secondBalancingData
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :=
  Data.ofComplexes (dualChainComplex (firstBalancedComplex X Y₁)) Y₂

abbrev SecondC0
    (xOne xTwo bitOne checkOne bitTwo checkTwo : Type u) :=
  C0Index (FirstC2 xTwo bitOne)
    (FirstQubit xOne xTwo bitOne checkOne) bitTwo checkTwo
abbrev SecondQubit
    (xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u) :=
  QubitIndex (FirstQubit xOne xTwo bitOne checkOne)
    (FirstC0 xZero xOne bitOne checkOne) bitTwo checkTwo

noncomputable instance secondQubitDecidableEq :
    DecidableEq
      (SecondQubit xZero xOne xTwo bitOne checkOne bitTwo checkTwo) :=
  Classical.decEq _
abbrev SecondC2
    (xZero xOne bitOne checkOne bitTwo : Type u) :=
  C2Index (FirstC0 xZero xOne bitOne checkOne) bitTwo

/-- The final PK20 complex, oriented so the first and second classical
factors amplify the homological and cohomological distances respectively. -/
noncomputable def twiceBalancedComplex
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :=
  dualChainComplex (chainComplex (secondBalancingData X Y₁ Y₂))

/-- Exact number of physical qubits after the two PK20 homological products.
It is recorded before any asymptotic estimates, so neither product may hide a
change of family scale. -/
theorem card_twiceBalanced_qubits
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :
    Fintype.card
        (SecondQubit xZero xOne xTwo bitOne checkOne bitTwo checkTwo) =
      (Fintype.card xOne * Fintype.card bitOne +
          Fintype.card xTwo * Fintype.card checkOne) *
        Fintype.card bitTwo +
      (Fintype.card xZero * Fintype.card bitOne +
          Fintype.card xOne * Fintype.card checkOne) *
        Fintype.card checkTwo := by
  simp [SecondQubit, FirstQubit, FirstC0,
    DistanceBalancing.QubitIndex, DistanceBalancing.C0Index]

theorem firstBalancing_distanceBounds
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    {dHomology dCohomology dClassical : Nat}
    (hSurjective : Function.Surjective Y)
    (hHomology : MiddleHomologyDistanceAtLeast X dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast X dCohomology)
    (hClassical : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y) dClassical) :
    MiddleHomologyDistanceAtLeast (firstBalancedComplex X Y)
        (dClassical * dHomology) ∧
      MiddleCohomologyDistanceAtLeast (firstBalancedComplex X Y)
        dCohomology := by
  have hSourceHomology : MiddleHomologyDistanceAtLeast
      (sourceChainComplex (Data.ofComplexes X Y)) dHomology := by
    simpa using hHomology
  have hSourceCohomology : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex (Data.ofComplexes X Y)) dCohomology := by
    simpa using hCohomology
  simpa [firstBalancedComplex, firstBalancingData] using
    (distanceBounds_of_classical_surjective (Data.ofComplexes X Y)
      (by simpa using hSurjective) hSourceHomology hSourceCohomology hClassical)

/-- Both distances after the two products and the two orientation reversals. -/
theorem twiceBalanced_distanceBounds
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {dHomology dCohomology dClassicalOne dClassicalTwo : Nat}
    (hSurjectiveOne : Function.Surjective Y₁)
    (hSurjectiveTwo : Function.Surjective Y₂)
    (hHomology : MiddleHomologyDistanceAtLeast X dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast X dCohomology)
    (hClassicalOne : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₁) dClassicalOne)
    (hClassicalTwo : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₂) dClassicalTwo) :
    MiddleHomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
        (dClassicalOne * dHomology) ∧
      MiddleCohomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
        (dClassicalTwo * dCohomology) := by
  have hFirst := firstBalancing_distanceBounds X Y₁ hSurjectiveOne
    hHomology hCohomology hClassicalOne
  have hSecondSourceHomology : MiddleHomologyDistanceAtLeast
      (sourceChainComplex (secondBalancingData X Y₁ Y₂)) dCohomology := by
    simpa [secondBalancingData] using
      ((middleHomologyDistanceAtLeast_dual_iff
        (firstBalancedComplex X Y₁) dCohomology).2 hFirst.2)
  have hSecondSourceCohomology : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex (secondBalancingData X Y₁ Y₂))
        (dClassicalOne * dHomology) := by
    simpa [secondBalancingData] using
      ((middleCohomologyDistanceAtLeast_dual_iff
        (firstBalancedComplex X Y₁)
          (dClassicalOne * dHomology)).2 hFirst.1)
  have hSecond := distanceBounds_of_classical_surjective
    (secondBalancingData X Y₁ Y₂)
    (by simpa [secondBalancingData] using hSurjectiveTwo)
    hSecondSourceHomology hSecondSourceCohomology hClassicalTwo
  exact ⟨
    (middleHomologyDistanceAtLeast_dual_iff
      (chainComplex (secondBalancingData X Y₁ Y₂))
        (dClassicalOne * dHomology)).2 hSecond.2,
    (middleCohomologyDistanceAtLeast_dual_iff
      (chainComplex (secondBalancingData X Y₁ Y₂))
        (dClassicalTwo * dCohomology)).2 hSecond.1⟩

/-- Each classical kernel multiplies the encoded dimension. -/
theorem twiceBalanced_dimensionLowerBound
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :
    Module.finrank (ZMod 2) X.middleHomology *
        Module.finrank (ZMod 2) (LinearMap.ker Y₁) *
        Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤
      Module.finrank (ZMod 2)
        (twiceBalancedComplex X Y₁ Y₂).middleHomology := by
  have hFirst := finrank_middleHomology_mul_finrank_classicalKernel_le
    (firstBalancingData X Y₁)
  have hSecond := finrank_middleHomology_mul_finrank_classicalKernel_le
    (secondBalancingData X Y₁ Y₂)
  have hFirstCohomology :
      Module.finrank (ZMod 2) (firstBalancedComplex X Y₁).middleCohomology =
        Module.finrank (ZMod 2) (firstBalancedComplex X Y₁).middleHomology :=
    BalancedProduct.HorizontalSubsystem.finrank_middleCohomology_eq_middleHomology _
  change _ ≤ Module.finrank (ZMod 2)
    (chainComplex (secondBalancingData X Y₁ Y₂)).middleCohomology
  rw [BalancedProduct.HorizontalSubsystem.finrank_middleCohomology_eq_middleHomology]
  change _ ≤ Module.finrank (ZMod 2)
    (chainComplex (secondBalancingData X Y₁ Y₂)).middleHomology
  change Module.finrank (ZMod 2) X.middleHomology *
      Module.finrank (ZMod 2) (LinearMap.ker Y₁) *
      Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤ _
  have hFirst' : Module.finrank (ZMod 2) X.middleHomology *
      Module.finrank (ZMod 2) (LinearMap.ker Y₁) ≤
        Module.finrank (ZMod 2) (firstBalancedComplex X Y₁).middleHomology := by
    unfold firstBalancingData at hFirst
    rw [sourceChainComplex_ofComplexes] at hFirst
    change Module.finrank (ZMod 2) X.middleHomology *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix' Y₁))) ≤ _ at hFirst
    rw [Matrix.toLin'_toMatrix'] at hFirst
    exact hFirst
  have hSecond' : Module.finrank (ZMod 2)
      (dualChainComplex (firstBalancedComplex X Y₁)).middleHomology *
      Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤
        Module.finrank (ZMod 2)
          (chainComplex (secondBalancingData X Y₁ Y₂)).middleHomology := by
    unfold secondBalancingData at hSecond
    rw [sourceChainComplex_ofComplexes] at hSecond
    change Module.finrank (ZMod 2)
        (dualChainComplex (firstBalancedComplex X Y₁)).middleHomology *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix' Y₂))) ≤ _ at hSecond
    rw [Matrix.toLin'_toMatrix'] at hSecond
    exact hSecond
  rw [finrank_middleHomology_dual_eq_middleCohomology,
    hFirstCohomology] at hSecond'
  exact (Nat.mul_le_mul_right _ hFirst').trans hSecond'

/-- Uniform locality grows only by the two classical locality constants. -/
theorem twiceBalanced_boundedLocality
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {sourceBound classicalBoundOne classicalBoundTwo : Nat}
    (hSource : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceBound)
    (hRowOne : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₁ (Pi.single b 1)) ≤ classicalBoundOne)
    (hColumnOne : ∀ a, HammingWeight
      (Y₁ (Pi.single a 1)) ≤ classicalBoundOne)
    (hRowTwo : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₂ (Pi.single b 1)) ≤ classicalBoundTwo)
    (hColumnTwo : ∀ a, HammingWeight
      (Y₂ (Pi.single a 1)) ≤ classicalBoundTwo) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (twiceBalancedComplex X Y₁ Y₂)).localityProfile
      (sourceBound + classicalBoundOne + classicalBoundTwo) := by
  have hFirst := boundedLocality_add_ofComplexes_of_source_bounded
    X Y₁ hSource hRowOne hColumnOne
  have hFirstDual := boundedLocality_dual (firstBalancedComplex X Y₁) hFirst
  have hSecond := boundedLocality_add_ofComplexes_of_source_bounded
    (dualChainComplex (firstBalancedComplex X Y₁)) Y₂
    hFirstDual hRowTwo hColumnTwo
  exact boundedLocality_dual
    (chainComplex (secondBalancingData X Y₁ Y₂)) hSecond

/-- The final finite code is an actual source-valid binary CSS stabilizer. -/
theorem twiceBalanced_sourceValid
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :
    ((twiceBalancedComplex X Y₁ Y₂).binaryCSSCode).stabilizer.IsSourceValidBinary :=
  ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary _

/-- Finite conclusion package used verbatim by the asymptotic assembly.  All
fields below are proved consequences of the two input boundaries; this
certificate is never accepted as a theorem premise. -/
def TwiceBalancedMemberCertificate
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    (sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      locality : Nat) : Prop :=
  ((twiceBalancedComplex X Y₁ Y₂).binaryCSSCode).stabilizer.IsSourceValidBinary ∧
    Fintype.card
        (SecondQubit xZero xOne xTwo bitOne checkOne bitTwo checkTwo) =
      (Fintype.card xOne * Fintype.card bitOne +
          Fintype.card xTwo * Fintype.card checkOne) *
        Fintype.card bitTwo +
      (Fintype.card xZero * Fintype.card bitOne +
          Fintype.card xOne * Fintype.card checkOne) *
        Fintype.card checkTwo ∧
    sourceDimension * classicalDimensionOne * classicalDimensionTwo ≤
      Module.finrank (ZMod 2) (twiceBalancedComplex X Y₁ Y₂).middleHomology ∧
    MiddleHomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
      (classicalDistanceOne * sourceDistance) ∧
    MiddleCohomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
      (classicalDistanceTwo * sourceDistance) ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (twiceBalancedComplex X Y₁ Y₂)).localityProfile locality

/-- Complete finite EKZ closure used by PK20 Theorem 2. -/
theorem twiceBalancedMemberCertificate
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      sourceLocality classicalLocalityOne classicalLocalityTwo : Nat}
    (hSourceDimension : sourceDimension ≤
      Module.finrank (ZMod 2) X.middleHomology)
    (hClassicalDimensionOne : classicalDimensionOne ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y₁))
    (hClassicalDimensionTwo : classicalDimensionTwo ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y₂))
    (hSurjectiveOne : Function.Surjective Y₁)
    (hSurjectiveTwo : Function.Surjective Y₂)
    (hHomology : MiddleHomologyDistanceAtLeast X sourceDistance)
    (hCohomology : MiddleCohomologyDistanceAtLeast X sourceDistance)
    (hClassicalOne : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₁) classicalDistanceOne)
    (hClassicalTwo : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₂) classicalDistanceTwo)
    (hSourceLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceLocality)
    (hRowOne : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₁ (Pi.single b 1)) ≤ classicalLocalityOne)
    (hColumnOne : ∀ a, HammingWeight
      (Y₁ (Pi.single a 1)) ≤ classicalLocalityOne)
    (hRowTwo : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₂ (Pi.single b 1)) ≤ classicalLocalityTwo)
    (hColumnTwo : ∀ a, HammingWeight
      (Y₂ (Pi.single a 1)) ≤ classicalLocalityTwo) :
    TwiceBalancedMemberCertificate X Y₁ Y₂
      sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      (sourceLocality + classicalLocalityOne + classicalLocalityTwo) := by
  have hDistances := twiceBalanced_distanceBounds X Y₁ Y₂
    hSurjectiveOne hSurjectiveTwo hHomology hCohomology
    hClassicalOne hClassicalTwo
  have hDimensionRaw := twiceBalanced_dimensionLowerBound X Y₁ Y₂
  have hDimension :
      sourceDimension * classicalDimensionOne * classicalDimensionTwo ≤
        Module.finrank (ZMod 2) (twiceBalancedComplex X Y₁ Y₂).middleHomology := by
    exact (Nat.mul_le_mul
      (Nat.mul_le_mul hSourceDimension hClassicalDimensionOne)
      hClassicalDimensionTwo).trans hDimensionRaw
  exact ⟨twiceBalanced_sourceValid X Y₁ Y₂,
    card_twiceBalanced_qubits X Y₁ Y₂,
    hDimension, hDistances.1, hDistances.2,
    twiceBalanced_boundedLocality X Y₁ Y₂ hSourceLocality
      hRowOne hColumnOne hRowTwo hColumnTwo⟩

end QEC.Coding.ExpanderCodes.PK20
