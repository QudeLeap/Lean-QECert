import QEC.Coding.FiberBundle.Core
/-!
# Homological distance interfaces for fiber-bundle codes

The Hamming-weight statements in the HHO20 distance argument are statements
about representatives of nontrivial middle cohomology and homology classes.
This module connects those representative-level statements exactly to the
existing pure-X and pure-Z CSS minimum-distance predicates.

No distance estimate is accepted as construction data here.  In particular,
an exact sector minimum is equivalent to both:

* an explicit nontrivial representative attaining that weight; and
* a lower bound for every nontrivial representative in that sector.
-/

namespace QEC.Coding.FiberBundle

universe u

/-- Every nontrivial middle cocycle has Hamming weight at least `d`. -/
def CohomologyDistanceAtLeast
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) : Prop :=
  ∀ x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
    x ∈ (chainComplex D).middleCocycleCode.carrier →
    x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier →
    d ≤ HammingWeight x

/-- Every nontrivial middle cycle has Hamming weight at least `d`. -/
def HomologyDistanceAtLeast
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) : Prop :=
  ∀ z : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
    z ∈ (chainComplex D).middleCycleCode.carrier →
    z ∉ (chainComplex D).middleBoundaryCode.carrier →
    d ≤ HammingWeight z

/--
Exact pure-X distance is precisely an attained nontrivial cohomology weight
together with the corresponding universal lower bound.
-/
theorem binaryPureXMinimumDistance_iff_cohomology
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) :
    BinaryPureXMinimumDistance D d ↔
      (∃ x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
        x ∈ (chainComplex D).middleCocycleCode.carrier ∧
        x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier ∧
        HammingWeight x = d) ∧
      CohomologyDistanceAtLeast D d := by
  constructor
  · rintro ⟨x, hxAmbient, hxTrivial, hxWeight, hxLeast⟩
    refine ⟨⟨x, ?_, ?_, hxWeight⟩, ?_⟩
    · simpa only [binaryCSSCode_zCode,
        ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] using
        hxAmbient
    · simpa only [binaryCSSCode_xCode] using hxTrivial
    · intro y hyCocycle hyCoboundary
      apply hxLeast y
      · simpa only [binaryCSSCode_zCode,
          ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] using
          hyCocycle
      · simpa only [binaryCSSCode_xCode] using hyCoboundary
  · rintro ⟨⟨x, hxCocycle, hxCoboundary, hxWeight⟩, hxLeast⟩
    refine ⟨x, ?_, ?_, hxWeight, ?_⟩
    · simpa only [binaryCSSCode_zCode,
        ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] using
        hxCocycle
    · simpa only [binaryCSSCode_xCode] using hxCoboundary
    · intro y hyAmbient hyTrivial
      apply hxLeast y
      · simpa only [binaryCSSCode_zCode,
          ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] using
          hyAmbient
      · simpa only [binaryCSSCode_xCode] using hyTrivial

/--
Exact pure-Z distance is precisely an attained nontrivial homology weight
together with the corresponding universal lower bound.
-/
theorem binaryPureZMinimumDistance_iff_homology
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) :
    BinaryPureZMinimumDistance D d ↔
      (∃ z : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
        z ∈ (chainComplex D).middleCycleCode.carrier ∧
        z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
        HammingWeight z = d) ∧
      HomologyDistanceAtLeast D d := by
  constructor
  · rintro ⟨z, hzAmbient, hzTrivial, hzWeight, hzLeast⟩
    refine ⟨⟨z, ?_, ?_, hzWeight⟩, ?_⟩
    · simpa only [binaryCSSCode_xCode,
        ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] using
        hzAmbient
    · simpa only [binaryCSSCode_zCode] using hzTrivial
    · intro y hyCycle hyBoundary
      apply hzLeast y
      · simpa only [binaryCSSCode_xCode,
          ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] using
          hyCycle
      · simpa only [binaryCSSCode_zCode] using hyBoundary
  · rintro ⟨⟨z, hzCycle, hzBoundary, hzWeight⟩, hzLeast⟩
    refine ⟨z, ?_, ?_, hzWeight, ?_⟩
    · simpa only [binaryCSSCode_xCode,
        ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] using
        hzCycle
    · simpa only [binaryCSSCode_zCode] using hzBoundary
    · intro y hyAmbient hyTrivial
      apply hzLeast y
      · simpa only [binaryCSSCode_xCode,
          ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] using
          hyAmbient
      · simpa only [binaryCSSCode_zCode] using hyTrivial

end QEC.Coding.FiberBundle
