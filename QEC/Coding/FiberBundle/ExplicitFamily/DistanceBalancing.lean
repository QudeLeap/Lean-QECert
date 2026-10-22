import QEC.Coding.CodeReduction.DistanceBalancing.Dimension
import QEC.Coding.FiberBundle.ClassicalLDPCBalance
import QEC.Coding.FiberBundle.ExplicitFamily.CohomologyDimension

/-!
# HHO20 weight reduction followed by EKZ distance balancing

This module instantiates the finite EKZ product with the dual of the
weight-reduced HHO20 fiber-bundle complex.  The separate classical factor is
the construction-owned bounded-degree code from `ClassicalLDPCBalance`.
-/

namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing

open QEC.Coding

abbrev MainRelation
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  baseSupportRelation
    (RandomTwist.fiberBundleData baseSample twistSample)

abbrev MainReducedCheck
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  ClassicalWeightReduction.WeightReducedCheck
    (MainRelation baseSample twistSample)

abbrev MainReducedBit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  ClassicalWeightReduction.WeightReducedBit
    (MainRelation baseSample twistSample)

abbrev MainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  C0Index (MainReducedCheck baseSample twistSample) (ZMod (ell * ell))

abbrev MainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  QubitIndex
    (MainReducedCheck baseSample twistSample)
    (MainReducedBit baseSample twistSample)
    (ZMod (ell * ell)) (ZMod (ell * ell))

abbrev MainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  C2Index (MainReducedBit baseSample twistSample) (ZMod (ell * ell))

abbrev BalanceBit {r : Nat} (sample : RandomBase.Sample r) :=
  ClassicalWeightReduction.WeightReducedBit
    (RandomBase.incidenceRelation sample)

abbrev BalanceCheck {r : Nat} (sample : RandomBase.Sample r) :=
  ClassicalWeightReduction.WeightReducedCheck
    (RandomBase.incidenceRelation sample)

noncomputable instance instDecidableEqMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (MainCZero baseSample twistSample) := Classical.decEq _

noncomputable instance instDecidableEqMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (MainQubit baseSample twistSample) := Classical.decEq _

noncomputable instance instDecidableEqMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (MainCTwo baseSample twistSample) := Classical.decEq _

/-- The weight-reduced HHO20 chain complex before dualizing. -/
noncomputable def mainComplex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (MainCZero baseSample twistSample))
      (Word (ZMod 2) (MainQubit baseSample twistSample))
      (Word (ZMod 2) (MainCTwo baseSample twistSample)) :=
  chainComplex
    (weightReducedData
      (RandomTwist.fiberBundleData baseSample twistSample))

/-- The actual finite EKZ datum; both factors are converted to matrices only
inside `Data.ofComplexes`. -/
noncomputable def balancedData
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    DistanceBalancing.Data
      (MainCTwo baseSample twistSample)
      (MainQubit baseSample twistSample)
      (MainCZero baseSample twistSample)
      (BalanceBit balanceSample) (BalanceCheck balanceSample) :=
  by
    classical
    exact DistanceBalancing.Data.ofComplexes
      (dualChainComplex (mainComplex baseSample twistSample))
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (RandomBase.incidenceRelation balanceSample))

@[simp]
theorem balancedData_sourceChainComplex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    DistanceBalancing.sourceChainComplex
        (balancedData baseSample twistSample balanceSample) =
      dualChainComplex (mainComplex baseSample twistSample) := by
  classical
  simp [balancedData]

/-- Homological distance retained by the main HHO20 complex after weight
reduction. -/
def mainReducedHomologyDistance (r ell Delta : Nat) : Nat :=
  ((ell * (4 * r)) / (5000 * Delta)) / (101 * Delta)

/-- Cohomological distance retained by the main HHO20 complex after weight
reduction. -/
def mainReducedCohomologyDistance (r ell Delta : Nat) : Nat :=
  (min ((ell * ell) / 2) ((6 * r) / (100000 * Delta))) /
    (101 * Delta)

/-- Finite HHO20--EKZ distance theorem.  The only hypotheses are properties
of concrete construction witnesses; the hierarchy theorem below selects
those witnesses without assumptions. -/
theorem balanced_distanceBounds
    {rMain typeCount ell DeltaMain rBalance DeltaBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance)
    (hDeltaMain : 1 ≤ DeltaMain)
    (hMainGood : RandomBase.IsFullyGood
      (Delta := DeltaMain) baseSample)
    (hLTC : TwistGraph.HasHHO20LocalTestability
      DeltaMain baseSample twistSample)
    (hDeltaBalance : 1 ≤ DeltaBalance)
    (hBalanceGood : RandomBase.IsFullyGood
      (Delta := DeltaBalance) balanceSample) :
    MiddleHomologyDistanceAtLeast
        (DistanceBalancing.chainComplex
          (balancedData baseSample twistSample balanceSample))
        (((4 * rBalance) / 5) *
          mainReducedCohomologyDistance rMain ell DeltaMain) ∧
      MiddleCohomologyDistanceAtLeast
        (DistanceBalancing.chainComplex
          (balancedData baseSample twistSample balanceSample))
        (mainReducedHomologyDistance rMain ell DeltaMain) := by
  let mainData := RandomTwist.fiberBundleData baseSample twistSample
  let reducedData := weightReducedData mainData
  let K := mainComplex baseSample twistSample
  have hInitialHomology :
      HomologyDistanceAtLeast mainData
        ((ell * (4 * rMain)) / (5000 * DeltaMain)) :=
    homologyDistanceAtLeast_explicit
      baseSample twistSample hMainGood.1.2.1 hMainGood.1.2.2 hLTC
        hDeltaMain
  have hInitialCohomology :
      CohomologyDistanceAtLeast mainData
        (min ((ell * ell) / 2)
          ((6 * rMain) / (100000 * DeltaMain))) := by
    simpa only [ZMod.card] using
      (cohomologyDistanceAtLeast_explicit
        baseSample twistSample hMainGood.1.2.1 hDeltaMain
          hMainGood.1.1 hMainGood.2)
  have hReducedHomology :
      MiddleHomologyDistanceAtLeast K
        (mainReducedHomologyDistance rMain ell DeltaMain) := by
    exact RandomBase.homologyDistanceAtLeast_weightReduced_randomFiberBundleData
      baseSample twistSample hDeltaMain hMainGood hInitialHomology
  have hReducedCohomology :
      MiddleCohomologyDistanceAtLeast K
        (mainReducedCohomologyDistance rMain ell DeltaMain) := by
    exact RandomBase.cohomologyDistanceAtLeast_weightReduced_randomFiberBundleData
      baseSample twistSample hDeltaMain hMainGood hInitialCohomology
  have hDualHomology :
      MiddleHomologyDistanceAtLeast (dualChainComplex K)
        (mainReducedCohomologyDistance rMain ell DeltaMain) :=
    (middleHomologyDistanceAtLeast_dual_iff K _).2 hReducedCohomology
  have hDualCohomology :
      MiddleCohomologyDistanceAtLeast (dualChainComplex K)
        (mainReducedHomologyDistance rMain ell DeltaMain) :=
    (middleCohomologyDistanceAtLeast_dual_iff K _).2 hReducedHomology
  have hSurjective : Function.Surjective
      (Matrix.toLin'
        (balancedData baseSample twistSample balanceSample).classicalBoundary) := by
    simpa [balancedData] using
      (RandomBase.weightReducedBoundary_surjective
        balanceSample hDeltaBalance hBalanceGood)
  have hClassical : DistanceBalancing.ClassicalDistanceAtLeast
      (balancedData baseSample twistSample balanceSample).classicalBoundary
      ((4 * rBalance) / 5) := by
    simpa [balancedData] using
      (RandomBase.weightReducedClassicalDistanceAtLeast
        balanceSample hDeltaBalance hBalanceGood)
  apply DistanceBalancing.distanceBounds_of_classical_surjective
    (balancedData baseSample twistSample balanceSample) hSurjective
  · simpa [K] using hDualHomology
  · simpa [K] using hDualCohomology
  · exact hClassical

/-- The finite HHO20--EKZ product has at least the product of the two
construction parameters as logical dimension. -/
theorem mul_le_finrank_balanced_middleHomology
    {rMain typeCount ell DeltaMain rBalance DeltaBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance)
    (hDeltaMain : 1 ≤ DeltaMain)
    (hMainGood : RandomBase.IsFullyGood
      (Delta := DeltaMain) baseSample)
    (hDeltaBalance : 1 ≤ DeltaBalance)
    (hBalanceGood : RandomBase.IsFullyGood
      (Delta := DeltaBalance) balanceSample) :
    rMain * rBalance ≤
      Module.finrank (ZMod 2)
        (DistanceBalancing.chainComplex
          (balancedData baseSample twistSample balanceSample)).middleHomology := by
  let D := balancedData baseSample twistSample balanceSample
  have hMain : rMain ≤
      Module.finrank (ZMod 2)
        (DistanceBalancing.sourceChainComplex D).middleHomology := by
    rw [show DistanceBalancing.sourceChainComplex D =
        dualChainComplex (mainComplex baseSample twistSample) by
      simpa [D] using
        balancedData_sourceChainComplex baseSample twistSample balanceSample]
    rw [finrank_middleHomology_dual_eq_middleCohomology]
    rw [finrank_middleCohomology_eq_middleHomology]
    exact
      RandomBase.r_le_finrank_middleHomology_weightReduced_randomFiberBundleData
        baseSample twistSample hDeltaMain hMainGood
  have hBalance :
      Module.finrank (ZMod 2) (DistanceBalancing.ClassicalKernel D) =
        rBalance := by
    exact
      (RandomBase.finrank_weightReducedClassicalKernel_eq
        balanceSample hDeltaBalance hBalanceGood)
  calc
    rMain * rBalance ≤
        Module.finrank (ZMod 2)
            (DistanceBalancing.sourceChainComplex D).middleHomology *
          Module.finrank (ZMod 2) (DistanceBalancing.ClassicalKernel D) := by
      rw [hBalance]
      exact Nat.mul_le_mul_right rBalance hMain
    _ ≤ Module.finrank (ZMod 2)
          (DistanceBalancing.chainComplex D).middleHomology :=
      DistanceBalancing.finrank_middleHomology_mul_finrank_classicalKernel_le D

/-- Explicit blocklength bound for the finite balanced product. -/
theorem card_balancedQubit_le
    {rMain typeCount ell DeltaMain rBalance DeltaBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance)
    (hMainGood : RandomBase.IsFullyGood
      (Delta := DeltaMain) baseSample)
    (hBalanceGood : RandomBase.IsFullyGood
      (Delta := DeltaBalance) balanceSample) :
    Fintype.card
        (DistanceBalancing.QubitIndex
          (MainQubit baseSample twistSample)
          (MainCZero baseSample twistSample)
          (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
      2611456 * rMain * DeltaMain * (ell * ell) *
        rBalance * DeltaBalance := by
  let M := 1616 * rMain * DeltaMain * (ell * ell)
  have hMainQ :
      Fintype.card (MainQubit baseSample twistSample) ≤ M := by
    exact RandomBase.card_qubitIndex_weightReduced_randomFiberBundleData_le
      baseSample twistSample hMainGood
  have hMainCZeroToQ :
      Fintype.card (MainCZero baseSample twistSample) ≤
        Fintype.card (MainQubit baseSample twistSample) := by
    simp only [MainCZero, MainQubit, C0Index, QubitIndex,
      Fintype.card_prod, Fintype.card_sum]
    omega
  have hMainCZero :
      Fintype.card (MainCZero baseSample twistSample) ≤ M :=
    hMainCZeroToQ.trans hMainQ
  have hBalanceBit :=
    RandomBase.card_weightReducedClassicalBit_le
      balanceSample hBalanceGood
  have hBalanceCheck :=
    RandomBase.card_weightReducedClassicalCheck_le
      balanceSample hBalanceGood
  rw [DistanceBalancing.card_qubitIndex]
  calc
    Fintype.card (MainQubit baseSample twistSample) *
          Fintype.card (BalanceBit balanceSample) +
        Fintype.card (MainCZero baseSample twistSample) *
          Fintype.card (BalanceCheck balanceSample) ≤
      M * Fintype.card (BalanceBit balanceSample) +
        M * Fintype.card (BalanceCheck balanceSample) := by
          gcongr
    _ = M *
        (Fintype.card (BalanceBit balanceSample) +
          Fintype.card (BalanceCheck balanceSample)) := by ring
    _ ≤ M * (808 * rBalance * DeltaBalance +
        808 * rBalance * DeltaBalance) := by
          exact Nat.mul_le_mul_left M (Nat.add_le_add
            hBalanceBit hBalanceCheck)
    _ = 2611456 * rMain * DeltaMain * (ell * ell) *
        rBalance * DeltaBalance := by
          simp only [M]
          ring

/-- Final homological distance expression at hierarchy index `s`; the main
HHO20 code is taken at `2s` and the balancing code at `s`. -/
def balancedHomologyDistanceAt (s : Nat) : Nat :=
  ((4 * RandomPartition.hho20BaseScale s) / 5) *
    mainReducedCohomologyDistance
      (RandomPartition.hho20BaseScale (2 * s))
      (RandomPartition.hho20FiberLength (2 * s))
      (RandomPartition.hho20DegreeScale (2 * s))

/-- Final cohomological distance expression at hierarchy index `s`. -/
def balancedCohomologyDistanceAt (s : Nat) : Nat :=
  mainReducedHomologyDistance
    (RandomPartition.hho20BaseScale (2 * s))
    (RandomPartition.hho20FiberLength (2 * s))
    (RandomPartition.hho20DegreeScale (2 * s))

/-- Explicit blocklength envelope at hierarchy index `s`. -/
def balancedBlocklengthUpperAt (s : Nat) : Nat :=
  2611456 * RandomPartition.hho20BaseScale (2 * s) *
    RandomPartition.hho20DegreeScale (2 * s) *
    (RandomPartition.hho20FiberLength (2 * s) *
      RandomPartition.hho20FiberLength (2 * s)) *
    RandomPartition.hho20BaseScale s *
    RandomPartition.hho20DegreeScale s

/-- Assumption-free existence of the finite distance-balanced code at every
hierarchy index `s ≥ 200`. -/
theorem exists_distanceBalancedCode_at
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
      ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale (2 * s)))
        (twistSample : RandomTwist.Sample
          (RandomPartition.hho20BaseScale (2 * s))
          (RandomPartition.hho20TypeCount (2 * s))
          (RandomPartition.hho20FiberLength (2 * s)))
        (balanceSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale s)),
      (MiddleHomologyDistanceAtLeast
          (DistanceBalancing.chainComplex
            (balancedData baseSample twistSample balanceSample))
          (balancedHomologyDistanceAt s) ∧
        MiddleCohomologyDistanceAtLeast
          (DistanceBalancing.chainComplex
            (balancedData baseSample twistSample balanceSample))
          (balancedCohomologyDistanceAt s)) ∧
        Fintype.card
            (DistanceBalancing.QubitIndex
              (MainQubit baseSample twistSample)
              (MainCZero baseSample twistSample)
              (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
          balancedBlocklengthUpperAt s ∧
        RandomPartition.hho20BaseScale (2 * s) *
            RandomPartition.hho20BaseScale s ≤
          Module.finrank (ZMod 2)
            (DistanceBalancing.chainComplex
              (balancedData baseSample twistSample balanceSample)).middleHomology ∧
        RandomBase.IsFullyGood
          (Delta := RandomPartition.hho20DegreeScale (2 * s)) baseSample ∧
        TwistGraph.HasHHO20LocalTestability
          (RandomPartition.hho20DegreeScale (2 * s))
          baseSample twistSample ∧
        RandomBase.IsFullyGood
          (Delta := RandomPartition.hho20DegreeScale s) balanceSample := by
  have hMainIndex : 200 ≤ 2 * s := by omega
  letI : NeZero (RandomPartition.hho20BaseScale (2 * s)) :=
    ⟨by
      have := RandomPartition.hho20_baseScale_ge_five_hundred
        (2 * s) hMainIndex
      omega⟩
  letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
    ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
  letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
      omega⟩
  letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
      omega⟩
  obtain ⟨baseSample, twistSample, hMainGood, _hChecks,
      _hSpectrum, hLTC⟩ :=
    RandomPartition.exists_hho20_base_and_twist_at (2 * s) hMainIndex
  letI : NeZero (RandomPartition.hho20BaseScale s) :=
    ⟨by
      have := RandomPartition.hho20_baseScale_ge_five_hundred s hs
      omega⟩
  letI : NeZero (RandomPartition.hho20TypeCount s) :=
    ⟨RandomPartition.hho20TypeCount_ne_zero s (by omega)⟩
  letI : NeZero (RandomPartition.hho20FiberLength s) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge s (by omega)
      omega⟩
  letI : NeZero (RandomPartition.hho20FiberLength s - 1) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge s (by omega)
      omega⟩
  obtain ⟨balanceSample, _balanceTwist, hBalanceGood,
      _hBalanceChecks, _hBalanceSpectrum, _hBalanceLTC⟩ :=
    RandomPartition.exists_hho20_base_and_twist_at s hs
  have hDeltaMain : 1 ≤ RandomPartition.hho20DegreeScale (2 * s) := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [RandomPartition.hho20DegreeScale,
        RandomPartition.hho20TypeCount]
      positivity)
  have hDeltaBalance : 1 ≤ RandomPartition.hho20DegreeScale s := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [RandomPartition.hho20DegreeScale,
        RandomPartition.hho20TypeCount]
      positivity)
  refine ⟨baseSample, twistSample, balanceSample, ?_, ?_, ?_,
    hMainGood, hLTC, hBalanceGood⟩
  · simpa [balancedHomologyDistanceAt, balancedCohomologyDistanceAt] using
      (balanced_distanceBounds
        baseSample twistSample balanceSample
        hDeltaMain hMainGood hLTC hDeltaBalance hBalanceGood)
  · change Fintype.card
        (DistanceBalancing.QubitIndex
          (MainQubit baseSample twistSample)
          (MainCZero baseSample twistSample)
          (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
        2611456 * RandomPartition.hho20BaseScale (2 * s) *
          RandomPartition.hho20DegreeScale (2 * s) *
          (RandomPartition.hho20FiberLength (2 * s) *
            RandomPartition.hho20FiberLength (2 * s)) *
          RandomPartition.hho20BaseScale s *
          RandomPartition.hho20DegreeScale s
    exact card_balancedQubit_le
      baseSample twistSample balanceSample hMainGood hBalanceGood
  · exact mul_le_finrank_balanced_middleHomology
      baseSample twistSample balanceSample
      hDeltaMain hMainGood hDeltaBalance hBalanceGood

end QEC.Coding.FiberBundle.HHO20DistanceBalancing
