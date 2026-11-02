import QEC.Coding.FiberBundle.ExplicitFamily.Asymptotics

/-!
# Fiber-bundle qLDPC family

The final HHO20 existence and tradeoff assembly uses the reusable explicit
construction, scales and certificates in Coding.
-/

namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing

open QEC.Coding

universe u

/-- Exact, assumption-free HHO20 fiber-bundle and qLDPC family theorem.

For every hierarchy index `s ≥ 200`, the construction itself selects the
random Tanner base, rotation twists, and balancing code.  The unreduced
member carries `InitialFamilyCertificate`, including exact integer forms of
the source's square-root dimension, asymmetric X/Z distances, and
polylogarithmic locality.  The same base and twist witnesses then pass through
weight reduction and distance balancing.  The resulting binary CSS chain
complex is source-valid, has uniform locality `8`, and both CSS distance
sectors exceed `distanceScaleAt s`.  The final two inequalities are the
integer fifth-power form of `K,D = Ω(N^(3/5)/polylog N)`; `2^(6s) ≤ N`
records that `s` is a logarithmic family scale rather than an unrelated
external parameter. -/
theorem exists_hho20_binary_css_qldpc_family_at :
    ∀ (s : Nat), ∀ (hs : 200 ≤ s),
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
      let X := finalComplex
        baseSample twistSample balanceSample
      let N := Fintype.card
        (FinalQubitIndex baseSample twistSample balanceSample)
      let K := Module.finrank (ZMod 2) X.middleHomology
      InitialFamilyCertificate (2 * s) baseSample twistSample ∧
        (X.binaryCSSCode).stabilizer.IsSourceValidBinary ∧
        MiddleHomologyDistanceAtLeast X (distanceScaleAt s) ∧
        MiddleCohomologyDistanceAtLeast X (distanceScaleAt s) ∧
        BoundedLocality
          (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile 8 ∧
        dimensionScaleAt s ≤ K ∧
        N ≤ blocklengthScaleAt s ∧
        RandomPartition.hho20FiberLength s ^ 6 ≤ N ∧
        N ^ 3 ≤ dimensionTradeoffCoefficient * s ^ 12 * K ^ 5 ∧
        N ^ 3 ≤ distanceTradeoffCoefficient * s ^ 32 *
          distanceScaleAt s ^ 5 := by
  intro s hs
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
  obtain ⟨baseSample, twistSample, balanceSample, hAll⟩ :=
    exists_distanceBalancedCode_at s hs
  have hDistances := hAll.1
  have hBlocklength := hAll.2.1
  have hDimension := hAll.2.2.1
  have hMainGood := hAll.2.2.2.1
  have hMainLTC := hAll.2.2.2.2.1
  have hInitial : InitialFamilyCertificate (2 * s)
      baseSample twistSample := by
    exact initialFamilyCertificate_of_good (2 * s) (by omega)
      baseSample twistSample hMainGood hMainLTC
  let X := finalComplex baseSample twistSample balanceSample
  let N := Fintype.card
    (FinalQubitIndex baseSample twistSample balanceSample)
  let K := Module.finrank (ZMod 2) X.middleHomology
  have hComplex : X = DistanceBalancing.chainComplex
      (balancedData baseSample twistSample balanceSample) := by
    change balancedLocalityComplex baseSample twistSample balanceSample = _
    exact balancedLocalityComplex_eq baseSample twistSample balanceSample
  have hHomology : MiddleHomologyDistanceAtLeast X
      (balancedHomologyDistanceAt s) := by
    rw [hComplex]
    exact hDistances.1
  have hCohomology : MiddleCohomologyDistanceAtLeast X
      (balancedCohomologyDistanceAt s) := by
    rw [hComplex]
    exact hDistances.2
  have hHomologyScale : MiddleHomologyDistanceAtLeast X
      (distanceScaleAt s) := by
    intro z hz hnontrivial
    exact (distanceScaleAt_le_homology s hs).trans
      (hHomology z hz hnontrivial)
  have hCohomologyScale : MiddleCohomologyDistanceAtLeast X
      (distanceScaleAt s) := by
    intro z hz hnontrivial
    exact (distanceScaleAt_le_cohomology s hs).trans
      (hCohomology z hz hnontrivial)
  have hLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile 8 := by
    exact balancedLocalityComplex_bounded_eight
      baseSample twistSample balanceSample
  have hK : dimensionScaleAt s ≤ K := by
    dsimp only [K]
    rw [hComplex]
    exact (dimensionScale_le_baseScale_product s hs).trans hDimension
  have hN : N ≤ blocklengthScaleAt s := by
    change Fintype.card
        (DistanceBalancing.QubitIndex
          (MainQubit baseSample twistSample)
          (MainCZero baseSample twistSample)
          (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
      blocklengthScaleAt s
    exact hBlocklength.trans (balancedBlocklengthUpperAt_le_scale s hs)
  have hKN : K ≤ N := by
    exact finrank_middleHomology_le_card X
  have hExponential : RandomPartition.hho20FiberLength s ^ 6 ≤ N := by
    apply (show RandomPartition.hho20FiberLength s ^ 6 ≤
        dimensionScaleAt s by rfl).trans
    exact hK.trans hKN
  have hKTradeoff := dimension_three_fifths s N K (by omega) hN hK
  have hDTradeoff := distance_three_fifths s N (distanceScaleAt s)
    hs hN (le_refl _)
  refine ⟨baseSample, twistSample, balanceSample, ?_⟩
  dsimp only
  exact ⟨hInitial, X.binaryCSSCode_stabilizer_isSourceValidBinary,
    hHomologyScale, hCohomologyScale, hLocality, hK, hN,
    hExponential, hKTradeoff, hDTradeoff⟩

end QEC.Coding.FiberBundle.HHO20DistanceBalancing
