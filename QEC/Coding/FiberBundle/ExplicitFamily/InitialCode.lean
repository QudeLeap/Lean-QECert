import QEC.Coding.FiberBundle.ExplicitFamily.Parameters
import QEC.Coding.FiberBundle.CohomologyRepresentatives
import QEC.Coding.FiberBundle.HomologyRepresentatives

/-!
# Initial HHO20 fiber-bundle code

This module turns the assumption-free random witnesses into an actual
fiber-bundle chain complex and records its exact block length and its two
unbalanced distance lower bounds.  These are the inputs to HHO20 weight
reduction and distance balancing.
-/

namespace QEC.Coding.FiberBundle

/-- Exact number of total-degree-one cells in the HHO20 bundle. -/
theorem card_hho20_qubitIndex
    (r ell : Nat) [NeZero ell] :
    Fintype.card
        (QubitIndex (Fin (3 * r)) (Fin (4 * r))
          (ZMod (ell * ell)) (ZMod (ell * ell))) =
      7 * r * (ell * ell) := by
  rw [card_qubitIndex]
  simp only [Fintype.card_fin, ZMod.card]
  ring

/-- The representative-level HHO20 homology estimate gives a universal
integer distance lower bound after division by its explicit coefficient. -/
theorem homologyDistanceAtLeast_explicit
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (hDelta : 1 ≤ Delta) :
    HomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample)
      ((ell * (4 * r)) / (5000 * Delta)) := by
  intro z hz hzNontrivial
  have hWeight :=
    homologyWeight_bound_of_twistGraphLTC
      baseSample twistSample hRank hDistance hLTC hDelta
      z hz hzNontrivial
  have hWeight' :
      ell * (4 * r) ≤
        (5000 * Delta) * HammingWeight z := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hWeight
  calc
    (ell * (4 * r)) / (5000 * Delta) ≤
        ((5000 * Delta) * HammingWeight z) /
          (5000 * Delta) :=
      Nat.div_le_div_right hWeight'
    _ = HammingWeight z := by
      exact Nat.mul_div_cancel_left
        (HammingWeight z) (by positivity)

namespace RandomPartition

/-- The concrete CSS code selected at every hierarchy index has its exact
block length and both pre-reduction distance lower bounds, in addition to all
random-base and twist-graph properties. -/
theorem exists_hho20_initial_code_at
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (hho20BaseScale s) :=
      ⟨by
        have := hho20_baseScale_ge_five_hundred s hs
        omega⟩
    letI : NeZero (hho20TypeCount s) :=
      ⟨hho20TypeCount_ne_zero s (by omega)⟩
    letI : NeZero (hho20FiberLength s) :=
      ⟨by
        have := hho20_fiberLength_ge s (by omega)
        omega⟩
    letI : NeZero (hho20FiberLength s - 1) :=
      ⟨by
        have := hho20_fiberLength_ge s (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample (hho20BaseScale s))
        (twistSample :
          RandomTwist.Sample (hho20BaseScale s)
            (hho20TypeCount s) (hho20FiberLength s)),
      RandomBase.IsFullyGood
          (Delta := hho20DegreeScale s) baseSample ∧
        TwistGraph.HasHHO20PartitionedChecks
          (hho20DegreeScale s) baseSample twistSample ∧
        TwistGraph.HasHHO20CayleySpectrum twistSample ∧
        TwistGraph.HasHHO20LocalTestability
          (hho20DegreeScale s) baseSample twistSample ∧
        Fintype.card
            (QubitIndex
              (Fin (3 * hho20BaseScale s))
              (Fin (4 * hho20BaseScale s))
              (ZMod (hho20FiberLength s * hho20FiberLength s))
              (ZMod (hho20FiberLength s * hho20FiberLength s))) =
          7 * hho20BaseScale s *
            (hho20FiberLength s * hho20FiberLength s) ∧
        CohomologyDistanceAtLeast
          (RandomTwist.fiberBundleData baseSample twistSample)
          (min
            (Fintype.card
              (ZMod (hho20FiberLength s * hho20FiberLength s)) / 2)
            ((6 * hho20BaseScale s) /
              (100000 * hho20DegreeScale s))) ∧
        HomologyDistanceAtLeast
          (RandomTwist.fiberBundleData baseSample twistSample)
          ((hho20FiberLength s * (4 * hho20BaseScale s)) /
            (5000 * hho20DegreeScale s)) ∧
        (binaryCSSCode
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).stabilizer.IsSourceValidBinary := by
  letI : NeZero (hho20BaseScale s) :=
    ⟨by
      have := hho20_baseScale_ge_five_hundred s hs
      omega⟩
  letI : NeZero (hho20TypeCount s) :=
    ⟨hho20TypeCount_ne_zero s (by omega)⟩
  letI : NeZero (hho20FiberLength s) :=
    ⟨by
      have := hho20_fiberLength_ge s (by omega)
      omega⟩
  letI : NeZero (hho20FiberLength s - 1) :=
    ⟨by
      have := hho20_fiberLength_ge s (by omega)
      omega⟩
  obtain ⟨baseSample, twistSample, hBase, hChecks, hSpectrum, hLTC⟩ :=
    exists_hho20_base_and_twist_at s hs
  rcases hBase with
    ⟨⟨hDegree, hRank, hDistance⟩, hExpansion⟩
  refine ⟨baseSample, twistSample,
    ⟨⟨hDegree, hRank, hDistance⟩, hExpansion⟩,
    hChecks, hSpectrum, hLTC, ?_, ?_, ?_, ?_⟩
  · exact card_hho20_qubitIndex
      (hho20BaseScale s) (hho20FiberLength s)
  · exact cohomologyDistanceAtLeast_explicit
      baseSample twistSample hRank
      (by
        simp only [hho20DegreeScale, hho20TypeCount]
        positivity)
      hDegree hExpansion
  · exact homologyDistanceAtLeast_explicit
      baseSample twistSample hRank hDistance hLTC
      (by
        exact Nat.one_le_iff_ne_zero.mpr (by
          simp only [hho20DegreeScale, hho20TypeCount]
          positivity))
  · exact binaryCSSCode_stabilizer_isSourceValidBinary
      (RandomTwist.fiberBundleData baseSample twistSample)

end RandomPartition
end QEC.Coding.FiberBundle
