import QEC.Coding.FiberBundle.ExplicitFamily.InitialCode
import QEC.Coding.FiberBundle.WeightReductionParameters

/-!
# Locality of the initial HHO20 fiber-bundle code

The random Tanner graph's degree windows control both boundary-row weights
and qubit participation in the unreduced fiber-bundle code.  This statement
is independent of the particular cofinal parameter hierarchy used later.
-/

namespace QEC.Coding.FiberBundle

open QEC.Coding

namespace RandomBase

theorem canonicalBasisWord_eq_single
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (i : I) :
    canonicalBasisWord (F := F) i = Pi.single i 1 := by
  classical
  ext j
  by_cases h : i = j
  · subst j
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, h]

theorem HammingWeight_randomFiberBundle_base_row_eq_checkDegree
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (a : Fin (3 * r)) :
    HammingWeight
        (fun b => (RandomTwist.fiberBundleData
          baseSample twistSample).baseBoundary a b) =
      checkDegree baseSample a := by
  classical
  simp [HammingWeight, hammingSupport, RandomTwist.fiberBundleData,
    multipleRotationCycleData, cycleData, boundary, checkDegree]

theorem HammingWeight_randomFiberBundle_base_col_eq_variableDegree
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) :
    HammingWeight
        (fun a => (RandomTwist.fiberBundleData
          baseSample twistSample).baseBoundary a b) =
      variableDegree baseSample b := by
  classical
  simp [HammingWeight, hammingSupport, RandomTwist.fiberBundleData,
    multipleRotationCycleData, cycleData, boundary, variableDegree]

/-- The initial HHO20 fiber-bundle code has locality at most the common
Tanner degree-window bound plus the two incident cycle edges. -/
theorem initialFiberBundle_boundedLocality
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDegree : HasDegreeWindows (Delta := Delta) baseSample) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex
          (RandomTwist.fiberBundleData
            baseSample twistSample))).localityProfile
      (101 * Delta + 2) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let X := chainComplex D
  have hLocal : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile
      (max (101 * Delta + 2) (101 * Delta + 2)) := by
    apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
        X (w := 101 * Delta + 2) (variableDegree := 101 * Delta + 2)
    · intro a
      rcases a with ⟨a, i⟩
      change HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (canonicalBasisWord (F := ZMod 2) (a, i))) ≤ 101 * Delta + 2
      rw [canonicalBasisWord_eq_single]
      apply HammingWeight_transpose_boundary1_single_le
        D (B := 101 * Delta) (F := 2) a i
      · rw [HammingWeight_randomFiberBundle_base_row_eq_checkDegree]
        have h := (hDegree.1 a).2
        omega
      · exact HammingWeight_cycleBoundary_row_le_two (ell * ell) i
    · intro b
      rcases b with ⟨b, j⟩
      change HammingWeight
        (boundary2 D (canonicalBasisWord (F := ZMod 2) (b, j))) ≤
          101 * Delta + 2
      rw [canonicalBasisWord_eq_single]
      have hBound := HammingWeight_boundary2_single_le
        D (B := 101 * Delta) (F := 2) b j
        (by
          rw [HammingWeight_randomFiberBundle_base_col_eq_variableDegree]
          have h := (hDegree.2 b).2
          omega)
        (HammingWeight_cycleBoundary_col_le_two (ell * ell) j)
      omega
    · intro q
      rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns]
      change HammingWeight
          (boundary1 D (canonicalBasisWord (F := ZMod 2) q)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (canonicalBasisWord (F := ZMod 2) q)) ≤ 101 * Delta + 2
      rw [canonicalBasisWord_eq_single]
      cases q with
      | inl q =>
          rcases q with ⟨b, i⟩
          rw [HammingWeight_boundary1_single_inl_eq]
          rw [HammingWeight_transpose_boundary2_single_inl_eq]
          rw [HammingWeight_randomFiberBundle_base_col_eq_variableDegree]
          have h := (hDegree.2 b).2
          have hf : HammingWeight (fun j => D.fiberBoundary i j) ≤ 2 := by
            simpa [D, RandomTwist.fiberBundleData, multipleRotationCycleData,
              cycleData] using
              (HammingWeight_cycleBoundary_row_le_two (ell * ell) i)
          omega
      | inr q =>
          rcases q with ⟨a, j⟩
          rw [HammingWeight_boundary1_single_inr_eq]
          rw [HammingWeight_transpose_boundary2_single_inr_eq]
          rw [HammingWeight_randomFiberBundle_base_row_eq_checkDegree]
          have h := (hDegree.1 a).2
          have hf : HammingWeight (fun i => D.fiberBoundary i j) ≤ 2 := by
            simpa [D, RandomTwist.fiberBundleData, multipleRotationCycleData,
              cycleData] using
              (HammingWeight_cycleBoundary_col_le_two (ell * ell) j)
          omega
  simpa only [max_self, X, D] using hLocal

end RandomBase
end QEC.Coding.FiberBundle
