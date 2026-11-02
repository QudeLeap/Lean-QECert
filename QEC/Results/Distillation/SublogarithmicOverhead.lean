import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.SelectedCode
import QEC.Distillation.LowOverheadProtocol.Sublogarithmic.TargetSchedule
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Asymptotic

/-!
# HH18 sublogarithmic distillation

The terminal HH18 theorem chooses its finite punctured Reed--Muller code from
the proved entropy selector, builds the source-oriented small diagonal input
rate for that code, and then uses the parameterized exact-batch construction
at every depth.  In particular, the cost conclusion is the existing
successful-output cost of the actual pointwise protocol family.
-/

noncomputable section

namespace QEC.Distillation.HH18

open Coding
open Coding.PuncturedReedMuller
open Filter Topology
open Semantics
open Semantics.FiniteInstrument
open QEC.Distillation.HH18PuncturedReedMuller
open HH18SublogarithmicEntropy
open HH18Parameterized

private theorem selected_physical_counts
    (A D j : Nat) :
    physicalInputCount (parameterM D j) (parameterW A j) =
        parameterLength A D j ∧
      logicalOutputCount (parameterM D j) (parameterW A j) =
        parameterDimension A D j ∧
      codeDistance (parameterR D j) (parameterW A j) =
        parameterDistance A D j := by
  constructor
  · rw [physicalInputCount_eq_binomialTail]
    rfl
  constructor
  · rw [logicalOutputCount_eq_binomialUpTo]
    rfl
  · rfl

private theorem selected_pooling_rate_exists
    {w r m : Nat} (_h : Admissible w r m) :
    ∃ epsilon : HH18NoisyInput.DiagonalErrorRate,
      0 < epsilon.1 ∧ decodedRetryPoolInitialPoolingDomain w r m epsilon := by
  let scale := routedDepthIterationScale w r m
  let outputs := (logicalOutputCount m w : ℝ)
  let rate : ℝ := 1 / (128 * scale * outputs)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact routedDepthIterationScale_pos w r m
  have houtputs : 0 < outputs := by
    dsimp [outputs]
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hrate : 0 < rate := by
    dsimp [rate]
    exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) hscale) houtputs)
  have hrate_le_half : rate ≤ 1 / 2 := by
    have hden : (2 : ℝ) ≤ 128 * scale * outputs := by
      have hscale_one : (1 : ℝ) ≤ scale := by
        dsimp [scale]
        exact routedDepthIterationScale_one_le w r m
      have houtputs_one : (1 : ℝ) ≤ outputs := by
        change (1 : ℝ) ≤ (logicalOutputCount m w : ℝ)
        exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
      nlinarith
    exact (one_div_le_one_div_of_le (by norm_num) hden).trans_eq (by norm_num)
  let epsilon : HH18NoisyInput.DiagonalErrorRate := ⟨rate, hrate.le, hrate_le_half⟩
  refine ⟨epsilon, hrate, ?_⟩
  change scale * rate ≤ 1 / (64 * outputs)
  have hproduct : scale * rate = 1 / (128 * outputs) := by
    dsimp [rate]
    field_simp [hscale.ne', houtputs.ne']
  rw [hproduct]
  apply one_div_le_one_div_of_le
  · exact mul_pos (by norm_num) houtputs
  · nlinarith

private theorem selected_target_tendsto_zero
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (_hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    Tendsto (fun depth : Nat =>
      routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0) := by
  let base : ℝ := routedDepthIterationScale w r m * epsilon.1
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    exact mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hbase1 : base < 1 := by
    dsimp [base]
    exact (decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
      epsilon hpool).trans_lt (by norm_num)
  have hpow : Tendsto (fun t : Nat => base ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have hdistance : 1 < codeDistance r w := by
    exact_mod_cast codeDistance_two_le h
  have hgrowth : Tendsto (fun depth : Nat => codeDistance r w ^ (depth + 1))
      atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt hdistance).comp
      (tendsto_add_atTop_nat 1)
  have hport := hpow.comp hgrowth
  simp only [routedDepthScheduleTargetError, base] at hport ⊢
  exact hport

private theorem selected_actual_output_tendsto_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (rhoUnit : DensityOperator
      (QEC.Semantics.FiniteInstrument.tensorPowerCarrier (PhysicalRegister m w) 0))
    (htarget : Tendsto (fun depth : Nat =>
      routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0)) :
    Tendsto (fun depth : Nat =>
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds htarget
    (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError_nonneg
      h hdegree epsilon depth rhoUnit)
    (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
      h hdegree epsilon hpool depth rhoUnit)

/-- The source-exact HH18 family has an exponent arbitrarily close to its
interval infimum and below one, while its actual finite-depth protocols have
polylogarithmic successful-output cost and vanishing output error. -/
theorem hh18_sublogarithmic_distillation_overhead (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
      0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
      let r := parameterR D j
      let w := parameterW A j
      let m := parameterM D j
      let n := parameterLength A D j
      let k := parameterDimension A D j
      let d := parameterDistance A D j
      ∃ h : Admissible w r m,
        m = 3 * r + 1 ∧ 0 ≤ 2 * w ∧ 2 * w < 2 * r ∧ 2 * r < m ∧
        (w : ℚ) = 3 * (r : ℚ) * q ∧
        Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w) = n ∧
        Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w) - Dimension (xCode w r m) -
            Dimension (zCode w r m) = k ∧
        Module.finrank Complex (cssCode h).stabilizer.code.carrier = 2 ^ k ∧
        StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h) d ∧
        (encodedCode h).ImplementsLogicalGate (physicalT w m) (logicalTInv w m) ∧
        (encodedCode h).ImplementsLogicalGate (physicalTInv w m) (logicalT w m) ∧
        hh18GammaInf ≤ hh18Gamma p0R ∧ hh18Gamma p0R < (339 / 500 : ℝ) ∧
        (339 / 500 : ℝ) < 1 ∧
        ∃ epsilon : HH18NoisyInput.DiagonalErrorRate,
          0 < epsilon.1 ∧
          ∃ hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon,
          ∃ gamma : ℝ,
            gamma = routedDepthScheduleGamma w r m ∧
            gamma = Real.log ((n : ℝ) / k) / Real.log d ∧
            |gamma - hh18GammaInf| < eta ∧ gamma < 1 ∧
          ∃ coefficient : ℝ,
            coefficient = decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon ∧
            0 < coefficient ∧ 0 ≤ coefficient ∧
            (∀ depth : Nat,
              PolylogarithmicOverhead
                (decodedRetryPoolPhysicalExactBatchProtocolFamily h
                  (selected_transversal_t_degree A D j) epsilon
                  hpool depth
                  decodedRetryPoolTensorUnitDensity)
                gamma coefficient ∧
              decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost h
                (selected_transversal_t_degree A D j) epsilon depth
                decodedRetryPoolTensorUnitDensity =
                DistillationProtocolFamily.successfulOutputCost
                  (decodedRetryPoolPhysicalExactBatchProtocolFamily h
                  (selected_transversal_t_degree A D j) epsilon
                  hpool depth
                  decodedRetryPoolTensorUnitDensity) PUnit.unit) ∧
            Tendsto (fun depth : Nat =>
              routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0) ∧
            Tendsto (fun depth : Nat =>
              decodedRetryPoolPhysicalExactBatchActualOutputError h
                (selected_transversal_t_degree A D j) epsilon depth
                decodedRetryPoolTensorUnitDensity) atTop (𝓝 0) := by
  rcases exists_finite_subunit_gamma_selector eta heta with
    ⟨q, A, D, j, hqL, hqU, hA, hD, hwindow, hj, hq, hselected⟩
  dsimp at hselected
  rcases hselected with ⟨h, hslope, hgamma, hclose, _, hsubunit⟩
  rcases parameter_sequence_admissible A D j hA hD hwindow hj with
    ⟨hm, hslopeSequence, hadmissible⟩
  have hslope' : (parameterW A j : ℚ) =
      3 * (parameterR D j : ℚ) * q := by
    rw [hslopeSequence, hq]
  have hcounts := selected_physical_counts A D j
  rcases hcounts with ⟨hn, hk, hd⟩
  have hgammaSchedule :
      routedDepthScheduleGamma (parameterW A j) (parameterR D j) (parameterM D j) =
        Real.log ((parameterLength A D j : ℝ) / parameterDimension A D j) /
          Real.log (parameterDistance A D j) := by
    unfold routedDepthScheduleGamma
    rw [hn, hk, hd]
  have hp0lower : hh18GammaInf ≤ hh18Gamma p0R := by
    rw [hh18GammaInf]
    exact csInf_le hh18GammaSet_bddBelow ⟨p0R, p0_mem_parameterInterval, rfl⟩
  rcases selected_pooling_rate_exists h with ⟨epsilon, hepsilon, hpool⟩
  let rhoUnit : DensityOperator
      (QEC.Semantics.FiniteInstrument.tensorPowerCarrier
        (PhysicalRegister (parameterM D j) (parameterW A j)) 0) :=
    decodedRetryPoolTensorUnitDensity
  let coefficient := decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    exact (decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
      h epsilon hepsilon hpool).le
  have htarget := selected_target_tendsto_zero h epsilon hepsilon hpool
  have hactual := selected_actual_output_tendsto_zero
    h (selected_transversal_t_degree A D j) epsilon hpool rhoUnit htarget
  refine ⟨q, A, D, j, hqL, hqU, hA, hD, hwindow, hj, hq, ?_⟩
  dsimp
  refine ⟨h, hm, h.1, h.2.1, h.2.2, hslope', ?_, ?_, ?_, ?_, ?_, ?_,
    hp0lower, hh18Gamma_p0_lt_339_div_500, by norm_num, epsilon, hepsilon,
    hpool, routedDepthScheduleGamma (parameterW A j) (parameterR D j) (parameterM D j),
    rfl, hgammaSchedule, ?_, ?_, coefficient, rfl, ?_, hcoefficient, ?_, htarget,
    hactual⟩
  · exact (cssParameters h).1
  · exact (cssParameters h).2.1
  · exact (cssParameters h).2.2.1
  · exact (cssParameters h).2.2.2
  · exact HH18PuncturedReedMuller.physicalT_implements_logicalTInv
      h (selected_transversal_t_degree A D j)
  · exact HH18PuncturedReedMuller.physicalTInv_implements_logicalT
      h (selected_transversal_t_degree A D j)
  · rw [hgammaSchedule, ← hgamma]
    exact hclose
  · rw [hgammaSchedule, ← hgamma]
    exact hsubunit
  · dsimp [coefficient]
    exact decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
      h epsilon hepsilon hpool
  · intro depth
    constructor
    · dsimp [coefficient, rhoUnit]
      exact decodedRetryPoolPhysicalExactBatchProtocolFamily_polylogarithmicOverhead
        h (selected_transversal_t_degree A D j) epsilon hepsilon hpool depth
          decodedRetryPoolTensorUnitDensity
    · exact decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
        h (selected_transversal_t_degree A D j) epsilon hpool depth
          decodedRetryPoolTensorUnitDensity

end QEC.Distillation.HH18
