import QEC.Distillation.LowOverheadProtocol.Parameterized.PathYield

/-!
# Parameterized HH18 finite-depth schedule accounting

This internal layer packages the finite objects consumed by the later HH18
asymptotic work.  Its reached error is the finite maximum of literal
path-indexed physical rates, while its distance-power target remains a
separate proved upper bound.  The schedule retains the actual routed slot
carriers and the pooled expected yield already derived from those paths.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

attribute [local instance 100] Fintype.ofFinite

/-- The actual routed physical-input carrier at one finite schedule depth. -/
abbrev routedDepthScheduleInputSlots (m w depth : Nat) :=
  routedDepthInputSlots m w depth

/-- The actual routed logical-output carrier at one finite schedule depth. -/
abbrev routedDepthScheduleOutputSlots (m w depth : Nat) :=
  routedDepthOutputSlots m w depth

/-- The reached schedule error is the finite maximum of the literal physical
rates indexing actual routed path runs. -/
noncomputable def routedDepthScheduleActualOutputError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : ℝ := by
  classical
  exact Finset.univ.sup'
    ⟨(routedDepthOutputSlots_nonempty m w depth).some, Finset.mem_univ _⟩
    fun path => (routedDepthPathRate h hdegree epsilon hsmall depth path).1

/-- Every literal path rate is included in the reached finite maximum. -/
theorem routedDepthPathRate_le_scheduleActualOutputError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ≤
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth := by
  classical
  unfold routedDepthScheduleActualOutputError
  exact Finset.le_sup' (fun other =>
    (routedDepthPathRate h hdegree epsilon hsmall depth other).1)
    (Finset.mem_univ path)

/-- The finite reached-error maximum is attained by one literal routed path. -/
theorem routedDepthScheduleActualOutputError_exists_path {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    ∃ path : routedDepthOutputSlots m w depth,
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth =
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 := by
  classical
  unfold routedDepthScheduleActualOutputError
  obtain ⟨path, _, hpath⟩ := Finset.exists_mem_eq_sup'
    ⟨(routedDepthOutputSlots_nonempty m w depth).some, Finset.mem_univ _⟩
    (fun path => (routedDepthPathRate h hdegree epsilon hsmall depth path).1)
  exact ⟨path, hpath⟩

/-- The finite reached-error maximum is nonnegative because it is attained by
a literal nonnegative physical path rate. -/
theorem routedDepthScheduleActualOutputError_nonneg {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 ≤ routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth := by
  obtain ⟨path, hpath⟩ :=
    routedDepthScheduleActualOutputError_exists_path h hdegree epsilon hsmall depth
  rw [hpath]
  exact (routedDepthPathRate h hdegree epsilon hsmall depth path).property.1

/-- The actual state-package rate at each path is included in the finite
reached-error maximum. -/
theorem routedDepthPathStatePackageRate_le_scheduleActualOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).rate.1 ≤
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth := by
  rw [← routedDepthPathRate_eq_statePackage_rate h hdegree epsilon hsmall depth path]
  exact routedDepthPathRate_le_scheduleActualOutputError
    h hdegree epsilon hsmall depth path

/-- The depth-zero reached error is the literal physical input rate of the
actual routed root state. -/
theorem routedDepthScheduleActualOutputError_zero_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    routedDepthScheduleActualOutputError h hdegree epsilon hsmall 0 = epsilon.1 := by
  apply le_antisymm
  · unfold routedDepthScheduleActualOutputError
    apply Finset.sup'_le
    intro path _
    simp only [routedDepthPathRate_root h hdegree epsilon hsmall path]
    exact le_rfl
  · calc
      epsilon.1 =
          (routedDepthPathRate h hdegree epsilon hsmall 0
            (routedDepthOutputPathEmpty m w)).1 := by
            simp only [routedDepthPathRate_root]
      _ ≤ routedDepthScheduleActualOutputError h hdegree epsilon hsmall 0 :=
        routedDepthPathRate_le_scheduleActualOutputError h hdegree epsilon hsmall 0
          (routedDepthOutputPathEmpty m w)

/-- The separate finite distance-power target at a schedule depth. -/
noncomputable def routedDepthScheduleTargetError (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) : ℝ :=
  (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth)

/-- The schedule target is the source-relevant distance power written using
the exact punctured Reed--Muller distance formula. -/
theorem routedDepthScheduleTargetError_eq_distancePower (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth =
      (routedDepthIterationScale w r m * epsilon.1) ^
        (binomialTail (r + 1) w ^ depth) := by
  unfold routedDepthScheduleTargetError
  rw [codeDistance_eq_binomialTail]

/-- The schedule target agrees with the scaled uniform envelope, which is
used only as an upper-bound proof and not as the reached-error definition. -/
theorem routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth =
      routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon depth := by
  unfold routedDepthScheduleTargetError
  exact (routedDepthErrorEnvelope_closed_form h epsilon depth).symm

/-- The uniform envelope is exactly the distance-power target divided by the
positive routing scale. -/
theorem routedDepthErrorEnvelope_eq_scheduleTargetError_div_scale {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon depth =
      routedDepthScheduleTargetError w r m epsilon depth /
        routedDepthIterationScale w r m := by
  rw [routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope h epsilon depth]
  field_simp [ne_of_gt (routedDepthIterationScale_pos w r m)]

/-- The uniform envelope is nonnegative at every finite depth. -/
theorem routedDepthScheduleErrorEnvelope_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    0 ≤ routedDepthErrorEnvelope w r m epsilon depth := by
  induction depth with
  | zero => exact epsilon.property.1
  | succ depth ih =>
      simp only [routedDepthErrorEnvelope]
      exact mul_nonneg
        (pow_nonneg (routedDepthIterationScale_pos w r m).le _) (pow_nonneg ih _)

/-- The scale lower bound turns the envelope into a bound by the separate
distance-power target. -/
theorem routedDepthErrorEnvelope_le_scheduleTargetError {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon depth ≤
      routedDepthScheduleTargetError w r m epsilon depth := by
  rw [routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope h epsilon depth]
  nlinarith [routedDepthIterationScale_one_le w r m,
    routedDepthScheduleErrorEnvelope_nonneg w r m epsilon depth]

/-- The finite maximum of actual routed physical rates is separately bounded
by the distance-power schedule target. -/
theorem routedDepthScheduleActualOutputError_le_targetError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth ≤
      routedDepthScheduleTargetError w r m epsilon depth := by
  classical
  calc
    routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth ≤
        routedDepthErrorEnvelope w r m epsilon depth := by
      unfold routedDepthScheduleActualOutputError
      apply Finset.sup'_le
      intro path _
      exact routedDepthPathRate_le_errorEnvelope h hdegree epsilon hsmall depth path
    _ ≤ routedDepthScheduleTargetError w r m epsilon depth :=
      routedDepthErrorEnvelope_le_scheduleTargetError h epsilon depth

/-- A positive initial physical rate makes every finite schedule target
strictly positive. -/
theorem routedDepthScheduleTargetError_pos (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (depth : Nat) :
    0 < routedDepthScheduleTargetError w r m epsilon depth := by
  unfold routedDepthScheduleTargetError
  exact pow_pos (mul_pos (routedDepthIterationScale_pos w r m) hepsilon) _

/-- The initial small-domain invariant makes every distance-power schedule
target strictly below one. -/
theorem routedDepthScheduleTargetError_lt_one {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth < 1 := by
  unfold routedDepthScheduleTargetError
  have hbaseNonneg : 0 ≤ routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hdistance : 1 ≤ codeDistance r w :=
    (codeDistance_two_le h).trans' (by omega)
  have hpower : 1 ≤ codeDistance r w ^ depth :=
    one_le_pow₀ hdistance
  calc
    (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth) ≤
        (1 / 4 : ℝ) ^ (codeDistance r w ^ depth) :=
      pow_le_pow_left₀ hbaseNonneg hsmall _
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpower
    _ < 1 := by norm_num

/-- The fixed-base distance-power target falls below every positive threshold
at some finite routed schedule depth. -/
theorem routedDepthScheduleTargetError_exists_lt {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (target : ℝ) (htarget : 0 < target) :
    ∃ depth : Nat, routedDepthScheduleTargetError w r m epsilon depth < target := by
  unfold routedDepthScheduleTargetError
  have hbaseNonneg : 0 ≤ routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hbaseLtOne : routedDepthIterationScale w r m * epsilon.1 < 1 :=
    hsmall.trans_lt (by norm_num)
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have nat_le_distance_pow : ∀ n : Nat, n ≤ codeDistance r w ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ codeDistance r w ^ n + 1 := Nat.add_le_add_right ih 1
          _ ≤ codeDistance r w ^ n + codeDistance r w ^ n :=
            Nat.add_le_add_left
              (Nat.one_le_pow n (codeDistance r w) (by omega)) _
          _ = codeDistance r w ^ n * 2 := by ring
          _ ≤ codeDistance r w ^ n * codeDistance r w :=
            Nat.mul_le_mul_left _ hdistance
          _ = codeDistance r w ^ (n + 1) := by rw [pow_succ]
  obtain ⟨n, hpower⟩ := exists_pow_lt_of_lt_one
    (x := target) (y := routedDepthIterationScale w r m * epsilon.1)
    htarget hbaseLtOne
  exact ⟨n, (pow_le_pow_of_le_one hbaseNonneg hbaseLtOne.le
    (nat_le_distance_pow n)).trans_lt hpower⟩

/-- The schedule's physical expected yield is the compiled pooled yield over
all actual routed output paths. -/
abbrev routedDepthScheduleExpectedYield {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : NNReal :=
  routedDepthPooledYield h hdegree epsilon hsmall depth

/-- The actual schedule expected yield has the uniform positive lower bound
already proved from literal finite path products. -/
theorem routedDepthScheduleExpectedYield_five_sixths_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (5 / 6 : ℝ) ≤ (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) :=
  routedDepthPooledYield_five_sixths_le h hdegree epsilon hsmall depth

/-- The actual schedule expected yield is strictly positive. -/
theorem routedDepthScheduleExpectedYield_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 < (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) :=
  routedDepthPooledYield_pos h hdegree epsilon hsmall depth

/-- The actual finite physical schedule carrier has exact `n^z` size. -/
theorem routedDepthScheduleInputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthScheduleInputSlots m w depth) =
      physicalInputCount m w ^ depth :=
  routedDepthPathTypedInputSlots_card m w depth

/-- The actual finite logical schedule carrier has exact `k^z` size. -/
theorem routedDepthScheduleOutputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthScheduleOutputSlots m w depth) =
      logicalOutputCount m w ^ depth :=
  routedDepthPathTypedOutputSlots_card m w depth

/-- The schedule input cardinality has the exact HH18 binomial-tail form. -/
theorem routedDepthScheduleInputSlots_card_eq_binomialTail (m w depth : Nat) :
    Fintype.card (routedDepthScheduleInputSlots m w depth) =
      binomialTail m w ^ depth := by
  rw [routedDepthScheduleInputSlots_card, physicalInputCount_eq_binomialTail]

/-- The schedule output cardinality has the exact HH18 cumulative-binomial
form. -/
theorem routedDepthScheduleOutputSlots_card_eq_binomialUpTo (m w depth : Nat) :
    Fintype.card (routedDepthScheduleOutputSlots m w depth) =
      binomialUpTo m w ^ depth := by
  rw [routedDepthScheduleOutputSlots_card, logicalOutputCount_eq_binomialUpTo]

/-- The successful-output accounting cost for the finite schedule. -/
abbrev routedDepthScheduleSuccessfulOutputCost {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) : ℝ :=
  routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth

/-- The schedule successful-output cost uses the pooled expected yield and
the actual finite routed input/output ratio. -/
theorem routedDepthScheduleSuccessfulOutputCost_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) :=
  routedDepthTypedSuccessfulOutputCost_eq h hdegree epsilon hsmall depth

/-- The actual finite schedule successful-output cost remains positive. -/
theorem routedDepthScheduleSuccessfulOutputCost_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 < routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth :=
  routedDepthTypedSuccessfulOutputCost_pos h hdegree epsilon hsmall depth

/-- The pooled expected-yield lower bound gives a uniform finite schedule
successful-output-cost factor. -/
theorem routedDepthScheduleSuccessfulOutputCost_le_six_fifths {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      (6 / 5 : ℝ) * ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
  routedDepthTypedSuccessfulOutputCost_le_six_fifths h hdegree epsilon hsmall depth

/-- The literal finite-slot input/output ratio and the HH18 distance determine
the schedule's logarithmic cost exponent. -/
noncomputable def routedDepthScheduleGamma (w r m : Nat) : ℝ :=
  Real.log ((physicalInputCount m w : ℝ) / logicalOutputCount m w) /
    Real.log (codeDistance r w)

/-- The positive logarithmic growth base of the fixed initial scaled input
error. -/
noncomputable def routedDepthScheduleLogGrowthBase (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  -Real.log (routedDepthIterationScale w r m * epsilon.1)

/-- The successful-output constant induced by the literal pooled-yield lower
bound and the fixed initial log-growth base. -/
noncomputable def routedDepthScheduleCostCoefficient {w r m : Nat}
    (_h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  (6 / 5 : ℝ) /
    Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
      (routedDepthScheduleGamma w r m)

/-- The real-power form of the schedule exponent exactly recovers the actual
finite routed input/output ratio at every depth. -/
theorem routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow
    {w r m : Nat} (h : Admissible w r m) (depth : Nat) :
    Real.rpow ((codeDistance r w : ℝ) ^ depth)
        (routedDepthScheduleGamma w r m) =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by
  have hdistance : (1 : ℝ) < codeDistance r w := by
    exact_mod_cast codeDistance_two_le h
  have hratio : 0 <
      (physicalInputCount m w : ℝ) / logicalOutputCount m w := by
    apply div_pos
    · exact_mod_cast routedDepthPhysicalInputCount_pos h
    · exact_mod_cast routedDepthLogicalOutputCount_pos m w
  calc
    Real.rpow ((codeDistance r w : ℝ) ^ depth)
        (routedDepthScheduleGamma w r m) =
        Real.exp (Real.log ((codeDistance r w : ℝ) ^ depth) *
          routedDepthScheduleGamma w r m) := by
          exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((depth : ℝ) *
        Real.log ((physicalInputCount m w : ℝ) / logicalOutputCount m w)) := by
          unfold routedDepthScheduleGamma
          congr 1
          rw [Real.log_pow]
          field_simp [ne_of_gt (Real.log_pos hdistance)]
    _ = Real.rpow ((physicalInputCount m w : ℝ) / logicalOutputCount m w)
        (depth : ℝ) := by
          symm
          calc
            Real.rpow ((physicalInputCount m w : ℝ) / logicalOutputCount m w)
                (depth : ℝ) =
                Real.exp (Real.log ((physicalInputCount m w : ℝ) /
                  logicalOutputCount m w) * (depth : ℝ)) :=
              Real.rpow_def_of_pos hratio _
            _ = Real.exp ((depth : ℝ) *
                Real.log ((physicalInputCount m w : ℝ) /
                  logicalOutputCount m w)) :=
              congrArg Real.exp (mul_comm _ _)
    _ = ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
      Real.rpow_natCast _ _

/-- Initial smallness supplies a positive logarithmic growth base. -/
theorem routedDepthScheduleLogGrowthBase_pos {w r m : Nat}
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    0 < routedDepthScheduleLogGrowthBase w r m epsilon := by
  unfold routedDepthScheduleLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (routedDepthIterationScale_pos w r m) hepsilon
  · exact hsmall.trans_lt (by norm_num)

/-- The derived successful-output coefficient is strictly positive. -/
theorem routedDepthScheduleCostCoefficient_pos {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    0 < routedDepthScheduleCostCoefficient h epsilon := by
  unfold routedDepthScheduleCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (routedDepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall) _)

/-- The exact distance-power target turns the depth exponent times the
initial log-growth base into the logarithm of its reciprocal. -/
theorem routedDepthSchedule_distancePow_mul_logGrowthBase_eq_log
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hepsilon : 0 < epsilon.1) (depth : Nat) :
    (codeDistance r w : ℝ) ^ depth *
        routedDepthScheduleLogGrowthBase w r m epsilon =
      Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth) := by
  have hbase : 0 < routedDepthIterationScale w r m * epsilon.1 :=
    mul_pos (routedDepthIterationScale_pos w r m) hepsilon
  unfold routedDepthScheduleTargetError
  rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hbase _)), Real.log_one,
    Real.log_pow]
  push_cast
  unfold routedDepthScheduleLogGrowthBase
  ring

/-- The literal pooled successful-output cost has the derived polylogarithmic
bound at every finite routed schedule depth. -/
theorem routedDepthScheduleSuccessfulOutputCost_le_polylog {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth))
          (routedDepthScheduleGamma w r m) := by
  have hbase : 0 < routedDepthScheduleLogGrowthBase w r m epsilon :=
    routedDepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall
  have hbaseRpow : 0 <
      Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
        (routedDepthScheduleGamma w r m) :=
    Real.rpow_pos_of_pos hbase _
  have hlog := routedDepthSchedule_distancePow_mul_logGrowthBase_eq_log
    (w := w) (r := r) (m := m) epsilon hepsilon depth
  have hfactorization :
      Real.rpow ((codeDistance r w : ℝ) ^ depth *
          routedDepthScheduleLogGrowthBase w r m epsilon)
          (routedDepthScheduleGamma w r m) =
        Real.rpow ((codeDistance r w : ℝ) ^ depth)
          (routedDepthScheduleGamma w r m) *
        Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
          (routedDepthScheduleGamma w r m) :=
    Real.mul_rpow (by positivity) hbase.le
  calc
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
        (6 / 5 : ℝ) *
          ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
      routedDepthScheduleSuccessfulOutputCost_le_six_fifths h hdegree epsilon
        hsmall depth
    _ = (6 / 5 : ℝ) *
        Real.rpow ((codeDistance r w : ℝ) ^ depth)
          (routedDepthScheduleGamma w r m) := by
      rw [routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow h depth]
    _ =
        ((6 / 5 : ℝ) *
          Real.rpow ((codeDistance r w : ℝ) ^ depth)
            (routedDepthScheduleGamma w r m) *
          Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
            (routedDepthScheduleGamma w r m)) /
          Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
            (routedDepthScheduleGamma w r m) := by
      field_simp [ne_of_gt hbaseRpow]
    _ = routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow ((codeDistance r w : ℝ) ^ depth *
          routedDepthScheduleLogGrowthBase w r m epsilon)
          (routedDepthScheduleGamma w r m) := by
      rw [hfactorization]
      unfold routedDepthScheduleCostCoefficient
      field_simp [ne_of_gt hbaseRpow]
    _ = routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth))
          (routedDepthScheduleGamma w r m) := by
      rw [hlog]

/-- The routed finite schedule satisfies the source-neutral finite-slot
polylogarithmic successful-output-cost predicate. -/
theorem routedDepthSchedule_typedPolylogCostBound {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    DependentBatch.typedPolylogCostBound
      (routedDepthScheduleInputSlots m w)
      (routedDepthScheduleOutputSlots m w)
      (routedDepthScheduleTargetError w r m epsilon)
      (routedDepthScheduleExpectedYield h hdegree epsilon hsmall)
      (routedDepthScheduleGamma w r m)
      (routedDepthScheduleCostCoefficient h epsilon) := by
  refine ⟨(routedDepthScheduleCostCoefficient_pos h epsilon hepsilon hsmall).le,
    ?_⟩
  intro depth _ _
  refine ⟨routedDepthScheduleExpectedYield_pos h hdegree epsilon hsmall depth,
    ?_⟩
  exact routedDepthScheduleSuccessfulOutputCost_le_polylog h hdegree epsilon
    hepsilon hsmall depth

/-- The actual routed finite schedule instantiates the physical expected-yield
overhead interface from separately proved physical, target, yield, and cost
facts. -/
theorem routedDepthSchedule_physicalPolylogarithmicExpectedYieldOverhead
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (routedDepthScheduleInputSlots m w)
      (routedDepthScheduleOutputSlots m w)
      (routedDepthScheduleTargetError w r m epsilon)
      (routedDepthScheduleActualOutputError h hdegree epsilon hsmall)
      (routedDepthScheduleExpectedYield h hdegree epsilon hsmall)
      (routedDepthScheduleGamma w r m)
      (routedDepthScheduleCostCoefficient h epsilon) := by
  rcases routedDepthSchedule_typedPolylogCostBound h hdegree epsilon hepsilon
    hsmall with ⟨hcoefficient, hcost⟩
  refine ⟨hcoefficient, ?_⟩
  intro depth htargetPos htargetLtOne
  obtain ⟨hyield, hcostBound⟩ := hcost depth htargetPos htargetLtOne
  exact ⟨routedDepthScheduleActualOutputError_le_targetError h hdegree epsilon
    hsmall depth, hyield, hcostBound⟩

end HH18Parameterized
end Distillation
end QEC
