import Mathlib.Data.Nat.Choose.Bounds
import QEC.Distillation.Universality.AdaptiveIdealClifford
import QEC.Distillation.Triorthogonal.Concatenation
import QEC.Distillation.ConstantOverheadProtocol.OneRound

/-!
# WHY24 constant-overhead distillation

This terminal module derives a concrete positive threshold and uniform direct
resource ratio from the actual F1024 family and correlated one-round protocol.
It also gives a closed finite resource program for the source-certified T/CCZ
conversion rates and connects the returned catalyst to an actual BH12 seed.
-/

noncomputable section

namespace QEC.Distillation.Why24ConstantOverhead

open Filter Topology
open Semantics
open Why24AGFamily Why24OneRoundProtocol
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open Triorthogonal.BH12Concatenation
open Triorthogonal.BH12EvenFamily
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12Protocol

/-! ## Exact finite family constants -/

private theorem why24OddGenus_subtrahend_le (index : Nat) :
    34 * 32 ^ (index + 1) <= 33 * 32 ^ (2 * index + 2) := by
  let q := 32 ^ (index + 1)
  have hpower : 32 <= q := by
    dsimp only [q]
    have h := pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 32)
      (by omega : 1 <= index + 1)
    norm_num at h ⊢
    exact h
  have hbig : 32 ^ (2 * index + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * index + 2 = (index + 1) + (index + 1) by omega, pow_add]
  change 34 * q <= 33 * 32 ^ (2 * index + 2)
  rw [hbig]
  have hmul : q * 32 <= q * q := Nat.mul_le_mul_left q hpower
  nlinarith

private theorem why24OddGenus_cast (index : Nat) :
    (oddGenus index : Int) =
      33 * (32 : Int) ^ (2 * index + 2) -
        34 * (32 : Int) ^ (index + 1) + 1 := by
  rw [oddGenus, Nat.cast_add,
    Nat.cast_sub (why24OddGenus_subtrahend_le index)]
  norm_num

private theorem why24OddGenus_lower_bound (index : Nat) :
    32705 <= oddGenus index := by
  let q : Int := (32 : Int) ^ (index + 1)
  have hqNat : 32 <= 32 ^ (index + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 32)
      (by omega : 1 <= index + 1)
    norm_num at h ⊢
    exact h
  have hq : (32 : Int) <= q := by
    dsimp only [q]
    exact_mod_cast hqNat
  have hpower : (32 : Int) ^ (2 * index + 2) = q * q := by
    dsimp only [q]
    rw [show 2 * index + 2 = (index + 1) + (index + 1) by omega, pow_add]
  have hcast := why24OddGenus_cast index
  have hbound : (32705 : Int) <= (oddGenus index : Int) := by
    rw [hcast, hpower]
    nlinarith
  exact_mod_cast hbound

private theorem why24OddLength_le_twentyFour_mul_dimension (index : Nat) :
    f1024Why24OddLength index <= 24 * f1024Why24OddDimension index := by
  have hlarge := why24OddGenus_lower_bound index
  have hupper := (f1024Why24OddLength_bounds index).2
  simp only [f1024Why24OddDimension, selectedLogicalCount,
    selectedPhysicalLengthUpperBound] at hupper ⊢
  omega

private theorem why24OddLength_le_twoForty_mul_radius (index : Nat) :
    f1024Why24OddLength index <= 240 * f1024Why24OddDecodingRadius index := by
  have hlarge := why24OddGenus_lower_bound index
  have hupper := (f1024Why24OddLength_bounds index).2
  simp only [f1024Why24OddDecodingRadius, selectedDecodingRadius,
    selectedPhysicalLengthUpperBound] at hupper ⊢
  omega

private theorem why24OddDimension_pos (index : Nat) :
    0 < f1024Why24OddDimension index := by
  have hlarge := why24OddGenus_lower_bound index
  simp only [f1024Why24OddDimension, selectedLogicalCount]
  omega

private theorem why24OddDecodingRadius_tendsto_atTop :
    Tendsto f1024Why24OddDecodingRadius atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := Real)).mp
  have hlengthCast : Tendsto
      (fun index : Nat => (f1024Why24OddLength index : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp f1024Why24OddLength_tendsto_atTop
  have hlengthNorm : Tendsto
      (norm ∘ fun index : Nat => (f1024Why24OddLength index : Real))
      atTop atTop := by
    simpa [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg] using hlengthCast
  have hradiusNorm :=
    f1024Why24OddDecodingRadius_isTheta_length.tendsto_norm_atTop_iff.mpr
      hlengthNorm
  simpa [Function.comp_def, Real.norm_eq_abs,
    abs_of_nonneg] using hradiusNorm

/-! ## Positive threshold and geometric suppression -/

private def why24ThresholdRate : Real :=
  1 / (140 * 2 ^ 240)

private def why24OverheadConstant : Real := 1680

/-- The explicit geometric envelope used after the finite binomial bound. -/
def why24GeometricErrorEnvelope (index : Nat) : Real :=
  (1 / 2 : Real) ^ (f1024Why24OddDecodingRadius index + 1)

theorem why24GeometricErrorEnvelope_tendsto_zero :
    Tendsto why24GeometricErrorEnvelope atTop (nhds 0) := by
  have hpow : Tendsto (fun exponent : Nat => (1 / 2 : Real) ^ exponent)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hexponent : Tendsto
      (fun index : Nat => f1024Why24OddDecodingRadius index + 1)
      atTop atTop :=
    (tendsto_add_atTop_nat 1).comp why24OddDecodingRadius_tendsto_atTop
  exact hpow.comp hexponent

private theorem why24FiniteBinomialBound_le_geometric (index : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount index))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount index)))
    (hthreshold : preparation.rate < why24ThresholdRate) :
    (Nat.choose (f1024Why24OddLength index)
        (f1024Why24OddDecodingRadius index + 1) : Real) *
        (70 * preparation.rate) ^
          (f1024Why24OddDecodingRadius index + 1) <=
      why24GeometricErrorEnvelope index := by
  let n := f1024Why24OddLength index
  let t := f1024Why24OddDecodingRadius index
  have hn : n <= 240 * (t + 1) := by
    dsimp only [n, t]
    have h := why24OddLength_le_twoForty_mul_radius index
    omega
  have hchoose : (Nat.choose n (t + 1) : Real) <= (2 : Real) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n (t + 1)
  have htwoPow : (2 : Real) ^ n <= (2 : Real) ^ (240 * (t + 1)) :=
    pow_le_pow_right₀ (by norm_num) hn
  have hrateNonneg : 0 <= 70 * preparation.rate :=
    mul_nonneg (by norm_num) preparation.rate_nonneg
  have hbaseNonneg : 0 <= (2 : Real) ^ 240 * (70 * preparation.rate) :=
    mul_nonneg (pow_nonneg (by norm_num) _) hrateNonneg
  have hbaseLt : (2 : Real) ^ 240 * (70 * preparation.rate) < 1 / 2 := by
    calc
      (2 : Real) ^ 240 * (70 * preparation.rate) =
          ((2 : Real) ^ 240 * 70) * preparation.rate := by ring
      _ < ((2 : Real) ^ 240 * 70) * why24ThresholdRate :=
        mul_lt_mul_of_pos_left hthreshold (by positivity)
      _ = 1 / 2 := by norm_num [why24ThresholdRate]
  change (Nat.choose n (t + 1) : Real) * (70 * preparation.rate) ^ (t + 1) <= _
  calc
    (Nat.choose n (t + 1) : Real) * (70 * preparation.rate) ^ (t + 1) <=
        (2 : Real) ^ n * (70 * preparation.rate) ^ (t + 1) :=
      mul_le_mul_of_nonneg_right hchoose (pow_nonneg hrateNonneg _)
    _ <= (2 : Real) ^ (240 * (t + 1)) *
        (70 * preparation.rate) ^ (t + 1) :=
      mul_le_mul_of_nonneg_right htwoPow (pow_nonneg hrateNonneg _)
    _ = ((2 : Real) ^ 240 * (70 * preparation.rate)) ^ (t + 1) := by
      rw [pow_mul, mul_pow, mul_pow]
      ring
    _ <= (1 / 2 : Real) ^ (t + 1) :=
      pow_le_pow_left₀ hbaseNonneg hbaseLt.le _
    _ = why24GeometricErrorEnvelope index := rfl

/-- Every actual correlated one-round output below the explicit threshold is
bounded by the geometric envelope. -/
theorem why24OneRoundOutputError_le_geometric (index : Nat)
    (preparation : Why24LocalStochasticPreparation
      (Fin (why24OneRoundInputCount index))
      (why24IdealCCZRegisterDensity (why24OneRoundInputCount index)))
    (hthreshold : preparation.rate < why24ThresholdRate) :
    why24OneRoundOutputError index preparation <=
      why24GeometricErrorEnvelope index :=
  (why24OneRoundOutputError_le index preparation).trans
    (why24FiniteBinomialBound_le_geometric index preparation hthreshold)

/-- The actual one-round `70 n / k` resource ratio is uniformly at most
`1680`. -/
theorem why24InputOutputRatio_le_overhead (index : Nat) :
    (why24OneRoundInputCount index : Real) /
        why24OneRoundOutputCount index <= why24OverheadConstant := by
  have hcount : why24OneRoundInputCount index <=
      1680 * why24OneRoundOutputCount index := by
    rw [why24OneRoundInputCount_eq, why24OneRoundOutputCount_eq]
    calc
      70 * f1024Why24OddLength index <=
          70 * (24 * f1024Why24OddDimension index) :=
        Nat.mul_le_mul_left 70
          (why24OddLength_le_twentyFour_mul_dimension index)
      _ = 1680 * f1024Why24OddDimension index := by ring
  apply (div_le_iff₀ (by
    exact_mod_cast why24OddDimension_pos index)).2
  rw [why24OverheadConstant]
  exact_mod_cast hcount

/-! ## Closed finite T/CCZ resource program -/

/-- The two resource species in WHY24's finite-rate conversion remark. -/
inductive Why24MagicResourceToken
  | t
  | ccz
  deriving DecidableEq, Repr

/-- A computed finite inventory; no claimed conversion result is stored. -/
structure Why24MagicInventory where
  tCount : Nat
  cczCount : Nat
  deriving DecidableEq, Repr

/-- The two source-certified finite stabilizer conversion primitives. -/
inductive Why24FiniteConversionPrimitive
  | fourTToCCZ
  | cczCatalyticT
  deriving DecidableEq, Repr

namespace Why24FiniteConversionPrimitive

/-- Literal resource debits of one primitive. -/
def inputLedger : Why24FiniteConversionPrimitive ->
    AdaptiveIdealClifford.ResourceLedger Why24MagicResourceToken
  | .fourTToCCZ => Multiset.replicate 4 .t
  | .cczCatalyticT => {.ccz, .t}

/-- Literal resource outputs of one primitive. -/
def outputLedger : Why24FiniteConversionPrimitive ->
    AdaptiveIdealClifford.ResourceLedger Why24MagicResourceToken
  | .fourTToCCZ => {.ccz}
  | .cczCatalyticT => Multiset.replicate 3 .t

/-- Apply one primitive only when its literal resources are available. -/
def apply : Why24FiniteConversionPrimitive -> Why24MagicInventory ->
    Option Why24MagicInventory
  | .fourTToCCZ, inventory =>
      if 4 <= inventory.tCount then
        some
          { tCount := inventory.tCount - 4
            cczCount := inventory.cczCount + 1 }
      else none
  | .cczCatalyticT, inventory =>
      if 1 <= inventory.tCount && 1 <= inventory.cczCount then
        some
          { tCount := inventory.tCount + 2
            cczCount := inventory.cczCount - 1 }
      else none

end Why24FiniteConversionPrimitive

/-- Evaluate a closed finite conversion program against its live inventory. -/
def why24RunConversionProgram : List Why24FiniteConversionPrimitive ->
    Why24MagicInventory -> Option Why24MagicInventory
  | [], inventory => some inventory
  | primitive :: program, inventory =>
      (primitive.apply inventory).bind (why24RunConversionProgram program)

/-- `batch` copies of the finite `4 T -> CCZ` primitive. -/
def why24FourTToCCZBatch (batch : Nat) :
    List Why24FiniteConversionPrimitive :=
  List.replicate batch .fourTToCCZ

/-- `batch` sequential catalytic `CCZ + T -> 3 T` primitives. -/
def why24CCZCatalyticTBatch (batch : Nat) :
    List Why24FiniteConversionPrimitive :=
  List.replicate batch .cczCatalyticT

private theorem why24FourTToCCZBatch_run_additionalCCZ
    (batch additionalCCZ : Nat) :
    why24RunConversionProgram (why24FourTToCCZBatch batch)
        { tCount := 4 * batch
          cczCount := additionalCCZ } =
      some
        { tCount := 0
          cczCount := additionalCCZ + batch } := by
  induction batch generalizing additionalCCZ with
  | zero => simp [why24FourTToCCZBatch, why24RunConversionProgram]
  | succ batch ih =>
      rw [show why24FourTToCCZBatch (Nat.succ batch) =
          .fourTToCCZ :: why24FourTToCCZBatch batch by
        simp [why24FourTToCCZBatch, List.replicate_succ]]
      rw [why24RunConversionProgram]
      have happly : Why24FiniteConversionPrimitive.apply .fourTToCCZ
          { tCount := 4 * Nat.succ batch
            cczCount := additionalCCZ } =
          some
            { tCount := 4 * batch
              cczCount := additionalCCZ + 1 } := by
        simp [Why24FiniteConversionPrimitive.apply, Nat.mul_succ]
      rw [happly, Option.bind_some, ih]
      congr 2
      omega

/-- A batch of `4B` T resources computes exactly `B` CCZ resources. -/
theorem why24FourTToCCZBatch_run (batch : Nat) :
    why24RunConversionProgram (why24FourTToCCZBatch batch)
        { tCount := 4 * batch
          cczCount := 0 } =
      some
        { tCount := 0
          cczCount := batch } := by
  simpa using why24FourTToCCZBatch_run_additionalCCZ batch 0

private theorem why24CCZCatalyticTBatch_run_from_seed
    (batch seed : Nat) (hseed : 0 < seed) :
    why24RunConversionProgram (why24CCZCatalyticTBatch batch)
        { tCount := seed
          cczCount := batch } =
      some
        { tCount := seed + 2 * batch
          cczCount := 0 } := by
  induction batch generalizing seed with
  | zero => simp [why24CCZCatalyticTBatch, why24RunConversionProgram]
  | succ batch ih =>
      rw [show why24CCZCatalyticTBatch (Nat.succ batch) =
          .cczCatalyticT :: why24CCZCatalyticTBatch batch by
        simp [why24CCZCatalyticTBatch, List.replicate_succ]]
      rw [why24RunConversionProgram]
      have happly : Why24FiniteConversionPrimitive.apply .cczCatalyticT
          { tCount := seed
            cczCount := Nat.succ batch } =
          some
            { tCount := seed + 2
              cczCount := batch } := by
        have hseedNe : seed ≠ 0 := Nat.ne_of_gt hseed
        simp [Why24FiniteConversionPrimitive.apply, hseedNe]
      rw [happly, Option.bind_some, ih (seed + 2) (by omega)]
      congr 2
      omega

/-- A single seed is returned: `B` CCZ resources produce `2B` fresh T
resources plus that one catalyst. -/
theorem why24CCZCatalyticTBatch_run (batch : Nat) :
    why24RunConversionProgram (why24CCZCatalyticTBatch batch)
        { tCount := 1
          cczCount := batch } =
      some
        { tCount := 2 * batch + 1
          cczCount := 0 } := by
  simpa [add_comm] using why24CCZCatalyticTBatch_run_from_seed batch 1 (by omega)

/-- After both finite conversions, `B` actual WHY24 blocks use at most `3360`
non-seed noisy T resources per fresh T output. -/
theorem why24ConvertedTInputOutputRatio_le_overhead (index batch : Nat)
    (hbatch : 0 < batch) :
    ((4 * batch * why24OneRoundInputCount index : Nat) : Real) /
        (2 * batch * why24OneRoundOutputCount index) <= 3360 := by
  have houtputNat : 0 < why24OneRoundOutputCount index := by
    rw [why24OneRoundOutputCount_eq]
    exact why24OddDimension_pos index
  have hbatchReal : (batch : Real) ≠ 0 := by exact_mod_cast hbatch.ne'
  have houtputReal : (why24OneRoundOutputCount index : Real) ≠ 0 := by
    exact_mod_cast houtputNat.ne'
  calc
    ((4 * batch * why24OneRoundInputCount index : Nat) : Real) /
        (2 * batch * why24OneRoundOutputCount index) =
        2 * ((why24OneRoundInputCount index : Real) /
          why24OneRoundOutputCount index) := by
      push_cast
      field_simp [hbatchReal, houtputReal]
      ring
    _ <= 2 * 1680 :=
      mul_le_mul_of_nonneg_left (why24InputOutputRatio_le_overhead index)
        (by norm_num)
    _ = 3360 := by norm_num

/-! ## Actual BH12 catalyst seed and its amortization -/

private def why24CatalystSeedParameter : ErrorParameter where
  rate := 1 / 200
  rate_nonneg := by norm_num
  rate_le_one := by norm_num

private theorem why24CatalystSeedParameter_pos :
    0 < why24CatalystSeedParameter.rate := by
  norm_num [why24CatalystSeedParameter]

private theorem why24CatalystSeedParameter_le_half :
    why24CatalystSeedParameter.rate <= 1 / 2 := by
  norm_num [why24CatalystSeedParameter]

private theorem why24CatalystSeedParameter_small :
    (bh12InputCount 1 : Real) * why24CatalystSeedParameter.rate <= 1 / 4 := by
  norm_num [bh12InputCount, resourceCount, Column, logicalCount,
    why24CatalystSeedParameter]

private theorem why24CatalystSeedParameter_strong :
    quadraticCoefficient 1 * why24CatalystSeedParameter.rate <= 1 / 2 := by
  norm_num [quadraticCoefficient, why24CatalystSeedParameter]

private def why24CatalystSeedPort : OddRow 1 := (0, 0)

private def why24CatalystSeedPath : depthOutputPath 1 1 :=
  fun _ => why24CatalystSeedPort

private def why24CatalystSeedScheduleIndex : BH12PathScheduleIndex 1 where
  depth := 1
  path := why24CatalystSeedPath

/-- The seed is charged the actual successful-output cost of a concrete
depth-one BH12 path at rate `1/200`. -/
noncomputable def why24CatalystSeedCost : Real :=
  bh12PathScheduleTypedSuccessfulOutputCost 1 why24CatalystSeedParameter
    why24CatalystSeedParameter_small why24CatalystSeedParameter_le_half
    why24CatalystSeedParameter_strong why24CatalystSeedScheduleIndex

/-- The physical BH12 seed has strictly positive, hence non-free, expected
successful-output cost. -/
theorem why24CatalystSeedCost_pos : 0 < why24CatalystSeedCost := by
  have hyield := bh12PathSchedule_yield_pos 1 why24CatalystSeedParameter
    why24CatalystSeedParameter_small why24CatalystSeedParameter_le_half
    why24CatalystSeedParameter_strong why24CatalystSeedScheduleIndex
  have hinput :
      (Fintype.card
        (bh12PathScheduleInputSlots 1 why24CatalystSeedScheduleIndex) : Real) = 14 := by
    change (Fintype.card (depthRawInputPath 1 1) : Real) = 14
    rw [bh12PathTypedInputSlot_card]
    norm_num [bh12InputCount, resourceCount, Column, logicalCount]
  have houtput :
      (Fintype.card
        (bh12PathScheduleOutputSlots 1 why24CatalystSeedScheduleIndex) : Real) = 2 := by
    change (Fintype.card (depthOutputPath 1 1) : Real) = 2
    rw [bh12PathTypedOutputSlot_card]
    norm_num [bh12OutputCount, logicalCount]
  unfold why24CatalystSeedCost bh12PathScheduleTypedSuccessfulOutputCost
    DependentBatch.typedSuccessfulOutputCost DependentBatch.typedInputOutputRatio
  rw [hinput, houtput]
  exact div_pos (by norm_num) hyield

private theorem why24CatalystSeedPhysicalOverhead :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (bh12PathScheduleInputSlots 1) (bh12PathScheduleOutputSlots 1)
      (bh12PathScheduleTargetError 1 why24CatalystSeedParameter)
      (fun schedule =>
        (bh12PathParameter 1 why24CatalystSeedParameter
          schedule.depth schedule.path).rate)
      (bh12PathScheduleTypedYieldFactor 1 why24CatalystSeedParameter
        why24CatalystSeedParameter_small why24CatalystSeedParameter_le_half
        why24CatalystSeedParameter_strong)
      (bh12BlockExponent 1)
      (bh12QuadraticEnvelopeCostCoefficient 1 why24CatalystSeedParameter) :=
  bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead 1
    why24CatalystSeedParameter why24CatalystSeedParameter_small
    why24CatalystSeedParameter_le_half why24CatalystSeedParameter_strong
    why24CatalystSeedParameter_pos (by norm_num)

private theorem why24CatalystSeed_cofinalActualOutputError
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists depth : Nat, forall path : depthOutputPath 1 depth,
      0 < rawSuccessMass 1
          (bh12PathParameter 1 why24CatalystSeedParameter depth path) ∧
        0 < (bh12PathRun 1 why24CatalystSeedParameter depth path).successProbability ∧
          (forall port : OddRow 1,
            bh12PathSelectedPortTransportedDensity 1 why24CatalystSeedParameter
                depth path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter 1
                  (bh12PathParameter 1 why24CatalystSeedParameter depth path)
                  port)) ∧
            (bh12PathParameter 1 why24CatalystSeedParameter depth path).rate <=
              epsilon :=
  bh12PathSchedule_cofinalActualOutputError 1 why24CatalystSeedParameter
    why24CatalystSeedParameter_small why24CatalystSeedParameter_le_half
    why24CatalystSeedParameter_strong epsilon hepsilon

/-- The literal seed cost divided by the `2B k` fresh outputs of `B` WHY24
blocks tends to zero. -/
noncomputable def why24CatalystSeedCostPerFreshOutput (batch : Nat) : Real :=
  why24CatalystSeedCost /
    ((2 * batch * why24OneRoundOutputCount batch : Nat) : Real)

private theorem why24FreshTOutputCount_tendsto_atTop :
    Tendsto (fun batch : Nat =>
      2 * batch * why24OneRoundOutputCount batch) atTop atTop := by
  apply tendsto_atTop.2
  intro bound
  filter_upwards [eventually_ge_atTop bound] with batch hbatch
  have houtput : 0 < why24OneRoundOutputCount batch := by
    rw [why24OneRoundOutputCount_eq]
    exact why24OddDimension_pos batch
  calc
    bound <= batch := hbatch
    _ <= 2 * batch := by omega
    _ <= 2 * batch * why24OneRoundOutputCount batch :=
      Nat.le_mul_of_pos_right _ houtput

/-- A physical catalyst is never assigned zero cost; only its positive finite
BH12 cost is amortized over a growing number of fresh outputs. -/
theorem why24CatalystSeedCost_perFreshOutput_tendsto_zero :
    Tendsto why24CatalystSeedCostPerFreshOutput atTop (nhds 0) := by
  exact (tendsto_const_div_atTop_nhds_zero_nat why24CatalystSeedCost).comp
    why24FreshTOutputCount_tendsto_atTop

/-! ## Terminal physical theorem -/

/-- WHY24's constant-overhead theorem for the actual F1024 family and the
actual correlated local-stochastic one-round preparation.  The same theorem
records the computed finite T/CCZ conversions and charges the returned
catalyst its positive BH12 successful-output cost before amortization. -/
theorem why24_constant_overhead_distillation :
    exists threshold Omega : Real,
      0 < threshold ∧
      0 < Omega ∧
      (forall epsilon : Real, 0 < epsilon ->
        forall physicalRate : Real, 0 <= physicalRate ->
          physicalRate < threshold ->
            exists firstIndex : Nat,
              forall index : Nat, firstIndex <= index ->
                forall preparation : Why24LocalStochasticPreparation
                    (Fin (why24OneRoundInputCount index))
                    (why24IdealCCZRegisterDensity
                      (why24OneRoundInputCount index)),
                  preparation.rate <= physicalRate ->
                    let protocol :=
                      why24OneRoundMagicStateDistillationProtocol index preparation
                    protocol.run = why24OneRoundRun index preparation ∧
                      protocol.inputErrorModel = InputErrorModel.localStochastic
                        (why24LocalStochasticInputErrorModel preparation) ∧
                      protocol.behavior = .activeCorrection (QuantumChannel.id _) ∧
                      protocol.run.resourceCount = 70 * f1024Why24OddLength index ∧
                      why24OneRoundOutputCount index =
                        f1024Why24OddDimension index ∧
                      protocol.run.successProbability = 1 ∧
                      protocol.successfulOutputError <=
                        why24GeometricErrorEnvelope index ∧
                      protocol.successfulOutputError <= epsilon ∧
                      (why24OneRoundInputCount index : Real) /
                        why24OneRoundOutputCount index <= Omega) ∧
      (forall index batch : Nat, 0 < batch ->
        ((4 * batch * why24OneRoundInputCount index : Nat) : Real) /
            (2 * batch * why24OneRoundOutputCount index) <= 3360) ∧
      (forall batch : Nat,
        why24RunConversionProgram (why24FourTToCCZBatch batch)
            { tCount := 4 * batch
              cczCount := 0 } =
            some
              { tCount := 0
                cczCount := batch } ∧
          why24RunConversionProgram (why24CCZCatalyticTBatch batch)
            { tCount := 1
              cczCount := batch } =
            some
              { tCount := 2 * batch + 1
                cczCount := 0 }) ∧
      0 < why24CatalystSeedCost ∧
      (exists seedParameter : ErrorParameter,
        seedParameter.rate = 1 / 200 ∧
        exists hsmall :
            (bh12InputCount 1 : Real) * seedParameter.rate <= 1 / 4,
          exists hhalf : seedParameter.rate <= 1 / 2,
            exists hstrong :
                quadraticCoefficient 1 * seedParameter.rate <= 1 / 2,
              exists schedule : BH12PathScheduleIndex 1,
                why24CatalystSeedCost =
                    bh12PathScheduleTypedSuccessfulOutputCost 1 seedParameter
                      hsmall hhalf hstrong schedule ∧
                  DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                    (bh12PathScheduleInputSlots 1) (bh12PathScheduleOutputSlots 1)
                    (bh12PathScheduleTargetError 1 seedParameter)
                    (fun schedule =>
                      (bh12PathParameter 1 seedParameter
                        schedule.depth schedule.path).rate)
                    (bh12PathScheduleTypedYieldFactor 1 seedParameter
                      hsmall hhalf hstrong)
                    (bh12BlockExponent 1)
                    (bh12QuadraticEnvelopeCostCoefficient 1 seedParameter) ∧
                  (forall seedEpsilon : Real, 0 < seedEpsilon ->
                    exists depth : Nat, forall path : depthOutputPath 1 depth,
                      0 < rawSuccessMass 1
                          (bh12PathParameter 1 seedParameter depth path) ∧
                        0 < (bh12PathRun 1 seedParameter depth path).successProbability ∧
                          (forall port : OddRow 1,
                            bh12PathSelectedPortTransportedDensity 1 seedParameter
                                depth path port =
                              OneQubit.diagonalAResource
                                (bh12TotalNextParameter 1
                                  (bh12PathParameter 1 seedParameter depth path)
                                  port)) ∧
                            (bh12PathParameter 1 seedParameter depth path).rate <=
                              seedEpsilon)) ∧
      Tendsto why24CatalystSeedCostPerFreshOutput atTop (nhds 0) := by
  refine ⟨why24ThresholdRate, why24OverheadConstant,
    by norm_num [why24ThresholdRate], by norm_num [why24OverheadConstant],
    ?_, ?_, ?_, why24CatalystSeedCost_pos, ?_,
    why24CatalystSeedCost_perFreshOutput_tendsto_zero⟩
  · intro epsilon hepsilon physicalRate hphysicalRateNonneg hphysicalRateLt
    obtain ⟨firstIndex, hfirstIndex⟩ :=
      (Metric.tendsto_atTop.1 why24GeometricErrorEnvelope_tendsto_zero)
        epsilon hepsilon
    refine ⟨firstIndex, ?_⟩
    intro index hindex preparation hpreparation
    obtain ⟨hrun, hinputModel, hbehavior, hresourceCount, houtputCount,
      hsuccess, hfiniteError⟩ :=
      why24_one_round_physical_protocol index preparation
    have hpreparationThreshold : preparation.rate < why24ThresholdRate :=
      lt_of_le_of_lt hpreparation hphysicalRateLt
    have hgeometric := why24FiniteBinomialBound_le_geometric index preparation
      hpreparationThreshold
    have hsuccessfulGeometric := hfiniteError.trans hgeometric
    have hgeometricNonneg : 0 <= why24GeometricErrorEnvelope index := by
      unfold why24GeometricErrorEnvelope
      positivity
    have hgeometricLt : why24GeometricErrorEnvelope index < epsilon := by
      have hdist := hfirstIndex index hindex
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg hgeometricNonneg] using hdist
    dsimp only
    exact ⟨hrun, hinputModel, hbehavior, hresourceCount, houtputCount,
      hsuccess, hsuccessfulGeometric, hsuccessfulGeometric.trans hgeometricLt.le,
      why24InputOutputRatio_le_overhead index⟩
  · intro index batch hbatch
    exact why24ConvertedTInputOutputRatio_le_overhead index batch hbatch
  · intro batch
    exact ⟨why24FourTToCCZBatch_run batch, why24CCZCatalyticTBatch_run batch⟩
  · refine ⟨why24CatalystSeedParameter, rfl,
      why24CatalystSeedParameter_small, why24CatalystSeedParameter_le_half,
      why24CatalystSeedParameter_strong, why24CatalystSeedScheduleIndex, rfl,
      why24CatalystSeedPhysicalOverhead, ?_⟩
    intro seedEpsilon hseedEpsilon
    exact why24CatalystSeed_cofinalActualOutputError seedEpsilon hseedEpsilon

end QEC.Distillation.Why24ConstantOverhead
