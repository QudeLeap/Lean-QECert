import Mathlib.Analysis.SpecificLimits.Basic
import QEC.Distillation.Triorthogonal.Protocol
import QEC.Distillation.Core.DependentBatch
import QEC.Distillation.Core.Overhead
/-!
# First BH12 concatenation bridge

This internal checkpoint connects the actual #755 BH12 run to the finite
transpose routing used by later concatenation.  It exposes no independence
claim between sibling outputs and no terminal overhead theorem.
-/

noncomputable section

namespace QEC.Distillation.Triorthogonal.BH12Concatenation

open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

/-- The literal physical resource count consumed by one BH12 block. -/
def bh12InputCount (q : Nat) : Nat :=
  resourceCount q

/-- The actual number of logical ports carried by one BH12 block. -/
def bh12OutputCount (q : Nat) : Nat :=
  logicalCount q

/-- #755's resource count is the actual `(3k + 8)` count for this block. -/
theorem bh12InputCount_eq_three_mul_output_add_eight (q : Nat) :
    bh12InputCount q = 3 * bh12OutputCount q + 8 := by
  simpa [bh12InputCount, bh12OutputCount] using
    resourceCount_eq_three_logicalCount_add_eight q

/-- A nonzero BH12 family index has a positive number of logical outputs. -/
theorem bh12OutputCount_pos {q : Nat} (hq : 0 < q) :
    0 < bh12OutputCount q := by
  change 0 < 2 * q
  omega

/-- The actual real input/output block ratio, formed directly from the BH12
resource and logical-output counts. -/
noncomputable def bh12BlockRatio (q : Nat) : ℝ :=
  (bh12InputCount q : ℝ) / bh12OutputCount q

/-- The source-derived `(3k + 8)` count identity gives the exact real ratio
form `3 + 8/k` whenever the block has output ports. -/
theorem bh12BlockRatio_eq_three_add_eight_div_outputCount {q : Nat}
    (hq : 0 < q) :
    bh12BlockRatio q = 3 + 8 / (bh12OutputCount q : ℝ) := by
  unfold bh12BlockRatio
  rw [bh12InputCount_eq_three_mul_output_add_eight]
  push_cast
  field_simp [ne_of_gt (by exact_mod_cast bh12OutputCount_pos hq)]

/-- Every nonzero BH12 block has an actual input/output ratio strictly greater
than one. -/
theorem one_lt_bh12BlockRatio {q : Nat} (hq : 0 < q) :
    1 < bh12BlockRatio q := by
  rw [bh12BlockRatio_eq_three_add_eight_div_outputCount hq]
  have hk : 0 < (bh12OutputCount q : ℝ) := by
    exact_mod_cast bh12OutputCount_pos hq
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hk]

/-- Every positive finite BH12 block ratio is strictly above the limiting
ratio `3`. -/
theorem three_lt_bh12BlockRatio {q : Nat} (hq : 0 < q) :
    3 < bh12BlockRatio q := by
  rw [bh12BlockRatio_eq_three_add_eight_div_outputCount hq]
  have hk : 0 < (bh12OutputCount q : ℝ) := by
    exact_mod_cast bh12OutputCount_pos hq
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hk]

/-- The fixed-block exponent `γ(q) = log(N/k) / log 2`, derived from the
actual count ratio rather than stored family metadata. -/
noncomputable def bh12BlockExponent (q : Nat) : ℝ :=
  Real.log (bh12BlockRatio q) / Real.log 2

/-- The actual fixed-block logarithmic exponent is positive for `q > 0`. -/
theorem bh12BlockExponent_pos {q : Nat} (hq : 0 < q) :
    0 < bh12BlockExponent q := by
  unfold bh12BlockExponent
  exact div_pos (Real.log_pos (one_lt_bh12BlockRatio hq))
    (Real.log_pos (by norm_num))

/-- Every positive finite BH12 block exponent is strictly above the limiting
exponent `log 3 / log 2`. -/
theorem log_three_div_log_two_lt_bh12BlockExponent {q : Nat} (hq : 0 < q) :
    Real.log 3 / Real.log 2 < bh12BlockExponent q := by
  have hratio : 3 < bh12BlockRatio q := three_lt_bh12BlockRatio hq
  have hratioPos : 0 < bh12BlockRatio q := lt_trans (by norm_num) hratio
  have hlog : Real.log 3 < Real.log (bh12BlockRatio q) :=
    Real.strictMonoOn_log (by norm_num) hratioPos hratio
  unfold bh12BlockExponent
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr hlog

/-- No positive fixed finite BH12 block attains the limiting exponent. -/
theorem bh12BlockExponent_ne_log_three_div_log_two {q : Nat} (hq : 0 < q) :
    bh12BlockExponent q ≠ Real.log 3 / Real.log 2 :=
  ne_of_gt (log_three_div_log_two_lt_bh12BlockExponent hq)

/-- Every positive even source parameter has a positive index in the BH12
family.  The existing zero index remains only the structural endpoint and is
not used by the ratio or logarithm statements below. -/
theorem bh12_exists_pos_index_of_even_pos {k : Nat} (hk : Even k) (hpos : 0 < k) :
    ∃ q : Nat, 0 < q ∧ k = logicalCount q := by
  obtain ⟨q, hq⟩ := exists_index_of_even hk
  refine ⟨q, ?_, hq⟩
  rw [hq] at hpos
  simp only [logicalCount] at hpos
  omega

/-- Reindexing by a positive even source count exposes the literal BH12
input/output count ratio. -/
theorem bh12BlockRatio_eq_countRatio_of_logicalCount_eq {q k : Nat}
    (_ : 0 < q) (hk : k = logicalCount q) :
    bh12BlockRatio q = ((3 * k + 8 : Nat) : ℝ) / (k : ℝ) := by
  subst k
  unfold bh12BlockRatio
  rw [bh12InputCount_eq_three_mul_output_add_eight]
  rfl

/-- Reindexing by a positive even source count gives the exact real
logarithmic BH12 exponent; the denominator is never formed at `k = 0`. -/
theorem bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq {q k : Nat}
    (hq : 0 < q) (hk : k = logicalCount q) :
    bh12BlockExponent q =
      Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) / Real.log 2 := by
  unfold bh12BlockExponent
  rw [bh12BlockRatio_eq_countRatio_of_logicalCount_eq hq hk]

/-- Every positive even source count has a positive BH12 index whose exact
reindexed exponent remains strictly above the limiting exponent. -/
theorem bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos
    {k : Nat} (hk : Even k) (hpos : 0 < k) :
    ∃ q : Nat, 0 < q ∧ k = logicalCount q ∧
      bh12BlockExponent q =
        Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) / Real.log 2 ∧
      Real.log 3 / Real.log 2 < bh12BlockExponent q := by
  obtain ⟨q, hq, hlogicalCount⟩ := bh12_exists_pos_index_of_even_pos hk hpos
  exact ⟨q, hq, hlogicalCount,
    bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq hq hlogicalCount,
    log_three_div_log_two_lt_bh12BlockExponent hq⟩

/-- Along the explicit unbounded positive sequence `q + 1`, the actual BH12
input/output ratio tends to the source leading ratio three. -/
theorem bh12BlockRatio_succ_tendsto_three :
    Tendsto (fun q : Nat => bh12BlockRatio (q + 1)) atTop (𝓝 3) := by
  have hratio (q : Nat) :
      bh12BlockRatio (q + 1) = 3 + (4 : ℝ) / ((q + 1 : Nat) : ℝ) := by
    rw [bh12BlockRatio_eq_three_add_eight_div_outputCount (Nat.succ_pos q)]
    congr 1
    have hq : (q : ℝ) + 1 ≠ 0 := by positivity
    simp only [bh12OutputCount, logicalCount, Nat.cast_mul, Nat.cast_succ]
    field_simp [hq]
    ring
  have hsmall :
      Tendsto (fun q : Nat => (4 : ℝ) / ((q + 1 : Nat) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp (tendsto_add_atTop_nat 1)
  refine Tendsto.congr (fun q => (hratio q).symm) ?_
  simpa using (tendsto_const_nhds.add hsmall)

/-- The exact BH12 logarithmic exponent has the corresponding symbolic limit
along the same explicit positive sequence. -/
theorem bh12BlockExponent_succ_tendsto_log_three_div_log_two :
    Tendsto (fun q : Nat => bh12BlockExponent (q + 1)) atTop
      (𝓝 (Real.log 3 / Real.log 2)) := by
  have hlog : Tendsto (fun q : Nat => Real.log (bh12BlockRatio (q + 1))) atTop
      (𝓝 (Real.log 3)) :=
    bh12BlockRatio_succ_tendsto_three.log (by norm_num)
  simpa only [bh12BlockExponent] using hlog.div_const (Real.log 2)

/-- For every positive tolerance, some actual positive BH12 index has its
exact exponent within that tolerance of `log 3 / log 2`. -/
theorem exists_pos_bh12BlockExponent_sub_lt {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ q : Nat, 0 < q ∧
      |bh12BlockExponent q - Real.log 3 / Real.log 2| < epsilon := by
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1
    bh12BlockExponent_succ_tendsto_log_three_div_log_two) epsilon hepsilon
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  simpa only [Real.dist_eq] using hn n le_rfl

/-- At every finite natural depth, the real-rpow form of the base-two
exponent is exactly the literal BH12 input/output ratio power. -/
theorem bh12BlockRatio_rpow_two_pow_eq_pow {q : Nat} (hq : 0 < q)
    (z : Nat) :
    Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) =
      ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := by
  calc
    Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) =
        Real.exp (Real.log ((2 : ℝ) ^ z) * bh12BlockExponent q) := by
      exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((z : ℝ) * Real.log (bh12BlockRatio q)) := by
      unfold bh12BlockExponent
      congr 1
      rw [Real.log_pow]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    _ = Real.rpow (bh12BlockRatio q) (z : ℝ) := by
      symm
      calc
        Real.rpow (bh12BlockRatio q) (z : ℝ) =
            Real.exp (Real.log (bh12BlockRatio q) * (z : ℝ)) :=
          Real.rpow_def_of_pos
            (lt_trans zero_lt_one (one_lt_bh12BlockRatio hq)) _
        _ = Real.exp ((z : ℝ) * Real.log (bh12BlockRatio q)) :=
          congrArg Real.exp (mul_comm _ _)
    _ = bh12BlockRatio q ^ z := Real.rpow_natCast _ _
    _ = ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := rfl

/-- The coefficient in #755's enumerator-derived quadratic output-error bound. -/
def quadraticCoefficient (q : Nat) : ℝ :=
  8 * ((1 + 6 * q : Nat) : ℝ)

theorem quadraticCoefficient_pos (q : Nat) : 0 < quadraticCoefficient q := by
  unfold quadraticCoefficient
  positivity

/-- Raw inputs for two levels of an actual BH12 block grid.  Each of the
`n` parent blocks consumes its own `n` physical resources. -/
abbrev depthTwoRawInputSlots (q : Nat) :=
  Fin (bh12InputCount q) × Fin (bh12InputCount q)

/-- The `k` logical ports produced by each of the `n` parent blocks. -/
abbrev depthTwoParentOutputSlots (q : Nat) :=
  Fin (bh12InputCount q) × Fin (bh12OutputCount q)

/-- The inputs to the `k` child blocks: child port first, distinct parent
block second. -/
abbrev depthTwoChildInputSlots (q : Nat) :=
  Fin (bh12OutputCount q) × Fin (bh12InputCount q)

/-- Potential output ports after the two child blocks have each run once. -/
abbrev depthTwoPotentialOutputSlots (q : Nat) :=
  Fin (bh12OutputCount q) × Fin (bh12OutputCount q)

/-- The actual parent-output to child-input routing is the finite transpose.
It makes no assertion that different child blocks have independent outcomes. -/
def depthTwoRouting (q : Nat) :
    depthTwoParentOutputSlots q ≃ depthTwoChildInputSlots q :=
  DependentBatch.transposeRouting (bh12InputCount q) (bh12OutputCount q)

@[simp] theorem depthTwoRouting_apply (q : Nat)
    (parent : Fin (bh12InputCount q)) (port : Fin (bh12OutputCount q)) :
    depthTwoRouting q (parent, port) = (port, parent) :=
  rfl

/-- The actual #755 resource-dependent run, not a rate-capturing surrogate. -/
noncomputable def bh12ActualRun (q : Nat) (p : ErrorParameter) :
    DistillationRun Qubit.QubitSpace (PhysicalRegister q) (LogicalRegister q) :=
  resourceDecodedRun q (noisyResources q p)

/-- The run's success probability is #755's actual finite raw success mass. -/
theorem bh12ActualRun_successProbability (q : Nat) (p : ErrorParameter) :
    (bh12ActualRun q p).successProbability = rawSuccessMass q p := by
  simpa [bh12ActualRun] using
    resourceDecodedRun_successProbability_noisyResources q p

/-- The literal all-zero physical error word passes every BH12 even-row check. -/
theorem bh12AllZeroAccepted (q : Nat) :
    Accepts (0 : PhysicalError q) := by
  rw [accepts_iff_pairing_even_rows]
  intro check
  simp

/-- The literal all-zero physical word has its concrete independent Bernoulli
mass on every one of the actual BH12 input sites. -/
theorem bh12AllZeroWordProbability (q : Nat) (p : ErrorParameter) :
    errorWordProbability p (0 : PhysicalError q) =
      (1 - p.rate) ^ bh12InputCount q := by
  simp [errorWordProbability, ErrorParameter.cleanWeight,
    bh12InputCount, resourceCount]

/-- The actual finite accepted mass retains the nonnegative all-zero Bernoulli
summand, rather than introducing a success hypothesis. -/
theorem rawSuccessMass_allZeroWord_le (q : Nat) (p : ErrorParameter) :
    (1 - p.rate) ^ bh12InputCount q ≤ rawSuccessMass q p := by
  classical
  rw [rawSuccessMass]
  calc
    (1 - p.rate) ^ bh12InputCount q =
        if Accepts (0 : PhysicalError q) then
          errorWordProbability p (0 : PhysicalError q) else 0 := by
      rw [if_pos (bh12AllZeroAccepted q)]
      exact (bh12AllZeroWordProbability q p).symm
    _ ≤ ∑ error : PhysicalError q,
        if Accepts error then errorWordProbability p error else 0 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun error : PhysicalError q =>
          if Accepts error then errorWordProbability p error else 0)
        (fun error _ => by
          by_cases haccept : Accepts error
          · simp [haccept, errorWordProbability_nonneg p error]
          · simp [haccept])
        (Finset.mem_univ _)

/-- Bernoulli's inequality applied to the literal all-zero word lower-bounds
the concrete finite accepted BH12 mass. -/
theorem rawSuccessMass_one_sub_inputCount_rate_le (q : Nat) (p : ErrorParameter) :
    1 - (bh12InputCount q : ℝ) * p.rate ≤ rawSuccessMass q p := by
  calc
    1 - (bh12InputCount q : ℝ) * p.rate =
        1 + (bh12InputCount q : ℝ) * ((1 - p.rate) - 1) := by ring
    _ ≤ (1 - p.rate) ^ bh12InputCount q := by
      simpa using one_add_mul_sub_le_pow
        (a := 1 - p.rate) (by linarith [p.rate_le_one]) (bh12InputCount q)
    _ ≤ rawSuccessMass q p := rawSuccessMass_allZeroWord_le q p

/-- The all-zero-word lower bound belongs to the actual resource-decoded run. -/
theorem bh12ActualRun_successProbability_one_sub_inputCount_rate_le
    (q : Nat) (p : ErrorParameter) :
    1 - (bh12InputCount q : ℝ) * p.rate ≤
      (bh12ActualRun q p).successProbability := by
  rw [bh12ActualRun_successProbability]
  exact rawSuccessMass_one_sub_inputCount_rate_le q p

/-- On the stated honest small-error premise, the actual BH12 run has a
fixed `3/4` success lower bound. -/
theorem bh12ActualRun_three_quarters_le_successProbability (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    (3 : ℝ) / 4 ≤ (bh12ActualRun q p).successProbability := by
  calc
    (3 : ℝ) / 4 ≤ 1 - (bh12InputCount q : ℝ) * p.rate := by linarith
    _ ≤ (bh12ActualRun q p).successProbability :=
      bh12ActualRun_successProbability_one_sub_inputCount_rate_le q p

/-- The same actual `3/4` bound supplies the positive normalization mass. -/
theorem bh12ActualRun_successProbability_pos_of_small_error (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    0 < (bh12ActualRun q p).successProbability := by
  exact lt_of_lt_of_le (by norm_num)
    (bh12ActualRun_three_quarters_le_successProbability q p hsmall)

/-- The accepted output is the concrete output of the resource-dependent #755
run.  Its normalized interpretation is used only after positive success. -/
noncomputable def bh12AcceptedOutput (q : Nat) (p : ErrorParameter) :
    DensityOperator (LogicalRegister q) :=
  (bh12ActualRun q p).acceptedOutput

/-- At positive raw success mass, the accepted output is the actual normalized
accepted endpoint of #755's resource-dependent run. -/
theorem bh12AcceptedOutput_eq_resourceAcceptedOutput (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) :
    bh12AcceptedOutput q p =
      resourceAcceptedOutput q (noisyResources q p)
        (by
          rw [resourceAcceptedWeight_noisyResources_eq_rawSuccessMass]
          exact hsuccess) := by
  have hresource :
      0 < resourceEndpointWeight q (noisyResources q p) .accepted := by
    rw [resourceAcceptedWeight_noisyResources_eq_rawSuccessMass]
    exact hsuccess
  simpa [bh12AcceptedOutput, bh12ActualRun] using
    resourceDecodedRun_acceptedOutput q (noisyResources q p) hresource

/-- The literal singleton subsystem retaining one selected BH12 logical output
port.  It is a physical one-port subsystem of the accepted logical register,
not an independence or repeated-run assertion. -/
noncomputable def bh12SelectedPortSubsystem (q : Nat) (port : OddRow q) :
    FiniteSubsystem (OddRow q) :=
  ⟨{port}⟩

/-- The sole coordinate retained by the singleton physical output subsystem. -/
noncomputable def bh12SelectedPortCoordinate (q : Nat) (port : OddRow q) :
    (bh12SelectedPortSubsystem q port).SelectedCoordinates :=
  ⟨port, by simp [bh12SelectedPortSubsystem]⟩

/-- Every selected coordinate of the singleton subsystem is its designated port. -/
theorem bh12SelectedPortCoordinate_eq (q : Nat) (port : OddRow q)
    (coordinate : (bh12SelectedPortSubsystem q port).SelectedCoordinates) :
    coordinate = bh12SelectedPortCoordinate q port := by
  apply Subtype.ext
  have hmem : (coordinate : OddRow q) ∈ ({port} : Finset (OddRow q)) :=
    coordinate.property
  exact Finset.mem_singleton.mp hmem

/-- Bit labels of the singleton selected register are exactly one physical qubit bit. -/
def bh12SelectedPortBitstringEquiv (q : Nat) (port : OddRow q) :
    Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates ≃ Fin 2 where
  toFun := fun bits => bits (bh12SelectedPortCoordinate q port)
  invFun := fun bit _ => bit
  left_inv := by
    intro bits
    funext coordinate
    rw [bh12SelectedPortCoordinate_eq q port coordinate]
  right_inv := by
    intro bit
    rfl

/-- The basis-preserving unitary identification of one selected port with `QubitSpace`. -/
noncomputable def bh12SelectedPortTransport (q : Nat) (port : OddRow q) :
    UnitaryTransport (bh12SelectedPortSubsystem q port).selectedSystem
      Qubit.QubitSpace := by
  let sourceBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates) Complex
  let targetBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let U := sourceBasis.equiv targetBasis (bh12SelectedPortBitstringEquiv q port)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

@[simp] theorem bh12SelectedPortTransport_apply_basis (q : Nat) (port : OddRow q)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates) :
    bh12SelectedPortTransport q port
      (EuclideanSpace.basisFun _ Complex bits) =
      EuclideanSpace.basisFun _ Complex
        (bh12SelectedPortBitstringEquiv q port bits) := by
  dsimp [bh12SelectedPortTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The selected-zero basis label paired with one complement label.  This is
the concrete reference amplitude used to expose the remaining product state. -/
private def bh12SelectedPortAnchorBitstring (q : Nat) (port : OddRow q)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    Qubit.Bitstring (OddRow q) :=
  (bh12SelectedPortSubsystem q port).recombineBitstring ((fun _ => 0), bits)

/-- The complement product-A/error state, written as the selected-zero
amplitude of the actual logical-error state with the one-qubit normalization
removed. -/
noncomputable def bh12SelectedPortComplementErrorState (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) :
    (bh12SelectedPortSubsystem q port).complementSystem :=
  WithLp.toLp 2 fun bits =>
    (Real.sqrt 2 : Complex) * logicalErrorState logical
      (bh12SelectedPortAnchorBitstring q port bits)

@[simp] theorem bh12SelectedPortComplementErrorState_apply
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    bh12SelectedPortComplementErrorState q port logical bits =
      (Real.sqrt 2 : Complex) * logicalErrorState logical
        (bh12SelectedPortAnchorBitstring q port bits) :=
  rfl

/-- The explicit computational-basis amplitude of the BH12 logical-error
state: a CSS-Z sign times the logical magic-state phase and normalization. -/
private theorem bh12LogicalErrorState_apply (q : Nat)
    (logical : Coding.Word (ZMod 2) (OddRow q))
    (bits : Qubit.Bitstring (OddRow q)) :
    logicalErrorState logical bits =
      Qubit.zSupportPhase (Coding.PauliSymplectic.binarySupport logical) bits *
        (BinaryRowFamily.logicalUniformScalar (OddRow q) *
          BinaryRowFamily.piDivFourPhase ^
            Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
              (OddRow q) bits)) := by
  simp [logicalErrorState, Coding.PauliSymplectic.toQubitOperator_apply,
    Coding.PauliSymplectic.cssZCheck, Coding.PauliSymplectic.xSupport,
    Coding.PauliSymplectic.zSupport]

private theorem bh12SelectedPortAnchorBitstring_apply_port (q : Nat) (port : OddRow q)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    bh12SelectedPortAnchorBitstring q port bits port = 0 := by
  simp [bh12SelectedPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    bh12SelectedPortSubsystem]

private theorem bh12SelectedPortRecombineBitstring_apply_port (q : Nat) (port : OddRow q)
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    (bh12SelectedPortSubsystem q port).recombineBitstring (left, right) port =
      left (bh12SelectedPortCoordinate q port) := by
  simp only [FiniteSubsystem.recombineBitstring]
  rw [dif_pos (by simp [bh12SelectedPortSubsystem])]
  let coordinate : (bh12SelectedPortSubsystem q port).SelectedCoordinates :=
    ⟨port, by simp [bh12SelectedPortSubsystem]⟩
  change left coordinate = left (bh12SelectedPortCoordinate q port)
  rw [bh12SelectedPortCoordinate_eq q port coordinate]

private theorem bh12SelectedPortRecombineBitstring_apply_ne (q : Nat) (port : OddRow q)
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates)
    (site : OddRow q) (hsite : site ≠ port) :
    (bh12SelectedPortSubsystem q port).recombineBitstring (left, right) site =
      bh12SelectedPortAnchorBitstring q port right site := by
  simp [bh12SelectedPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    bh12SelectedPortSubsystem, hsite]

/-- The magic-state Hamming exponent splits into the selected singleton bit
and the selected-zero complement label. -/
private theorem bh12SelectedPortHammingWeight_recombine (q : Nat) (port : OddRow q)
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
      ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right))) =
      (bh12SelectedPortBitstringEquiv q port left).val +
        Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
          (bh12SelectedPortAnchorBitstring q port right)) := by
  classical
  generalize hbit : bh12SelectedPortBitstringEquiv q port left = bit
  fin_cases bit
  · have hleft : left (bh12SelectedPortCoordinate q port) = 0 := by
      simpa [bh12SelectedPortBitstringEquiv] using hbit
    have heq :
        (bh12SelectedPortSubsystem q port).recombineBitstring (left, right) =
          bh12SelectedPortAnchorBitstring q port right := by
      funext site
      by_cases hsite : site = port
      · subst site
        rw [bh12SelectedPortRecombineBitstring_apply_port,
          bh12SelectedPortAnchorBitstring_apply_port, hleft]
      · exact bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite
    simp [heq]
  · have hleft : left (bh12SelectedPortCoordinate q port) = 1 := by
      simpa [bh12SelectedPortBitstringEquiv] using hbit
    have hsupp :
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right))) =
          insert port
            (Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
              (bh12SelectedPortAnchorBitstring q port right))) := by
      ext site
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and,
        Coding.PauliSymplectic.bitstringWordEquiv_apply]
      by_cases hsite : site = port
      · subst site
        norm_num [
          bh12SelectedPortRecombineBitstring_apply_port,
          bh12SelectedPortAnchorBitstring_apply_port, hleft]
        exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
      · have happly :=
          bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite
        simp only [happly, hsite, false_or]
    have hnotmem : port ∉
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
          (bh12SelectedPortAnchorBitstring q port right)) := by
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter]
      simp [Coding.PauliSymplectic.bitstringWordEquiv_apply,
        bh12SelectedPortAnchorBitstring_apply_port]
      rfl
    simp only [Coding.HammingWeight, hsupp,
      Finset.card_insert_of_notMem hnotmem]
    omega

/-- The CSS-Z sign splits at the selected physical coordinate. -/
private theorem bh12SelectedPortZSupportPhase_recombine (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q))
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    Qubit.zSupportPhase (Coding.PauliSymplectic.binarySupport logical)
      ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
      (if logical port = 0 then 1 else
        Qubit.zPhase (bh12SelectedPortBitstringEquiv q port left)) *
        Qubit.zSupportPhase (Coding.PauliSymplectic.binarySupport logical)
          (bh12SelectedPortAnchorBitstring q port right) := by
  classical
  let support := Coding.PauliSymplectic.binarySupport logical
  by_cases hmem : port ∈ support
  · have hlogical : logical port ≠ 0 := by
      simpa [support, Coding.PauliSymplectic.binarySupport] using hmem
    have hprod :
        Qubit.zSupportPhase (support.erase port)
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
          Qubit.zSupportPhase (support.erase port)
            (bh12SelectedPortAnchorBitstring q port right) := by
      unfold Qubit.zSupportPhase
      apply Finset.prod_congr rfl
      intro site hsite
      have hsite_ne : site ≠ port := Finset.ne_of_mem_erase hsite
      rw [bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite_ne]
    calc
      Qubit.zSupportPhase support
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
          Qubit.zPhase
              ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right) port) *
            Qubit.zSupportPhase (support.erase port)
              ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) := by
            unfold Qubit.zSupportPhase
            nth_rewrite 1 [← Finset.insert_erase hmem]
            rw [Finset.prod_insert (Finset.notMem_erase _ _)]
      _ = Qubit.zPhase (bh12SelectedPortBitstringEquiv q port left) *
            Qubit.zSupportPhase (support.erase port)
              (bh12SelectedPortAnchorBitstring q port right) := by
            rw [bh12SelectedPortRecombineBitstring_apply_port, hprod]
            rfl
      _ = (if logical port = 0 then 1 else
            Qubit.zPhase (bh12SelectedPortBitstringEquiv q port left)) *
          Qubit.zSupportPhase support (bh12SelectedPortAnchorBitstring q port right) := by
            have hanchor :
                Qubit.zSupportPhase support (bh12SelectedPortAnchorBitstring q port right) =
                  Qubit.zSupportPhase (support.erase port)
                    (bh12SelectedPortAnchorBitstring q port right) := by
              unfold Qubit.zSupportPhase
              calc
                (∏ i ∈ support, Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i)) =
                    ∏ i ∈ insert port (support.erase port),
                      Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i) := by
                      nth_rewrite 1 [← Finset.insert_erase hmem]
                      rfl
                _ = Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right port) *
                    ∏ i ∈ support.erase port,
                      Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i) := by
                      rw [Finset.prod_insert (Finset.notMem_erase _ _)]
                _ = ∏ i ∈ support.erase port,
                    Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i) := by
                      rw [bh12SelectedPortAnchorBitstring_apply_port]
                      simp
            rw [if_neg hlogical]
            rw [hanchor]
  · have hlogical : logical port = 0 := by
      by_contra hlogical
      apply hmem
      simp [support, Coding.PauliSymplectic.binarySupport, hlogical]
    have hprod :
        Qubit.zSupportPhase support
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
          Qubit.zSupportPhase support (bh12SelectedPortAnchorBitstring q port right) := by
      unfold Qubit.zSupportPhase
      apply Finset.prod_congr rfl
      intro site hsite
      have hsite_ne : site ≠ port := by
        intro hsite_eq
        subst site
        exact hmem hsite
      rw [bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite_ne]
    rw [hprod, if_pos hlogical, one_mul]

/-- In the selected-port coordinates, the logical-error state has the literal
one-qubit `A`-basis amplitude times the selected-zero complement amplitude. -/
private theorem bh12SelectedPortLogicalErrorState_recombine_amplitude
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    logicalErrorState logical
        ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
      (if logical port = 0 then OneQubit.aZeroState else OneQubit.aOneState)
          (bh12SelectedPortBitstringEquiv q port left) *
        bh12SelectedPortComplementErrorState q port logical right := by
  rw [bh12LogicalErrorState_apply, bh12SelectedPortComplementErrorState_apply,
    bh12LogicalErrorState_apply, bh12SelectedPortHammingWeight_recombine,
    bh12SelectedPortZSupportPhase_recombine]
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast OneQubitMagic.sqrt_two_pos.ne'
  generalize hbit : bh12SelectedPortBitstringEquiv q port left = bit
  fin_cases bit <;> by_cases hlogical : logical port = 0
  all_goals simp [hlogical, OneQubit.aZeroState, OneQubit.aOneState,
    OneQubit.zTransport, OneQubit.zLinearEquiv, OneQubitMagic.phaseState,
    Qubit.pauliZ_apply, BinaryRowFamily.piDivFourPhase]
  all_goals field_simp [hsqrt_ne]
  all_goals ring

/-- The inverse singleton transport reads a selected-register amplitude at
the corresponding concrete bit. -/
private theorem bh12SelectedPortTransport_symm_apply (q : Nat) (port : OddRow q)
    (psi : Qubit.QubitSpace)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates) :
    (bh12SelectedPortTransport q port).symm psi bits =
      psi (bh12SelectedPortBitstringEquiv q port bits) := by
  have hinner := (bh12SelectedPortTransport q port).map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((bh12SelectedPortTransport q port).symm psi)
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [bh12SelectedPortTransport_apply_basis, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

/-- The inverse register factorization evaluates a pure selected/complement
tensor at the literal split bitstring. -/
private theorem bh12SelectedPortRegisterFactorization_symm_tmul_apply
    (q : Nat) (port : OddRow q)
    (leftState : (bh12SelectedPortSubsystem q port).selectedSystem)
    (rightState : (bh12SelectedPortSubsystem q port).complementSystem)
    (bits : Qubit.Bitstring (OddRow q)) :
    (bh12SelectedPortSubsystem q port).registerFactorization.symm
        (leftState ⊗ₜ[Complex] rightState) bits =
      leftState ((bh12SelectedPortSubsystem q port).splitBitstring bits).1 *
        rightState ((bh12SelectedPortSubsystem q port).splitBitstring bits).2 := by
  have hinner := (bh12SelectedPortSubsystem q port).registerFactorization.map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((bh12SelectedPortSubsystem q port).registerFactorization.symm
      (leftState ⊗ₜ[Complex] rightState))
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [FiniteSubsystem.registerFactorization_apply_basis, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

/-- The literal selected/complement decomposition of the actual logical-error
state.  No independent-output assumption is used: this is a coordinate
identity for one branch of the fixed finite BH12 logical register. -/
theorem bh12SelectedPortLogicalErrorState_factorization (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) :
    (bh12SelectedPortSubsystem q port).registerFactorization
        (logicalErrorState logical) =
      (if logical port = 0 then
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
      else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) ⊗ₜ[Complex]
        bh12SelectedPortComplementErrorState q port logical := by
  apply (bh12SelectedPortSubsystem q port).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_apply_apply]
  ext bits
  change logicalErrorState logical bits =
    (bh12SelectedPortSubsystem q port).registerFactorization.symm
      ((if logical port = 0 then
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
      else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) ⊗ₜ[Complex]
        bh12SelectedPortComplementErrorState q port logical) bits
  rw [bh12SelectedPortRegisterFactorization_symm_tmul_apply]
  have hsplit :
      (bh12SelectedPortSubsystem q port).recombineBitstring
          ((bh12SelectedPortSubsystem q port).splitBitstring bits) = bits := by
    simpa [FiniteSubsystem.bitstringFactorization] using
      (bh12SelectedPortSubsystem q port).bitstringFactorization.symm_apply_apply bits
  by_cases hlogical : logical port = 0
  · rw [if_pos hlogical]
    change logicalErrorState logical bits =
      (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
        ((bh12SelectedPortSubsystem q port).splitBitstring bits).1 *
        bh12SelectedPortComplementErrorState q port logical
          ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
    rw [bh12SelectedPortTransport_symm_apply]
    calc
      logicalErrorState logical bits =
          logicalErrorState logical
            ((bh12SelectedPortSubsystem q port).recombineBitstring
              ((bh12SelectedPortSubsystem q port).splitBitstring bits)) := by rw [hsplit]
      _ = OneQubit.aZeroState
            (bh12SelectedPortBitstringEquiv q port
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).1) *
            bh12SelectedPortComplementErrorState q port logical
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).2 := by
            simpa [hlogical] using
              bh12SelectedPortLogicalErrorState_recombine_amplitude q port logical
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).1
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
  · rw [if_neg hlogical]
    change logicalErrorState logical bits =
      (bh12SelectedPortTransport q port).symm OneQubit.aOneState
        ((bh12SelectedPortSubsystem q port).splitBitstring bits).1 *
        bh12SelectedPortComplementErrorState q port logical
          ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
    rw [bh12SelectedPortTransport_symm_apply]
    calc
      logicalErrorState logical bits =
          logicalErrorState logical
            ((bh12SelectedPortSubsystem q port).recombineBitstring
              ((bh12SelectedPortSubsystem q port).splitBitstring bits)) := by rw [hsplit]
      _ = OneQubit.aOneState
            (bh12SelectedPortBitstringEquiv q port
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).1) *
            bh12SelectedPortComplementErrorState q port logical
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).2 := by
            simpa [hlogical] using
              bh12SelectedPortLogicalErrorState_recombine_amplitude q port logical
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).1
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).2

/-- The concrete complement state in the selected-port factorization is
normalized because the fixed logical-error branch and its one-qubit factor
are both normalized. -/
theorem bh12SelectedPortComplementErrorState_inner_self (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) :
    inner Complex (bh12SelectedPortComplementErrorState q port logical)
      (bh12SelectedPortComplementErrorState q port logical) = 1 := by
  have hglobal : inner Complex (logicalErrorState logical) (logicalErrorState logical) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hnorm : ‖logicalErrorState logical‖ = 1 := by
      nlinarith [norm_nonneg (logicalErrorState logical), logicalErrorState_normSq logical]
    rw [hnorm]
    norm_num
  have hlocal :
      inner Complex
          (if logical port = 0 then
            (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
          else (bh12SelectedPortTransport q port).symm OneQubit.aOneState)
          (if logical port = 0 then
            (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
          else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) = 1 := by
    by_cases hlogical : logical port = 0
    · rw [if_pos hlogical]
      calc
        inner Complex ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState)
            ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState) =
            inner Complex
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState))
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState)) :=
              ((bh12SelectedPortTransport q port).map_inner _ _).symm
        _ = inner Complex OneQubit.aZeroState OneQubit.aZeroState := by
              simp only [UnitaryTransport.symm_toLinearEquiv,
                LinearEquiv.apply_symm_apply]
        _ = 1 := by
              rw [inner_self_eq_norm_sq_to_K]
              simp
    · rw [if_neg hlogical]
      calc
        inner Complex ((bh12SelectedPortTransport q port).symm OneQubit.aOneState)
            ((bh12SelectedPortTransport q port).symm OneQubit.aOneState) =
            inner Complex
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aOneState))
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aOneState)) :=
              ((bh12SelectedPortTransport q port).map_inner _ _).symm
        _ = inner Complex OneQubit.aOneState OneQubit.aOneState := by
              simp only [UnitaryTransport.symm_toLinearEquiv,
                LinearEquiv.apply_symm_apply]
        _ = 1 := by
              rw [OneQubit.aOneState_eq_pauliZ, OneQubit.pauliZ_map_inner,
                inner_self_eq_norm_sq_to_K]
              simp
  have hfactorNorm :
      inner Complex
          ((bh12SelectedPortSubsystem q port).registerFactorization
            (logicalErrorState logical))
          ((bh12SelectedPortSubsystem q port).registerFactorization
            (logicalErrorState logical)) = 1 := by
    rw [(bh12SelectedPortSubsystem q port).registerFactorization.map_inner]
    exact hglobal
  rw [bh12SelectedPortLogicalErrorState_factorization, TensorProduct.inner_tmul,
    hlocal, one_mul] at hfactorNorm
  exact hfactorNorm

/-- A factored pure branch with local `|A⟩` has exactly the corresponding
physical selected-port density after the concrete partial trace and transport. -/
theorem bh12SelectedPortTransport_partialTrace_pure_aZero_of_factorized
    (q : Nat) (port : OddRow q) (psi : LogicalRegister q)
    (hpsi : ‖psi‖ ^ 2 = 1)
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization psi =
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    (bh12SelectedPortTransport q port).conjDensity
      ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (DensityOperator.pureDensity psi hpsi)) = OneQubit.aZeroDensity := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, FiniteSubsystem.selectedPartialTrace,
    DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [hfactor]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [hrest]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact OneQubit.aZeroDensity_rankOne.symm

/-- A factored pure branch with local `Z|A⟩` has exactly the corresponding
physical selected-port density after the concrete partial trace and transport. -/
theorem bh12SelectedPortTransport_partialTrace_pure_aOne_of_factorized
    (q : Nat) (port : OddRow q) (psi : LogicalRegister q)
    (hpsi : ‖psi‖ ^ 2 = 1)
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization psi =
        (bh12SelectedPortTransport q port).symm OneQubit.aOneState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    (bh12SelectedPortTransport q port).conjDensity
      ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (DensityOperator.pureDensity psi hpsi)) = OneQubit.aOneDensity := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, FiniteSubsystem.selectedPartialTrace,
    DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [hfactor]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [hrest]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact OneQubit.aOneDensity_rankOne.symm

/-- The physical density on one selected output port of the actual BH12
accepted output, obtained by the concrete CPTP partial trace. -/
noncomputable def bh12SelectedPortDensity (q : Nat) (p : ErrorParameter)
    (port : OddRow q) :
    DensityOperator (bh12SelectedPortSubsystem q port).selectedSystem :=
  (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
    (bh12AcceptedOutput q p)

/-- The raw marginal error mass is bounded by the actual raw accepted mass:
each nonzero logical-bit sector is a nonnegative sub-sum of the finite
accepted logical-error decomposition. -/
theorem bh12RawMarginalErrorWeight_le_rawSuccessMass (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    rawMarginalErrorWeight q p port ≤ rawSuccessMass q p := by
  calc
    rawMarginalErrorWeight q p port =
        ∑ logical : Coding.Word (ZMod 2) (OddRow q),
          if logical port = 0 then 0 else rawLogicalErrorWeight q p logical := rfl
    _ ≤ ∑ logical : Coding.Word (ZMod 2) (OddRow q),
          rawLogicalErrorWeight q p logical := by
      apply Finset.sum_le_sum
      intro logical _
      by_cases hbit : logical port = 0
      · simp [hbit, rawLogicalErrorWeight_nonneg]
      · simp [hbit]
    _ = rawSuccessMass q p := sum_rawLogicalErrorWeight q p

/-- After conditioning on positive actual success mass, the decoded marginal
error is a probability. -/
theorem bh12DecodedMarginalError_le_one (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    decodedMarginalError q p hsuccess port ≤ 1 := by
  simp only [decodedMarginalError, dif_pos hsuccess]
  rw [div_le_one₀ hsuccess]
  exact bh12RawMarginalErrorWeight_le_rawSuccessMass q p port

/-- The actual normalized accepted marginal is a concrete valid one-qubit
error parameter. -/
noncomputable def bh12DecodedMarginalErrorParameter (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) : ErrorParameter where
  rate := decodedMarginalError q p hsuccess port
  rate_nonneg := decodedMarginalError_nonneg q p hsuccess port
  rate_le_one := bh12DecodedMarginalError_le_one q p hsuccess port

@[simp] theorem bh12DecodedMarginalErrorParameter_rate (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    (bh12DecodedMarginalErrorParameter q p hsuccess port).rate =
      decodedMarginalError q p hsuccess port :=
  rfl

/-- The actual selected physical marginal, transported to the canonical
one-qubit Hilbert space. -/
noncomputable def bh12SelectedPortTransportedDensity (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    (bh12SelectedPortDensity q p port)

/-- The selected physical port of one actual decoded logical-error branch,
transported to the canonical one-qubit Hilbert space. -/
noncomputable def bh12SelectedPortLogicalErrorDensity (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) : DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
      (logicalErrorDensity logical))

/-- An actual logical-error branch whose concrete selected/complement state
factorization has local `|A⟩` has exactly the `|A⟩` physical port density. -/
theorem bh12SelectedPortLogicalErrorDensity_eq_aZeroDensity_of_factorized
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization
          (logicalErrorState logical) =
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    bh12SelectedPortLogicalErrorDensity q port logical = OneQubit.aZeroDensity := by
  simpa [bh12SelectedPortLogicalErrorDensity, logicalErrorDensity] using
    bh12SelectedPortTransport_partialTrace_pure_aZero_of_factorized q port
      (logicalErrorState logical) (logicalErrorState_normSq logical) rest hfactor hrest

/-- An actual logical-error branch whose concrete selected/complement state
factorization has local `Z|A⟩` has exactly the `Z|A⟩` physical port density. -/
theorem bh12SelectedPortLogicalErrorDensity_eq_aOneDensity_of_factorized
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization
          (logicalErrorState logical) =
        (bh12SelectedPortTransport q port).symm OneQubit.aOneState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    bh12SelectedPortLogicalErrorDensity q port logical = OneQubit.aOneDensity := by
  simpa [bh12SelectedPortLogicalErrorDensity, logicalErrorDensity] using
    bh12SelectedPortTransport_partialTrace_pure_aOne_of_factorized q port
      (logicalErrorState logical) (logicalErrorState_normSq logical) rest hfactor hrest

/-- The exact physical selected-port branch follows from the still-explicit
selected/complement factorization of the actual logical-error state. -/
theorem bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_of_factorization
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization
          (logicalErrorState logical) =
        (if logical port = 0 then
          (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
        else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    bh12SelectedPortLogicalErrorDensity q port logical =
      if logical port = 0 then OneQubit.aZeroDensity else OneQubit.aOneDensity := by
  by_cases hbit : logical port = 0
  · rw [if_pos hbit] at hfactor ⊢
    exact bh12SelectedPortLogicalErrorDensity_eq_aZeroDensity_of_factorized
      q port logical rest hfactor hrest
  · rw [if_neg hbit] at hfactor ⊢
    exact bh12SelectedPortLogicalErrorDensity_eq_aOneDensity_of_factorized
      q port logical rest hfactor hrest

/-- The actual selected port of every fixed BH12 logical-error branch is the
corresponding one-qubit `A`-basis density.  The complement witness and its
normalization are constructed above from the branch amplitudes themselves. -/
theorem bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_actual
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q)) :
    bh12SelectedPortLogicalErrorDensity q port logical =
      if logical port = 0 then OneQubit.aZeroDensity else OneQubit.aOneDensity := by
  exact bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_of_factorization
    q port logical (bh12SelectedPortComplementErrorState q port logical)
    (bh12SelectedPortLogicalErrorState_factorization q port logical)
    (bh12SelectedPortComplementErrorState_inner_self q port logical)

/-- The actual transported selected-port operation, retained privately to
make the accepted-mixture linearity explicit at the operator level. -/
private noncomputable def bh12SelectedPortTransportedChannel (q : Nat)
    (port : OddRow q) :
    QuantumChannel (LogicalRegister q) Qubit.QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (bh12SelectedPortTransport q port))
    (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister

private theorem bh12SelectedPortTransportedDensity_toOperator (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    (bh12SelectedPortTransportedDensity q p port).toOperator =
      bh12SelectedPortTransportedChannel q port
        (bh12AcceptedOutput q p).toOperator :=
  rfl

private theorem bh12SelectedPortTransportedChannel_logicalErrorDensity
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q)) :
    bh12SelectedPortTransportedChannel q port
        (logicalErrorDensity logical).toOperator =
      if logical port = 0 then OneQubit.aZeroDensity.toOperator
      else OneQubit.aOneDensity.toOperator := by
  change (bh12SelectedPortLogicalErrorDensity q port logical).toOperator = _
  simpa only [apply_ite] using congrArg DensityOperator.toOperator
    (bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_actual q port logical)

/-- The marginal-error coefficient is the literal physical finite sum over
accepted branches whose decoded selected bit is nonzero. -/
private theorem bh12RawMarginalErrorWeight_eq_errorWordSum (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    rawMarginalErrorWeight q p port =
      ∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port ≠ 0 then
          errorWordProbability p error else 0 := by
  classical
  unfold rawMarginalErrorWeight rawLogicalErrorWeight
  calc
    (∑ logical : Coding.Word (ZMod 2) (OddRow q),
      if logical port = 0 then 0 else
        ∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error = logical then
            errorWordProbability p error else 0) =
        ∑ logical : Coding.Word (ZMod 2) (OddRow q),
          ∑ error : PhysicalError q,
            if logical port = 0 then 0 else
              if Accepts error ∧ logicalErrorWord error = logical then
                errorWordProbability p error else 0 := by
      apply Finset.sum_congr rfl
      intro logical _
      by_cases hlogical : logical port = 0 <;> simp [hlogical]
    _ = ∑ error : PhysicalError q,
          ∑ logical : Coding.Word (ZMod 2) (OddRow q),
            if logical port = 0 then 0 else
              if Accepts error ∧ logicalErrorWord error = logical then
                errorWordProbability p error else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port ≠ 0 then
          errorWordProbability p error else 0 := by
      apply Finset.sum_congr rfl
      intro error _
      by_cases haccept : Accepts error
      · by_cases hbit : logicalErrorWord error port = 0
        · rw [Fintype.sum_eq_single (logicalErrorWord error)]
          · simp [haccept, hbit]
          · intro logical hne
            simp [hne.symm]
        · rw [Fintype.sum_eq_single (logicalErrorWord error)]
          · simp [haccept, hbit]
          · intro logical hne
            simp [hne.symm]
      · simp [haccept]

/-- The accepted physical finite sum partitions into its selected-zero and
selected-nonzero decoded sectors. -/
private theorem bh12RawSuccessMass_eq_zeroPlusMarginal (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    rawSuccessMass q p =
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port = 0 then
          errorWordProbability p error else 0) +
        rawMarginalErrorWeight q p port := by
  rw [bh12RawMarginalErrorWeight_eq_errorWordSum]
  change (∑ error : PhysicalError q,
    if Accepts error then errorWordProbability p error else 0) = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccept : Accepts error
  · by_cases hbit : logicalErrorWord error port = 0 <;>
      simp [haccept, hbit]
  · simp [haccept]

private theorem bh12RawZeroBitWeight_eq_success_sub_marginal (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    (∑ error : PhysicalError q,
      if Accepts error ∧ logicalErrorWord error port = 0 then
        errorWordProbability p error else 0) =
      rawSuccessMass q p - rawMarginalErrorWeight q p port := by
  linarith [bh12RawSuccessMass_eq_zeroPlusMarginal q p port]

/-- Regrouping the literal accepted physical error-word sum after the selected
port channel gives the exact clean/error `A`-basis coefficients. -/
private theorem bh12SelectedPortTransported_errorWordSum_grouped (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    (∑ error : PhysicalError q,
      if Accepts error then
        (errorWordProbability p error : Complex) •
          (if logicalErrorWord error port = 0 then OneQubit.aZeroDensity.toOperator
          else OneQubit.aOneDensity.toOperator)
      else 0) =
      ((rawSuccessMass q p - rawMarginalErrorWeight q p port : Complex) •
        OneQubit.aZeroDensity.toOperator) +
      ((rawMarginalErrorWeight q p port : Complex) •
        OneQubit.aOneDensity.toOperator) := by
  have hzero :
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port = 0 then
          errorWordProbability p error else 0) =
        rawSuccessMass q p - rawMarginalErrorWeight q p port :=
    bh12RawZeroBitWeight_eq_success_sub_marginal q p port
  have hzeroComplex :
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port = 0 then
          (errorWordProbability p error : Complex) else 0) =
        (rawSuccessMass q p - rawMarginalErrorWeight q p port : Complex) := by
    convert congrArg (fun x : ℝ => (x : Complex)) hzero using 1
    · push_cast
      apply Finset.sum_congr rfl
      intro error _
      split <;> rfl
    · norm_cast
  have hmarginalComplex :
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port ≠ 0 then
          (errorWordProbability p error : Complex) else 0) =
        (rawMarginalErrorWeight q p port : Complex) := by
    convert congrArg (fun x : ℝ => (x : Complex))
      (bh12RawMarginalErrorWeight_eq_errorWordSum q p port).symm using 1
    · push_cast
      apply Finset.sum_congr rfl
      intro error _
      split <;> rfl
  calc
    (∑ error : PhysicalError q,
      if Accepts error then
        (errorWordProbability p error : Complex) •
          (if logicalErrorWord error port = 0 then OneQubit.aZeroDensity.toOperator
          else OneQubit.aOneDensity.toOperator)
      else 0) =
        ∑ error : PhysicalError q,
          ((if Accepts error ∧ logicalErrorWord error port = 0 then
            (errorWordProbability p error : Complex) else 0) •
              OneQubit.aZeroDensity.toOperator +
            (if Accepts error ∧ logicalErrorWord error port ≠ 0 then
              (errorWordProbability p error : Complex) else 0) •
                OneQubit.aOneDensity.toOperator) := by
          apply Finset.sum_congr rfl
          intro error _
          by_cases haccept : Accepts error
          · by_cases hbit : logicalErrorWord error port = 0 <;>
              simp [haccept, hbit]
          · simp [haccept]
    _ = ((∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error port = 0 then
            (errorWordProbability p error : Complex) else 0) •
            OneQubit.aZeroDensity.toOperator) +
        ((∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error port ≠ 0 then
            (errorWordProbability p error : Complex) else 0) •
            OneQubit.aOneDensity.toOperator) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
    _ = _ := by rw [hzeroComplex, hmarginalComplex]

/-- The transported physical selected-port density of the actual normalized
accepted BH12 mixture is exactly the diagonal `A`-basis resource at its
derived decoded-marginal error rate. -/
theorem bh12SelectedPortTransportedDensity_eq_diagonalAResource (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (port : OddRow q) :
    bh12SelectedPortTransportedDensity q p port =
      OneQubit.diagonalAResource
        (bh12DecodedMarginalErrorParameter q p hsuccess port) := by
  apply DensityOperator.ext_toOperator
  rw [bh12SelectedPortTransportedDensity_toOperator, bh12AcceptedOutput,
    bh12ActualRun, resourceDecodedRun_acceptedOutput_toOperator_errorWordSum
      q p hsuccess]
  simp only [map_smul, map_sum, apply_ite, map_zero]
  simp_rw [bh12SelectedPortTransportedChannel_logicalErrorDensity]
  rw [bh12SelectedPortTransported_errorWordSum_grouped]
  rw [OneQubit.diagonalAResource_toOperator]
  simp only [bh12DecodedMarginalErrorParameter_rate, ErrorParameter.cleanWeight,
    decodedMarginalError, dif_pos hsuccess,
    RCLike.real_smul_eq_coe_smul (K := Complex), map_sub, map_mul, map_inv₀,
    div_eq_mul_inv]
  have hsuccessComplex : (rawSuccessMass q p : Complex) ≠ 0 := by
    exact_mod_cast hsuccess.ne'
  have hzeroCoeff :
      (rawSuccessMass q p : Complex)⁻¹ *
          (rawSuccessMass q p - rawMarginalErrorWeight q p port : Complex) =
        1 - (rawMarginalErrorWeight q p port : Complex) *
          (rawSuccessMass q p : Complex)⁻¹ := by
    field_simp [hsuccessComplex]
  rw [smul_add, smul_smul, smul_smul, hzeroCoeff]
  ring_nf
  simp only [Complex.coe_algebraMap, Complex.ofReal_one]

/-- The selected-port density is the literal partial trace of #755's actual
resource-decoded accepted run. -/
theorem bh12SelectedPortDensity_eq_actualRunMarginal (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    bh12SelectedPortDensity q p port =
      (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        ((resourceDecodedRun q (noisyResources q p)).acceptedOutput) := by
  rfl

/-- At positive raw success mass, the selected-port density is the partial
trace of the actual normalized resource-accepted output. -/
theorem bh12SelectedPortDensity_eq_resourceAcceptedMarginal (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    bh12SelectedPortDensity q p port =
      (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (resourceAcceptedOutput q (noisyResources q p)
          (by
            rw [resourceAcceptedWeight_noisyResources_eq_rawSuccessMass]
            exact hsuccess)) := by
  rw [bh12SelectedPortDensity, bh12AcceptedOutput_eq_resourceAcceptedOutput q p hsuccess]

/-- The actual A-basis error diagnostic for the same selected port in the
accepted register, before any unproved identification with a one-qubit
density observable. -/
noncomputable def bh12SelectedPortABasisError (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : ℝ :=
  bh12ABasisOutputError port (bh12AcceptedOutput q p) (bh12IdealOutput q)

/-- #755's exact enumerator calculation identifies the selected port's actual
A-basis error diagnostic with its normalized marginal error. -/
theorem bh12SelectedPortABasisError_eq_decodedMarginal (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    bh12SelectedPortABasisError q p port = decodedMarginalError q p hsuccess port := by
  simpa [bh12SelectedPortABasisError, bh12AcceptedOutput, bh12ActualRun] using
    bh12ABasisOutputError_acceptedOutput q p hsuccess port

/-- A selected logical port's actual accepted marginal error. -/
noncomputable def bh12AcceptedPortError (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) : ℝ :=
  decodedMarginalError q p hsuccess port

/-- The selected port inherits the enumerator-derived quadratic bound from the
actual #755 accepted logical-error mixture. -/
theorem bh12AcceptedPortError_le_quadratic (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q)
    (hhalf : p.rate ≤ 1 / 2) :
    bh12AcceptedPortError q p hsuccess port ≤
      quadraticCoefficient q * p.rate ^ 2 := by
  simpa [bh12AcceptedPortError, quadraticCoefficient] using
    decodedMarginalError_le_evenFamily_quadratic q p port hhalf

/-- One actual BH12 step preserves explicit source-domain smallness for a
selected physical port.  Its output parameter is derived from the normalized
accepted mixture, rather than supplied as a rate or density assumption. -/
theorem bh12OneStepPhysicalInvariant (q : Nat) (p : ErrorParameter)
    (port : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∃ hsuccess : 0 < rawSuccessMass q p,
      0 < (bh12ActualRun q p).successProbability ∧
        bh12SelectedPortTransportedDensity q p port =
          OneQubit.diagonalAResource
            (bh12DecodedMarginalErrorParameter q p hsuccess port) ∧
        (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
          quadraticCoefficient q * p.rate ^ 2 ∧
        (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ p.rate ∧
        (bh12InputCount q : ℝ) *
            (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ 1 / 4 ∧
        (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ 1 / 2 ∧
        quadraticCoefficient q *
            (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ 1 := by
  have hactualSuccess : 0 < (bh12ActualRun q p).successProbability :=
    bh12ActualRun_successProbability_pos_of_small_error q p hsmall
  have hsuccess : 0 < rawSuccessMass q p := by
    rw [← bh12ActualRun_successProbability q p]
    exact hactualSuccess
  have hquadratic :
      (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
        quadraticCoefficient q * p.rate ^ 2 := by
    simpa only [bh12DecodedMarginalErrorParameter_rate, bh12AcceptedPortError] using
      bh12AcceptedPortError_le_quadratic q p hsuccess port hhalf
  have hnonincrease :
      (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ p.rate := by
    calc
      (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
          quadraticCoefficient q * p.rate ^ 2 := hquadratic
      _ = (quadraticCoefficient q * p.rate) * p.rate := by ring
      _ ≤ 1 * p.rate :=
        mul_le_mul_of_nonneg_right hquadraticSmall p.rate_nonneg
      _ = p.rate := one_mul _
  refine ⟨hsuccess, hactualSuccess,
    bh12SelectedPortTransportedDensity_eq_diagonalAResource q p hsuccess port,
    hquadratic, hnonincrease, ?_, hnonincrease.trans hhalf, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hnonincrease (by positivity)).trans hsmall
  · exact (mul_le_mul_of_nonneg_left hnonincrease
      (le_of_lt (quadraticCoefficient_pos q))).trans hquadraticSmall

/-- The routed input slot of one fixed child block, supplied by a designated
fresh parent block. -/
def depthTwoChildInputSlot (q : Nat) (child : Fin (bh12OutputCount q))
    (parent : Fin (bh12InputCount q)) :
    depthTwoChildInputSlots q :=
  depthTwoRouting q (DependentBatch.childInputSlot child parent)

@[simp] theorem depthTwoChildInputSlot_apply (q : Nat)
    (child : Fin (bh12OutputCount q)) (parent : Fin (bh12InputCount q)) :
    depthTwoChildInputSlot q child parent = (child, parent) :=
  rfl

/-- The routed inputs of one child block have pairwise distinct parent sources. -/
theorem depthTwoChildInputSlot_injective (q : Nat)
    (child : Fin (bh12OutputCount q)) :
    Function.Injective (depthTwoChildInputSlot q child) := by
  intro left right h
  apply DependentBatch.childInputSlot_injective child
  apply (depthTwoRouting q).injective
  exact h

/-- The actual BH12 execution associated with one fresh parent index.  This is
an indexed copy of the physical run, not an independence assertion. -/
noncomputable def depthTwoFreshParentRun (q : Nat) (p : ErrorParameter)
    (_parent : Fin (bh12InputCount q)) :=
  bh12ActualRun q p

/-- The physical selected-port state produced by one indexed fresh parent. -/
noncomputable def depthTwoFreshParentPortDensity (q : Nat) (p : ErrorParameter)
    (parent : Fin (bh12InputCount q)) (port : OddRow q) :
    DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
      (depthTwoFreshParentRun q p parent).acceptedOutput)

theorem depthTwoFreshParentPortDensity_eq_selectedPortDensity (q : Nat)
    (p : ErrorParameter) (parent : Fin (bh12InputCount q)) (port : OddRow q) :
    depthTwoFreshParentPortDensity q p parent port =
      bh12SelectedPortTransportedDensity q p port :=
  rfl

/-- The child resource family uses one selected physical output from each
distinct indexed parent execution. -/
noncomputable def depthTwoChildResources (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : ResourceInput (bh12InputCount q) Qubit.QubitSpace :=
  fun parent => depthTwoFreshParentPortDensity q p parent port

/-- The physical child resources are exactly the ordinary BH12 noisy-resource
family at the selected parent's derived decoded-marginal parameter. -/
theorem depthTwoChildResources_eq_noisyResources (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    depthTwoChildResources q p port =
      noisyResources q (bh12DecodedMarginalErrorParameter q p hsuccess port) := by
  funext parent
  change depthTwoFreshParentPortDensity q p parent port =
    OneQubit.diagonalAResource
      (bh12DecodedMarginalErrorParameter q p hsuccess port)
  rw [depthTwoFreshParentPortDensity_eq_selectedPortDensity]
  exact bh12SelectedPortTransportedDensity_eq_diagonalAResource q p hsuccess port

/-- The actual second-level resource-decoded BH12 run fed by the fresh parent
selected-port family. -/
noncomputable def depthTwoChildRun (q : Nat) (p : ErrorParameter)
    (port : OddRow q) :=
  resourceDecodedRun q (depthTwoChildResources q p port)

/-- Once the parent success mass is positive, the child run is exactly the
ordinary BH12 run at the derived decoded-marginal parameter. -/
theorem depthTwoChildRun_eq_bh12ActualRun (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    depthTwoChildRun q p port =
      bh12ActualRun q (bh12DecodedMarginalErrorParameter q p hsuccess port) := by
  unfold depthTwoChildRun bh12ActualRun
  rw [depthTwoChildResources_eq_noisyResources]

/-- The physical selected-port density of the actual second-level child run. -/
noncomputable def depthTwoChildSelectedPortTransportedDensity (q : Nat)
    (p : ErrorParameter) (firstPort secondPort : OddRow q) :
    DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q secondPort).conjDensity
    ((bh12SelectedPortSubsystem q secondPort).selectedPartialTraceFromRegister.mapDensity
      (depthTwoChildRun q p firstPort).acceptedOutput)

theorem depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
    (q : Nat) (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (firstPort secondPort : OddRow q) :
    depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
      bh12SelectedPortTransportedDensity q
        (bh12DecodedMarginalErrorParameter q p hsuccess firstPort) secondPort := by
  unfold depthTwoChildSelectedPortTransportedDensity
  rw [depthTwoChildRun_eq_bh12ActualRun q p hsuccess firstPort]
  rfl

/-- Two physical BH12 levels assembled from fresh parent outputs: the child
run succeeds, has its exact selected-port diagonal resource, and obeys the
twice-applied quadratic error bound. -/
theorem depthTwoChildPhysicalInvariant (q : Nat) (p : ErrorParameter)
    (firstPort secondPort : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∃ hfirst : 0 < rawSuccessMass q p,
      ∃ hsecond : 0 < rawSuccessMass q
          (bh12DecodedMarginalErrorParameter q p hfirst firstPort),
        0 < (depthTwoChildRun q p firstPort).successProbability ∧
          depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
            OneQubit.diagonalAResource
              (bh12DecodedMarginalErrorParameter q
                (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
                hsecond secondPort) ∧
          (bh12DecodedMarginalErrorParameter q
            (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
            hsecond secondPort).rate ≤
              quadraticCoefficient q ^ 3 * p.rate ^ 4 := by
  obtain ⟨hfirst, hfirstActual, _hfirstDensity, hfirstQuadratic,
    _hfirstNonincrease, hfirstSmall, hfirstHalf, hfirstCoefficient⟩ :=
    bh12OneStepPhysicalInvariant q p firstPort hsmall hhalf hquadraticSmall
  obtain ⟨hsecond, hsecondActual, hsecondDensity, hsecondQuadratic,
    _hsecondNonincrease, _hsecondSmall, _hsecondHalf, _hsecondCoefficient⟩ :=
    bh12OneStepPhysicalInvariant q
      (bh12DecodedMarginalErrorParameter q p hfirst firstPort) secondPort
      hfirstSmall hfirstHalf hfirstCoefficient
  have hchildSuccess : 0 < (depthTwoChildRun q p firstPort).successProbability := by
    rw [depthTwoChildRun_eq_bh12ActualRun q p hfirst firstPort]
    exact hsecondActual
  have hchildDensity :
      depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
        OneQubit.diagonalAResource
          (bh12DecodedMarginalErrorParameter q
            (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
            hsecond secondPort) := by
    rw [depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
      q p hfirst firstPort secondPort]
    exact hsecondDensity
  have hfirstRateNonneg :
      0 ≤ (bh12DecodedMarginalErrorParameter q p hfirst firstPort).rate :=
    (bh12DecodedMarginalErrorParameter q p hfirst firstPort).rate_nonneg
  have hquadraticUpperNonneg :
      0 ≤ quadraticCoefficient q * p.rate ^ 2 :=
    mul_nonneg (le_of_lt (quadraticCoefficient_pos q)) (sq_nonneg _)
  have hfirstSquare :
      (bh12DecodedMarginalErrorParameter q p hfirst firstPort).rate ^ 2 ≤
        (quadraticCoefficient q * p.rate ^ 2) ^ 2 :=
    (sq_le_sq₀ hfirstRateNonneg hquadraticUpperNonneg).mpr hfirstQuadratic
  have htwiceQuadratic :
      (bh12DecodedMarginalErrorParameter q
        (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
        hsecond secondPort).rate ≤
          quadraticCoefficient q * (quadraticCoefficient q * p.rate ^ 2) ^ 2 :=
    hsecondQuadratic.trans
      (mul_le_mul_of_nonneg_left hfirstSquare
        (le_of_lt (quadraticCoefficient_pos q)))
  refine ⟨hfirst, hsecond, hchildSuccess, hchildDensity, ?_⟩
  calc
    (bh12DecodedMarginalErrorParameter q
      (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
      hsecond secondPort).rate ≤
        quadraticCoefficient q * (quadraticCoefficient q * p.rate ^ 2) ^ 2 :=
      htwiceQuadratic
    _ = quadraticCoefficient q ^ 3 * p.rate ^ 4 := by ring

/-- A length-`z` physical raw-input address: one BH12 input index at every
level. -/
abbrev depthRawInputPath (q z : Nat) :=
  Fin z → Fin (bh12InputCount q)

/-- A length-`z` selected-logical-port address. -/
abbrev depthOutputPath (q z : Nat) :=
  Fin z → OddRow q

theorem card_depthRawInputPath (q z : Nat) :
    Fintype.card (depthRawInputPath q z) = (bh12InputCount q) ^ z := by
  simp [depthRawInputPath]

theorem card_depthOutputPath (q z : Nat) :
    Fintype.card (depthOutputPath q z) = (bh12OutputCount q) ^ z := by
  simp [depthOutputPath, bh12OutputCount, logicalCount, Nat.mul_comm]

/-- The preceding selected ports of a nonempty output path. -/
def depthOutputPathPrefix (q z : Nat) (path : depthOutputPath q (z + 1)) :
    depthOutputPath q z :=
  fun i => path i.castSucc

/-- The final selected port of a nonempty output path. -/
def depthOutputPathLast (q z : Nat) (path : depthOutputPath q (z + 1)) :
    OddRow q :=
  path (Fin.last z)

/-- A total parameter selector.  The fallback is only a definition-level
totality branch; the physical path theorems below prove and use its positive
success branch from the three explicit admissibility inequalities. -/
noncomputable def bh12TotalNextParameter (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : ErrorParameter :=
  dite (0 < rawSuccessMass q p)
    (fun hsuccess => bh12DecodedMarginalErrorParameter q p hsuccess port)
    (fun _ => p)

theorem bh12TotalNextParameter_of_success (q : Nat) (p : ErrorParameter)
    (port : OddRow q) (hsuccess : 0 < rawSuccessMass q p) :
    bh12TotalNextParameter q p port =
      bh12DecodedMarginalErrorParameter q p hsuccess port := by
  simp [bh12TotalNextParameter, hsuccess]

/-- The recursively derived actual error parameter along a finite selected
physical output path. -/
noncomputable def bh12PathParameter (q : Nat) (p : ErrorParameter) :
    (z : Nat) → depthOutputPath q z → ErrorParameter
  | 0, _ => p
  | z + 1, path =>
      bh12TotalNextParameter q
        (bh12PathParameter q p z (depthOutputPathPrefix q z path))
        (depthOutputPathLast q z path)

@[simp] theorem bh12PathParameter_zero (q : Nat) (p : ErrorParameter)
    (path : depthOutputPath q 0) :
    bh12PathParameter q p 0 path = p :=
  rfl

@[simp] theorem bh12PathParameter_succ (q z : Nat) (p : ErrorParameter)
    (path : depthOutputPath q (z + 1)) :
    bh12PathParameter q p (z + 1) path =
      bh12TotalNextParameter q
        (bh12PathParameter q p z (depthOutputPathPrefix q z path))
        (depthOutputPathLast q z path) :=
  rfl

/-- Every parameter reached by a finite physical selected-port path preserves
the three one-step admissibility inequalities. -/
theorem bh12PathParameter_admissible (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∀ (z : Nat) (path : depthOutputPath q z),
      (bh12InputCount q : ℝ) * (bh12PathParameter q p z path).rate ≤ 1 / 4 ∧
        (bh12PathParameter q p z path).rate ≤ 1 / 2 ∧
        quadraticCoefficient q * (bh12PathParameter q p z path).rate ≤ 1 := by
  intro z
  induction z with
  | zero =>
      intro path
      refine ⟨?_, ?_, hquadraticSmall⟩
      · exact hsmall
      · exact hhalf
  | succ z ih =>
      intro path
      obtain ⟨hpreviousSmall, hpreviousHalf, hpreviousCoefficient⟩ :=
        ih (depthOutputPathPrefix q z path)
      obtain ⟨hsuccess, _hactualSuccess, _hdensity, _hquadratic,
        _hnonincreasing, hnextSmall, hnextHalf, hnextCoefficient⟩ :=
        bh12OneStepPhysicalInvariant q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hpreviousSmall hpreviousHalf
          hpreviousCoefficient
      rw [bh12PathParameter_succ,
        bh12TotalNextParameter_of_success q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hsuccess]
      exact ⟨hnextSmall, hnextHalf, hnextCoefficient⟩

/-- The actual BH12 success mass is positive at every finite physical path
parameter satisfying the initial admissibility inequalities. -/
theorem bh12PathParameter_success (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) :
    0 < rawSuccessMass q (bh12PathParameter q p z path) := by
  obtain ⟨hpathSmall, _hpathHalf, _hpathCoefficient⟩ :=
    bh12PathParameter_admissible q p hsmall hhalf hquadraticSmall z path
  rw [← bh12ActualRun_successProbability]
  exact bh12ActualRun_successProbability_pos_of_small_error q
    (bh12PathParameter q p z path) hpathSmall

/-- The fresh-parent resources used for one next physical path step. -/
noncomputable def bh12PathNextResources (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    ResourceInput (bh12InputCount q) Qubit.QubitSpace :=
  depthTwoChildResources q (bh12PathParameter q p z path) port

/-- Under the initial three inequalities, the literal fresh-parent resource
family at every path step is the standard noisy-resource family at the total
next parameter. -/
theorem bh12PathNextResources_eq_noisyResources (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    bh12PathNextResources q p z path port =
      noisyResources q
        (bh12TotalNextParameter q (bh12PathParameter q p z path) port) := by
  have hsuccess : 0 < rawSuccessMass q (bh12PathParameter q p z path) :=
    bh12PathParameter_success q p hsmall hhalf hquadraticSmall z path
  unfold bh12PathNextResources
  rw [bh12TotalNextParameter_of_success q (bh12PathParameter q p z path)
    port hsuccess]
  exact depthTwoChildResources_eq_noisyResources q
    (bh12PathParameter q p z path) hsuccess port

/-- The actual BH12 run at a recursively derived path parameter. -/
noncomputable def bh12PathRun (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) :=
  bh12ActualRun q (bh12PathParameter q p z path)

/-- The selected physical output density of the actual run at a finite path
parameter. -/
noncomputable def bh12PathSelectedPortTransportedDensity (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
      (bh12PathRun q p z path).acceptedOutput)

/-- The finite-path physical selected output is exactly the diagonal A-basis
resource at its total next parameter. -/
theorem bh12PathSelectedPortTransportedDensity_eq_diagonalAResource
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    bh12PathSelectedPortTransportedDensity q p z path port =
      OneQubit.diagonalAResource
        (bh12TotalNextParameter q (bh12PathParameter q p z path) port) := by
  have hsuccess : 0 < rawSuccessMass q (bh12PathParameter q p z path) :=
    bh12PathParameter_success q p hsmall hhalf hquadraticSmall z path
  change bh12SelectedPortTransportedDensity q (bh12PathParameter q p z path) port = _
  rw [bh12TotalNextParameter_of_success q (bh12PathParameter q p z path)
    port hsuccess]
  exact bh12SelectedPortTransportedDensity_eq_diagonalAResource q
    (bh12PathParameter q p z path) hsuccess port

/-- The recursively iterated quadratic upper envelope for a finite path. -/
def bh12QuadraticEnvelope (q : Nat) (p : ErrorParameter) : Nat → ℝ
  | 0 => p.rate
  | z + 1 => quadraticCoefficient q * (bh12QuadraticEnvelope q p z) ^ 2

theorem bh12QuadraticEnvelope_nonneg (q : Nat) (p : ErrorParameter) :
    ∀ z : Nat, 0 ≤ bh12QuadraticEnvelope q p z := by
  intro z
  induction z with
  | zero => simpa [bh12QuadraticEnvelope] using p.rate_nonneg
  | succ z ih =>
      simp only [bh12QuadraticEnvelope]
      exact mul_nonneg (le_of_lt (quadraticCoefficient_pos q)) (sq_nonneg _)

/-- Every recursively derived physical path parameter is bounded by the
corresponding quadratic envelope. -/
theorem bh12PathParameter_rate_le_quadraticEnvelope (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∀ (z : Nat) (path : depthOutputPath q z),
      (bh12PathParameter q p z path).rate ≤ bh12QuadraticEnvelope q p z := by
  intro z
  induction z with
  | zero =>
      intro path
      simp [bh12QuadraticEnvelope]
  | succ z ih =>
      intro path
      have hpreviousRate :
          (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            bh12QuadraticEnvelope q p z :=
        ih (depthOutputPathPrefix q z path)
      obtain ⟨hpreviousSmall, hpreviousHalf, hpreviousCoefficient⟩ :=
        bh12PathParameter_admissible q p hsmall hhalf hquadraticSmall z
          (depthOutputPathPrefix q z path)
      obtain ⟨hsuccess, _hactualSuccess, _hdensity, hnextQuadratic,
        _hnonincreasing, _hnextSmall, _hnextHalf, _hnextCoefficient⟩ :=
        bh12OneStepPhysicalInvariant q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hpreviousSmall hpreviousHalf
          hpreviousCoefficient
      have hpreviousNonneg :
          0 ≤ (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate :=
        (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate_nonneg
      have henvelopeNonneg : 0 ≤ bh12QuadraticEnvelope q p z :=
        bh12QuadraticEnvelope_nonneg q p z
      have hpreviousSquare :
          (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ^ 2 ≤
            (bh12QuadraticEnvelope q p z) ^ 2 :=
        (sq_le_sq₀ hpreviousNonneg henvelopeNonneg).mpr hpreviousRate
      rw [bh12PathParameter_succ,
        bh12TotalNextParameter_of_success q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hsuccess,
        bh12QuadraticEnvelope]
      exact hnextQuadratic.trans
        (mul_le_mul_of_nonneg_left hpreviousSquare
          (le_of_lt (quadraticCoefficient_pos q)))

/-- The quadratic envelope has an exact finite-depth form after multiplication
by the positive BH12 coefficient. -/
theorem bh12QuadraticEnvelope_closedForm (q : Nat) (p : ErrorParameter)
    (z : Nat) :
    quadraticCoefficient q * bh12QuadraticEnvelope q p z =
      (quadraticCoefficient q * p.rate) ^ (2 ^ z) := by
  induction z with
  | zero => simp [bh12QuadraticEnvelope]
  | succ z ih =>
      calc
        quadraticCoefficient q * bh12QuadraticEnvelope q p (z + 1) =
            (quadraticCoefficient q * bh12QuadraticEnvelope q p z) ^ 2 := by
          simp only [bh12QuadraticEnvelope]
          ring
        _ = ((quadraticCoefficient q * p.rate) ^ (2 ^ z)) ^ 2 := by rw [ih]
        _ = (quadraticCoefficient q * p.rate) ^ (2 ^ z * 2) := by
          rw [← pow_mul]
        _ = (quadraticCoefficient q * p.rate) ^ (2 ^ (z + 1)) := by
          rw [pow_succ]

/-- A positive initial error rate makes every finite quadratic envelope
positive. -/
theorem bh12QuadraticEnvelope_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) :
    ∀ z : Nat, 0 < bh12QuadraticEnvelope q p z := by
  intro z
  induction z with
  | zero => simpa [bh12QuadraticEnvelope] using hp
  | succ z ih =>
      simp only [bh12QuadraticEnvelope]
      exact mul_pos (quadraticCoefficient_pos q) (pow_pos ih 2)

/-- The BH12 quadratic coefficient is at least one. -/
theorem one_le_quadraticCoefficient (q : Nat) : 1 ≤ quadraticCoefficient q := by
  have hcount : (1 : ℝ) ≤ ((1 + 6 * q : Nat) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : 1 + 6 * q ≠ 0))
  unfold quadraticCoefficient
  nlinarith

/-- Under the strong source-domain coefficient condition, the scaled envelope
stays at most one half at every finite depth. -/
theorem bh12QuadraticEnvelope_scaled_le_half (q : Nat) (p : ErrorParameter)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    ∀ z : Nat,
      quadraticCoefficient q * bh12QuadraticEnvelope q p z ≤ 1 / 2 := by
  intro z
  induction z with
  | zero => simpa [bh12QuadraticEnvelope] using hstrong
  | succ z ih =>
      have hscaledNonneg :
          0 ≤ quadraticCoefficient q * bh12QuadraticEnvelope q p z :=
        mul_nonneg (le_of_lt (quadraticCoefficient_pos q))
          (bh12QuadraticEnvelope_nonneg q p z)
      calc
        quadraticCoefficient q * bh12QuadraticEnvelope q p (z + 1) =
            (quadraticCoefficient q * bh12QuadraticEnvelope q p z) ^ 2 := by
          simp only [bh12QuadraticEnvelope]
          ring
        _ ≤ ((1 : ℝ) / 2) ^ 2 :=
          (sq_le_sq₀ hscaledNonneg (by norm_num)).mpr ih
        _ ≤ 1 / 2 := by norm_num

/-- The explicit positive/small-rate assumptions make each finite quadratic
envelope a genuine number strictly between zero and one. -/
theorem bh12QuadraticEnvelope_lt_one (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    ∀ z : Nat, bh12QuadraticEnvelope q p z < 1 := by
  intro z
  induction z with
  | zero =>
      simpa [bh12QuadraticEnvelope] using
        lt_of_le_of_lt hhalf (by norm_num : (1 : ℝ) / 2 < 1)
  | succ z ih =>
      have hscaled :
          quadraticCoefficient q * bh12QuadraticEnvelope q p z ≤ 1 / 2 :=
        bh12QuadraticEnvelope_scaled_le_half q p hstrong z
      calc
        bh12QuadraticEnvelope q p (z + 1) =
            (quadraticCoefficient q * bh12QuadraticEnvelope q p z) *
              bh12QuadraticEnvelope q p z := by
          simp only [bh12QuadraticEnvelope]
          ring
        _ ≤ (1 / 2) * bh12QuadraticEnvelope q p z :=
          mul_le_mul_of_nonneg_right hscaled
            (bh12QuadraticEnvelope_pos q p hp z).le
        _ < (1 / 2) * 1 :=
          mul_lt_mul_of_pos_left ih (by norm_num : (0 : ℝ) < 1 / 2)
        _ < 1 := by norm_num

/-- The exact positive logarithmic growth base of the finite quadratic
envelope. -/
noncomputable def bh12QuadraticEnvelopeLogGrowthBase (q : Nat)
    (p : ErrorParameter) : ℝ :=
  -Real.log (quadraticCoefficient q * p.rate)

/-- The strong input domain makes the quadratic-envelope logarithmic base
strictly positive. -/
theorem bh12QuadraticEnvelopeLogGrowthBase_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    0 < bh12QuadraticEnvelopeLogGrowthBase q p := by
  unfold bh12QuadraticEnvelopeLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (quadraticCoefficient_pos q) hp
  · exact hstrong.trans_lt (by norm_num)

/-- The compiled finite closed form gives the source-faithful logarithmic
lower bound for every finite quadratic-envelope depth. -/
theorem bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log
    (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) (z : Nat) :
    (2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p ≤
      Real.log (1 / bh12QuadraticEnvelope q p z) := by
  have hcoefficientPos : 0 < quadraticCoefficient q := quadraticCoefficient_pos q
  have hbasePos : 0 < quadraticCoefficient q * p.rate :=
    mul_pos hcoefficientPos hp
  have henvelopePos : 0 < bh12QuadraticEnvelope q p z :=
    bh12QuadraticEnvelope_pos q p hp z
  have hpowPos : 0 < (quadraticCoefficient q * p.rate) ^ (2 ^ z) :=
    pow_pos hbasePos _
  have hreciprocal :
      1 / bh12QuadraticEnvelope q p z =
        quadraticCoefficient q / (quadraticCoefficient q * p.rate) ^ (2 ^ z) := by
    field_simp [ne_of_gt henvelopePos, ne_of_gt hpowPos]
    simpa [mul_comm] using (bh12QuadraticEnvelope_closedForm q p z).symm
  have hlogForm :
      Real.log (1 / bh12QuadraticEnvelope q p z) =
        Real.log (quadraticCoefficient q) +
          (2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p := by
    rw [hreciprocal, Real.log_div (ne_of_gt hcoefficientPos) (ne_of_gt hpowPos),
      Real.log_pow]
    push_cast
    unfold bh12QuadraticEnvelopeLogGrowthBase
    ring
  have hcoefficientLogNonneg : 0 ≤ Real.log (quadraticCoefficient q) :=
    Real.log_nonneg (one_le_quadraticCoefficient q)
  have _henvelopeLtOne : bh12QuadraticEnvelope q p z < 1 :=
    bh12QuadraticEnvelope_lt_one q p hp hhalf hstrong z
  rw [hlogForm]
  linarith

/-- The exact finite-depth coefficient that converts the quadratic-envelope
logarithm into the typed BH12 output-cost bound. -/
noncomputable def bh12QuadraticEnvelopeCostCoefficient (q : Nat)
    (p : ErrorParameter) : ℝ :=
  2 / Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
    (bh12BlockExponent q)

/-- On the explicit positive/small-rate domain, the exact finite-depth cost
coefficient is positive (and hence nonnegative). -/
theorem bh12QuadraticEnvelopeCostCoefficient_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    0 < bh12QuadraticEnvelopeCostCoefficient q p := by
  unfold bh12QuadraticEnvelopeCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (bh12QuadraticEnvelopeLogGrowthBase_pos q p hp hstrong)
      (bh12BlockExponent q))

/-- Under the strict BH12 input-domain condition, the finite quadratic
envelope reaches every positive real target at some finite depth. -/
theorem bh12QuadraticEnvelope_exists_le (q : Nat) (p : ErrorParameter)
    (hstrict : quadraticCoefficient q * p.rate < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, bh12QuadraticEnvelope q p z ≤ epsilon := by
  have hcoefficientPos : 0 < quadraticCoefficient q := quadraticCoefficient_pos q
  have nat_le_two_pow : ∀ n : Nat, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
          _ ≤ 2 ^ n + 2 ^ n :=
            Nat.add_le_add_left (Nat.one_le_pow n 2 (by norm_num)) _
          _ = 2 ^ (n + 1) := by
            rw [pow_succ]
            ring
  obtain ⟨n, hpower⟩ := exists_pow_lt_of_lt_one
    (x := quadraticCoefficient q * epsilon)
    (y := quadraticCoefficient q * p.rate)
    (mul_pos hcoefficientPos hepsilon) hstrict
  have hnat : n ≤ 2 ^ n := nat_le_two_pow n
  have hbaseNonneg : 0 ≤ quadraticCoefficient q * p.rate :=
    mul_nonneg hcoefficientPos.le p.rate_nonneg
  refine ⟨n, ?_⟩
  have hscaledPower :
      (quadraticCoefficient q * p.rate) ^ (2 ^ n) <
        quadraticCoefficient q * epsilon :=
    (pow_le_pow_of_le_one hbaseNonneg (le_of_lt hstrict) hnat).trans_lt hpower
  have hscaledEnvelope :
      quadraticCoefficient q * bh12QuadraticEnvelope q p n <
        quadraticCoefficient q * epsilon := by
    rw [bh12QuadraticEnvelope_closedForm]
    exact hscaledPower
  exact (lt_of_mul_lt_mul_left hscaledEnvelope hcoefficientPos.le).le

/-- A strict initial BH12 coefficient condition gives one finite depth that
uniformly bounds the recursively derived rate along every selected-port path. -/
theorem bh12PathParameter_exists_depth_rate_le (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (hstrict : quadraticCoefficient q * p.rate < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      (bh12PathParameter q p z path).rate ≤ epsilon := by
  obtain ⟨z, henvelope⟩ :=
    bh12QuadraticEnvelope_exists_le q p hstrict epsilon hepsilon
  refine ⟨z, ?_⟩
  intro path
  exact (bh12PathParameter_rate_le_quadraticEnvelope q p hsmall hhalf
    hquadraticSmall z path).trans henvelope

/-- At one finite uniform target depth, every physical path has positive
actual success, exact transported selected-port density, and the requested
rate bound. -/
theorem bh12PathUniformPhysicalTarget (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (hstrict : quadraticCoefficient q * p.rate < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
        0 < (bh12PathRun q p z path).successProbability ∧
          (∀ port : OddRow q,
            bh12PathSelectedPortTransportedDensity q p z path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter q (bh12PathParameter q p z path) port)) ∧
            (bh12PathParameter q p z path).rate ≤ epsilon := by
  obtain ⟨z, hrate⟩ := bh12PathParameter_exists_depth_rate_le q p hsmall hhalf
    hquadraticSmall hstrict epsilon hepsilon
  refine ⟨z, ?_⟩
  intro path
  have hsuccess : 0 < rawSuccessMass q (bh12PathParameter q p z path) :=
    bh12PathParameter_success q p hsmall hhalf hquadraticSmall z path
  refine ⟨hsuccess, ?_, ?_, hrate path⟩
  · change 0 < (bh12ActualRun q (bh12PathParameter q p z path)).successProbability
    rw [bh12ActualRun_successProbability]
    exact hsuccess
  · intro port
    exact bh12PathSelectedPortTransportedDensity_eq_diagonalAResource q p
      hsmall hhalf hquadraticSmall z path port

/-- The physical finite-error distribution, with every logical port flagged
as accepted precisely when the actual BH12 checks accept that error word. -/
noncomputable def bh12PhysicalFlaggedBatch (q : Nat) (p : ErrorParameter) :
    DependentBatch.FiniteFlaggedBatch (OddRow q) (PhysicalError q) where
  weight := errorWordProbability p
  weight_nonneg := errorWordProbability_nonneg p
  total_weight := sum_errorWordProbability (Index := Column q) p
  accepted := fun error _ => decide (Accepts error)

/-- Every literal physical-error outcome has a nonnegative batch weight. -/
theorem bh12PhysicalFlaggedBatch_weight_nonneg (q : Nat) (p : ErrorParameter)
    (error : PhysicalError q) :
    0 ≤ (bh12PhysicalFlaggedBatch q p).weight error :=
  (bh12PhysicalFlaggedBatch q p).weight_nonneg error

/-- The physical-error weights normalize over the finite BH12 error space. -/
theorem bh12PhysicalFlaggedBatch_total_weight (q : Nat) (p : ErrorParameter) :
    ∑ error : PhysicalError q, (bh12PhysicalFlaggedBatch q p).weight error = 1 :=
  (bh12PhysicalFlaggedBatch q p).total_weight

/-- An accepted BH12 error word flags all actual logical ports; a rejected
word flags none. -/
theorem bh12PhysicalFlaggedBatch_acceptedPortCount (q : Nat) (p : ErrorParameter)
    (error : PhysicalError q) :
    DependentBatch.acceptedPortCount (bh12PhysicalFlaggedBatch q p) error =
      if Accepts error then bh12OutputCount q else 0 := by
  classical
  unfold DependentBatch.acceptedPortCount
  by_cases haccept : Accepts error
  · simp [bh12PhysicalFlaggedBatch, haccept, bh12OutputCount, logicalCount,
      Nat.mul_comm]
  · simp [bh12PhysicalFlaggedBatch, haccept]

/-- The literal one-block accepted-port expectation is the actual output
count times the actual BH12 raw success mass. -/
theorem bh12PhysicalExpectedAcceptedPorts (q : Nat) (p : ErrorParameter) :
    DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q p) =
      (bh12OutputCount q : ℝ) * rawSuccessMass q p := by
  classical
  unfold DependentBatch.expectedAcceptedPorts
  simp_rw [bh12PhysicalFlaggedBatch_acceptedPortCount]
  rw [rawSuccessMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccept : Accepts error <;>
    simp [bh12PhysicalFlaggedBatch, haccept] <;> ring

/-- A finite pool of fresh blocks is represented only as a finite indexed
family of identical one-block distributions; no independence is asserted. -/
noncomputable def bh12PhysicalFlaggedPool (q : Nat) (p : ErrorParameter)
    (count : Nat) :
    Fin count → DependentBatch.FiniteFlaggedBatch (OddRow q) (PhysicalError q) :=
  fun _ => bh12PhysicalFlaggedBatch q p

/-- Finite linearity gives the pooled expected accepted-port count. -/
theorem bh12PhysicalPooledExpectedAcceptedPorts (q : Nat) (p : ErrorParameter)
    (count : Nat) :
    DependentBatch.pooledExpectedAcceptedPorts count
        (bh12PhysicalFlaggedPool q p count) =
      (count : ℝ) * (bh12OutputCount q : ℝ) * rawSuccessMass q p := by
  unfold DependentBatch.pooledExpectedAcceptedPorts bh12PhysicalFlaggedPool
  simp_rw [bh12PhysicalExpectedAcceptedPorts]
  simp [mul_assoc]

/-- Small physical input error yields the pooled three-quarters lower bound
by finite linearity alone. -/
theorem bh12PhysicalPooledExpectedAcceptedPorts_threeQuarters_le
    (q : Nat) (p : ErrorParameter) (count : Nat)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    (count : ℝ) * (bh12OutputCount q : ℝ) * ((3 : ℝ) / 4) ≤
      DependentBatch.pooledExpectedAcceptedPorts count
        (bh12PhysicalFlaggedPool q p count) := by
  rw [bh12PhysicalPooledExpectedAcceptedPorts,
    ← bh12ActualRun_successProbability q p]
  have hfactor : 0 ≤ (count : ℝ) * (bh12OutputCount q : ℝ) := by
    positivity
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (bh12ActualRun_three_quarters_le_successProbability q p hsmall) hfactor

/-- A nonempty finite pool has positive expected accepted-port yield whenever
the actual BH12 block has at least one logical port. -/
theorem bh12PhysicalPooledExpectedAcceptedPorts_pos_of_nonzero
    (q : Nat) (p : ErrorParameter) (count : Nat)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hcount : count ≠ 0) (hports : 0 < bh12OutputCount q) :
    0 < DependentBatch.pooledExpectedAcceptedPorts count
      (bh12PhysicalFlaggedPool q p count) := by
  rw [bh12PhysicalPooledExpectedAcceptedPorts]
  have hsuccess : 0 < rawSuccessMass q p := by
    rw [← bh12ActualRun_successProbability]
    exact lt_of_lt_of_le (by norm_num)
      (bh12ActualRun_three_quarters_le_successProbability q p hsmall)
  have hcountReal : 0 < (count : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcount
  have hportsReal : 0 < (bh12OutputCount q : ℝ) := by
    exact_mod_cast hports
  exact mul_pos (mul_pos hcountReal hportsReal) hsuccess

/-- The smallest one-level #458 family: one actual #755 BH12 protocol for
each selected logical port, with its enumerator-derived quadratic target. -/
noncomputable def bh12OneLevelProtocolFamily (q : Nat) (p : ErrorParameter)
    (hhalf : p.rate ≤ 1 / 2) :
    DistillationProtocolFamily Qubit.QubitSpace (PhysicalRegister q)
      (LogicalRegister q) (OddRow q) where
  targetError := fun _ => quadraticCoefficient q * p.rate ^ 2
  protocol := fun port =>
    bh12MagicStateDistillationProtocol q p port
      (rawSuccessMass_pos_of_rate_le_half q p hhalf)
  outputResourceCount := fun _ => bh12OutputCount q
  outputResourceCount_pos := by
    intro port
    have hq : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hqzero
      subst q
      exact Fin.elim0 port.1
    change 0 < 2 * q
    omega
  successfulOutputError_le_targetError := by
    intro port
    exact bh12MagicStateDistillationProtocol_quadratic q p port hhalf

/-- The target is exactly the actual BH12 quadratic error bound. -/
theorem bh12OneLevelProtocolFamily_targetError (q : Nat) (p : ErrorParameter)
    (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).targetError port =
      quadraticCoefficient q * p.rate ^ 2 :=
  rfl

/-- At every selected-port index, the family exposes #755's actual BH12
magic-state protocol. -/
theorem bh12OneLevelProtocolFamily_protocol (q : Nat) (p : ErrorParameter)
    (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).protocol port =
      bh12MagicStateDistillationProtocol q p port
        (rawSuccessMass_pos_of_rate_le_half q p hhalf) :=
  rfl

/-- The family protocol's run is the literal resource-decoded BH12 run. -/
theorem bh12OneLevelProtocolFamily_run (q : Nat) (p : ErrorParameter)
    (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).run =
      bh12ActualRun q p :=
  rfl

/-- The #458 input count is the actual physical BH12 resource count. -/
theorem bh12OneLevelProtocolFamily_inputResourceCount (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).inputResourceCount port =
      bh12InputCount q :=
  rfl

/-- The #458 output count is the actual number of BH12 logical ports. -/
theorem bh12OneLevelProtocolFamily_outputResourceCount (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).outputResourceCount port =
      bh12OutputCount q :=
  rfl

/-- The reported family output count is the cardinality of the actual logical
register's BH12 port index. -/
theorem bh12OneLevelProtocolFamily_outputResourceCount_eq_card_oddRow
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).outputResourceCount port =
      Fintype.card (OddRow q) := by
  rw [bh12OneLevelProtocolFamily_outputResourceCount]
  simpa [bh12OutputCount] using (card_oddRow q).symm

/-- The family retains the actual finite BH12 raw success mass. -/
theorem bh12OneLevelProtocolFamily_successProbability (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).run.successProbability =
      rawSuccessMass q p := by
  rw [bh12OneLevelProtocolFamily_run]
  exact bh12ActualRun_successProbability q p

/-- The selected protocol's successful output error obeys its exact family
target through #755's physical quadratic theorem. -/
theorem bh12OneLevelProtocolFamily_successfulOutputError_le_targetError
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).successfulOutputError ≤
      quadraticCoefficient q * p.rate ^ 2 := by
  change (bh12MagicStateDistillationProtocol q p port
    (rawSuccessMass_pos_of_rate_le_half q p hhalf)).successfulOutputError ≤ _
  exact bh12MagicStateDistillationProtocol_quadratic q p port hhalf

/-- The #458 successful-output cost has the literal BH12 denominator: actual
logical-port count times actual raw success mass. -/
theorem bh12OneLevelProtocolFamily_successfulOutputCost (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
      (bh12InputCount q : ℝ) /
        ((bh12OutputCount q : ℝ) * rawSuccessMass q p) := by
  unfold DistillationProtocolFamily.successfulOutputCost
  rw [bh12OneLevelProtocolFamily_inputResourceCount,
    bh12OneLevelProtocolFamily_outputResourceCount,
    bh12OneLevelProtocolFamily_successProbability]

/-- The same one-level cost is input resources divided by the literal flagged
batch expected accepted-port yield. -/
theorem bh12OneLevelProtocolFamily_successfulOutputCost_eq_expectedAcceptedPorts
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
      (bh12InputCount q : ℝ) /
        DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q p) := by
  rw [bh12OneLevelProtocolFamily_successfulOutputCost,
    bh12PhysicalExpectedAcceptedPorts]

/-- Under the literal one-level small-error premise, the actual BH12 family
cost is at most four-thirds of its actual input-to-logical-output ratio. -/
theorem bh12OneLevelProtocolFamily_successfulOutputCost_le_four_thirds
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port ≤
      ((4 : ℝ) / 3) * ((bh12InputCount q : ℝ) / bh12OutputCount q) := by
  have hsuccess : (3 : ℝ) / 4 ≤ rawSuccessMass q p := by
    rw [← bh12ActualRun_successProbability]
    exact bh12ActualRun_three_quarters_le_successProbability q p hsmall
  have hratioNonneg : 0 ≤ (bh12InputCount q : ℝ) / bh12OutputCount q := by
    positivity
  have hdiv :
      (bh12InputCount q : ℝ) / bh12OutputCount q / rawSuccessMass q p ≤
        ((bh12InputCount q : ℝ) / bh12OutputCount q) / ((3 : ℝ) / 4) :=
    div_le_div_of_nonneg_left hratioNonneg (by norm_num) hsuccess
  calc
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
        (bh12InputCount q : ℝ) /
          ((bh12OutputCount q : ℝ) * rawSuccessMass q p) :=
      bh12OneLevelProtocolFamily_successfulOutputCost q p hhalf port
    _ = (bh12InputCount q : ℝ) / bh12OutputCount q / rawSuccessMass q p := by
      rw [div_div]
    _ ≤ ((bh12InputCount q : ℝ) / bh12OutputCount q) / ((3 : ℝ) / 4) := hdiv
    _ = ((4 : ℝ) / 3) * ((bh12InputCount q : ℝ) / bh12OutputCount q) := by
      ring

/-- Restrict a finite physical output path to the stages strictly before one
chosen stage.  This is an address restriction only. -/
def bh12PathStage (q z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    depthOutputPath q stage.1 :=
  fun i => path ⟨i.1, lt_trans i.2 stage.2⟩

/-- Under the stronger initial coefficient premise, every finite selected
physical path has a rate which decreases by at least one factor of two per
actual BH12 stage. -/
theorem bh12PathParameter_rate_le_geometric (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    ∀ (z : Nat) (path : depthOutputPath q z),
      (bh12PathParameter q p z path).rate ≤ p.rate / (2 : ℝ) ^ z := by
  have hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1 :=
    hstrong.trans (by norm_num)
  intro z
  induction z with
  | zero =>
      intro path
      simp
  | succ z ih =>
      intro path
      have hpreviousRate :
          (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            p.rate / (2 : ℝ) ^ z :=
        ih (depthOutputPathPrefix q z path)
      have hpreviousLeInitial :
          (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            p.rate :=
        hpreviousRate.trans (div_le_self p.rate_nonneg
          (one_le_pow₀ (by norm_num)))
      obtain ⟨hpreviousSmall, hpreviousHalf, hpreviousCoefficient⟩ :=
        bh12PathParameter_admissible q p hsmall hhalf hquadraticSmall z
          (depthOutputPathPrefix q z path)
      obtain ⟨hsuccess, _hactualSuccess, _hdensity, hnextQuadratic,
        _hnonincreasing, _hnextSmall, _hnextHalf, _hnextCoefficient⟩ :=
        bh12OneStepPhysicalInvariant q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hpreviousSmall hpreviousHalf
          hpreviousCoefficient
      have hpreviousCoefficientHalf :
          quadraticCoefficient q *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            1 / 2 :=
        (mul_le_mul_of_nonneg_left hpreviousLeInitial
          (le_of_lt (quadraticCoefficient_pos q))).trans hstrong
      rw [bh12PathParameter_succ,
        bh12TotalNextParameter_of_success q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hsuccess]
      calc
        (bh12DecodedMarginalErrorParameter q
            (bh12PathParameter q p z (depthOutputPathPrefix q z path)) hsuccess
            (depthOutputPathLast q z path)).rate ≤
            quadraticCoefficient q *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ^ 2 :=
          hnextQuadratic
        _ = (quadraticCoefficient q *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate) *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate := by
          ring
        _ ≤ (1 / 2) *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate :=
          mul_le_mul_of_nonneg_right hpreviousCoefficientHalf
            (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate_nonneg
        _ ≤ (1 / 2) * (p.rate / (2 : ℝ) ^ z) :=
          mul_le_mul_of_nonneg_left hpreviousRate (by norm_num)
        _ = p.rate / (2 : ℝ) ^ (z + 1) := by
          rw [pow_succ]
          field_simp [pow_ne_zero]

/-- The actual one-level success mass at one stage of a finite selected path.
It is an accounting factor for separately pooled fresh levels, not a claim
about a joint event across stages. -/
noncomputable def bh12PathYieldFactor (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) (stage : Fin z) : ℝ :=
  rawSuccessMass q (bh12PathParameter q p stage.1
    (bh12PathStage q z path stage))

/-- A path yield factor is the actual BH12 run success probability at its
stage parameter. -/
theorem bh12PathYieldFactor_eq_actualSuccess (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    bh12PathYieldFactor q p z path stage =
      (bh12PathRun q p stage.1
        (bh12PathStage q z path stage)).successProbability := by
  change rawSuccessMass q (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage)) =
    (bh12ActualRun q (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage))).successProbability
  exact (bh12ActualRun_successProbability q
    (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))).symm

/-- The same factor is the success probability retained by the corresponding
one-level selected-port family. -/
theorem bh12PathYieldFactor_eq_oneLevelFamilySuccess (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (stage : Fin z)
    (hhalf : (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage)).rate ≤ 1 / 2) :
    bh12PathYieldFactor q p z path stage =
      ((bh12OneLevelProtocolFamily q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)) hhalf).protocol
        (path stage)).run.successProbability := by
  unfold bh12PathYieldFactor
  symm
  exact bh12OneLevelProtocolFamily_successProbability q
    (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)) hhalf
    (path stage)

/-- The actual one-level flagged-batch expected yield, normalized by its
literal number of output ports, is the same path accounting factor. -/
theorem bh12PathYieldFactor_eq_flaggedYieldFraction (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    bh12PathYieldFactor q p z path stage =
      DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))) /
        (bh12OutputCount q : ℝ) := by
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hqzero
    subst q
    exact Fin.elim0 (path stage).1
  have hkNat : 0 < bh12OutputCount q := by
    change 0 < 2 * q
    omega
  have hk : (bh12OutputCount q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hkNat)
  rw [bh12PhysicalExpectedAcceptedPorts]
  unfold bh12PathYieldFactor
  apply (eq_div_iff hk).2
  ring

/-- The finite-path stage factor has the uniform lower bound obtained from
the actual all-zero-word success estimate and the geometric path-rate bound. -/
theorem bh12PathYieldFactor_lower (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    1 - 1 / (4 * (2 : ℝ) ^ stage.1) ≤
      bh12PathYieldFactor q p z path stage := by
  have hrate :
      (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate ≤
        p.rate / (2 : ℝ) ^ stage.1 :=
    bh12PathParameter_rate_le_geometric q p hsmall hhalf hstrong stage.1
      (bh12PathStage q z path stage)
  have hinput :
      (bh12InputCount q : ℝ) *
          (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate ≤
        1 / (4 * (2 : ℝ) ^ stage.1) := by
    calc
      (bh12InputCount q : ℝ) *
          (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate ≤
          (bh12InputCount q : ℝ) * (p.rate / (2 : ℝ) ^ stage.1) :=
        mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = ((bh12InputCount q : ℝ) * p.rate) / (2 : ℝ) ^ stage.1 := by
        ring
      _ ≤ (1 / 4) / (2 : ℝ) ^ stage.1 :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = 1 / (4 * (2 : ℝ) ^ stage.1) := by
        field_simp [pow_ne_zero]
  unfold bh12PathYieldFactor
  calc
    1 - 1 / (4 * (2 : ℝ) ^ stage.1) ≤
        1 - (bh12InputCount q : ℝ) *
          (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate := by
      linarith
    _ ≤ rawSuccessMass q (bh12PathParameter q p stage.1
          (bh12PathStage q z path stage)) :=
      rawSuccessMass_one_sub_inputCount_rate_le q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))

/-- A finite product of factors in `[0, 1]` is bounded below by one minus the
sum of their losses. -/
theorem bh12FiniteOneSubSum_le_product {ι : Type*} (s : Finset ι)
    (loss : ι → ℝ) (hlossNonneg : ∀ i ∈ s, 0 ≤ loss i)
    (hlossLeOne : ∀ i ∈ s, loss i ≤ 1) :
    1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hsumNonneg : 0 ≤ ∑ i ∈ s, loss i :=
        Finset.sum_nonneg fun i hi =>
          hlossNonneg i (Finset.mem_insert_of_mem hi)
      have hrest :
          1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) :=
        ih (fun i hi => hlossNonneg i (Finset.mem_insert_of_mem hi))
          (fun i hi => hlossLeOne i (Finset.mem_insert_of_mem hi))
      calc
        1 - (loss a + ∑ i ∈ s, loss i) ≤
            (1 - loss a) * (1 - ∑ i ∈ s, loss i) := by
          nlinarith [hlossNonneg a (Finset.mem_insert_self a s)]
        _ ≤ (1 - loss a) * ∏ i ∈ s, (1 - loss i) :=
          mul_le_mul_of_nonneg_left hrest (by
            linarith [hlossLeOne a (Finset.mem_insert_self a s)])

/-- The sum of the finite geometric loss schedule is at most one half. -/
theorem bh12GeometricLossSum_le_half (z : Nat) :
    (∑ stage : Fin z, 1 / (4 * (2 : ℝ) ^ stage.1)) ≤ 1 / 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ i ∈ Finset.range z,
        if h : i < z then 1 / (4 * (2 : ℝ) ^ i) else 0) =
        (∑ i ∈ Finset.range z, 1 / (4 * (2 : ℝ) ^ i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    _ =
        (1 / 4) * ∑ i ∈ Finset.range z, (1 / (2 : ℝ)) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [div_pow, pow_ne_zero]
      rw [← mul_pow]
      norm_num
    _ ≤ (1 / 4) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le z) (by norm_num)
    _ = 1 / 2 := by norm_num

/-- The finite product of separately proved actual one-level yield factors
along a selected path.  It is an accounting product, not a joint-event
probability. -/
noncomputable def bh12PathYieldFactorProduct (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) : ℝ :=
  ∏ stage : Fin z, bh12PathYieldFactor q p z path stage

/-- The finite accounting product of actual fresh-level yield factors is
uniformly at least one half. -/
theorem bh12PathYieldFactorProduct_half_le (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    (1 : ℝ) / 2 ≤ bh12PathYieldFactorProduct q p z path := by
  let loss : Fin z → ℝ := fun stage => 1 / (4 * (2 : ℝ) ^ stage.1)
  have hlossNonneg (stage : Fin z) : 0 ≤ loss stage := by
    dsimp [loss]
    positivity
  have hlossLeOne (stage : Fin z) : loss stage ≤ 1 := by
    have hpow : 1 ≤ (2 : ℝ) ^ stage.1 := one_le_pow₀ (by norm_num)
    have hdenomPos : 0 < 4 * (2 : ℝ) ^ stage.1 := by positivity
    dsimp [loss]
    apply (div_le_iff₀ hdenomPos).2
    nlinarith
  have hproductLower :
      1 - ∑ stage : Fin z, loss stage ≤
        ∏ stage : Fin z, bh12PathYieldFactor q p z path stage := by
    calc
      1 - ∑ stage : Fin z, loss stage ≤ ∏ stage : Fin z, (1 - loss stage) := by
        simpa using (bh12FiniteOneSubSum_le_product Finset.univ loss
          (fun stage _ => hlossNonneg stage)
          (fun stage _ => hlossLeOne stage))
      _ ≤ ∏ stage : Fin z, bh12PathYieldFactor q p z path stage := by
        refine Finset.prod_le_prod ?_ ?_
        · intro stage _
          linarith [hlossLeOne stage]
        · intro stage _
          dsimp [loss]
          exact bh12PathYieldFactor_lower q p hsmall hhalf hstrong z path stage
  have hsum : ∑ stage : Fin z, loss stage ≤ 1 / 2 := by
    simpa [loss] using bh12GeometricLossSum_le_half z
  unfold bh12PathYieldFactorProduct
  linarith

/-- The preceding uniform lower bound makes every finite actual accounting
product strictly positive. -/
theorem bh12PathYieldFactorProduct_pos (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    0 < bh12PathYieldFactorProduct q p z path := by
  exact lt_of_lt_of_le (by norm_num)
    (bh12PathYieldFactorProduct_half_le q p hsmall hhalf hstrong z path)

/-- The typed finite raw-input slot count along a BH12 path is exactly the
literal one-block input count raised to the path depth. -/
theorem bh12PathTypedInputSlot_card (q z : Nat) :
    Fintype.card (depthRawInputPath q z) = (bh12InputCount q) ^ z :=
  card_depthRawInputPath q z

/-- The typed finite logical-output slot count along a BH12 path is exactly
the literal one-block output count raised to the path depth. -/
theorem bh12PathTypedOutputSlot_card (q z : Nat) :
    Fintype.card (depthOutputPath q z) = (bh12OutputCount q) ^ z :=
  card_depthOutputPath q z

/-- Package the separately proved finite-path accounting yield as an explicit
nonnegative factor for the source-neutral typed slot adapter. -/
noncomputable def bh12PathTypedYieldFactor (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) : NNReal :=
  ⟨bh12PathYieldFactorProduct q p z path,
    (bh12PathYieldFactorProduct_pos q p hsmall hhalf hstrong z path).le⟩

/-- Successful-output cost for the actual finite BH12 input and output path
slot types, divided by the deterministic accounting yield product. -/
noncomputable def bh12PathTypedSuccessfulOutputCost (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (depthRawInputPath q z)
    (depthOutputPath q z)
    (bh12PathTypedYieldFactor q p hsmall hhalf hstrong z path)

/-- The actual typed output-slot count times the finite BH12 accounting yield
is positive for every supplied path. -/
theorem bh12PathTypedSuccessfulOutputCost_denominator_pos (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    0 < (Fintype.card (depthOutputPath q z) : ℝ) *
      bh12PathYieldFactorProduct q p z path := by
  have hslots : 0 < Fintype.card (depthOutputPath q z) :=
    Fintype.card_pos_iff.mpr ⟨path⟩
  exact mul_pos (by exact_mod_cast hslots)
    (bh12PathYieldFactorProduct_pos q p hsmall hhalf hstrong z path)

/-- The BH12 typed finite-slot cost has the exact count-derived form. -/
theorem bh12PathTypedSuccessfulOutputCost_eq (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path =
      ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z /
        bh12PathYieldFactorProduct q p z path := by
  unfold bh12PathTypedSuccessfulOutputCost
  unfold DependentBatch.typedSuccessfulOutputCost
  unfold DependentBatch.typedInputOutputRatio
  unfold bh12PathTypedYieldFactor
  rw [bh12PathTypedInputSlot_card, bh12PathTypedOutputSlot_card]
  simp only [Nat.cast_pow]
  rw [div_pow]
  rfl

/-- The uniformly positive finite accounting yield bounds the typed BH12
cost by twice its literal finite input-output ratio. -/
theorem bh12PathTypedSuccessfulOutputCost_le_two (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      2 * ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := by
  rw [bh12PathTypedSuccessfulOutputCost_eq]
  have hratioNonneg : 0 ≤ ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  have hyieldHalf : (1 : ℝ) / 2 ≤ bh12PathYieldFactorProduct q p z path :=
    bh12PathYieldFactorProduct_half_le q p hsmall hhalf hstrong z path
  calc
    ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z /
        bh12PathYieldFactorProduct q p z path ≤
        ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z / ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyieldHalf
    _ = 2 * ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := by ring

/-- The finite typed physical cost bound can be stated exactly with the
fixed-block base-two exponent, without introducing a target-error or
asymptotic overhead layer. -/
theorem bh12PathTypedSuccessfulOutputCost_le_two_rpow (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hq : 0 < q) (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) := by
  rw [bh12BlockRatio_rpow_two_pow_eq_pow hq z]
  exact bh12PathTypedSuccessfulOutputCost_le_two q p hsmall hhalf hstrong z path

/-- The actual finite typed BH12 cost is bounded by the real-rpow of the
compiled finite quadratic-envelope logarithm, with no target-family or
asymptotic packaging. -/
theorem bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      bh12QuadraticEnvelopeCostCoefficient q p *
        Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) := by
  have hbasePos : 0 < bh12QuadraticEnvelopeLogGrowthBase q p :=
    bh12QuadraticEnvelopeLogGrowthBase_pos q p hp hstrong
  have hexponentPos : 0 < bh12BlockExponent q := bh12BlockExponent_pos hq
  have hlog :
      (2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p ≤
        Real.log (1 / bh12QuadraticEnvelope q p z) :=
    bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log q p hp hhalf hstrong z
  have hpowComparison :
      Real.rpow ((2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p)
          (bh12BlockExponent q) ≤
        Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) :=
    Real.rpow_le_rpow
      (mul_nonneg (by positivity) hbasePos.le) hlog hexponentPos.le
  have hfactorization :
      Real.rpow ((2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p)
          (bh12BlockExponent q) =
        Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) :=
    Real.mul_rpow (by positivity) hbasePos.le
  have hbaseRpowPos :
      0 < Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
        (bh12BlockExponent q) :=
    Real.rpow_pos_of_pos hbasePos _
  rw [hfactorization] at hpowComparison
  have htwiceComparison :
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) ≤
        2 * Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) := by
    calc
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) =
          2 * (Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
            Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
              (bh12BlockExponent q)) := by ring
      _ ≤ 2 * Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) :=
        mul_le_mul_of_nonneg_left hpowComparison (by norm_num)
  calc
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
        2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) :=
      bh12PathTypedSuccessfulOutputCost_le_two_rpow q p hsmall hhalf hstrong hq z path
    _ =
        (2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q)) /
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) := by
      field_simp [ne_of_gt hbaseRpowPos]
    _ ≤
        (2 * Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q)) /
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) :=
      div_le_div_of_nonneg_right
        htwiceComparison hbaseRpowPos.le
    _ =
        bh12QuadraticEnvelopeCostCoefficient q p *
          Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
            (bh12BlockExponent q) := by
      unfold bh12QuadraticEnvelopeCostCoefficient
      field_simp [ne_of_gt hbaseRpowPos]

/-- One actual finite BH12 selected-port schedule, indexed by its depth and
the literal output path chosen at that depth. -/
structure BH12PathScheduleIndex (q : Nat) where
  depth : Nat
  path : depthOutputPath q depth

/-- The schedule index formed by one newly selected physical output after an
existing depth-`z` path. -/
def bh12PathScheduleIndex_succ (q z : Nat) (path : depthOutputPath q (z + 1)) :
    BH12PathScheduleIndex q where
  depth := z + 1
  path := path

/-- The actual raw-input slots used by a finite BH12 schedule index. -/
abbrev bh12PathScheduleInputSlots (q : Nat) (index : BH12PathScheduleIndex q) :=
  depthRawInputPath q index.depth

/-- The actual output slots carried by a finite BH12 schedule index. -/
abbrev bh12PathScheduleOutputSlots (q : Nat) (index : BH12PathScheduleIndex q) :=
  depthOutputPath q index.depth

/-- The exact compiled quadratic-envelope target at one physical path index. -/
def bh12PathScheduleTargetError (q : Nat) (p : ErrorParameter)
    (index : BH12PathScheduleIndex q) : ℝ :=
  bh12QuadraticEnvelope q p index.depth

/-- The actual accounting-yield product packaged as the typed schedule's
nonnegative yield factor. -/
noncomputable def bh12PathScheduleTypedYieldFactor (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) : NNReal :=
  bh12PathTypedYieldFactor q p hsmall hhalf hstrong index.depth index.path

/-- The actual successful-output cost of the indexed dependent slot types. -/
noncomputable def bh12PathScheduleTypedSuccessfulOutputCost (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (bh12PathScheduleInputSlots q index)
    (bh12PathScheduleOutputSlots q index)
    (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong index)

/-- The indexed typed cost is definitionally the actual finite-path cost. -/
theorem bh12PathScheduleTypedSuccessfulOutputCost_eq (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    bh12PathScheduleTypedSuccessfulOutputCost q p hsmall hhalf hstrong index =
      bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong
        index.depth index.path :=
  rfl

/-- A positive input rate makes every indexed compiled target positive. -/
theorem bh12PathSchedule_targetError_pos (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (index : BH12PathScheduleIndex q) :
    0 < bh12PathScheduleTargetError q p index :=
  bh12QuadraticEnvelope_pos q p hp index.depth

/-- The explicit finite-domain assumptions make every indexed compiled target
strictly below one. -/
theorem bh12PathSchedule_targetError_lt_one (q : Nat) (p : ErrorParameter)
    (hp : 0 < p.rate) (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    bh12PathScheduleTargetError q p index < 1 :=
  bh12QuadraticEnvelope_lt_one q p hp hhalf hstrong index.depth

/-- The actual accounting yield is strictly positive at every indexed finite
path. -/
theorem bh12PathSchedule_yield_pos (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    0 < (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong index : ℝ) := by
  change 0 < bh12PathYieldFactorProduct q p index.depth index.path
  exact bh12PathYieldFactorProduct_pos q p hsmall hhalf hstrong
    index.depth index.path

/-- The actual recursively reached output error is bounded by the indexed
compiled quadratic-envelope target. -/
theorem bh12PathSchedule_actualOutputError_le_targetError (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    (bh12PathParameter q p index.depth index.path).rate ≤
      bh12PathScheduleTargetError q p index := by
  exact bh12PathParameter_rate_le_quadraticEnvelope q p hsmall hhalf
    (hstrong.trans (by norm_num)) index.depth index.path

/-- The selected final physical output of a nonzero schedule depth has its
exact transported density and its same-path actual error is bounded by the
compiled target, without an independence assertion. -/
theorem bh12PathSchedule_physicalSelectedOutput (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q (z + 1)) :
    (bh12PathParameter q p (z + 1) path).rate ≤
        bh12PathScheduleTargetError q p
          (bh12PathScheduleIndex_succ q z path) ∧
      bh12PathSelectedPortTransportedDensity q p z
          (depthOutputPathPrefix q z path) (depthOutputPathLast q z path) =
        OneQubit.diagonalAResource
          (bh12PathParameter q p (z + 1) path) := by
  refine ⟨bh12PathSchedule_actualOutputError_le_targetError q p hsmall hhalf
    hstrong (bh12PathScheduleIndex_succ q z path), ?_⟩
  simpa only [bh12PathParameter_succ] using
    (bh12PathSelectedPortTransportedDensity_eq_diagonalAResource q p hsmall
      hhalf (hstrong.trans (by norm_num)) z (depthOutputPathPrefix q z path)
        (depthOutputPathLast q z path))

/-- The compiled BH12 physical schedule satisfies the source-neutral
dependent typed polylogarithmic predicate using its exact exponent and
coefficient. -/
theorem bh12PathSchedule_typedPolylogCostBound (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) :
    DependentBatch.typedPolylogCostBound (bh12PathScheduleInputSlots q)
      (bh12PathScheduleOutputSlots q) (bh12PathScheduleTargetError q p)
      (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
      (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) := by
  refine ⟨(bh12QuadraticEnvelopeCostCoefficient_pos q p hp hstrong).le, ?_⟩
  intro index _ _
  refine ⟨bh12PathSchedule_yield_pos q p hsmall hhalf hstrong index, ?_⟩
  exact bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog q p hsmall
    hhalf hstrong hp hq index.depth index.path

/-- The BH12 path schedule realizes the additive, level-indexed
expected-yield overhead interface.  Its yield is the finite product of actual
one-level flagged expected-yield factors; it is not a joint binary success
probability for the whole varying-register construction. -/
theorem bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
      (bh12PathScheduleTargetError q p)
      (fun index => (bh12PathParameter q p index.depth index.path).rate)
      (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
      (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) := by
  rcases bh12PathSchedule_typedPolylogCostBound q p hsmall hhalf hstrong hp hq with
    ⟨hcoefficient, hcost⟩
  refine ⟨hcoefficient, ?_⟩
  intro index htargetPos htargetLtOne
  obtain ⟨hyield, hcostBound⟩ := hcost index htargetPos htargetLtOne
  exact ⟨bh12PathSchedule_actualOutputError_le_targetError q p hsmall hhalf
    hstrong index, hyield, hcostBound⟩

/-- The actual BH12 paths are cofinal in positive error targets.  This is a
direct reuse of the compiled finite-target physical theorem, not a second
convergence proof. -/
theorem bh12PathSchedule_cofinalActualOutputError (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
        0 < (bh12PathRun q p z path).successProbability ∧
          (∀ port : OddRow q,
            bh12PathSelectedPortTransportedDensity q p z path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter q (bh12PathParameter q p z path) port)) ∧
            (bh12PathParameter q p z path).rate ≤ epsilon := by
  exact bh12PathUniformPhysicalTarget q p hsmall hhalf
    (hstrong.trans (by norm_num))
    (hstrong.trans_lt (by norm_num)) epsilon hepsilon

/-- The finite depth-one accounting product is exactly the actual raw BH12
success mass. -/
theorem bh12PathYieldFactorProduct_depth_one (q : Nat) (p : ErrorParameter)
    (path : depthOutputPath q 1) :
    bh12PathYieldFactorProduct q p 1 path = rawSuccessMass q p := by
  simp [bh12PathYieldFactorProduct, bh12PathYieldFactor,
    bh12PathParameter]

/-- At depth one, the typed finite-slot adapter is exactly the #458
successful-output cost of the actual selected one-level BH12 family. -/
theorem bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (path : depthOutputPath q 1) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong 1 path =
      (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost (path 0) := by
  unfold bh12PathTypedSuccessfulOutputCost
  refine DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
    (bh12OneLevelProtocolFamily q p hhalf) (path 0)
    (depthRawInputPath q 1) (depthOutputPath q 1)
    (bh12PathTypedYieldFactor q p hsmall hhalf hstrong 1 path) ?_ ?_ ?_
  · rw [bh12PathTypedInputSlot_card]
    simpa using
      (bh12OneLevelProtocolFamily_inputResourceCount q p hhalf (path 0)).symm
  · rw [bh12PathTypedOutputSlot_card]
    simpa using
      (bh12OneLevelProtocolFamily_outputResourceCount q p hhalf (path 0)).symm
  · change bh12PathYieldFactorProduct q p 1 path =
      ((bh12OneLevelProtocolFamily q p hhalf).protocol (path 0)).run.successProbability
    calc
      bh12PathYieldFactorProduct q p 1 path = rawSuccessMass q p :=
      bh12PathYieldFactorProduct_depth_one q p path
      _ = ((bh12OneLevelProtocolFamily q p hhalf).protocol (path 0)).run.successProbability :=
        (bh12OneLevelProtocolFamily_successProbability q p hhalf (path 0)).symm

/-- The complete source-backed BH12 public realization for one positive
family index.  Every component is derived from the concrete #753--#756
construction: the explicit CSS family, its corrected transversal action, the
independent diagonal physical input and syndrome-postselected run, the
level-indexed fresh-parent expected-yield accounting, and the exact finite
block exponent.  The multi-level predicate is intentionally additive rather
than an invalid fixed-register `DistillationProtocolFamily`. -/
theorem bh12TriorthogonalCodeDistillation (q : Nat) (p : ErrorParameter)
    (hq : 0 < q) (hp : 0 < p.rate)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    bh12InputCount q = 3 * bh12OutputCount q + 8 ∧
      Fintype.card (OddRow q) = bh12OutputCount q ∧
        Coding.PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 ∧
          ((family q).encodedCode (isTriorthogonal q)).ImplementsLogicalGate
              (family q).correctedAllSiteT (allSiteT (Index := OddRow q)) ∧
            (InputErrorModel.independent (bh12IndependentInputModel q p)).Permits
                (noisyResources q p) ∧
              (∀ port : OddRow q, ∃ hsuccess : 0 < rawSuccessMass q p,
                0 < (bh12ActualRun q p).successProbability ∧
                  bh12SelectedPortTransportedDensity q p port =
                    OneQubit.diagonalAResource
                      (bh12DecodedMarginalErrorParameter q p hsuccess port) ∧
                  (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
                    quadraticCoefficient q * p.rate ^ 2) ∧
                DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                  (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
                  (bh12PathScheduleTargetError q p)
                  (fun index =>
                    (bh12PathParameter q p index.depth index.path).rate)
                  (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
                  (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) ∧
                  (∀ path : depthOutputPath q 1,
                    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong 1 path =
                      (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost (path 0)) ∧
                    (∀ epsilon : ℝ, 0 < epsilon →
                      ∃ z : Nat, ∀ path : depthOutputPath q z,
                        0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
                          0 < (bh12PathRun q p z path).successProbability ∧
                            (∀ port : OddRow q,
                              bh12PathSelectedPortTransportedDensity q p z path port =
                                OneQubit.diagonalAResource
                                  (bh12TotalNextParameter q
                                    (bh12PathParameter q p z path) port)) ∧
                              (bh12PathParameter q p z path).rate ≤ epsilon) ∧
                      bh12BlockExponent q =
                        Real.log (((3 * bh12OutputCount q + 8 : Nat) : ℝ) /
                          (bh12OutputCount q : ℝ)) / Real.log 2 ∧
                        Tendsto (fun index : Nat => bh12BlockExponent (index + 1)) atTop
                          (𝓝 (Real.log 3 / Real.log 2)) ∧
                          bh12BlockExponent q ≠ Real.log 3 / Real.log 2 ∧
                            (∀ k : Nat, Even k → 0 < k →
                              ∃ index : Nat, 0 < index ∧ k = logicalCount index ∧
                                bh12BlockExponent index =
                                  Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) /
                                    Real.log 2 ∧
                                  Real.log 3 / Real.log 2 < bh12BlockExponent index) := by
  refine ⟨bh12InputCount_eq_three_mul_output_add_eight q, ?_,
    pureZLogicalMinimumDistance_two hq, ?_, bh12IndependentInputModel_permits q p,
    ?_, bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead q p hsmall
      hhalf hstrong hp hq, ?_, ?_, ?_,
    bh12BlockExponent_succ_tendsto_log_three_div_log_two,
    bh12BlockExponent_ne_log_three_div_log_two hq, ?_⟩
  · simpa [bh12OutputCount] using card_oddRow q
  · exact BinaryRowFamily.correctedAllSiteT_implements_logicalAllSiteT
      (family q) (isTriorthogonal q)
  · intro port
    obtain ⟨hsuccess, hactualSuccess, hdensity, hquadratic, _, _, _, _⟩ :=
      bh12OneStepPhysicalInvariant q p port hsmall hhalf (hstrong.trans (by norm_num))
    exact ⟨hsuccess, hactualSuccess, hdensity, hquadratic⟩
  · intro path
    exact bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily q p hsmall
      hhalf hstrong path
  · intro epsilon hepsilon
    exact bh12PathSchedule_cofinalActualOutputError q p hsmall hhalf hstrong epsilon hepsilon
  · exact bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq hq rfl
  · intro k hk hkpos
    exact bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos hk hkpos

end QEC.Distillation.Triorthogonal.BH12Concatenation
