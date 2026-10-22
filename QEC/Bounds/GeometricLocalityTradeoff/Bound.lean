import QEC.Locality.Core.Definitions
import QEC.Locality.OptimalTradeoff.Interaction
/-!
# QEC.Bounds.BPT

Statement surfaces for the audited exact locality and connectivity tradeoff
frontier.
-/

namespace QEC

universe u v w

namespace Coding
namespace CodeParameters

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι]

/-- The recorded minimum distance is positive, witnessed by `distance_spec`. -/
theorem minimumDistance_pos (p : CodeParameters F ι) : 0 < p.minimumDistance := by
  rcases p.distance_spec with ⟨x, _hxC, hx0, hweight, _hleast⟩
  have hweight_ne_zero : HammingWeight x ≠ 0 := by
    intro hzero
    exact hx0 ((HammingWeight_eq_zero_iff x).mp hzero)
  have hweight_pos : 0 < HammingWeight x := Nat.pos_of_ne_zero hweight_ne_zero
  rw [← hweight]
  exact hweight_pos

/--
The recorded block length is positive, derived from the same nonzero
minimum-distance witness rather than assumed coordinate nonemptiness.
-/
theorem length_pos (p : CodeParameters F ι) : 0 < p.length := by
  rcases p.distance_spec with ⟨x, _hxC, hx0, _hweight, _hleast⟩
  have hweight_ne_zero : HammingWeight x ≠ 0 := by
    intro hzero
    exact hx0 ((HammingWeight_eq_zero_iff x).mp hzero)
  have hweight_pos : 0 < HammingWeight x := Nat.pos_of_ne_zero hweight_ne_zero
  have hweight_le_length : HammingWeight x ≤ Length F ι := by
    simpa [HammingWeight, Length] using Finset.card_le_univ (hammingSupport x)
  have hlength : 0 < Length F ι := lt_of_lt_of_le hweight_pos hweight_le_length
  simpa [p.length_eq] using hlength

end CodeParameters
end Coding

namespace Bounds
namespace BPT

/-- Numerical parameters shared by exact quantum-code tradeoff statements. -/
structure QuantumCodeParameters where
  blockLength : ℝ
  encodedQubits : ℝ
  distance : ℝ
  blockLength_pos : 0 < blockLength
  encodedQubits_nonneg : 0 ≤ encodedQubits
  distance_pos : 0 < distance

namespace QuantumCodeParameters

/--
Forget a concrete finite-field code-parameter record to the bare real-valued
numeric surface used by BPT statement forms.
-/
noncomputable def ofCodeParameters {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    QuantumCodeParameters where
  blockLength := (p.length : ℝ)
  encodedQubits := (p.dimension : ℝ)
  distance := (p.minimumDistance : ℝ)
  blockLength_pos := by
    exact_mod_cast Coding.CodeParameters.length_pos p
  encodedQubits_nonneg := by
    exact_mod_cast Nat.zero_le p.dimension
  distance_pos := by
    exact_mod_cast Coding.CodeParameters.minimumDistance_pos p

@[simp]
theorem ofCodeParameters_blockLength {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).blockLength = (p.length : ℝ) :=
  rfl

@[simp]
theorem ofCodeParameters_encodedQubits {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).encodedQubits = (p.dimension : ℝ) :=
  rfl

@[simp]
theorem ofCodeParameters_distance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).distance = (p.minimumDistance : ℝ) :=
  rfl

end QuantumCodeParameters

/-- The BPT finite-size bound, written without division. -/
def BPTBound (p : QuantumCodeParameters) (constant : ℝ) : Prop :=
  0 < constant ∧ p.encodedQubits * p.distance ^ 2 ≤ constant * p.blockLength

/-- Frameworks have the same BPT local data when the local range and local dimension agree. -/
def SameBPTLocalData {F : Type u} {ι : Type v} {H K : Type w}
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (left right : Locality.ExactLocalityFramework F ι H K) : Prop :=
  left.localProjectorCode.projectorLocality = right.localProjectorCode.projectorLocality ∧
    left.localDimensionBound = right.localDimensionBound

/--
BPT tradeoff data tying numerical parameters and the local constant to a
particular exact-locality framework.
-/
structure BPTTradeoffData (F : Type u) (ι : Type v) (H K : Type w)
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] where
  framework : Locality.ExactLocalityFramework F ι H K
  parameters : QuantumCodeParameters
  parameters_match_framework : Prop
  constantFor : Locality.ExactLocalityFramework F ι H K → ℝ

/-- The BPT constant is uniform across frameworks with the same local data. -/
def BPTLocalConstant {F : Type u} {ι : Type v} {H K : Type w}
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (constantFor : Locality.ExactLocalityFramework F ι H K → ℝ)
    (framework : Locality.ExactLocalityFramework F ι H K) : Prop :=
  0 < constantFor framework ∧
    ∀ other : Locality.ExactLocalityFramework F ι H K,
      SameBPTLocalData framework other → constantFor other = constantFor framework

/--
BPT exact geometric locality tradeoff statement surface.

This declaration records the source shape `k d^2 <= O(n)` for a two-dimensional
commuting-projector locality framework. It is a statement surface, not a proof
of the Bravyi-Poulin-Terhal theorem.
-/
def BPTTradeoffStatement {F : Type u} {ι : Type v} {H K : Type w}
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (data : BPTTradeoffData F ι H K) : Prop :=
  data.framework.latticeDimension = 2 →
    data.framework.distanceConvention →
      data.parameters_match_framework →
        BPTLocalConstant data.constantFor data.framework ∧
          BPTBound data.parameters (data.constantFor data.framework)

/-- Asymptotic family parameters indexed by a natural size parameter. -/
structure QuantumCodeFamily where
  parameters : Nat → QuantumCodeParameters
  validIndex : Nat → Prop

namespace QuantumCodeFamily

/--
Nat-indexed family adapter from concrete code parameters to the bare BPT
numeric family surface.
-/
noncomputable def ofCodeParameters {F : Type u} {ι : Nat → Type v} [Field F]
    [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n))
    (validIndex : Nat → Prop := fun _ => True) : QuantumCodeFamily where
  parameters := fun n => QuantumCodeParameters.ofCodeParameters (codeParameters n)
  validIndex := validIndex

@[simp]
theorem ofCodeParameters_validIndex {F : Type u} {ι : Nat → Type v} [Field F]
    [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    (ofCodeParameters codeParameters validIndex).validIndex n = validIndex n :=
  rfl

@[simp]
theorem ofCodeParameters_parameters_blockLength {F : Type u} {ι : Nat → Type v}
    [Field F] [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    ((ofCodeParameters codeParameters validIndex).parameters n).blockLength =
      ((codeParameters n).length : ℝ) :=
  rfl

@[simp]
theorem ofCodeParameters_parameters_encodedQubits {F : Type u} {ι : Nat → Type v}
    [Field F] [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    ((ofCodeParameters codeParameters validIndex).parameters n).encodedQubits =
      ((codeParameters n).dimension : ℝ) :=
  rfl

@[simp]
theorem ofCodeParameters_parameters_distance {F : Type u} {ι : Nat → Type v}
    [Field F] [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    ((ofCodeParameters codeParameters validIndex).parameters n).distance =
      ((codeParameters n).minimumDistance : ℝ) :=
  rfl

end QuantumCodeFamily

/-- Eventually-on-family quantification for audited Big-O statement surfaces. -/
def EventuallyOnFamily (family : QuantumCodeFamily) (predicate : Nat → Prop) : Prop :=
  ∃ start : Nat, ∀ i : Nat, start ≤ i → family.validIndex i → predicate i

/-- A concrete Big-O witness using explicit positive multiplicative constants. -/
def AsymptoticBigO (family : QuantumCodeFamily) (value bound : Nat → ℝ) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    EventuallyOnFamily family (fun i => value i ≤ constant * bound i)

/-- A separator exponent is eventually uniformly below one. -/
def UniformlyBelowOne (family : QuantumCodeFamily) (cMax : Nat → ℝ) : Prop :=
  ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
    EventuallyOnFamily family (fun i => cMax i ≤ ceiling)

/-- Family-level connectivity-separator data for the BK tradeoff surface. -/
structure ConnectivitySeparatorFamily (ι : Type u) [Fintype ι] [DecidableEq ι] where
  codeFamily : QuantumCodeFamily
  graph : Nat → Locality.ConnectivityGraph ι
  cMax : Nat → ℝ
  assumesMeasuredProfileExponentUpperBound :
    ∀ i : Nat, Locality.AssumedBKMeasuredProfileExponentUpperBound (graph i) (cMax i)

/-- The BK family has the graph and separator-profile data required by the source. -/
def ConnectivitySeparatorHypotheses {ι : Type u} [Fintype ι] [DecidableEq ι]
    (data : ConnectivitySeparatorFamily ι) : Prop :=
  EventuallyOnFamily data.codeFamily
    (fun i => Locality.AssumedBKMeasuredProfileExponentUpperBound
      (data.graph i) (data.cMax i))

/-- BK separator bound term `n d^(2(c_max-1)) log(n)^2`. -/
noncomputable def BKSeparatorBoundTerm (family : QuantumCodeFamily)
    (cMax : Nat → ℝ) (i : Nat) : ℝ :=
  (family.parameters i).blockLength *
    Real.rpow (family.parameters i).distance (2 * (cMax i - 1)) *
      (Real.log (family.parameters i).blockLength) ^ 2

/-- The log-free BK bound term under a uniform separator-exponent gap. -/
noncomputable def BKLogFreeBoundTerm (family : QuantumCodeFamily)
    (cMax : Nat → ℝ) (i : Nat) : ℝ :=
  (family.parameters i).blockLength *
    Real.rpow (family.parameters i).distance (2 * (cMax i - 1))

/--
BK connectivity-separator tradeoff statement surface.

The first conjunct records the logarithmic bound. The second records the
source's log-free specialization under a uniform `c_max < 1` hypothesis.
-/
noncomputable def ConnectivitySeparatorTradeoffStatement
    {ι : Type u} [Fintype ι] [DecidableEq ι] (data : ConnectivitySeparatorFamily ι) : Prop :=
  ConnectivitySeparatorHypotheses data ∧
    AsymptoticBigO data.codeFamily
      (fun i => (data.codeFamily.parameters i).encodedQubits)
      (BKSeparatorBoundTerm data.codeFamily data.cMax) ∧
        (UniformlyBelowOne data.codeFamily data.cMax →
          AsymptoticBigO data.codeFamily
            (fun i => (data.codeFamily.parameters i).encodedQubits)
            (BKLogFreeBoundTerm data.codeFamily data.cMax))

/-- The BGKL exponent range `c in (0,1]`. -/
def RestrictedConnectivityExponentValid (c : ℝ) : Prop :=
  0 < c ∧ c ≤ 1

/-- Family-level restricted-connectivity data for the BGKL tradeoff surface. -/
structure RestrictedConnectivityFamily (ι : Type u) [Fintype ι] [DecidableEq ι] where
  codeFamily : QuantumCodeFamily
  graph : Nat → Locality.ConnectivityGraph ι
  exponent : ℝ
  fixedGeneratorSet : Nat → Prop
  assumesMeasuredProfilePowerUpperBound :
    ∀ i : Nat, Locality.AssumedBGKLMeasuredProfilePowerUpperBound
      (graph i) 1 exponent

/-- The BGKL family has fixed-generator graphs and separation profiles eventually. -/
def RestrictedConnectivityHypotheses {ι : Type u} [Fintype ι] [DecidableEq ι]
    (data : RestrictedConnectivityFamily ι) : Prop :=
  RestrictedConnectivityExponentValid data.exponent ∧
  EventuallyOnFamily data.codeFamily
      (fun i => data.fixedGeneratorSet i ∧
        Locality.AssumedBGKLMeasuredProfilePowerUpperBound
          (data.graph i) 1 data.exponent)

/-- BGKL restricted-connectivity value term `k d^((1-c^2)/c)`. -/
noncomputable def BGKLRestrictedValueTerm
    (family : QuantumCodeFamily) (c : ℝ) (i : Nat) : ℝ :=
  (family.parameters i).encodedQubits *
    Real.rpow (family.parameters i).distance ((1 - c ^ 2) / c)

/-- BGKL restricted-connectivity tradeoff statement surface. -/
noncomputable def RestrictedConnectivityTradeoffStatement
    {ι : Type u} [Fintype ι] [DecidableEq ι] (data : RestrictedConnectivityFamily ι) : Prop :=
  RestrictedConnectivityHypotheses data ∧
    AsymptoticBigO data.codeFamily
      (BGKLRestrictedValueTerm data.codeFamily data.exponent)
      (fun i => (data.codeFamily.parameters i).blockLength)

/--
Concrete fixed-presentation embedding data for the legacy Dai--Li family
statement surface.  Long-interaction counts are derived below from the actual
finite unordered edge set; they are not stored as arbitrary numerical data.
-/
structure EmbeddedInteractionFamily (ι : Type u) (κ : Type v)
    [Fintype ι] [DecidableEq ι] [Fintype κ] where
  codeFamily : QuantumCodeFamily
  presentation : Nat → Coding.StabilizerCode.BinaryStabilizerPresentation
    (ι := ι) (κ := κ)
  embedding : Nat → Locality.UnitSeparatedEmbedding2D ι

namespace EmbeddedInteractionFamily

/--
The family surface's long-interaction count is the finite cardinality computed
from the fixed presentation and unit-separated embedding at that index.
-/
noncomputable def interactionsAtLengthAtLeast {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (data : EmbeddedInteractionFamily ι κ) (i : Nat) (threshold : ℝ) : Nat :=
  (data.presentation i).longInteractionCount (data.embedding i) threshold

/-- The family accessor unfolds to the cardinality of the actual unordered edge set. -/
theorem interactionsAtLengthAtLeast_eq_card {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (data : EmbeddedInteractionFamily ι κ) (i : Nat) (threshold : ℝ) :
    data.interactionsAtLengthAtLeast i threshold =
      ((data.presentation i).interactionsAtLengthAtLeast (data.embedding i) threshold).card :=
  rfl

end EmbeddedInteractionFamily

/-- The Dai-Li length scale `max(d/sqrt(n), (k d^2/n)^(1/4))`. -/
noncomputable def DaiLiLengthScale (p : QuantumCodeParameters) : ℝ :=
  max (p.distance / Real.sqrt p.blockLength)
    (Real.rpow (p.encodedQubits * p.distance ^ 2 / p.blockLength) (1 / 4 : ℝ))

/-- The Dai-Li above-BPT-threshold hypothesis `k d^2 >= c1 n`. -/
def AboveBPTThreshold (p : QuantumCodeParameters) (c1 : ℝ) : Prop :=
  c1 * p.blockLength ≤ p.encodedQubits * p.distance ^ 2

/--
Dai-Li optimal locality tradeoff statement surface.

The conclusion records both audited lower bounds: many long interactions and a
minimum long-interaction length at the source scale.
-/
noncomputable def OptimalLocalityTradeoffStatement
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (embedding : EmbeddedInteractionFamily ι κ) : Prop :=
  ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
    EventuallyOnFamily embedding.codeFamily (fun i =>
      AboveBPTThreshold (embedding.codeFamily.parameters i) c1 →
        c0 *
            max (embedding.codeFamily.parameters i).encodedQubits
              (embedding.codeFamily.parameters i).distance ≤
          (embedding.interactionsAtLengthAtLeast i
            (c0 * DaiLiLengthScale (embedding.codeFamily.parameters i)) : ℝ))

end BPT
end Bounds
end QEC
