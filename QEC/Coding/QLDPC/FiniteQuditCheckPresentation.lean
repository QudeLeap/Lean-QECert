import QEC.Coding.QLDPC.Core
import QEC.Semantics.ErrorCorrection.Detectability
import QEC.Semantics.ErrorCorrection.QuditSubsystem

/-!
# Finite-qudit semantic check presentations

This module ties finite local checks to an actual quantum code on a uniform
finite-qudit register.  Numerical observations are derived from the same
presentation: the physical length is the coordinate cardinality, locality is
the check-region incidence profile, and distance is the least support size of
a nondetectable local operator.

The checks are operator-level.  A construction over a particular finite field
must separately prove that its algebraic checks instantiate this semantic
interface.
-/

noncomputable section

namespace QEC
namespace QLDPC

universe u v

/-- The constant local-dimension function for a uniform finite-qudit register.

This is an abbreviation so constructions stated with the explicit constant
function share the same inferred finite-register instances as the semantic
presentation API. -/
abbrev uniformQuditDimensions {ι : Type u} (alphabetSize : Nat) : ι → Nat :=
  fun _ => alphabetSize

/-- A selected region supports a local operator that is not scalar on the code. -/
def SupportsNondetectableLocalOperator
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q) : Prop :=
  ∃ localOperator : Semantics.Operator region.selectedSystem,
    ¬ Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator)

/--
The least coordinate-region size supporting a nondetectable local operator.

The natural-number infimum is zero when no such operator exists. Downstream
codes with a nontrivial logical sector may separately prove attainment using
`semanticQuditDistance_attained`.
-/
def semanticQuditDistance
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q)) : Nat :=
  sInf {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
    Fintype.card region.SelectedCoordinates = weight ∧
      SupportsNondetectableLocalOperator code region}

/-- Any concrete nondetectable local operator upper-bounds semantic distance. -/
theorem semanticQuditDistance_le_of_nondetectable
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q)
    (localOperator : Semantics.Operator region.selectedSystem)
    (hoperator : ¬ Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator)) :
    semanticQuditDistance q code ≤ Fintype.card region.SelectedCoordinates := by
  apply Nat.sInf_le
  exact ⟨region, rfl, localOperator, hoperator⟩

/-- Every operator on a region smaller than semantic distance is detectable. -/
theorem detectable_of_card_lt_semanticQuditDistance
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q)
    (hcard : Fintype.card region.SelectedCoordinates <
      semanticQuditDistance q code)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator) := by
  by_contra hoperator
  have hle := semanticQuditDistance_le_of_nondetectable
    code region localOperator hoperator
  omega

/-- A nonempty logical-region set attains the finite semantic distance. -/
theorem semanticQuditDistance_attained
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (hnonempty : {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = weight ∧
        SupportsNondetectableLocalOperator code region}.Nonempty) :
    ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = semanticQuditDistance q code ∧
        SupportsNondetectableLocalOperator code region := by
  exact Nat.sInf_mem hnonempty

/-- Semantic distance never exceeds the number of physical coordinates,
including the convention that a code with no nondetectable operator has distance zero. -/
theorem semanticQuditDistance_le_card
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q)) :
    semanticQuditDistance q code ≤ Fintype.card ι := by
  classical
  let weights : Set Nat := {weight | ∃ region : Semantics.QuditSubsystem q,
    Fintype.card region.SelectedCoordinates = weight ∧
      SupportsNondetectableLocalOperator code region}
  by_cases hnonempty : weights.Nonempty
  · obtain ⟨region, hcard, _⟩ := semanticQuditDistance_attained code hnonempty
    rw [← hcard]
    exact region.card_selected_le_total
  · have hempty : weights = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    change sInf weights ≤ Fintype.card ι
    rw [hempty, Nat.sInf_empty]
    exact Nat.zero_le _

/-- A detecting threshold lower-bounds semantic distance once some local failure exists. -/
theorem le_semanticQuditDistance_of_detectable_and_exists_nondetectable
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (d : Nat)
    (hdetect : ∀ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates < d →
        ∀ localOperator : Semantics.Operator region.selectedSystem,
          Semantics.DetectableOn code
            (region.extendLocalToRegister localOperator))
    (hexists : ∃ region : Semantics.QuditSubsystem q,
      SupportsNondetectableLocalOperator code region) :
    d ≤ semanticQuditDistance q code := by
  have hnonempty : {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = weight ∧
        SupportsNondetectableLocalOperator code region}.Nonempty := by
    obtain ⟨region, hregion⟩ := hexists
    exact ⟨Fintype.card region.SelectedCoordinates, region, rfl, hregion⟩
  obtain ⟨region, hcard, localOperator, hnot⟩ :=
    semanticQuditDistance_attained code hnonempty
  by_contra hless
  exact hnot (hdetect region (by omega) localOperator)

/-- A check given by an operator on an explicit finite coordinate region. -/
structure FiniteQuditCheck (ι : Type u) [Fintype ι] [DecidableEq ι]
    (alphabetSize : Nat) where
  region : Semantics.QuditSubsystem (uniformQuditDimensions (ι := ι) alphabetSize)
  localOperator : Semantics.Operator region.selectedSystem

namespace FiniteQuditCheck

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {alphabetSize : Nat}

/-- The local check extended by the identity to the whole physical register. -/
noncomputable def globalOperator (check : FiniteQuditCheck ι alphabetSize) :
    Semantics.Operator
      (Semantics.Qudit.QuditRegister (uniformQuditDimensions (ι := ι) alphabetSize)) :=
  check.region.extendLocalToRegister check.localOperator

@[simp]
theorem globalOperator_eq_extendLocalToRegister
    (check : FiniteQuditCheck ι alphabetSize) :
    check.globalOperator =
      check.region.extendLocalToRegister check.localOperator :=
  rfl

end FiniteQuditCheck

/--
An actual finite-qudit quantum code together with a finite local check
presentation whose common fixed space is exactly the code carrier.

The encoded-qudit count is certified against the semantic carrier dimension;
block length, distance, and locality are deliberately not stored as detached
numeric fields.
-/
structure FiniteQuditCheckPresentation
    (ι : Type u) (κ : Type v) [Fintype ι] [DecidableEq ι] [Fintype κ] where
  alphabetSize : Nat
  alphabetSize_ge_two : 2 ≤ alphabetSize
  code : Semantics.QuantumCode
    (Semantics.Qudit.QuditRegister
      (uniformQuditDimensions (ι := ι) alphabetSize))
  checks : κ → FiniteQuditCheck ι alphabetSize
  carrier_iff_fixed : ∀ ψ, ψ ∈ code.carrier ↔
    ∀ checkIndex, (checks checkIndex).globalOperator ψ = ψ
  encodedQudits : Nat
  dimension_eq : code.dimension = alphabetSize ^ encodedQudits

namespace FiniteQuditCheckPresentation

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The number of physical qudits, derived from the coordinate type. -/
def blockLength (_P : FiniteQuditCheckPresentation ι κ) : Nat :=
  Fintype.card ι

/-- The concrete check-variable incidence relation induced by check regions. -/
def incidence (P : FiniteQuditCheckPresentation ι κ) :
    CheckIncidence κ ι where
  incident checkIndex coordinate :=
    coordinate ∈ (P.checks checkIndex).region.selected

/-- The row-weight and variable-degree profile derived from check incidence. -/
noncomputable def localityProfile (P : FiniteQuditCheckPresentation ι κ) :
    Coding.LocalityProfile :=
  P.incidence.localityProfile

/-- The least support size of a nondetectable local operator on the semantic code. -/
def distance (P : FiniteQuditCheckPresentation ι κ) : Nat :=
  semanticQuditDistance
    (uniformQuditDimensions (ι := ι) P.alphabetSize) P.code

/-- The alphabet has positive local dimension. -/
theorem alphabetSize_pos (P : FiniteQuditCheckPresentation ι κ) :
    0 < P.alphabetSize :=
  lt_of_lt_of_le (by decide) P.alphabetSize_ge_two

/-- Every site in the uniform register has positive local dimension. -/
theorem localDimension_pos (P : FiniteQuditCheckPresentation ι κ) (i : ι) :
    0 < uniformQuditDimensions (ι := ι) P.alphabetSize i := by
  simpa [uniformQuditDimensions] using P.alphabetSize_pos

/-- Carrier membership is exactly simultaneous fixation by every global check. -/
theorem mem_carrier_iff_fixed (P : FiniteQuditCheckPresentation ι κ)
    (ψ : Semantics.Qudit.QuditRegister
      (uniformQuditDimensions (ι := ι) P.alphabetSize)) :
    ψ ∈ P.code.carrier ↔
      ∀ checkIndex, (P.checks checkIndex).globalOperator ψ = ψ :=
  P.carrier_iff_fixed ψ

/-- The derived block length is the physical coordinate cardinality. -/
@[simp]
theorem blockLength_eq_card (P : FiniteQuditCheckPresentation ι κ) :
    P.blockLength = Fintype.card ι :=
  rfl

/-- The declared encoded-qudit count is tied to the actual carrier finrank. -/
theorem semantic_dimension_eq (P : FiniteQuditCheckPresentation ι κ) :
    P.code.dimension = P.alphabetSize ^ P.encodedQudits :=
  P.dimension_eq

/-- A coordinate is incident to a check exactly when it lies in that check's region. -/
@[simp]
theorem incidence_iff_mem_region (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) (coordinate : ι) :
    P.incidence.incident checkIndex coordinate ↔
      coordinate ∈ (P.checks checkIndex).region.selected :=
  Iff.rfl

/-- The incidence support of a check is its explicitly selected local region. -/
theorem checkSupport_eq_region (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) :
    P.incidence.checkSupport checkIndex =
      (P.checks checkIndex).region.selected := by
  ext coordinate
  simp

/-- Variable support lists exactly the checks whose local region contains the coordinate. -/
@[simp]
theorem mem_variableSupport_iff_mem_region
    (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) (coordinate : ι) :
    checkIndex ∈ P.incidence.variableSupport coordinate ↔
      coordinate ∈ (P.checks checkIndex).region.selected := by
  simp

/-- Concrete row and column bounds certify bounded locality for the derived profile. -/
theorem boundedLocality_of_region_bounds
    (P : FiniteQuditCheckPresentation ι κ) {bound : Nat}
    (hcheck : ∀ checkIndex,
      (P.checks checkIndex).region.selected.card ≤ bound)
    (hcoordinate : ∀ coordinate,
      (P.incidence.variableSupport coordinate).card ≤ bound) :
    Coding.BoundedLocality P.localityProfile bound := by
  apply P.incidence.boundedLocality_of_row_col_bounds
  · intro checkIndex
    rw [P.checkSupport_eq_region]
    exact hcheck checkIndex
  · exact hcoordinate

/-- The presentation's distance is the semantic local-operator distance of its code. -/
theorem distance_eq_semanticQuditDistance
    (P : FiniteQuditCheckPresentation ι κ) :
    P.distance = semanticQuditDistance
      (uniformQuditDimensions (ι := ι) P.alphabetSize) P.code :=
  rfl

/-- The derived distance is at most the physical block length. -/
theorem distance_le_blockLength (P : FiniteQuditCheckPresentation ι κ) :
    P.distance ≤ P.blockLength := by
  rw [P.distance_eq_semanticQuditDistance, P.blockLength_eq_card]
  exact semanticQuditDistance_le_card _ _

/-- Every local operator below the derived distance is detectable by the code. -/
theorem detectable_of_card_lt_distance
    (P : FiniteQuditCheckPresentation ι κ)
    (region : Semantics.QuditSubsystem
      (uniformQuditDimensions (ι := ι) P.alphabetSize))
    (hcard : Fintype.card region.SelectedCoordinates < P.distance)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn P.code
      (region.extendLocalToRegister localOperator) := by
  exact detectable_of_card_lt_semanticQuditDistance
    P.code region hcard localOperator

/-- The presentation's locality profile is exactly its incidence profile. -/
theorem localityProfile_eq_incidence
    (P : FiniteQuditCheckPresentation ι κ) :
    P.localityProfile = P.incidence.localityProfile :=
  rfl

end FiniteQuditCheckPresentation

end QLDPC
end QEC
