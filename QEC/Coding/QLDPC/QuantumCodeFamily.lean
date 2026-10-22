import QEC.Coding.QLDPC.FiniteQuditCheckPresentation

/-!
# Finite-qudit quantum-code families

An index specifies a concrete finite-qudit check presentation. Physical length,
encoded-qudit count, semantic distance, and check locality are observations of
that same presentation. The family only requires cofinal physical length; no
asymptotic rate, relative-distance, or uniform locality conclusion is built in.
-/

noncomputable section

namespace QEC.QLDPC

universe u v w

/-- A cofinal family of actual finite-qudit codes with local check presentations. -/
structure QuantumCodeFamily
    (A : Type u) (ι : A → Type v) (κ : A → Type w)
    [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)] where
  presentation : ∀ a, FiniteQuditCheckPresentation (ι a) (κ a)
  cofinal_blockLength : ∀ N : Nat, ∃ a : A, N ≤ (presentation a).blockLength

namespace QuantumCodeFamily

variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

/-- The physical block length at an index, derived from its coordinate type. -/
def blockLength (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.presentation a).blockLength

/-- The number of encoded qudits at an index, certified by its carrier dimension. -/
def encodedDimension (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.presentation a).encodedQudits

/-- The least support size of a nondetectable local operator at an index. -/
def distance (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.presentation a).distance

/-- The row-weight and variable-degree profile of the indexed checks. -/
def localityProfile (F : QuantumCodeFamily A ι κ) (a : A) : Coding.LocalityProfile :=
  (F.presentation a).localityProfile

/-- Maximum number of coordinates in one indexed check region. -/
def maxCheckWeight (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.localityProfile a).maxCheckWeight

/-- Maximum number of indexed checks incident to one coordinate. -/
def maxVariableDegree (F : QuantumCodeFamily A ι κ) (a : A) : Nat :=
  (F.localityProfile a).maxVariableDegree

/-- The family contains codes of arbitrarily large physical block length. -/
theorem exists_blockLength_ge (F : QuantumCodeFamily A ι κ) (N : Nat) :
    ∃ a : A, N ≤ F.blockLength a :=
  F.cofinal_blockLength N

/-- Physical length counts the actual coordinates of the indexed register. -/
@[simp] theorem blockLength_eq_card (F : QuantumCodeFamily A ι κ) (a : A) :
    F.blockLength a = Fintype.card (ι a) :=
  (F.presentation a).blockLength_eq_card

/-- Encoded dimension is certified by the actual indexed quantum-code carrier. -/
theorem code_dimension_eq (F : QuantumCodeFamily A ι κ) (a : A) :
    (F.presentation a).code.dimension =
      (F.presentation a).alphabetSize ^ F.encodedDimension a :=
  (F.presentation a).semantic_dimension_eq

/-- Indexed distance is the semantic local-operator distance of the indexed code. -/
theorem distance_eq_semanticQuditDistance
    (F : QuantumCodeFamily A ι κ) (a : A) :
    F.distance a = semanticQuditDistance
      (uniformQuditDimensions (ι := ι a) (F.presentation a).alphabetSize)
      (F.presentation a).code :=
  (F.presentation a).distance_eq_semanticQuditDistance

/-- Every indexed code has distance at most its actual physical length. -/
theorem distance_le_blockLength (F : QuantumCodeFamily A ι κ) (a : A) :
    F.distance a ≤ F.blockLength a :=
  (F.presentation a).distance_le_blockLength

/-- Operators supported on fewer than the indexed distance are detectable. -/
theorem detectable_of_card_lt_distance
    (F : QuantumCodeFamily A ι κ) (a : A)
    (region : Semantics.QuditSubsystem
      (uniformQuditDimensions (ι := ι a) (F.presentation a).alphabetSize))
    (hcard : Fintype.card region.SelectedCoordinates < F.distance a)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn (F.presentation a).code
      (region.extendLocalToRegister localOperator) :=
  (F.presentation a).detectable_of_card_lt_distance region hcard localOperator

/-- Indexed locality is precisely the incidence profile of its actual checks. -/
theorem localityProfile_eq_incidence (F : QuantumCodeFamily A ι κ) (a : A) :
    F.localityProfile a = (F.presentation a).incidence.localityProfile :=
  (F.presentation a).localityProfile_eq_incidence

/-- Concrete row and column bounds imply the indexed locality bound. -/
theorem boundedLocality_of_region_bounds
    (F : QuantumCodeFamily A ι κ) (a : A) {bound : Nat}
    (hcheck : ∀ checkIndex,
      ((F.presentation a).checks checkIndex).region.selected.card ≤ bound)
    (hcoordinate : ∀ coordinate,
      ((F.presentation a).incidence.variableSupport coordinate).card ≤ bound) :
    Coding.BoundedLocality (F.localityProfile a) bound :=
  (F.presentation a).boundedLocality_of_region_bounds hcheck hcoordinate

/-- A bound on both derived locality components is exactly bounded locality. -/
theorem boundedLocality_iff (F : QuantumCodeFamily A ι κ) (a : A) (bound : Nat) :
    Coding.BoundedLocality (F.localityProfile a) bound ↔
      F.maxCheckWeight a ≤ bound ∧ F.maxVariableDegree a ≤ bound :=
  Iff.rfl

end QuantumCodeFamily

end QEC.QLDPC
