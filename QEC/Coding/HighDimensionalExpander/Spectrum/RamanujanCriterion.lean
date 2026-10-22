import QEC.Coding.HighDimensionalExpander.Spectrum.PrefixHeckeCompatibility
import QEC.Coding.HighDimensionalExpander.Spectrum.QuotientL2

/-!
# The conditional LSV local Ramanujan criterion

This module closes the local conditional Ramanujan boundary.  The finite colored
operators and their universal-building target are the concrete constructions
from `LSVFiniteSpectrum` and `UniversalBuildingSpectrum`; the actual
quotient representation and occurrence relation are imported from
`LSVQuotientL2`.

The only external mathematical premise accepted by the terminal adapters is
the exact equivalence of Lubotzky--Samuels--Vishne Proposition 1.5: the
concrete quotient is Ramanujan if and only if every irreducible spherical
infinite-dimensional constituent occurring in its actual quotient `L²`
representation is tempered.  The equivalence is written literally in each
adapter signature.  It is not stored in a structure, an axiom, or a
conclusion-bearing specification.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open QEC.Coding.HighDimensionalExpander.SphericalHecke

universe u

/-- A spherical constituent of the actual LSV quotient `L²` representation.
Occurrence is witnessed by a closed invariant subspace and an intertwining
linear isometry; irreducibility, unitarity, and sphericality are predicates on
that actual occurring representation. -/
def IsLSVSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  OccursInLSVAutomorphicL2 P r level sigma ∧
    IsIrreducibleUnitarySpherical sigma

/-- A trivial constituent in the representation-theoretic formulation of
LSV Proposition 1.5: an actually occurring irreducible unitary spherical
constituent whose representation space is finite-dimensional. -/
def IsLSVTrivialSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  IsLSVSphericalConstituent P r level sigma ∧ Module.Finite ℂ V

/-- The constituents quantified over by LSV Proposition 1.5: actually
occurring irreducible unitary spherical representations that are not
finite-dimensional. -/
def IsLSVInfiniteDimensionalSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) : Prop :=
  IsLSVSphericalConstituent P r level sigma ∧ ¬ Module.Finite ℂ V

/-- Closed isometric occurrence in the concrete quotient `L²` forces
unitarity.  Thus unitarity is inherited from the proved right-regular
representation and is not independent caller-supplied representation data. -/
theorem isUnitary_of_occursInLSVAutomorphicL2
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hoccurs : OccursInLSVAutomorphicL2 P r level sigma) :
    IsUnitary sigma := by
  rcases hoccurs with ⟨U, hUclosed, e, hintertwines⟩
  intro g v w
  have hv := hintertwines g v
  have hw := hintertwines g w
  calc
    inner ℂ (sigma g v) (sigma g w) =
        inner ℂ (e (sigma g v)) (e (sigma g w)) :=
      (e.inner_map_map (sigma g v) (sigma g w)).symm
    _ = inner ℂ
        (((e (sigma g v) : U.toSubmodule) :
          LSVAutomorphicL2 P r level))
        (((e (sigma g w) : U.toSubmodule) :
          LSVAutomorphicL2 P r level)) := rfl
    _ = inner ℂ
        (lsvRightRegularRepresentation P r level g
          (((e v : U.toSubmodule) :
            LSVAutomorphicL2 P r level)))
        (lsvRightRegularRepresentation P r level g
          (((e w : U.toSubmodule) :
            LSVAutomorphicL2 P r level))) := by
      rw [hv, hw]
    _ = inner ℂ
        (((e v : U.toSubmodule) : LSVAutomorphicL2 P r level))
        (((e w : U.toSubmodule) : LSVAutomorphicL2 P r level)) :=
      lsvRightRegularRepresentation_isUnitary P r level g _ _
    _ = inner ℂ (e v) (e w) := rfl
    _ = inner ℂ v w := e.inner_map_map v w

/-- Every actual irreducible spherical occurrence may use the inherited
unitarity theorem when discharging the constituent predicate. -/
theorem isLSVSphericalConstituent_of_occurs
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hoccurs : OccursInLSVAutomorphicL2 P r level sigma)
    (hirreducible : Representation.IsIrreducible sigma)
    (hspherical : IsSpherical sigma) :
    IsLSVSphericalConstituent P r level sigma := by
  exact ⟨hoccurs, hirreducible,
    isUnitary_of_occursInLSVAutomorphicL2 P r level sigma hoccurs,
    hspherical⟩

/-- Finite-dimensional and infinite-dimensional spherical constituents form
an exhaustive partition. -/
theorem isLSVTrivial_or_infiniteDimensionalSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hconstituent : IsLSVSphericalConstituent P r level sigma) :
    IsLSVTrivialSphericalConstituent P r level sigma ∨
      IsLSVInfiniteDimensionalSphericalConstituent P r level sigma := by
  by_cases hfinite : Module.Finite ℂ V
  · exact Or.inl ⟨hconstituent, hfinite⟩
  · exact Or.inr ⟨hconstituent, hfinite⟩

/-- The representation-theoretic trivial and infinite-dimensional sectors
are disjoint. -/
theorem not_isLSVTrivial_and_infiniteDimensionalSphericalConstituent
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V) :
    ¬ (IsLSVTrivialSphericalConstituent P r level sigma ∧
      IsLSVInfiniteDimensionalSphericalConstituent P r level sigma) := by
  rintro ⟨⟨_, hfinite⟩, ⟨_, hinfinite⟩⟩
  exact hinfinite hfinite

/-- The final nontrivial joint spectrum.  Nontriviality is imposed on the
witnessing finite-quotient eigenvector, so an eigenvalue shared with a
finite-dimensional determinant-character constituent is not accidentally
deleted. -/
def lsvNontrivialJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  lsvFiniteDetCandidateNontrivialJointSpectrum P r level

theorem mem_lsvNontrivialJointSpectrum_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ) :
    eigenvalue ∈ lsvNontrivialJointSpectrum P r level ↔
      ∃ vector,
        IsLSVJointEigenpair P r level eigenvalue vector ∧
          ¬ IsLSVFiniteDetCharacterVector P r level vector := by
  exact mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
    P r level eigenvalue

/-- The concrete LSV quotient is Ramanujan when its actual nontrivial finite
colored joint spectrum is contained in the checked-in joint approximate
point spectrum of the universal Bruhat--Tits building. -/
def IsLSVRamanujanQuotient
    (P : BasePrime) (r : Rank) (level : Nat) : Prop :=
  lsvNontrivialJointSpectrum P r level ⊆
    lsvUniversalBuildingJointSpectrum P r

theorem isLSVRamanujanQuotient_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsLSVRamanujanQuotient P r level ↔
      ∀ eigenvalue vector,
        IsLSVJointEigenpair P r level eigenvalue vector →
        ¬ IsLSVFiniteDetCharacterVector P r level vector →
        eigenvalue ∈ lsvUniversalBuildingJointSpectrum P r := by
  exact isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
    P r level

/-- Rank-three adapter for the exact LSV05a Proposition 1.5 equivalence.
The complete equivalence remains visible as a theorem argument. -/
theorem rankThree_isLSVRamanujanQuotient_iff_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .three level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .three level sigma →
            IsTempered sigma) :
    IsLSVRamanujanQuotient P .three level ↔
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .three level sigma →
          IsTempered sigma :=
  hLSV05aPropositionOneFive

/-- Forward rank-three adapter consumed downstream after temperedness has
been proved for every actual relevant constituent. -/
theorem rankThree_isLSVRamanujanQuotient_of_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .three level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .three level sigma →
            IsTempered sigma)
    (htempered :
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .three level sigma →
          IsTempered sigma) :
    IsLSVRamanujanQuotient P .three level :=
  hLSV05aPropositionOneFive.mpr htempered

/-- Rank-four adapter for the exact LSV05a Proposition 1.5 equivalence.
The complete equivalence remains visible as a theorem argument. -/
theorem rankFour_isLSVRamanujanQuotient_iff_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .four level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .four level sigma →
            IsTempered sigma) :
    IsLSVRamanujanQuotient P .four level ↔
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .four level sigma →
          IsTempered sigma :=
  hLSV05aPropositionOneFive

/-- Forward rank-four adapter consumed downstream after temperedness has
been proved for every actual relevant constituent. -/
theorem rankFour_isLSVRamanujanQuotient_of_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .four level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .four level sigma →
            IsTempered sigma)
    (htempered :
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .four level sigma →
          IsTempered sigma) :
    IsLSVRamanujanQuotient P .four level :=
  hLSV05aPropositionOneFive.mpr htempered

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
