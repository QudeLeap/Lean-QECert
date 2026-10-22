import QEC.Coding.CodeReduction.DistanceBalancing.Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Removing dependent classical parity checks

The EKZ product is most convenient for a surjective classical boundary.  A
parity-check map need not initially be surjective, but one can retain a basis
chosen from its actual rows.  The resulting matrix is surjective, has exactly
the same kernel, and cannot increase either row or column weight.

This is a finite-dimensional construction, not an assumption about a family.
-/

namespace QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction

open QEC.Coding
open QEC.Coding.DistanceBalancing

universe u

variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]

def rowSet (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Set (Word (ZMod 2) bit) :=
  Set.range (fun b => wordLinearMapTranspose Y (Pi.single b 1))

private theorem exists_independentRows
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    ∃ rows : Finset (Word (ZMod 2) bit),
      ↑rows ⊆ rowSet Y ∧
      Submodule.span (ZMod 2) (rows : Set (Word (ZMod 2) bit)) =
        Submodule.span (ZMod 2) (rowSet Y) ∧
      LinearIndepOn (ZMod 2) id
        (rows : Set (Word (ZMod 2) bit)) := by
  obtain ⟨rows, hsubset, _hcard, hspan, hindependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) (rowSet Y)
  exact ⟨rows, hsubset, hspan, hindependent⟩

noncomputable def independentRows
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Finset (Word (ZMod 2) bit) :=
  Classical.choose (exists_independentRows Y)

theorem independentRows_subset
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    ↑(independentRows Y) ⊆ rowSet Y :=
  (Classical.choose_spec (exists_independentRows Y)).1

theorem span_independentRows
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Submodule.span (ZMod 2)
        (independentRows Y : Set (Word (ZMod 2) bit)) =
      Submodule.span (ZMod 2) (rowSet Y) :=
  (Classical.choose_spec (exists_independentRows Y)).2.1

theorem independent_independentRows
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    LinearIndepOn (ZMod 2) id
      (independentRows Y : Set (Word (ZMod 2) bit)) :=
  (Classical.choose_spec (exists_independentRows Y)).2.2

abbrev ReducedCheck
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :=
  {row // row ∈ (independentRows Y : Set (Word (ZMod 2) bit))}

/-- The matrix consisting of one copy of every selected independent row. -/
noncomputable def reducedMatrix
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Matrix (ReducedCheck Y) bit (ZMod 2) :=
  fun r a => r.1 a

noncomputable def reducedBoundary
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) (ReducedCheck Y) :=
  Matrix.toLin' (reducedMatrix Y)

theorem reducedMatrix_rows_independent
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
  LinearIndependent (ZMod 2) (reducedMatrix Y).row := by
  change LinearIndependent (ZMod 2)
    (fun r : ReducedCheck Y => (r.1 : Word (ZMod 2) bit))
  exact linearIndependent_subtype_iff.mpr (independent_independentRows Y)

/-- Independent rows give a full-row-rank, hence surjective, check map. -/
theorem reducedBoundary_surjective
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Function.Surjective (reducedBoundary Y) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hRank : (reducedMatrix Y).rank = Fintype.card (ReducedCheck Y) :=
    (reducedMatrix_rows_independent Y).rank_matrix
  rw [(reducedMatrix Y).rank_eq_finrank_range_toLin
    (Pi.basisFun (ZMod 2) (ReducedCheck Y))
    (Pi.basisFun (ZMod 2) bit)] at hRank
  rw [Matrix.toLin_eq_toLin'] at hRank
  change Module.finrank (ZMod 2) (LinearMap.range (reducedBoundary Y)) =
    Fintype.card (ReducedCheck Y) at hRank
  calc
    Module.finrank (ZMod 2) (LinearMap.range (reducedBoundary Y)) =
        Fintype.card (ReducedCheck Y) := hRank
    _ = Module.finrank (ZMod 2) (Word (ZMod 2) (ReducedCheck Y)) :=
      (Module.finrank_pi (ZMod 2)).symm

private theorem pairing_row_eq_apply
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (x : Word (ZMod 2) bit) (b : check) :
    wordPairing (wordLinearMapTranspose Y (Pi.single b 1)) x = Y x b := by
  rw [wordPairing_wordLinearMapTranspose]
  exact single_one_dotProduct b (Y x)

theorem ker_reducedBoundary_eq
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    LinearMap.ker (reducedBoundary Y) = LinearMap.ker Y := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext b
    have hrow : wordLinearMapTranspose Y (Pi.single b 1) ∈
        Submodule.span (ZMod 2)
          (independentRows Y : Set (Word (ZMod 2) bit)) := by
      rw [span_independentRows Y]
      exact Submodule.subset_span ⟨b, rfl⟩
    have horth : ∀ v ∈ Submodule.span (ZMod 2)
        (independentRows Y : Set (Word (ZMod 2) bit)),
        wordPairing v x = 0 := by
      intro v hv
      refine Submodule.span_induction (p := fun v _ => wordPairing v x = 0)
        ?_ ?_ ?_ ?_ hv
      · intro v hvRows
        have hvReduced := congrFun hx ⟨v, hvRows⟩
        simpa [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct, wordPairing_apply, mul_comm] using hvReduced
      · simp [wordPairing_apply]
      · intro v w _ _ hv hw
        simp [wordPairing_apply, dotProduct_add, hv, hw]
      · intro c v _ hv
        simp [wordPairing_apply, hv]
    rw [← pairing_row_eq_apply Y x b]
    exact horth _ hrow
  · intro hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext r
    obtain ⟨b, hb⟩ := independentRows_subset Y r.2
    have hpair : wordPairing r.1 x = 0 := by
      rw [← hb, pairing_row_eq_apply Y x b]
      exact congrFun hx b
    simpa [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
      Matrix.mulVec, wordPairing_apply] using hpair

theorem finrank_ker_reducedBoundary
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Module.finrank (ZMod 2) (LinearMap.ker (reducedBoundary Y)) =
      Module.finrank (ZMod 2) (LinearMap.ker Y) := by
  rw [ker_reducedBoundary_eq]

theorem classicalDistanceAtLeast_reducedBoundary
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {d : Nat}
    (hDistance : ClassicalDistanceAtLeast (LinearMap.toMatrix' Y) d) :
    ClassicalDistanceAtLeast
      (LinearMap.toMatrix' (reducedBoundary Y)) d := by
  intro x hx hne
  apply hDistance x
  · rw [Matrix.toLin'_toMatrix'] at hx ⊢
    rw [← LinearMap.mem_ker, ← ker_reducedBoundary_eq Y,
      LinearMap.mem_ker]
    exact hx
  · exact hne

/-- Every selected row is literally an original row, so row weight does not
increase. -/
theorem reducedBoundary_rowWeight
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {w : Nat}
    (hRow : ∀ b, HammingWeight
      (wordLinearMapTranspose Y (Pi.single b 1)) ≤ w) :
    ∀ r, HammingWeight
      (wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1)) ≤ w := by
  intro r
  obtain ⟨b, hb⟩ := independentRows_subset Y r.2
  have hSelected :
      wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1) = r.1 := by
    ext a
    calc
      wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1) a =
          wordPairing (wordLinearMapTranspose (reducedBoundary Y)
            (Pi.single r 1)) (Pi.single a 1) := by
            symm
            exact dotProduct_single_one _ _
      _ = reducedBoundary Y (Pi.single a 1) r :=
        pairing_row_eq_apply (reducedBoundary Y) (Pi.single a 1) r
      _ = r.1 a := by
        simp [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
          Matrix.mulVec, dotProduct_single_one]
  rw [hSelected, ← hb]
  exact hRow b

noncomputable def originalRow
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (r : ReducedCheck Y) : check :=
  Classical.choose (independentRows_subset Y r.2)

theorem originalRow_spec
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (r : ReducedCheck Y) :
    wordLinearMapTranspose Y (Pi.single (originalRow Y r) 1) = r.1 :=
  Classical.choose_spec (independentRows_subset Y r.2)

theorem originalRow_injective
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Function.Injective (originalRow Y) := by
  intro r s hrs
  apply Subtype.ext
  rw [← originalRow_spec Y r, ← originalRow_spec Y s, hrs]

/-- Row reduction never creates more checks than the original matrix had. -/
theorem card_reducedCheck_le
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Fintype.card (ReducedCheck Y) ≤ Fintype.card check := by
  exact Fintype.card_le_of_injective (originalRow Y)
    (originalRow_injective Y)

/-- Deleting rows also cannot increase a column weight. -/
theorem reducedBoundary_columnWeight
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (a : bit) :
    HammingWeight (reducedBoundary Y (Pi.single a 1)) ≤
      HammingWeight (Y (Pi.single a 1)) := by
  classical
  rw [HammingWeight_eq_card_hammingSupport,
    HammingWeight_eq_card_hammingSupport]
  apply Finset.card_le_card_of_injOn (originalRow Y)
  · intro r hr
    have hcoordinate : reducedBoundary Y (Pi.single a 1) r = r.1 a := by
      simp [reducedBoundary, reducedMatrix, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct_single_one]
    have horiginal : Y (Pi.single a 1) (originalRow Y r) = r.1 a := by
      calc
        Y (Pi.single a 1) (originalRow Y r) =
            wordPairing (Pi.single (originalRow Y r) 1)
              (Y (Pi.single a 1)) := by
                symm
                exact single_one_dotProduct _ _
        _ = wordPairing
              (wordLinearMapTranspose Y (Pi.single (originalRow Y r) 1))
              (Pi.single a 1) := by
                symm
                exact wordPairing_wordLinearMapTranspose Y _ _
        _ = wordLinearMapTranspose Y
              (Pi.single (originalRow Y r) 1) a :=
                dotProduct_single_one _ _
        _ = r.1 a := congrFun (originalRow_spec Y r) a
    simpa [hammingSupport, hcoordinate, horiginal] using hr
  · exact (originalRow_injective Y).injOn

end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
