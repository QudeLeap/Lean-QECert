import QEC.Distillation.PrimeQuditProtocol.Protocol
import QEC.Distillation.Core.DependentBatch
import QEC.Semantics.ErrorCorrection.QuditSubsystem
import QEC.Coding.ReedSolomon.Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# KT19 vanishing-overhead route

This module will close the source-backed KT19 asymptotic theorem using the
actual decoded output of the finite protocol.  In particular, a child input is
obtained by a literal singleton-coordinate qudit partial trace; it is not a
freshly prepared density selected from an error parameter.
-/

noncomputable section

namespace QEC.Distillation.KT19VanishingOverhead

open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators

attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype

/-- Finite physical-outcome predicates in this local route use classical
decidability, without adding computable equality assumptions to the register
index types. -/
local instance instKT19VanishingOverheadClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

universe u

/-- The explicit changing-prime retained-degree choice. -/
def kt19ExplicitL (p : Nat) : Nat := p / 4

/-- The explicit changing-prime logical-dimension choice. -/
def kt19ExplicitK (p : Nat) : Nat := p / 8

/-- The elementary source-side parameter conditions for the concrete
changing-prime choice.  The lower cutoff is used only to make all finite
indices nonempty and the shortened stabilizer dimension at least two. -/
theorem kt19ExplicitParameters_admissible (p : Nat) (hp : Nat.Prime p)
    (hlarge : 32 ≤ p) :
    Admissible p (kt19ExplicitL p) (kt19ExplicitK p) := by
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  all_goals simp [kt19ExplicitL, kt19ExplicitK] <;> omega

/-- The selected puncture locations are concretely enumerated by their
canonical residues below `k`.  This local copy is kept private because it is
only needed to display the #884 row family. -/
private noncomputable def kt19SelectedPunctureEquivFin (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) : SelectedPunctureLocation p k ≃ Fin k := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine
    { toFun := fun point => ⟨point.1.val, (Finset.mem_filter.mp point.2).2⟩
      invFun := fun index => ⟨(index.1 : ZMod p), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (index.2.trans_le hkp)]
        exact index.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Subtype.ext
    exact ZMod.natCast_zmod_val point.1
  · intro index
    apply Fin.ext
    change ((index.1 : ZMod p).val) = index.1
    exact ZMod.val_natCast_of_lt (index.2.trans_le hkp)

/-- The selected-coordinate Kronecker word used to interpolate one logical
row of the explicit Reed--Solomon construction. -/
private noncomputable def kt19SelectedDeltaWord (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (index : Fin k) : Word (ZMod p) (SelectedPunctureLocation p k) :=
  fun point => if kt19SelectedPunctureEquivFin p k hkp point = index then 1 else 0

/-- The actual degree-`< k` interpolant of a selected-coordinate word. -/
private noncomputable def kt19SelectedInterpolation (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    Polynomial.degreeLT (ZMod p) k := by
  let equivalence := Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)
  let raw := equivalence.symm word
  refine ⟨raw.1, ?_⟩
  simpa [selectedPunctureLocations_card p k hkp] using raw.2

/-- The explicit logical polynomial is the negative Lagrange delta polynomial
at one selected puncture coordinate. -/
private noncomputable def kt19ExplicitLogicalPolynomial (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (index : Fin k) : Polynomial (ZMod p) :=
  -(kt19SelectedInterpolation p k hkp (kt19SelectedDeltaWord p k hkp index)).1

/-- The common nodal factor vanishing on every selected puncture coordinate. -/
private noncomputable def kt19SelectedNodalPolynomial (p k : Nat) [Fact p.Prime] :
    Polynomial (ZMod p) :=
  Lagrange.nodal (selectedPunctureLocations p k) (fun point : ZMod p => point)

/-- The explicit stabilizer polynomials: the selected nodal factor times the
successive low-degree monomials. -/
private noncomputable def kt19ExplicitStabilizerPolynomial (p l k : Nat)
    [Fact p.Prime] (index : Fin (l - k)) : Polynomial (ZMod p) :=
  kt19SelectedNodalPolynomial p k * Polynomial.X ^ (index : Nat)

/-- The retained logical rows of the changing-prime construction. -/
private noncomputable def kt19ExplicitLogicalRow (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fin k → Word (ZMod p) (KeptPunctureLocation p k) :=
  fun index => restrictKept p k
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp index))

/-- The retained stabilizer rows of the changing-prime construction. -/
private noncomputable def kt19ExplicitStabilizerRow (p l k : Nat) [Fact p.Prime] :
    Fin (l - k) → Word (ZMod p) (KeptPunctureLocation p k) :=
  fun index => restrictKept p k
    (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))

/-- All concrete retained rows in their actual logical/stabilizer tags. -/
private noncomputable def kt19ExplicitRow (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fin k ⊕ Fin (l - k) → Word (ZMod p) (KeptPunctureLocation p k) :=
  Sum.elim (kt19ExplicitLogicalRow p l k hkp) (kt19ExplicitStabilizerRow p l k)

/-- The full polynomial behind each retained displayed row.  Keeping this
local makes the changing-prime carrier proof an actual evaluation argument,
rather than a stored matrix-span assertion. -/
private noncomputable def kt19ExplicitRowPolynomial (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) : Fin k ⊕ Fin (l - k) → Polynomial (ZMod p) :=
  Sum.elim (kt19ExplicitLogicalPolynomial p k hkp)
    (kt19ExplicitStabilizerPolynomial p l k)

private theorem kt19ExplicitRow_eq_restrictKept_evaluation (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (index : Fin k ⊕ Fin (l - k)) :
    kt19ExplicitRow p l k hkp index =
      restrictKept p k (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp index)) := by
  rcases index with index | index <;> rfl

private theorem kt19ExplicitLogicalPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) (index : Fin k) :
    kt19ExplicitLogicalPolynomial p k hkp index ∈ Polynomial.degreeLT (ZMod p) l := by
  apply Submodule.neg_mem
  exact (Polynomial.degreeLT_mono (R := ZMod p) hkl)
    (kt19SelectedInterpolation p k hkp
      (kt19SelectedDeltaWord p k hkp index)).property

private theorem kt19ExplicitStabilizerPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) (index : Fin (l - k)) :
    kt19ExplicitStabilizerPolynomial p l k index ∈ Polynomial.degreeLT (ZMod p) l := by
  rw [Polynomial.mem_degreeLT]
  calc
    (kt19ExplicitStabilizerPolynomial p l k index).degree ≤
        (kt19SelectedNodalPolynomial p k).degree +
          (Polynomial.X ^ (index : Nat) : Polynomial (ZMod p)).degree :=
      Polynomial.degree_mul_le _ _
    _ = (k : WithBot ℕ) + (index : Nat) := by
      rw [kt19SelectedNodalPolynomial,
        Lagrange.degree_nodal, selectedPunctureLocations_card p k hkp]
      simp
    _ < (l : WithBot ℕ) := by
      exact_mod_cast (show k + (index : Nat) < l by omega)

private theorem kt19ExplicitRowPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l)
    (index : Fin k ⊕ Fin (l - k)) :
    kt19ExplicitRowPolynomial p l k hkp index ∈ Polynomial.degreeLT (ZMod p) l := by
  rcases index with index | index
  · exact kt19ExplicitLogicalPolynomial_degreeLT p l k hkp hkl index
  · exact kt19ExplicitStabilizerPolynomial_degreeLT p l k hkp hkl index

/-- The local copy of selected-coordinate interpolation evaluation used by the
explicit row construction.  The public RS module keeps this implementation
lemma private, so the #884 construction rederives it from Lagrange inverse
evaluation. -/
private theorem kt19RestrictSelected_evaluation_selectedInterpolation
    (p k : Nat) [Fact p.Prime] (hkp : k ≤ p)
    (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    restrictSelected p k (evaluationLinearMap p k
      (kt19SelectedInterpolation p k hkp word)) = word := by
  ext point
  change
    ((Lagrange.funEquivDegreeLT
      (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
      (by
        intro left hleft right hright heq
        exact heq)).symm word).1.eval point.1 = word point
  exact congrFun ((Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)).apply_symm_apply word) point

/-- A logical row has exactly its negative selected Kronecker values on the
punctured coordinates. -/
private theorem kt19ExplicitLogical_restrictSelected (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (index : Fin k) :
    restrictSelected p k
      (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp index)) =
        -(kt19SelectedDeltaWord p k hkp index) := by
  ext point
  simpa [kt19ExplicitLogicalPolynomial, evaluationMap] using
    congrArg Neg.neg
      (congrFun (kt19RestrictSelected_evaluation_selectedInterpolation p k hkp
        (kt19SelectedDeltaWord p k hkp index)) point)

/-- Each stabilizer row is literally zero at all selected coordinates because
the common nodal factor vanishes there. -/
private theorem kt19ExplicitStabilizer_restrictSelected_zero (p l k : Nat)
    [Fact p.Prime] (index : Fin (l - k)) :
    restrictSelected p k
      (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index)) = 0 := by
  ext point
  change
    (kt19ExplicitStabilizerPolynomial p l k index).eval point.1 = 0
  rw [kt19ExplicitStabilizerPolynomial, Polynomial.eval_mul,
    kt19SelectedNodalPolynomial,
    Lagrange.eval_nodal_at_node
      (s := selectedPunctureLocations p k)
      (v := fun root : ZMod p => root) (i := point.1) point.2]
  simp

/-- The one polynomial obtained from an arbitrary concrete combination of all
logical and stabilizer rows. -/
private noncomputable def kt19ExplicitCoefficientPolynomial (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p) : Polynomial (ZMod p) :=
  (∑ index : Fin k, u index • kt19ExplicitLogicalPolynomial p k hkp index) +
    ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerPolynomial p l k index

private theorem kt19ExplicitCoefficientPolynomial_degreeLT (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l)
    (u : Fin k → ZMod p) (h : Fin (l - k) → ZMod p) :
    kt19ExplicitCoefficientPolynomial p l k hkp u h ∈ Polynomial.degreeLT (ZMod p) l := by
  apply Submodule.add_mem
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod p) l) fun index _ =>
      Submodule.smul_mem _ _
        (kt19ExplicitLogicalPolynomial_degreeLT p l k hkp hkl index)
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod p) l) fun index _ =>
      Submodule.smul_mem _ _
        (kt19ExplicitStabilizerPolynomial_degreeLT p l k hkp hkl index)

private theorem kt19ExplicitCoefficient_restrictKept (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p) :
    restrictKept p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) =
        (∑ index : Fin k, u index • kt19ExplicitLogicalRow p l k hkp index) +
          ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerRow p l k index := by
  ext point
  simp only [restrictKept_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    kt19ExplicitLogicalRow, kt19ExplicitStabilizerRow, evaluationMap]
  rw [kt19ExplicitCoefficientPolynomial, Polynomial.eval_add,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply,
    Polynomial.eval_C_mul, Algebra.algebraMap_self_apply]

private theorem kt19ExplicitCoefficient_eq_zero_of_restrictKept_zero
    (p l k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l)
    (hlength : l ≤ p - k) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p)
    (hzero : (∑ index : Fin k, u index • kt19ExplicitLogicalRow p l k hkp index) +
      ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerRow p l k index = 0) :
    kt19ExplicitCoefficientPolynomial p l k hkp u h = 0 := by
  have hreduced : restrictKept p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) = 0 := by
    rw [kt19ExplicitCoefficient_restrictKept]
    exact hzero
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (keptPunctureLocations p k)
  · exact (Polynomial.mem_degreeLT.mp
      (kt19ExplicitCoefficientPolynomial_degreeLT p l k hkp hkl u h)).trans_le
        (by simpa [keptPunctureLocations_card p k hkp] using hlength)
  · exact WithBot.bot_lt_coe (keptPunctureLocations p k).card
  · intro point hpoint
    have hvalue := congrFun hreduced ⟨point, hpoint⟩
    simpa [evaluationMap] using hvalue

private theorem kt19ExplicitCoefficient_restrictSelected (p l k : Nat)
    [Fact p.Prime] (hkp : k ≤ p) (u : Fin k → ZMod p)
    (h : Fin (l - k) → ZMod p) :
    restrictSelected p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) =
        ∑ index : Fin k, u index •
          -(kt19SelectedDeltaWord p k hkp index) := by
  ext point
  have hlogical (index : Fin k) :
      (kt19ExplicitLogicalPolynomial p k hkp index).eval point.1 =
        -kt19SelectedDeltaWord p k hkp index point := by
    simpa [evaluationMap] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp index) point
  have hstabilizer (index : Fin (l - k)) :
      (kt19ExplicitStabilizerPolynomial p l k index).eval point.1 = 0 := by
    simpa [evaluationMap] using congrFun
      (kt19ExplicitStabilizer_restrictSelected_zero p l k index) point
  simp only [restrictSelected_apply, Finset.sum_apply, Pi.smul_apply, evaluationMap]
  rw [kt19ExplicitCoefficientPolynomial, Polynomial.eval_add,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp [Algebra.smul_def, Polynomial.algebraMap_apply,
    Polynomial.eval_C_mul, Algebra.algebraMap_self_apply, hlogical, hstabilizer]

private theorem kt19SelectedDelta_coefficients_zero (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (u : Fin k → ZMod p)
    (hzero : ∑ index : Fin k, u index •
      -(kt19SelectedDeltaWord p k hkp index) = 0) : u = 0 := by
  funext index
  have hpoint := congrFun hzero
    ((kt19SelectedPunctureEquivFin p k hkp).symm index)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply] at hpoint
  rw [Fintype.sum_eq_single index] at hpoint
  · have hneg : -u index = 0 := by
      simpa [kt19SelectedDeltaWord] using hpoint
    exact neg_eq_zero.mp hneg
  · intro other hne
    have hindexOther : index ≠ other := Ne.symm hne
    simp [kt19SelectedDeltaWord, hindexOther]

private theorem kt19ExplicitStabilizerCombination_factor (p l k : Nat)
    [Fact p.Prime] (h : Fin (l - k) → ZMod p) :
    ∑ index : Fin (l - k), h index •
      kt19ExplicitStabilizerPolynomial p l k index =
        kt19SelectedNodalPolynomial p k *
          ∑ index : Fin (l - k), h index • (Polynomial.X ^ (index : Nat)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp [kt19ExplicitStabilizerPolynomial, Algebra.smul_def]
  ring

private theorem kt19SelectedNodalPolynomial_ne_zero (p k : Nat) [Fact p.Prime] :
    kt19SelectedNodalPolynomial p k ≠ 0 := by
  simpa [kt19SelectedNodalPolynomial] using
    (Lagrange.nodal_monic (s := selectedPunctureLocations p k)
      (v := fun point : ZMod p => point)).ne_zero

private theorem kt19MonomialCoefficients_zero (p n : Nat) [Fact p.Prime]
    (h : Fin n → ZMod p)
    (hzero : ∑ index : Fin n, h index •
      (Polynomial.X ^ (index : Nat) : Polynomial (ZMod p)) = 0) : h = 0 := by
  funext index
  have hcoeff := congrArg (fun polynomial : Polynomial (ZMod p) =>
    polynomial.coeff (index : Nat)) hzero
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  rw [Fintype.sum_eq_single index] at hcoeff
  · simpa using hcoeff
  · intro other hne
    have hcoerce : (index : Nat) ≠ (other : Nat) := by
      intro hvalue
      exact hne (Fin.ext hvalue).symm
    simp [hcoerce]

private theorem kt19Explicit_rows_independent (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (u : Fin k → ZMod p) (h : Fin (l - k) → ZMod p)
    (hzero : (∑ index : Fin k, u index • kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) index) +
      ∑ index : Fin (l - k), h index • kt19ExplicitStabilizerRow p l k index = 0) :
    u = 0 ∧ h = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hlength : l ≤ p - k := by omega
  have hpolynomial : kt19ExplicitCoefficientPolynomial p l k hkp u h = 0 :=
    kt19ExplicitCoefficient_eq_zero_of_restrictKept_zero p l k hkp hkl hlength u h
      (by simpa using hzero)
  have hselected : restrictSelected p k (evaluationMap p
      (kt19ExplicitCoefficientPolynomial p l k hkp u h)) = 0 := by
    rw [hpolynomial]
    ext point
    simp [evaluationMap]
  rw [kt19ExplicitCoefficient_restrictSelected] at hselected
  have hu : u = 0 := kt19SelectedDelta_coefficients_zero p k hkp u hselected
  have hstabilizer : ∑ index : Fin (l - k), h index •
      kt19ExplicitStabilizerPolynomial p l k index = 0 := by
    rw [kt19ExplicitCoefficientPolynomial, hu] at hpolynomial
    simpa using hpolynomial
  rw [kt19ExplicitStabilizerCombination_factor] at hstabilizer
  have hmonomial : ∑ index : Fin (l - k), h index •
      (Polynomial.X ^ (index : Nat) : Polynomial (ZMod p)) = 0 := by
    exact (mul_eq_zero.mp hstabilizer).resolve_left
      (kt19SelectedNodalPolynomial_ne_zero p k)
  exact ⟨hu, kt19MonomialCoefficients_zero p (l - k) h hmonomial⟩

/-- The literal span of the displayed nodal rows.  This is intentionally kept
private: the public family exposes the same span through `stabilizerCarrier`. -/
private noncomputable def kt19ExplicitStabilizerCarrier (p l k : Nat) [NeZero p]
    [Fact p.Prime] :
    Submodule (ZMod p) (PrimeQuditRegisterLabel p (KeptPunctureLocation p k)) :=
  Submodule.span (ZMod p) (Set.range (kt19ExplicitStabilizerRow p l k))

private theorem kt19ExplicitStabilizer_mem_shortened (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) (index : Fin (l - k)) :
    kt19ExplicitStabilizerRow p l k index ∈
      (shortenedReedSolomonCode p l k).carrier := by
  apply (mem_shortenedReedSolomonCode _).2
  refine ⟨evaluationLinearMap p l
    ⟨kt19ExplicitStabilizerPolynomial p l k index,
      kt19ExplicitStabilizerPolynomial_degreeLT p l k hkp hkl index⟩, ?_, ?_, ?_⟩
  · exact evaluation_mem_reedSolomonCode p l _
  · exact kt19ExplicitStabilizer_restrictSelected_zero p l k index
  · rfl

private theorem kt19ExplicitStabilizerCarrier_le_shortened (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) :
    kt19ExplicitStabilizerCarrier p l k ≤
      (shortenedReedSolomonCode p l k).carrier := by
  rw [kt19ExplicitStabilizerCarrier]
  apply Submodule.span_le.2
  rintro word ⟨index, rfl⟩
  exact kt19ExplicitStabilizer_mem_shortened p l k hkp hkl index

private theorem kt19Explicit_stabilizer_rows_linearIndependent (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hadmissible : Admissible p l k) :
    LinearIndependent (ZMod p) (kt19ExplicitStabilizerRow p l k) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hzero index
  have hboth := kt19Explicit_rows_independent p l k hadmissible 0 coefficient
    (by simpa using hzero)
  simpa using congrFun hboth.2 index

private theorem kt19ExplicitStabilizerCarrier_finrank (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k) :
    Module.finrank (ZMod p) (kt19ExplicitStabilizerCarrier p l k) = l - k := by
  rw [kt19ExplicitStabilizerCarrier]
  simpa using finrank_span_eq_card
    (kt19Explicit_stabilizer_rows_linearIndependent p l k hadmissible)

private theorem kt19ExplicitStabilizerCarrier_eq_shortened (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hadmissible : Admissible p l k) :
    kt19ExplicitStabilizerCarrier p l k =
      (shortenedReedSolomonCode p l k).carrier := by
  have hkp : k ≤ p := hadmissible.2.2.1.trans hadmissible.2.2.2.1
  apply Submodule.eq_of_le_of_finrank_eq
    (kt19ExplicitStabilizerCarrier_le_shortened p l k hkp hadmissible.2.2.1)
  rw [kt19ExplicitStabilizerCarrier_finrank p l k hadmissible]
  simpa [Dimension_eq_finrank_carrier] using
    (shortenedReedSolomonCode_dimension p l k hkp hadmissible.2.2.1
      hadmissible.2.2.2.1).symm

/-- Full-code cubic orthogonality for any three displayed generic rows. -/
private theorem kt19Explicit_full_cubic_zero (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (left middle right : Fin k ⊕ Fin (l - k)) :
    cubicPairing p
      (evaluationMap p (kt19ExplicitRowPolynomial p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) left))
      (evaluationMap p (kt19ExplicitRowPolynomial p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) middle))
      (evaluationMap p (kt19ExplicitRowPolynomial p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) right)) = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, htriple⟩
  have hkp : k ≤ p := hkl.trans hlp
  let leftBounded : Polynomial.degreeLT (ZMod p) l :=
    ⟨kt19ExplicitRowPolynomial p l k hkp left,
      kt19ExplicitRowPolynomial_degreeLT p l k hkp hkl left⟩
  let middleBounded : Polynomial.degreeLT (ZMod p) l :=
    ⟨kt19ExplicitRowPolynomial p l k hkp middle,
      kt19ExplicitRowPolynomial_degreeLT p l k hkp hkl middle⟩
  let rightBounded : Polynomial.degreeLT (ZMod p) l :=
    ⟨kt19ExplicitRowPolynomial p l k hkp right,
      kt19ExplicitRowPolynomial_degreeLT p l k hkp hkl right⟩
  have hleft : evaluationLinearMap p l leftBounded ∈ (reedSolomonCode p l).carrier :=
    evaluation_mem_reedSolomonCode p l leftBounded
  have hmiddle : evaluationLinearMap p l middleBounded ∈ (reedSolomonCode p l).carrier :=
    evaluation_mem_reedSolomonCode p l middleBounded
  have hright : evaluationLinearMap p l rightBounded ∈ (reedSolomonCode p l).carrier :=
    evaluation_mem_reedSolomonCode p l rightBounded
  have hproduct : coordinatewiseProduct (evaluationLinearMap p l leftBounded)
      (evaluationLinearMap p l middleBounded) ∈ (reedSolomonCode p l).dual.carrier := by
    apply reedSolomonCode_product_le_dual p l htriple
    rw [coordinatewiseProductCode]
    exact Submodule.subset_span ⟨evaluationLinearMap p l leftBounded, hleft,
      evaluationLinearMap p l middleBounded, hmiddle, rfl⟩
  have horthogonal := ((reedSolomonCode p l).mem_dual _).1 hproduct
    (evaluationLinearMap p l rightBounded) hright
  exact horthogonal

/-- Splitting the literal finite field into retained and selected puncture
coordinates for a cubic pairing. -/
private theorem kt19Explicit_retained_cubic_add_selected_cubic_eq_full
    (p k : Nat) [NeZero p] [Fact p.Prime]
    (left middle right : Word (ZMod p) (ZMod p)) :
    cubicPairing p (restrictKept p k left) (restrictKept p k middle)
      (restrictKept p k right) +
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * middle point.1 * right point.1) = cubicPairing p left middle right := by
  classical
  change (∑ point : KeptPunctureLocation p k,
      left point.1 * middle point.1 * right point.1) +
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * middle point.1 * right point.1) =
    ∑ point : ZMod p, left point * middle point * right point
  rw [Finset.sum_coe_sort (keptPunctureLocations p k)
      (fun point => left point * middle point * right point),
    Finset.sum_coe_sort (selectedPunctureLocations p k)
      (fun point => left point * middle point * right point)]
  simpa [keptPunctureLocations] using
    (Finset.sum_filter_not_add_sum_filter
      (Finset.univ : Finset (ZMod p))
      (fun point => point ∈ selectedPunctureLocations p k)
      (fun point => left point * middle point * right point))

private theorem kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero
    (p k : Nat) [NeZero p] [Fact p.Prime]
    (left middle right : Word (ZMod p) (ZMod p))
    (hselectedSum :
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * middle point.1 * right point.1) = 0) :
    cubicPairing p (restrictKept p k left) (restrictKept p k middle)
      (restrictKept p k right) = cubicPairing p left middle right := by
  have hsplit := kt19Explicit_retained_cubic_add_selected_cubic_eq_full p k left middle right
  rw [hselectedSum, add_zero] at hsplit
  exact hsplit

private theorem kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero
    (p k : Nat) [NeZero p] [Fact p.Prime]
    (left middle right : Word (ZMod p) (ZMod p))
    (hselected : restrictSelected p k left = 0) :
    (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
      left point.1 * middle point.1 * right point.1) = 0 := by
  apply Finset.sum_eq_zero
  intro point _
  have hpoint : left point.1 = 0 := by
    simpa using congrFun hselected
      (⟨point.1, point.2⟩ : SelectedPunctureLocation p k)
  rw [hpoint]
  simp

/-- Distinct selected Kronecker coordinates have zero triple product unless
all three logical indices agree. -/
private theorem kt19SelectedDeltaWord_triple_product_zero (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (left middle right : Fin k)
    (hnot : ¬ (left = middle ∧ middle = right))
    (point : SelectedPunctureLocation p k) :
    kt19SelectedDeltaWord p k hkp left point *
        kt19SelectedDeltaWord p k hkp middle point *
          kt19SelectedDeltaWord p k hkp right point = 0 := by
  by_cases hleftMiddle : left = middle
  · subst middle
    have hleftRight : left ≠ right := by
      intro hleftRight
      exact hnot ⟨rfl, hleftRight⟩
    by_cases hpoint : kt19SelectedPunctureEquivFin p k hkp point = left
    · simp [kt19SelectedDeltaWord, hpoint, hleftRight]
    · simp [kt19SelectedDeltaWord, hpoint]
  · by_cases hpoint : kt19SelectedPunctureEquivFin p k hkp point = left
    · simp [kt19SelectedDeltaWord, hpoint, hleftMiddle]
    · simp [kt19SelectedDeltaWord, hpoint]

private theorem kt19ExplicitLogical_selected_triple_sum_zero (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hkp : k ≤ p) (left middle right : Fin k)
    (hnot : ¬ (left = middle ∧ middle = right)) :
    (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
      evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp left) point.1 *
        evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp middle) point.1 *
          evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp right) point.1) = 0 := by
  apply Finset.sum_eq_zero
  intro point _
  let selectedPoint : SelectedPunctureLocation p k := ⟨point.1, point.2⟩
  have hleft : evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp left) point.1 =
      -kt19SelectedDeltaWord p k hkp left selectedPoint := by
    simpa [selectedPoint] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp left) selectedPoint
  have hmiddle : evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp middle) point.1 =
      -kt19SelectedDeltaWord p k hkp middle selectedPoint := by
    simpa [selectedPoint] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp middle) selectedPoint
  have hright : evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp right) point.1 =
      -kt19SelectedDeltaWord p k hkp right selectedPoint := by
    simpa [selectedPoint] using congrFun
      (kt19ExplicitLogical_restrictSelected p l k hkp right) selectedPoint
  rw [hleft, hmiddle, hright]
  calc
    (-kt19SelectedDeltaWord p k hkp left selectedPoint) *
        (-kt19SelectedDeltaWord p k hkp middle selectedPoint) *
          (-kt19SelectedDeltaWord p k hkp right selectedPoint) =
        -(kt19SelectedDeltaWord p k hkp left selectedPoint *
          kt19SelectedDeltaWord p k hkp middle selectedPoint *
            kt19SelectedDeltaWord p k hkp right selectedPoint) := by ring
    _ = 0 := by
      rw [kt19SelectedDeltaWord_triple_product_zero p k hkp left middle right hnot]
      simp

private theorem kt19Explicit_stabilizer_triple_zero (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (left middle right : Fin k ⊕ Fin (l - k))
    (hcontains : (∃ index, left = Sum.inr index) ∨
      (∃ index, middle = Sum.inr index) ∨ (∃ index, right = Sum.inr index)) :
    cubicPairing p
      (kt19ExplicitRow p l k (hadmissible.2.2.1.trans hadmissible.2.2.2.1) left)
      (kt19ExplicitRow p l k (hadmissible.2.2.1.trans hadmissible.2.2.2.1) middle)
      (kt19ExplicitRow p l k (hadmissible.2.2.1.trans hadmissible.2.2.2.1) right) = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, htriple⟩
  have hkp : k ≤ p := hkl.trans hlp
  let hadmissible : Admissible p l k := ⟨hp, hk, hkl, hlp, htriple⟩
  rcases hcontains with ⟨index, rfl⟩ | ⟨index, rfl⟩ | ⟨index, rfl⟩
  · rw [kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp (Sum.inr index),
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp middle,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp right]
    simp only [kt19ExplicitRowPolynomial, Sum.elim_inr]
    calc
      _ = cubicPairing p
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right)) :=
        kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right))
          (kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero p k _ _ _
            (kt19ExplicitStabilizer_restrictSelected_zero p l k index))
      _ = 0 := kt19Explicit_full_cubic_zero p l k hadmissible
        (Sum.inr index) middle right
  · rw [kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp left,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp (Sum.inr index),
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp right]
    simp only [kt19ExplicitRowPolynomial, Sum.elim_inr]
    calc
      _ = cubicPairing p
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right)) :=
        kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero p k
                (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp right))
                (kt19ExplicitStabilizer_restrictSelected_zero p l k index)))
      _ = 0 := kt19Explicit_full_cubic_zero p l k hadmissible
        left (Sum.inr index) right
  · rw [kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp left,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp middle,
      kt19ExplicitRow_eq_restrictKept_evaluation p l k hkp (Sum.inr index)]
    simp only [kt19ExplicitRowPolynomial, Sum.elim_inr]
    calc
      _ = cubicPairing p
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index)) :=
        kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
          (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
          (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (kt19Explicit_selected_cubic_sum_zero_of_restrictSelected_zero p k
                (evaluationMap p (kt19ExplicitStabilizerPolynomial p l k index))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp left))
                (evaluationMap p (kt19ExplicitRowPolynomial p l k hkp middle))
                (kt19ExplicitStabilizer_restrictSelected_zero p l k index)))
      _ = 0 := kt19Explicit_full_cubic_zero p l k hadmissible
        left middle (Sum.inr index)

private theorem kt19Explicit_logical_offDiagonal_zero (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k)
    (left middle right : Fin k)
    (hnot : ¬ (left = middle ∧ middle = right)) :
    cubicPairing p
      (kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) left)
      (kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) middle)
      (kt19ExplicitLogicalRow p l k
        (hadmissible.2.2.1.trans hadmissible.2.2.2.1) right) = 0 := by
  rcases hadmissible with ⟨hp, hk, hkl, hlp, htriple⟩
  have hkp : k ≤ p := hkl.trans hlp
  let hadmissible : Admissible p l k := ⟨hp, hk, hkl, hlp, htriple⟩
  have hselected := kt19ExplicitLogical_selected_triple_sum_zero p l k hkp
    left middle right hnot
  have htransport := kt19Explicit_cubic_restrict_eq_full_of_selected_sum_zero p k
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp left))
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp middle))
    (evaluationMap p (kt19ExplicitLogicalPolynomial p k hkp right)) hselected
  simpa [kt19ExplicitLogicalRow] using htransport.trans
    (kt19Explicit_full_cubic_zero p l k hadmissible
      (Sum.inl left) (Sum.inl middle) (Sum.inl right))

/-- The actual generic KT19 cubic rows, constructed from Lagrange deltas and
the selected nodal factor rather than stored as a matrix with asserted laws. -/
noncomputable def kt19ExplicitCubicRowFamily (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k) :
    CubicRowFamily p (Fin k) (Fin (l - k)) (KeptPunctureLocation p k) := by
  let hkp : k ≤ p := hadmissible.2.2.1.trans hadmissible.2.2.2.1
  exact
    { logicalRow := kt19ExplicitLogicalRow p l k hkp
      stabilizerRow := kt19ExplicitStabilizerRow p l k
      rowIndependent := kt19Explicit_rows_independent p l k hadmissible
      stabilizerTriple_zero := kt19Explicit_stabilizer_triple_zero p l k hadmissible
      logicalTriple_offDiagonal_zero := kt19Explicit_logical_offDiagonal_zero p l k hadmissible }

/-- The stabilizer part of the explicit row family is the literal shortened
Reed--Solomon carrier, proved by its row span and dimension. -/
theorem kt19ExplicitCubicRowFamily_stabilizerCarrier (p l k : Nat) [NeZero p]
    [Fact p.Prime] (hadmissible : Admissible p l k) :
    stabilizerCarrier (kt19ExplicitCubicRowFamily p l k hadmissible) =
      (shortenedReedSolomonCode p l k).carrier := by
  simpa [stabilizerCarrier, kt19ExplicitCubicRowFamily,
    kt19ExplicitStabilizerCarrier] using
    (kt19ExplicitStabilizerCarrier_eq_shortened p l k hadmissible)

/-- The explicit Lagrange/nodal rows form an actual physical KT19 family for
every fixed prime and admissible source-safe parameter triple.  The family
contains only concrete row/code data; its run, success, error, and cost are
all derived by the public #883 interfaces. -/
noncomputable def kt19ExplicitFixedPrimeDistillationFamily (p l k : Nat)
    [NeZero p] [Fact p.Prime] (hfive : 5 ≤ p)
    (hadmissible : Admissible p l k) :
    KT19DistillationFamily p l k := by
  exact
    { primeAtLeastFive := ⟨Fact.out, hfive⟩
      admissible := hadmissible
      rowFamily := kt19ExplicitCubicRowFamily p l k hadmissible
      stabilizerCarrier_eq_shortened :=
        kt19ExplicitCubicRowFamily_stabilizerCarrier p l k hadmissible }

/-- The concrete changing-prime KT19 family used by the asymptotic route. -/
noncomputable def kt19ExplicitDistillationFamily (p : Nat) [NeZero p]
    [Fact p.Prime] (hlarge : 32 ≤ p) :
    KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p) := by
  let hadmissible : Admissible p (kt19ExplicitL p) (kt19ExplicitK p) :=
    kt19ExplicitParameters_admissible p Fact.out hlarge
  exact kt19ExplicitFixedPrimeDistillationFamily p (kt19ExplicitL p)
    (kt19ExplicitK p) (by omega) hadmissible

/-- Split the register pairing at one literal output coordinate.  This is kept
private because it is only the bookkeeping step for the physical #884
selected-port marginal. -/
private theorem kt19RegisterPairing_split_port (p k : Nat) [NeZero p]
    (port : Fin k) (e x : PrimeQuditRegisterLabel p (Fin k)) :
    registerPairing p e x = e port * x port +
      ∑ site : {site : Fin k // site ≠ port}, e site * x site := by
  unfold registerPairing
  rw [Fintype.sum_eq_add_sum_subtype_ne _ port]

/-- Split the cubic phase exponent at one literal output coordinate. -/
private theorem kt19CubicExponent_split_port (p k : Nat) [NeZero p]
    (port : Fin k) (x : PrimeQuditRegisterLabel p (Fin k)) :
    cubicExponent p x = x port ^ 3 +
      ∑ site : {site : Fin k // site ≠ port}, x site ^ 3 := by
  unfold cubicExponent
  rw [Fintype.sum_eq_add_sum_subtype_ne _ port]

/-- The concrete computational-label relabeling from a prime-qudit register
to the coordinate model used by `QuditSubsystem`. -/
private def kt19PrimeQuditLabelEquiv (p : Nat) [NeZero p] (Site : Type u)
    [Fintype Site] [DecidableEq Site] :
    PrimeQuditRegisterLabel p Site ≃ Qudit.Label (fun _ : Site => p) where
  toFun label site := (ZMod.finEquiv p).symm (label site)
  invFun label site := ZMod.finEquiv p (label site)
  left_inv label := by
    funext site
    exact (ZMod.finEquiv p).apply_symm_apply (label site)
  right_inv label := by
    funext site
    exact (ZMod.finEquiv p).symm_apply_apply (label site)

/-- The preceding explicit computational-basis relabeling as a unitary
transport.  It changes no physical state; it only exposes the coordinate
factorization required for a literal selected partial trace. -/
private noncomputable def kt19PrimeQuditRegisterQuditTransport
    (p : Nat) [NeZero p] (Site : Type u) [Fintype Site] [DecidableEq Site] :
    UnitaryTransport (PrimeQuditRegister p Site)
      (Qudit.QuditRegister (fun _ : Site => p)) := by
  let sourceBasis := EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex
  let targetBasis := EuclideanSpace.basisFun (Qudit.Label (fun _ : Site => p)) Complex
  let E := sourceBasis.equiv targetBasis (kt19PrimeQuditLabelEquiv p Site)
  exact
    { toLinearEquiv := E.toLinearEquiv
      map_inner := E.inner_map_map }

@[simp] private theorem kt19PrimeQuditRegisterQuditTransport_apply_basis
    (p : Nat) [NeZero p] (Site : Type u) [Fintype Site] [DecidableEq Site]
    (label : PrimeQuditRegisterLabel p Site) :
    kt19PrimeQuditRegisterQuditTransport p Site
      (EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex label) =
        EuclideanSpace.basisFun (Qudit.Label (fun _ : Site => p)) Complex
          (kt19PrimeQuditLabelEquiv p Site label) := by
  dsimp [kt19PrimeQuditRegisterQuditTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The prime-register basis relabeling evaluates a transported state at the
inverse corresponding `ZMod` label. -/
private theorem kt19PrimeQuditRegisterQuditTransport_apply
    (p : Nat) [NeZero p] (Site : Type u) [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : Qudit.Label (fun _ : Site => p)) :
    kt19PrimeQuditRegisterQuditTransport p Site psi label =
      psi ((kt19PrimeQuditLabelEquiv p Site).symm label) := by
  have hinner := (kt19PrimeQuditRegisterQuditTransport p Site).map_inner
    (EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex
      ((kt19PrimeQuditLabelEquiv p Site).symm label)) psi
  rw [kt19PrimeQuditRegisterQuditTransport_apply_basis,
    (kt19PrimeQuditLabelEquiv p Site).apply_symm_apply,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner] at hinner
  exact hinner

/-- The literal singleton output-coordinate subsystem of a KT19 logical
register. -/
noncomputable def kt19SelectedPortSubsystem (p k : Nat) [NeZero p]
    (port : Fin k) : QuditSubsystem (fun _ : Fin k => p) where
  selected := {port}

private def kt19SelectedPortCoordinate (p k : Nat) [NeZero p]
    (port : Fin k) : (kt19SelectedPortSubsystem p k port).SelectedCoordinates :=
  ⟨port, by simp [kt19SelectedPortSubsystem]⟩

/-- The selected coordinate is explicitly relabeled as the same one-site
carrier used by a subsequent KT19 resource input. -/
private def kt19SelectedPortLabelEquiv (p k : Nat) [NeZero p]
    (port : Fin k) :
    Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions ≃
      PrimeQuditRegisterLabel p (KT19SingleResourceSite.{0}) where
  toFun label _ := ZMod.finEquiv p (label (kt19SelectedPortCoordinate p k port))
  invFun label selected := (ZMod.finEquiv p).symm (label default)
  left_inv label := by
    funext selected
    have hselected : selected = kt19SelectedPortCoordinate p k port := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp selected.property
    rw [hselected]
    simp [kt19SelectedPortCoordinate]
  right_inv label := by
    funext site
    have hsite : site = default := Subsingleton.elim _ _
    rw [hsite]
    simp

/-- The singleton selected-coordinate carrier, transported to the actual
one-site KT19 input carrier rather than identified by dimension alone. -/
private noncomputable def kt19SelectedPortTransport (p k : Nat) [NeZero p]
    (port : Fin k) :
    UnitaryTransport (kt19SelectedPortSubsystem p k port).selectedSystem
      (KT19SingleQudit.{0} p) := by
  let sourceBasis := EuclideanSpace.basisFun
    (Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) Complex
  let targetBasis := EuclideanSpace.basisFun
    (PrimeQuditRegisterLabel p KT19SingleResourceSite.{0}) Complex
  let E := sourceBasis.equiv targetBasis (kt19SelectedPortLabelEquiv p k port)
  exact
    { toLinearEquiv := E.toLinearEquiv
      map_inner := E.inner_map_map }

@[simp] private theorem kt19SelectedPortTransport_apply_basis (p k : Nat) [NeZero p]
    (port : Fin k)
    (label : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) :
    kt19SelectedPortTransport p k port
      (EuclideanSpace.basisFun
        (Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) Complex label) =
        EuclideanSpace.basisFun
          (PrimeQuditRegisterLabel p KT19SingleResourceSite.{0}) Complex
          (kt19SelectedPortLabelEquiv p k port label) := by
  dsimp [kt19SelectedPortTransport]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- Evaluation after transporting a singleton selected factor back to its
coordinate carrier is exactly evaluation at the explicitly corresponding
one-site KT19 label. -/
private theorem kt19SelectedPortTransport_symm_apply (p k : Nat) [NeZero p]
    (port : Fin k) (psi : KT19SingleQudit.{0} p)
    (label : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) :
    (kt19SelectedPortTransport p k port).symm psi label =
      psi (kt19SelectedPortLabelEquiv p k port label) := by
  have hinner := (kt19SelectedPortTransport p k port).map_inner
    (EuclideanSpace.basisFun
      (Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) Complex label)
    ((kt19SelectedPortTransport p k port).symm psi)
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [kt19SelectedPortTransport_apply_basis, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

/-- Every coordinate of the singleton selected factor has the positive local
dimension of the underlying prime qudit. -/
private theorem kt19SelectedPortDimensions_pos (p k : Nat) [NeZero p]
    (port : Fin k) :
    ∀ coordinate, 0 < (kt19SelectedPortSubsystem p k port).selectedDimensions coordinate := by
  intro coordinate
  exact Nat.pos_of_ne_zero (NeZero.ne p)

/-- A fixed computational-basis coordinate for defining the complementary
factor of a sitewise magic ket by a nonzero amplitude ratio.  This avoids any
identification of the physical output with a freshly prepared resource. -/
private def kt19SelectedPortZeroLabel (p k : Nat) [NeZero p]
    (port : Fin k) :
    Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions :=
  Qudit.zeroLabel _ (kt19SelectedPortDimensions_pos p k port)

/-- The selected tensor factor of one concrete magic-register word, already
transported to the actual one-site KT19 carrier. -/
private noncomputable def kt19SelectedPortMagicState (p k : Nat) [NeZero p]
    (port : Fin k) (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortSubsystem p k port).selectedSystem :=
  (kt19SelectedPortTransport p k port).symm
    (magicRegisterKet p (kt19SingleSiteLabel (label port)))

/-- The complementary tensor factor is defined from the global state at a
fixed selected coordinate divided by the corresponding nonzero selected
magic amplitude.  The subsequent local factorization proof establishes both
the exact product identity and its normalization. -/
private noncomputable def kt19SelectedPortComplementState (p k : Nat) [NeZero p]
    (port : Fin k) (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortSubsystem p k port).complementSystem :=
  WithLp.toLp 2 (fun right =>
    (((kt19PrimeQuditRegisterQuditTransport p (Fin k)) (magicRegisterKet p label)).ofLp
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right))) /
      (kt19SelectedPortMagicState p k port label).ofLp
        (kt19SelectedPortZeroLabel p k port))

/-- Evaluate the inverse concrete coordinate factorization on a pure tensor. -/
private theorem kt19SelectedPortRegisterFactorization_symm_tmul_apply
    (p k : Nat) [NeZero p] (port : Fin k)
    (leftState : (kt19SelectedPortSubsystem p k port).selectedSystem)
    (rightState : (kt19SelectedPortSubsystem p k port).complementSystem)
    (labels : Qudit.Label (fun _ : Fin k => p)) :
    (kt19SelectedPortSubsystem p k port).registerFactorization.symm
        (leftState ⊗ₜ[Complex] rightState) labels =
      leftState ((kt19SelectedPortSubsystem p k port).splitLabel labels).1 *
        rightState ((kt19SelectedPortSubsystem p k port).splitLabel labels).2 := by
  have hinner := (kt19SelectedPortSubsystem p k port).registerFactorization.map_inner
    (EuclideanSpace.basisFun _ Complex labels)
    ((kt19SelectedPortSubsystem p k port).registerFactorization.symm
      (leftState ⊗ₜ[Complex] rightState))
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [QuditSubsystem.registerFactorization_apply_basis, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm

/-- The source-label representative of a recombined singleton coordinate is
the corresponding selected qudit label. -/
private theorem kt19PrimeQuditLabelEquiv_symm_recombine_apply_port
    (p k : Nat) [NeZero p] (port : Fin k)
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    (kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)) port =
      ZMod.finEquiv p (left (kt19SelectedPortCoordinate p k port)) := by
  simp [kt19PrimeQuditLabelEquiv, QuditSubsystem.recombineLabel,
    kt19SelectedPortSubsystem, kt19SelectedPortCoordinate]

/-- Away from the selected singleton, recombination reads the literal
complementary coordinate. -/
private theorem kt19PrimeQuditLabelEquiv_symm_recombine_apply_ne
    (p k : Nat) [NeZero p] (port : Fin k)
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions)
    (site : {site : Fin k // site ≠ port}) :
    (kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)) site =
      ZMod.finEquiv p (right ⟨site, by simpa [kt19SelectedPortSubsystem] using site.property⟩) := by
  simp [kt19PrimeQuditLabelEquiv, QuditSubsystem.recombineLabel,
    kt19SelectedPortSubsystem, site.property]

/-- The fixed selected-zero anchor has literal prime-field label zero at the
selected coordinate. -/
private theorem kt19PrimeQuditLabelEquiv_symm_recombine_zero_apply_port
    (p k : Nat) [NeZero p] (port : Fin k)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    (kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right)) port = 0 := by
  rw [kt19PrimeQuditLabelEquiv_symm_recombine_apply_port]
  simp [kt19SelectedPortZeroLabel, Qudit.zeroLabel]

/-- The selected magic amplitude at the anchor is nonzero, so the local
complement ratio is an honest physical vector coordinate. -/
private theorem kt19SelectedPortMagicState_zero_ne_zero
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortMagicState p k port label).ofLp
        (kt19SelectedPortZeroLabel p k port) ≠ 0 := by
  rw [kt19SelectedPortMagicState, kt19SelectedPortTransport_symm_apply,
    magicRegisterKet_apply]
  apply mul_ne_zero
  · apply pow_ne_zero
    apply inv_ne_zero
    have hpos : (0 : Real) < (p : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hpos)
  · intro hphase
    have hunit := phase_mul_conj p
      (registerPairing p (kt19SingleSiteLabel (label port))
        (kt19SelectedPortLabelEquiv p k port (kt19SelectedPortZeroLabel p k port)) +
          cubicExponent p (kt19SelectedPortLabelEquiv p k port
            (kt19SelectedPortZeroLabel p k port)))
    rw [hphase, zero_mul] at hunit
    norm_num at hunit

/-- The singleton coordinate relabeling is literally the singleton KT19
magic-label word at the selected finite-field value. -/
private theorem kt19SelectedPortLabelEquiv_eq_singleSiteLabel
    (p k : Nat) [NeZero p] (port : Fin k)
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions) :
    kt19SelectedPortLabelEquiv p k port left =
      kt19SingleSiteLabel
        (ZMod.finEquiv p (left (kt19SelectedPortCoordinate p k port))) := by
  funext site
  have hsite : site = default := Subsingleton.elim _ _
  subst site
  rfl

/-- The register pairing on the actual singleton KT19 carrier has one term. -/
private theorem kt19SingleSiteLabel_registerPairing
    (p : Nat) [NeZero p] (a x : ZMod p) :
    registerPairing p (kt19SingleSiteLabel a) (kt19SingleSiteLabel x) = a * x := by
  unfold registerPairing
  rw [Fintype.sum_unique]
  rfl

/-- The cubic exponent on the actual singleton KT19 carrier has one term. -/
private theorem kt19SingleSiteLabel_cubicExponent
    (p : Nat) [NeZero p] (x : ZMod p) :
    cubicExponent p (kt19SingleSiteLabel x) = x ^ 3 := by
  unfold cubicExponent
  rw [Fintype.sum_unique]
  rfl

/-- Splitting the global magic exponent at the selected port gives exactly
the cross-product identity required by the anchor-amplitude ratio. -/
private theorem kt19SelectedPortMagicExponent_cross
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k))
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    (registerPairing p label
        ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
          ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right))) +
      cubicExponent p
        ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
          ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)))) +
      (registerPairing p (kt19SingleSiteLabel (label port))
          (kt19SelectedPortLabelEquiv p k port
            (kt19SelectedPortZeroLabel p k port)) +
        cubicExponent p (kt19SelectedPortLabelEquiv p k port
          (kt19SelectedPortZeroLabel p k port))) =
      (registerPairing p (kt19SingleSiteLabel (label port))
          (kt19SelectedPortLabelEquiv p k port left) +
        cubicExponent p (kt19SelectedPortLabelEquiv p k port left)) +
      (registerPairing p label
          ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
            ((kt19SelectedPortSubsystem p k port).recombineLabel
              (kt19SelectedPortZeroLabel p k port, right))) +
        cubicExponent p
          ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
            ((kt19SelectedPortSubsystem p k port).recombineLabel
              (kt19SelectedPortZeroLabel p k port, right)))) := by
  rw [kt19SelectedPortLabelEquiv_eq_singleSiteLabel p k port left,
    kt19SelectedPortLabelEquiv_eq_singleSiteLabel p k port
      (kt19SelectedPortZeroLabel p k port)]
  rw [kt19SingleSiteLabel_registerPairing, kt19SingleSiteLabel_cubicExponent,
    kt19SingleSiteLabel_registerPairing, kt19SingleSiteLabel_cubicExponent]
  rw [kt19RegisterPairing_split_port p k port label
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right))),
    kt19CubicExponent_split_port p k port
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right))),
    kt19RegisterPairing_split_port p k port label
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right))),
    kt19CubicExponent_split_port p k port
      ((kt19PrimeQuditLabelEquiv p (Fin k)).symm
        ((kt19SelectedPortSubsystem p k port).recombineLabel
          (kt19SelectedPortZeroLabel p k port, right)))]
  rw [kt19PrimeQuditLabelEquiv_symm_recombine_apply_port p k port left right,
    kt19PrimeQuditLabelEquiv_symm_recombine_zero_apply_port p k port right]
  simp_rw [kt19PrimeQuditLabelEquiv_symm_recombine_apply_ne p k port left right,
    kt19PrimeQuditLabelEquiv_symm_recombine_apply_ne p k port
      (kt19SelectedPortZeroLabel p k port) right]
  simp [kt19SelectedPortZeroLabel, Qudit.zeroLabel]
  ring

/-- Two magic amplitudes with equal total phase exponent satisfy the
corresponding scalar cross-product equality. -/
private theorem kt19Phase_cross_product
    (p : Nat) [NeZero p] (globalScale localScale : Complex)
    (globalLeft localZero localLeft globalZero : ZMod p)
    (hphaseExponent : globalLeft + localZero = localLeft + globalZero) :
    (globalScale * phase p globalLeft) * (localScale * phase p localZero) =
      (localScale * phase p localLeft) * (globalScale * phase p globalZero) := by
  have hphase : phase p globalLeft * phase p localZero =
      phase p localLeft * phase p globalZero := by
    rw [← phase_add, hphaseExponent, phase_add]
  calc
    (globalScale * phase p globalLeft) * (localScale * phase p localZero) =
        (globalScale * localScale) *
          (phase p globalLeft * phase p localZero) := by ring
    _ = (globalScale * localScale) *
          (phase p localLeft * phase p globalZero) := by rw [hphase]
    _ = (localScale * phase p localLeft) *
          (globalScale * phase p globalZero) := by ring

/-- The globally transported magic word factors pointwise into its selected
magic factor and the honest complementary anchor ratio. -/
private theorem kt19SelectedPortMagicState_recombine_amplitude
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k))
    (left : Qudit.Label (kt19SelectedPortSubsystem p k port).selectedDimensions)
    (right : Qudit.Label (kt19SelectedPortSubsystem p k port).complementDimensions) :
    ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label)).ofLp
        ((kt19SelectedPortSubsystem p k port).recombineLabel (left, right)) =
      (kt19SelectedPortMagicState p k port label).ofLp left *
        (kt19SelectedPortComplementState p k port label).ofLp right := by
  simp only [kt19SelectedPortComplementState, WithLp.ofLp_toLp]
  field_simp [kt19SelectedPortMagicState_zero_ne_zero p k port label]
  simpa only [kt19SelectedPortMagicState, kt19SelectedPortTransport_symm_apply,
    kt19PrimeQuditRegisterQuditTransport_apply, magicRegisterKet_apply] using
    (kt19Phase_cross_product p _ _ _ _ _ _
      (kt19SelectedPortMagicExponent_cross p k port label left right))

/-- The actual routed magic-register ket has the literal selected/complement
tensor factorization used by the singleton physical partial trace. -/
private theorem kt19SelectedPortMagicState_factorization
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortSubsystem p k port).registerFactorization
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label)) =
      kt19SelectedPortMagicState p k port label ⊗ₜ[Complex]
        kt19SelectedPortComplementState p k port label := by
  apply (kt19SelectedPortSubsystem p k port).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_apply_apply]
  ext labels
  change ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
      (magicRegisterKet p label)) labels =
    (kt19SelectedPortSubsystem p k port).registerFactorization.symm
      (kt19SelectedPortMagicState p k port label ⊗ₜ[Complex]
        kt19SelectedPortComplementState p k port label) labels
  rw [kt19SelectedPortRegisterFactorization_symm_tmul_apply]
  have hsplit :
      (kt19SelectedPortSubsystem p k port).recombineLabel
          ((kt19SelectedPortSubsystem p k port).splitLabel labels) = labels :=
    (kt19SelectedPortSubsystem p k port).recombine_splitLabel labels
  calc
    ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label)) labels =
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label))
          ((kt19SelectedPortSubsystem p k port).recombineLabel
            ((kt19SelectedPortSubsystem p k port).splitLabel labels)) := by rw [hsplit]
    _ = (kt19SelectedPortMagicState p k port label)
          ((kt19SelectedPortSubsystem p k port).splitLabel labels).1 *
        (kt19SelectedPortComplementState p k port label)
          ((kt19SelectedPortSubsystem p k port).splitLabel labels).2 := by
          exact kt19SelectedPortMagicState_recombine_amplitude p k port label
            ((kt19SelectedPortSubsystem p k port).splitLabel labels).1
            ((kt19SelectedPortSubsystem p k port).splitLabel labels).2

/-- The selected factor is normalized because it is a unitary transport of a
one-site KT19 magic ket. -/
private theorem kt19SelectedPortMagicState_inner_self
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    inner Complex (kt19SelectedPortMagicState p k port label)
      (kt19SelectedPortMagicState p k port label) = 1 := by
  rw [kt19SelectedPortMagicState]
  calc
    inner Complex
        ((kt19SelectedPortTransport p k port).symm
          (magicRegisterKet p (kt19SingleSiteLabel (label port))))
        ((kt19SelectedPortTransport p k port).symm
          (magicRegisterKet p (kt19SingleSiteLabel (label port)))) =
      inner Complex
        ((kt19SelectedPortTransport p k port)
          ((kt19SelectedPortTransport p k port).symm
            (magicRegisterKet p (kt19SingleSiteLabel (label port)))))
        ((kt19SelectedPortTransport p k port)
          ((kt19SelectedPortTransport p k port).symm
            (magicRegisterKet p (kt19SingleSiteLabel (label port))))) :=
          ((kt19SelectedPortTransport p k port).map_inner _ _).symm
    _ = inner Complex (magicRegisterKet p (kt19SingleSiteLabel (label port)))
        (magicRegisterKet p (kt19SingleSiteLabel (label port))) := by
          simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
          rfl
    _ = 1 := magicRegisterKet_inner_self p (kt19SingleSiteLabel (label port))

/-- The complementary anchor-ratio factor is normalized because the factored
global magic word and its selected factor are both normalized. -/
private theorem kt19SelectedPortComplementState_inner_self
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    inner Complex (kt19SelectedPortComplementState p k port label)
      (kt19SelectedPortComplementState p k port label) = 1 := by
  have hglobal : inner Complex
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label))
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
        (magicRegisterKet p label)) = 1 := by
    rw [(kt19PrimeQuditRegisterQuditTransport p (Fin k)).map_inner]
    exact magicRegisterKet_inner_self p label
  have hfactorNorm : inner Complex
      ((kt19SelectedPortSubsystem p k port).registerFactorization
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label)))
      ((kt19SelectedPortSubsystem p k port).registerFactorization
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k))
          (magicRegisterKet p label))) = 1 := by
    rw [(kt19SelectedPortSubsystem p k port).registerFactorization.map_inner]
    exact hglobal
  rw [kt19SelectedPortMagicState_factorization, TensorProduct.inner_tmul,
    kt19SelectedPortMagicState_inner_self, one_mul] at hfactorNorm
  exact hfactorNorm

/-- The literal selected-coordinate partial trace of one transported routed
magic word is the corresponding actual one-site KT19 magic-word density. -/
private theorem kt19SelectedPort_partialTrace_pure_magicWord
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    (kt19SelectedPortTransport p k port).conjDensity
      ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
          (DensityOperator.pureDensity (magicRegisterKet p label) (by
            rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
              magicRegisterKet_inner_self]
            norm_num)))) =
      DensityOperator.pureDensity
        (magicRegisterKet p (kt19SingleSiteLabel (label port))) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num) := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    QuditSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, QuditSubsystem.selectedPartialTrace,
    DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne
    (kt19PrimeQuditRegisterQuditTransport p (Fin k))]
  rw [QuditSubsystem.conjOperator_rankOne
    (kt19SelectedPortSubsystem p k port).registerFactorization]
  rw [kt19SelectedPortMagicState_factorization]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [kt19SelectedPortComplementState_inner_self]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne (kt19SelectedPortTransport p k port)]
  rw [kt19SelectedPortMagicState]
  simpa only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]

variable {p l k : Nat} [NeZero p] [Fact p.Prime]

/-- The actual one-port density of a KT19 accepted output: first expose the
prime register as qudit coordinates, then trace out every coordinate except
the designated logical port, and finally transport that concrete factor to the
one-site KT19 carrier. -/
noncomputable def kt19SelectedPortActualMarginal
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  (kt19SelectedPortTransport p k port).conjDensity
    ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
        (family.run mu hmu_nonneg hmu_sum).acceptedOutput))

/-- The actual accepted one-port density used as the next-level physical
resource candidate. -/
noncomputable def kt19SelectedPortDensity
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  kt19SelectedPortActualMarginal family mu hmu_nonneg hmu_sum port

/-- The concrete magic-label law induced at one actual output port by the
complete readout of the accepted joint output.  This is a finite marginal of
the physical output law, not an independently supplied noise parameter. -/
noncomputable def kt19SelectedPortLabelDistribution
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) (a : ZMod p) : ℝ :=
  ∑ label : PrimeQuditRegisterLabel p (Fin k),
    if label port = a then
      kt19OutputLabelDistribution (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
    else 0

/-- Every mass in the actual port-label marginal is nonnegative because it is
a finite sub-sum of complete magic-basis Born weights. -/
theorem kt19SelectedPortLabelDistribution_nonneg
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) (a : ZMod p) :
    0 ≤ kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port a := by
  unfold kt19SelectedPortLabelDistribution
  apply Finset.sum_nonneg
  intro label _
  by_cases hlabel : label port = a
  · simpa [hlabel] using kt19OutputLabelDistribution_nonneg
      (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
  · simp [hlabel]

/-- The finite port-label marginal has total mass one. -/
theorem kt19SelectedPortLabelDistribution_sum
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    ∑ a : ZMod p, kt19SelectedPortLabelDistribution
      family mu hmu_nonneg hmu_sum port a = 1 := by
  classical
  unfold kt19SelectedPortLabelDistribution
  calc
    (∑ a : ZMod p, ∑ label : PrimeQuditRegisterLabel p (Fin k),
        if label port = a then
          kt19OutputLabelDistribution (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
        else 0) =
        ∑ label : PrimeQuditRegisterLabel p (Fin k), ∑ a : ZMod p,
          if label port = a then
            kt19OutputLabelDistribution
              (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
          else 0 := Finset.sum_comm
    _ = ∑ label : PrimeQuditRegisterLabel p (Fin k),
        kt19OutputLabelDistribution (family.run mu hmu_nonneg hmu_sum).acceptedOutput label := by
      apply Finset.sum_congr rfl
      intro label _
      rw [Finset.sum_eq_single (label port)]
      · simp
      · intro other _ hother
        simp [hother, Ne.symm hother]
      · simp
    _ = 1 := kt19OutputLabelDistribution_sum
      (family.run mu hmu_nonneg hmu_sum).acceptedOutput

/-- The nonzero-label rate of the actual one-port marginal is exactly the
corresponding physical decoded-output port error.  This is a finite
partition-of-labels identity, independent of the later density-factorization
bridge. -/
theorem kt19SelectedPortErrorRate_eq_outputPortError
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    kt19ErrorRate (kt19SelectedPortLabelDistribution
      family mu hmu_nonneg hmu_sum port) =
      kt19OutputPortError (family.run mu hmu_nonneg hmu_sum).acceptedOutput port := by
  unfold kt19ErrorRate kt19SelectedPortLabelDistribution kt19OutputPortError
  calc
    1 - (∑ label : PrimeQuditRegisterLabel p (Fin k),
        if label port = 0 then
          kt19OutputLabelDistribution
            (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
        else 0) =
        (∑ label : PrimeQuditRegisterLabel p (Fin k),
          kt19OutputLabelDistribution
            (family.run mu hmu_nonneg hmu_sum).acceptedOutput label) -
          (∑ label : PrimeQuditRegisterLabel p (Fin k),
            if label port = 0 then
              kt19OutputLabelDistribution
                (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
            else 0) := by
              rw [kt19OutputLabelDistribution_sum]
    _ = ∑ label : PrimeQuditRegisterLabel p (Fin k),
        (kt19OutputLabelDistribution
          (family.run mu hmu_nonneg hmu_sum).acceptedOutput label -
          (if label port = 0 then
            kt19OutputLabelDistribution
              (family.run mu hmu_nonneg hmu_sum).acceptedOutput label
          else 0)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ label : PrimeQuditRegisterLabel p (Fin k),
        (if label port = 0 then 0 else
          kt19OutputLabelDistribution
            (family.run mu hmu_nonneg hmu_sum).acceptedOutput label) := by
            apply Finset.sum_congr rfl
            intro label _
            by_cases hlabel : label port = 0 <;> simp [hlabel]

/-- The next-level density is definitionally the physical singleton marginal
of the accepted KT19 output, with the partial trace retained explicitly. -/
theorem kt19SelectedPortDensity_eq_actualMarginal
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    kt19SelectedPortDensity family mu hmu_nonneg hmu_sum port =
      kt19SelectedPortActualMarginal family mu hmu_nonneg hmu_sum port :=
  rfl

/-- The actual physical channel from a decoded KT19 logical register to one
selected output port: expose qudit coordinates, trace the literal complement,
and transport the retained factor to the next-level single-site carrier. -/
private noncomputable def kt19SelectedPortTransportedChannel
    (p k : Nat) [NeZero p] (port : Fin k) :
    QuantumChannel (PrimeQuditRegister p (Fin k)) (KT19SingleQudit.{0} p) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (kt19SelectedPortTransport p k port))
    (QuantumChannel.comp
      (kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister
      (QuantumChannel.unitaryConj
        (kt19PrimeQuditRegisterQuditTransport p (Fin k))))

/-- The actual selected marginal is the density induced by that composed
physical channel on the accepted KT19 output. -/
private theorem kt19SelectedPortActualMarginal_toOperator
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    (kt19SelectedPortActualMarginal family mu hmu_nonneg hmu_sum port).toOperator =
      kt19SelectedPortTransportedChannel p k port
        (family.run mu hmu_nonneg hmu_sum).acceptedOutput.toOperator :=
  rfl

/-- The one-site magic-word density appearing after a routed selected-port
partial trace. -/
private noncomputable def kt19SelectedPortMagicWordDensity
    (p : Nat) [NeZero p] (a : ZMod p) : DensityOperator (KT19SingleQudit.{0} p) :=
  DensityOperator.pureDensity (magicRegisterKet p (kt19SingleSiteLabel a)) (by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
      magicRegisterKet_inner_self]
    norm_num)

/-- The composed physical selected channel maps every routed logical magic
word to the one-site magic density with its literal selected label. -/
private theorem kt19SelectedPortTransportedChannel_pure_magicWord
    (p k : Nat) [NeZero p] (port : Fin k)
    (label : PrimeQuditRegisterLabel p (Fin k)) :
    kt19SelectedPortTransportedChannel p k port
        (DensityOperator.pureDensity (magicRegisterKet p label) (by
          rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
            magicRegisterKet_inner_self]
          norm_num)).toOperator =
      (kt19SelectedPortMagicWordDensity p (label port)).toOperator := by
  change
    ((kt19SelectedPortTransport p k port).conjDensity
      ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
        ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
          (DensityOperator.pureDensity (magicRegisterKet p label) (by
            rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
              magicRegisterKet_inner_self]
            norm_num))))).toOperator = _
  simpa only [kt19SelectedPortMagicWordDensity] using
    congrArg DensityOperator.toOperator
      (kt19SelectedPort_partialTrace_pure_magicWord p k port label)

/-- A local equivalence between prime-field labels and labels on the actual
singleton KT19 carrier, used only to expand its concrete IID resource. -/
private def kt19SelectedPortSingleSiteLabelEquiv (p : Nat) [NeZero p] :
    ZMod p ≃ PrimeQuditRegisterLabel p KT19SingleResourceSite.{0} where
  toFun := kt19SingleSiteLabel
  invFun word := word default
  left_inv _ := rfl
  right_inv word := by
    funext site
    have hsite : site = default := Subsingleton.elim _ _
    rw [hsite]
    rfl

/-- The IID product weight of a literal singleton label is its sole
prime-field coordinate weight. -/
private theorem kt19SelectedPortSingleSite_wordProbability
    (p : Nat) [NeZero p] (nu : ZMod p → ℝ) (a : ZMod p) :
    wordProbability p nu (kt19SingleSiteLabel a) = nu a := by
  unfold wordProbability kt19SingleSiteLabel
  rw [Fintype.prod_unique]
  rfl

/-- Expand the actual one-site KT19 resource over literal prime-field magic
labels, rather than treating its distribution as an abstract input. -/
private theorem kt19SelectedPortSingleSiteResource_toOperator
    (p : Nat) [NeZero p] (nu : ZMod p → ℝ)
    (hnu_nonneg : ∀ a : ZMod p, 0 ≤ nu a)
    (hnu_sum : ∑ a : ZMod p, nu a = 1) :
    (kt19SingleSiteResource nu hnu_nonneg hnu_sum).toOperator =
      ∑ a : ZMod p, (nu a : Complex) •
        (kt19SelectedPortMagicWordDensity p a).toOperator := by
  unfold kt19SingleSiteResource magicRegisterResource
  rw [DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  symm
  apply Fintype.sum_equiv (kt19SelectedPortSingleSiteLabelEquiv p)
  intro a
  change
    (nu a : Complex) • (kt19SelectedPortMagicWordDensity p a).toOperator =
      (wordProbability p nu (kt19SingleSiteLabel a) : Complex) •
        (kt19SelectedPortMagicWordDensity p a).toOperator
  rw [kt19SelectedPortSingleSite_wordProbability]

/-- The unnormalized physical accepted mass whose routed selected output
label is exactly `a`. -/
private noncomputable def kt19SelectedPortRoutedMass
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (port : Fin k) (a : ZMod p) : ℝ :=
  ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
    if kt19AcceptedWord family.rowFamily error ∧
        KT19DistillationFamily.kt19Routing family error port = a then
      wordProbability p mu error
    else 0

/-- The observed selected-label marginal is the concrete routed accepted
mass at that label divided by the actual success probability. -/
private theorem kt19SelectedPortLabelDistribution_eq_routedPortMass_div_success
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k)
    (heps : kt19ErrorRate mu < 1) (a : ZMod p) :
    kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port a =
      kt19SelectedPortRoutedMass family mu port a /
        kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
  classical
  unfold kt19SelectedPortLabelDistribution
  simp_rw [KT19DistillationFamily.outputLabelDistribution_eq_routedMass_div_success
    family mu hmu_nonneg hmu_sum heps]
  calc
    (∑ label : PrimeQuditRegisterLabel p (Fin k),
        if label port = a then
          KT19DistillationFamily.routedAcceptedMass family mu label /
            kt19Success family.rowFamily mu hmu_nonneg hmu_sum
        else 0) =
        (∑ label : PrimeQuditRegisterLabel p (Fin k),
          if label port = a then
            KT19DistillationFamily.routedAcceptedMass family mu label else 0) /
          kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro label _
            by_cases hlabel : label port = a <;> simp [hlabel]
    _ = kt19SelectedPortRoutedMass family mu port a /
          kt19Success family.rowFamily mu hmu_nonneg hmu_sum := by
      congr 1
      unfold KT19DistillationFamily.routedAcceptedMass kt19SelectedPortRoutedMass
      calc
        (∑ label : PrimeQuditRegisterLabel p (Fin k),
          if label port = a then
            ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
              if kt19AcceptedWord family.rowFamily error ∧
                  label = KT19DistillationFamily.kt19Routing family error then
                wordProbability p mu error
              else 0
          else 0) =
          ∑ label : PrimeQuditRegisterLabel p (Fin k),
            ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
              if label port = a then
                if kt19AcceptedWord family.rowFamily error ∧
                    label = KT19DistillationFamily.kt19Routing family error then
                  wordProbability p mu error
                else 0
              else 0 := by
                apply Finset.sum_congr rfl
                intro label _
                by_cases hlabel : label port = a <;> simp [hlabel]
        _ = ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
            ∑ label : PrimeQuditRegisterLabel p (Fin k),
              if label port = a then
                if kt19AcceptedWord family.rowFamily error ∧
                    label = KT19DistillationFamily.kt19Routing family error then
                  wordProbability p mu error
                else 0
              else 0 := Finset.sum_comm
        _ = ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
            if kt19AcceptedWord family.rowFamily error ∧
                KT19DistillationFamily.kt19Routing family error port = a then
              wordProbability p mu error
            else 0 := by
              apply Finset.sum_congr rfl
              intro error _
              by_cases haccepted : kt19AcceptedWord family.rowFamily error
              · rw [Fintype.sum_eq_single
                    (KT19DistillationFamily.kt19Routing family error)]
                · simp [haccepted]
                · intro label hne
                  simp [hne]
              · simp [haccepted]

/-- Regrouping the finite accepted routed-word sum by its literal selected
prime-field output label. -/
private theorem kt19SelectedPort_routedWordSum_grouped
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (port : Fin k) :
    (∑ error : Word (ZMod p) (KeptPunctureLocation p k),
      if kt19AcceptedWord family.rowFamily error then
        (wordProbability p mu error : Complex) •
          (kt19SelectedPortMagicWordDensity p
            (KT19DistillationFamily.kt19Routing family error port)).toOperator
      else 0) =
      ∑ a : ZMod p, (kt19SelectedPortRoutedMass family mu port a : Complex) •
        (kt19SelectedPortMagicWordDensity p a).toOperator := by
  classical
  calc
    (∑ error : Word (ZMod p) (KeptPunctureLocation p k),
      if kt19AcceptedWord family.rowFamily error then
        (wordProbability p mu error : Complex) •
          (kt19SelectedPortMagicWordDensity p
            (KT19DistillationFamily.kt19Routing family error port)).toOperator
      else 0) =
        ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
          ∑ a : ZMod p,
            if kt19AcceptedWord family.rowFamily error ∧
                KT19DistillationFamily.kt19Routing family error port = a then
              (wordProbability p mu error : Complex) •
                (kt19SelectedPortMagicWordDensity p a).toOperator
            else 0 := by
              apply Finset.sum_congr rfl
              intro error _
              by_cases haccepted : kt19AcceptedWord family.rowFamily error
              · rw [Fintype.sum_eq_single
                    (KT19DistillationFamily.kt19Routing family error port)]
                · simp [haccepted]
                · intro a hne
                  have hroute : ¬ (kt19AcceptedWord family.rowFamily error ∧
                      KT19DistillationFamily.kt19Routing family error port = a) := by
                    intro hroute
                    exact hne hroute.2.symm
                  rw [if_neg hroute]
              · simp [haccepted]
    _ = ∑ a : ZMod p,
          ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
            if kt19AcceptedWord family.rowFamily error ∧
                KT19DistillationFamily.kt19Routing family error port = a then
              (wordProbability p mu error : Complex) •
                (kt19SelectedPortMagicWordDensity p a).toOperator
            else 0 := Finset.sum_comm
    _ = ∑ a : ZMod p, (kt19SelectedPortRoutedMass family mu port a : Complex) •
          (kt19SelectedPortMagicWordDensity p a).toOperator := by
            apply Finset.sum_congr rfl
            intro a _
            unfold kt19SelectedPortRoutedMass
            rw [Complex.ofReal_sum, Finset.sum_smul]
            apply Finset.sum_congr rfl
            intro error _
            split <;> simp

/-- The actual singleton marginal of the normalized accepted KT19 output is
exactly the one-site KT19 resource at its physically induced selected-label
distribution. -/
theorem kt19SelectedPortDensity_eq_singleSiteResource
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k)
    (heps : kt19ErrorRate mu < 1) :
    kt19SelectedPortDensity family mu hmu_nonneg hmu_sum port =
      kt19SingleSiteResource
        (kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port)
        (kt19SelectedPortLabelDistribution_nonneg family mu hmu_nonneg hmu_sum port)
        (kt19SelectedPortLabelDistribution_sum family mu hmu_nonneg hmu_sum port) := by
  apply DensityOperator.ext_toOperator
  rw [kt19SelectedPortDensity_eq_actualMarginal,
    kt19SelectedPortActualMarginal_toOperator,
    KT19DistillationFamily.acceptedOutput_toOperator_eq_routed_sum
      family mu hmu_nonneg hmu_sum heps]
  simp only [map_smul, map_sum, apply_ite, map_zero]
  simp_rw [kt19SelectedPortTransportedChannel_pure_magicWord]
  rw [kt19SelectedPort_routedWordSum_grouped]
  rw [kt19SelectedPortSingleSiteResource_toOperator]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [kt19SelectedPortLabelDistribution_eq_routedPortMass_div_success
    family mu hmu_nonneg hmu_sum port heps a]
  simp only [smul_smul, Complex.ofReal_div, div_eq_mul_inv]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : Complex)) (mul_comm _ _)

/-! ## Fixed-prime routed physical schedule -/

/-- A literal finite address of one retained physical input slot at every
stage of a fixed-prime routed construction.  Its codomain is the actual
`Fin`-enumeration of retained puncture sites, rather than an advertised
resource-count parameter. -/
abbrev kt19FixedPrimeInputSlots (p k depth : Nat) [NeZero p] [Fact p.Prime] :=
  Fin depth → Fin (Fintype.card (KeptPunctureLocation p k))

/-- A literal selected logical-output path at every stage of a fixed-prime
routed construction. -/
abbrev kt19FixedPrimeOutputSlots (k depth : Nat) :=
  Fin depth → Fin k

/-- The routed input-address carrier has exactly the actual retained-site
count at every stage. -/
private theorem kt19FixedPrimeInputSlots_card
    (family : KT19DistillationFamily p l k) (depth : Nat) :
    Fintype.card (kt19FixedPrimeInputSlots p k depth) = (p - k) ^ depth := by
  simp only [kt19FixedPrimeInputSlots, Fintype.card_fun, Fintype.card_fin]
  rw [KT19DistillationFamily.inputResourceCount_eq family]

/-- The routed output-path carrier counts literal finite output-port paths. -/
private theorem kt19FixedPrimeOutputSlots_card (k depth : Nat) :
    Fintype.card (kt19FixedPrimeOutputSlots k depth) = k ^ depth := by
  simp [kt19FixedPrimeOutputSlots]

/-- The unique empty routed output path. -/
def kt19FixedPrimeOutputPathEmpty (k : Nat) : kt19FixedPrimeOutputSlots k 0 :=
  fun index => Fin.elim0 index

/-- Append the next physically selected output port to a routed path. -/
def kt19FixedPrimeOutputPathAppend (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k) :
    kt19FixedPrimeOutputSlots k (depth + 1) :=
  Fin.lastCases port path

/-- The prefix preceding the final selected port of a nonempty routed path. -/
def kt19FixedPrimeOutputPathInit (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k (depth + 1)) :
    kt19FixedPrimeOutputSlots k depth :=
  fun index => path index.castSucc

/-- The final selected port of a nonempty routed path. -/
def kt19FixedPrimeOutputPathLast (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k (depth + 1)) : Fin k :=
  path (Fin.last depth)

@[simp] private theorem kt19FixedPrimeOutputPathInit_append (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k) :
    kt19FixedPrimeOutputPathInit k depth
      (kt19FixedPrimeOutputPathAppend k depth path port) = path := by
  funext index
  simp [kt19FixedPrimeOutputPathInit, kt19FixedPrimeOutputPathAppend]

@[simp] private theorem kt19FixedPrimeOutputPathLast_append (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k) :
    kt19FixedPrimeOutputPathLast k depth
      (kt19FixedPrimeOutputPathAppend k depth path port) = port := by
  simp [kt19FixedPrimeOutputPathLast, kt19FixedPrimeOutputPathAppend]

/-- A finite prime-label distribution together with the exact nonnegativity
and normalization facts needed to prepare a literal KT19 run.  This stores
only input data, never an output/error/cost conclusion. -/
private structure KT19FixedPrimeDistribution (p : Nat) [NeZero p] [Fact p.Prime] where
  mass : ZMod p → ℝ
  mass_nonneg : ∀ a : ZMod p, 0 ≤ mass a
  mass_sum : ∑ a : ZMod p, mass a = 1

/-- The actual label distribution produced by selecting one port of a
physical KT19 accepted output. -/
private noncomputable def kt19FixedPrimeSuccessorDistribution
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k) :
    KT19FixedPrimeDistribution p where
  mass := kt19SelectedPortLabelDistribution family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port
  mass_nonneg := kt19SelectedPortLabelDistribution_nonneg family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port
  mass_sum := kt19SelectedPortLabelDistribution_sum family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port

/-- The actual path-dependent selected-port distribution.  At a successor it
uses the concrete marginal of the prefix run and the literal final port. -/
private noncomputable def kt19FixedPrimePathDistribution
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) :
    ∀ (depth : Nat), kt19FixedPrimeOutputSlots k depth →
      KT19FixedPrimeDistribution p
  | 0, _ => initial
  | depth + 1, path =>
      kt19FixedPrimeSuccessorDistribution family
        (kt19FixedPrimePathDistribution family initial depth
          (kt19FixedPrimeOutputPathInit k depth path))
        (kt19FixedPrimeOutputPathLast k depth path)

/-- The parent-output grid consists of one physical run copy and one
selected logical port. -/
private abbrev kt19FixedPrimeParentOutputSlots (p k : Nat) [NeZero p] [Fact p.Prime] :=
  Fin (Fintype.card (KeptPunctureLocation p k)) × Fin k

/-- The child-input grid transposes the parent index and selected-port
coordinate, so a fixed child gets one input from each distinct parent. -/
private abbrev kt19FixedPrimeChildInputSlots (p k : Nat) [NeZero p] [Fact p.Prime] :=
  Fin k × Fin (Fintype.card (KeptPunctureLocation p k))

/-- The literal transpose between parent-output and child-input grids. -/
private def kt19FixedPrimeRouting (p k : Nat) [NeZero p] [Fact p.Prime] :
    kt19FixedPrimeParentOutputSlots p k ≃ kt19FixedPrimeChildInputSlots p k :=
  DependentBatch.parentPortTranspose
    (Fin (Fintype.card (KeptPunctureLocation p k))) (Fin k)

/-- The physical source slot supplying a named retained input of one fixed
child run. -/
private def kt19FixedPrimeChildInputSlot (p k : Nat) [NeZero p] [Fact p.Prime]
    (port : Fin k) (parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    kt19FixedPrimeChildInputSlots p k :=
  kt19FixedPrimeRouting p k (DependentBatch.childInputSlot port parent)

@[simp] private theorem kt19FixedPrimeChildInputSlot_apply (p k : Nat)
    [NeZero p] [Fact p.Prime] (port : Fin k)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    kt19FixedPrimeChildInputSlot p k port parent = (port, parent) :=
  rfl

/-- The physical sources of a fixed child are distinct parent runs. -/
private theorem kt19FixedPrimeChildInputSlot_injective (p k : Nat)
    [NeZero p] [Fact p.Prime] (port : Fin k) :
    Function.Injective (kt19FixedPrimeChildInputSlot p k port) := by
  intro left right hroute
  apply DependentBatch.childInputSlot_injective port
  apply (kt19FixedPrimeRouting p k).injective
  exact hroute

/-- An indexed copy of the current actual KT19 family run.  The index records
the source provenance of a future child input and does not assert statistical
independence between different parent copies. -/
private noncomputable def kt19FixedPrimeFreshParentRun
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p)
    (_parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  family.run distribution.mass distribution.mass_nonneg distribution.mass_sum

/-- The literal selected physical marginal of a designated indexed parent
run, retaining the register transport and singleton qudit partial trace. -/
private noncomputable def kt19FixedPrimeFreshParentPortDensity
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) (port : Fin k) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  (kt19SelectedPortTransport p k port).conjDensity
    ((kt19SelectedPortSubsystem p k port).selectedPartialTraceFromRegister.mapDensity
      ((kt19PrimeQuditRegisterQuditTransport p (Fin k)).conjDensity
        (kt19FixedPrimeFreshParentRun family distribution parent).acceptedOutput))

/-- The indexed parent marginal is exactly the selected-port density already
derived from the actual accepted KT19 output. -/
private theorem kt19FixedPrimeFreshParentPortDensity_eq_selectedPortDensity
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) (port : Fin k) :
    kt19FixedPrimeFreshParentPortDensity family distribution parent port =
      kt19SelectedPortDensity family distribution.mass distribution.mass_nonneg
        distribution.mass_sum port :=
  rfl

/-- The actual child input resources routed from the selected marginals of a
fresh parent grid.  The inverse routing is retained explicitly so the parent
and selected-port provenance is physical data, not a rate-only abbreviation. -/
private noncomputable def kt19FixedPrimeChildResources
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k) :
    ResourceInput (Fintype.card (KeptPunctureLocation p k))
      (KT19SingleQudit.{0} p) :=
  fun parent =>
    let source := (kt19FixedPrimeRouting p k).symm
      (kt19FixedPrimeChildInputSlot p k port parent)
    kt19FixedPrimeFreshParentPortDensity family distribution source.1 source.2

/-- Every routed child resource has the designated parent/port source. -/
@[simp] private theorem kt19FixedPrimeChildResources_apply
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (parent : Fin (Fintype.card (KeptPunctureLocation p k))) :
    kt19FixedPrimeChildResources family distribution port parent =
      kt19FixedPrimeFreshParentPortDensity family distribution parent port := by
  rfl

/-- Under the real strict-error premise needed to normalize the accepted
output, the routed child resources are pointwise the ordinary one-site KT19
resources at the actual selected-port label distribution. -/
private theorem kt19FixedPrimeChildResources_eq_noisySingleSiteResources
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (heps : kt19ErrorRate distribution.mass < 1) :
    kt19FixedPrimeChildResources family distribution port =
      kt19NoisySingleSiteResources (Site := KeptPunctureLocation p k)
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass_nonneg
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass_sum := by
  funext parent
  rw [kt19FixedPrimeChildResources_apply,
    kt19FixedPrimeFreshParentPortDensity_eq_selectedPortDensity]
  exact kt19SelectedPortDensity_eq_singleSiteResource family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port heps

/-- The literal child execution: it prepares the routed physical resources,
runs the real complete KT19 binary instrument with its totalized fallback,
and only then applies the family decoder. -/
private noncomputable def kt19FixedPrimeChildRun
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  (FiniteInstrument.binaryDistillationRun
    (kt19ProtocolInstrument family.rowFamily) (kt19Accepts family.rowFamily)
    (kt19ProtocolInstrument_complete family.rowFamily)
    (Fintype.card (KeptPunctureLocation p k))
    (kt19FixedPrimeChildResources family distribution port)
    (kt19PrepareInput (q := p) (Site := KeptPunctureLocation p k))
    (kt19EndpointFallback (q := p) (Site := KeptPunctureLocation p k))).postprocess family.decoder

/-- The physically routed child execution is exactly the ordinary family run
at the selected port's actual output distribution; this conclusion is proved
from its input-resource equality rather than built into the child definition. -/
private theorem kt19FixedPrimeChildRun_eq_familyRun
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (heps : kt19ErrorRate distribution.mass < 1) :
    kt19FixedPrimeChildRun family distribution port =
      family.run (kt19FixedPrimeSuccessorDistribution family distribution port).mass
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass_nonneg
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass_sum := by
  unfold kt19FixedPrimeChildRun KT19DistillationFamily.run
    KT19DistillationFamily.decoder kt19Run kt19SyndromeRun
  rw [kt19FixedPrimeChildResources_eq_noisySingleSiteResources
    family distribution port heps]

/-- The ordinary current run at a literal finite path.  Its successor is
identified below with a separately constructed routed child execution. -/
private noncomputable def kt19FixedPrimePathRun
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  family.run (kt19FixedPrimePathDistribution family initial depth path).mass
    (kt19FixedPrimePathDistribution family initial depth path).mass_nonneg
    (kt19FixedPrimePathDistribution family initial depth path).mass_sum

/-- A path successor is the literal physical routed child run, conditional
only on the explicit strict-error premise for that prefix distribution. -/
private theorem kt19FixedPrimePathRun_append_eq_childRun
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (port : Fin k)
    (heps : kt19ErrorRate
      (kt19FixedPrimePathDistribution family initial depth path).mass < 1) :
    kt19FixedPrimePathRun family initial (depth + 1)
      (kt19FixedPrimeOutputPathAppend k depth path port) =
      kt19FixedPrimeChildRun family
        (kt19FixedPrimePathDistribution family initial depth path) port := by
  simpa [kt19FixedPrimePathRun, kt19FixedPrimePathDistribution] using
    (kt19FixedPrimeChildRun_eq_familyRun family
      (kt19FixedPrimePathDistribution family initial depth path) port heps).symm

/-- The literal prefix of a routed output path at a finite stage. -/
def kt19FixedPrimeOutputPathPrefix (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin (depth + 1)) :
    kt19FixedPrimeOutputSlots k stage.1 :=
  fun index => path ⟨index.1,
    Nat.lt_of_lt_of_le index.2 (Nat.le_of_lt_succ stage.2)⟩

/-- The selected prefix that determines the actual run at one stage of a
finite output path. -/
def kt19FixedPrimePathStagePath (k depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    kt19FixedPrimeOutputSlots k stage.1 :=
  kt19FixedPrimeOutputPathPrefix k depth path stage.castSucc

/-- The actual finite KT19 family run at one literal stage of a selected
path.  The recursive handoff theorem above identifies successors with the
separately constructed routed physical child runs. -/
private noncomputable def kt19FixedPrimePathStageRun
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    DistillationRun (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) :=
  kt19FixedPrimePathRun family initial stage.1
    (kt19FixedPrimePathStagePath k depth path stage)

/-- The literal accepted Born mass of one actual path stage, retained as a
nonnegative accounting factor. -/
private noncomputable def kt19FixedPrimePathStageYield
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) : NNReal :=
  ⟨(kt19FixedPrimePathStageRun family initial depth path stage).successProbability,
    (kt19FixedPrimePathStageRun family initial depth path stage).success_nonneg⟩

/-- Coercing a stage yield recovers the success probability of its actual
routed path-stage run. -/
private theorem kt19FixedPrimePathStageYield_eq_actualRunSuccess
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    (kt19FixedPrimePathStageYield family initial depth path stage : ℝ) =
      (kt19FixedPrimePathStageRun family initial depth path stage).successProbability :=
  rfl

/-- The one-stage finite-slot adapter is the shared #883 successful-output
cost of this literal routed stage.  The input and output carriers are the
actual retained and logical port types, while the yield is the accepted Born
mass of the path-stage run itself. -/
private noncomputable def kt19FixedPrimePathStageTypedSuccessfulOutputCost
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (KeptPunctureLocation p k) (Fin k)
    (kt19FixedPrimePathStageYield family initial depth path stage)

/-- The local stage adapter really reaches the shared family accounting
surface: this is not a separately stored per-stage cost. -/
private theorem kt19FixedPrimePathStageTypedSuccessfulOutputCost_eq_shared
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    kt19FixedPrimePathStageTypedSuccessfulOutputCost family initial depth path stage =
      KT19DistillationFamily.successfulOutputCost family
        (kt19FixedPrimePathDistribution family initial stage.1
          (kt19FixedPrimePathStagePath k depth path stage)).mass
        (kt19FixedPrimePathDistribution family initial stage.1
          (kt19FixedPrimePathStagePath k depth path stage)).mass_nonneg
        (kt19FixedPrimePathDistribution family initial stage.1
          (kt19FixedPrimePathStagePath k depth path stage)).mass_sum := by
  let distribution := kt19FixedPrimePathDistribution family initial stage.1
    (kt19FixedPrimePathStagePath k depth path stage)
  change DependentBatch.typedSuccessfulOutputCost
      (KeptPunctureLocation p k) (Fin k)
      (kt19FixedPrimePathStageYield family initial depth path stage) =
    KT19DistillationFamily.successfulOutputCost family distribution.mass
      distribution.mass_nonneg distribution.mass_sum
  calc
    DependentBatch.typedSuccessfulOutputCost
        (KeptPunctureLocation p k) (Fin k)
        (kt19FixedPrimePathStageYield family initial depth path stage) =
        (KT19DistillationFamily.overheadFamily family distribution.mass
          distribution.mass_nonneg distribution.mass_sum).successfulOutputCost PUnit.unit := by
      refine
        DependentBatch.typedSuccessfulOutputCost_eq_distillationProtocolFamily_successfulOutputCost
          (KT19DistillationFamily.overheadFamily family distribution.mass
            distribution.mass_nonneg distribution.mass_sum)
          PUnit.unit (KeptPunctureLocation p k) (Fin k)
          (kt19FixedPrimePathStageYield family initial depth path stage) ?_ ?_ ?_
      · exact (KT19DistillationFamily.inputResourceCount_eq family).trans
          (KT19DistillationFamily.overheadFamily_inputResourceCount_eq family
            distribution.mass distribution.mass_nonneg distribution.mass_sum).symm
      · rfl
      · change (kt19FixedPrimePathStageRun family initial depth path stage).successProbability =
          ((KT19DistillationFamily.overheadFamily family distribution.mass
            distribution.mass_nonneg distribution.mass_sum).protocol PUnit.unit).run.successProbability
        rfl
    _ = KT19DistillationFamily.successfulOutputCost family distribution.mass
        distribution.mass_nonneg distribution.mass_sum :=
      (KT19DistillationFamily.successfulOutputCost_eq_shared family distribution.mass
        distribution.mass_nonneg distribution.mass_sum).symm

/-- The finite fresh-layer yield of one selected output path is the product
of the literal accepted success probabilities of its actual stage runs. -/
private noncomputable def kt19FixedPrimePathYieldFactor
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) : NNReal :=
  ∏ stage : Fin depth, kt19FixedPrimePathStageYield family initial depth path stage

/-- The finite path factor is exactly the product of actual stage success
probabilities, rather than a separately supplied success sequence. -/
private theorem kt19FixedPrimePathYieldFactor_eq_actualStageSuccessProduct
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) =
      ∏ stage : Fin depth,
        (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
  classical
  rw [kt19FixedPrimePathYieldFactor, NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro stage _
  exact kt19FixedPrimePathStageYield_eq_actualRunSuccess
    family initial depth path stage

/-- The expected accepted-output count obtained by summing the literal
survival factor of every finite routed output path.  This is a finite pooled
accounting sum, not a simultaneous-success assertion for every block. -/
private noncomputable def kt19FixedPrimePooledAcceptedOutput
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : NNReal :=
  ∑ path : kt19FixedPrimeOutputSlots k depth,
    kt19FixedPrimePathYieldFactor family initial depth path

/-- Coercing the pooled accepted-output count exposes the literal finite sum
of actual path-stage success products. -/
private theorem kt19FixedPrimePooledAcceptedOutput_eq_sum
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    (kt19FixedPrimePooledAcceptedOutput family initial depth : ℝ) =
      ∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) := by
  classical
  rw [kt19FixedPrimePooledAcceptedOutput, NNReal.coe_sum]

/-- Admissibility supplies a genuine logical port, hence every finite output
path carrier is inhabited. -/
private theorem kt19FixedPrimeOutputSlots_nonempty
    (family : KT19DistillationFamily p l k) (depth : Nat) :
    Nonempty (kt19FixedPrimeOutputSlots k depth) := by
  rcases KT19DistillationFamily.outputPort_nonempty family with ⟨port⟩
  exact ⟨fun _ => port⟩

/-- The actual finite output-path carrier has positive cardinality. -/
private theorem kt19FixedPrimeOutputSlots_card_pos
    (family : KT19DistillationFamily p l k) (depth : Nat) :
    0 < Fintype.card (kt19FixedPrimeOutputSlots k depth) :=
  Fintype.card_pos_iff.mpr (kt19FixedPrimeOutputSlots_nonempty family depth)

/-- The normalized pooled yield is the expected accepted-output count per
actual routed output slot. -/
private noncomputable def kt19FixedPrimePooledYield
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : NNReal :=
  kt19FixedPrimePooledAcceptedOutput family initial depth /
    Fintype.card (kt19FixedPrimeOutputSlots k depth)

/-- The pooled yield is exactly the finite path sum divided by the concrete
output-path slot cardinality. -/
private theorem kt19FixedPrimePooledYield_eq_sum_div_card
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    (kt19FixedPrimePooledYield family initial depth : ℝ) =
      (∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ)) /
        Fintype.card (kt19FixedPrimeOutputSlots k depth) := by
  rw [kt19FixedPrimePooledYield, NNReal.coe_div,
    kt19FixedPrimePooledAcceptedOutput_eq_sum]
  rfl

/-- The pooled yield normalizes actual path products by the exact `k^depth`
output-path cardinality. -/
private theorem kt19FixedPrimePooledYield_eq_normalized_path_sum
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    (kt19FixedPrimePooledYield family initial depth : ℝ) =
      (∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ)) /
        (k : ℝ) ^ depth := by
  rw [kt19FixedPrimePooledYield_eq_sum_div_card,
    kt19FixedPrimeOutputSlots_card]
  norm_cast

/-- The typed successful-output cost uses the actual routed input/output slot
types and the normalized pooled yield over every output path. -/
private noncomputable def kt19FixedPrimeTypedSuccessfulOutputCost
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (kt19FixedPrimeInputSlots p k depth)
    (kt19FixedPrimeOutputSlots k depth)
    (kt19FixedPrimePooledYield family initial depth)

/-- The typed cost has its exact finite physical input/output ratio and
normalized actual pooled-yield form. -/
private theorem kt19FixedPrimeTypedSuccessfulOutputCost_eq
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    kt19FixedPrimeTypedSuccessfulOutputCost family initial depth =
      ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) /
        (kt19FixedPrimePooledYield family initial depth : ℝ) := by
  unfold kt19FixedPrimeTypedSuccessfulOutputCost
  unfold DependentBatch.typedSuccessfulOutputCost
  unfold DependentBatch.typedInputOutputRatio
  rw [kt19FixedPrimeInputSlots_card family,
    kt19FixedPrimeOutputSlots_card]
  simp only [Nat.cast_pow]
  rw [div_pow]

/-! ## Fixed-prime pathwise recurrence envelope -/

/-- The actual IID nonzero-label rate at a literal selected-output path.  The
definition reads the physical selected-port distribution constructed above;
it is not a separate recursively stored error parameter. -/
private noncomputable def kt19FixedPrimePathError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) : ℝ :=
  kt19ErrorRate (kt19FixedPrimePathDistribution family initial depth path).mass

/-- Every actual path error is nonnegative because its selected label law is
a genuine finite probability distribution. -/
private theorem kt19FixedPrimePathError_nonneg
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    0 ≤ kt19FixedPrimePathError family initial depth path := by
  unfold kt19FixedPrimePathError
  exact kt19ErrorRate_nonneg
    (kt19FixedPrimePathDistribution family initial depth path).mass
    (kt19FixedPrimePathDistribution family initial depth path).mass_nonneg
    (kt19FixedPrimePathDistribution family initial depth path).mass_sum

/-- Every actual selected-path error is at most one. -/
private theorem kt19FixedPrimePathError_le_one
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    kt19FixedPrimePathError family initial depth path ≤ 1 := by
  unfold kt19FixedPrimePathError
  exact kt19ErrorRate_le_one
    (kt19FixedPrimePathDistribution family initial depth path).mass
    (kt19FixedPrimePathDistribution family initial depth path).mass_nonneg

/-- The depth-zero physical path rate is the supplied IID root rate. -/
private theorem kt19FixedPrimePathError_zero
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p)
    (path : kt19FixedPrimeOutputSlots k 0) :
    kt19FixedPrimePathError family initial 0 path = kt19ErrorRate initial.mass :=
  rfl

/-- One literal selected-port successor obeys the already-proved #883
small-error recurrence for the physical decoded worst-port law. -/
private theorem kt19FixedPrimeSuccessorError_le_smallErrorRecurrence
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (hsmall : ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤ 1 / 2) :
    kt19ErrorRate
      (kt19FixedPrimeSuccessorDistribution family distribution port).mass ≤
      KT19DistillationFamily.smallErrorRecurrenceConstant family *
        kt19ErrorRate distribution.mass ^ (l + 1 - k) := by
  change kt19ErrorRate
      (kt19SelectedPortLabelDistribution family distribution.mass
        distribution.mass_nonneg distribution.mass_sum port) ≤ _
  rw [kt19SelectedPortErrorRate_eq_outputPortError family distribution.mass
    distribution.mass_nonneg distribution.mass_sum port]
  letI : Nonempty (Fin k) := KT19DistillationFamily.outputPort_nonempty family
  calc
    kt19OutputPortError
        (family.run distribution.mass distribution.mass_nonneg
          distribution.mass_sum).acceptedOutput port ≤
        KT19DistillationFamily.outputWorstPortError family distribution.mass
          distribution.mass_nonneg distribution.mass_sum :=
      kt19OutputPortError_le_worst _ _
    _ ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family *
          kt19ErrorRate distribution.mass ^ (l + 1 - k) :=
      KT19DistillationFamily.outputWorstPortError_le_smallErrorRecurrence family
        distribution.mass distribution.mass_nonneg distribution.mass_sum hsmall

/-- The source-safe `l-k` recurrence follows from #883's exact
`l+1-k` distance law and the proved probability bound on every actual
selected-path distribution. -/
private theorem kt19FixedPrimeSuccessorError_le_distanceRecurrence
    (family : KT19DistillationFamily p l k)
    (distribution : KT19FixedPrimeDistribution p) (port : Fin k)
    (hsmall : ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤ 1 / 2) :
    kt19ErrorRate
      (kt19FixedPrimeSuccessorDistribution family distribution port).mass ≤
      KT19DistillationFamily.smallErrorRecurrenceConstant family *
        kt19ErrorRate distribution.mass ^ (l - k) := by
  have hkl : k ≤ l := family.admissible.2.2.1
  have herr_nonneg : 0 ≤ kt19ErrorRate distribution.mass :=
    kt19ErrorRate_nonneg distribution.mass distribution.mass_nonneg
      distribution.mass_sum
  have herr_le_one : kt19ErrorRate distribution.mass ≤ 1 :=
    kt19ErrorRate_le_one distribution.mass distribution.mass_nonneg
  have hpower : kt19ErrorRate distribution.mass ^ (l + 1 - k) ≤
      kt19ErrorRate distribution.mass ^ (l - k) := by
    calc
      kt19ErrorRate distribution.mass ^ (l + 1 - k) =
          kt19ErrorRate distribution.mass ^ (l - k) *
            kt19ErrorRate distribution.mass := by
              rw [show l + 1 - k = (l - k) + 1 by omega, pow_succ]
      _ ≤ kt19ErrorRate distribution.mass ^ (l - k) * 1 :=
        mul_le_mul_of_nonneg_left herr_le_one
          (pow_nonneg herr_nonneg _)
      _ = kt19ErrorRate distribution.mass ^ (l - k) := by ring
  have hconstant_nonneg :
      0 ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family := by
    unfold KT19DistillationFamily.smallErrorRecurrenceConstant
    positivity
  calc
    kt19ErrorRate
        (kt19FixedPrimeSuccessorDistribution family distribution port).mass ≤
        KT19DistillationFamily.smallErrorRecurrenceConstant family *
          kt19ErrorRate distribution.mass ^ (l + 1 - k) :=
      kt19FixedPrimeSuccessorError_le_smallErrorRecurrence family distribution port
        hsmall
    _ ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family *
          kt19ErrorRate distribution.mass ^ (l - k) :=
      mul_le_mul_of_nonneg_left hpower hconstant_nonneg

/-- A local scale dominating both the physical retained-slot count and the
proved #883 recurrence coefficient.  It is derived from those quantities,
not attached as a property of a family record. -/
private noncomputable def kt19FixedPrimeIterationScale
    (family : KT19DistillationFamily p l k) : ℝ :=
  KT19DistillationFamily.smallErrorRecurrenceConstant family +
    4 * ((p - k : Nat) : ℝ) + 1

private theorem kt19FixedPrimeRecurrenceConstant_nonneg
    (family : KT19DistillationFamily p l k) :
    0 ≤ KT19DistillationFamily.smallErrorRecurrenceConstant family := by
  unfold KT19DistillationFamily.smallErrorRecurrenceConstant
  positivity

/-- The locally derived scale is at least one. -/
private theorem kt19FixedPrimeIterationScale_one_le
    (family : KT19DistillationFamily p l k) :
    1 ≤ kt19FixedPrimeIterationScale family := by
  unfold kt19FixedPrimeIterationScale
  have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  nlinarith [kt19FixedPrimeRecurrenceConstant_nonneg family, hcount_nonneg]

/-- The scale visibly retains four times the actual retained input count for
the later physical path-yield budget. -/
private theorem kt19FixedPrime_four_mul_inputCount_le_iterationScale
    (family : KT19DistillationFamily p l k) :
    4 * ((p - k : Nat) : ℝ) ≤ kt19FixedPrimeIterationScale family := by
  unfold kt19FixedPrimeIterationScale
  have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  nlinarith [kt19FixedPrimeRecurrenceConstant_nonneg family, hcount_nonneg]

private theorem kt19FixedPrimeIterationScale_pos
    (family : KT19DistillationFamily p l k) :
    0 < kt19FixedPrimeIterationScale family :=
  lt_of_lt_of_le zero_lt_one (kt19FixedPrimeIterationScale_one_le family)

/-- Under the genuine contractive distance condition, the scale dominates
the recurrence coefficient at the required predecessor power. -/
private theorem kt19FixedPrimeRecurrenceConstant_le_scale_pow_pred
    (family : KT19DistillationFamily p l k) (hdistance : 2 ≤ l - k) :
    KT19DistillationFamily.smallErrorRecurrenceConstant family ≤
      kt19FixedPrimeIterationScale family ^ (l - k - 1) := by
  have hpred : 1 ≤ l - k - 1 := by omega
  calc
    KT19DistillationFamily.smallErrorRecurrenceConstant family ≤
        kt19FixedPrimeIterationScale family := by
      unfold kt19FixedPrimeIterationScale
      have hcount_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
      nlinarith [hcount_nonneg]
    _ = kt19FixedPrimeIterationScale family ^ 1 := by simp
    _ ≤ kt19FixedPrimeIterationScale family ^ (l - k - 1) :=
      pow_le_pow_right₀ (kt19FixedPrimeIterationScale_one_le family) hpred

/-- The explicit small root domain from which each literal successor's
physical small-error premise is derived. -/
private def kt19FixedPrimeInitialSmallDomain
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) : Prop :=
  kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass ≤ 1 / 4

/-- The separate uniform envelope for actual selected-path IID error rates.
The path-dependent rates remain physical objects; this is only a proved
upper-bound schedule. -/
private noncomputable def kt19FixedPrimeErrorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) : Nat → ℝ
  | 0 => kt19ErrorRate initial.mass
  | depth + 1 =>
      kt19FixedPrimeIterationScale family ^ (l - k - 1) *
        (kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k)

/-- The envelope has the exact double-power closed form required for the
fixed-prime error and cost schedule. -/
private theorem kt19FixedPrimeErrorEnvelope_closed_form
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (depth : Nat) :
    kt19FixedPrimeIterationScale family *
        kt19FixedPrimeErrorEnvelope family initial depth =
      (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^
        ((l - k) ^ depth) := by
  have hdistance_one : 1 ≤ l - k := hdistance.trans' (by omega)
  induction depth with
  | zero =>
      simp [kt19FixedPrimeErrorEnvelope]
  | succ depth ih =>
      calc
        kt19FixedPrimeIterationScale family *
            kt19FixedPrimeErrorEnvelope family initial (depth + 1) =
            (kt19FixedPrimeIterationScale family *
              kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k) := by
          simp only [kt19FixedPrimeErrorEnvelope]
          rw [mul_pow]
          have hsub : l - k - 1 + 1 = l - k :=
            Nat.sub_add_cancel hdistance_one
          calc
            kt19FixedPrimeIterationScale family *
                (kt19FixedPrimeIterationScale family ^ (l - k - 1) *
                  kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k)) =
                (kt19FixedPrimeIterationScale family ^ (l - k - 1) *
                  kt19FixedPrimeIterationScale family) *
                  kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) := by
                    ring
            _ = kt19FixedPrimeIterationScale family ^ (l - k) *
                  kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) := by
                    rw [← pow_succ, hsub]
        _ = ((kt19FixedPrimeIterationScale family *
            kt19ErrorRate initial.mass) ^ ((l - k) ^ depth)) ^ (l - k) := by
              rw [ih]
        _ = (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^
            ((l - k) ^ (depth + 1)) := by
              rw [← pow_mul, pow_succ]

private theorem kt19FixedPrimeErrorEnvelope_nonneg
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    0 ≤ kt19FixedPrimeErrorEnvelope family initial depth := by
  induction depth with
  | zero =>
      exact kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum
  | succ depth ih =>
      simp only [kt19FixedPrimeErrorEnvelope]
      exact mul_nonneg
        (pow_nonneg (kt19FixedPrimeIterationScale_pos family).le _)
        (pow_nonneg ih _)

/-- Every envelope point stays in the scale-selected small domain. -/
private theorem kt19FixedPrimeErrorEnvelope_scaled_small
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeIterationScale family *
      kt19FixedPrimeErrorEnvelope family initial depth ≤ 1 / 4 := by
  rw [kt19FixedPrimeErrorEnvelope_closed_form family initial hdistance]
  have hbase_nonneg : 0 ≤
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hpower : 1 ≤ (l - k) ^ depth :=
    one_le_pow₀ (hdistance.trans' (by omega))
  calc
    (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^
        ((l - k) ^ depth) ≤ (1 / 4 : ℝ) ^ ((l - k) ^ depth) :=
      pow_le_pow_left₀ hbase_nonneg hsmall _
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpower
    _ = 1 / 4 := by norm_num

/-- One envelope step contracts by at least a factor of four. -/
private theorem kt19FixedPrimeErrorEnvelope_succ_le_quarter
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeErrorEnvelope family initial (depth + 1) ≤
      kt19FixedPrimeErrorEnvelope family initial depth / 4 := by
  have hpred : 1 ≤ l - k - 1 := by omega
  have henvelope_nonneg : 0 ≤ kt19FixedPrimeErrorEnvelope family initial depth :=
    kt19FixedPrimeErrorEnvelope_nonneg family initial depth
  have hpower :
      (kt19FixedPrimeIterationScale family *
        kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) ≤ 1 / 4 := by
    calc
      (kt19FixedPrimeIterationScale family *
          kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) ≤
          (1 / 4 : ℝ) ^ (l - k - 1) :=
        pow_le_pow_left₀
          (mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
            henvelope_nonneg)
          (kt19FixedPrimeErrorEnvelope_scaled_small family initial hdistance
            hsmall depth) _
      _ ≤ (1 / 4 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hpred
      _ = 1 / 4 := by norm_num
  have hfactor :
      kt19FixedPrimeIterationScale family ^ (l - k - 1) *
          kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) =
        kt19FixedPrimeErrorEnvelope family initial depth *
          (kt19FixedPrimeIterationScale family *
            kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) := by
    rw [mul_pow]
    have hsub : l - k - 1 + 1 = l - k :=
      Nat.sub_add_cancel (by omega)
    calc
      kt19FixedPrimeIterationScale family ^ (l - k - 1) *
          kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) =
          kt19FixedPrimeIterationScale family ^ (l - k - 1) *
            kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k - 1 + 1) := by
              rw [hsub]
      _ = kt19FixedPrimeIterationScale family ^ (l - k - 1) *
            (kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k - 1) *
              kt19FixedPrimeErrorEnvelope family initial depth) := by
              rw [pow_succ]
      _ = kt19FixedPrimeErrorEnvelope family initial depth *
            (kt19FixedPrimeIterationScale family ^ (l - k - 1) *
              kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k - 1)) := by
              ring
  calc
    kt19FixedPrimeErrorEnvelope family initial (depth + 1) =
        kt19FixedPrimeIterationScale family ^ (l - k - 1) *
          kt19FixedPrimeErrorEnvelope family initial depth ^ (l - k) := rfl
    _ = kt19FixedPrimeErrorEnvelope family initial depth *
          (kt19FixedPrimeIterationScale family *
            kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k - 1) := hfactor
    _ ≤ kt19FixedPrimeErrorEnvelope family initial depth * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower henvelope_nonneg
    _ = kt19FixedPrimeErrorEnvelope family initial depth / 4 := by ring

/-- The finite envelope sum together with its geometric tail is bounded by
the actual root IID error. -/
private theorem kt19FixedPrimeErrorEnvelope_sum_with_tail_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) +
      (4 / 3 : ℝ) * kt19FixedPrimeErrorEnvelope family initial depth ≤
        (4 / 3 : ℝ) * kt19ErrorRate initial.mass := by
  induction depth with
  | zero =>
      change 0 + (4 / 3 : ℝ) * kt19ErrorRate initial.mass ≤
        (4 / 3 : ℝ) * kt19ErrorRate initial.mass
      linarith
  | succ depth ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hnext := kt19FixedPrimeErrorEnvelope_succ_le_quarter family initial
        hdistance hsmall depth
      nlinarith

/-- The finite envelope sum has the corresponding uniform geometric bound. -/
private theorem kt19FixedPrimeErrorEnvelope_sum_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    ∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1 ≤
      (4 / 3 : ℝ) * kt19ErrorRate initial.mass := by
  calc
    ∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1 ≤
        (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) +
          (4 / 3 : ℝ) * kt19FixedPrimeErrorEnvelope family initial depth := by
      exact le_add_of_nonneg_right
        (mul_nonneg (by norm_num)
          (kt19FixedPrimeErrorEnvelope_nonneg family initial depth))
    _ ≤ (4 / 3 : ℝ) * kt19ErrorRate initial.mass :=
      kt19FixedPrimeErrorEnvelope_sum_with_tail_le family initial hdistance hsmall depth

/-- The visible input-count term in the scale turns the finite envelope sum
into the physical path-loss budget used by literal success products. -/
private theorem kt19FixedPrimeInputCount_mul_envelope_sum_le_one_sixth
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    ((p - k : Nat) : ℝ) *
      (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) ≤
        1 / 6 := by
  have hcount_nonneg : 0 ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  have hcount_scale :=
    kt19FixedPrime_four_mul_inputCount_le_iterationScale family
  have hscaled_product :
      (4 * ((p - k : Nat) : ℝ)) * kt19ErrorRate initial.mass ≤
        kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_le_mul_of_nonneg_right hcount_scale
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hcount_error : ((p - k : Nat) : ℝ) * kt19ErrorRate initial.mass ≤ 1 / 16 := by
    change kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass ≤ 1 / 4 at hsmall
    nlinarith [hscaled_product, hsmall]
  calc
    ((p - k : Nat) : ℝ) *
        (∑ stage : Fin depth, kt19FixedPrimeErrorEnvelope family initial stage.1) ≤
        ((p - k : Nat) : ℝ) * ((4 / 3 : ℝ) * kt19ErrorRate initial.mass) :=
      mul_le_mul_of_nonneg_left
        (kt19FixedPrimeErrorEnvelope_sum_le family initial hdistance hsmall depth)
        hcount_nonneg
    _ = (4 / 3 : ℝ) * (((p - k : Nat) : ℝ) * kt19ErrorRate initial.mass) := by
      ring
    _ ≤ (4 / 3 : ℝ) * (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left hcount_error (by norm_num)
    _ ≤ 1 / 6 := by norm_num

/-- Each literal path error is bounded by the uniform envelope at the same
depth.  The successor step is the actual selected marginal recurrence, with
its small-domain witness derived internally from the envelope. -/
private theorem kt19FixedPrimePathError_le_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) :
    ∀ (depth : Nat) (path : kt19FixedPrimeOutputSlots k depth),
      kt19FixedPrimePathError family initial depth path ≤
        kt19FixedPrimeErrorEnvelope family initial depth := by
  intro depth
  induction depth with
  | zero =>
      intro path
      simp [kt19FixedPrimePathError, kt19FixedPrimePathDistribution,
        kt19FixedPrimeErrorEnvelope]
  | succ depth ih =>
      intro path
      let priorPath := kt19FixedPrimeOutputPathInit k depth path
      let port := kt19FixedPrimeOutputPathLast k depth path
      let prior := kt19FixedPrimePathDistribution family initial depth priorPath
      have hprior : kt19ErrorRate prior.mass ≤
          kt19FixedPrimeErrorEnvelope family initial depth := by
        simpa [prior, priorPath, kt19FixedPrimePathError] using ih priorPath
      have hscaled : kt19FixedPrimeIterationScale family *
          kt19ErrorRate prior.mass ≤ 1 / 4 := by
        calc
          kt19FixedPrimeIterationScale family * kt19ErrorRate prior.mass ≤
              kt19FixedPrimeIterationScale family *
                kt19FixedPrimeErrorEnvelope family initial depth :=
            mul_le_mul_of_nonneg_left hprior
              (kt19FixedPrimeIterationScale_pos family).le
          _ ≤ 1 / 4 :=
            kt19FixedPrimeErrorEnvelope_scaled_small family initial hdistance
              hsmall depth
      have hlocal : ((p - k : Nat) : ℝ) * kt19ErrorRate prior.mass ≤ 1 / 2 := by
        have hcount_scale :=
          kt19FixedPrime_four_mul_inputCount_le_iterationScale family
        have hcount_nonneg : 0 ≤ kt19ErrorRate prior.mass :=
          kt19ErrorRate_nonneg prior.mass prior.mass_nonneg prior.mass_sum
        have hmult : (4 * ((p - k : Nat) : ℝ)) * kt19ErrorRate prior.mass ≤
            kt19FixedPrimeIterationScale family * kt19ErrorRate prior.mass :=
          mul_le_mul_of_nonneg_right hcount_scale hcount_nonneg
        nlinarith
      have hrecurrence :=
        kt19FixedPrimeSuccessorError_le_distanceRecurrence family prior port hlocal
      have hcoefficient :=
        kt19FixedPrimeRecurrenceConstant_le_scale_pow_pred family hdistance
      have hprior_nonneg : 0 ≤ kt19ErrorRate prior.mass :=
        kt19ErrorRate_nonneg prior.mass prior.mass_nonneg prior.mass_sum
      change kt19ErrorRate
          (kt19FixedPrimeSuccessorDistribution family
            (kt19FixedPrimePathDistribution family initial depth
              (kt19FixedPrimeOutputPathInit k depth path))
            (kt19FixedPrimeOutputPathLast k depth path)).mass ≤ _
      calc
        kt19ErrorRate
            (kt19FixedPrimeSuccessorDistribution family prior port).mass ≤
            KT19DistillationFamily.smallErrorRecurrenceConstant family *
              kt19ErrorRate prior.mass ^ (l - k) := hrecurrence
        _ ≤ kt19FixedPrimeIterationScale family ^ (l - k - 1) *
              kt19ErrorRate prior.mass ^ (l - k) :=
          mul_le_mul_of_nonneg_right hcoefficient
            (pow_nonneg hprior_nonneg _)
        _ ≤ kt19FixedPrimeIterationScale family ^ (l - k - 1) *
              (kt19FixedPrimeErrorEnvelope family initial depth) ^ (l - k) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hprior_nonneg hprior _)
            (pow_nonneg (kt19FixedPrimeIterationScale_pos family).le _)
        _ = kt19FixedPrimeErrorEnvelope family initial (depth + 1) := rfl

/-- The actual error of a path stage is bounded by the same envelope at the
literal stage prefix. -/
private theorem kt19FixedPrimePathStageError_le_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    kt19FixedPrimePathError family initial stage.1
      (kt19FixedPrimePathStagePath k depth path stage) ≤
        kt19FixedPrimeErrorEnvelope family initial stage.1 :=
  kt19FixedPrimePathError_le_errorEnvelope family initial hdistance hsmall
    stage.1 (kt19FixedPrimePathStagePath k depth path stage)

/-- At every literal path stage, the all-zero accepted word bounds the actual
KT19 run success probability from below. -/
private theorem kt19FixedPrimePathStageRun_success_one_sub_inputCount_error_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) (stage : Fin depth) :
    1 - ((p - k : Nat) : ℝ) *
      kt19FixedPrimePathError family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage) ≤
      (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
  let distribution := kt19FixedPrimePathDistribution family initial stage.1
    (kt19FixedPrimePathStagePath k depth path stage)
  change 1 - ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤
    (family.run distribution.mass distribution.mass_nonneg
      distribution.mass_sum).successProbability
  rw [KT19DistillationFamily.run, kt19Run_successProbability]
  change 1 - ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤
    kt19Success family.rowFamily distribution.mass distribution.mass_nonneg
      distribution.mass_sum
  have herr_nonneg : 0 ≤ kt19ErrorRate distribution.mass :=
    kt19ErrorRate_nonneg distribution.mass distribution.mass_nonneg
      distribution.mass_sum
  have herr_le_one : kt19ErrorRate distribution.mass ≤ 1 :=
    kt19ErrorRate_le_one distribution.mass distribution.mass_nonneg
  calc
    1 - ((p - k : Nat) : ℝ) * kt19ErrorRate distribution.mass ≤
        (1 - kt19ErrorRate distribution.mass) ^ (p - k) := by
      have hbernoulli := one_add_mul_sub_le_pow
        (a := 1 - kt19ErrorRate distribution.mass) (by linarith) (p - k)
      convert hbernoulli using 1 <;> first | rfl | ring
    _ ≤ kt19Success family.rowFamily distribution.mass distribution.mass_nonneg
          distribution.mass_sum :=
      KT19DistillationFamily.success_ge_one_sub_errorRate_pow family
        distribution.mass distribution.mass_nonneg distribution.mass_sum

/-- A finite product of factors in the unit interval is bounded below by one
minus the sum of their individual losses. -/
private theorem kt19FixedPrimeFiniteOneSubSum_le_product {ι : Type*}
    (s : Finset ι) (loss : ι → ℝ)
    (hloss_nonneg : ∀ item ∈ s, 0 ≤ loss item)
    (hloss_le_one : ∀ item ∈ s, loss item ≤ 1) :
    1 - ∑ item ∈ s, loss item ≤ ∏ item ∈ s, (1 - loss item) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert item s hitem ih =>
      rw [Finset.sum_insert hitem, Finset.prod_insert hitem]
      have hsum_nonneg : 0 ≤ ∑ other ∈ s, loss other :=
        Finset.sum_nonneg fun other hother =>
          hloss_nonneg other (Finset.mem_insert_of_mem hother)
      have hrest : 1 - ∑ item ∈ s, loss item ≤
          ∏ item ∈ s, (1 - loss item) :=
        ih (fun other hother => hloss_nonneg other
          (Finset.mem_insert_of_mem hother))
          (fun other hother => hloss_le_one other
            (Finset.mem_insert_of_mem hother))
      calc
        1 - (loss item + ∑ other ∈ s, loss other) ≤
            (1 - loss item) * (1 - ∑ other ∈ s, loss other) := by
          nlinarith [hloss_nonneg item (Finset.mem_insert_self item s),
            hsum_nonneg]
        _ ≤ (1 - loss item) * ∏ other ∈ s, (1 - loss other) :=
          mul_le_mul_of_nonneg_left hrest
            (by linarith [hloss_le_one item (Finset.mem_insert_self item s)])

/-- The physical retained-site weighted losses along every literal output
path obey the uniform envelope budget. -/
private theorem kt19FixedPrimePathLoss_sum_le_one_sixth
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    ∑ stage : Fin depth, ((p - k : Nat) : ℝ) *
      kt19FixedPrimePathError family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage) ≤ 1 / 6 := by
  rw [← Finset.mul_sum]
  calc
    ((p - k : Nat) : ℝ) *
        ∑ stage : Fin depth,
          kt19FixedPrimePathError family initial stage.1
            (kt19FixedPrimePathStagePath k depth path stage) ≤
        ((p - k : Nat) : ℝ) *
          ∑ stage : Fin depth,
            kt19FixedPrimeErrorEnvelope family initial stage.1 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun stage _ =>
          kt19FixedPrimePathStageError_le_errorEnvelope family initial hdistance
            hsmall depth path stage)
        (Nat.cast_nonneg _)
    _ ≤ 1 / 6 :=
      kt19FixedPrimeInputCount_mul_envelope_sum_le_one_sixth family initial
        hdistance hsmall depth

/-- The actual fresh-stage success product of every output path is uniformly
bounded below by five sixths.  This is a pathwise accounting statement, not a
simultaneous-success claim over the branching construction. -/
private theorem kt19FixedPrimePathYieldFactor_five_sixths_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    (5 / 6 : ℝ) ≤ (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) := by
  classical
  let loss : Fin depth → ℝ := fun stage =>
    ((p - k : Nat) : ℝ) *
      kt19FixedPrimePathError family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage)
  have hloss_nonneg (stage : Fin depth) : 0 ≤ loss stage := by
    dsimp [loss]
    exact mul_nonneg (Nat.cast_nonneg _)
      (kt19FixedPrimePathError_nonneg family initial stage.1
        (kt19FixedPrimePathStagePath k depth path stage))
  have hsum_loss : ∑ stage : Fin depth, loss stage ≤ 1 / 6 := by
    simpa only [loss] using
      kt19FixedPrimePathLoss_sum_le_one_sixth family initial hdistance hsmall
        depth path
  have hloss_le_one (stage : Fin depth) : loss stage ≤ 1 := by
    calc
      loss stage ≤ ∑ other : Fin depth, loss other :=
        Finset.single_le_sum (fun other _ => hloss_nonneg other)
          (Finset.mem_univ stage)
      _ ≤ 1 / 6 := hsum_loss
      _ ≤ 1 := by norm_num
  have hproduct_lower :
      1 - ∑ stage : Fin depth, loss stage ≤
        ∏ stage : Fin depth,
          (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
    calc
      1 - ∑ stage : Fin depth, loss stage ≤
          ∏ stage : Fin depth, (1 - loss stage) := by
        simpa using (kt19FixedPrimeFiniteOneSubSum_le_product Finset.univ loss
          (fun stage _ => hloss_nonneg stage)
          (fun stage _ => hloss_le_one stage))
      _ ≤ ∏ stage : Fin depth,
          (kt19FixedPrimePathStageRun family initial depth path stage).successProbability := by
        refine Finset.prod_le_prod ?_ ?_
        · intro stage _
          linarith [hloss_le_one stage]
        · intro stage _
          dsimp [loss]
          exact kt19FixedPrimePathStageRun_success_one_sub_inputCount_error_le
            family initial depth path stage
  rw [kt19FixedPrimePathYieldFactor_eq_actualStageSuccessProduct]
  linarith

/-- Averaging the literal finite path survival factors preserves their
uniform five-sixths lower bound. -/
private theorem kt19FixedPrimePooledYield_five_sixths_le
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    (5 / 6 : ℝ) ≤ (kt19FixedPrimePooledYield family initial depth : ℝ) := by
  classical
  have hcard : 0 < (Fintype.card (kt19FixedPrimeOutputSlots k depth) : ℝ) := by
    exact_mod_cast kt19FixedPrimeOutputSlots_card_pos family depth
  rw [kt19FixedPrimePooledYield_eq_sum_div_card]
  apply (le_div_iff₀ hcard).mpr
  calc
    (5 / 6 : ℝ) * Fintype.card (kt19FixedPrimeOutputSlots k depth) =
        ∑ path : kt19FixedPrimeOutputSlots k depth, (5 / 6 : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    _ ≤ ∑ path : kt19FixedPrimeOutputSlots k depth,
        (kt19FixedPrimePathYieldFactor family initial depth path : ℝ) :=
      Finset.sum_le_sum fun path _ =>
        kt19FixedPrimePathYieldFactor_five_sixths_le family initial hdistance
          hsmall depth path

private theorem kt19FixedPrimePooledYield_pos
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    0 < (kt19FixedPrimePooledYield family initial depth : ℝ) :=
  lt_of_lt_of_le (by norm_num)
    (kt19FixedPrimePooledYield_five_sixths_le family initial hdistance hsmall depth)

/-- The reached physical output error is the finite maximum over literal
selected-port path marginals at that depth. -/
private noncomputable def kt19FixedPrimeReachedOutputError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) : ℝ := by
  classical
  exact Finset.univ.sup'
    ⟨(kt19FixedPrimeOutputSlots_nonempty family depth).some, Finset.mem_univ _⟩
    fun path => kt19FixedPrimePathError family initial depth path

private theorem kt19FixedPrimePathError_le_reachedOutputError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat)
    (path : kt19FixedPrimeOutputSlots k depth) :
    kt19FixedPrimePathError family initial depth path ≤
      kt19FixedPrimeReachedOutputError family initial depth := by
  classical
  unfold kt19FixedPrimeReachedOutputError
  exact Finset.le_sup' (fun other =>
    kt19FixedPrimePathError family initial depth other) (Finset.mem_univ path)

private theorem kt19FixedPrimeReachedOutputError_nonneg
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (depth : Nat) :
    0 ≤ kt19FixedPrimeReachedOutputError family initial depth := by
  classical
  unfold kt19FixedPrimeReachedOutputError
  obtain ⟨path, _, hpath⟩ := Finset.exists_mem_eq_sup'
    ⟨(kt19FixedPrimeOutputSlots_nonempty family depth).some, Finset.mem_univ _⟩
    (fun path => kt19FixedPrimePathError family initial depth path)
  rw [hpath]
  exact kt19FixedPrimePathError_nonneg family initial depth path

/-- The finite maximum of actual selected-path errors remains bounded by the
separate fixed-prime envelope. -/
private theorem kt19FixedPrimeReachedOutputError_le_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeReachedOutputError family initial depth ≤
      kt19FixedPrimeErrorEnvelope family initial depth := by
  classical
  unfold kt19FixedPrimeReachedOutputError
  apply Finset.sup'_le
  intro path _
  exact kt19FixedPrimePathError_le_errorEnvelope family initial hdistance hsmall
    depth path

/-! ## Public fixed-prime target and accounting interface -/

/-- Package an approved literal IID label law as the root of the routed
physical construction.  This contains only input distribution facts. -/
private def kt19FixedPrimeInitialDistribution
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) : KT19FixedPrimeDistribution p where
  mass := mu
  mass_nonneg := hmu_nonneg
  mass_sum := hmu_sum

/-- The fixed-prime target error schedule extracted from the actual root IID
error and the proved recurrence scale. -/
noncomputable def kt19FixedPrimeScheduleTargetError
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) (depth : Nat) : ℝ :=
  (kt19FixedPrimeIterationScale family * kt19ErrorRate mu) ^ ((l - k) ^ depth)

/-- The actual reached error: a finite maximum over literal selected-port
paths of the routed physical construction. -/
noncomputable def kt19FixedPrimeActualOutputError
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (depth : Nat) : ℝ :=
  kt19FixedPrimeReachedOutputError family
    (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth

/-- The normalized pooled expected yield over all actual finite output paths. -/
noncomputable def kt19FixedPrimeExpectedYield
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (depth : Nat) : NNReal :=
  kt19FixedPrimePooledYield family
    (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth

/-- The literal typed successful-output cost of the fixed-prime routed
construction, derived from its actual input/output slot carriers and pooled
yield. -/
noncomputable def kt19FixedPrimeSuccessfulOutputCost
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (depth : Nat) : ℝ :=
  kt19FixedPrimeTypedSuccessfulOutputCost family
    (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth

private theorem kt19FixedPrimeScheduleTargetError_eq_scale_mul_errorEnvelope
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (depth : Nat) :
    kt19FixedPrimeScheduleTargetError family initial.mass depth =
      kt19FixedPrimeIterationScale family *
        kt19FixedPrimeErrorEnvelope family initial depth := by
  unfold kt19FixedPrimeScheduleTargetError
  exact (kt19FixedPrimeErrorEnvelope_closed_form family initial hdistance depth).symm

private theorem kt19FixedPrimeScheduleTargetError_pos
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p)
    (hepsilon : 0 < kt19ErrorRate initial.mass) (depth : Nat) :
    0 < kt19FixedPrimeScheduleTargetError family initial.mass depth := by
  unfold kt19FixedPrimeScheduleTargetError
  exact pow_pos (mul_pos (kt19FixedPrimeIterationScale_pos family) hepsilon) _

private theorem kt19FixedPrimeScheduleTargetError_lt_one
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeScheduleTargetError family initial.mass depth < 1 := by
  unfold kt19FixedPrimeScheduleTargetError
  have hbase_nonneg : 0 ≤
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hbase_lt_one :
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass < 1 :=
    hsmall.trans_lt (by norm_num)
  have hpower_pos : 0 < (l - k) ^ depth :=
    pow_pos (show 0 < l - k by omega) _
  exact pow_lt_one₀ hbase_nonneg hbase_lt_one (ne_of_gt hpower_pos)

/-- The target error double-power schedule tends to zero for every fixed
contractive KT19 family in the explicit root small domain. -/
theorem kt19FixedPrimeTargetError_tendsto_zero
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    Tendsto (fun depth : Nat =>
      kt19FixedPrimeScheduleTargetError family mu depth) atTop (𝓝 0) := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hbase_nonneg : 0 ≤
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass :=
    mul_nonneg (kt19FixedPrimeIterationScale_pos family).le
      (kt19ErrorRate_nonneg initial.mass initial.mass_nonneg initial.mass_sum)
  have hbase_lt_one :
      kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass < 1 := by
    change kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4 at hsmall
    exact hsmall.trans_lt (by norm_num : (1 / 4 : ℝ) < 1)
  have hpow : Tendsto (fun exponent : Nat =>
      (kt19FixedPrimeIterationScale family * kt19ErrorRate initial.mass) ^ exponent)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one
  have hgrowth : Tendsto (fun depth : Nat => (l - k) ^ depth) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  exact hpow.comp hgrowth

/-- The actual finite maximum of selected-path physical errors lies below the
separate target schedule. -/
private theorem kt19FixedPrimeReachedOutputError_le_scheduleTargetError
    (family : KT19DistillationFamily p l k)
    (initial : KT19FixedPrimeDistribution p) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeInitialSmallDomain family initial) (depth : Nat) :
    kt19FixedPrimeReachedOutputError family initial depth ≤
      kt19FixedPrimeScheduleTargetError family initial.mass depth := by
  calc
    kt19FixedPrimeReachedOutputError family initial depth ≤
        kt19FixedPrimeErrorEnvelope family initial depth :=
      kt19FixedPrimeReachedOutputError_le_errorEnvelope family initial hdistance
        hsmall depth
    _ ≤ kt19FixedPrimeIterationScale family *
          kt19FixedPrimeErrorEnvelope family initial depth := by
      nlinarith [kt19FixedPrimeIterationScale_one_le family,
        kt19FixedPrimeErrorEnvelope_nonneg family initial depth]
    _ = kt19FixedPrimeScheduleTargetError family initial.mass depth :=
      (kt19FixedPrimeScheduleTargetError_eq_scale_mul_errorEnvelope family initial
        hdistance depth).symm

/-- The public actual output error is bounded by the explicit fixed-prime
target schedule. -/
theorem kt19FixedPrimeActualOutputError_le_scheduleTargetError
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth ≤
      kt19FixedPrimeScheduleTargetError family mu depth := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hsmall_initial : kt19FixedPrimeInitialSmallDomain family initial := by
    exact hsmall
  exact kt19FixedPrimeReachedOutputError_le_scheduleTargetError family initial
    hdistance hsmall_initial depth

/-- The actual selected-path output error therefore tends to zero, rather
than merely an auxiliary envelope or advertised target. -/
theorem kt19FixedPrimeActualOutputError_tendsto_zero
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    Tendsto (fun depth : Nat =>
      kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth)
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    (kt19FixedPrimeTargetError_tendsto_zero family mu hmu_nonneg hmu_sum
      hdistance hepsilon hsmall)
    (fun depth => by
      unfold kt19FixedPrimeActualOutputError
      exact kt19FixedPrimeReachedOutputError_nonneg family
        (kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum) depth)
    (fun depth => kt19FixedPrimeActualOutputError_le_scheduleTargetError family mu
      hmu_nonneg hmu_sum hdistance hsmall depth)

/-- The public pooled yield has the uniform physical lower bound obtained
from literal per-path products. -/
theorem kt19FixedPrimeExpectedYield_five_sixths_le
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    (5 / 6 : ℝ) ≤
      (kt19FixedPrimeExpectedYield family mu hmu_nonneg hmu_sum depth : ℝ) := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hsmall_initial : kt19FixedPrimeInitialSmallDomain family initial := by
    exact hsmall
  simpa [kt19FixedPrimeExpectedYield, initial] using
    kt19FixedPrimePooledYield_five_sixths_le family initial hdistance
      hsmall_initial depth

theorem kt19FixedPrimeExpectedYield_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    0 < (kt19FixedPrimeExpectedYield family mu hmu_nonneg hmu_sum depth : ℝ) :=
  lt_of_lt_of_le (by norm_num)
    (kt19FixedPrimeExpectedYield_five_sixths_le family mu hmu_nonneg hmu_sum
      hdistance hsmall depth)

/-- The literal typed successful-output cost is controlled by the same
uniform physical pooled-yield lower bound. -/
theorem kt19FixedPrimeSuccessfulOutputCost_le_six_fifths
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeSuccessfulOutputCost family mu hmu_nonneg hmu_sum depth ≤
      (6 / 5 : ℝ) * ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) := by
  let initial := kt19FixedPrimeInitialDistribution mu hmu_nonneg hmu_sum
  have hsmall_initial : kt19FixedPrimeInitialSmallDomain family initial := by
    exact hsmall
  rw [kt19FixedPrimeSuccessfulOutputCost,
    kt19FixedPrimeTypedSuccessfulOutputCost_eq]
  have hinput_nonneg : (0 : ℝ) ≤ ((p - k : Nat) : ℝ) := Nat.cast_nonneg _
  have houtput_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hratio_nonneg : 0 ≤ ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) :=
    pow_nonneg (div_nonneg hinput_nonneg houtput_nonneg) _
  have hyield : (5 / 6 : ℝ) ≤
      (kt19FixedPrimePooledYield family initial depth : ℝ) :=
    kt19FixedPrimePooledYield_five_sixths_le family initial hdistance
      hsmall_initial depth
  calc
    ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) /
        (kt19FixedPrimePooledYield family initial depth : ℝ) ≤
        ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) / ((5 : ℝ) / 6) :=
      div_le_div_of_nonneg_left hratio_nonneg (by norm_num) hyield
    _ = (6 / 5 : ℝ) * ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) := by
      ring

/-- The fixed-prime cost exponent dictated by the literal retained/input and
logical/output slot ratio and the source-safe iteration distance. -/
noncomputable def kt19FixedPrimeGamma (p l k : Nat) : ℝ :=
  Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) / Real.log ((l - k : Nat) : ℝ)

/-- The exponent is written with the required ratio-over-distance form. -/
private theorem kt19FixedPrimeGamma_eq
    (p l k : Nat) :
    kt19FixedPrimeGamma p l k =
      Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
        Real.log ((l - k : Nat) : ℝ) :=
  rfl

private theorem kt19FixedPrimeInputCount_pos
    (family : KT19DistillationFamily p l k) : 0 < p - k := by
  rcases family.admissible with ⟨_, hk, hkl, hlp, htriple⟩
  have hp_five : 5 ≤ p := family.primeAtLeastFive.five_le
  omega

private theorem kt19FixedPrimeOutputCount_pos
    (family : KT19DistillationFamily p l k) : 0 < k := by
  have hk : 1 ≤ k := family.admissible.2.1
  omega

/-- The positive logarithmic growth base of the selected fixed-prime root
target. -/
private noncomputable def kt19FixedPrimeLogGrowthBase
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) : ℝ :=
  -Real.log (kt19FixedPrimeIterationScale family * kt19ErrorRate mu)

/-- The cost coefficient induced by literal five-sixths pooled yield and the
fixed initial target-log factor. -/
noncomputable def kt19FixedPrimeCostCoefficient
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ) : ℝ :=
  (6 / 5 : ℝ) /
    Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
      (kt19FixedPrimeGamma p l k)

/-- The real-power form of the exact fixed-prime exponent recovers the
literal finite input/output ratio at every depth. -/
private theorem kt19FixedPrime_rpow_distancePow_eq_inputOutputRatio_pow
    (family : KT19DistillationFamily p l k) (hdistance : 2 ≤ l - k)
    (depth : Nat) :
    Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) =
      ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) := by
  have hdistance_nat : 1 < l - k := by omega
  have hdistance_real : (1 : ℝ) < ((l - k : Nat) : ℝ) := by
    exact_mod_cast hdistance_nat
  have hratio : 0 < ((p - k : Nat) : ℝ) / (k : ℝ) := by
    apply div_pos
    · exact_mod_cast kt19FixedPrimeInputCount_pos family
    · exact_mod_cast kt19FixedPrimeOutputCount_pos family
  calc
    Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) =
        Real.exp (Real.log (((l - k : Nat) : ℝ) ^ depth) *
          kt19FixedPrimeGamma p l k) := by
          exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((depth : ℝ) *
        Real.log (((p - k : Nat) : ℝ) / (k : ℝ))) := by
      congr 1
      rw [Real.log_pow]
      rw [kt19FixedPrimeGamma_eq]
      field_simp [ne_of_gt (Real.log_pos hdistance_real)] <;> ring
    _ = Real.rpow (((p - k : Nat) : ℝ) / (k : ℝ)) (depth : ℝ) := by
      symm
      calc
        Real.rpow (((p - k : Nat) : ℝ) / (k : ℝ)) (depth : ℝ) =
            Real.exp (Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) *
              (depth : ℝ)) :=
          Real.rpow_def_of_pos hratio _
        _ = Real.exp ((depth : ℝ) *
            Real.log (((p - k : Nat) : ℝ) / (k : ℝ))) :=
          congrArg Real.exp (mul_comm _ _)
    _ = ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) :=
      Real.rpow_natCast _ _

private theorem kt19FixedPrimeLogGrowthBase_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    0 < kt19FixedPrimeLogGrowthBase family mu := by
  unfold kt19FixedPrimeLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (kt19FixedPrimeIterationScale_pos family) hepsilon
  · exact hsmall.trans_lt (by norm_num)

private theorem kt19FixedPrimeCostCoefficient_pos
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    0 < kt19FixedPrimeCostCoefficient family mu := by
  unfold kt19FixedPrimeCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (kt19FixedPrimeLogGrowthBase_pos family mu hmu_nonneg hmu_sum
        hepsilon hsmall) _)

private theorem kt19FixedPrime_distancePow_mul_logGrowthBase_eq_log
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hepsilon : 0 < kt19ErrorRate mu) (depth : Nat) :
    ((l - k : Nat) : ℝ) ^ depth * kt19FixedPrimeLogGrowthBase family mu =
      Real.log (1 / kt19FixedPrimeScheduleTargetError family mu depth) := by
  have hbase : 0 < kt19FixedPrimeIterationScale family * kt19ErrorRate mu :=
    mul_pos (kt19FixedPrimeIterationScale_pos family) hepsilon
  unfold kt19FixedPrimeScheduleTargetError
  rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hbase _)), Real.log_one,
    Real.log_pow]
  push_cast
  unfold kt19FixedPrimeLogGrowthBase
  ring

/-- The literal typed successful-output cost obeys the fixed-prime
polylogarithmic comparison at every finite physical depth. -/
theorem kt19FixedPrimeSuccessfulOutputCost_le_polylog
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeSuccessfulOutputCost family mu hmu_nonneg hmu_sum depth ≤
      kt19FixedPrimeCostCoefficient family mu *
        Real.rpow (Real.log
          (1 / kt19FixedPrimeScheduleTargetError family mu depth))
          (kt19FixedPrimeGamma p l k) := by
  have hbase : 0 < kt19FixedPrimeLogGrowthBase family mu :=
    kt19FixedPrimeLogGrowthBase_pos family mu hmu_nonneg hmu_sum hepsilon hsmall
  have hbase_rpow : 0 < Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
      (kt19FixedPrimeGamma p l k) :=
    Real.rpow_pos_of_pos hbase _
  have hlog := kt19FixedPrime_distancePow_mul_logGrowthBase_eq_log family mu
    hepsilon depth
  have hfactorization :
      Real.rpow (((l - k : Nat) : ℝ) ^ depth *
          kt19FixedPrimeLogGrowthBase family mu) (kt19FixedPrimeGamma p l k) =
        Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) *
          Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
            (kt19FixedPrimeGamma p l k) :=
    Real.mul_rpow (by positivity) hbase.le
  calc
    kt19FixedPrimeSuccessfulOutputCost family mu hmu_nonneg hmu_sum depth ≤
        (6 / 5 : ℝ) * ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) :=
      kt19FixedPrimeSuccessfulOutputCost_le_six_fifths family mu hmu_nonneg
        hmu_sum hdistance hsmall depth
    _ = (6 / 5 : ℝ) *
        Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) := by
      rw [kt19FixedPrime_rpow_distancePow_eq_inputOutputRatio_pow family
        hdistance depth]
    _ =
        ((6 / 5 : ℝ) *
          Real.rpow (((l - k : Nat) : ℝ) ^ depth) (kt19FixedPrimeGamma p l k) *
          Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
            (kt19FixedPrimeGamma p l k)) /
          Real.rpow (kt19FixedPrimeLogGrowthBase family mu)
            (kt19FixedPrimeGamma p l k) := by
      field_simp [ne_of_gt hbase_rpow]
    _ = kt19FixedPrimeCostCoefficient family mu *
        Real.rpow (((l - k : Nat) : ℝ) ^ depth *
          kt19FixedPrimeLogGrowthBase family mu) (kt19FixedPrimeGamma p l k) := by
      rw [hfactorization]
      unfold kt19FixedPrimeCostCoefficient
      field_simp [ne_of_gt hbase_rpow]
    _ = kt19FixedPrimeCostCoefficient family mu *
        Real.rpow (Real.log
          (1 / kt19FixedPrimeScheduleTargetError family mu depth))
          (kt19FixedPrimeGamma p l k) := by
      rw [hlog]

/-- The complete fixed-prime KT19 construction: literal selected-path runs
have vanishing physical output error and a typed successful-output cost bound
at the required logarithmic exponent. -/
theorem kt19FixedPrime
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    Tendsto (fun depth : Nat =>
      kt19FixedPrimeScheduleTargetError family mu depth) atTop (𝓝 0) ∧
      Tendsto (fun depth : Nat =>
        kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth)
        atTop (𝓝 0) ∧
      DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
        (fun depth => kt19FixedPrimeInputSlots p k depth)
        (fun depth => kt19FixedPrimeOutputSlots k depth)
        (kt19FixedPrimeScheduleTargetError family mu)
        (kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum)
        (kt19FixedPrimeExpectedYield family mu hmu_nonneg hmu_sum)
        (kt19FixedPrimeGamma p l k) (kt19FixedPrimeCostCoefficient family mu) := by
  refine ⟨kt19FixedPrimeTargetError_tendsto_zero family mu hmu_nonneg hmu_sum
      hdistance hepsilon hsmall,
    kt19FixedPrimeActualOutputError_tendsto_zero family mu hmu_nonneg hmu_sum
      hdistance hepsilon hsmall, ?_⟩
  refine ⟨(kt19FixedPrimeCostCoefficient_pos family mu hmu_nonneg hmu_sum
      hepsilon hsmall).le, ?_⟩
  intro depth _ _
  refine ⟨kt19FixedPrimeActualOutputError_le_scheduleTargetError family mu
      hmu_nonneg hmu_sum hdistance hsmall depth,
    kt19FixedPrimeExpectedYield_pos family mu hmu_nonneg hmu_sum hdistance
      hsmall depth, ?_⟩
  exact kt19FixedPrimeSuccessfulOutputCost_le_polylog family mu hmu_nonneg
    hmu_sum hdistance hepsilon hsmall depth

/-- On the congruence ray `p = 1 + 8t`, the displayed floor parameters become
literal linear functions of `t`.  This is the finite arithmetic behind the
changing-prime family; it is not an asymptotic replacement for the family. -/
private theorem kt19ExplicitParameters_eight_ray (t : Nat) :
    kt19ExplicitK (1 + 8 * t) = t ∧
      kt19ExplicitL (1 + 8 * t) = 2 * t ∧
      (1 + 8 * t) - kt19ExplicitK (1 + 8 * t) = 7 * t + 1 ∧
      kt19ExplicitL (1 + 8 * t) - kt19ExplicitK (1 + 8 * t) = t := by
  simp only [kt19ExplicitK, kt19ExplicitL]
  omega

/-- The concrete congruence ray has the source exponent bounded by
`log 8 / log t`. -/
private theorem kt19FixedPrimeGamma_eight_ray_le (t : Nat) (ht : 1 < t) :
    kt19FixedPrimeGamma (1 + 8 * t)
        (kt19ExplicitL (1 + 8 * t)) (kt19ExplicitK (1 + 8 * t)) ≤
      Real.log 8 / Real.log (t : ℝ) := by
  rcases kt19ExplicitParameters_eight_ray t with ⟨hk, hl, hinput, hdistance⟩
  have hinput' : (1 + 8 * t) - t = 7 * t + 1 := by
    simpa only [hk] using hinput
  have hdistance' : 2 * t - t = t := by
    simpa only [hk, hl] using hdistance
  rw [kt19FixedPrimeGamma, hk, hl, hinput', hdistance']
  have htpos_nat : 0 < t := by omega
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos_nat
  have hlogt : 0 < Real.log (t : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ht
  apply (div_le_div_iff_of_pos_right hlogt).2
  apply Real.log_le_log
  · exact div_pos (by positivity) htpos
  · apply (div_le_iff₀ htpos).2
    have htone : (1 : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (show 1 ≤ t by omega)
    push_cast
    nlinarith

/-- For every lower prime cutoff and positive tolerance, an actual larger
prime KT19 parameter choice has a strictly smaller displayed exponent.  The
prime is selected on the literal `1 (mod 8)` ray, so the accompanying
`kt19ExplicitDistillationFamily` is constructed from its Lagrange/nodal rows
by the existing definition rather than supplied as an asymptotic shell. -/
theorem kt19ChangingPrimeExponent (bound : Nat) (eta : ℝ) (heta : 0 < eta) :
    ∃ p : Nat, bound ≤ p ∧ Nat.Prime p ∧ 32 ≤ p ∧ p ≡ 1 [MOD 8] ∧
      kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (bound : ℝ) (Real.exp (Real.log 8 / eta) + 4))
  obtain ⟨p, hp, hpgt, hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one (8 * N + 1) (by norm_num : 8 ≠ 0)
  have hNbound_real : (bound : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hNbound : bound < N := by exact_mod_cast hNbound_real
  have hNexp : Real.exp (Real.log 8 / eta) + 4 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hNfour_real : (4 : ℝ) < (N : ℝ) := by
    nlinarith [Real.exp_pos (Real.log 8 / eta)]
  have hNfour : 4 < N := by exact_mod_cast hNfour_real
  have hlarge : 32 ≤ p := by omega
  have hptwo : 2 ≤ p := hp.two_le
  have hpone : 1 ≤ p := by omega
  obtain ⟨t, hpt⟩ := (Nat.modEq_iff_exists_eq_add hpone).mp hpmod.symm
  have hNt : N < t := by omega
  have ht : 1 < t := by omega
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have htexp : Real.exp (Real.log 8 / eta) < (t : ℝ) := by
    have hNt_real : (N : ℝ) < (t : ℝ) := by exact_mod_cast hNt
    nlinarith
  have hlog_lower : Real.log 8 / eta < Real.log (t : ℝ) :=
    (Real.lt_log_iff_exp_lt htpos).2 htexp
  have hlogt : 0 < Real.log (t : ℝ) := by
    apply Real.log_pos
    exact_mod_cast ht
  have hsmall : Real.log 8 / Real.log (t : ℝ) < eta := by
    apply (div_lt_iff₀ hlogt).2
    have h := (div_lt_iff₀ heta).1 hlog_lower
    simpa [mul_comm] using h
  refine ⟨p, le_trans (Nat.le_of_lt hNbound) (Nat.le_of_lt ?_), hp, hlarge,
    hpmod, ?_⟩
  · omega
  · rw [hpt]
    exact (kt19FixedPrimeGamma_eight_ray_le t ht).trans_lt hsmall

/-- The concrete IID error rate used by the terminal construction.  It is
chosen from the proved physical iteration scale, rather than supplied as an
extra small-error assumption. -/
private noncomputable def kt19SmallIIDRate
    (family : KT19DistillationFamily p l k) : ℝ :=
  1 / (4 * kt19FixedPrimeIterationScale family)

/-- A literal two-point prime-qudit IID law: all nonzero error mass sits at
the distinguished label `1`, while the remaining mass stays at `0`. -/
private noncomputable def kt19SmallIIDLaw
    (family : KT19DistillationFamily p l k) : ZMod p → ℝ :=
  fun a => if a = 0 then 1 - kt19SmallIIDRate family
    else if a = 1 then kt19SmallIIDRate family else 0

private theorem kt19SmallIIDRate_pos
    (family : KT19DistillationFamily p l k) :
    0 < kt19SmallIIDRate family := by
  unfold kt19SmallIIDRate
  exact one_div_pos.mpr
    (mul_pos (by norm_num) (kt19FixedPrimeIterationScale_pos family))

private theorem kt19SmallIIDRate_le_one
    (family : KT19DistillationFamily p l k) :
    kt19SmallIIDRate family ≤ 1 := by
  unfold kt19SmallIIDRate
  have hden : (1 : ℝ) ≤ 4 * kt19FixedPrimeIterationScale family := by
    have hscale : (1 : ℝ) ≤ kt19FixedPrimeIterationScale family :=
      kt19FixedPrimeIterationScale_one_le family
    nlinarith
  exact (one_div_le_one_div_of_le (by norm_num) hden).trans_eq (by norm_num)

private theorem kt19SmallIIDLaw_nonneg
    (family : KT19DistillationFamily p l k) (a : ZMod p) :
    0 ≤ kt19SmallIIDLaw family a := by
  unfold kt19SmallIIDLaw
  split_ifs
  · exact sub_nonneg.mpr (kt19SmallIIDRate_le_one family)
  · exact (kt19SmallIIDRate_pos family).le
  · exact le_rfl

private theorem kt19SmallIIDLaw_sum
    (family : KT19DistillationFamily p l k) [Fact p.Prime] :
    ∑ a : ZMod p, kt19SmallIIDLaw family a = 1 := by
  classical
  let support : Finset (ZMod p) :=
    (Finset.univ.erase (0 : ZMod p)).erase 1
  have hsupport : ∑ a ∈ support, kt19SmallIIDLaw family a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have haone : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have hazero : a ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [kt19SmallIIDLaw, hazero, haone]
  calc
    ∑ a : ZMod p, kt19SmallIIDLaw family a =
        (∑ a ∈ Finset.univ.erase (0 : ZMod p), kt19SmallIIDLaw family a) +
          kt19SmallIIDLaw family 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    _ = (∑ a ∈ support, kt19SmallIIDLaw family a) +
          kt19SmallIIDLaw family 1 + kt19SmallIIDLaw family 0 := by
      rw [← Finset.sum_erase_add (a := (1 : ZMod p))
        (Finset.univ.erase (0 : ZMod p)) _ (by simp)]
    _ = 1 := by
      rw [hsupport]
      simp [kt19SmallIIDLaw]

private theorem kt19SmallIIDLaw_errorRate
    (family : KT19DistillationFamily p l k) :
    kt19ErrorRate (kt19SmallIIDLaw family) = kt19SmallIIDRate family := by
  simp [kt19ErrorRate, kt19SmallIIDLaw]

private theorem kt19SmallIIDLaw_scaled_small
    (family : KT19DistillationFamily p l k) :
    kt19FixedPrimeIterationScale family *
        kt19ErrorRate (kt19SmallIIDLaw family) ≤ 1 / 4 := by
  rw [kt19SmallIIDLaw_errorRate]
  unfold kt19SmallIIDRate
  have hscale_ne : kt19FixedPrimeIterationScale family ≠ 0 :=
    (kt19FixedPrimeIterationScale_pos family).ne'
  have hproduct :
      kt19FixedPrimeIterationScale family *
          (1 / (4 * kt19FixedPrimeIterationScale family)) = (1 / 4 : ℝ) := by
    field_simp [hscale_ne]
  rw [hproduct]

/-- The literal changing-prime parameters retain a nontrivial source-safe
distance denominator once the public lower cutoff is imposed. -/
private theorem kt19ExplicitParameters_distance
    (p : Nat) (hlarge : 32 ≤ p) :
    2 ≤ kt19ExplicitL p - kt19ExplicitK p := by
  simp only [kt19ExplicitL, kt19ExplicitK]
  omega

/-- The fixed-prime physical package is derived from one actual family and
the literal small IID law.  It is private proof plumbing for the terminal
conjunction, not a record storing any protocol conclusion. -/
private theorem kt19FixedFamilyPhysicalPackage
    (family : KT19DistillationFamily p l k) (hdistance : 2 ≤ l - k) :
    let mu := kt19SmallIIDLaw family
    let hmu_nonneg := kt19SmallIIDLaw_nonneg family
    let hmu_sum := kt19SmallIIDLaw_sum family
    ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
      ∃ gate : UnitaryTransport
          (PrimeQuditRegister p (KeptPunctureLocation p k))
          (PrimeQuditRegister p (KeptPunctureLocation p k)),
        ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
            (PrimeQuditRegister p (KeptPunctureLocation p k))
            (PrimeQuditRegister p (Fin k)),
          resource = family.inputResource mu hmu_nonneg hmu_sum ∧
            gate = family.physicalGate ∧
              protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                  Admissible p l k ∧
                    2 ≤ l - k ∧
                      kt19Length p k = p - k ∧
                        kt19LogicalDimension p l k = k ∧
                          kt19SafeDistance p l k ≥ l - k ∧
                            stabilizerCarrier family.rowFamily =
                              (shortenedReedSolomonCode p l k).carrier ∧
                              family.encodedCode.ImplementsLogicalGate gate
                                family.rowFamily.logicalInverseU13 ∧
                                0 < kt19ErrorRate mu ∧
                                  ∃ coefficient : ℝ,
                                    0 < coefficient ∧
                                      coefficient = kt19FixedPrimeCostCoefficient family mu ∧
                                      kt19FixedPrimeGamma p l k =
                                        Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                          Real.log ((l - k : Nat) : ℝ) ∧
                                      Tendsto (fun depth : Nat =>
                                        kt19FixedPrimeScheduleTargetError family mu depth)
                                        atTop (𝓝 0) ∧
                                      Tendsto (fun depth : Nat =>
                                        kt19FixedPrimeActualOutputError family mu
                                          hmu_nonneg hmu_sum depth)
                                        atTop (𝓝 0) ∧
                                      DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                        (fun depth => kt19FixedPrimeInputSlots p k depth)
                                        (fun depth => kt19FixedPrimeOutputSlots k depth)
                                        (kt19FixedPrimeScheduleTargetError family mu)
                                        (kt19FixedPrimeActualOutputError family mu
                                          hmu_nonneg hmu_sum)
                                        (kt19FixedPrimeExpectedYield family mu
                                          hmu_nonneg hmu_sum)
                                        (kt19FixedPrimeGamma p l k) coefficient := by
  let mu : ZMod p → ℝ := kt19SmallIIDLaw family
  have hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a :=
    kt19SmallIIDLaw_nonneg family
  have hmu_sum : ∑ a : ZMod p, mu a = 1 :=
    kt19SmallIIDLaw_sum family
  have hepsilon : 0 < kt19ErrorRate mu := by
    rw [kt19SmallIIDLaw_errorRate]
    exact kt19SmallIIDRate_pos family
  have hsmall :
      kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4 :=
    kt19SmallIIDLaw_scaled_small family
  have hfixed := kt19FixedPrime family mu hmu_nonneg hmu_sum hdistance hepsilon hsmall
  have hparameters := kt19_family_parameters p l k family.admissible
  have hcoefficient : 0 < kt19FixedPrimeCostCoefficient family mu :=
    kt19FixedPrimeCostCoefficient_pos family mu hmu_nonneg hmu_sum hepsilon hsmall
  change ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
    ∃ gate : UnitaryTransport
        (PrimeQuditRegister p (KeptPunctureLocation p k))
        (PrimeQuditRegister p (KeptPunctureLocation p k)),
      ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
          (PrimeQuditRegister p (KeptPunctureLocation p k))
          (PrimeQuditRegister p (Fin k)),
        resource = family.inputResource mu hmu_nonneg hmu_sum ∧
          gate = family.physicalGate ∧
            protocol = family.protocol mu hmu_nonneg hmu_sum ∧
              protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                Admissible p l k ∧
                  2 ≤ l - k ∧
                    kt19Length p k = p - k ∧
                      kt19LogicalDimension p l k = k ∧
                        kt19SafeDistance p l k ≥ l - k ∧
                          stabilizerCarrier family.rowFamily =
                            (shortenedReedSolomonCode p l k).carrier ∧
                            family.encodedCode.ImplementsLogicalGate gate
                              family.rowFamily.logicalInverseU13 ∧
                              0 < kt19ErrorRate mu ∧
                                ∃ coefficient : ℝ,
                                  0 < coefficient ∧
                                    coefficient = kt19FixedPrimeCostCoefficient family mu ∧
                                    kt19FixedPrimeGamma p l k =
                                      Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                        Real.log ((l - k : Nat) : ℝ) ∧
                                    Tendsto (fun depth : Nat =>
                                      kt19FixedPrimeScheduleTargetError family mu depth)
                                      atTop (𝓝 0) ∧
                                    Tendsto (fun depth : Nat =>
                                      kt19FixedPrimeActualOutputError family mu
                                        hmu_nonneg hmu_sum depth) atTop (𝓝 0) ∧
                                    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                      (fun depth => kt19FixedPrimeInputSlots p k depth)
                                      (fun depth => kt19FixedPrimeOutputSlots k depth)
                                      (kt19FixedPrimeScheduleTargetError family mu)
                                      (kt19FixedPrimeActualOutputError family mu
                                        hmu_nonneg hmu_sum)
                                      (kt19FixedPrimeExpectedYield family mu
                                        hmu_nonneg hmu_sum)
                                      (kt19FixedPrimeGamma p l k) coefficient
  refine ⟨family.inputResource mu hmu_nonneg hmu_sum, family.physicalGate,
    family.protocol mu hmu_nonneg hmu_sum, rfl, rfl, rfl, rfl,
    family.admissible, hdistance, hparameters.1, hparameters.2.1,
    hparameters.2.2, family.stabilizerCarrier_eq_shortened,
    KT19DistillationFamily.physicalGate_implements_inverseLogicalU13 family, hepsilon,
    kt19FixedPrimeCostCoefficient family mu, hcoefficient, rfl, rfl, hfixed.1,
    hfixed.2.1, ?_⟩
  simpa using hfixed.2.2

/-- KT19's terminal result has two deliberately separate quantifier layers.
The first is a fixed-prime physical statement for every admissible displayed
row family.  The second selects unbounded concrete primes only to make that
fixed-prime exponent arbitrarily small; it never holds the alphabet,
resource, gate, or protocol fixed while the prime changes. -/
theorem kt19_qudit_zero_exponent :
    (∀ (p l k : Nat) (hp : Nat.Prime p) (hfive : 5 ≤ p)
        (hadmissible : Admissible p l k) (hdistance : 2 ≤ l - k),
      letI : NeZero p := ⟨hp.ne_zero⟩
      letI : Fact p.Prime := ⟨hp⟩
      ∃ family : KT19DistillationFamily p l k,
        family = kt19ExplicitFixedPrimeDistillationFamily p l k hfive hadmissible ∧
          let mu := kt19SmallIIDLaw family
          let hmu_nonneg := kt19SmallIIDLaw_nonneg family
          let hmu_sum := kt19SmallIIDLaw_sum family
          ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
            ∃ gate : UnitaryTransport
                (PrimeQuditRegister p (KeptPunctureLocation p k))
                (PrimeQuditRegister p (KeptPunctureLocation p k)),
              ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
                  (PrimeQuditRegister p (KeptPunctureLocation p k))
                  (PrimeQuditRegister p (Fin k)),
                resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                  gate = family.physicalGate ∧
                    protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                      protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                        Admissible p l k ∧
                          2 ≤ l - k ∧
                            kt19Length p k = p - k ∧
                              kt19LogicalDimension p l k = k ∧
                                kt19SafeDistance p l k ≥ l - k ∧
                                  stabilizerCarrier family.rowFamily =
                                    (shortenedReedSolomonCode p l k).carrier ∧
                                    family.encodedCode.ImplementsLogicalGate gate
                                      family.rowFamily.logicalInverseU13 ∧
                                      0 < kt19ErrorRate mu ∧
                                        ∃ coefficient : ℝ,
                                          0 < coefficient ∧
                                            coefficient =
                                              kt19FixedPrimeCostCoefficient family mu ∧
                                            kt19FixedPrimeGamma p l k =
                                              Real.log (((p - k : Nat) : ℝ) / (k : ℝ)) /
                                                Real.log ((l - k : Nat) : ℝ) ∧
                                            Tendsto (fun depth : Nat =>
                                              kt19FixedPrimeScheduleTargetError family mu depth)
                                              atTop (𝓝 0) ∧
                                            Tendsto (fun depth : Nat =>
                                              kt19FixedPrimeActualOutputError family mu
                                                hmu_nonneg hmu_sum depth)
                                              atTop (𝓝 0) ∧
                                            DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                                              (fun depth => kt19FixedPrimeInputSlots p k depth)
                                              (fun depth => kt19FixedPrimeOutputSlots k depth)
                                              (kt19FixedPrimeScheduleTargetError family mu)
                                              (kt19FixedPrimeActualOutputError family mu
                                                hmu_nonneg hmu_sum)
                                              (kt19FixedPrimeExpectedYield family mu
                                                hmu_nonneg hmu_sum)
                                              (kt19FixedPrimeGamma p l k) coefficient) ∧
      ∀ (bound : Nat) (eta : ℝ), 0 < eta →
        ∃ p : Nat, ∃ hp : Nat.Prime p, ∃ hlarge : 32 ≤ p,
          bound ≤ p ∧ p ≡ 1 [MOD 8] ∧
            letI : NeZero p := ⟨hp.ne_zero⟩
            letI : Fact p.Prime := ⟨hp⟩
            ∃ family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p),
              family = kt19ExplicitDistillationFamily p hlarge ∧
                kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta ∧
                let mu := kt19SmallIIDLaw family
                let hmu_nonneg := kt19SmallIIDLaw_nonneg family
                let hmu_sum := kt19SmallIIDLaw_sum family
                ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
                  ∃ gate : UnitaryTransport
                      (PrimeQuditRegister p
                        (KeptPunctureLocation p (kt19ExplicitK p)))
                      (PrimeQuditRegister p
                        (KeptPunctureLocation p (kt19ExplicitK p))),
                    ∃ protocol : MagicStateDistillationProtocol
                        (KT19SingleQudit.{0} p)
                        (PrimeQuditRegister p
                          (KeptPunctureLocation p (kt19ExplicitK p)))
                        (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
                      resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                        gate = family.physicalGate ∧
                          protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                            protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                              Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                                stabilizerCarrier family.rowFamily =
                                  (shortenedReedSolomonCode p (kt19ExplicitL p)
                                    (kt19ExplicitK p)).carrier ∧
                                  family.encodedCode.ImplementsLogicalGate gate
                                    family.rowFamily.logicalInverseU13 := by
  constructor
  · intro p l k hp hfive hadmissible hdistance
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    let family : KT19DistillationFamily p l k :=
      kt19ExplicitFixedPrimeDistillationFamily p l k hfive hadmissible
    refine ⟨family, rfl, ?_⟩
    exact kt19FixedFamilyPhysicalPackage family hdistance
  · intro bound eta heta
    rcases kt19ChangingPrimeExponent bound eta heta with
      ⟨p, hbound, hp, hlarge, hmod, hgamma⟩
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Fact p.Prime := ⟨hp⟩
    let family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p) :=
      kt19ExplicitDistillationFamily p hlarge
    let mu : ZMod p → ℝ := kt19SmallIIDLaw family
    have hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a :=
      kt19SmallIIDLaw_nonneg family
    have hmu_sum : ∑ a : ZMod p, mu a = 1 :=
      kt19SmallIIDLaw_sum family
    refine ⟨p, hp, hlarge, hbound, hmod, ?_⟩
    change ∃ family : KT19DistillationFamily p (kt19ExplicitL p) (kt19ExplicitK p),
      family = kt19ExplicitDistillationFamily p hlarge ∧
        kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta ∧
        let mu := kt19SmallIIDLaw family
        let hmu_nonneg := kt19SmallIIDLaw_nonneg family
        let hmu_sum := kt19SmallIIDLaw_sum family
        ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
          ∃ gate : UnitaryTransport
              (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
              (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p))),
            ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
                (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
                (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
              resource = family.inputResource mu hmu_nonneg hmu_sum ∧
                gate = family.physicalGate ∧
                  protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                    protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                      Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                        stabilizerCarrier family.rowFamily =
                          (shortenedReedSolomonCode p (kt19ExplicitL p)
                            (kt19ExplicitK p)).carrier ∧
                          family.encodedCode.ImplementsLogicalGate gate
                            family.rowFamily.logicalInverseU13
    refine ⟨family, rfl, hgamma, ?_⟩
    change ∃ resource : DensityOperator (KT19SingleQudit.{0} p),
      ∃ gate : UnitaryTransport
          (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
          (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p))),
        ∃ protocol : MagicStateDistillationProtocol (KT19SingleQudit.{0} p)
            (PrimeQuditRegister p (KeptPunctureLocation p (kt19ExplicitK p)))
            (PrimeQuditRegister p (Fin (kt19ExplicitK p))),
          resource = family.inputResource mu hmu_nonneg hmu_sum ∧
            gate = family.physicalGate ∧
              protocol = family.protocol mu hmu_nonneg hmu_sum ∧
                protocol.run = family.run mu hmu_nonneg hmu_sum ∧
                  Admissible p (kt19ExplicitL p) (kt19ExplicitK p) ∧
                    stabilizerCarrier family.rowFamily =
                      (shortenedReedSolomonCode p (kt19ExplicitL p)
                        (kt19ExplicitK p)).carrier ∧
                      family.encodedCode.ImplementsLogicalGate gate
                        family.rowFamily.logicalInverseU13
    refine ⟨family.inputResource mu hmu_nonneg hmu_sum, family.physicalGate,
      family.protocol mu hmu_nonneg hmu_sum, rfl, rfl, rfl, rfl,
      family.admissible, family.stabilizerCarrier_eq_shortened,
      KT19DistillationFamily.physicalGate_implements_inverseLogicalU13 family⟩

end QEC.Distillation.KT19VanishingOverhead
