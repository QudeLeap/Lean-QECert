import QEC.Coding.ExpanderCodes.LPSHeckeTrace
import QEC.Coding.ExpanderCodes.LPSReducedWords

/-!
# LPS Hecke elements as alternating reduced spheres

The finite Hecke polynomial recurrence is identified here with the exact
non-backtracking recurrence proved for reduced LPS words.  Consequently the
identity coefficient of the Hecke element is the concrete quantity
`L_n(e,e)` from the LPS trace argument.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- Every finite LPS Hecke element commutes with the generator sum at which
its defining polynomial is evaluated. -/
theorem lpsFiniteHeckeElement_commute_generatorSum
    (a : LPSResiduePrime p) (n : ℕ) :
    Commute (lpsFiniteHeckeElement a n)
      (cayleyGeneratorSum (lpsQuaternionLabel a)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hnOne =>
      rw [show n + 2 = n + 2 by rfl,
        lpsFiniteHeckeElement_add_two]
      apply Commute.sub_left
      · exact hnOne.mul_left (Commute.refl _)
      · exact (Algebra.commute_algebraMap_left _ _).mul_left hn

/-- Left-handed form of the finite Hecke recurrence. -/
theorem lpsFiniteHeckeElement_add_two_left
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a (n + 2) =
      cayleyGeneratorSum (lpsQuaternionLabel a) *
          lpsFiniteHeckeElement a (n + 1) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsFiniteHeckeElement a n := by
  rw [lpsFiniteHeckeElement_add_two]
  rw [(lpsFiniteHeckeElement_commute_generatorSum a (n + 1)).eq]

/-- Subtractive form of the alternating-sphere Hecke recurrence. -/
theorem lpsAlternatingReducedWordElement_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsAlternatingReducedWordElement a (n + 2) =
      cayleyGeneratorSum (lpsQuaternionLabel a) *
          lpsAlternatingReducedWordElement a (n + 1) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsAlternatingReducedWordElement a n := by
  have hrec :=
    cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one a n
  have hscalar :
      algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsAlternatingReducedWordElement a n =
        p • lpsAlternatingReducedWordElement a n := by
    rw [← Algebra.smul_def,
      Nat.cast_smul_eq_nsmul ℂ p]
  rw [hscalar]
  exact (eq_sub_iff_add_eq).2 hrec.symm

/-- The finite Hecke element is exactly the alternating sum of reduced-word
spheres `S_n + S_{n-2} + ⋯`. -/
theorem lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a n =
      lpsAlternatingReducedWordElement a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hnOne =>
      rw [lpsFiniteHeckeElement_add_two_left,
        lpsAlternatingReducedWordElement_add_two, hn, hnOne]

/-- Exact finite LPS trace count: the identity coefficient of the Hecke
element is `L_n(e,e)`, the number of closed words in the alternating reduced
spheres. -/
theorem coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsFiniteHeckeElement a n).coeff 1 =
      (lpsAlternatingClosedReducedWordCount a n : ℂ) := by
  rw [lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement,
    coeff_lpsAlternatingReducedWordElement_one]

/-- Regular trace form of the exact reduced-word identity. -/
theorem trace_lpsFiniteHeckeElement_eq_alternatingClosedReducedWordCount
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        (lpsAlternatingClosedReducedWordCount a n : ℂ) := by
  rw [trace_lpsFiniteHeckeElement,
    coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount]

end QEC.Coding.TannerLiftedProduct
