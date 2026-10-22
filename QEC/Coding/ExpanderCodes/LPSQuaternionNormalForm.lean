import QEC.Coding.ExpanderCodes.LPSQuaternionPrimePowerCount
import QEC.Coding.ExpanderCodes.LPSQuaternionWord

/-!
# The finite LPS quaternion normal-form map

This file packages the candidate normal forms in Lemma 3.1 of the original
LPS construction.  A normal form at exponent `n` is either a reduced word of
length `n`, or `p` times a normal form at exponent `n - 2`.  Its quaternion
product has norm `p^n` and the LPS parity.  Correcting the sign of the real
coordinate therefore gives a point of the normalized norm shell.

The source and target are proved to have equal finite cardinality.  Thus the
only remaining content of the classical quaternion factorization theorem is
surjectivity of this explicit map; uniqueness then follows automatically.
-/

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- The disjoint union `S_n ⊔ S_{n-2} ⊔ ...` of alternating reduced-word
spheres, presented recursively so the power of `p` is part of the shape. -/
def LPSAlternatingReducedWord (hp : 0 < p) : ℕ → Type
  | 0 => LPSReducedWord hp 0
  | 1 => LPSReducedWord hp 1
  | n + 2 => LPSReducedWord hp (n + 2) ⊕
      LPSAlternatingReducedWord hp n

noncomputable instance lpsAlternatingReducedWordFintype
    (hp : 0 < p) (n : ℕ) : Fintype (LPSAlternatingReducedWord hp n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change Fintype (LPSReducedWord hp 0)
      infer_instance
  | one =>
      change Fintype (LPSReducedWord hp 1)
      infer_instance
  | more n hn _hnOne =>
      change Fintype
        (LPSReducedWord hp (n + 2) ⊕ LPSAlternatingReducedWord hp n)
      exact @instFintypeSum _ _ inferInstance hn

/-- The recursive normal-form type has exactly the alternating reduced-word
count defined from finite word spheres. -/
theorem fintype_card_lpsAlternatingReducedWord
    (hp : 0 < p) (n : ℕ) :
    Fintype.card (LPSAlternatingReducedWord hp n) =
      lpsAlternatingReducedWordCount hp n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change Fintype.card (LPSReducedWord hp 0) =
        (lpsReducedWords hp 0).card
      exact (card_lpsReducedWords_eq_fintype_card hp 0).symm
  | one =>
      change Fintype.card (LPSReducedWord hp 1) =
        (lpsReducedWords hp 1).card
      exact (card_lpsReducedWords_eq_fintype_card hp 1).symm
  | more n hn _hnOne =>
      change Fintype.card
          (LPSReducedWord hp (n + 2) ⊕ LPSAlternatingReducedWord hp n) =
        (lpsReducedWords hp (n + 2)).card +
          lpsAlternatingReducedWordCount hp n
      rw [Fintype.card_sum, hn,
        card_lpsReducedWords_eq_fintype_card hp (n + 2)]

/-- Coordinatewise multiplication of an integral quaternion by a central
integer scalar. -/
def lpsScaleQuaternion (s : ℤ) (t : LPSQuaternion) : LPSQuaternion where
  a := s * t.a
  b := s * t.b
  c := s * t.c
  d := s * t.d

@[simp] theorem norm_lpsScaleQuaternion (s : ℤ) (t : LPSQuaternion) :
    (lpsScaleQuaternion s t).norm = s ^ 2 * t.norm := by
  simp [lpsScaleQuaternion, LPSQuaternion.norm]
  ring

theorem hasLPSParity_lpsScaleQuaternion_of_odd
    {s : ℤ} {t : LPSQuaternion} (hs : Odd s)
    (ht : t.HasLPSParity) :
    (lpsScaleQuaternion s t).HasLPSParity := by
  exact ⟨hs.mul ht.1, ht.2.1.mul_left s,
    ht.2.2.1.mul_left s, ht.2.2.2.mul_left s⟩

/-- Integral quaternion represented by an alternating reduced-word normal
form.  Passing to the older summand multiplies by the central scalar `p`. -/
noncomputable def lpsAlternatingQuaternionProduct
    (a : LPSResiduePrime p) :
    (n : ℕ) → LPSAlternatingReducedWord a.degreePrime.pos n → LPSQuaternion
  | 0, word => lpsQuaternionWordProduct word.1.1
  | 1, word => lpsQuaternionWordProduct word.1.1
  | _n + 2, Sum.inl word => lpsQuaternionWordProduct word.1.1
  | n + 2, Sum.inr word =>
      lpsScaleQuaternion (p : ℤ) (lpsAlternatingQuaternionProduct a n word)

/-- Every candidate normal form at exponent `n` has norm `p^n`. -/
theorem norm_lpsAlternatingQuaternionProduct
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSAlternatingReducedWord a.degreePrime.pos n) :
    (lpsAlternatingQuaternionProduct a n word).norm = (p : ℤ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using norm_lpsQuaternionWordProduct a word.1.1
  | one =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using norm_lpsQuaternionWordProduct a word.1.1
  | more n hn _hnOne =>
      change LPSReducedWord a.degreePrime.pos (n + 2) ⊕
        LPSAlternatingReducedWord a.degreePrime.pos n at word
      cases word with
      | inl word =>
          simpa [lpsAlternatingQuaternionProduct]
            using norm_lpsQuaternionWordProduct a word.1.1
      | inr word =>
          rw [lpsAlternatingQuaternionProduct,
            norm_lpsScaleQuaternion, hn word]
          ring

/-- Every candidate normal form stays in the multiplicative LPS parity
class. -/
theorem hasLPSParity_lpsAlternatingQuaternionProduct
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSAlternatingReducedWord a.degreePrime.pos n) :
    (lpsAlternatingQuaternionProduct a n word).HasLPSParity := by
  have hpNeTwo : p ≠ 2 := by
    have hp4 := a.degreeModFour
    omega
  have hpOddNat : Odd p := a.degreePrime.odd_of_ne_two hpNeTwo
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using hasLPSParity_lpsQuaternionWordProduct a word.1.1
  | one =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using hasLPSParity_lpsQuaternionWordProduct a word.1.1
  | more n hn _hnOne =>
      change LPSReducedWord a.degreePrime.pos (n + 2) ⊕
        LPSAlternatingReducedWord a.degreePrime.pos n at word
      cases word with
      | inl word =>
          simpa [lpsAlternatingQuaternionProduct]
            using hasLPSParity_lpsQuaternionWordProduct a word.1.1
      | inr word =>
          exact hasLPSParity_lpsScaleQuaternion_of_odd hpOdd (hn word)

/-- Change the global sign, when needed, so the real coordinate is positive. -/
def lpsNormalizeFirstSign (t : LPSQuaternion) : LPSQuaternion :=
  if 0 < t.a then t else ⟨-t.a, -t.b, -t.c, -t.d⟩

@[simp] theorem norm_lpsNormalizeFirstSign (t : LPSQuaternion) :
    (lpsNormalizeFirstSign t).norm = t.norm := by
  by_cases h : 0 < t.a <;>
    simp [lpsNormalizeFirstSign, h, LPSQuaternion.norm]

theorem hasLPSParity_lpsNormalizeFirstSign
    {t : LPSQuaternion} (ht : t.HasLPSParity) :
    (lpsNormalizeFirstSign t).HasLPSParity := by
  by_cases h : 0 < t.a
  · simpa [lpsNormalizeFirstSign, h] using ht
  · simp only [lpsNormalizeFirstSign, if_neg h,
      LPSQuaternion.HasLPSParity]
    exact ⟨ht.1.neg, ht.2.1.neg, ht.2.2.1.neg, ht.2.2.2.neg⟩

theorem lpsNormalizeFirstSign_a_pos_of_odd
    {t : LPSQuaternion} (ht : Odd t.a) :
    0 < (lpsNormalizeFirstSign t).a := by
  have hne : t.a ≠ 0 := by
    intro hzero
    have hoddZero : Odd (0 : ℤ) := hzero ▸ ht
    simp at hoddZero
  by_cases h : 0 < t.a
  · simp [lpsNormalizeFirstSign, h]
  · simp [lpsNormalizeFirstSign, h]
    omega

/-- The explicit finite map from alternating reduced-word normal forms to
the normalized integral quaternion shell of norm `p^n`. -/
noncomputable def lpsAlternatingReducedWordToQuaternionShell
    (a : LPSResiduePrime p) (n : ℕ) :
    LPSAlternatingReducedWord a.degreePrime.pos n →
      {t // t ∈ lpsQuaternionShell (p ^ n)} := fun word =>
  ⟨lpsNormalizeFirstSign (lpsAlternatingQuaternionProduct a n word),
    (mem_lpsQuaternionShell_iff (pow_pos a.degreePrime.pos n) _).mpr <| by
      have hparity := hasLPSParity_lpsAlternatingQuaternionProduct a n word
      exact ⟨by
        rw [norm_lpsNormalizeFirstSign,
          norm_lpsAlternatingQuaternionProduct]
        norm_cast,
      lpsNormalizeFirstSign_a_pos_of_odd hparity.1,
      (hasLPSParity_lpsNormalizeFirstSign hparity).1⟩⟩

/-- Source and target of the finite normal-form map have equal cardinality. -/
theorem card_lpsAlternatingReducedWord_eq_quaternionShell
    (a : LPSResiduePrime p) (n : ℕ) :
    Fintype.card (LPSAlternatingReducedWord a.degreePrime.pos n) =
      Fintype.card {t // t ∈ lpsQuaternionShell (p ^ n)} := by
  rw [fintype_card_lpsAlternatingReducedWord,
    Fintype.card_coe,
    card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
      a.degreePrime a.degreeModFour]

/-- Once existence (surjectivity) of the classical quaternion factorization
is established, its uniqueness is automatic from the exact finite counts. -/
theorem lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    Function.Bijective (lpsAlternatingReducedWordToQuaternionShell a n) := by
  exact (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨hsurj, card_lpsAlternatingReducedWord_eq_quaternionShell a n⟩

end QEC.Coding.TannerLiftedProduct
