import QEC.Coding.ExpanderCodes.LPSQuaternionNormalForm
import QEC.Coding.ExpanderCodes.LPSHeckeReducedWords

/-!
# Trace congruences for LPS quaternion normal forms

The central powers of `p` and the global sign in an LPS quaternion normal
form do not affect divisibility of the three imaginary coordinates by `2q`.
Consequently an alternating normal form closes in the finite LPS Cayley graph
exactly when its normalized quaternion lies in the trace congruence shell.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

private theorem lps_degree_coprime_two_mul_residue
    (a : LPSResiduePrime p) : Nat.Coprime p (2 * a.q) := by
  have hpNeTwo : p ≠ 2 := by
    have hp4 := a.degreeModFour
    omega
  have hpTwo : Nat.Coprime p 2 :=
    Nat.coprime_two_right.mpr (a.degreePrime.odd_of_ne_two hpNeTwo)
  have hpq : Nat.Coprime p a.q := by
    have hp := a.degreePrime.pos
    have hlarge := a.large
    exact ((a.prime.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt hp (by omega))).symm
  exact hpTwo.mul_right hpq

private theorem two_mul_residue_dvd_degree_mul_iff
    (a : LPSResiduePrime p) (x : ℤ) :
    ((2 * a.q : ℕ) : ℤ) ∣ (p : ℤ) * x ↔
      ((2 * a.q : ℕ) : ℤ) ∣ x := by
  have hcoprimeNat := (lps_degree_coprime_two_mul_residue a).symm
  have hcoprime : IsCoprime (((2 * a.q : ℕ) : ℤ)) (p : ℤ) :=
    hcoprimeNat.isCoprime
  constructor
  · intro h
    exact hcoprime.dvd_of_dvd_mul_right (by simpa [mul_comm] using h)
  · rintro ⟨y, rfl⟩
    refine ⟨(p : ℤ) * y, ?_⟩
    ring

private theorem two_mul_residue_dvd_scale_iff
    (a : LPSResiduePrime p) (t : LPSQuaternion) :
    (((2 * a.q : ℕ) : ℤ) ∣ (lpsScaleQuaternion (p : ℤ) t).b ↔
        ((2 * a.q : ℕ) : ℤ) ∣ t.b) ∧
      (((2 * a.q : ℕ) : ℤ) ∣ (lpsScaleQuaternion (p : ℤ) t).c ↔
        ((2 * a.q : ℕ) : ℤ) ∣ t.c) ∧
      (((2 * a.q : ℕ) : ℤ) ∣ (lpsScaleQuaternion (p : ℤ) t).d ↔
        ((2 * a.q : ℕ) : ℤ) ∣ t.d) := by
  exact ⟨two_mul_residue_dvd_degree_mul_iff a t.b,
    two_mul_residue_dvd_degree_mul_iff a t.c,
    two_mul_residue_dvd_degree_mul_iff a t.d⟩

private theorem dvd_normalizeFirstSign_iff
    (m : ℤ) (t : LPSQuaternion) :
    (m ∣ (lpsNormalizeFirstSign t).b ↔ m ∣ t.b) ∧
      (m ∣ (lpsNormalizeFirstSign t).c ↔ m ∣ t.c) ∧
      (m ∣ (lpsNormalizeFirstSign t).d ↔ m ∣ t.d) := by
  by_cases h : 0 < t.a
  · simp [lpsNormalizeFirstSign, h]
  · simp [lpsNormalizeFirstSign, h]

/-- The finite `PSL` product attached to an alternating reduced-word normal
form; central powers of `p` do not contribute to this projective product. -/
noncomputable def lpsAlternatingPSLWordProduct
    (a : LPSResiduePrime p) :
    (n : ℕ) → LPSAlternatingReducedWord a.degreePrime.pos n →
      PSL(2, ZMod a.q)
  | 0, word => lpsPSLWordProduct a word.1.1
  | 1, word => lpsPSLWordProduct a word.1.1
  | _n + 2, Sum.inl word => lpsPSLWordProduct a word.1.1
  | n + 2, Sum.inr word => lpsAlternatingPSLWordProduct a n word

private theorem lpsPSLWordProduct_eq_one_iff_imaginary_dvd
    (a : LPSResiduePrime p) {n : ℕ}
    (word : LPSReducedWord a.degreePrime.pos n) :
    lpsPSLWordProduct a word.1.1 = 1 ↔
      ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word.1.1).b ∧
        ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word.1.1).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word.1.1).d := by
  have h := lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell
    a word.1.1
  rw [mem_lpsTraceCongruenceShell_iff
      (pow_pos a.degreePrime.pos word.1.1.length),
    norm_lpsQuaternionWordProduct a word.1.1] at h
  simpa only [Int.natCast_pow, true_and] using h

/-- An alternating normal form closes projectively exactly when the three
imaginary coordinates of its normalized quaternion are divisible by `2q`. -/
theorem lpsAlternatingPSLWordProduct_eq_one_iff_imaginary_dvd
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSAlternatingReducedWord a.degreePrime.pos n) :
    lpsAlternatingPSLWordProduct a n word = 1 ↔
      ((2 * a.q : ℕ) : ℤ) ∣
          (lpsAlternatingReducedWordToQuaternionShell a n word).1.b ∧
        ((2 * a.q : ℕ) : ℤ) ∣
          (lpsAlternatingReducedWordToQuaternionShell a n word).1.c ∧
        ((2 * a.q : ℕ) : ℤ) ∣
          (lpsAlternatingReducedWordToQuaternionShell a n word).1.d := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change LPSReducedWord a.degreePrime.pos 0 at word
      change lpsPSLWordProduct a word.1.1 = 1 ↔
        ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).b ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).d
      rw [lpsPSLWordProduct_eq_one_iff_imaginary_dvd]
      have hnormalize := dvd_normalizeFirstSign_iff
        (((2 * a.q : ℕ) : ℤ))
        (lpsQuaternionWordProduct word.1.1)
      rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
  | one =>
      change LPSReducedWord a.degreePrime.pos 1 at word
      change lpsPSLWordProduct a word.1.1 = 1 ↔
        ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).b ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).d
      rw [lpsPSLWordProduct_eq_one_iff_imaginary_dvd]
      have hnormalize := dvd_normalizeFirstSign_iff
        (((2 * a.q : ℕ) : ℤ))
        (lpsQuaternionWordProduct word.1.1)
      rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
  | more n hn _hnOne =>
      change LPSReducedWord a.degreePrime.pos (n + 2) ⊕
        LPSAlternatingReducedWord a.degreePrime.pos n at word
      cases word with
      | inl word =>
          change lpsPSLWordProduct a word.1.1 = 1 ↔
            ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsQuaternionWordProduct word.1.1)).b ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsQuaternionWordProduct word.1.1)).c ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsQuaternionWordProduct word.1.1)).d
          rw [lpsPSLWordProduct_eq_one_iff_imaginary_dvd]
          have hnormalize := dvd_normalizeFirstSign_iff
            (((2 * a.q : ℕ) : ℤ))
            (lpsQuaternionWordProduct word.1.1)
          rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
      | inr word =>
          change lpsAlternatingPSLWordProduct a n word = 1 ↔
            ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsScaleQuaternion (p : ℤ)
                    (lpsAlternatingQuaternionProduct a n word))).b ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsScaleQuaternion (p : ℤ)
                    (lpsAlternatingQuaternionProduct a n word))).c ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsScaleQuaternion (p : ℤ)
                    (lpsAlternatingQuaternionProduct a n word))).d
          rw [hn word]
          have hnormalize := dvd_normalizeFirstSign_iff
            (((2 * a.q : ℕ) : ℤ))
            (lpsScaleQuaternion (p : ℤ)
              (lpsAlternatingQuaternionProduct a n word))
          rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
          have hscale := two_mul_residue_dvd_scale_iff a
            (lpsAlternatingQuaternionProduct a n word)
          rw [hscale.1, hscale.2.1, hscale.2.2]
          change
            (((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsAlternatingQuaternionProduct a n word)).b ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsAlternatingQuaternionProduct a n word)).c ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsAlternatingQuaternionProduct a n word)).d) ↔ _
          have hbase := dvd_normalizeFirstSign_iff
            (((2 * a.q : ℕ) : ℤ))
            (lpsAlternatingQuaternionProduct a n word)
          rw [hbase.1, hbase.2.1, hbase.2.2]

/-- Closed alternating reduced-word normal forms. -/
abbrev LPSClosedAlternatingReducedWord
    (a : LPSResiduePrime p) (n : ℕ) :=
  {word : LPSAlternatingReducedWord a.degreePrime.pos n //
    lpsAlternatingPSLWordProduct a n word = 1}

/-- Normalized quaternions in the trace congruence class. -/
abbrev LPSNormalizedTraceQuaternion
    (a : LPSResiduePrime p) (n : ℕ) :=
  {t : {t // t ∈ lpsQuaternionShell (p ^ n)} //
    ((2 * a.q : ℕ) : ℤ) ∣ t.1.b ∧
      ((2 * a.q : ℕ) : ℤ) ∣ t.1.c ∧
        ((2 * a.q : ℕ) : ℤ) ∣ t.1.d}

/-- Surjectivity of the explicit quaternion factorization map identifies
closed alternating normal forms with normalized trace-shell points. -/
noncomputable def lpsClosedAlternatingReducedWordEquivNormalizedTrace
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    LPSClosedAlternatingReducedWord a n ≃
      LPSNormalizedTraceQuaternion a n :=
  (Equiv.ofBijective (lpsAlternatingReducedWordToQuaternionShell a n)
    (lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
      a n hsurj)).subtypeEquiv fun word =>
        lpsAlternatingPSLWordProduct_eq_one_iff_imaginary_dvd a n word

/-- Multiply an integral quaternion by the central unit selected by a sign
bit. -/
def lpsSignedQuaternion (negative : Bool)
    (t : LPSQuaternion) : LPSQuaternion :=
  if negative then ⟨-t.a, -t.b, -t.c, -t.d⟩ else t

@[simp] theorem norm_lpsSignedQuaternion
    (negative : Bool) (t : LPSQuaternion) :
    (lpsSignedQuaternion negative t).norm = t.norm := by
  cases negative <;> simp [lpsSignedQuaternion, LPSQuaternion.norm]

private theorem dvd_lpsSignedQuaternion_iff
    (m : ℤ) (negative : Bool) (t : LPSQuaternion) :
    (m ∣ (lpsSignedQuaternion negative t).b ↔ m ∣ t.b) ∧
      (m ∣ (lpsSignedQuaternion negative t).c ↔ m ∣ t.c) ∧
      (m ∣ (lpsSignedQuaternion negative t).d ↔ m ∣ t.d) := by
  cases negative <;> simp [lpsSignedQuaternion]

private theorem even_of_two_mul_dvd
    {q : ℕ} {x : ℤ} (h : (((2 * q : ℕ) : ℤ)) ∣ x) : Even x := by
  rcases h with ⟨y, rfl⟩
  refine ⟨(q : ℤ) * y, ?_⟩
  push_cast
  ring

/-- Add the two global signs to a normalized trace quaternion. -/
noncomputable def lpsSignedNormalizedTraceQuaternion
    (a : LPSResiduePrime p) (n : ℕ) :
    Bool × LPSNormalizedTraceQuaternion a n →
      {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)} := fun x =>
  ⟨lpsSignedQuaternion x.1 x.2.1.1,
    (mem_lpsTraceCongruenceShell_iff (pow_pos a.degreePrime.pos n) _).mpr <| by
      have hnorm := (mem_lpsQuaternionShell_iff
        (pow_pos a.degreePrime.pos n) x.2.1.1).mp x.2.1.2
      have hdvd := dvd_lpsSignedQuaternion_iff
        (((2 * a.q : ℕ) : ℤ)) x.1 x.2.1.1
      exact ⟨by rw [norm_lpsSignedQuaternion, hnorm.1],
        hdvd.1.mpr x.2.2.1,
        hdvd.2.1.mpr x.2.2.2.1,
        hdvd.2.2.mpr x.2.2.2.2⟩⟩

private theorem lpsSignedNormalizedTraceQuaternion_injective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Injective (lpsSignedNormalizedTraceQuaternion a n) := by
  rintro ⟨negative, t⟩ ⟨negative', u⟩ h
  have hval := congrArg Subtype.val h
  have htPos := ((mem_lpsQuaternionShell_iff
    (pow_pos a.degreePrime.pos n) t.1.1).mp t.1.2).2.1
  have huPos := ((mem_lpsQuaternionShell_iff
    (pow_pos a.degreePrime.pos n) u.1.1).mp u.1.2).2.1
  cases negative <;> cases negative'
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      simpa [lpsSignedNormalizedTraceQuaternion,
        lpsSignedQuaternion] using hval
  · have ha := congrArg LPSQuaternion.a hval
    simp [lpsSignedNormalizedTraceQuaternion,
      lpsSignedQuaternion] at ha
    omega
  · have ha := congrArg LPSQuaternion.a hval
    simp [lpsSignedNormalizedTraceQuaternion,
      lpsSignedQuaternion] at ha
    omega
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg LPSQuaternion.a hval
      have hb := congrArg LPSQuaternion.b hval
      have hc := congrArg LPSQuaternion.c hval
      have hd := congrArg LPSQuaternion.d hval
      apply LPSQuaternion.ext <;>
        simp [lpsSignedNormalizedTraceQuaternion,
          lpsSignedQuaternion] at ha hb hc hd ⊢ <;>
        omega

private theorem lpsSignedNormalizedTraceQuaternion_surjective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Surjective (lpsSignedNormalizedTraceQuaternion a n) := by
  intro u
  have hu := (mem_lpsTraceCongruenceShell_iff
    (pow_pos a.degreePrime.pos n) u.1).mp u.2
  have hbEven : Even u.1.b := even_of_two_mul_dvd hu.2.1
  have hcEven : Even u.1.c := even_of_two_mul_dvd hu.2.2.1
  have hdEven : Even u.1.d := even_of_two_mul_dvd hu.2.2.2
  have hpPow4 : p ^ n % 4 = 1 :=
    lps_prime_pow_mod_four a.degreeModFour n
  have haOdd : Odd u.1.a := by
    rcases exactly_one_odd_coordinate hpPow4 u.1 hu.1 with
      ha | hb | hc | hd
    · exact ha.1
    · exact ((Int.not_odd_iff_even.mpr hbEven) hb.2.1).elim
    · exact ((Int.not_odd_iff_even.mpr hcEven) hc.2.2.1).elim
    · exact ((Int.not_odd_iff_even.mpr hdEven) hd.2.2.2).elim
  have haNe : u.1.a ≠ 0 := by
    intro hzero
    have hoddZero : Odd (0 : ℤ) := hzero ▸ haOdd
    simp at hoddZero
  by_cases haPos : 0 < u.1.a
  · let t : LPSNormalizedTraceQuaternion a n :=
      ⟨⟨u.1, (mem_lpsQuaternionShell_iff
        (pow_pos a.degreePrime.pos n) u.1).mpr
          ⟨by exact_mod_cast hu.1, haPos, haOdd⟩⟩,
        hu.2⟩
    refine ⟨⟨false, t⟩, ?_⟩
    apply Subtype.ext
    rfl
  · have hnegPos : 0 < -u.1.a := by omega
    let negU : LPSQuaternion := ⟨-u.1.a, -u.1.b, -u.1.c, -u.1.d⟩
    have hnegNorm : negU.norm = (p ^ n : ℕ) := by
      change (-u.1.a) ^ 2 + (-u.1.b) ^ 2 +
        (-u.1.c) ^ 2 + (-u.1.d) ^ 2 = _
      simpa [LPSQuaternion.norm] using hu.1
    let t : LPSNormalizedTraceQuaternion a n :=
      ⟨⟨negU, (mem_lpsQuaternionShell_iff
        (pow_pos a.degreePrime.pos n) negU).mpr
          ⟨hnegNorm, hnegPos, haOdd.neg⟩⟩,
        by simpa [negU] using hu.2⟩
    refine ⟨⟨true, t⟩, ?_⟩
    apply Subtype.ext
    apply LPSQuaternion.ext <;>
      simp [lpsSignedNormalizedTraceQuaternion,
        lpsSignedQuaternion, t, negU]

/-- The trace congruence shell is exactly two signed copies of its normalized
positive-real-coordinate part. -/
noncomputable def lpsSignedNormalizedTraceQuaternionEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    Bool × LPSNormalizedTraceQuaternion a n ≃
      {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)} :=
  Equiv.ofBijective (lpsSignedNormalizedTraceQuaternion a n)
    ⟨lpsSignedNormalizedTraceQuaternion_injective a n,
      lpsSignedNormalizedTraceQuaternion_surjective a n⟩

/-- Exact factor-two cardinality between the full trace shell and its
normalized positive-real-coordinate part. -/
theorem card_traceCongruenceShell_eq_two_mul_normalizedTrace
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * Fintype.card (LPSNormalizedTraceQuaternion a n) := by
  have hcard := Fintype.card_congr
    (lpsSignedNormalizedTraceQuaternionEquiv a n)
  simpa [Fintype.card_prod] using hcard.symm

@[simp] theorem lpsPSLWordProduct_eq_cayleyVectorWordProduct
    (a : LPSResiduePrime p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    lpsPSLWordProduct a word.1 =
      cayleyVectorWordProduct (lpsQuaternionLabel a) word := by
  rfl

/-- The subtype of closed reduced words and the existing filtered-finset
presentation are canonically equivalent. -/
noncomputable def lpsClosedReducedWordSubtypeEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    {word : LPSReducedWord a.degreePrime.pos n //
      lpsPSLWordProduct a word.1.1 = 1} ≃
      {word // word ∈ lpsClosedReducedWords a n} where
  toFun word := ⟨word.1.1,
    (mem_lpsClosedReducedWords_iff a word.1.1).mpr
      ⟨word.1.2, by simpa using word.2⟩⟩
  invFun word :=
    ⟨⟨word.1, (mem_lpsClosedReducedWords_iff a word.1).mp word.2 |>.1⟩,
      by
        have hclosed :=
          (mem_lpsClosedReducedWords_iff a word.1).mp word.2 |>.2
        simpa using hclosed⟩
  left_inv word := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv word := by
    apply Subtype.ext
    rfl

/-- Unfold one two-step layer of the alternating normal-form type. -/
def lpsAlternatingReducedWordAddTwoEquiv
    (hp : 0 < p) (n : ℕ) :
    LPSAlternatingReducedWord hp (n + 2) ≃
      LPSReducedWord hp (n + 2) ⊕ LPSAlternatingReducedWord hp n :=
  Equiv.refl _

/-- A closed alternating normal form at `n+2` is either a closed reduced
word of length `n+2` or a closed alternating normal form at `n`. -/
noncomputable def lpsClosedAlternatingReducedWordAddTwoEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    LPSClosedAlternatingReducedWord a (n + 2) ≃
      {word : LPSReducedWord a.degreePrime.pos (n + 2) //
        lpsPSLWordProduct a word.1.1 = 1} ⊕
        LPSClosedAlternatingReducedWord a n :=
  ((lpsAlternatingReducedWordAddTwoEquiv a.degreePrime.pos n).subtypeEquiv
    fun _word => Iff.rfl).trans Equiv.subtypeSum

/-- The recursive closed normal-form subtype is counted by the existing
alternating closed reduced-word count `L_n(e,e)`. -/
theorem fintype_card_lpsClosedAlternatingReducedWord
    (a : LPSResiduePrime p) (n : ℕ) :
    Fintype.card (LPSClosedAlternatingReducedWord a n) =
      lpsAlternatingClosedReducedWordCount a n := by
  classical
  induction n using Nat.twoStepInduction with
  | zero =>
      change Fintype.card
          {word : LPSReducedWord a.degreePrime.pos 0 //
            lpsPSLWordProduct a word.1.1 = 1} =
        (lpsClosedReducedWords a 0).card
      rw [Fintype.card_congr (lpsClosedReducedWordSubtypeEquiv a 0),
        Fintype.card_coe]
  | one =>
      change Fintype.card
          {word : LPSReducedWord a.degreePrime.pos 1 //
            lpsPSLWordProduct a word.1.1 = 1} =
        (lpsClosedReducedWords a 1).card
      rw [Fintype.card_congr (lpsClosedReducedWordSubtypeEquiv a 1),
        Fintype.card_coe]
  | more n hn _hnOne =>
      rw [lpsAlternatingClosedReducedWordCount]
      calc
        Fintype.card (LPSClosedAlternatingReducedWord a (n + 2)) =
            Fintype.card
              ({word : LPSReducedWord a.degreePrime.pos (n + 2) //
                  lpsPSLWordProduct a word.1.1 = 1} ⊕
                LPSClosedAlternatingReducedWord a n) := by
                  exact Fintype.card_congr
                    (lpsClosedAlternatingReducedWordAddTwoEquiv a n)
        _ = Fintype.card
              {word : LPSReducedWord a.degreePrime.pos (n + 2) //
                lpsPSLWordProduct a word.1.1 = 1} +
              Fintype.card (LPSClosedAlternatingReducedWord a n) :=
                Fintype.card_sum
        _ = (lpsClosedReducedWords a (n + 2)).card +
              lpsAlternatingClosedReducedWordCount a n := by
                rw [Fintype.card_congr
                  (lpsClosedReducedWordSubtypeEquiv a (n + 2)),
                  Fintype.card_coe, hn]

/-- Conditional form of the exact LPS trace identity (4.14).  Its sole
remaining hypothesis is existence of the explicit integral quaternion
normal form; uniqueness has already been discharged by cardinality. -/
theorem card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * lpsAlternatingClosedReducedWordCount a n := by
  rw [card_traceCongruenceShell_eq_two_mul_normalizedTrace]
  congr 1
  rw [← fintype_card_lpsClosedAlternatingReducedWord a n]
  exact Fintype.card_congr
    (lpsClosedAlternatingReducedWordEquivNormalizedTrace a n hsurj).symm

/-- Theta-coefficient form of the same exact conditional identity. -/
theorem coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) =
      2 * lpsAlternatingClosedReducedWordCount a n := by
  rw [coeff_lpsTraceThetaSeries_eq_congruenceShell
    a.prime.pos (pow_pos a.degreePrime.pos n)]
  exact card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
    a n hsurj

/-- Complex-coefficient Hecke form of the exact conditional LPS identity:
the theta coefficient at `p^n` is twice the identity coefficient of the
finite Hecke element. -/
theorem coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) =
      2 * (lpsFiniteHeckeElement a n).coeff 1 := by
  rw [coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
      a n hsurj,
    coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount]
  norm_cast

end QEC.Coding.TannerLiftedProduct
