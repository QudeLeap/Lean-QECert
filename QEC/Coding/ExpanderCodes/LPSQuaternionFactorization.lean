import QEC.Coding.ExpanderCodes.LPSQuaternionPrimeFactor
import QEC.Coding.ExpanderCodes.LPSQuaternionNormalForm

/-!
# Exact LPS quaternion factorization

Primitive quaternions of norm `p^n` are factored recursively into reduced
words of normalized norm-`p` generators.  Non-primitive quaternions descend
by a central factor of `p`, yielding the alternating normal form.
-/

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

theorem LPSQuaternion.CoordinatesDvd.neg
    {s : ℤ} {t : LPSQuaternion} (ht : t.CoordinatesDvd s) :
    (-t).CoordinatesDvd s := by
  rcases ht with ⟨ha, hb, hc, hd⟩
  exact ⟨dvd_neg.mpr ha, dvd_neg.mpr hb,
    dvd_neg.mpr hc, dvd_neg.mpr hd⟩

theorem LPSQuaternion.CoordinatesDvd.mul_right
    {s : ℤ} {t : LPSQuaternion} (ht : t.CoordinatesDvd s)
    (u : LPSQuaternion) : (t * u).CoordinatesDvd s := by
  rcases ht with ⟨ha, hb, hc, hd⟩
  constructor
  · simp only [LPSQuaternion.mul_a]
    exact (((ha.mul_right u.a).sub (hb.mul_right u.b)).sub
      (hc.mul_right u.c)).sub (hd.mul_right u.d)
  constructor
  · simp only [LPSQuaternion.mul_b]
    exact (((ha.mul_right u.b).add (hb.mul_right u.a)).add
      (hc.mul_right u.d)).sub (hd.mul_right u.c)
  constructor
  · simp only [LPSQuaternion.mul_c]
    exact (((ha.mul_right u.c).sub (hb.mul_right u.d)).add
      (hc.mul_right u.a)).add (hd.mul_right u.b)
  · simp only [LPSQuaternion.mul_d]
    exact (((ha.mul_right u.d).add (hb.mul_right u.c)).sub
      (hc.mul_right u.b)).add (hd.mul_right u.a)

theorem coordinatesDvd_lpsScaleQuaternion (s : ℤ) (t : LPSQuaternion) :
    (lpsScaleQuaternion s t).CoordinatesDvd s := by
  exact ⟨⟨t.a, rfl⟩, ⟨t.b, rfl⟩, ⟨t.c, rfl⟩, ⟨t.d, rfl⟩⟩

@[simp] theorem lpsScaleQuaternion_neg (s : ℤ) (t : LPSQuaternion) :
    lpsScaleQuaternion s (-t) = -lpsScaleQuaternion s t := by
  apply LPSQuaternion.ext <;> simp [lpsScaleQuaternion]

@[simp] theorem lpsQuaternionWordProduct_append
    (word₁ word₂ : List (LPSGeneratorIndex p)) :
    lpsQuaternionWordProduct (word₁ ++ word₂) =
      lpsQuaternionWordProduct word₁ * lpsQuaternionWordProduct word₂ := by
  simp [lpsQuaternionWordProduct]

@[simp] theorem lpsQuaternionWordProduct_singleton
    (x : LPSGeneratorIndex p) :
    lpsQuaternionWordProduct [x] = x.1 := by
  simp [lpsQuaternionWordProduct]

/-- If `x` is the last letter of a word, multiplying its quaternion product
by `x̄` creates a central factor of `p`. -/
theorem coordinatesDvd_wordProduct_mul_conj_of_mem_getLast
    (hp : p.Prime) (word : List (LPSGeneratorIndex p))
    (x : LPSGeneratorIndex p) (hx : x ∈ word.getLast?) :
    (lpsQuaternionWordProduct word * x.1.conj).CoordinatesDvd (p : ℤ) := by
  have hdecomp : word.dropLast ++ [x] = word :=
    List.dropLast_append_getLast? x hx
  have hxNorm : x.1.norm = (p : ℤ) :=
    norm_eq_of_mem_lpsQuaternionShell hp.pos x.2
  have heq : lpsQuaternionWordProduct word * x.1.conj =
      lpsScaleQuaternion (p : ℤ)
        (lpsQuaternionWordProduct word.dropLast) := by
    calc
      lpsQuaternionWordProduct word * x.1.conj =
          lpsQuaternionWordProduct (word.dropLast ++ [x]) * x.1.conj := by
            rw [hdecomp]
      _ = (lpsQuaternionWordProduct word.dropLast * x.1) * x.1.conj := by
        simp [lpsQuaternionWordProduct]
      _ = lpsQuaternionWordProduct word.dropLast * (x.1 * x.1.conj) :=
        mul_assoc _ _ _
      _ = lpsQuaternionWordProduct word.dropLast *
          lpsScaleQuaternion (p : ℤ) 1 := by
        rw [LPSQuaternion.mul_conj_self, hxNorm]
      _ = lpsScaleQuaternion (p : ℤ)
          (lpsQuaternionWordProduct word.dropLast) := by
        rw [← lpsScaleQuaternion_mul_right]
        simp
  rw [heq]
  exact coordinatesDvd_lpsScaleQuaternion _ _

/-- A primitive quaternion of norm `p^n` and LPS parity is represented,
up to its central sign, by a reduced word of length `n`. -/
theorem exists_lpsReducedWord_product_eq_or_eq_neg
    (a : LPSResiduePrime p) : ∀ (n : ℕ) (t : LPSQuaternion),
    t.norm = (p : ℤ) ^ n → t.HasLPSParity →
    ¬t.CoordinatesDvd (p : ℤ) →
    ∃ word : LPSReducedWord a.degreePrime.pos n,
      lpsQuaternionWordProduct word.1.1 = t ∨
        lpsQuaternionWordProduct word.1.1 = -t := by
  intro n
  letI : Fact p.Prime := ⟨a.degreePrime⟩
  induction n with
  | zero =>
      intro t hnorm hparity _hprimitive
      have hnormOne : t.norm = 1 := by simpa using hnorm
      rcases eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
          t hnormOne hparity with ht | ht
      · let word : LPSReducedWord a.degreePrime.pos 0 :=
          ⟨⟨[], rfl⟩, lpsWordIsReduced_nil _⟩
        exact ⟨word, Or.inl (by simp [word, lpsQuaternionWordProduct, ht])⟩
      · let word : LPSReducedWord a.degreePrime.pos 0 :=
          ⟨⟨[], rfl⟩, lpsWordIsReduced_nil _⟩
        exact ⟨word, Or.inr (by simp [word, lpsQuaternionWordProduct, ht])⟩
  | succ n ih =>
      intro t hnorm hparity hprimitive
      have hpDvdNorm : (p : ℤ) ∣ t.norm := by
        refine ⟨(p : ℤ) ^ n, ?_⟩
        rw [hnorm, pow_succ]
        ring
      obtain ⟨beta, hdiv⟩ :=
        exists_lpsPrimeRightFactor_of_not_coordinatesDvd
          a.degreePrime a.degreeModFour t hpDvdNorm hprimitive
      have hbetaNorm : beta.1.norm = (p : ℤ) :=
        norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos beta.2
      let u := lpsQuaternionDiv (p : ℤ) (t * beta.1.conj)
      have hfactor : u * beta.1 = t :=
        lpsQuaternionDiv_mul_conj_mul_eq a.degreePrime hbetaNorm hdiv
      have huNorm : u.norm = (p : ℤ) ^ n := by
        exact norm_lpsQuaternionDiv_mul_conj a.degreePrime hnorm hbetaNorm hdiv
      have hpNeTwo : p ≠ 2 := by
        intro hpTwo
        subst p
        have hp4 := a.degreeModFour
        norm_num at hp4
      have hpOddNat : Odd p := a.degreePrime.odd_of_ne_two hpNeTwo
      have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
      have hbetaParity :=
        hasLPSParity_of_mem_lpsQuaternionShell_prime a.degreeModFour beta.2
      have huParity : u.HasLPSParity := by
        apply hasLPSParity_lpsQuaternionDiv hpOdd hdiv
        exact hparity.mul hbetaParity.conj
      have huPrimitive : ¬u.CoordinatesDvd (p : ℤ) := by
        intro huDiv
        apply hprimitive
        rw [← hfactor]
        exact huDiv.mul_right beta.1
      obtain ⟨word, hwordProduct⟩ := ih u huNorm huParity huPrimitive
      let vec : List.Vector (LPSGeneratorIndex p) (n + 1) :=
        ⟨word.1.1 ++ [beta], by simp⟩
      have hvecReduced : LPSWordIsReduced a.degreePrime.pos vec.1 := by
        apply word.2.append (lpsWordIsReduced_singleton _ beta)
        intro x hx y hy
        simp only [List.head?_singleton, Option.mem_def] at hy
        have hyEq : y = beta := Option.some.inj hy.symm
        subst y
        intro hbacktrack
        have hbackVal := congrArg Subtype.val hbacktrack
        change beta.1 = x.1.conj at hbackVal
        apply hprimitive
        have hlastDiv :=
          coordinatesDvd_wordProduct_mul_conj_of_mem_getLast
            a.degreePrime word.1.1 x hx
        rcases hwordProduct with hwordProduct | hwordProduct
        · have htEq : t =
              lpsQuaternionWordProduct word.1.1 * x.1.conj := by
            rw [← hfactor, ← hwordProduct, hbackVal]
          rw [htEq]
          exact hlastDiv
        · have huEq : u = -lpsQuaternionWordProduct word.1.1 := by
            have hneg := congrArg Neg.neg hwordProduct
            simpa using hneg.symm
          have htEq : t =
              -(lpsQuaternionWordProduct word.1.1 * x.1.conj) := by
            rw [← hfactor, huEq, hbackVal]
            simp
          rw [htEq]
          exact hlastDiv.neg
      let result : LPSReducedWord a.degreePrime.pos (n + 1) :=
        ⟨vec, hvecReduced⟩
      refine ⟨result, ?_⟩
      rcases hwordProduct with hwordProduct | hwordProduct
      · left
        change lpsQuaternionWordProduct (word.1.1 ++ [beta]) = t
        rw [lpsQuaternionWordProduct_append,
          lpsQuaternionWordProduct_singleton, hwordProduct, hfactor]
      · right
        change lpsQuaternionWordProduct (word.1.1 ++ [beta]) = -t
        rw [lpsQuaternionWordProduct_append,
          lpsQuaternionWordProduct_singleton, hwordProduct, neg_mul, hfactor]

/-- Every LPS-parity quaternion of norm `p^n` has an alternating normal
form, up to the harmless central sign. -/
theorem exists_lpsAlternatingReducedWord_product_eq_or_eq_neg
    (a : LPSResiduePrime p) : ∀ (n : ℕ) (t : LPSQuaternion),
    t.norm = (p : ℤ) ^ n → t.HasLPSParity →
    ∃ word : LPSAlternatingReducedWord a.degreePrime.pos n,
      lpsAlternatingQuaternionProduct a n word = t ∨
        lpsAlternatingQuaternionProduct a n word = -t := by
  intro n
  letI : Fact p.Prime := ⟨a.degreePrime⟩
  have hpNeTwo : p ≠ 2 := by
    intro hpTwo
    subst p
    have hp4 := a.degreeModFour
    norm_num at hp4
  have hpOddNat : Odd p := a.degreePrime.odd_of_ne_two hpNeTwo
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  induction n using Nat.twoStepInduction with
  | zero =>
      intro t hnorm hparity
      have hnormOne : t.norm = 1 := by simpa using hnorm
      rcases eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
          t hnormOne hparity with ht | ht
      · let word : LPSAlternatingReducedWord a.degreePrime.pos 0 :=
          ⟨⟨[], rfl⟩, lpsWordIsReduced_nil _⟩
        exact ⟨word, Or.inl (by
          simp [word, lpsAlternatingQuaternionProduct,
            lpsQuaternionWordProduct, ht])⟩
      · let word : LPSAlternatingReducedWord a.degreePrime.pos 0 :=
          ⟨⟨[], rfl⟩, lpsWordIsReduced_nil _⟩
        exact ⟨word, Or.inr (by
          simp [word, lpsAlternatingQuaternionProduct,
            lpsQuaternionWordProduct, ht])⟩
  | one =>
      intro t hnorm hparity
      have hprimitive : ¬t.CoordinatesDvd (p : ℤ) :=
        not_coordinatesDvd_of_norm_eq_prime a.degreePrime t (by simpa using hnorm)
      obtain ⟨word, hword⟩ :=
        exists_lpsReducedWord_product_eq_or_eq_neg a 1 t hnorm hparity hprimitive
      exact ⟨word, by
        simpa [LPSAlternatingReducedWord,
          lpsAlternatingQuaternionProduct] using hword⟩
  | more n ih _ihOne =>
      intro t hnorm hparity
      by_cases hdiv : t.CoordinatesDvd (p : ℤ)
      · let u := lpsQuaternionDiv (p : ℤ) t
        have hscale : lpsScaleQuaternion (p : ℤ) u = t :=
          lpsScaleQuaternion_div_eq hdiv
        have huNorm : u.norm = (p : ℤ) ^ n :=
          norm_lpsQuaternionDiv_of_prime_pow a.degreePrime hdiv hnorm
        have huParity : u.HasLPSParity :=
          hasLPSParity_lpsQuaternionDiv hpOdd hdiv hparity
        obtain ⟨word, hword⟩ := ih u huNorm huParity
        refine ⟨Sum.inr word, ?_⟩
        rcases hword with hword | hword
        · left
          change lpsScaleQuaternion (p : ℤ)
              (lpsAlternatingQuaternionProduct a n word) = t
          rw [hword, hscale]
        · right
          change lpsScaleQuaternion (p : ℤ)
              (lpsAlternatingQuaternionProduct a n word) = -t
          rw [hword, lpsScaleQuaternion_neg, hscale]
      · obtain ⟨word, hword⟩ :=
          exists_lpsReducedWord_product_eq_or_eq_neg
            a (n + 2) t hnorm hparity hdiv
        exact ⟨Sum.inl word, by
          simpa [lpsAlternatingQuaternionProduct] using hword⟩

/-- The explicit alternating-normal-form map is surjective.  This is the
existence statement in the classical LPS quaternion factorization lemma. -/
theorem lpsAlternatingReducedWordToQuaternionShell_surjective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n) := by
  intro t
  have htNormalized := (mem_lpsQuaternionShell_iff
    (pow_pos a.degreePrime.pos n) t.1).mp t.2
  have htNorm : t.1.norm = (p : ℤ) ^ n := by
    exact_mod_cast htNormalized.1
  have hpPow4 : p ^ n % 4 = 1 :=
    lps_prime_pow_mod_four a.degreeModFour n
  have htParity : t.1.HasLPSParity :=
    hasLPSParity_of_mem_lpsQuaternionShell_prime hpPow4 t.2
  obtain ⟨word, hword⟩ :=
    exists_lpsAlternatingReducedWord_product_eq_or_eq_neg
      a n t.1 htNorm htParity
  refine ⟨word, Subtype.ext ?_⟩
  change lpsNormalizeFirstSign
      (lpsAlternatingQuaternionProduct a n word) = t.1
  rcases hword with hword | hword
  · simp [lpsNormalizeFirstSign, hword, htNormalized.2.1]
  · have htPos : 0 < t.1.a := htNormalized.2.1
    have hneg : ¬0 < (-t.1).a := by
      rw [LPSQuaternion.neg_a]
      omega
    rw [hword]
    rw [lpsNormalizeFirstSign, if_neg hneg]
    apply LPSQuaternion.ext <;> simp

/-- The explicit alternating normal-form map is a bijection. -/
theorem lpsAlternatingReducedWordToQuaternionShell_bijective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Bijective
      (lpsAlternatingReducedWordToQuaternionShell a n) :=
  lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)

/-- Exact LPS formula (4.14): the trace-congruence quaternion count is
twice the alternating closed reduced-word count. -/
theorem card_traceCongruenceShell_eq_two_mul_alternatingClosedCount
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * lpsAlternatingClosedReducedWordCount a n :=
  card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)

/-- Coefficient form of the exact LPS trace-count identity. -/
theorem coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount
    (a : LPSResiduePrime p) (n : ℕ) :
    PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) =
      2 * lpsAlternatingClosedReducedWordCount a n :=
  coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)

/-- The trace theta coefficient is exactly twice the finite Hecke identity
coefficient, with no remaining factorization hypothesis. -/
theorem coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff
    (a : LPSResiduePrime p) (n : ℕ) :
    ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) =
      2 * (lpsFiniteHeckeElement a n).coeff 1 :=
  coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)

end QEC.Coding.TannerLiftedProduct
