import QEC.Coding.ExpanderCodes.CayleyWordTrace
import QEC.Coding.ExpanderCodes.JacobiFourSquareCount

/-!
# Reduced words in the LPS quaternion generators

The direct trace proof uses the spheres in the free quaternion tree.  This
module makes their finite combinatorics explicit: quaternion conjugation is
the fixed-point-free inverse involution on the `p + 1` directions, and a
reduced word is one with no adjacent inverse pair.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- Quaternion conjugation acts as an involution on generator indices. -/
@[simp] theorem lpsGeneratorConjEquiv_apply_apply
    (hp : 0 < p) (t : LPSGeneratorIndex p) :
    lpsGeneratorConjEquiv hp (lpsGeneratorConjEquiv hp t) = t := by
  apply Subtype.ext
  exact t.1.conj_conj

/-- A normalized prime-norm LPS generator is never its own conjugate. -/
theorem lpsGeneratorConjEquiv_ne
    (hp : p.Prime) (t : LPSGeneratorIndex p) :
    lpsGeneratorConjEquiv hp.pos t ≠ t := by
  intro hfixed
  have hval := congrArg Subtype.val hfixed
  change t.1.conj = t.1 at hval
  have hb := congrArg LPSQuaternion.b hval
  have hc := congrArg LPSQuaternion.c hval
  have hd := congrArg LPSQuaternion.d hval
  simp only [LPSQuaternion.conj_b] at hb
  simp only [LPSQuaternion.conj_c] at hc
  simp only [LPSQuaternion.conj_d] at hd
  have hbZero : t.1.b = 0 := by linarith
  have hcZero : t.1.c = 0 := by linarith
  have hdZero : t.1.d = 0 := by linarith
  have hnorm := norm_eq_of_mem_lpsQuaternionShell hp.pos t.2
  have haSqInt : t.1.a ^ 2 = (p : ℤ) := by
    simpa [LPSQuaternion.norm, hbZero, hcZero, hdZero] using hnorm
  have haSqNat : t.1.a.natAbs ^ 2 = p := by
    rw [← Nat.cast_inj (R := ℤ), Int.natCast_pow,
      Int.natCast_natAbs, sq_abs]
    exact haSqInt
  exact hp.not_isSquare ⟨t.1.a.natAbs, by
    simpa [sq] using haSqNat.symm⟩

/-- Directions allowed immediately after `t` in a reduced LPS word. -/
noncomputable def lpsReducedSuccessors
    (hp : 0 < p) (t : LPSGeneratorIndex p) :
    Finset (LPSGeneratorIndex p) :=
  Finset.univ.erase (lpsGeneratorConjEquiv hp t)

theorem mem_lpsReducedSuccessors_iff
    (hp : 0 < p) (t u : LPSGeneratorIndex p) :
    u ∈ lpsReducedSuccessors hp t ↔
      u ≠ lpsGeneratorConjEquiv hp t := by
  simp [lpsReducedSuccessors]

/-- Exactly `p` directions remain after forbidding immediate backtracking. -/
theorem card_lpsReducedSuccessors
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSGeneratorIndex p) :
    (lpsReducedSuccessors hp.pos t).card = p := by
  rw [lpsReducedSuccessors, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_lpsGeneratorIndex,
    card_lpsQuaternionShell_eq_prime_add_one hp hp4]
  omega

/-- A word is reduced when no letter is followed by its conjugate/inverse. -/
def LPSWordIsReduced
    (hp : 0 < p) (word : List (LPSGeneratorIndex p)) : Prop :=
  word.IsChain fun t u => u ≠ lpsGeneratorConjEquiv hp t

noncomputable instance (hp : 0 < p)
    (word : List (LPSGeneratorIndex p)) :
    Decidable (LPSWordIsReduced hp word) :=
  Classical.propDecidable _

@[simp] theorem lpsWordIsReduced_nil (hp : 0 < p) :
    LPSWordIsReduced hp [] := by
  exact List.isChain_nil

@[simp] theorem lpsWordIsReduced_singleton
    (hp : 0 < p) (t : LPSGeneratorIndex p) :
    LPSWordIsReduced hp [t] := by
  exact List.isChain_singleton t

theorem lpsWordIsReduced_cons_cons
    (hp : 0 < p) (t u : LPSGeneratorIndex p)
    (word : List (LPSGeneratorIndex p)) :
    LPSWordIsReduced hp (t :: u :: word) ↔
      u ≠ lpsGeneratorConjEquiv hp t ∧
        LPSWordIsReduced hp (u :: word) :=
  List.isChain_cons_cons

/-- The no-backtracking relation is symmetric after applying quaternion
conjugation to the opposite endpoint. -/
theorem ne_lpsGeneratorConjEquiv_comm
    (hp : 0 < p) (t u : LPSGeneratorIndex p) :
    u ≠ lpsGeneratorConjEquiv hp t ↔
      t ≠ lpsGeneratorConjEquiv hp u := by
  constructor
  · intro h htu
    apply h
    have hconj := congrArg (lpsGeneratorConjEquiv hp) htu
    simpa using hconj.symm
  · intro h hut
    apply h
    have hconj := congrArg (lpsGeneratorConjEquiv hp) hut
    simpa using hconj.symm

/-- The finite set of reduced LPS words of a fixed length. -/
noncomputable def lpsReducedWords
    (hp : 0 < p) (n : ℕ) :
    Finset (List.Vector (LPSGeneratorIndex p) n) :=
  Finset.univ.filter fun word => LPSWordIsReduced hp word.1

/-- Subtype form of a fixed-length reduced word, useful for finite
equivalences that expose one no-backtracking choice. -/
abbrev LPSReducedWord (hp : 0 < p) (n : ℕ) :=
  {word : List.Vector (LPSGeneratorIndex p) n //
    LPSWordIsReduced hp word.1}

theorem mem_lpsReducedWords_iff
    (hp : 0 < p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    word ∈ lpsReducedWords hp n ↔
      LPSWordIsReduced hp word.1 := by
  simp [lpsReducedWords]

/-- A reduced word of length at least two is uniquely a reduced tail
prefixed by one of the `p` directions that does not backtrack. -/
noncomputable def lpsReducedWordConsEquiv
    (hp : p.Prime) (n : ℕ) :
    LPSReducedWord hp.pos (n + 2) ≃
      {pair : LPSReducedWord hp.pos (n + 1) × LPSGeneratorIndex p //
        pair.2 ∈ lpsReducedSuccessors hp.pos pair.1.1.head} where
  toFun word := by
    let tail : List.Vector (LPSGeneratorIndex p) (n + 1) := word.1.tail
    have htail : LPSWordIsReduced hp.pos tail.1 := by
      dsimp [tail]
      rw [List.Vector.tail_val]
      exact word.2.tail
    let reducedTail : LPSReducedWord hp.pos (n + 1) := ⟨tail, htail⟩
    refine ⟨⟨reducedTail, word.1.head⟩, ?_⟩
    rw [mem_lpsReducedSuccessors_iff,
      ← ne_lpsGeneratorConjEquiv_comm]
    have hchain : LPSWordIsReduced hp.pos
        (word.1.head :: word.1.tail.1) := by
      have hval := congrArg Subtype.val
        (List.Vector.cons_head_tail word.1)
      rw [List.Vector.cons_val] at hval
      rw [hval]
      exact word.2
    have htailVal := congrArg Subtype.val
      (List.Vector.cons_head_tail word.1.tail)
    rw [List.Vector.cons_val] at htailVal
    have htwo : LPSWordIsReduced hp.pos
        (word.1.head :: word.1.tail.head :: word.1.tail.tail.1) := by
      rw [htailVal]
      exact hchain
    exact (lpsWordIsReduced_cons_cons _ _ _ _).mp htwo |>.1
  invFun pair := by
    refine ⟨pair.1.2 ::ᵥ pair.1.1.1, ?_⟩
    rw [List.Vector.cons_val]
    apply List.IsChain.cons pair.1.1.2
    intro u hu
    have huHead : u = pair.1.1.1.head := by
      exact Option.some.inj
        (hu.symm.trans (List.Vector.head?_toList pair.1.1.1))
    subst u
    rw [ne_lpsGeneratorConjEquiv_comm,
      ← mem_lpsReducedSuccessors_iff]
    exact pair.2
  left_inv word := by
    apply Subtype.ext
    exact List.Vector.cons_head_tail word.1
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      simp
    · simp

/-- Prefix-oriented form of `lpsReducedWordConsEquiv`. -/
noncomputable def lpsReducedWordPrefixEquiv
    (hp : p.Prime) (n : ℕ) :
    {pair : LPSGeneratorIndex p × LPSReducedWord hp.pos (n + 1) //
      pair.1 ∈ lpsReducedSuccessors hp.pos pair.2.1.head} ≃
      LPSReducedWord hp.pos (n + 2) where
  toFun pair :=
    (lpsReducedWordConsEquiv hp n).symm
      ⟨⟨pair.1.2, pair.1.1⟩, pair.2⟩
  invFun word :=
    let pair := lpsReducedWordConsEquiv hp n word
    ⟨⟨pair.1.2, pair.1.1⟩, pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    simp
  right_inv word := by
    simp

/-- A forbidden prefix is uniquely the conjugate of the first letter. -/
noncomputable def lpsBacktrackingPrefixEquiv
    (hp : p.Prime) (n : ℕ) :
    {pair : LPSGeneratorIndex p × LPSReducedWord hp.pos (n + 1) //
      pair.1 ∉ lpsReducedSuccessors hp.pos pair.2.1.head} ≃
      LPSReducedWord hp.pos (n + 1) where
  toFun pair := pair.1.2
  invFun word := by
    refine ⟨⟨lpsGeneratorConjEquiv hp.pos word.1.head, word⟩, ?_⟩
    simp [mem_lpsReducedSuccessors_iff]
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · have hbacktrack : pair.1.1 =
          lpsGeneratorConjEquiv hp.pos pair.1.2.1.head := by
        simpa [mem_lpsReducedSuccessors_iff] using pair.2
      exact hbacktrack.symm
    · rfl
  right_inv word := rfl

@[simp] theorem lpsReducedWordConsEquiv_symm_tail
    (hp : p.Prime) (n : ℕ)
    (pair : {pair : LPSReducedWord hp.pos (n + 1) ×
        LPSGeneratorIndex p //
      pair.2 ∈ lpsReducedSuccessors hp.pos pair.1.1.head}) :
    ((lpsReducedWordConsEquiv hp n).symm pair).1.tail =
      pair.1.1.1 := by
  apply Subtype.ext
  simp [lpsReducedWordConsEquiv]

/-- The subtype and finite-set presentations of reduced words have the same
cardinality. -/
theorem card_lpsReducedWords_eq_fintype_card
    (hp : 0 < p) (n : ℕ) :
    (lpsReducedWords hp n).card =
      Fintype.card (LPSReducedWord hp n) := by
  classical
  rw [Fintype.card_subtype]
  rfl

/-- After the first letter, every reduced LPS word has exactly `p` possible
new prefixes. -/
theorem fintype_card_lpsReducedWord_add_two
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Fintype.card (LPSReducedWord hp.pos (n + 2)) =
      p * Fintype.card (LPSReducedWord hp.pos (n + 1)) := by
  classical
  rw [Fintype.card_congr (lpsReducedWordConsEquiv hp n),
    Fintype.card_congr
      (Equiv.subtypeProdEquivSigmaSubtype fun
        (tail : LPSReducedWord hp.pos (n + 1))
        (t : LPSGeneratorIndex p) =>
          t ∈ lpsReducedSuccessors hp.pos tail.1.head),
    Fintype.card_sigma]
  simp_rw [Fintype.card_coe,
    card_lpsReducedSuccessors hp hp4]
  simp [mul_comm]

/-- Finset form of the exact `p`-branching recurrence for reduced words. -/
theorem card_lpsReducedWords_add_two
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsReducedWords hp.pos (n + 2)).card =
      p * (lpsReducedWords hp.pos (n + 1)).card := by
  rw [card_lpsReducedWords_eq_fintype_card,
    card_lpsReducedWords_eq_fintype_card,
    fintype_card_lpsReducedWord_add_two hp hp4]

@[simp] theorem card_lpsReducedWords_zero (hp : 0 < p) :
    (lpsReducedWords hp 0).card = 1 := by
  classical
  have hall : ∀ word : List.Vector (LPSGeneratorIndex p) 0,
      LPSWordIsReduced hp word.1 := by
    intro word
    have hnil : word.1 = [] := List.eq_nil_of_length_eq_zero word.2
    rw [hnil]
    exact lpsWordIsReduced_nil (p := p) hp
  rw [lpsReducedWords]
  simp_rw [hall]
  simp [card_vector]

@[simp] theorem card_lpsReducedWords_one
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsReducedWords hp.pos 1).card = p + 1 := by
  classical
  have hall : ∀ word : List.Vector (LPSGeneratorIndex p) 1,
      LPSWordIsReduced hp.pos word.1 := by
    intro word
    have hlength := word.2
    obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hlength
    rw [ht]
    exact lpsWordIsReduced_singleton _ _
  rw [lpsReducedWords]
  simp_rw [hall]
  simp [card_vector,
    card_lpsQuaternionShell_eq_prime_add_one hp hp4]

/-- Exact size of the radius-`n+1` sphere in the free `(p+1)`-regular LPS
quaternion tree. -/
theorem card_lpsReducedWords_add_one
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsReducedWords hp.pos (n + 1)).card =
      (p + 1) * p ^ n := by
  induction n with
  | zero => simp [card_lpsReducedWords_one hp hp4]
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega,
        card_lpsReducedWords_add_two hp hp4 n, ih, pow_succ]
      ac_rfl

/-- Group-algebra sum of the finite reduced-word sphere. -/
noncomputable def lpsReducedWordElement
    (a : LPSResiduePrime p) (n : ℕ) :
    MonoidAlgebra ℂ PSL(2, ZMod a.q) :=
  ∑ word ∈ lpsReducedWords a.degreePrime.pos n,
    MonoidAlgebra.single
      (cayleyVectorWordProduct (lpsQuaternionLabel a) word) 1

/-- Subtype-sum presentation of the reduced-word sphere. -/
theorem lpsReducedWordElement_eq_sum
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsReducedWordElement a n =
      ∑ word : LPSReducedWord a.degreePrime.pos n,
        MonoidAlgebra.single
          (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1) 1 := by
  classical
  rw [lpsReducedWordElement]
  exact Finset.sum_subtype
    (lpsReducedWords a.degreePrime.pos n)
    (fun word => mem_lpsReducedWords_iff _ word)
    (fun word => MonoidAlgebra.single
      (cayleyVectorWordProduct (lpsQuaternionLabel a) word) 1)

@[simp] theorem cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
    (a : LPSResiduePrime p) (n : ℕ)
    (pair : {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      pair.1 ∈ lpsReducedSuccessors
        a.degreePrime.pos pair.2.1.head}) :
    cayleyVectorWordProduct (lpsQuaternionLabel a)
        (lpsReducedWordPrefixEquiv a.degreePrime n pair).1 =
      lpsQuaternionLabel a pair.1.1 *
        cayleyVectorWordProduct (lpsQuaternionLabel a) pair.1.2.1 := by
  exact cayleyVectorWordProduct_cons _ _ _

/-- Prefixing a letter and then its conjugate cancels in the finite LPS
vertex group.  This is the algebraic half of the non-backtracking Hecke
recurrence. -/
@[simp] theorem cayleyVectorWordProduct_lps_backtrack
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) {n : ℕ}
    (tail : List.Vector (LPSGeneratorIndex p) n) :
    cayleyVectorWordProduct (lpsQuaternionLabel a)
        (t ::ᵥ (lpsGeneratorConjEquiv a.degreePrime.pos t ::ᵥ tail)) =
      cayleyVectorWordProduct (lpsQuaternionLabel a) tail := by
  simp [cayleyVectorWordProduct_cons]

/-- Product carried by the canonical forbidden prefix reduces to the tail of
the reduced word. -/
@[simp] theorem lpsBacktrackingPrefixEquiv_symm_product
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSReducedWord a.degreePrime.pos (n + 1)) :
    lpsQuaternionLabel a
        ((lpsBacktrackingPrefixEquiv a.degreePrime n).symm word).1.1 *
      cayleyVectorWordProduct (lpsQuaternionLabel a)
        ((lpsBacktrackingPrefixEquiv a.degreePrime n).symm word).1.2.1 =
      cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail := by
  change lpsQuaternionLabel a
        (lpsGeneratorConjEquiv a.degreePrime.pos word.1.head) *
      cayleyVectorWordProduct (lpsQuaternionLabel a) word.1 = _
  rw [← cayleyVectorWordProduct_cons,
    ← List.Vector.cons_head_tail word.1]
  simpa using cayleyVectorWordProduct_lps_backtrack a
    (lpsGeneratorConjEquiv a.degreePrime.pos word.1.head) word.1.tail

/-- Summing the products left after one immediate backtrack gives exactly
`p` copies of the preceding reduced sphere. -/
theorem sum_lpsReducedWord_tail_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    (∑ word : LPSReducedWord a.degreePrime.pos (n + 2),
      MonoidAlgebra.single
        (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail) (1 : ℂ)) =
      p • lpsReducedWordElement a (n + 1) := by
  classical
  rw [lpsReducedWordElement_eq_sum]
  let e := lpsReducedWordConsEquiv a.degreePrime n
  let sigmaEquiv := Equiv.subtypeProdEquivSigmaSubtype fun
    (tail : LPSReducedWord a.degreePrime.pos (n + 1))
    (t : LPSGeneratorIndex p) =>
      t ∈ lpsReducedSuccessors a.degreePrime.pos tail.1.head
  calc
    (∑ word : LPSReducedWord a.degreePrime.pos (n + 2),
        MonoidAlgebra.single
          (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail) (1 : ℂ)) =
        ∑ pair,
          MonoidAlgebra.single
            (cayleyVectorWordProduct (lpsQuaternionLabel a)
              ((e.symm pair).1.tail)) (1 : ℂ) := by
                exact (Equiv.sum_comp e.symm _).symm
    _ = ∑ pair : {pair :
          LPSReducedWord a.degreePrime.pos (n + 1) × LPSGeneratorIndex p //
          pair.2 ∈ lpsReducedSuccessors
            a.degreePrime.pos pair.1.1.head},
          MonoidAlgebra.single
            (cayleyVectorWordProduct (lpsQuaternionLabel a) pair.1.1.1) (1 : ℂ) := by
              apply Finset.sum_congr rfl
              intro pair _hpair
              rw [show e = lpsReducedWordConsEquiv a.degreePrime n by rfl,
                lpsReducedWordConsEquiv_symm_tail]
    _ = ∑ pair : Σ tail : LPSReducedWord a.degreePrime.pos (n + 1),
          {t // t ∈ lpsReducedSuccessors
            a.degreePrime.pos tail.1.head},
          MonoidAlgebra.single
            (cayleyVectorWordProduct (lpsQuaternionLabel a) pair.1.1) (1 : ℂ) := by
              change (∑ x, MonoidAlgebra.single
                  (cayleyVectorWordProduct (lpsQuaternionLabel a)
                    (sigmaEquiv x).1.1) (1 : ℂ)) = _
              exact Equiv.sum_comp sigmaEquiv
                (fun pair : Σ tail : LPSReducedWord
                    a.degreePrime.pos (n + 1),
                    {t // t ∈ lpsReducedSuccessors
                      a.degreePrime.pos tail.1.head} =>
                  MonoidAlgebra.single
                    (cayleyVectorWordProduct
                      (lpsQuaternionLabel a) pair.1.1) (1 : ℂ))
    _ = ∑ tail : LPSReducedWord a.degreePrime.pos (n + 1),
          ∑ _t : {t // t ∈ lpsReducedSuccessors
            a.degreePrime.pos tail.1.head},
            MonoidAlgebra.single
              (cayleyVectorWordProduct (lpsQuaternionLabel a) tail.1) (1 : ℂ) := by
                rw [Fintype.sum_sigma]
    _ = p • ∑ tail : LPSReducedWord a.degreePrime.pos (n + 1),
          MonoidAlgebra.single
            (cayleyVectorWordProduct (lpsQuaternionLabel a) tail.1) (1 : ℂ) := by
              have hcard (tail : LPSReducedWord
                  a.degreePrime.pos (n + 1)) :
                  Fintype.card {t // t ∈ lpsReducedSuccessors
                    a.degreePrime.pos tail.1.head} = p := by
                simpa only [Fintype.card_coe] using
                  card_lpsReducedSuccessors
                    a.degreePrime a.degreeModFour tail.1.head
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro tail _htail
              rw [Finset.sum_const, Finset.card_univ, hcard tail]

/-- Whether a generator can prefix a reduced word without backtracking. -/
def LPSPrefixIsReduced (a : LPSResiduePrime p) (n : ℕ)
    (pair : LPSGeneratorIndex p ×
      LPSReducedWord a.degreePrime.pos (n + 1)) : Prop :=
  pair.1 ∈ lpsReducedSuccessors a.degreePrime.pos pair.2.1.head

noncomputable instance (a : LPSResiduePrime p) (n : ℕ)
    (pair : LPSGeneratorIndex p ×
      LPSReducedWord a.degreePrime.pos (n + 1)) :
    Decidable (LPSPrefixIsReduced a n pair) :=
  Classical.propDecidable _

/-- Prefix equivalence with the named prefix predicate as its exact domain. -/
noncomputable def lpsPrefixIsReducedEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      LPSPrefixIsReduced a n pair} ≃
      LPSReducedWord a.degreePrime.pos (n + 2) :=
  lpsReducedWordPrefixEquiv a.degreePrime n

/-- Forbidden-prefix equivalence with the named prefix predicate as its exact
domain. -/
noncomputable def lpsPrefixIsBacktrackingEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      ¬LPSPrefixIsReduced a n pair} ≃
      LPSReducedWord a.degreePrime.pos (n + 1) :=
  lpsBacktrackingPrefixEquiv a.degreePrime n

/-- Group-algebra contribution of a generator prefixed to a reduced word. -/
noncomputable def lpsPrefixTerm (a : LPSResiduePrime p) {n : ℕ}
    (pair : LPSGeneratorIndex p ×
      LPSReducedWord a.degreePrime.pos n) :
    MonoidAlgebra ℂ PSL(2, ZMod a.q) :=
  MonoidAlgebra.single
    (lpsQuaternionLabel a pair.1 *
      cayleyVectorWordProduct (lpsQuaternionLabel a) pair.2.1) 1

@[simp] theorem lpsPrefixTerm_reducedPrefixEquiv
    (a : LPSResiduePrime p) (n : ℕ)
    (pair : {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      LPSPrefixIsReduced a n pair}) :
    lpsPrefixTerm a pair.1 =
      MonoidAlgebra.single
        (cayleyVectorWordProduct (lpsQuaternionLabel a)
          (lpsReducedWordPrefixEquiv a.degreePrime n pair).1) 1 := by
  apply congrArg (fun g => MonoidAlgebra.single g (1 : ℂ))
  exact (cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
    a n pair).symm

@[simp] theorem lpsPrefixTerm_backtrackingPrefixEquiv_symm
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSReducedWord a.degreePrime.pos (n + 1)) :
    lpsPrefixTerm a
        ((lpsBacktrackingPrefixEquiv a.degreePrime n).symm word).1 =
      MonoidAlgebra.single
        (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail) 1 := by
  apply congrArg (fun g => MonoidAlgebra.single g (1 : ℂ))
  exact lpsBacktrackingPrefixEquiv_symm_product a n word

/-- The non-backtracking part of a prefixed sphere is the next sphere. -/
theorem sum_lpsPrefixTerm_filter_reduced
    (a : LPSResiduePrime p) (n : ℕ) :
    (∑ pair ∈ Finset.univ with LPSPrefixIsReduced a n pair,
      lpsPrefixTerm a pair) =
      lpsReducedWordElement a (n + 2) := by
  classical
  calc
    (∑ pair ∈ Finset.univ with LPSPrefixIsReduced a n pair,
        lpsPrefixTerm a pair) =
        ∑ pair : {pair // LPSPrefixIsReduced a n pair},
          lpsPrefixTerm a pair.1 := by
            exact Finset.sum_subtype
              (Finset.univ.filter (LPSPrefixIsReduced a n))
              (fun pair => by simp) (lpsPrefixTerm a)
    _ = ∑ word : LPSReducedWord a.degreePrime.pos (n + 2),
        MonoidAlgebra.single
          (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1) 1 := by
            let prefixEquiv := lpsPrefixIsReducedEquiv a n
            calc
              (∑ pair : {pair // LPSPrefixIsReduced a n pair},
                  lpsPrefixTerm a pair.1) =
                  ∑ pair, MonoidAlgebra.single
                    (cayleyVectorWordProduct (lpsQuaternionLabel a)
                      (prefixEquiv pair).1) (1 : ℂ) := by
                        apply Finset.sum_congr rfl
                        intro pair _hpair
                        exact lpsPrefixTerm_reducedPrefixEquiv a n pair
              _ = _ := Equiv.sum_comp prefixEquiv
                (fun word : LPSReducedWord a.degreePrime.pos (n + 2) =>
                  MonoidAlgebra.single
                    (cayleyVectorWordProduct
                      (lpsQuaternionLabel a) word.1) (1 : ℂ))
    _ = lpsReducedWordElement a (n + 2) :=
      (lpsReducedWordElement_eq_sum a (n + 2)).symm

/-- The backtracking part of a prefixed sphere is `p` copies of the sphere
two radii below. -/
theorem sum_lpsPrefixTerm_filter_backtracking_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    (∑ pair ∈ Finset.univ with ¬LPSPrefixIsReduced a (n + 1) pair,
      lpsPrefixTerm a pair) =
      p • lpsReducedWordElement a (n + 1) := by
  classical
  let backtrackEquiv := lpsPrefixIsBacktrackingEquiv a (n + 1)
  calc
    (∑ pair ∈ Finset.univ with ¬LPSPrefixIsReduced a (n + 1) pair,
        lpsPrefixTerm a pair) =
        ∑ pair : {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 2) //
        ¬LPSPrefixIsReduced a (n + 1) pair},
          lpsPrefixTerm a pair.1 := by
            exact Finset.sum_subtype
              (Finset.univ.filter fun pair =>
                ¬LPSPrefixIsReduced a (n + 1) pair)
              (fun pair => by simp) (lpsPrefixTerm a)
    _ = ∑ word : LPSReducedWord a.degreePrime.pos (n + 2),
          MonoidAlgebra.single
            (cayleyVectorWordProduct
              (lpsQuaternionLabel a) word.1.tail) 1 := by
            calc
              (∑ pair : {pair : LPSGeneratorIndex p ×
                  LPSReducedWord a.degreePrime.pos (n + 2) //
                  ¬LPSPrefixIsReduced a (n + 1) pair},
                  lpsPrefixTerm a pair.1) =
                  ∑ word, lpsPrefixTerm a
                    (backtrackEquiv.symm word).1 := by
                      exact (Equiv.sum_comp backtrackEquiv.symm
                        (fun pair => lpsPrefixTerm a pair.1)).symm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro word _hword
                exact lpsPrefixTerm_backtrackingPrefixEquiv_symm
                  a (n + 1) word
    _ = p • lpsReducedWordElement a (n + 1) :=
      sum_lpsReducedWord_tail_add_two a n

/-- Exact non-backtracking recurrence in the finite LPS group algebra.  The
coefficient `p` is proved by the reduced-prefix fibre count above. -/
theorem cayleyGeneratorSum_mul_lpsReducedWordElement_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyGeneratorSum (lpsQuaternionLabel a) *
        lpsReducedWordElement a (n + 2) =
      lpsReducedWordElement a (n + 3) +
        p • lpsReducedWordElement a (n + 1) := by
  classical
  rw [cayleyGeneratorSum, lpsReducedWordElement_eq_sum,
    Finset.sum_mul]
  simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul]
  rw [← Fintype.sum_prod_type
    (fun pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 2) =>
      MonoidAlgebra.single
        (lpsQuaternionLabel a pair.1 *
          cayleyVectorWordProduct (lpsQuaternionLabel a) pair.2.1)
        (1 : ℂ))]
  change (∑ pair, lpsPrefixTerm a pair) = _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (LPSPrefixIsReduced a (n + 1)) (lpsPrefixTerm a),
    sum_lpsPrefixTerm_filter_reduced a (n + 1),
    sum_lpsPrefixTerm_filter_backtracking_add_two a n]

/-- A coefficient of the reduced-word element counts reduced words with the
chosen finite group product. -/
theorem coeff_lpsReducedWordElement
    (a : LPSResiduePrime p) (n : ℕ)
    (g : PSL(2, ZMod a.q)) :
    (lpsReducedWordElement a n).coeff g =
      (((lpsReducedWords a.degreePrime.pos n).filter fun word =>
        cayleyVectorWordProduct (lpsQuaternionLabel a) word = g).card : ℂ) := by
  classical
  rw [lpsReducedWordElement, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_boole]

/-- Reduced words of length `n` that close at the identity in the finite LPS
Cayley graph. -/
noncomputable def lpsClosedReducedWords
    (a : LPSResiduePrime p) (n : ℕ) :
    Finset (List.Vector (LPSGeneratorIndex p) n) :=
  (lpsReducedWords a.degreePrime.pos n).filter fun word =>
    cayleyVectorWordProduct (lpsQuaternionLabel a) word = 1

theorem mem_lpsClosedReducedWords_iff
    (a : LPSResiduePrime p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    word ∈ lpsClosedReducedWords a n ↔
      LPSWordIsReduced a.degreePrime.pos word.1 ∧
        cayleyVectorWordProduct (lpsQuaternionLabel a) word = 1 := by
  simp [lpsClosedReducedWords, mem_lpsReducedWords_iff]

/-- The identity coefficient of a reduced-word sphere is its number of closed
reduced words. -/
theorem coeff_lpsReducedWordElement_one
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsReducedWordElement a n).coeff 1 =
      ((lpsClosedReducedWords a n).card : ℂ) := by
  simpa [lpsClosedReducedWords] using
    coeff_lpsReducedWordElement a n (1 : PSL(2, ZMod a.q))

/-- The alternating reduced spheres occurring in the LPS Hecke operator
`L_n = S_n + S_{n-2} + ⋯`. -/
noncomputable def lpsAlternatingReducedWordElement
    (a : LPSResiduePrime p) : ℕ →
    MonoidAlgebra ℂ PSL(2, ZMod a.q)
  | 0 => lpsReducedWordElement a 0
  | 1 => lpsReducedWordElement a 1
  | n + 2 => lpsReducedWordElement a (n + 2) +
      lpsAlternatingReducedWordElement a n

/-- Number of closed reduced words in the alternating LPS spheres of parity
`n`.  This is the finite Cayley-graph quantity denoted `L_n(e,e)` in LPS. -/
noncomputable def lpsAlternatingClosedReducedWordCount
    (a : LPSResiduePrime p) : ℕ → ℕ
  | 0 => (lpsClosedReducedWords a 0).card
  | 1 => (lpsClosedReducedWords a 1).card
  | n + 2 => (lpsClosedReducedWords a (n + 2)).card +
      lpsAlternatingClosedReducedWordCount a n

/-- The identity coefficient of the alternating reduced-sphere element is the
LPS closed-walk count `L_n(e,e)`. -/
theorem coeff_lpsAlternatingReducedWordElement_one
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsAlternatingReducedWordElement a n).coeff 1 =
      (lpsAlternatingClosedReducedWordCount a n : ℂ) := by
  classical
  induction n using Nat.twoStepInduction with
  | zero => simp [lpsAlternatingReducedWordElement,
      lpsAlternatingClosedReducedWordCount,
      coeff_lpsReducedWordElement_one]
  | one => simp [lpsAlternatingReducedWordElement,
      lpsAlternatingClosedReducedWordCount,
      coeff_lpsReducedWordElement_one]
  | more m hm _hmOne =>
    rw [lpsAlternatingReducedWordElement,
      lpsAlternatingClosedReducedWordCount, MonoidAlgebra.coeff_add]
    change (lpsReducedWordElement a (m + 2)).coeff 1 +
      (lpsAlternatingReducedWordElement a m).coeff 1 = _
    rw [coeff_lpsReducedWordElement_one, hm]
    exact_mod_cast rfl

@[simp] theorem lpsReducedWordElement_zero
    (a : LPSResiduePrime p) :
    lpsReducedWordElement a 0 = 1 := by
  classical
  rw [lpsReducedWordElement, lpsReducedWords]
  simp only [Finset.sum_filter]
  have hall : ∀ word : List.Vector (LPSGeneratorIndex p) 0,
      LPSWordIsReduced a.degreePrime.pos word.1 := by
    intro word
    have hnil : word.1 = [] := List.eq_nil_of_length_eq_zero word.2
    rw [hnil]
    exact lpsWordIsReduced_nil (p := p) a.degreePrime.pos
  simp_rw [hall]
  simp only [if_true]
  change cayleyWordElement (lpsQuaternionLabel a) 0 = 1
  exact cayleyWordElement_zero _

@[simp] theorem lpsReducedWordElement_one
    (a : LPSResiduePrime p) :
    lpsReducedWordElement a 1 =
      cayleyGeneratorSum (lpsQuaternionLabel a) := by
  classical
  rw [lpsReducedWordElement, lpsReducedWords]
  simp only [Finset.sum_filter]
  have hall : ∀ word : List.Vector (LPSGeneratorIndex p) 1,
      LPSWordIsReduced a.degreePrime.pos word.1 := by
    intro word
    have hlength := word.2
    obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hlength
    rw [ht]
    exact lpsWordIsReduced_singleton _ _
  simp_rw [hall]
  simp only [if_true]
  change cayleyWordElement (lpsQuaternionLabel a) 1 =
    cayleyGeneratorSum (lpsQuaternionLabel a)
  rw [cayleyWordElement_eq_pow, pow_one]

/-- At radius one, the backtracking fibre has `p+1` choices because there is
no preceding letter to exclude. -/
theorem sum_lpsPrefixTerm_filter_backtracking_zero
    (a : LPSResiduePrime p) :
    (∑ pair ∈ Finset.univ with ¬LPSPrefixIsReduced a 0 pair,
      lpsPrefixTerm a pair) =
      (p + 1) • lpsReducedWordElement a 0 := by
  classical
  let backtrackEquiv := lpsPrefixIsBacktrackingEquiv a 0
  have hcard : Fintype.card
      (LPSReducedWord a.degreePrime.pos 1) = p + 1 := by
    rw [← card_lpsReducedWords_eq_fintype_card,
      card_lpsReducedWords_one a.degreePrime a.degreeModFour]
  calc
    (∑ pair ∈ Finset.univ with ¬LPSPrefixIsReduced a 0 pair,
        lpsPrefixTerm a pair) =
        ∑ pair : {pair : LPSGeneratorIndex p ×
            LPSReducedWord a.degreePrime.pos 1 //
          ¬LPSPrefixIsReduced a 0 pair},
          lpsPrefixTerm a pair.1 := by
            exact Finset.sum_subtype
              (Finset.univ.filter fun pair =>
                ¬LPSPrefixIsReduced a 0 pair)
              (fun pair => by simp) (lpsPrefixTerm a)
    _ = ∑ word : LPSReducedWord a.degreePrime.pos 1,
          MonoidAlgebra.single
            (cayleyVectorWordProduct
              (lpsQuaternionLabel a) word.1.tail) 1 := by
            calc
              (∑ pair : {pair : LPSGeneratorIndex p ×
                  LPSReducedWord a.degreePrime.pos 1 //
                  ¬LPSPrefixIsReduced a 0 pair},
                  lpsPrefixTerm a pair.1) =
                  ∑ word, lpsPrefixTerm a
                    (backtrackEquiv.symm word).1 := by
                      exact (Equiv.sum_comp backtrackEquiv.symm
                        (fun pair => lpsPrefixTerm a pair.1)).symm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro word _hword
                exact lpsPrefixTerm_backtrackingPrefixEquiv_symm a 0 word
    _ = ∑ _word : LPSReducedWord a.degreePrime.pos 1,
          (1 : MonoidAlgebra ℂ PSL(2, ZMod a.q)) := by
            apply Finset.sum_congr rfl
            intro word _hword
            rw [List.Vector.singleton_tail word.1]
            rfl
    _ = (p + 1) • (1 : MonoidAlgebra ℂ PSL(2, ZMod a.q)) := by
      rw [Finset.sum_const, Finset.card_univ, hcard]
    _ = (p + 1) • lpsReducedWordElement a 0 := by simp

/-- Exceptional first non-backtracking recurrence at the root of the
`(p+1)`-regular tree. -/
theorem cayleyGeneratorSum_mul_lpsReducedWordElement_one
    (a : LPSResiduePrime p) :
    cayleyGeneratorSum (lpsQuaternionLabel a) *
        lpsReducedWordElement a 1 =
      lpsReducedWordElement a 2 +
        (p + 1) • lpsReducedWordElement a 0 := by
  classical
  rw [cayleyGeneratorSum, lpsReducedWordElement_eq_sum,
    Finset.sum_mul]
  simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul]
  rw [← Fintype.sum_prod_type
    (fun pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos 1 =>
      MonoidAlgebra.single
        (lpsQuaternionLabel a pair.1 *
          cayleyVectorWordProduct (lpsQuaternionLabel a) pair.2.1)
        (1 : ℂ))]
  change (∑ pair, lpsPrefixTerm a pair) = _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (LPSPrefixIsReduced a 0) (lpsPrefixTerm a),
    sum_lpsPrefixTerm_filter_reduced a 0,
    sum_lpsPrefixTerm_filter_backtracking_zero a]

@[simp] theorem lpsAlternatingReducedWordElement_zero
    (a : LPSResiduePrime p) :
    lpsAlternatingReducedWordElement a 0 = 1 := by
  simp [lpsAlternatingReducedWordElement]

@[simp] theorem lpsAlternatingReducedWordElement_one
    (a : LPSResiduePrime p) :
    lpsAlternatingReducedWordElement a 1 =
      cayleyGeneratorSum (lpsQuaternionLabel a) := by
  simp [lpsAlternatingReducedWordElement]

/-- The alternating reduced spheres satisfy the exact LPS Hecke recurrence. -/
theorem cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyGeneratorSum (lpsQuaternionLabel a) *
        lpsAlternatingReducedWordElement a (n + 1) =
      lpsAlternatingReducedWordElement a (n + 2) +
        p • lpsAlternatingReducedWordElement a n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [lpsAlternatingReducedWordElement]
      rw [cayleyGeneratorSum_mul_lpsReducedWordElement_one]
      simp [add_assoc, add_comm]
  | one =>
      simp only [lpsAlternatingReducedWordElement]
      rw [mul_add,
        cayleyGeneratorSum_mul_lpsReducedWordElement_add_two a 0]
      simp [add_comm, add_left_comm]
  | more n hn _hnOne =>
      simp only [lpsAlternatingReducedWordElement]
      rw [mul_add,
        cayleyGeneratorSum_mul_lpsReducedWordElement_add_two a (n + 1),
        hn, nsmul_add]
      rw [show lpsAlternatingReducedWordElement a (n + 2) =
        lpsReducedWordElement a (n + 2) +
          lpsAlternatingReducedWordElement a n by rfl]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      abel_nf

end QEC.Coding.TannerLiftedProduct
