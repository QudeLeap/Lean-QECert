import QEC.Coding.ExpanderCodes.LPSQuaternionWord
import Mathlib.Data.Fintype.Vector

/-!
# Finite word expansion of Cayley adjacency powers

The `n`-th power of a labelled Cayley generator sum is the sum of the group
elements represented by all length-`n` words, with multiplicity.  For the
concrete LPS labels, closed words therefore map canonically to the quaternion
congruence shell occurring in the trace theta series.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

universe v

variable {G W : Type v} [Group G] [Fintype W]

/-- Ordered product in `G` represented by a fixed-length word of labels. -/
def cayleyVectorWordProduct
    (label : W → G) {n : ℕ} (word : List.Vector W n) : G :=
  (word.1.map label).prod

/-- Decompose a nonempty fixed-length word into its head and tail. -/
def vectorConsEquiv (n : ℕ) :
    W × List.Vector W n ≃ List.Vector W (n + 1) where
  toFun x := x.1 ::ᵥ x.2
  invFun word := (word.head, word.tail)
  left_inv x := by
    rcases x with ⟨head, tail⟩
    simp
  right_inv word := List.Vector.cons_head_tail word

omit [Fintype W] in
@[simp] theorem cayleyVectorWordProduct_cons
    (label : W → G) (head : W) {n : ℕ}
    (tail : List.Vector W n) :
    cayleyVectorWordProduct label (head ::ᵥ tail) =
      label head * cayleyVectorWordProduct label tail := by
  simp [cayleyVectorWordProduct, List.Vector.cons_val]

/-- Group-algebra sum of all length-`n` labelled words. -/
noncomputable def cayleyWordElement
    (label : W → G) (n : ℕ) : MonoidAlgebra ℂ G :=
  ∑ word : List.Vector W n,
    MonoidAlgebra.single (cayleyVectorWordProduct label word) 1

@[simp] theorem cayleyWordElement_zero (label : W → G) :
    cayleyWordElement label 0 = 1 := by
  classical
  have hproduct : ∀ word : List.Vector W 0,
      cayleyVectorWordProduct label word = 1 := by
    intro word
    have hnil : word.1 = [] :=
      List.eq_nil_of_length_eq_zero word.2
    simp [cayleyVectorWordProduct, hnil]
  unfold cayleyWordElement
  simp_rw [hproduct]
  simp
  exact MonoidAlgebra.one_def.symm

/-- Prefixing one generator gives the exact word recurrence. -/
theorem cayleyWordElement_add_one
    (label : W → G) (n : ℕ) :
    cayleyWordElement label (n + 1) =
      cayleyGeneratorSum label * cayleyWordElement label n := by
  classical
  rw [cayleyGeneratorSum, cayleyWordElement, cayleyWordElement,
    Finset.sum_mul]
  simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul]
  calc
    (∑ word : List.Vector W (n + 1),
        MonoidAlgebra.single
          (cayleyVectorWordProduct label word) (1 : ℂ)) =
        ∑ x : W × List.Vector W n,
          MonoidAlgebra.single
            (cayleyVectorWordProduct label (vectorConsEquiv n x))
            (1 : ℂ) := by
              exact (Equiv.sum_comp (vectorConsEquiv (W := W) n)
                (fun word => MonoidAlgebra.single
                  (cayleyVectorWordProduct label word) (1 : ℂ))).symm
    _ = ∑ x : W × List.Vector W n,
          MonoidAlgebra.single
            (label x.1 * cayleyVectorWordProduct label x.2) (1 : ℂ) := by
              apply Finset.sum_congr rfl
              intro x _hx
              change MonoidAlgebra.single
                  (cayleyVectorWordProduct label (x.1 ::ᵥ x.2)) (1 : ℂ) = _
              rw [cayleyVectorWordProduct_cons]
    _ = ∑ head : W, ∑ tail : List.Vector W n,
          MonoidAlgebra.single
            (label head * cayleyVectorWordProduct label tail) (1 : ℂ) :=
      Fintype.sum_prod_type _

/-- The finite word element is exactly the corresponding power of the
labelled Cayley generator sum. -/
theorem cayleyWordElement_eq_pow
    (label : W → G) (n : ℕ) :
    cayleyWordElement label n = cayleyGeneratorSum label ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega,
        cayleyWordElement_add_one, ih]
      exact (pow_succ' (cayleyGeneratorSum label) n).symm

/-- A coefficient of an adjacency power counts labelled words with the given
group product, including parallel-label multiplicity. -/
theorem coeff_cayleyGeneratorSum_pow
    [DecidableEq G] (label : W → G) (n : ℕ) (g : G) :
    (cayleyGeneratorSum label ^ n).coeff g =
      ((Finset.univ.filter fun word : List.Vector W n =>
        cayleyVectorWordProduct label word = g).card : ℂ) := by
  classical
  rw [← cayleyWordElement_eq_pow, cayleyWordElement,
    MonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_boole]

section LPS

variable {p : ℕ}

/-- Length-`n` LPS words whose product closes at the identity in the finite
vertex group. -/
noncomputable def lpsClosedWords
    (a : LPSResiduePrime p) (n : ℕ) :
    Finset (List.Vector (LPSGeneratorIndex p) n) :=
  Finset.univ.filter fun word =>
    lpsPSLWordProduct a word.1 = 1

theorem mem_lpsClosedWords_iff
    (a : LPSResiduePrime p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    word ∈ lpsClosedWords a n ↔
      lpsPSLWordProduct a word.1 = 1 := by
  simp [lpsClosedWords]

/-- The identity coefficient of the ordinary LPS adjacency power is the
number of closed labelled words. -/
theorem coeff_lpsGeneratorSum_pow_one
    (a : LPSResiduePrime p) (n : ℕ) :
    (cayleyGeneratorSum (lpsQuaternionLabel a) ^ n).coeff 1 =
      ((lpsClosedWords a n).card : ℂ) := by
  rw [coeff_cayleyGeneratorSum_pow]
  congr 1

/-- A closed finite LPS word has an integral quaternion product in the trace
congruence shell at norm `p^n`. -/
theorem lpsQuaternionWordProduct_mem_traceCongruenceShell_of_closed
    (a : LPSResiduePrime p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n)
    (hword : word ∈ lpsClosedWords a n) :
    lpsQuaternionWordProduct word.1 ∈
      lpsTraceCongruenceShell a.q (p ^ n) := by
  have hclosed := (mem_lpsClosedWords_iff a word).mp hword
  have hmem :=
    (lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell a word.1).mp
      hclosed
  simpa using hmem

/-- The canonical finite orbit map from closed LPS words to the trace
quadratic-form congruence shell.  Determining its fibres after the Hecke
backtracking correction is the remaining arithmetic orbit count. -/
noncomputable def lpsClosedWordToTraceShell
    (a : LPSResiduePrime p) (n : ℕ) :
    {word // word ∈ lpsClosedWords a n} →
      {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)} :=
  fun word => ⟨lpsQuaternionWordProduct word.1.1,
    lpsQuaternionWordProduct_mem_traceCongruenceShell_of_closed
      a word.1 word.2⟩

/-- The finite fibre of the closed-word orbit map above a fixed congruence
shell point.  The unresolved LPS orbit multiplicity is now represented by an
ordinary finite cardinality. -/
noncomputable def lpsClosedWordFiber
    (a : LPSResiduePrime p) (n : ℕ)
    (t : {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)}) :
    Finset {word // word ∈ lpsClosedWords a n} :=
  Finset.univ.filter fun word =>
    lpsClosedWordToTraceShell a n word = t

/-- Closed words decompose exactly into the fibres of their quaternion
congruence-shell image, including shell points with empty fibre. -/
theorem card_lpsClosedWords_eq_sum_closedWordFiber
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsClosedWords a n).card =
      ∑ t : {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)},
        (lpsClosedWordFiber a n t).card := by
  classical
  rw [← Fintype.card_coe]
  simpa [lpsClosedWordFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ :
        Finset {word // word ∈ lpsClosedWords a n}))
      (t := (Finset.univ :
        Finset {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)}))
      (f := lpsClosedWordToTraceShell a n)
      (fun _word _hword => Finset.mem_univ _))

end LPS

end QEC.Coding.TannerLiftedProduct
