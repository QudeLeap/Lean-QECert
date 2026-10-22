import QEC.Coding.BalancedProduct.LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The residue-prime branch of the LPS arithmetic schedule

For the PK22 graph `X^{p,q}`, the fixed degree prime `p` and the growing
quotient prime `q` are both `1` modulo `4`, and `p` must be a quadratic
residue modulo `q`.  This file constructs a cofinal supply of such `q` by
searching for the least prime in the progression `1 mod 4p` and applying
quadratic reciprocity. Dirichlet provides erased termination evidence; the
original family sequence now executes the actual decidable candidate search.

Only arithmetic facts are stored here.  In particular, there is no generator,
graph-expansion, spectral, or coding-theoretic assumption in the index.
-/

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

open scoped MatrixGroups

open Matrix

/-- `SL(2,q)` is the determinant-one kernel inside `GL(2,q)`.  Mathlib has
both groups and the determinant homomorphism; this equivalence makes the
finite-order calculation below explicit. -/
def specialLinearTwoEquivDetKer (q : ℕ) [Fact q.Prime] :
    SL(2, ZMod q) ≃
      (Matrix.GeneralLinearGroup.det :
        GL (Fin 2) (ZMod q) →* (ZMod q)ˣ).ker where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by simp⟩
  invFun A := ⟨(A.1 : Matrix (Fin 2) (Fin 2) (ZMod q)), by
    have h := congrArg Units.val A.property
    exact h⟩
  left_inv A := by rfl
  right_inv A := by
    ext
    rfl

/-- Exact order of `SL(2,q)` over a prime field. -/
theorem card_sl_two_zmod
    (q : ℕ) [Fact q.Prime] :
    Fintype.card SL(2, ZMod q) = q * (q ^ 2 - 1) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI : Fintype (GL (Fin 2) (ZMod q)) :=
    Fintype.ofInjective Units.val Units.val_injective
  have hGL : Nat.card (GL (Fin 2) (ZMod q)) =
      (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field (n := 2)]
    simp [ZMod.card]
  let detHom :=
    (Matrix.GeneralLinearGroup.det :
      GL (Fin 2) (ZMod q) →* (ZMod q)ˣ)
  have hdetRange : detHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective
  have hker := detHom.ker.card_mul_index
  rw [Subgroup.index_ker, hdetRange, Subgroup.card_top] at hker
  have hUnits : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hUnits, hGL] at hker
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (specialLinearTwoEquivDetKer q)]
  have hfactor : q ^ 2 - q = q * (q - 1) := by
    simp [pow_two, Nat.mul_sub_left_distrib]
  rw [hfactor] at hker
  have hqTwo : 2 ≤ q := (Fact.out : q.Prime).two_le
  apply Nat.mul_right_cancel (by omega : 0 < q - 1)
  calc
    Nat.card detHom.ker * (q - 1) =
        (q ^ 2 - 1) * (q * (q - 1)) := hker
    _ = (q * (q ^ 2 - 1)) * (q - 1) := by ring

/-- For odd prime `q`, the center of `SL(2,q)` consists of the two scalar
matrices `±I`. -/
theorem card_center_sl_two_zmod
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    Nat.card (Subgroup.center SL(2, ZMod q)) = 2 := by
  calc
    Nat.card (Subgroup.center SL(2, ZMod q)) =
        Nat.card (rootsOfUnity 2 (ZMod q)) := by
      exact Nat.card_congr
        Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv
    _ = 2 := (IsPrimitiveRoot.neg_one q hqTwo).card_rootsOfUnity

/-- Exact order of `PSL(2,q)` for an odd prime `q`. -/
theorem card_psl_two_zmod
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    Fintype.card PSL(2, ZMod q) = q * (q ^ 2 - 1) / 2 := by
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center SL(2, ZMod q))
  change Nat.card SL(2, ZMod q) =
    Nat.card PSL(2, ZMod q) *
      Nat.card (Subgroup.center SL(2, ZMod q)) at hquot
  have hsl : Nat.card SL(2, ZMod q) = q * (q ^ 2 - 1) := by
    rw [Nat.card_eq_fintype_card, card_sl_two_zmod]
  rw [hsl, card_center_sl_two_zmod q hqTwo] at hquot
  rw [← Nat.card_eq_fintype_card]
  omega

/-- A source-compatible quotient prime for the residue/`PSL(2,q)` branch of
the LPS construction at the fixed degree prime `p`. -/
structure LPSResiduePrime (p : ℕ) where
  degreePrime : p.Prime
  degreeModFour : p % 4 = 1
  q : ℕ
  prime : q.Prime
  large : 4 * p < q
  modFour : q % 4 = 1
  residue : @legendreSym q ⟨prime⟩ p = 1

instance (a : LPSResiduePrime p) : Fact a.q.Prime := ⟨a.prime⟩

theorem LPSResiduePrime.ne_degreePrime (a : LPSResiduePrime p) :
    a.q ≠ p := by
  have hp : 0 < p := a.degreePrime.pos
  have hlarge := a.large
  omega

/-- The LPS degree prime is a good prime for the level `16q²` used by the
four-variable trace theta form [LPS, §4].  This is only a coprimality fact;
it does not assert modularity or a Hecke coefficient bound. -/
theorem LPSResiduePrime.coprime_thetaLevel
    (a : LPSResiduePrime p) : Nat.Coprime p (16 * a.q ^ 2) := by
  have hpTwo : p ≠ 2 := by
    intro h
    have hMod := a.degreeModFour
    norm_num [h] at hMod
  have hp16 : Nat.Coprime p 16 := by
    simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using
      (((Nat.coprime_primes a.degreePrime Nat.prime_two).2 hpTwo).pow_right 4)
  have hpq : Nat.Coprime p a.q :=
    (Nat.coprime_primes a.degreePrime a.prime).2 a.ne_degreePrime.symm
  exact Nat.Coprime.mul_right hp16 (hpq.pow_right 2)

theorem LPSResiduePrime.degree_nonzero (a : LPSResiduePrime p) :
    (p : ZMod a.q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt a.degreePrime.pos
    (by
      have hp : 0 < p := a.degreePrime.pos
      have hlarge := a.large
      omega)

/-- The exact Euler-criterion form of the source's residue condition. -/
theorem LPSResiduePrime.eulerCriterion (a : LPSResiduePrime p) :
    (p : ZMod a.q) ^ (a.q / 2) = 1 := by
  have h := legendreSym.eq_pow a.q (p : ℤ)
  simpa [a.residue] using h.symm

/-- The residue hypothesis in the exact natural-number congruence form printed
in PK22 Example 2.4. -/
theorem LPSResiduePrime.sourceResidueCongruence (a : LPSResiduePrime p) :
    p ^ ((a.q - 1) / 2) % a.q = 1 := by
  have hhalf : (a.q - 1) / 2 = a.q / 2 := by
    have hmod := a.modFour
    omega
  have hcast :
      ((p ^ ((a.q - 1) / 2) : ℕ) : ZMod a.q) = 1 := by
    simpa [hhalf] using a.eulerCriterion
  have hcast' :
      ((p ^ ((a.q - 1) / 2) : ℕ) : ZMod a.q) =
        ((1 : ℕ) : ZMod a.q) := by
    simpa using hcast
  have hmod := (ZMod.natCast_eq_natCast_iff'
    (p ^ ((a.q - 1) / 2)) 1 a.q).mp hcast'
  exact hmod.trans (Nat.mod_eq_of_lt a.prime.one_lt)

/-- Exact order of the source's LPS vertex group at this arithmetic index. -/
theorem LPSResiduePrime.card_psl (a : LPSResiduePrime p) :
    Fintype.card PSL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) / 2 := by
  apply card_psl_two_zmod a.q
  have hmod := a.modFour
  omega

/-- The bipartite double cover has exactly `q(q²-1)` vertices, matching the
`n` used in PK22 Example 2.4 and Lemma 3. -/
theorem LPSResiduePrime.two_mul_card_psl (a : LPSResiduePrime p) :
    2 * Fintype.card PSL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) := by
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center SL(2, ZMod a.q))
  change Nat.card SL(2, ZMod a.q) =
    Nat.card PSL(2, ZMod a.q) *
      Nat.card (Subgroup.center SL(2, ZMod a.q)) at hquot
  have hsl : Nat.card SL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) := by
    rw [Nat.card_eq_fintype_card, card_sl_two_zmod]
  have hqTwo : a.q ≠ 2 := by
    have hmod := a.modFour
    omega
  rw [hsl, card_center_sl_two_zmod a.q hqTwo] at hquot
  rw [Nat.card_eq_fintype_card] at hquot
  omega

/-- There are source-compatible residue primes above every bound.  The
progression `q = 1 mod 4p` simultaneously enforces `q = 1 mod 4` and
`q = 1 mod p`; quadratic reciprocity then gives `(p/q) = 1`. -/
theorem exists_lpsResiduePrime_gt
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    ∃ a : LPSResiduePrime p, B < a.q := by
  obtain ⟨q, hqBound, hqPrime, hqMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (4 * p))
      (q := 4 * p) (a := 1)
      (mul_ne_zero (by norm_num) hp.ne_zero) (by simp)
  letI : Fact q.Prime := ⟨hqPrime⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hqModFour : q % 4 = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hqMod)
    norm_num
  have hqModP : q % p = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hqMod)
    exact hp.one_lt
  have hqNeTwo : q ≠ 2 := by
    omega
  have hresidue : @legendreSym q ⟨hqPrime⟩ p = 1 := by
    change legendreSym q (p : ℤ) = 1
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp4 hqNeTwo,
      legendreSym.mod]
    have hmod : (q : ℤ) % p = 1 := by
      exact_mod_cast hqModP
    rw [hmod]
    simp
  exact ⟨⟨hp, hp4, q, hqPrime,
      lt_of_le_of_lt (Nat.le_max_right B (4 * p)) hqBound,
      hqModFour, hresidue⟩,
    lt_of_le_of_lt (Nat.le_max_left B (4 * p)) hqBound⟩

/-- Candidate test for the source-compatible arithmetic progression. -/
def lpsPrimeCandidate (p B q : ℕ) : Prop :=
  max B (4 * p) < q ∧ q.Prime ∧ q % (4 * p) = 1

instance (p B : ℕ) : DecidablePred (lpsPrimeCandidate p B) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Dirichlet supplies termination, while the candidate predicate is decidable. -/
theorem exists_lpsPrimeCandidate {p : ℕ} (hp : p.Prime) (B : ℕ) :
    ∃ q, lpsPrimeCandidate p B q := by
  obtain ⟨q, hBound, hPrime, hMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (4 * p))
      (q := 4 * p) (a := 1)
      (mul_ne_zero (by norm_num) hp.ne_zero) (by simp)
  refine ⟨q, hBound, hPrime, ?_⟩
  have hFour : 1 < 4 * p := by have := hp.two_le; omega
  exact Nat.mod_eq_of_modEq hMod hFour

/-- The actual least candidate, with proof-erased termination evidence. -/
def lpsLeastPrimeAbove {p : ℕ} (hp : p.Prime) (B : ℕ) : ℕ :=
  Nat.find (exists_lpsPrimeCandidate hp B)

theorem lpsLeastPrimeAbove_spec {p : ℕ} (hp : p.Prime) (B : ℕ) :
    lpsPrimeCandidate p B (lpsLeastPrimeAbove hp B) :=
  Nat.find_spec (exists_lpsPrimeCandidate hp B)

theorem lpsLeastPrimeAbove_min {p : ℕ} (hp : p.Prime) (B q : ℕ)
    (hq : lpsPrimeCandidate p B q) : lpsLeastPrimeAbove hp B ≤ q :=
  Nat.find_min' (exists_lpsPrimeCandidate hp B) hq

/-- Construct the real arithmetic LPS certificate from the computed candidate. -/
def lpsResiduePrimeAt {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) : LPSResiduePrime p := by
  let q := lpsLeastPrimeAbove hp B
  have hSpec := lpsLeastPrimeAbove_spec hp B
  have hBound := hSpec.1
  have hPrime := hSpec.2.1
  have hMod := hSpec.2.2
  have hModEq : Nat.ModEq (4 * p) q 1 := by
    exact hMod.trans (Nat.mod_eq_of_lt (by have := hp.two_le; omega)).symm
  have hModFour : q % 4 = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hModEq)
    norm_num
  have hModP : q % p = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hModEq)
    exact hp.one_lt
  let : Fact q.Prime := ⟨hPrime⟩
  let : Fact p.Prime := ⟨hp⟩
  have hNeTwo : q ≠ 2 := by omega
  have hResidue : @legendreSym q ⟨hPrime⟩ p = 1 := by
    change legendreSym q (p : ℤ) = 1
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp4 hNeTwo,
      legendreSym.mod]
    have hModInt : (q : ℤ) % p = 1 := by exact_mod_cast hModP
    rw [hModInt]
    simp
  exact ⟨hp, hp4, q, hPrime,
    lt_of_le_of_lt (Nat.le_max_right B (4 * p)) hBound,
    hModFour, hResidue⟩

@[simp] theorem lpsResiduePrimeAt_q {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsResiduePrimeAt hp hp4 B).q = lpsLeastPrimeAbove hp B := rfl

/-- The computed source-compatible quotient prime is above the requested bound. -/
theorem lt_lpsResiduePrimeAt
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    B < (lpsResiduePrimeAt hp hp4 B).q := by
  exact lt_of_le_of_lt (Nat.le_max_left _ _) (lpsLeastPrimeAbove_spec hp B).1

end QEC.Coding.TannerLiftedProduct
