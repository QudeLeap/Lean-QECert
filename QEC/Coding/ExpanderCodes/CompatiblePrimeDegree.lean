import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Prime degrees compatible with local-code blocks

PK22 uses graph degrees `w = p + 1` with `p` prime and `p = 1 mod 4`.
The random local-code argument is most convenient when `w` is a multiple of
one fixed finite parameter block.  This module proves that the two arithmetic
requirements are simultaneously cofinal whenever the block length is odd.

No graph, spectral, local-code, or terminal coding conclusion is included in
the arithmetic witness.
-/

namespace QEC.Coding.TannerLiftedProduct

/-- A PK22 degree prime whose successor is compatible with one fixed local
parameter block. -/
structure CompatibleDegreePrime (A : Nat) where
  p : Nat
  prime : p.Prime
  oneModFour : p % 4 = 1
  blockDvdDegree : A ∣ p + 1

/-- Number of copies of the local parameter block in the graph degree. -/
def CompatibleDegreePrime.blocks {A : Nat} (a : CompatibleDegreePrime A) : Nat :=
  (a.p + 1) / A

theorem CompatibleDegreePrime.degree_eq_block_mul
    {A : Nat} (a : CompatibleDegreePrime A) :
    a.p + 1 = A * a.blocks := by
  symm
  exact Nat.mul_div_cancel' a.blockDvdDegree

theorem CompatibleDegreePrime.blocks_pos
    {A : Nat} (a : CompatibleDegreePrime A) (hA : 0 < A) :
    0 < a.blocks := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (by omega) a.blockDvdDegree
  · exact hA

/-- Every positive block quotient is within a factor `64 = 2^6` of the
sixth power of its floored sixth root. -/
theorem le_sixtyFour_mul_nthRoot_six_pow
    (n : Nat) (hn : 0 < n) :
    n ≤ 64 * (Nat.nthRoot 6 n) ^ 6 := by
  let x := Nat.nthRoot 6 n
  have hxPositive : 0 < x := by
    have hxOne : 1 ≤ Nat.nthRoot 6 n := by
      rw [Nat.le_nthRoot_iff (by norm_num)]
      simpa using (show 1 ≤ n by omega)
    exact hxOne
  have hnUpper : n < (x + 1) ^ 6 := by
    simpa [x] using Nat.lt_pow_nthRoot_add_one (by norm_num : 6 ≠ 0) n
  have hxDouble : x + 1 ≤ 2 * x := by omega
  calc
    n ≤ (x + 1) ^ 6 := hnUpper.le
    _ ≤ (2 * x) ^ 6 := Nat.pow_le_pow_left hxDouble 6
    _ = 64 * x ^ 6 := by ring

/-- The residue `2A - 1` is coprime to `4A` for every positive odd `A`.
It is simultaneously `-1 mod A` and `1 mod 4`. -/
theorem two_mul_sub_one_coprime_four_mul
    (A : Nat) (hA : 0 < A) (hOdd : Odd A) :
    (2 * A - 1).Coprime (4 * A) := by
  have hCoprimeA : (2 * A - 1).Coprime A := by
    have hRewrite : 2 * A - 1 = (A - 1) + A := by omega
    rw [hRewrite, Nat.coprime_add_self_left]
    exact (Nat.coprime_self_sub_left (by omega : 1 ≤ A)).2 (by simp)
  have hCoprimeFour : (2 * A - 1).Coprime 4 := by
    obtain ⟨k, rfl⟩ := hOdd
    have hRewrite : 2 * (2 * k + 1) - 1 = 4 * k + 1 := by omega
    rw [hRewrite]
    simp
  exact Nat.Coprime.mul_right hCoprimeFour hCoprimeA

/-- Above every bound there is a PK22-compatible prime degree divisible by
the prescribed positive odd block length. -/
theorem exists_compatibleDegreePrime_gt
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    ∃ a : CompatibleDegreePrime A, B < a.p := by
  have hCoprime := two_mul_sub_one_coprime_four_mul A hA hOdd
  obtain ⟨p, hpB, hpPrime, hpMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B
      (q := 4 * A) (a := 2 * A - 1) (by positivity) hCoprime
  have hResidueLt : 2 * A - 1 < 4 * A := by omega
  have hpMod' : p % (4 * A) = 2 * A - 1 := by
    change p % (4 * A) = (2 * A - 1) % (4 * A) at hpMod
    rw [Nat.mod_eq_of_lt hResidueLt] at hpMod
    exact hpMod
  have hpModA : p % A = A - 1 := by
    calc
      p % A = (p % (4 * A)) % A := by
        symm
        exact Nat.mod_mod_of_dvd p (by exact ⟨4, by ring⟩)
      _ = (2 * A - 1) % A := by rw [hpMod']
      _ = A - 1 := by
        have hRewrite : 2 * A - 1 = A + (A - 1) := by omega
        rw [hRewrite, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hpModFour : p % 4 = 1 := by
    calc
      p % 4 = (p % (4 * A)) % 4 := by
        symm
        exact Nat.mod_mod_of_dvd p (by exact ⟨A, by ring⟩)
      _ = (2 * A - 1) % 4 := by rw [hpMod']
      _ = 1 := by
        obtain ⟨k, rfl⟩ := hOdd
        omega
  have hDegree : A ∣ p + 1 := by
    by_cases hAOne : A = 1
    · subst A
      simp
    · rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpModA]
      have hOneMod : 1 % A = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hOneMod, Nat.sub_add_cancel (by omega : 1 ≤ A), Nat.mod_self]
  exact ⟨⟨p, hpPrime, hpModFour, hDegree⟩, hpB⟩

/-- The compatible prime can be chosen so that the floored sixth root of its
block quotient exceeds any prescribed scale. -/
theorem exists_compatibleDegreePrime_nthRoot_ge
    (A target : Nat) (hA : 0 < A) (hOdd : Odd A) :
    ∃ a : CompatibleDegreePrime A,
      target ≤ Nat.nthRoot 6 a.blocks := by
  obtain ⟨a, haLarge⟩ :=
    exists_compatibleDegreePrime_gt A (A * target ^ 6) hA hOdd
  refine ⟨a, (Nat.le_nthRoot_iff (by norm_num)).2 ?_⟩
  have hScaled : A * target ^ 6 < A * a.blocks := by
    calc
      A * target ^ 6 < a.p := haLarge
      _ < a.p + 1 := by omega
      _ = A * a.blocks := a.degree_eq_block_mul
  exact (Nat.mul_lt_mul_left hA).mp hScaled |>.le

/-- A deterministic noncomputable compatible degree prime above a bound. -/
noncomputable def compatibleDegreePrimeAt
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    CompatibleDegreePrime A :=
  Classical.choose (exists_compatibleDegreePrime_gt A B hA hOdd)

theorem lt_compatibleDegreePrimeAt
    (A B : Nat) (hA : 0 < A) (hOdd : Odd A) :
    B < (compatibleDegreePrimeAt A B hA hOdd).p :=
  Classical.choose_spec (exists_compatibleDegreePrime_gt A B hA hOdd)

end QEC.Coding.TannerLiftedProduct
