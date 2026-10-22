import QEC.Coding.ExpanderCodes.FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith

/-!
# Full-degree finite-field points with square norm ratio

A multiplicative generator remains a field generator after squaring. The
rational substitution `y = t² / (1 - t²)` then gives a full-degree point with
`y / (1 + y) = t²`. This supplies the determinant-square condition for the
first arithmetic quaternion generator without assuming a square witness.
-/

namespace QEC.Coding.ExpanderCodes

open IntermediateField

/-- The square of a multiplicative generator still generates the entire finite field. -/
theorem adjoin_square_generator_eq_top {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (g : Kˣ) (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) :
    adjoin F ({(g : K) ^ 2} : Set K) = ⊤ := by
  classical
  let S := adjoin F ({(g : K) ^ 2} : Set K)
  let : Fintype S := Fintype.ofFinite S
  have hS : 1 < Nat.card S := Finite.one_lt_card
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have hPow : g ^ (2 * (Nat.card S - 1)) = 1 := by
    let a : S := ⟨(g : K) ^ 2, mem_adjoin_simple_self F ((g : K) ^ 2)⟩
    have ha : a ≠ 0 := by
      intro hZero
      exact pow_ne_zero 2 g.ne_zero (congrArg Subtype.val hZero)
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    have hField := congrArg (fun x : S => (x : K)) h
    change ((g : K) ^ 2) ^ (Fintype.card S - 1) = 1 at hField
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, ← pow_mul,
      Nat.card_eq_fintype_card] using hField
  have hDvd : Nat.card K - 1 ∣ 2 * (Nat.card S - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one hPow
  by_contra hProper
  have hMissing : ∃ x : K, x ∉ S := by
    by_contra hMissing
    push Not at hMissing
    apply hProper
    apply top_unique
    intro x _
    exact hMissing x
  obtain ⟨x, hx⟩ := hMissing
  have hLt : Nat.card S < Nat.card K := Finite.card_subtype_lt hx
  have hAddDvd : Nat.card S ∣ Nat.card K :=
    AddSubgroup.card_addSubgroup_dvd_card S.toSubfield.toSubring.toAddSubgroup
  obtain ⟨k, hk⟩ := hDvd
  have hkPositive : 0 < k := by
    by_contra hkNot
    have hkZero : k = 0 := by omega
    simp only [hkZero, mul_zero] at hk
    omega
  have hkLt : k < 2 := by
    have hBound : 2 * (Nat.card S - 1) < 2 * (Nat.card K - 1) := by omega
    nlinarith
  have hkOne : k = 1 := by omega
  rw [hkOne, mul_one] at hk
  have hAdd : Nat.card S ∣ Nat.card K + 1 := by
    exact ⟨2, by omega⟩
  have hOne : Nat.card S ∣ 1 := by
    simpa using Nat.dvd_sub hAdd hAddDvd
  have := Nat.le_of_dvd (by decide : 0 < 1) hOne
  omega

/-- An actual primitive field point with square ratio, obtained by a rational substitution. -/
theorem exists_square_ratio_generator {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (hCard : 3 < Nat.card K) :
    ∃ y t : K, y ≠ 0 ∧ 1 + y ≠ 0 ∧ t ≠ 0 ∧
      t ^ 2 = y / (1 + y) ∧ adjoin F ({y} : Set K) = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hSquareNeOne : (g : K) ^ 2 ≠ 1 := by
    intro hEqual
    have hDvd : Nat.card K - 1 ∣ 2 := by
      rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one (Units.ext hEqual)
    have := Nat.le_of_dvd (by decide : 0 < 2) hDvd
    omega
  have hDenom : 1 - (g : K) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hSquareNeOne)
  let y : K := (g : K) ^ 2 / (1 - (g : K) ^ 2)
  have hY : y ≠ 0 := div_ne_zero (pow_ne_zero 2 g.ne_zero) hDenom
  have hOneEq : 1 + y = (1 - (g : K) ^ 2)⁻¹ := by
    dsimp [y]
    field_simp
    ring
  have hOne : 1 + y ≠ 0 := by rw [hOneEq]; exact inv_ne_zero hDenom
  have hRatio : y / (1 + y) = (g : K) ^ 2 := by
    rw [hOneEq]
    dsimp [y]
    field_simp
  have hTop : adjoin F ({y} : Set K) = ⊤ := by
    have hMem : (g : K) ^ 2 ∈ adjoin F ({y} : Set K) := by
      rw [← hRatio]
      exact div_mem (mem_adjoin_simple_self F y)
        (add_mem (one_mem _) (mem_adjoin_simple_self F y))
    have hLe : adjoin F ({(g : K) ^ 2} : Set K) ≤ adjoin F ({y} : Set K) :=
      adjoin_le_iff.mpr (by
        intro z hz
        have hzEq : z = (g : K) ^ 2 := Set.mem_singleton_iff.mp hz
        rw [hzEq]
        exact hMem)
    rw [adjoin_square_generator_eq_top g hg] at hLe
    exact top_unique hLe
  exact ⟨y, g, hY, hOne, g.ne_zero, hRatio.symm, hTop⟩

/-- Every constant becomes a square in an even-degree finite-field extension. -/
theorem exists_constant_square_root_of_even_finrank
    {F K : Type*} [Field F] [Field K] [Finite K] [Algebra F K]
    (a : F) (hEven : 2 ∣ Module.finrank F K) :
    ∃ r : K, r ^ 2 = algebraMap F K a := by
  by_cases hSquare : ∃ r : F, r ^ 2 = a
  · obtain ⟨r, hr⟩ := hSquare
    exact ⟨algebraMap F K r, by rw [← map_pow, hr]⟩
  · apply exists_square_root_of_even_finrank a _ hEven
    intro r hr
    exact hSquare ⟨r, hr⟩

/-- Full-degree even specializations with the three explicit square roots
needed to place both quaternion generator sets in PSL₂. -/
theorem exists_even_psl_parameters (p n : ℕ) [hPrime : Fact p.Prime]
    (hDegree : 1 < n) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) :
    ∃ y r s i : GaloisField p (2 * n),
      y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
      s ^ 2 = y / (1 + y) ∧ i ^ 2 = -1 ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n := by
  have hCard : 3 < Nat.card (GaloisField p (2 * n)) := by
    rw [GaloisField.card p (2 * n) (by omega)]
    have := Nat.lt_pow_self hPrime.out.one_lt (n := 2 * n)
    omega
  obtain ⟨y, s, hY, hOne, hS, hRatio, hGenerate⟩ :=
    exists_square_ratio_generator (F := ZMod p) hCard
  have hEven : 2 ∣ Module.finrank (ZMod p) (GaloisField p (2 * n)) := by
    rw [GaloisField.finrank p (by omega)]
    exact dvd_mul_right 2 n
  obtain ⟨r, hRoot⟩ := exists_constant_square_root_of_even_finrank epsilon hEven
  obtain ⟨i, hI⟩ := exists_constant_square_root_of_even_finrank (-1 : ZMod p) hEven
  have hR : r ≠ 0 := by
    intro hZero
    have hImage : algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon = 0 := by
      simpa [hZero] using hRoot.symm
    exact hEpsilon ((algebraMap (ZMod p) (GaloisField p (2 * n))).injective
      (by simpa only [map_zero] using hImage))
  have hMinDegree := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) y).mp
    hGenerate
  refine ⟨y, r, s, i, hY, hOne, hR, hS, hRoot, hRatio, ?_,
    minpoly.irreducible (IsIntegral.of_finite (ZMod p) y), ?_⟩
  · simpa only [map_neg, map_one] using hI
  · rw [GaloisField.finrank p (n := 2 * n) (by omega)] at hMinDegree
    exact hMinDegree

end QEC.Coding.ExpanderCodes
