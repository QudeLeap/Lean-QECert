import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Lean.Elab.Tactic.Omega

/-!
# Finite-field specialization parameters

The quaternion construction in [DEL21, Section 6.2] is specialized away from
`y = 0` and `y = -1`. A primitive element in an actual extension of degree
greater than one avoids both points, and its irreducible minimal polynomial
has the prescribed degree. Extension field cardinalities are cofinal here;
this is not a claim that a selected arithmetic group maps onto PSL₂, nor a
proof of the Ramanujan property of a congruence quotient.
-/

namespace QEC.Coding.ExpanderCodes

open IntermediateField

/-- An actual generator of a finite extension avoids the two excluded points. -/
theorem exists_full_degree_parameter (p n : ℕ) [Fact p.Prime] (hDegree : 1 < n) :
    ∃ y : GaloisField p n, y ≠ 0 ∧ 1 + y ≠ 0 ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = n ∧
      adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊤ := by
  have hNonzero : n ≠ 0 := by omega
  obtain ⟨y, hGenerate⟩ :=
    Field.exists_primitive_element_of_finite_top (ZMod p) (GaloisField p n)
  have hProper : (⊥ : IntermediateField (ZMod p) (GaloisField p n)) ≠ ⊤ := by
    intro hEqual
    have hRank := bot_eq_top_iff_finrank_eq_one.mp hEqual
    rw [GaloisField.finrank p hNonzero] at hRank
    omega
  refine ⟨y, ?_, ?_, minpoly.irreducible (IsIntegral.of_finite (ZMod p) y), ?_,
    hGenerate⟩
  · intro hZero
    apply hProper
    simpa only [hZero, adjoin_zero] using hGenerate
  · intro hZero
    have hNegative : y = -(1 : GaloisField p n) := eq_neg_of_add_eq_zero_right hZero
    have hBot : adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊥ :=
      adjoin_simple_eq_bot_iff.mpr (by
        rw [hNegative]
        exact (⊥ : IntermediateField (ZMod p) (GaloisField p n)).neg_mem
          (one_mem _))
    exact hProper (hBot.symm.trans hGenerate)
  · have hRank := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) y).mp
      hGenerate
    simpa only [GaloisField.finrank p hNonzero] using hRank

/-- Fixed-characteristic extension fields are arbitrarily large, with a
genuine irreducible specialization parameter of degree greater than two. -/
theorem exists_large_extension_parameter (p N : ℕ) [hPrime : Fact p.Prime] :
    ∃ n : ℕ, 2 < n ∧ N ≤ Nat.card (GaloisField p n) ∧
      ∃ y : GaloisField p n, y ≠ 0 ∧ 1 + y ≠ 0 ∧
        Irreducible (minpoly (ZMod p) y) ∧
        (minpoly (ZMod p) y).natDegree = n ∧
        adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊤ := by
  refine ⟨N + 3, by omega, ?_, exists_full_degree_parameter p (N + 3) (by omega)⟩
  rw [GaloisField.card p (N + 3) (by omega)]
  have hPow : N + 3 < p ^ (N + 3) := Nat.lt_pow_self hPrime.out.one_lt
  omega

end QEC.Coding.ExpanderCodes
