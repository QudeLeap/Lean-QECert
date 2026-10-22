import QEC.Coding.AlgebraicGeometry.Towers.SourceCoordinates
import QEC.Coding.AlgebraicGeometry.Towers.RationalTraceSeed

/-!
# Actual coordinates away from the two w-fibres

The source equation propagates local units. This is the regular-place input
to Stichtenoth (2006), F2 and the proof that only w=0/infinity ramify.
It does not assert unramifiedness or a different formula by definition.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

/-- A unit additive parameter forces both the coordinate and its recursion
denominator to be units at the supplied actual place. -/
theorem additiveCoordinate_units (Q : GlobalPlace F256 E) (x : E)
    (hx : Q.valuation (x ^ 16 + x) = 1) :
    Q.valuation x = 1 ∧ Q.valuation (x ^ 15 + 1) = 1 := by
  have hunit : Q.valuation x = 1 := by
    rcases lt_trichotomy (Q.valuation x) 1 with hsmall | heq | hlarge
    · have hpow : Q.valuation (x ^ 16) < 1 := by
        rw [map_pow]
        exact pow_lt_one₀ zero_le hsmall (by norm_num)
      have h := (Q.valuation.map_add (x ^ 16) x).trans_lt (max_lt hpow hsmall)
      rw [hx] at h
      exact (lt_irrefl _ h).elim
    · exact heq
    · have hpow : Q.valuation x < Q.valuation (x ^ 16) := by
        rw [map_pow]
        simpa only [pow_one] using pow_lt_pow_right₀ hlarge (by norm_num : 1 < (16 : ℕ))
      have h := Q.valuation.map_add_eq_of_lt_left hpow
      rw [hx] at h
      exact (not_lt_of_ge (h.symm.le) (hlarge.trans hpow)).elim
  refine ⟨hunit, ?_⟩
  have hfactor : x * (x ^ 15 + 1) = x ^ 16 + x := by ring
  have h := congrArg Q.valuation hfactor
  simpa only [map_mul, hunit, one_mul, hx] using h

/-- The displayed rational recursion preserves this unit condition. -/
theorem sourceRecursion_units (Q : GlobalPlace F256 E) (x y : E)
    (hx : Q.valuation x = 1) (hden : Q.valuation (x ^ 15 + 1) = 1)
    (hrec : y ^ 16 + y = sourceStepRhs x) :
    Q.valuation y = 1 ∧ Q.valuation (y ^ 15 + 1) = 1 := by
  apply additiveCoordinate_units Q y
  rw [hrec, sourceStepRhs, map_div₀, map_pow, hx, hden, one_pow, div_self one_ne_zero]

/-- Unit propagation along a literal finite source coordinate sequence. -/
theorem sourceCoordinateSequence_units (Q : GlobalPlace F256 E) (x : ℕ → E) (m : ℕ)
    (hrec : ∀ i < m, x (i + 1) ^ 16 + x (i + 1) = sourceStepRhs (x i))
    (hseed : Q.valuation (x 0 ^ 16 + x 0) = 1) (i : ℕ) (hi : i ≤ m) :
    Q.valuation (x i) = 1 ∧ Q.valuation (x i ^ 15 + 1) = 1 := by
  induction i with
  | zero => exact additiveCoordinate_units Q (x 0) hseed
  | succ i ih =>
      have h := ih (by omega)
      exact sourceRecursion_units Q (x i) (x (i + 1)) h.1 h.2 (hrec i (by omega))

/-- The preceding calculation on every coordinate of an actual embedded
source field, with its actual image of w as the sole local unit premise. -/
theorem embeddedSourceCoordinates_units (m : ℕ) (f : SourceField m →ₐ[F256] E)
    (Q : GlobalPlace F256 E)
    (hw : Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1)
    (i : ℕ) (hi : i ≤ m) :
    Q.valuation (f (sourceCoordinates m i)) = 1 ∧
      Q.valuation (f (sourceCoordinates m i) ^ 15 + 1) = 1 := by
  apply sourceCoordinateSequence_units Q (fun j => f (sourceCoordinates m j)) m ?_ ?_ i hi
  · intro j hj
    simpa only [map_add, map_pow, sourceStepRhs, map_div₀, map_one] using
      congrArg f (sourceCoordinates_recursion m j hj)
  · simpa only [sourceCoordinates_zero, galoisBaseW, map_add, map_pow] using hw

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
