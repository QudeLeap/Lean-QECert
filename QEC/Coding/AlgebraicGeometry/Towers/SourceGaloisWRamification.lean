import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWGlobalPlaces

/-!
# The first source Galois ramification constraint over F256(w)

The rational seed coordinate `x₀` is an actual element of every corrected
source normal closure and satisfies `x₀¹⁶ + x₀ = w`.  At an upper place
over the pole of `w`, comparison of the two unequal orders in this literal
equation shows that the common ramification index is divisible by sixteen.

This file proves only the resulting infinity-fibre divisibility, parity, and
lower bound.  It does not assert the corresponding zero-fibre calculation,
the different, a divisor, genus, canonicality, or an asymptotic conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private abbrev E (m : ℕ) := SourceGaloisClosureField m

/-- The literal rational seed coordinate `x₀` inside source normal-closure
level `m`. -/
noncomputable def sourceGaloisSeedCoordinate (m : ℕ) : E m :=
  sourceGaloisSeedRatFuncToClosure m RatFunc.X

/-- The embedded seed coordinate satisfies the defining relation
`x₀¹⁶ + x₀ = w`. -/
theorem sourceGaloisSeedCoordinate_pow_sixteen_add (m : ℕ) :
    sourceGaloisSeedCoordinate m ^ 16 + sourceGaloisSeedCoordinate m =
      (sourceGaloisWClosureGenerator m : E m) := by
  change sourceGaloisSeedRatFuncToClosure m RatFunc.X ^ 16 +
      sourceGaloisSeedRatFuncToClosure m RatFunc.X =
    sourceGaloisSeedRatFuncToClosure m galoisBaseW
  rw [galoisBaseW, map_add, map_pow]

private theorem sourceGaloisSeedCoordinate_ne_zero (m : ℕ) :
    sourceGaloisSeedCoordinate m ≠ 0 := by
  have h := (sourceGaloisSeedRatFuncToClosure m).injective.ne RatFunc.X_ne_zero
  simp only [map_zero] at h
  exact h

private theorem sourceGaloisWClosureGenerator_ne_zero (m : ℕ) :
    (sourceGaloisWClosureGenerator m : E m) ≠ 0 := by
  have hw : galoisBaseW ≠ 0 := by
    intro hzero
    apply sourceGaloisBaseW_transcendental
    rw [hzero]
    exact isAlgebraic_zero
  change sourceGaloisSeedRatFuncToClosure m galoisBaseW ≠ 0
  have h := (sourceGaloisSeedRatFuncToClosure m).injective.ne hw
  simp only [map_zero] at h
  exact h

private theorem sourceGaloisW_order_pow (m n : ℕ)
    (P : GlobalPlace F256 (E m)) (x : E m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

private theorem sourceGaloisW_valuation_eq_exp_neg_order (m : ℕ)
    (P : GlobalPlace F256 (E m)) (x : E m) (hx : x ≠ 0) :
    P.valuation x = WithZero.exp (-P.order x) := by
  unfold GlobalPlace.order
  rw [neg_neg]
  exact (WithZero.exp_log (P.valuation.ne_zero_iff.mpr hx)).symm

/-- The common ramification index above the pole of `w` is divisible by
sixteen.  This is forced by the actual relation `x₀¹⁶ + x₀ = w`, not by
a stored numerical ramification value. -/
theorem sourceGaloisWInfinityRamificationIndex_sixteen_dvd (m : ℕ) :
    16 ∣ sourceGaloisWInfinityRamificationIndex m := by
  let P : SourceGaloisWInfinityPrime m :=
    Classical.choice (sourceGaloisWInfinityPrime_nonempty m)
  let Q : GlobalPlace F256 (E m) := sourceGaloisWInfinityPlaceOfPrime m P
  let x : E m := sourceGaloisSeedCoordinate m
  let w : E m := sourceGaloisWClosureGenerator m
  have hx : x ≠ 0 := by
    simpa only [x] using sourceGaloisSeedCoordinate_ne_zero m
  have hw : w ≠ 0 := by
    simpa only [w] using sourceGaloisWClosureGenerator_ne_zero m
  have hrelation : x ^ 16 + x = w := by
    simpa only [x, w] using sourceGaloisSeedCoordinate_pow_sixteen_add m
  have hworder : Q.order w =
      -(sourceGaloisWInfinityRamificationIndex m : ℤ) := by
    simpa only [Q, w] using
      sourceGaloisWInfinityPlaceOfPrime_order_generator m P
  have hxorder_neg : Q.order x < 0 := by
    by_contra hnot
    have hxorder_nonneg : 0 ≤ Q.order x := le_of_not_gt hnot
    have hxregular : GlobalPlace.RegularAt Q x :=
      (Q.regularAt_iff_order_nonnegative hx).mpr hxorder_nonneg
    have hxmem : x ∈ Q.valuationRing :=
      (Q.regularAt_iff_mem_valuationRing x).mp hxregular
    have hxpowmem : x ^ 16 ∈ Q.valuationRing :=
      Q.valuationRing.toSubring.pow_mem hxmem 16
    have hwmem : w ∈ Q.valuationRing := by
      rw [← hrelation]
      exact Q.valuationRing.add_mem _ _ hxpowmem hxmem
    have hwregular : GlobalPlace.RegularAt Q w :=
      (Q.regularAt_iff_mem_valuationRing w).mpr hwmem
    have hworder_nonneg : 0 ≤ Q.order w :=
      (Q.regularAt_iff_order_nonnegative hw).mp hwregular
    have hpositive := sourceGaloisWInfinityRamificationIndex_pos m
    omega
  have hxpow_order : Q.order (x ^ 16) = 16 * Q.order x := by
    simpa only [Nat.cast_ofNat] using sourceGaloisW_order_pow m 16 Q x
  have hxvalue : Q.valuation x = WithZero.exp (-Q.order x) :=
    sourceGaloisW_valuation_eq_exp_neg_order m Q x hx
  have hxpowvalue : Q.valuation (x ^ 16) =
      WithZero.exp (-(16 * Q.order x)) := by
    rw [sourceGaloisW_valuation_eq_exp_neg_order m Q (x ^ 16)
      (pow_ne_zero 16 hx), hxpow_order]
  have hvalue_lt : Q.valuation x < Q.valuation (x ^ 16) := by
    rw [hxvalue, hxpowvalue]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hsumorder : Q.order (x ^ 16 + x) = 16 * Q.order x := by
    calc
      Q.order (x ^ 16 + x) = Q.order (x ^ 16) := by
        unfold GlobalPlace.order
        rw [Q.valuation.map_add_eq_of_lt_left hvalue_lt]
      _ = 16 * Q.order x := hxpow_order
  rw [hrelation, hworder] at hsumorder
  let n : ℕ := Int.natAbs (Q.order x)
  have hn : (n : ℤ) = -Q.order x := by
    dsimp [n]
    rw [Int.natCast_natAbs, abs_of_neg hxorder_neg]
  refine ⟨n, ?_⟩
  have hcast : (sourceGaloisWInfinityRamificationIndex m : ℤ) =
      16 * (n : ℤ) := by
    calc
      (sourceGaloisWInfinityRamificationIndex m : ℤ) =
          -(16 * Q.order x) := by omega
      _ = 16 * (-Q.order x) := by ring
      _ = 16 * (n : ℤ) := by rw [← hn]
  exact_mod_cast hcast

/-- The common infinity-fibre ramification index is even. -/
theorem sourceGaloisWInfinityRamificationIndex_even (m : ℕ) :
    Even (sourceGaloisWInfinityRamificationIndex m) := by
  obtain ⟨n, hn⟩ := sourceGaloisWInfinityRamificationIndex_sixteen_dvd m
  refine ⟨8 * n, ?_⟩
  omega

/-- The common infinity-fibre ramification index is at least two. -/
theorem sourceGaloisWInfinityRamificationIndex_two_le (m : ℕ) :
    2 ≤ sourceGaloisWInfinityRamificationIndex m := by
  obtain ⟨n, hn⟩ := sourceGaloisWInfinityRamificationIndex_sixteen_dvd m
  have hpositive := sourceGaloisWInfinityRamificationIndex_pos m
  omega

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
