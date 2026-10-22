import QEC.Coding.AlgebraicGeometry.Towers.RegularRefinement
import QEC.Coding.AlgebraicGeometry.Towers.SourceRegularCoordinates

/-!
# Regular refinements of the actual source sequence

Away from the zero and pole of w the literal coordinate equations can be
adjoined in order, with all four trace steps regular at the final place.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

private theorem coordinateWindow_last_mem (x : ℕ → E) (n : ℕ) :
    x n ∈ coordinateWindow x 0 n := by
  cases n with
  | zero => exact mem_adjoin_simple_self F256 (x 0)
  | succ n =>
      simp only [coordinateWindow, Nat.zero_add]
      exact (show F256⟮x (n + 1)⟯ ≤ coordinateWindow x 0 n ⊔ F256⟮x (n + 1)⟯ from le_sup_right)
        (mem_adjoin_simple_self F256 (x (n + 1)))

/-- Direct regular adjunction of the entire literal source coordinate
sequence, over any already present initial field containing its w-parameter. -/
theorem sourceCoordinateSequence_regularRefinement
    (Q : GlobalPlace F256 E) (K : IntermediateField F256 E) (x : ℕ → E) (m : ℕ)
    (hrec : ∀ i < m, x (i + 1) ^ 16 + x (i + 1) = sourceStepRhs (x i))
    (hseed : x 0 ^ 16 + x 0 ∈ K)
    (hregular : ∀ i ≤ m, x i ∈ Q.valuationRing) :
    RegularRefinement Q K (K ⊔ coordinateWindow x 0 m) := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F256 E).injective 2
  induction m with
  | zero => exact artinSchreier16_regularRefinement Q K (x 0) (hregular 0 le_rfl) hseed
  | succ m ih =>
      have hprevious := ih (fun i hi => hrec i (by omega))
        (fun i hi => hregular i (by omega))
      let L := K ⊔ coordinateWindow x 0 m
      have hx : x m ∈ L := (show coordinateWindow x 0 m ≤ L from le_sup_right)
        (coordinateWindow_last_mem x m)
      have ha : x (m + 1) ^ 16 + x (m + 1) ∈ L := by
        rw [hrec m (by omega), sourceStepRhs]
        exact L.div_mem (L.toSubalgebra.pow_mem hx 16)
          (L.add_mem (L.toSubalgebra.pow_mem hx 15) L.one_mem)
      have hnext := artinSchreier16_regularRefinement Q L (x (m + 1))
        (hregular (m + 1) le_rfl) ha
      simpa only [L, coordinateWindow, Nat.zero_add, sup_assoc] using hprevious.trans hnext

/-- A regular actual image of w gives a regular refinement through the
whole embedded source field, without assuming a chain or an index formula. -/
theorem embeddedSourceW_regularRefinement (m : ℕ) (f : SourceField m →ₐ[F256] E)
    (Q : GlobalPlace F256 E) (K : IntermediateField F256 E)
    (hK : f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ∈ K)
    (hw : Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1) :
    RegularRefinement Q K (K ⊔ f.fieldRange) := by
  have h := sourceCoordinateSequence_regularRefinement Q K
    (fun i => f (sourceCoordinates m i)) m
    (fun i hi => by
      simpa only [map_add, map_pow, sourceStepRhs, map_div₀, map_one] using
        congrArg f (sourceCoordinates_recursion m i hi))
    (by simpa only [sourceCoordinates_zero, galoisBaseW, map_add, map_pow] using hK)
    (fun i hi => (Q.mem_valuationRing_iff _).mpr
      (le_of_eq (embeddedSourceCoordinates_units m f Q hw i hi).1))
  rw [← coordinateWindow_map, sourceCoordinates_window_eq_top,
    ← AlgHom.fieldRange_eq_map] at h
  exact h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
