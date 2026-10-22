import QEC.Coding.AlgebraicGeometry.Towers.PlaceRefinement

/-!
# Literal consecutive-coordinate windows of the source pyramid

The window starting at `a` with width `n` is exactly
`k(x_a, ..., x_(a+n))`. Adjacent windows form the source's actual compositum
square; no common rational generator is assumed to lie in every window.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

/-- A literal coordinate window with `n + 1` coordinates. -/
def coordinateWindow (x : ℕ → E) (a : ℕ) : ℕ → IntermediateField F256 E
  | 0 => F256⟮x a⟯
  | n + 1 => coordinateWindow x a n ⊔ F256⟮x (a + n + 1)⟯

theorem coordinateWindow_le_succ (x : ℕ → E) (a n : ℕ) :
    coordinateWindow x a n ≤ coordinateWindow x a (n + 1) := le_sup_left

/-- The same actual window obtained by adjoining its first coordinate to
the remaining consecutive-coordinate window. -/
theorem coordinateWindow_first_sup_tail (x : ℕ → E) (a n : ℕ) :
    coordinateWindow x a (n + 1) = F256⟮x a⟯ ⊔ coordinateWindow x (a + 1) n := by
  induction n with
  | zero => simp only [coordinateWindow, Nat.add_zero]
  | succ n ih =>
      rw [coordinateWindow, ih, sup_assoc, coordinateWindow]
      rw [show a + (n + 1) + 1 = (a + 1) + n + 1 by omega]

theorem coordinateWindow_tail_le (x : ℕ → E) (a n : ℕ) :
    coordinateWindow x (a + 1) n ≤ coordinateWindow x a (n + 1) := by
  rw [coordinateWindow_first_sup_tail]
  exact le_sup_right

theorem coordinateWindow_first_le (x : ℕ → E) (a n : ℕ) :
    F256⟮x a⟯ ≤ coordinateWindow x a n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
      rw [coordinateWindow_first_sup_tail]
      exact le_sup_left

theorem coordinateWindow_congr (x y : ℕ → E) (a n : ℕ)
    (h : ∀ i, i ≤ n → x (a + i) = y (a + i)) :
    coordinateWindow x a n = coordinateWindow y a n := by
  induction n with
  | zero => simpa only [coordinateWindow, Nat.add_zero] using
      congrArg (fun z => F256⟮z⟯) (h 0 le_rfl)
  | succ n ih =>
      rw [coordinateWindow, coordinateWindow, ih (fun i hi => h i (by omega)),
        show x (a + n + 1) = y (a + n + 1) from h (n + 1) le_rfl]

theorem coordinateWindow_map {L : Type*} [_root_.Field L] [Algebra F256 L]
    (f : E →ₐ[F256] L) (x : ℕ → E) (a n : ℕ) :
    (coordinateWindow x a n).map f = coordinateWindow (fun i => f (x i)) a n := by
  induction n with
  | zero => simp only [coordinateWindow, IntermediateField.adjoin_map, Set.image_singleton]
  | succ n ih =>
      rw [coordinateWindow, IntermediateField.map_sup, ih, coordinateWindow,
        IntermediateField.adjoin_map, Set.image_singleton]

/-- The two overlapping windows in one source-pyramid square generate
exactly the next whole window. -/
theorem coordinateWindow_sup_adjacent (x : ℕ → E) (a n : ℕ) :
    coordinateWindow x a (n + 1) ⊔ coordinateWindow x (a + 1) (n + 1) =
      coordinateWindow x a (n + 2) := by
  change coordinateWindow x a (n + 1) ⊔
      (coordinateWindow x (a + 1) n ⊔ F256⟮x ((a + 1) + n + 1)⟯) =
    coordinateWindow x a (n + 1) ⊔ F256⟮x (a + (n + 1) + 1)⟯
  rw [← sup_assoc, sup_eq_left.mpr (coordinateWindow_tail_le x a n),
    show (a + 1) + n + 1 = a + (n + 1) + 1 by omega]

/-- Finiteness over a window follows from its actual first coordinate
field. This is an ordinary field-extension property, not ramification data. -/
scoped instance coordinateWindow_finite (x : ℕ → E) (a n : ℕ)
    [FiniteDimensional F256⟮x a⟯ E] :
    FiniteDimensional (coordinateWindow x a n) E := by
  letI : Algebra F256⟮x a⟯ (coordinateWindow x a n) :=
    (IntermediateField.inclusion (coordinateWindow_first_le x a n)).toRingHom.toAlgebra
  letI : IsScalarTower F256⟮x a⟯ (coordinateWindow x a n) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite F256⟮x a⟯ (coordinateWindow x a n) E

scoped instance coordinateWindow_separable (x : ℕ → E) (a n : ℕ)
    [Algebra.IsSeparable F256⟮x a⟯ E] :
    Algebra.IsSeparable (coordinateWindow x a n) E := by
  letI : Algebra F256⟮x a⟯ (coordinateWindow x a n) :=
    (IntermediateField.inclusion (coordinateWindow_first_le x a n)).toRingHom.toAlgebra
  letI : IsScalarTower F256⟮x a⟯ (coordinateWindow x a n) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable F256⟮x a⟯ (coordinateWindow x a n) E

variable (Q : GlobalPlace F256 E) [Finite Q.residueField] (x : ℕ → E)
    [∀ a, FiniteDimensional F256⟮x a⟯ E]
    [∀ a, Algebra.IsSeparable F256⟮x a⟯ E]

/-- The source's finite pyramid induction, in both directions. The only
normalized inputs are the two rational projections of its basic cells;
every higher edge is derived by sweeping the actual overlapping windows. -/
theorem coordinateWindow_normalized_edges (N : ℕ)
    (hbasic : ∀ a, a < N →
      PlaceNormalizedExtension Q (coordinateWindow x a 0) (coordinateWindow x a 1) ∧
      PlaceNormalizedExtension Q (coordinateWindow x (a + 1) 0) (coordinateWindow x a 1)) :
    ∀ n a, a + n < N →
      PlaceNormalizedExtension Q (coordinateWindow x a n) (coordinateWindow x a (n + 1)) ∧
      PlaceNormalizedExtension Q (coordinateWindow x (a + 1) n)
        (coordinateWindow x a (n + 1)) := by
  intro n
  induction n with
  | zero =>
      intro a ha
      exact hbasic a (by omega)
  | succ n ih =>
      intro a ha
      have hleft := (ih a (by omega)).2
      have hright := (ih (a + 1) (by omega)).1
      constructor
      · simpa only [coordinateWindow_sup_adjacent] using
          PlaceNormalizedExtension.compositum_left Q hleft hright
      · simpa only [sup_comm (coordinateWindow x (a + 1) (n + 1)),
          coordinateWindow_sup_adjacent] using
          PlaceNormalizedExtension.compositum_left Q hright hleft

/-- The left side of the finite pyramid is the whole original coordinate
chain, refined into normalized quadratic steps at the fixed ambient place. -/
theorem coordinateWindow_normalized_prefix (N : ℕ)
    (hbasic : ∀ a, a < N →
      PlaceNormalizedExtension Q (coordinateWindow x a 0) (coordinateWindow x a 1) ∧
      PlaceNormalizedExtension Q (coordinateWindow x (a + 1) 0) (coordinateWindow x a 1)) :
    ∀ n, n ≤ N → PlaceNormalizedExtension Q (coordinateWindow x 0 0)
      (coordinateWindow x 0 n) := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨le_rfl, ?_⟩
      have h : IntermediateField.extendScalars
          (show coordinateWindow x 0 0 ≤ coordinateWindow x 0 0 from le_rfl) = ⊥ := by
        apply IntermediateField.restrictScalars_injective F256
        exact (IntermediateField.restrictScalars_bot_eq_self _).symm
      rw [h]
  | succ n ih =>
      intro hn
      exact PlaceNormalizedExtension.trans Q (ih (by omega))
        ((coordinateWindow_normalized_edges Q x N hbasic n 0 (by omega)).1)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
