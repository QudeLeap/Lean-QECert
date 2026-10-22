import QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
import QEC.Coding.ExpanderCodes.ProjectiveLinearSize

/-!
# A cofinal arithmetic PSL₂ geometric family

At one fixed constant field and quadratic torus, actual square-ratio points
are chosen in every even extension of degree at least four. The resulting
PSL₂ square complexes have a fixed index and inverse permutations, and their
group cardinalities are cofinal. The spectral estimate is not asserted here.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily

open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators

abbrev FieldAt (p n : ℕ) [Fact p.Prime] := GaloisField p (2 * (n + 2))
abbrev GroupAt (p n : ℕ) [Fact p.Prime] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FieldAt p n)

variable (p : ℕ) [hPrime : Fact p.Prime]

instance fieldAtFintype (n : ℕ) : Fintype (FieldAt p n) := Fintype.ofFinite _
instance groupAtFintype (n : ℕ) : Fintype (GroupAt p n) := Fintype.ofFinite _

-- Downstream family interfaces compare these finite types without enumerating them.
attribute [irreducible] fieldAtFintype groupAtFintype

/-- The roots and full-degree point selected by the proved finite-field theorem. -/
structure Specialization (epsilon : ZMod p) (n : ℕ) where
  y : FieldAt p n
  r : FieldAt p n
  s : FieldAt p n
  i : FieldAt p n
  y_ne_zero : y ≠ 0
  one_add_y_ne_zero : 1 + y ≠ 0
  r_ne_zero : r ≠ 0
  root : r ^ 2 = algebraMap (ZMod p) (FieldAt p n) epsilon
  ratio : s ^ 2 = y / (1 + y)
  sqrt_neg_one : i ^ 2 = -1
  irreducible : Irreducible (minpoly (ZMod p) y)
  minpoly_degree : (minpoly (ZMod p) y).natDegree = 2 * (n + 2)

/-- No specialization certificate is assumed: all fields are constructed. -/
@[irreducible] def specialization (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) (n : ℕ) :
    Specialization p epsilon n := by
  apply Classical.choice
  obtain ⟨y, r, s, i, hY, hOne, hR, _, hRoot, hRatio, hI, hIrred, hDegree⟩ :=
    exists_even_psl_parameters p (n + 2) (by omega) epsilon hEpsilon
  exact ⟨⟨y, r, s, i, hY, hOne, hR, hRoot, hRatio, hI, hIrred, hDegree⟩⟩

omit hPrime in
theorem two_ne_zero {K : Type*} [Field K] [CharP K p]
    (hOdd : 3 ≤ p) : (2 : K) ≠ 0 := by
  intro hZero
  have hDvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hZero
  have := Nat.le_of_dvd (by decide : 0 < 2) hDvd
  omega

variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)

def left (n : ℕ) : TorusIndex epsilon → GroupAt p n :=
  let a := specialization p epsilon hEpsilon n
  pslLeft (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one

def right (n : ℕ) : TorusIndex epsilon → GroupAt p n :=
  let a := specialization p epsilon hEpsilon n
  pslRight (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one

theorem left_injective (n : ℕ) : Function.Injective (left p hOdd epsilon hEpsilon n) := by
  let a := specialization p epsilon hEpsilon n
  exact pslLeft_injective (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one

theorem right_injective (n : ℕ) : Function.Injective (right p hOdd epsilon hEpsilon n) := by
  let a := specialization p epsilon hEpsilon n
  exact pslRight_injective (algebraMap (ZMod p) (FieldAt p n)) epsilon a.r a.y a.s a.i
    hEpsilon a.root a.r_ne_zero (two_ne_zero p hOdd) a.y_ne_zero
    a.one_add_y_ne_zero (two_ne_zero p hOdd) a.ratio a.sqrt_neg_one

theorem left_inverse (n : ℕ) (a : TorusIndex epsilon) :
    left p hOdd epsilon hEpsilon n (indexedLeftInverse epsilon hEpsilon a) =
      (left p hOdd epsilon hEpsilon n a)⁻¹ := by
  let x := specialization p epsilon hEpsilon n
  exact pslLeft_inverse (algebraMap (ZMod p) (FieldAt p n)) epsilon x.r x.y x.s x.i
    hEpsilon x.root x.r_ne_zero (two_ne_zero p hOdd) x.y_ne_zero
    x.one_add_y_ne_zero (two_ne_zero p hOdd) x.ratio x.sqrt_neg_one a

theorem right_inverse (n : ℕ) (a : TorusIndex epsilon) :
    right p hOdd epsilon hEpsilon n a = (right p hOdd epsilon hEpsilon n a)⁻¹ := by
  let x := specialization p epsilon hEpsilon n
  exact pslRight_inverse (algebraMap (ZMod p) (FieldAt p n)) epsilon x.r x.y x.s x.i
    hEpsilon x.root x.r_ne_zero (two_ne_zero p hOdd) x.y_ne_zero
    x.one_add_y_ne_zero (two_ne_zero p hOdd) x.ratio x.sqrt_neg_one a

theorem total_nonconjugacy (n : ℕ) (g : GroupAt p n) (a b : TorusIndex epsilon) :
    left p hOdd epsilon hEpsilon n a * g ≠ g * right p hOdd epsilon hEpsilon n b := by
  let x := specialization p epsilon hEpsilon n
  exact psl_total_nonconjugacy (algebraMap (ZMod p) (FieldAt p n)) epsilon x.r x.y x.s x.i
    hEpsilon x.root x.r_ne_zero (two_ne_zero p hOdd) x.y_ne_zero
    x.one_add_y_ne_zero (two_ne_zero p hOdd) x.ratio x.sqrt_neg_one a b g

/-- The fixed-degree square geometry at each actual finite PSL₂ group. -/
def squareComplex (n : ℕ) :
    LeftRightCayleySquareComplex (GroupAt p n) (TorusIndex epsilon) (TorusIndex epsilon)
      (CayleySquare (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)) :=
  cayleySquareComplex (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon n) (right_injective p hOdd epsilon hEpsilon n)
    (left_inverse p hOdd epsilon hEpsilon n) (right_inverse p hOdd epsilon hEpsilon n)
    (total_nonconjugacy p hOdd epsilon hEpsilon n)

theorem squareComplex_hasCayleyLinkIdentities (n : ℕ) :
    (squareComplex p hOdd epsilon hEpsilon n).HasCayleyLinkIdentities :=
  cayleySquareComplex_hasCayleyLinkIdentities
    (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon n) (right_injective p hOdd epsilon hEpsilon n)
    (left_inverse p hOdd epsilon hEpsilon n) (right_inverse p hOdd epsilon hEpsilon n)
    (total_nonconjugacy p hOdd epsilon hEpsilon n)

include hOdd in
theorem index_card (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    Fintype.card (TorusIndex epsilon) = p + 1 := by
  rw [torusIndex_card epsilon hNonSquare (two_ne_zero p hOdd), ZMod.card]

/-- Unboundedness follows from an explicit field-to-PSL₂ injection. -/
theorem cofinal_group_card : ∀ N : ℕ, ∃ n, N ≤ Fintype.card (GroupAt p n) := by
  intro N
  refine ⟨N, ?_⟩
  rw [← Nat.card_eq_fintype_card]
  apply le_trans _ (ProjectiveLinearSize.field_card_le_psl_card (K := FieldAt p N))
  rw [GaloisField.card p (2 * (N + 2)) (by omega)]
  have := Nat.lt_pow_self hPrime.out.one_lt (n := 2 * (N + 2))
  omega

end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
