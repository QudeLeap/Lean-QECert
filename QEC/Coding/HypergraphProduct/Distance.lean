import QEC.Coding.HypergraphProduct.Parameters

/-!
# Extended distances for the Tillich--Zémor hypergraph product

Tillich and Zémor assign distance infinity to the zero classical code.  The
repository's older `MinimumDistance` predicate deliberately describes only a
nonzero finite minimum.  This module therefore defines the corresponding
actual `WithTop Nat`-valued distance by taking a finite infimum.  No distance
value or minimum-distance proof is stored in the construction data.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

/-- The minimum of a natural-number weight over a predicate on a finite type;
it is infinity when the predicate has no witness. -/
def finitePredicateMinimum
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (P : alpha → Prop) [DecidablePred P] (weight : alpha → Nat) : WithTop Nat :=
  Finset.univ.inf fun x => if P x then (weight x : WithTop Nat) else ⊤

theorem finitePredicateMinimum_le_of
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {P : alpha → Prop} [DecidablePred P] {weight : alpha → Nat}
    {x : alpha} (hx : P x) :
    finitePredicateMinimum P weight ≤ (weight x : WithTop Nat) := by
  exact (Finset.inf_le (f := fun y => if P y then (weight y : WithTop Nat) else ⊤)
    (Finset.mem_univ x)).trans_eq (if_pos hx)

theorem le_finitePredicateMinimum
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {P : alpha → Prop} [DecidablePred P] {weight : alpha → Nat}
    {d : WithTop Nat}
    (h : ∀ x, P x → d ≤ (weight x : WithTop Nat)) :
    d ≤ finitePredicateMinimum P weight := by
  apply Finset.le_inf
  intro x _hx
  by_cases hx : P x
  · simpa [finitePredicateMinimum, hx] using h x hx
  · simp [hx]

theorem finitePredicateMinimum_eq_top_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {P : alpha → Prop} [DecidablePred P] {weight : alpha → Nat} :
    finitePredicateMinimum P weight = ⊤ ↔ ∀ x, ¬ P x := by
  constructor
  · intro htop x hx
    have hle := finitePredicateMinimum_le_of (weight := weight) hx
    rw [htop] at hle
    exact (WithTop.not_top_le_coe (weight x) hle)
  · intro hnone
    apply top_unique
    apply le_finitePredicateMinimum
    intro x hx
    exact (hnone x hx).elim

/-- The source-convention distance of a finite-coordinate classical code. -/
def extendedMinimumDistance
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (C : LinearCode F iota) : WithTop Nat := by
  classical
  exact finitePredicateMinimum
    (fun x : Word F iota => x ∈ C.carrier ∧ x ≠ 0) HammingWeight

/-- A classical code has infinite extended distance exactly when it is the
zero code. -/
theorem extendedMinimumDistance_eq_top_iff
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (C : LinearCode F iota) :
    extendedMinimumDistance C = ⊤ ↔ C.carrier = ⊥ := by
  classical
  rw [extendedMinimumDistance, finitePredicateMinimum_eq_top_iff]
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      by_contra hx0
      exact h x ⟨hx, hx0⟩
    · exact bot_le
  · intro h x hx
    rw [h] at hx
    exact hx.2 (by simpa using hx.1)

/-- The union of the two nontrivial pure CSS logical sectors. -/
def IsCSSLogical
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota]
    (xCode zCode : LinearCode F iota) (x : Word F iota) : Prop :=
  (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
    (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)

/-- The actual `WithTop Nat`-valued algebraic CSS distance, including infinity
when there is no nontrivial logical sector. -/
def extendedAlgebraicCSSMinimumDistance
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (xCode zCode : LinearCode F iota) : WithTop Nat := by
  classical
  exact finitePredicateMinimum (IsCSSLogical xCode zCode) HammingWeight

end QEC.Coding.HypergraphProduct
