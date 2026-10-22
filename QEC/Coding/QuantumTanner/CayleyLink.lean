import QEC.Coding.QuantumTanner.Distance

/-!
# Cayley link transport

The abstract incidence interface by itself does not relate links to group
multiplication. These exact rebase identities express the additional actual
four-corner geometry used by [LZ22, Section 3.1 and proof of thm:main].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- Rebase a realized square at each of its two opposite-side neighbors. -/
def HasCayleyLinkIdentities (X : LeftRightCayleySquareComplex G A B Square) : Prop :=
  (∀ g side a b, X.link (g, side) (a, b) =
    X.link (X.leftGenerator a * g, !side) (X.leftInverse a, b)) ∧
  (∀ g side a b, X.link (g, side) (a, b) =
    X.link (g * X.rightGenerator b, !side) (a, X.rightInverse b))

/-- A left edge transports an entire row without changing its word coordinates. -/
theorem rowRestriction_localRestriction_rebase_left
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) :
    rowRestriction a (X.localRestriction (g, side) x) =
      rowRestriction (X.leftInverse a)
        (X.localRestriction (X.leftGenerator a * g, !side) x) := by
  ext b
  exact congrArg x (hX.1 g side a b)

/-- A right edge similarly transports an entire column. -/
theorem columnRestriction_localRestriction_rebase_right
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (b : B) :
    columnRestriction b (X.localRestriction (g, side) x) =
      columnRestriction (X.rightInverse b)
        (X.localRestriction (g * X.rightGenerator b, !side) x) := by
  ext a
  exact congrArg x (hX.2 g side a b)

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
