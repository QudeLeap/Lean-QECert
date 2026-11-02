import QEC.Coding.ExpanderCodes.Tradeoff

/-!
# Conditional PK20 Theorems 1--2

This is the terminal conditional declaration.  Its only input
is the narrowly scoped PK20 Proposition 1 expanding quasi-cyclic matrix
family.  The conclusion contains the complete first family and, for every
real `0 <= alpha < 1`, the actual twice-balanced binary CSS family at the
source exponent `alpha / (2(1-alpha))`.

All code parameters in the conclusion are derived fields of
`FirstFamilyMember` or `TradeoffMember`; neither is accepted as an input.
The unconditional public theorem remains unavailable until Proposition 1
itself is formalized.
-/

namespace QEC.Coding.ExpanderCodes.PK20

/-- Construction-level form of PK20 Theorems 1--2.  The first conjunct
contains both sides of the dimension window, the lower bounds for both CSS
distance sectors, the explicit weight-`ell` upper logical witness, and a
family-independent locality constant.  The second conjunct contains every
real tradeoff exponent, the two actual EKZ products, exact final blocklength,
the multiplied dimension and distance bounds, and uniform locality. -/
def LiftedProductAlmostLinearDistance : Prop :=
  FirstAlmostLinearFamily ∧ TwoProductConstructionFamily

/-- PK20 Theorems 1--2 conditional only on PK20 Proposition 1. -/
theorem liftedProductAlmostLinearDistance
    (hPropositionOne : PropositionOneExpandingMatrixFamily) :
    LiftedProductAlmostLinearDistance := by
  exact ⟨firstAlmostLinearFamily_of_propositionOne hPropositionOne,
    twoProductConstructionFamily_of_propositionOne hPropositionOne⟩

end QEC.Coding.ExpanderCodes.PK20
