import QEC.Coding.Core.Definitions

/-!
# Small-set expansion predicates for BE20 Tanner boundaries

The Panteleev--Kalachev distance argument used by BE20 takes quantitative
small-set expansion of a Tanner boundary and its transpose.  This module
records the property with exact natural-number cross multiplication.  It is a
proposition to be proved for the constructed Tanner maps, never a field of the
balanced-product construction.
-/

namespace QEC.Coding

end QEC.Coding

namespace LinearMap

open QEC.Coding

universe u v w

/--
Every input of weight at most `radius` expands by the rational factor
`expansionNumerator / expansionDenominator`.  Cross multiplication avoids any
rounding or coercion ambiguity.
-/
def SmallSetExpanding
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    (radius expansionNumerator expansionDenominator : Nat) : Prop :=
  0 < expansionDenominator ∧
    ∀ x : Word F ι,
      HammingWeight x ≤ radius →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator * HammingWeight (f x)

/--
Relative-radius form: the small-set premise is
`radiusDenominator * |x| ≤ radiusNumerator * |ι|`.
-/
def SmallSetExpandingAtRelativeRadius
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat) : Prop :=
  0 < radiusDenominator ∧ 0 < expansionDenominator ∧
    ∀ x : Word F ι,
      radiusDenominator * HammingWeight x ≤
          radiusNumerator * Fintype.card ι →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator * HammingWeight (f x)

theorem smallSetExpanding_mono_radius
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {f : Word F ι →ₗ[F] Word F κ}
    {smallRadius largeRadius expansionNumerator expansionDenominator : Nat}
    (hRadius : smallRadius ≤ largeRadius)
    (hExpansion : f.SmallSetExpanding
      largeRadius expansionNumerator expansionDenominator) :
    f.SmallSetExpanding
      smallRadius expansionNumerator expansionDenominator := by
  refine ⟨hExpansion.1, ?_⟩
  intro x hx
  exact hExpansion.2 x (hx.trans hRadius)

theorem smallSetExpandingAtRelativeRadius_mono_numerator
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {f : Word F ι →ₗ[F] Word F κ}
    {smallNumerator largeNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hNumerator : smallNumerator ≤ largeNumerator)
    (hExpansion : f.SmallSetExpandingAtRelativeRadius
      largeNumerator radiusDenominator
      expansionNumerator expansionDenominator) :
    f.SmallSetExpandingAtRelativeRadius
      smallNumerator radiusDenominator
      expansionNumerator expansionDenominator := by
  refine ⟨hExpansion.1, hExpansion.2.1, ?_⟩
  intro x hx
  apply hExpansion.2.2 x
  exact hx.trans (Nat.mul_le_mul_right (Fintype.card ι) hNumerator)

end LinearMap
