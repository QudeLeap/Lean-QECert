import QEC.Coding.BalancedProduct.BalancedFamilyLocality

/-!
# Conditional balanced-product families

The final BE20 conjunction retains the uniform graph-only LPS premise. The
balanced and unbalanced construction certificates remain reusable in Coding.
-/

namespace QEC.Coding.BalancedProduct.BE20Balanced

open QEC.Coding
open LPSFamily

/-- Public conditional endpoint for the registered BE20 family result. -/
theorem breuckmannEberhardtBalancedProductQLDPCFamilies
    (hLPS : LPS401FamilyRayleighBound) :
    (∀ B : Nat, ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BE20Unbalanced.UnbalancedFamilyCertificate
        a.q a.gt40 a.legendre) ∧
    (∀ B : Nat, ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BalancedFamilyCertificate a.q a.gt40 a.legendre) :=
  ⟨BE20Unbalanced.exists_be20_unbalanced_family_at hLPS,
    exists_be20_balanced_family_at hLPS⟩

end QEC.Coding.BalancedProduct.BE20Balanced
