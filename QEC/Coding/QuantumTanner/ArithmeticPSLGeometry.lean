import QEC.Coding.ExpanderCodes.QuaternionPSLGenerators
import QEC.Coding.QuantumTanner.Goodness

/-!
# Arithmetic PSL₂ square complexes

The concrete quaternion generators are lifted into PSL₂ and used to construct
the four-corner square complex. Their constant-field index and inverse
permutations do not vary with the specialization field. All link identities
follow from the actual injectivity, inverse laws and total nonconjugacy.
This algebraic construction alone makes no Ramanujan or goodness claim.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.ArithmeticPSLGeometry

open QEC.Coding.ExpanderCodes.QuaternionGenerators

universe v

variable {F K : Type v} [Field F] [Field K] [Fintype F] [Fintype K]

/-- A fallback when the canonical quotient enumeration cannot be synthesized.
Keep Mathlib's quotient instance preferred under aggregate imports. -/
instance (priority := low) finitePSL :
    Fintype (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
  Fintype.ofFinite _

variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)

local notation "L" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "R" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI

/-- The actual PSL₂ square complex with a specialization-independent index. -/
def squareComplex :
    LeftRightCayleySquareComplex (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (TorusIndex epsilon) (TorusIndex epsilon) (CayleySquare L R) :=
  cayleySquareComplex L R (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (pslLeft_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslLeft_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (fun g a b => psl_total_nonconjugacy f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI a b g)

/-- The four-corner incidence laws required by the global distance argument. -/
theorem squareComplex_hasCayleyLinkIdentities :
    (squareComplex f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI).HasCayleyLinkIdentities := by
  unfold squareComplex
  exact cayleySquareComplex_hasCayleyLinkIdentities L R
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (pslLeft_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslLeft_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (fun g a b => psl_total_nonconjugacy f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI a b g)

end QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
