import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewReconstructionTheorem
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Faithful Laurent evaluation at `1+y`

The central powers `z^{dn}` are Laurent powers of the transcendental
element `1+y`.  This module packages the injective evaluation needed to
separate skew exponents in the global representation.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def splittingOnePlusYUnit
    (P : BasePrime) (r : Rank) : (SplittingFunctionField P r)ˣ :=
  Units.mk0 (onePlusY P r) (onePlusY_ne_zero P r)

noncomputable def onePlusYLaurentEvaluation
    (P : BasePrime) (r : Rank) :
    LaurentPolynomial (ConstantExtension P r) →+*
      SplittingFunctionField P r :=
  LaurentPolynomial.eval₂
    (algebraMap (ConstantExtension P r) (SplittingFunctionField P r))
    (splittingOnePlusYUnit P r)

theorem onePlusYLaurentEvaluation_toLaurent
    (P : BasePrime) (r : Rank)
    (f : Polynomial (ConstantExtension P r)) :
    onePlusYLaurentEvaluation P r (Polynomial.toLaurent f) =
      algebraMap (Polynomial (ConstantExtension P r))
        (SplittingFunctionField P r)
          (f.comp (Polynomial.X + 1)) := by
  rw [onePlusYLaurentEvaluation, LaurentPolynomial.eval₂_toLaurent]
  change Polynomial.eval₂ RatFunc.C (1 + RatFunc.X) f = _
  calc
    _ = Polynomial.eval₂ RatFunc.C RatFunc.X
        (f.comp (Polynomial.X + 1)) := by
      symm
      rw [Polynomial.eval₂_comp]
      simp [add_comm]
    _ = _ := by
      have heq : Polynomial.eval₂RingHom RatFunc.C RatFunc.X =
          algebraMap (Polynomial (ConstantExtension P r))
            (SplittingFunctionField P r) := by
        ext c <;> simp
      exact RingHom.congr_fun heq _

theorem onePlusYPolynomialEvaluation_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective
      (fun f : Polynomial (ConstantExtension P r) =>
        Polynomial.eval₂
          (algebraMap (ConstantExtension P r) (SplittingFunctionField P r))
          (onePlusY P r) f) := by
  intro f g h
  have hmap : algebraMap (Polynomial (ConstantExtension P r))
      (SplittingFunctionField P r) (f.comp (Polynomial.X + 1)) =
    algebraMap (Polynomial (ConstantExtension P r))
      (SplittingFunctionField P r) (g.comp (Polynomial.X + 1)) := by
    rw [← onePlusYLaurentEvaluation_toLaurent P r f,
      ← onePlusYLaurentEvaluation_toLaurent P r g]
    simpa [onePlusYLaurentEvaluation, splittingOnePlusYUnit] using h
  have hcomp : f.comp (Polynomial.X + 1) =
      g.comp (Polynomial.X + 1) :=
    RatFunc.algebraMap_injective (ConstantExtension P r) hmap
  apply sub_eq_zero.mp
  apply (Polynomial.comp_X_add_C_eq_zero_iff
    (p := f - g) (t := (1 : ConstantExtension P r))).mp
  rw [Polynomial.sub_comp]
  have hcomp' : f.comp (Polynomial.X + Polynomial.C 1) =
      g.comp (Polynomial.X + Polynomial.C 1) := by
    simpa using hcomp
  rw [hcomp', sub_self]

theorem onePlusYLaurentEvaluation_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (onePlusYLaurentEvaluation P r) := by
  rw [onePlusYLaurentEvaluation]
  apply (IsLocalization.lift_injective_iff _).2
  intro f g
  rw [LaurentPolynomial.algebraMap_eq_toLaurent,
    LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_inj]
  simpa [splittingOnePlusYUnit, onePlusY] using
    (onePlusYPolynomialEvaluation_injective P r).eq_iff.symm

noncomputable def functionFieldOnePlusYUnit
    (P : BasePrime) : (FunctionField P)ˣ :=
  Units.mk0 (1 + RatFunc.X) (functionField_onePlusY_ne_zero P)

noncomputable def functionFieldOnePlusYLaurentEvaluation
    (P : BasePrime) :
    LaurentPolynomial (BaseField P) →+* FunctionField P :=
  LaurentPolynomial.eval₂
    (algebraMap (BaseField P) (FunctionField P))
    (functionFieldOnePlusYUnit P)

theorem functionFieldOnePlusYLaurentEvaluation_toLaurent
    (P : BasePrime) (f : PolynomialRing P) :
    functionFieldOnePlusYLaurentEvaluation P (Polynomial.toLaurent f) =
      algebraMap (PolynomialRing P) (FunctionField P)
        (f.comp (Polynomial.X + 1)) := by
  rw [functionFieldOnePlusYLaurentEvaluation,
    LaurentPolynomial.eval₂_toLaurent]
  change Polynomial.eval₂ RatFunc.C (1 + RatFunc.X) f = _
  calc
    _ = Polynomial.eval₂ RatFunc.C RatFunc.X
        (f.comp (Polynomial.X + 1)) := by
      symm
      rw [Polynomial.eval₂_comp]
      simp [add_comm]
    _ = _ := by
      have heq : Polynomial.eval₂RingHom RatFunc.C RatFunc.X =
          algebraMap (PolynomialRing P) (FunctionField P) := by
        ext c <;> simp
      exact RingHom.congr_fun heq _

theorem functionFieldOnePlusYPolynomialEvaluation_injective
    (P : BasePrime) :
    Function.Injective
      (fun f : PolynomialRing P =>
        Polynomial.eval₂
          (algebraMap (BaseField P) (FunctionField P))
          (1 + RatFunc.X) f) := by
  intro f g h
  have hmap : algebraMap (PolynomialRing P) (FunctionField P)
      (f.comp (Polynomial.X + 1)) =
    algebraMap (PolynomialRing P) (FunctionField P)
      (g.comp (Polynomial.X + 1)) := by
    rw [← functionFieldOnePlusYLaurentEvaluation_toLaurent P f,
      ← functionFieldOnePlusYLaurentEvaluation_toLaurent P g]
    simpa [functionFieldOnePlusYLaurentEvaluation,
      functionFieldOnePlusYUnit] using h
  have hcomp : f.comp (Polynomial.X + 1) =
      g.comp (Polynomial.X + 1) :=
    RatFunc.algebraMap_injective (BaseField P) hmap
  apply sub_eq_zero.mp
  apply (Polynomial.comp_X_add_C_eq_zero_iff
    (p := f - g) (t := (1 : BaseField P))).mp
  rw [Polynomial.sub_comp]
  have hcomp' : f.comp (Polynomial.X + Polynomial.C 1) =
      g.comp (Polynomial.X + Polynomial.C 1) := by
    simpa using hcomp
  rw [hcomp', sub_self]

theorem functionFieldOnePlusYLaurentEvaluation_injective
    (P : BasePrime) :
    Function.Injective (functionFieldOnePlusYLaurentEvaluation P) := by
  rw [functionFieldOnePlusYLaurentEvaluation]
  apply (IsLocalization.lift_injective_iff _).2
  intro f g
  rw [LaurentPolynomial.algebraMap_eq_toLaurent,
    LaurentPolynomial.algebraMap_eq_toLaurent,
    Polynomial.toLaurent_inj]
  simpa [functionFieldOnePlusYUnit] using
    (functionFieldOnePlusYPolynomialEvaluation_injective P).eq_iff.symm

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
