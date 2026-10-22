import QEC.Coding.AlgebraicGeometry.Codes.NormalClosureShortening
import QEC.Distillation.MultiplicativeQuditProtocol.CSSShortening

/-!
# Concrete normal-closure inputs for multiplicative CSS shortening

The input is constructed from actual evaluation codes, proved pivot
surjectivity, the constant function, and the global residue pairing.
No code parameter or multiplication property is supplied as a hypothesis.
This module stops at the classical input boundary of [Ngu24, Lemma: Qudit
code with transversal low-degree phase gates].
-/

noncomputable section

namespace QEC.Distillation.Ngu24MultiplicativeCSS

open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- The complete, proved input to the existing source CSS constructor. -/
def f256SourceInput (i : ℕ) : SourceInput F256 (Fin (f256GarciaStichtenothLength i))
    (Fin (f256MultiplicationLogicalCount i)) where
  code := f256MultiplicationCode i
  pivotEmbedding := f256MultiplicationPivot i
  pivotRestrict_surjective := by
    intro u
    obtain ⟨f, hf⟩ := f256MultiplicationPivot_evaluation_surjective i u
    refine ⟨⟨agEvaluationLinearMap (f256MultiplicationDivisor i)
      (f256GarciaStichtenothSelectedRationalPlace i)
      (f256MultiplicationDivisor_selected_eq_zero i) f, ⟨f, rfl⟩⟩, hf⟩
  one_mem_code := f256MultiplicationCode_one_mem i
  starSquare_le_dual := f256MultiplicationCode_starSquare_le_dual i

/-- The constructor's shortened image is the concrete subtracted-divisor AG code. -/
theorem f256SourceInput_shortenedCode_eq (i : ℕ) :
    (f256SourceInput i).shortenedCode = (f256ShortenedMultiplicationCode i).carrier := by
  ext w
  refine Iff.trans ?_ (f256ShortenedMultiplicationCode_mem_iff i w).symm
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, x.property, ?_, rfl⟩
    intro a
    exact congrFun (LinearMap.mem_ker.mp hx) a
  · rintro ⟨x, hx, hzero, hword⟩
    exact ⟨⟨x, hx⟩, LinearMap.mem_ker.mpr (funext hzero), hword⟩

/-- Puncturing the entire actual code gives the retained-place evaluation code. -/
theorem f256SourceInput_puncturedCode_eq (i : ℕ) :
    (f256SourceInput i).code.carrier.map (f256SourceInput i).puncture =
      (f256PuncturedMultiplicationCode i).carrier := by
  ext w
  refine Iff.trans ?_ (f256PuncturedMultiplicationCode_mem_iff i w).symm
  rfl

theorem f256SourceInput_shortened_dimension (i : ℕ) :
    Module.finrank F256 (f256SourceInput i).shortenedCode + f256MultiplicationLogicalCount i =
      Dimension (f256MultiplicationCode i) := by
  rw [f256SourceInput_shortenedCode_eq]
  exact f256ShortenedMultiplicationCode_dimension_eq i

end QEC.Distillation.Ngu24MultiplicativeCSS

end
