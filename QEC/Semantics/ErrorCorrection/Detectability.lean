import QEC.Semantics.ErrorCorrection.CodeSupport
/-!
# Semantic error detectability

This module defines detectability by code-carrier matrix elements and proves
its equivalence with compression by the semantic quantum-code projector.
-/

universe u

namespace QEC
namespace Semantics

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/-- Matrix-element detectability on a code carrier with a fixed scalar. -/
def DetectableOnWithScalar
    (C : QuantumCode H) (E : Operator H) (c : Complex) : Prop :=
  ∀ x : H, x ∈ C.carrier →
    ∀ y : H, y ∈ C.carrier →
      inner Complex x (E y) = c * inner Complex x y

/-- An operator is detectable on a code when one scalar controls all carrier matrix elements. -/
def DetectableOn (C : QuantumCode H) (E : Operator H) : Prop :=
  ∃ c : Complex, DetectableOnWithScalar C E c

theorem projectorEquation_of_detectableOnWithScalar
    {C : QuantumCode H} {E : Operator H} {c : Complex}
    (h : DetectableOnWithScalar C E c) :
    (C.projector.comp E).comp C.projector = c • C.projector := by
  ext v
  apply ext_inner_left Complex
  intro w
  have hinnerP :
      inner Complex (C.projector w) (C.projector v) =
        inner Complex w (C.projector v) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w (C.projector v)
    have hIdemV : C.projector (C.projector v) = C.projector v := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun A : Operator H => A v) C.projector_idempotent
    simpa [C.projector_adjoint_eq_self, hIdemV] using hAdj.symm
  calc
    inner Complex w (((C.projector.comp E).comp C.projector) v) =
        inner Complex (C.projector w) (E (C.projector v)) := by
          have hAdj :=
            LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w
              (E (C.projector v))
          simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self] using hAdj
    _ = c * inner Complex (C.projector w) (C.projector v) :=
      h (C.projector w) (C.projector_mem_carrier w)
        (C.projector v) (C.projector_mem_carrier v)
    _ = c * inner Complex w (C.projector v) := by rw [hinnerP]
    _ = inner Complex w ((c • C.projector) v) := by simp

theorem detectableOnWithScalar_of_projectorEquation
    {C : QuantumCode H} {E : Operator H} {c : Complex}
    (h : (C.projector.comp E).comp C.projector = c • C.projector) :
    DetectableOnWithScalar C E c := by
  intro x hx y hy
  have hxP : C.projector x = x := C.projector_eq_self_of_mem hx
  have hyP : C.projector y = y := C.projector_eq_self_of_mem hy
  have hInsert :
      inner Complex x (E y) =
        inner Complex x (C.projector (E (C.projector y))) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector x
        (E (C.projector y))
    simpa [C.projector_adjoint_eq_self, hxP, hyP] using hAdj.symm
  calc
    inner Complex x (E y) =
        inner Complex x (C.projector (E (C.projector y))) := hInsert
    _ = inner Complex x ((c • C.projector) y) := by
      simpa [LinearMap.comp_apply, hyP] using
        congrArg (fun z : H => inner Complex x z)
          (congrArg (fun A : Operator H => A y) h)
    _ = c * inner Complex x y := by simp [hyP]

/-- Fixed-scalar matrix-element detectability is exactly projector compression. -/
theorem detectableOnWithScalar_iff_projectorEquation
    (C : QuantumCode H) (E : Operator H) (c : Complex) :
    DetectableOnWithScalar C E c ↔
      (C.projector.comp E).comp C.projector = c • C.projector := by
  constructor
  · exact projectorEquation_of_detectableOnWithScalar
  · exact detectableOnWithScalar_of_projectorEquation

/-- Semantic detectability is equivalent to a scalar projector-compression equation. -/
theorem detectableOn_iff_projectorEquation
    (C : QuantumCode H) (E : Operator H) :
    DetectableOn C E ↔
      ∃ c : Complex, (C.projector.comp E).comp C.projector = c • C.projector := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, projectorEquation_of_detectableOnWithScalar hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, detectableOnWithScalar_of_projectorEquation hc⟩

end

end Semantics
end QEC
