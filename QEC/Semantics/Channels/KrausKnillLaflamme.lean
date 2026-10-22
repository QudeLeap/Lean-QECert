import QEC.Semantics.Channels.Kraus
import QEC.Semantics.ErrorCorrection.KnillLaflamme
/-!
# Finite-Kraus Knill-Laflamme alignment

This module aligns the finite indexed same-space Kraus error model with the
selected Knill-Laflamme error-set and projector-equation APIs.
-/

universe u v

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteKrausFamily

variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/--
Indexed matrix-element Knill-Laflamme data for a same-space finite Kraus
family.
-/
def IndexedKnillLaflammeConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) : Prop :=
  ∀ i j : ι,
    ∀ x : H, x ∈ C.carrier →
      ∀ y : H, y ∈ C.carrier →
        inner Complex (E.operator i x) (E.operator j y) =
          scalar i j * inner Complex x y

/-- The indexed same-space Kraus form of the Knill-Laflamme criterion. -/
def IndexedKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) : Prop :=
  ∃ scalar : ι → ι → Complex,
    IndexedKnillLaflammeConditionWithScalar E C scalar

/-- The image of the code carrier under one Kraus operator. -/
def errorImageSubspace
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (i : ι) :
    Submodule Complex H :=
  C.carrier.map (E.operator i)

theorem mem_errorImageSubspace_iff
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (i : ι) (x : H) :
    x ∈ E.errorImageSubspace C i ↔
      ∃ y : H, y ∈ C.carrier ∧ E.operator i y = x := by
  rfl

/--
If an indexed KL scalar vanishes, the corresponding error-image subspaces are
orthogonal in the concrete inner-product sense needed by recovery construction.
-/
theorem errorImageSubspace_inner_eq_zero_of_indexedConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar)
    {i j : ι} (hzero : scalar i j = 0) :
    ∀ x : H, x ∈ E.errorImageSubspace C i →
      ∀ y : H, y ∈ E.errorImageSubspace C j →
        inner Complex x y = 0 := by
  intro x hx y hy
  rcases (E.mem_errorImageSubspace_iff C i x).1 hx with ⟨x₀, hx₀, hxmap⟩
  rcases (E.mem_errorImageSubspace_iff C j y).1 hy with ⟨y₀, hy₀, hymap⟩
  rw [← hxmap, ← hymap]
  calc
    inner Complex (E.operator i x₀) (E.operator j y₀)
        = scalar i j * inner Complex x₀ y₀ := h i j x₀ hx₀ y₀ hy₀
    _ = 0 := by rw [hzero, zero_mul]

/-- Indexed KL scalar data is preserved by indexed scalar branch weights. -/
theorem scale_indexedKnillLaflammeConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (amp : ι → Complex) {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    IndexedKnillLaflammeConditionWithScalar (E.scale amp) C
      (fun i j => star (amp i) * amp j * scalar i j) := by
  intro i j x hx y hy
  have hbase := h i j x hx y hy
  simp [FiniteKrausFamily.scale, hbase, mul_assoc, mul_left_comm, mul_comm]

/-- Indexed projector-equation KL data with a fixed scalar matrix. -/
def IndexedKnillLaflammeProjectorConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) : Prop :=
  ∀ i j : ι,
    (C.projector.comp ((LinearMap.adjoint (E.operator i)).comp (E.operator j))).comp
        C.projector =
      scalar i j • C.projector

/-- The indexed projector-equation form of finite-Kraus KL data. -/
def IndexedKnillLaflammeProjectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) : Prop :=
  ∃ scalar : ι → ι → Complex,
    IndexedKnillLaflammeProjectorConditionWithScalar E C scalar

theorem indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    IndexedKnillLaflammeProjectorConditionWithScalar E C scalar := by
  intro i j
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
    inner Complex w
        (((C.projector.comp ((LinearMap.adjoint (E.operator i)).comp
          (E.operator j))).comp C.projector) v)
        = inner Complex (C.projector w)
            (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
              (C.projector v)) := by
          have hAdj :=
            LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w
              (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
                (C.projector v))
          simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self] using hAdj
    _ = inner Complex (E.operator i (C.projector w))
          (E.operator j (C.projector v)) := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) (E.operator i)
              (C.projector w) (E.operator j (C.projector v)))
    _ = scalar i j * inner Complex (C.projector w) (C.projector v) :=
          h i j (C.projector w) (C.projector_mem_carrier w)
            (C.projector v) (C.projector_mem_carrier v)
    _ = scalar i j * inner Complex w (C.projector v) := by
          rw [hinnerP]
    _ = inner Complex w ((scalar i j • C.projector) v) := by
          simp

theorem indexedConditionWithScalar_of_indexedProjectorConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    IndexedKnillLaflammeConditionWithScalar E C scalar := by
  intro i j x hx y hy
  have hxP : C.projector x = x := C.projector_eq_self_of_mem hx
  have hyP : C.projector y = y := C.projector_eq_self_of_mem hy
  have hInsert :
      inner Complex x ((LinearMap.adjoint (E.operator i)) (E.operator j y)) =
        inner Complex x
          (C.projector (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
            (C.projector y))) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector x
        (((LinearMap.adjoint (E.operator i)).comp (E.operator j)) (C.projector y))
    simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self, hxP, hyP] using
      hAdj.symm
  calc
    inner Complex (E.operator i x) (E.operator j y)
        = inner Complex x ((LinearMap.adjoint (E.operator i)) (E.operator j y)) := by
          simpa using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) (E.operator i) x
              (E.operator j y)).symm
    _ = inner Complex x
          (C.projector (((LinearMap.adjoint (E.operator i)).comp (E.operator j))
            (C.projector y))) :=
          hInsert
    _ = inner Complex x ((scalar i j • C.projector) y) := by
          simpa [LinearMap.comp_apply, hyP] using
            congrArg (fun z : H => inner Complex x z)
              (congrArg (fun A : Operator H => A y) (h i j))
    _ = scalar i j * inner Complex x y := by
          simp [hyP]

theorem indexedConditionWithScalar_iff_indexedProjectorConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) :
    IndexedKnillLaflammeConditionWithScalar E C scalar ↔
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar := by
  constructor
  · exact indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
  · exact indexedConditionWithScalar_of_indexedProjectorConditionWithScalar

theorem indexedKnillLaflammeCriterion_iff_indexedProjectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔
      IndexedKnillLaflammeProjectorEquation E C := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar,
      indexedProjectorConditionWithScalar_of_indexedConditionWithScalar hscalar⟩
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar,
      indexedConditionWithScalar_of_indexedProjectorConditionWithScalar hscalar⟩

private noncomputable def sameSpaceScalar
    (E : FiniteKrausFamily ι H H) (scalar : ι → ι → Complex) :
    Operator H → Operator H → Complex := by
  classical
  exact fun A B =>
    if hA : A ∈ E.sameSpaceErrorSet then
      if hB : B ∈ E.sameSpaceErrorSet then
        scalar
          (Classical.choose ((E.mem_sameSpaceErrorSet_iff A).1 hA))
          (Classical.choose ((E.mem_sameSpaceErrorSet_iff B).1 hB))
      else 0
    else 0

theorem indexedConditionWithScalar_of_matrixConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : Operator H → Operator H → Complex}
    (h : KnillLaflammeMatrixConditionWithScalar C E.sameSpaceErrorSet scalar) :
    IndexedKnillLaflammeConditionWithScalar E C
      (fun i j => scalar (E.operator i) (E.operator j)) := by
  intro i j x hx y hy
  exact h (by exact ⟨i, rfl⟩) (by exact ⟨j, rfl⟩) x hx y hy

theorem matrixConditionWithScalar_of_indexedConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    KnillLaflammeMatrixConditionWithScalar C E.sameSpaceErrorSet
      (sameSpaceScalar E scalar) := by
  classical
  intro A hA B hB x hx y hy
  let i : ι := Classical.choose ((E.mem_sameSpaceErrorSet_iff A).1 hA)
  let j : ι := Classical.choose ((E.mem_sameSpaceErrorSet_iff B).1 hB)
  have hAi : E.operator i = A := by
    dsimp [i]
    exact Classical.choose_spec ((E.mem_sameSpaceErrorSet_iff A).1 hA)
  have hBj : E.operator j = B := by
    dsimp [j]
    exact Classical.choose_spec ((E.mem_sameSpaceErrorSet_iff B).1 hB)
  have hscalar : sameSpaceScalar E scalar A B = scalar i j := by
    simp [sameSpaceScalar, hA, hB, i, j]
  calc
    inner Complex (A x) (B y)
        = inner Complex (E.operator i x) (E.operator j y) := by
          rw [← hAi, ← hBj]
    _ = scalar i j * inner Complex x y := h i j x hx y hy
    _ = sameSpaceScalar E scalar A B * inner Complex x y := by
          rw [hscalar]

/--
The indexed same-space finite-Kraus KL criterion is equivalent to the existing
error-set criterion over `E.sameSpaceErrorSet`.
-/
theorem indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔ E.sameSpaceKnillLaflammeCriterion C := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    exact ⟨sameSpaceScalar E scalar,
      matrixConditionWithScalar_of_indexedConditionWithScalar hscalar⟩
  · rintro ⟨scalar, hscalar⟩
    exact ⟨fun i j => scalar (E.operator i) (E.operator j),
      indexedConditionWithScalar_of_matrixConditionWithScalar hscalar⟩

/--
The same-space finite-Kraus KL criterion is equivalent to an indexed scalar
condition over the original Kraus family. Duplicate operators are handled by
choosing representatives from `E.sameSpaceErrorSet`, not by assuming
injectivity of `E.operator`.
-/
theorem sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      ∃ scalar : ι → ι → Complex,
        ∀ i j : ι,
          ∀ x : H, x ∈ C.carrier →
            ∀ y : H, y ∈ C.carrier →
              inner Complex (E.operator i x) (E.operator j y) =
                scalar i j * inner Complex x y :=
  (indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion E C).symm

/-- Same-space KL data is preserved by indexed scalar branch weights. -/
theorem scale_sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (amp : ι → Complex)
    (h : E.sameSpaceKnillLaflammeCriterion C) :
    (E.scale amp).sameSpaceKnillLaflammeCriterion C := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).1 h with
    ⟨scalar, hscalar⟩
  exact
    ((E.scale amp).sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).2
      ⟨fun i j => star (amp i) * amp j * scalar i j,
        scale_indexedKnillLaflammeConditionWithScalar E C amp hscalar⟩

/--
The same-space finite-Kraus KL criterion is equivalent to projector equations
with scalars indexed by the original Kraus family.
-/
theorem sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      IndexedKnillLaflammeProjectorEquation E C := by
  rw [← indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion]
  exact indexedKnillLaflammeCriterion_iff_indexedProjectorEquation E C

/--
The same-space finite-Kraus KL criterion matches the projector-equation form
over the same finite-Kraus error set.
-/
theorem sameSpaceKnillLaflammeCriterion_iff_projectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      KnillLaflammeProjectorEquation C E.sameSpaceErrorSet :=
  KnillLaflamme.criterion_iff_projectorEquation C E.sameSpaceErrorSet

/--
The indexed finite-Kraus KL criterion matches the projector-equation form over
the same finite-Kraus error set.
-/
theorem indexedKnillLaflammeCriterion_iff_projectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔
      KnillLaflammeProjectorEquation C E.sameSpaceErrorSet := by
  rw [indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion]
  exact sameSpaceKnillLaflammeCriterion_iff_projectorEquation E C

end FiniteKrausFamily

end

end Semantics
end QEC
