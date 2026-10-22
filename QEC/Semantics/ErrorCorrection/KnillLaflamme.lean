import QEC.Semantics.ErrorCorrection.CodeSupport
/-!
# Knill-Laflamme formulation bridge

This module connects the matrix-element condition with the code-projector
equation over the same semantic code carrier and error set.
-/

universe u

namespace QEC
namespace Semantics

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/-- Matrix-element Knill-Laflamme data with a fixed scalar function. -/
def KnillLaflammeMatrixConditionWithScalar
    (C : QuantumCode H) (errors : Set (Operator H))
    (scalar : Operator H → Operator H → Complex) : Prop :=
  ∀ ⦃E : Operator H⦄, E ∈ errors →
    ∀ ⦃F : Operator H⦄, F ∈ errors →
      ∀ x : H, x ∈ C.carrier →
        ∀ y : H, y ∈ C.carrier →
          inner Complex (E x) (F y) = scalar E F * inner Complex x y

/-- Projector-equation Knill-Laflamme data with a fixed scalar function. -/
def KnillLaflammeProjectorConditionWithScalar
    (C : QuantumCode H) (errors : Set (Operator H))
    (scalar : Operator H → Operator H → Complex) : Prop :=
  ∀ ⦃E : Operator H⦄, E ∈ errors →
    ∀ ⦃F : Operator H⦄, F ∈ errors →
      (C.projector.comp ((LinearMap.adjoint E).comp F)).comp C.projector =
        scalar E F • C.projector

/-- The projector-equation form of the Knill-Laflamme condition. -/
def KnillLaflammeProjectorEquation
    (C : QuantumCode H) (errors : Set (Operator H)) : Prop :=
  ∃ scalar : Operator H → Operator H → Complex,
    KnillLaflammeProjectorConditionWithScalar C errors scalar

namespace KnillLaflamme

theorem projectorConditionWithScalar_of_matrixConditionWithScalar
    {C : QuantumCode H} {errors : Set (Operator H)}
    {scalar : Operator H → Operator H → Complex}
    (h : KnillLaflammeMatrixConditionWithScalar C errors scalar) :
    KnillLaflammeProjectorConditionWithScalar C errors scalar := by
  intro E hE F hF
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
        (((C.projector.comp ((LinearMap.adjoint E).comp F)).comp C.projector) v)
        = inner Complex (C.projector w)
            (((LinearMap.adjoint E).comp F) (C.projector v)) := by
          have hAdj :=
            LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w
              (((LinearMap.adjoint E).comp F) (C.projector v))
          simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self] using hAdj
    _ = inner Complex (E (C.projector w)) (F (C.projector v)) := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) E (C.projector w)
              (F (C.projector v)))
    _ = scalar E F * inner Complex (C.projector w) (C.projector v) :=
          h hE hF (C.projector w) (C.projector_mem_carrier w)
            (C.projector v) (C.projector_mem_carrier v)
    _ = scalar E F * inner Complex w (C.projector v) := by
          rw [hinnerP]
    _ = inner Complex w ((scalar E F • C.projector) v) := by
          simp

theorem matrixConditionWithScalar_of_projectorConditionWithScalar
    {C : QuantumCode H} {errors : Set (Operator H)}
    {scalar : Operator H → Operator H → Complex}
    (h : KnillLaflammeProjectorConditionWithScalar C errors scalar) :
    KnillLaflammeMatrixConditionWithScalar C errors scalar := by
  intro E hE F hF x hx y hy
  have hxP : C.projector x = x := C.projector_eq_self_of_mem hx
  have hyP : C.projector y = y := C.projector_eq_self_of_mem hy
  have hInsert :
      inner Complex x ((LinearMap.adjoint E) (F y)) =
        inner Complex x
          (C.projector (((LinearMap.adjoint E).comp F) (C.projector y))) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector x
        (((LinearMap.adjoint E).comp F) (C.projector y))
    simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self, hxP, hyP] using
      hAdj.symm
  calc
    inner Complex (E x) (F y)
        = inner Complex x ((LinearMap.adjoint E) (F y)) := by
          simpa using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) E x (F y)).symm
    _ = inner Complex x
          (C.projector (((LinearMap.adjoint E).comp F) (C.projector y))) :=
          hInsert
    _ = inner Complex x ((scalar E F • C.projector) y) := by
          simpa [LinearMap.comp_apply, hyP] using
            congrArg (fun z : H => inner Complex x z)
              (congrArg (fun A : Operator H => A y) (h hE hF))
    _ = scalar E F * inner Complex x y := by
          simp [hyP]

/--
The matrix-element and projector-equation forms of the Knill-Laflamme
condition are equivalent over the same code carrier and error set.
-/
theorem criterion_iff_projectorEquation
    (C : QuantumCode H) (errors : Set (Operator H)) :
    KnillLaflammeCriterion H C errors ↔
      KnillLaflammeProjectorEquation C errors := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar, projectorConditionWithScalar_of_matrixConditionWithScalar hscalar⟩
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar, matrixConditionWithScalar_of_projectorConditionWithScalar hscalar⟩

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

/--
Transport the selected Knill-Laflamme matrix-element criterion across a unitary
equivalence of code carriers.
-/
theorem unitaryTransport
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D)
    (hKL : KnillLaflammeCriterion H C errors) :
    KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors) := by
  rcases hKL with ⟨scalar, hscalar⟩
  let scalarTransported : Operator K → Operator K → Complex :=
    fun E F =>
      scalar
        (U.toLinearEquiv.symm.toLinearMap.comp (E.comp U.toLinearEquiv.toLinearMap))
        (U.toLinearEquiv.symm.toLinearMap.comp (F.comp U.toLinearEquiv.toLinearMap))
  refine ⟨scalarTransported, ?_⟩
  intro E hE F hF x hx y hy
  rcases hE with ⟨E₀, hE₀, rfl⟩
  rcases hF with ⟨F₀, hF₀, rfl⟩
  let x₀ : H := U.toLinearEquiv.symm x
  let y₀ : H := U.toLinearEquiv.symm y
  have hx₀ : x₀ ∈ C.carrier := by
    have hxD : U.toLinearEquiv x₀ ∈ D.carrier := by
      simpa [x₀] using hx
    exact (hCD x₀).2 hxD
  have hy₀ : y₀ ∈ C.carrier := by
    have hyD : U.toLinearEquiv y₀ ∈ D.carrier := by
      simpa [y₀] using hy
    exact (hCD y₀).2 hyD
  have hScalarE :
      U.toLinearEquiv.symm.toLinearMap.comp
          ((U.conjOperator E₀).comp U.toLinearEquiv.toLinearMap) = E₀ := by
    ext z
    simp [UnitaryTransport.conjOperator]
  have hScalarF :
      U.toLinearEquiv.symm.toLinearMap.comp
          ((U.conjOperator F₀).comp U.toLinearEquiv.toLinearMap) = F₀ := by
    ext z
    simp [UnitaryTransport.conjOperator]
  have hxy : inner Complex x₀ y₀ = inner Complex x y := by
    simpa [x₀, y₀] using (U.map_inner x₀ y₀).symm
  calc
    inner Complex (U.conjOperator E₀ x) (U.conjOperator F₀ y)
        = inner Complex (U.toLinearEquiv (E₀ x₀)) (U.toLinearEquiv (F₀ y₀)) := by
          simp [UnitaryTransport.conjOperator, x₀, y₀]
    _ = inner Complex (E₀ x₀) (F₀ y₀) := U.map_inner (E₀ x₀) (F₀ y₀)
    _ = scalar E₀ F₀ * inner Complex x₀ y₀ := hscalar hE₀ hF₀ x₀ hx₀ y₀ hy₀
    _ = scalarTransported (U.conjOperator E₀) (U.conjOperator F₀) *
          inner Complex x y := by
        simp [scalarTransported, hScalarE, hScalarF, hxy]

/--
Pull the transported Knill-Laflamme criterion back along a unitary equivalence
of code carriers.
-/
theorem of_unitaryTransport
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D)
    (hKL : KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors)) :
    KnillLaflammeCriterion H C errors := by
  rcases hKL with ⟨scalar, hscalar⟩
  refine ⟨fun E F => scalar (U.conjOperator E) (U.conjOperator F), ?_⟩
  intro E hE F hF x hx y hy
  have hxD : U.toLinearEquiv x ∈ D.carrier := (hCD x).1 hx
  have hyD : U.toLinearEquiv y ∈ D.carrier := (hCD y).1 hy
  have hmatrix :=
    hscalar (E := U.conjOperator E)
      (Set.mem_image_of_mem (UnitaryTransport.conjOperator U) hE)
      (F := U.conjOperator F)
      (Set.mem_image_of_mem (UnitaryTransport.conjOperator U) hF)
      (U.toLinearEquiv x) hxD (U.toLinearEquiv y) hyD
  calc
    inner Complex (E x) (F y)
        = inner Complex (U.toLinearEquiv (E x)) (U.toLinearEquiv (F y)) := by
          simpa using (U.map_inner (E x) (F y)).symm
    _ = scalar (U.conjOperator E) (U.conjOperator F) * inner Complex x y := by
          simpa [UnitaryTransport.conjOperator, U.map_inner x y] using hmatrix

/--
The selected Knill-Laflamme matrix-element criterion is invariant under unitary
transport of the code and conjugation of the error family.
-/
theorem unitaryTransport_iff
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D) :
    KnillLaflammeCriterion H C errors ↔
      KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors) := by
  constructor
  · exact unitaryTransport U hCD
  · exact of_unitaryTransport U hCD

end KnillLaflamme

end

end Semantics
end QEC
