import QEC.Semantics.Core.Definitions
/-!
# CPTP positivity consequences

Complete positivity implies ordinary positivity by applying the matrix
amplification definition to a one-by-one block matrix.
-/

universe u

namespace QEC
namespace Semantics

open scoped TensorProduct

namespace OperatorMatrix

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- The one-by-one block matrix whose only entry is `A`. -/
def oneByOne (A : Operator H) : OperatorMatrix 1 H :=
  fun _ _ => A

@[simp]
theorem oneByOne_apply (A : Operator H) (i j : Fin 1) :
    oneByOne A i j = A :=
  rfl

/--
The project block-positivity predicate agrees with `LinearMap.IsPositive` on
one-by-one operator matrices.
-/
theorem oneByOne_isPositive_iff (A : Operator H) :
    IsPositive (oneByOne A) ↔ LinearMap.IsPositive A := by
  constructor
  · intro hM
    constructor
    · have hAdj : A = LinearMap.adjoint A := by
        simpa [oneByOne] using hM.1 0 0
      intro x y
      calc
        inner Complex (A x) y = inner Complex ((LinearMap.adjoint A) x) y := by
          exact congrArg (fun T : Operator H => inner Complex (T x) y) hAdj
        _ = inner Complex x (A y) := by
          simpa using (LinearMap.adjoint_inner_left (𝕜 := Complex) A y x)
    · intro x
      simpa [oneByOne] using hM.2 (fun _ : Fin 1 => x)
  · intro hA
    constructor
    · intro i j
      fin_cases i
      fin_cases j
      simpa [oneByOne] using hA.1.adjoint_eq.symm
    · intro x
      simpa [oneByOne] using hA.2 (x 0)

end OperatorMatrix

namespace CompletelyPositive

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- A completely positive operator-space map is positive. -/
theorem map_positive {Φ : Operator H →ₗ[Complex] Operator K}
    (hΦ : CompletelyPositive Φ) {A : Operator H}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (Φ A) := by
  have hBlock :
      OperatorMatrix.IsPositive
        (OperatorMatrix.map Φ (OperatorMatrix.oneByOne A)) :=
    hΦ 1 (OperatorMatrix.oneByOne A)
      ((OperatorMatrix.oneByOne_isPositive_iff A).2 hA)
  have hmap : OperatorMatrix.map Φ (OperatorMatrix.oneByOne A) =
      OperatorMatrix.oneByOne (Φ A) := by
    ext i j
    rfl
  rw [hmap] at hBlock
  exact (OperatorMatrix.oneByOne_isPositive_iff (Φ A)).1 hBlock

end CompletelyPositive

namespace UnitaryTransport

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- Unitary conjugation as a linear operator-space map. -/
noncomputable def conjOperatorLinearMap (U : UnitaryTransport H K) :
    Operator H →ₗ[Complex] Operator K where
  toFun := U.conjOperator
  map_add' := by
    intro A B
    ext x
    simp [UnitaryTransport.conjOperator]
  map_smul' := by
    intro c A
    ext x
    simp [UnitaryTransport.conjOperator]

@[simp]
theorem conjOperatorLinearMap_apply (U : UnitaryTransport H K) (A : Operator H) :
    U.conjOperatorLinearMap A = U.conjOperator A :=
  rfl

@[simp]
theorem inner_conjOperator (U : UnitaryTransport H K) (A : Operator H) (x y : K) :
    inner Complex ((U.conjOperator A) x) y =
      inner Complex (A (U.toLinearEquiv.symm x)) (U.toLinearEquiv.symm y) := by
  rw [UnitaryTransport.conjOperator_apply]
  nth_rewrite 1 [← U.toLinearEquiv.apply_symm_apply y]
  exact U.map_inner (A (U.toLinearEquiv.symm x)) (U.toLinearEquiv.symm y)

/--
Unitary conjugation is completely positive.

The block-positivity proof pulls each test vector back along `U.symm`, so the
argument works for every matrix amplification size rather than only for
ordinary positivity.
-/
theorem completelyPositive_conjOperator (U : UnitaryTransport H K) :
    CompletelyPositive U.conjOperatorLinearMap := by
  intro n M hM
  constructor
  · intro i j
    change U.conjOperator (M j i) = LinearMap.adjoint (U.conjOperator (M i j))
    rw [hM.1 i j, UnitaryTransport.conjOperator_adjoint]
  · intro x
    have hPullback := hM.2 (fun i : Fin n => U.toLinearEquiv.symm (x i))
    simpa only [OperatorMatrix.map, conjOperatorLinearMap_apply, inner_conjOperator] using hPullback

end UnitaryTransport

namespace QuantumChannel

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- A quantum channel maps positive operators to positive operators. -/
theorem map_positive (Φ : QuantumChannel H K) {A : Operator H}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (Φ A) :=
  Φ.completely_positive.map_positive hA

/-- Apply a quantum channel to a density operator. -/
noncomputable def mapDensity (Φ : QuantumChannel H K)
    (rho : DensityOperator H) : DensityOperator K where
  toOperator := Φ rho.toOperator
  positive := Φ.map_positive rho.positive
  trace_one := by
    rw [Φ.trace_map, rho.trace_one]

@[simp]
theorem mapDensity_toOperator (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    (Φ.mapDensity rho).toOperator = Φ rho.toOperator :=
  rfl

theorem mapDensity_positive (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    LinearMap.IsPositive (Φ.mapDensity rho).toOperator :=
  (Φ.mapDensity rho).positive

theorem mapDensity_trace (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (Φ.mapDensity rho).toOperator = 1 :=
  (Φ.mapDensity rho).trace_one

/-- Unitary conjugation as a quantum channel. -/
noncomputable def unitaryConj (U : UnitaryTransport H K) : QuantumChannel H K where
  toLinearMap := U.conjOperatorLinearMap
  completely_positive := U.completelyPositive_conjOperator
  trace_preserving := by
    intro A
    simpa [UnitaryTransport.conjOperatorLinearMap_apply] using
      (UnitaryTransport.trace_conjOperator U A)

@[simp]
theorem unitaryConj_apply (U : UnitaryTransport H K) (A : Operator H) :
    (unitaryConj U) A = U.conjOperator A :=
  rfl

/-- The identity operator map as a quantum channel. -/
noncomputable def id (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : QuantumChannel H H where
  toLinearMap := LinearMap.id
  completely_positive := by
    intro n M hM
    have hmap : OperatorMatrix.map (LinearMap.id : Operator H →ₗ[Complex] Operator H) M =
        M := by
      ext i j
      rfl
    rw [hmap]
    exact hM
  trace_preserving := by
    intro A
    rfl

@[simp]
theorem id_apply (A : Operator H) : (id H) A = A :=
  rfl

/-- Composition of quantum channels is a quantum channel. -/
noncomputable def comp {L : Type u} [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) :
    QuantumChannel H L where
  toLinearMap := Ψ.toLinearMap.comp Φ.toLinearMap
  completely_positive := by
    intro n M hM
    exact Ψ.completely_positive n (OperatorMatrix.map Φ.toLinearMap M)
      (Φ.completely_positive n M hM)
  trace_preserving := by
    intro A
    calc
      LinearMap.trace Complex L ((Ψ.toLinearMap.comp Φ.toLinearMap) A)
          = LinearMap.trace Complex K (Φ.toLinearMap A) := Ψ.trace_map (Φ.toLinearMap A)
      _ = LinearMap.trace Complex H A := Φ.trace_map A

@[simp]
theorem comp_apply {L : Type u} [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K)
    (A : Operator H) : (comp Ψ Φ) A = Ψ (Φ A) :=
  rfl

end QuantumChannel

namespace Correctable

variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]

theorem unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K}
    {recovery : QuantumChannel K H}
    (h : Correctable H K C noise recovery) :
    Correctable Ht Kt (C.transport U)
      (QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
      (QuantumChannel.comp (QuantumChannel.unitaryConj U)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm))) := by
  intro rho hρ
  let rho₀ : DensityOperator H := U.symm.conjDensity rho
  have hρ₀ : DensityOperator.SupportedOn C rho₀ := by
    exact (DensityOperator.supportedOn_symm_conjDensity_transport_iff U C rho).2 hρ
  have hcorr := h rho₀ hρ₀
  have hcorr' : recovery (noise (U.symm.conjOperator rho.toOperator)) =
      U.symm.conjOperator rho.toOperator := by
    simpa [rho₀] using hcorr
  change U.conjOperator
      (recovery (V.symm.conjOperator
        (V.conjOperator (noise (U.symm.conjOperator rho.toOperator))))) =
    rho.toOperator
  rw [UnitaryTransport.symm_conjOperator_conjOperator]
  rw [hcorr']
  rw [UnitaryTransport.conjOperator_symm_conjOperator]

theorem of_unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K}
    {recovery : QuantumChannel Kt Ht}
    (h : Correctable Ht Kt (C.transport U)
      (QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
      recovery) :
    Correctable H K C noise
      (QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V))) := by
  intro rho hρ
  let rhoT : DensityOperator Ht := U.conjDensity rho
  have hρT : DensityOperator.SupportedOn (C.transport U) rhoT := by
    exact DensityOperator.supportedOn_conjDensity_transport U C rho hρ
  have hcorr := h rhoT hρT
  have hcorr' : recovery (V.conjOperator (noise rho.toOperator)) =
      U.conjOperator rho.toOperator := by
    simpa [rhoT] using hcorr
  change U.symm.conjOperator (recovery (V.conjOperator (noise rho.toOperator))) =
    rho.toOperator
  rw [hcorr']
  rw [UnitaryTransport.symm_conjOperator_conjOperator]

theorem exists_unitaryTransport_iff
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : QuantumChannel H K} :
    (∃ recovery : QuantumChannel Kt Ht,
      Correctable Ht Kt (C.transport U)
        (QuantumChannel.comp (QuantumChannel.unitaryConj V)
          (QuantumChannel.comp noise (QuantumChannel.unitaryConj U.symm)))
        recovery) ↔
    (∃ recovery : QuantumChannel K H, Correctable H K C noise recovery) := by
  constructor
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V)),
      of_unitaryTransport U V h⟩
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm)),
      unitaryTransport U V h⟩

end Correctable

/-- The raw right partial trace packaged as a completely positive trace-preserving channel. -/
noncomputable def partialTraceRightRaw_cptp (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    QuantumChannel (CompositeSystem H K) H where
  toLinearMap := partialTraceRightRaw H K
  completely_positive := partialTraceRightRaw_completely_positive H K
  trace_preserving := partialTraceRightRaw_trace_preserving H K

@[simp]
theorem partialTraceRightRaw_cptp_toLinearMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (partialTraceRightRaw_cptp H K).toLinearMap = partialTraceRightRaw H K :=
  rfl

/-- The raw right partial trace maps composite-system density operators to density operators. -/
noncomputable def partialTraceRightRaw_mapDensity (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator (CompositeSystem H K)) : DensityOperator H :=
  (partialTraceRightRaw_cptp H K).mapDensity rho

@[simp]
theorem partialTraceRightRaw_mapDensity_toOperator (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator (CompositeSystem H K)) :
    (partialTraceRightRaw_mapDensity H K rho).toOperator =
      (partialTraceRightRaw H K) rho.toOperator :=
  rfl

end Semantics
end QEC
