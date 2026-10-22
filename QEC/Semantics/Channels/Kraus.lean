import QEC.Semantics.Channels.Core
/-!
# Finite Kraus error models

This module supplies finite Kraus noise used by the M2 correctability topology.
The family stores only its operators; completeness upgrades the raw
operator-sum map to a `QuantumChannel` by theorem, not by a bundled field.
-/

universe u v

namespace QEC
namespace Semantics

open scoped BigOperators

noncomputable section

/-- A linear Kraus/error operator from an input system `H` to an output system `K`. -/
abbrev KrausOperator (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Type u :=
  H →ₗ[Complex] K

/--
A finite indexed Kraus/error family.

The structure stores only the operators. Completeness, raw induced map, and
correctability are separate definitions below so later CPTP lemmas must prove
their conclusions from the operator family rather than projecting a bundled
channel witness.
-/
structure FiniteKrausFamily (ι : Type v) [Fintype ι] (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  operator : ι → KrausOperator H K

section TracePairing

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- Operators are separated by right trace pairings against all test operators. -/
theorem operator_ext_of_trace_comp_right_eq {S T : Operator H}
    (htrace : ∀ A : Operator H,
      LinearMap.trace Complex H (A.comp S) = LinearMap.trace Complex H (A.comp T)) :
    S = T := by
  classical
  let b := Module.Free.chooseBasis Complex H
  apply (LinearMap.toMatrix b b).injective
  apply (Matrix.ext_iff_trace_mul_left).2
  intro X
  let A : Operator H := Matrix.toLin b b X
  have hA := htrace A
  rw [LinearMap.trace_eq_matrix_trace Complex b, LinearMap.trace_eq_matrix_trace Complex b] at hA
  rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b] at hA
  simpa [A] using hA

end TracePairing

namespace FiniteKrausFamily

variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/--
Kraus completeness on the input space: `sum_i E_i^† E_i = 1`.

This is only the finite-family completeness condition. It is not a CPTP field
and does not bundle the induced map as a `QuantumChannel`.
-/
def Complete (E : FiniteKrausFamily ι H K) : Prop :=
  ∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i) = 1

/-- Scale every branch in a finite Kraus family by an indexed amplitude. -/
noncomputable def scale (E : FiniteKrausFamily ι H K) (amp : ι → Complex) :
    FiniteKrausFamily ι H K where
  operator i := amp i • E.operator i

@[simp]
theorem scale_operator (E : FiniteKrausFamily ι H K) (amp : ι → Complex) (i : ι) :
    (E.scale amp).operator i = amp i • E.operator i :=
  rfl

/--
Completeness of a scaled finite Kraus family from the corresponding weighted
adjoint-square sum.
-/
theorem scale_complete_of_adjoint_square_sum
    (E : FiniteKrausFamily ι H K) (amp : ι → Complex)
    (h : ∑ i : ι, (star (amp i) * amp i) •
          ((LinearMap.adjoint (E.operator i)).comp (E.operator i)) = 1) :
    (E.scale amp).Complete := by
  classical
  unfold Complete scale
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _hi
  have hAdj :
      LinearMap.adjoint (amp i • E.operator i) =
        star (amp i) • LinearMap.adjoint (E.operator i) := by
    exact
      map_smulₛₗ
        (LinearMap.adjoint : (H →ₗ[Complex] K) ≃ₗ⋆[Complex] (K →ₗ[Complex] H))
        (amp i) (E.operator i)
  rw [hAdj]
  ext x
  simp [LinearMap.comp_apply, smul_smul, mul_comm]

/-- The raw operator-sum map induced by a finite Kraus family. -/
def inducedMap (E : FiniteKrausFamily ι H K) :
    Operator H →ₗ[Complex] Operator K where
  toFun A := ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i)))
  map_add' := by
    intro A B
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    ext x
    simp [Finset.smul_sum]

@[simp]
theorem inducedMap_apply (E : FiniteKrausFamily ι H K) (A : Operator H) :
    E.inducedMap A =
      ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))) :=
  rfl

/-- The raw operator-sum map induced by a finite Kraus family is completely positive. -/
theorem inducedMap_completelyPositive (E : FiniteKrausFamily ι H K) :
    CompletelyPositive E.inducedMap := by
  classical
  intro n M hM
  constructor
  · intro i j
    ext x
    simp [OperatorMatrix.map, inducedMap_apply, hM.1 i j, LinearMap.adjoint_comp]
  · intro x
    have hQuadratic :
        Complex.re (∑ i : Fin n, ∑ j : Fin n,
          inner Complex ((OperatorMatrix.map E.inducedMap M) i j (x j)) (x i)) =
        ∑ a : ι, Complex.re
          (∑ i : Fin n, ∑ j : Fin n,
            inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
              ((LinearMap.adjoint (E.operator a)) (x i))) := by
      calc
        Complex.re (∑ i : Fin n, ∑ j : Fin n,
            inner Complex ((OperatorMatrix.map E.inducedMap M) i j (x j)) (x i))
            = Complex.re (∑ i : Fin n, ∑ j : Fin n, ∑ a : ι,
                inner Complex ((E.operator a)
                  (M i j ((LinearMap.adjoint (E.operator a)) (x j)))) (x i)) := by
              simp only [OperatorMatrix.map, inducedMap_apply, LinearMap.sum_apply,
                LinearMap.comp_apply, sum_inner]
        _ = Complex.re (∑ i : Fin n, ∑ j : Fin n, ∑ a : ι,
                inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                  ((LinearMap.adjoint (E.operator a)) (x i))) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro a _ha
              exact (LinearMap.adjoint_inner_right (𝕜 := Complex) (E.operator a)
                (M i j ((LinearMap.adjoint (E.operator a)) (x j))) (x i)).symm
        _ = Complex.re (∑ a : ι, ∑ i : Fin n, ∑ j : Fin n,
                inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                  ((LinearMap.adjoint (E.operator a)) (x i))) := by
              congr 1
              calc
                (∑ i : Fin n, ∑ j : Fin n, ∑ a : ι,
                  inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                    ((LinearMap.adjoint (E.operator a)) (x i)))
                    = ∑ i : Fin n, ∑ a : ι, ∑ j : Fin n,
                  inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                    ((LinearMap.adjoint (E.operator a)) (x i)) := by
                      apply Finset.sum_congr rfl
                      intro i _hi
                      rw [Finset.sum_comm]
                _ = ∑ a : ι, ∑ i : Fin n, ∑ j : Fin n,
                  inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
                    ((LinearMap.adjoint (E.operator a)) (x i)) := by
                      rw [Finset.sum_comm]
        _ = ∑ a : ι, Complex.re
          (∑ i : Fin n, ∑ j : Fin n,
            inner Complex (M i j ((LinearMap.adjoint (E.operator a)) (x j)))
              ((LinearMap.adjoint (E.operator a)) (x i))) := by
              rw [Complex.re_sum]
    rw [hQuadratic]
    exact Finset.sum_nonneg (by
      intro a _ha
      exact hM.2 (fun i : Fin n => (LinearMap.adjoint (E.operator a)) (x i)))

/--
The trace of the induced map pairs the input operator with the Kraus
completeness sum.
-/
theorem inducedMap_trace_eq_trace_comp_completeSum (E : FiniteKrausFamily ι H K)
    (A : Operator H) :
    LinearMap.trace Complex K (E.inducedMap A) =
      LinearMap.trace Complex H
        (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
  classical
  unfold inducedMap
  calc
    LinearMap.trace Complex K
        (∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))))
        = ∑ i : ι, LinearMap.trace Complex K
            ((E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i)))) := by
          rw [map_sum]
    _ = ∑ i : ι, LinearMap.trace Complex H
            (A.comp ((LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simpa [LinearMap.comp_assoc] using
            (LinearMap.trace_comp_cycle
              (R := Complex) (M := H) (N := H) (P := K)
              (f := A) (g := E.operator i) (h := LinearMap.adjoint (E.operator i)))
    _ = LinearMap.trace Complex H
        (∑ i : ι, A.comp ((LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
          rw [map_sum]
    _ = LinearMap.trace Complex H
        (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))) := by
          congr 1
          ext x
          simp [Finset.sum_apply]

/-- Completeness makes the finite Kraus operator-sum map trace preserving. -/
theorem inducedMap_trace_preserving (E : FiniteKrausFamily ι H K)
    (hE : E.Complete) (A : Operator H) :
    LinearMap.trace Complex K (E.inducedMap A) = LinearMap.trace Complex H A := by
  classical
  calc
    LinearMap.trace Complex K (E.inducedMap A)
        = LinearMap.trace Complex H
            (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))) :=
          E.inducedMap_trace_eq_trace_comp_completeSum A
    _ = LinearMap.trace Complex H A := by
          rw [hE]
          rfl

/-- Trace preservation of the induced operator-sum map forces Kraus completeness. -/
theorem complete_of_inducedMap_trace_preserving (E : FiniteKrausFamily ι H K)
    (htrace : ∀ A : Operator H,
      LinearMap.trace Complex K (E.inducedMap A) = LinearMap.trace Complex H A) :
    E.Complete := by
  classical
  unfold Complete
  apply operator_ext_of_trace_comp_right_eq
  intro A
  calc
    LinearMap.trace Complex H
        (A.comp (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i)))
        = LinearMap.trace Complex K (E.inducedMap A) := by
          rw [E.inducedMap_trace_eq_trace_comp_completeSum]
    _ = LinearMap.trace Complex H A := htrace A
    _ = LinearMap.trace Complex H (A.comp (1 : Operator H)) := rfl

/-- A complete finite Kraus family defines a completely positive trace-preserving channel. -/
noncomputable def toQuantumChannel (E : FiniteKrausFamily ι H K) (hE : E.Complete) :
    QuantumChannel H K where
  toLinearMap := E.inducedMap
  completely_positive := E.inducedMap_completelyPositive
  trace_preserving := E.inducedMap_trace_preserving hE

@[simp]
theorem toQuantumChannel_toLinearMap (E : FiniteKrausFamily ι H K) (hE : E.Complete) :
    (E.toQuantumChannel hE).toLinearMap = E.inducedMap :=
  rfl

@[simp]
theorem toQuantumChannel_apply (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (A : Operator H) :
    (E.toQuantumChannel hE) A = E.inducedMap A :=
  rfl

theorem toQuantumChannel_apply_sum (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (A : Operator H) :
    (E.toQuantumChannel hE) A =
      ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))) := by
  rw [toQuantumChannel_apply, inducedMap_apply]

/-- Transport a finite Kraus family by unitary conjugation on input and output spaces. -/
noncomputable def unitaryTransport (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) :
    FiniteKrausFamily ι Ht Kt where
  operator i := V.toLinearEquiv.toLinearMap.comp
    ((E.operator i).comp U.toLinearEquiv.symm.toLinearMap)

@[simp]
theorem unitaryTransport_operator (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (i : ι) :
    (E.unitaryTransport U V).operator i =
      V.toLinearEquiv.toLinearMap.comp
        ((E.operator i).comp U.toLinearEquiv.symm.toLinearMap) :=
  rfl

theorem unitaryTransport_complete (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (hE : E.Complete) :
    (E.unitaryTransport U V).Complete := by
  classical
  unfold Complete unitaryTransport
  ext x
  have hEx := congrArg (fun A : Operator H => A (U.toLinearEquiv.symm x)) hE
  have hEx' :
      (∑ i : ι, (LinearMap.adjoint (E.operator i))
        ((E.operator i) (U.toLinearEquiv.symm x))) = U.toLinearEquiv.symm x := by
    simpa [Finset.sum_apply, LinearMap.comp_apply] using hEx
  simp [U.adjoint_symm_toLinearMap, V.adjoint_toLinearMap]
  calc
    ∑ i : ι, U.toLinearEquiv
        ((LinearMap.adjoint (E.operator i))
          ((E.operator i) (U.toLinearEquiv.symm x))) =
        U.toLinearEquiv (∑ i : ι,
          (LinearMap.adjoint (E.operator i))
            ((E.operator i) (U.toLinearEquiv.symm x))) := by
          simp
    _ = x := by
          rw [hEx']
          simp

theorem unitaryTransport_inducedMap_apply (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (A : Operator Ht) :
    (E.unitaryTransport U V).inducedMap A =
      V.conjOperator (E.inducedMap (U.symm.conjOperator A)) := by
  ext x
  simp [unitaryTransport, inducedMap_apply, UnitaryTransport.conjOperator,
    UnitaryTransport.symm, U.adjoint_symm_toLinearMap, V.adjoint_toLinearMap,
    Finset.sum_apply]

@[simp]
theorem unitaryTransport_symm_operator (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (i : ι) :
    ((E.unitaryTransport U V).unitaryTransport U.symm V.symm).operator i =
      E.operator i := by
  ext x
  simp [unitaryTransport, UnitaryTransport.symm]

theorem of_unitaryTransport_complete (E : FiniteKrausFamily ι H K)
    {Ht Kt : Type u}
    [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
    [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    (hE : (E.unitaryTransport U V).Complete) :
    E.Complete := by
  have hback := (E.unitaryTransport U V).unitaryTransport_complete U.symm V.symm hE
  simpa only [Complete, unitaryTransport_symm_operator] using hback

/--
The same-space error set associated to a finite Kraus family.

This is the bridge shape expected by `KnillLaflammeCriterion`, which consumes a
`Set (Operator H)`.
-/
def sameSpaceErrorSet (E : FiniteKrausFamily ι H H) : Set (Operator H) :=
  Set.range E.operator

theorem mem_sameSpaceErrorSet_iff (E : FiniteKrausFamily ι H H) (F : Operator H) :
    F ∈ E.sameSpaceErrorSet ↔ ∃ i : ι, E.operator i = F :=
  Iff.rfl

/-- Knill-Laflamme criterion specialized to the range of a same-space Kraus family. -/
def sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) : Prop :=
  KnillLaflammeCriterion H C E.sameSpaceErrorSet

/--
The raw correction predicate for a supplied CPTP recovery channel.

Only the recovery is a bundled `QuantumChannel`; the noise is the raw
operator-sum map induced by the finite Kraus family.
-/
def CorrectedBy (E : FiniteKrausFamily ι H K)
    (C : QuantumCode H) (recovery : QuantumChannel K H) : Prop :=
  ∀ rho : DensityOperator H,
    DensityOperator.SupportedOn C rho →
      recovery (E.inducedMap rho.toOperator) = rho.toOperator

/--
Correcting the raw induced finite-Kraus map is the same as correcting the
bundled CPTP channel obtained from a complete finite Kraus family.
-/
theorem correctedBy_iff_correctable_toQuantumChannel
    (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (C : QuantumCode H) (recovery : QuantumChannel K H) :
    E.CorrectedBy C recovery ↔ Correctable H K C (E.toQuantumChannel hE) recovery := by
  rfl

end FiniteKrausFamily

/--
Finite-Kraus correctability for a code.

The noise model is a complete finite Kraus family. Correctability remains stated
against the raw operator-sum map, while `FiniteKrausFamily.toQuantumChannel`
connects complete Kraus families to bundled CPTP channels.
-/
def FiniteKrausCorrectable (ι : Type v) [Fintype ι] (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K)
    (recovery : QuantumChannel K H) : Prop :=
  noise.Complete ∧ noise.CorrectedBy C recovery

/--
Finite-Kraus correctability is exactly completeness plus ordinary semantic
correctability for the induced bundled CPTP channel.
-/
theorem finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
    {ι : Type v} [Fintype ι] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K)
    (recovery : QuantumChannel K H) :
    FiniteKrausCorrectable ι H K C noise recovery ↔
      ∃ hnoise : noise.Complete,
        Correctable H K C (noise.toQuantumChannel hnoise) recovery := by
  constructor
  · intro h
    exact ⟨h.1, (noise.correctedBy_iff_correctable_toQuantumChannel h.1 C recovery).1 h.2⟩
  · rintro ⟨hnoise, hcorrectable⟩
    exact ⟨hnoise,
      (noise.correctedBy_iff_correctable_toQuantumChannel hnoise C recovery).2 hcorrectable⟩

/--
Existential finite-Kraus correctability is exactly existence of completeness and
a bundled-channel `Correctable` recovery for the induced CPTP channel.
-/
theorem exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
    {ι : Type v} [Fintype ι] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : FiniteKrausFamily ι H K) :
    (∃ recovery : QuantumChannel K H,
        FiniteKrausCorrectable ι H K C noise recovery) ↔
      ∃ hnoise : noise.Complete,
        ∃ recovery : QuantumChannel K H,
          Correctable H K C (noise.toQuantumChannel hnoise) recovery := by
  constructor
  · rintro ⟨recovery, hcorrectable⟩
    rcases (finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
      C noise recovery).1 hcorrectable with ⟨hnoise, hbundled⟩
    exact ⟨hnoise, recovery, hbundled⟩
  · rintro ⟨hnoise, recovery, hbundled⟩
    exact ⟨recovery,
      (finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel C noise recovery).2
        ⟨hnoise, hbundled⟩⟩

namespace FiniteKrausCorrectable

variable {ι : Type v} [Fintype ι]
variable {H K Ht Kt : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht] [FiniteQuantumSystem Ht]
variable [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt] [FiniteQuantumSystem Kt]

theorem unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K}
    {recovery : QuantumChannel K H}
    (h : FiniteKrausCorrectable ι H K C noise recovery) :
    FiniteKrausCorrectable ι Ht Kt (C.transport U)
      (noise.unitaryTransport U V)
      (QuantumChannel.comp (QuantumChannel.unitaryConj U)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm))) := by
  rcases h with ⟨hcomplete, hcorrected⟩
  constructor
  · exact noise.unitaryTransport_complete U V hcomplete
  · intro rho hρ
    let rho₀ : DensityOperator H := U.symm.conjDensity rho
    have hρ₀ : DensityOperator.SupportedOn C rho₀ := by
      exact (DensityOperator.supportedOn_symm_conjDensity_transport_iff U C rho).2 hρ
    have hcorr := hcorrected rho₀ hρ₀
    have hcorr' : recovery (noise.inducedMap (U.symm.conjOperator rho.toOperator)) =
        U.symm.conjOperator rho.toOperator := by
      simpa [rho₀] using hcorr
    change U.conjOperator
        (recovery (V.symm.conjOperator
          ((noise.unitaryTransport U V).inducedMap rho.toOperator))) = rho.toOperator
    rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply]
    rw [UnitaryTransport.symm_conjOperator_conjOperator]
    rw [hcorr']
    rw [UnitaryTransport.conjOperator_symm_conjOperator]

theorem of_unitaryTransport
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K}
    {recovery : QuantumChannel Kt Ht}
    (h : FiniteKrausCorrectable ι Ht Kt (C.transport U)
      (noise.unitaryTransport U V) recovery) :
    FiniteKrausCorrectable ι H K C noise
      (QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
        (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V))) := by
  rcases h with ⟨hcomplete, hcorrected⟩
  constructor
  · exact noise.of_unitaryTransport_complete U V hcomplete
  · intro rho hρ
    let rhoT : DensityOperator Ht := U.conjDensity rho
    have hρT : DensityOperator.SupportedOn (C.transport U) rhoT := by
      exact DensityOperator.supportedOn_conjDensity_transport U C rho hρ
    have hcorr := hcorrected rhoT hρT
    have hcorr' : recovery (V.conjOperator (noise.inducedMap rho.toOperator)) =
        U.conjOperator rho.toOperator := by
      rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply] at hcorr
      simpa [rhoT] using hcorr
    change U.symm.conjOperator
        (recovery (V.conjOperator (noise.inducedMap rho.toOperator))) = rho.toOperator
    rw [hcorr']
    rw [UnitaryTransport.symm_conjOperator_conjOperator]

theorem exists_unitaryTransport_iff
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt)
    {C : QuantumCode H} {noise : FiniteKrausFamily ι H K} :
    (∃ recovery : QuantumChannel Kt Ht,
      FiniteKrausCorrectable ι Ht Kt (C.transport U)
        (noise.unitaryTransport U V) recovery) ↔
    (∃ recovery : QuantumChannel K H,
      FiniteKrausCorrectable ι H K C noise recovery) := by
  constructor
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U.symm)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V)),
      of_unitaryTransport U V h⟩
  · rintro ⟨recovery, h⟩
    exact ⟨QuantumChannel.comp (QuantumChannel.unitaryConj U)
      (QuantumChannel.comp recovery (QuantumChannel.unitaryConj V.symm)),
      unitaryTransport U V h⟩

end FiniteKrausCorrectable

end

end Semantics
end QEC
