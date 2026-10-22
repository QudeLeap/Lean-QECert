import QEC.Coding.Core.Definitions
import QEC.Coding.Stabilizer.PauliSemantics
import QEC.Locality.Graph.Core
import QEC.Locality.CorrectableRegions.LocalPauliErasureTransfer
import QEC.Locality.CorrectableRegions.SemanticDistanceErasure
import QEC.Locality.SeparatorProfile.Core
import QEC.Locality.ConnectivityTradeoff.MaxFamily
import QEC.Locality.ConnectivityTradeoff.RecursiveSeparator
import QEC.Locality.CorrectablePartition.EdgeDivision
import QEC.Locality.SeparatorProfile.EdgeDivision
import QEC.Locality.SeparatorProfile.ExplicitDivision
import QEC.Locality.CorrectablePartition.Core
import QEC.Locality.CorrectableRegions.TwoCorrectableRegionsDimension
import QEC.Locality.OptimalTradeoff.BadSquareSubdivision
/-!
# QEC.Locality

Locality and connectivity interfaces for exact quantum-code tradeoff results.
-/

namespace QEC
namespace Locality

universe u v w

/-- Finite-site metric data used by geometric locality statements. -/
structure LatticeGeometry (ι : Type u) [Fintype ι] where
  distance : ι → ι → Nat
  distance_self : ∀ i : ι, distance i i = 0
  distance_symm : ∀ i j : ι, distance i j = distance j i

/-- A support has bounded diameter in a chosen lattice geometry. -/
def BoundedDiameter {ι : Type u} [Fintype ι] (geometry : LatticeGeometry ι)
    (support : Set ι) (radius : Nat) : Prop :=
  ∀ ⦃i : ι⦄, i ∈ support → ∀ ⦃j : ι⦄, j ∈ support →
    geometry.distance i j ≤ radius

/--
Local commuting-projector code data.

This records the geometric support and commutation vocabulary needed by exact
locality tradeoff statements without asserting any BPT-style bound.
-/
structure LocalProjectorCode (ι : Type u) (H : Type v) [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] where
  geometry : LatticeGeometry ι
  code : Semantics.QuantumCode H
  checks : Set (Semantics.Operator H)
  support : Semantics.Operator H → Set ι
  projectorLocality : Nat
  projector_checks : ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks → P.comp P = P
  local_support : ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks →
    BoundedDiameter geometry (support P) projectorLocality
  commuting_checks : ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks →
    ∀ ⦃Q : Semantics.Operator H⦄, Q ∈ checks → P.comp Q = Q.comp P
  code_eq_fixed_by_checks : ∀ v : H, v ∈ code.carrier ↔
    ∀ ⦃P : Semantics.Operator H⦄, P ∈ checks → P v = v

/-- The projector onto the `+1` eigenspace of an involutive stabilizer operator. -/
noncomputable def stabilizerProjector
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (U : Semantics.Operator H) : Semantics.Operator H :=
  (1 / 2 : Complex) • (1 + U)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]

/-- The `+1` eigenspace projector is idempotent when the stabilizer squares to identity. -/
theorem stabilizerProjector_idempotent_of_involutive
    (U : Semantics.Operator H) (hU : U.comp U = 1) :
    (stabilizerProjector U).comp (stabilizerProjector U) =
      stabilizerProjector U := by
  ext v
  have hUv : U (U v) = v := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Semantics.Operator H => A v) hU
  simp [stabilizerProjector, LinearMap.comp_apply, hUv, smul_add, smul_smul]
  module

/-- Fixed points of an operator are exactly fixed points of its stabilizer projector. -/
theorem stabilizerProjector_fixed_iff
    (U : Semantics.Operator H) (v : H) :
    stabilizerProjector U v = v ↔ U v = v := by
  constructor
  · intro h
    have h2 := congrArg (fun x : H => (2 : Complex) • x) h
    simp [stabilizerProjector, smul_add, smul_smul] at h2
    calc
      U v = (v + U v) - v := by abel
      _ = (2 : Complex) • v - v := by rw [h2]
      _ = v := by module
  · intro h
    simp [stabilizerProjector, h, smul_add]
    module

/-- Commuting stabilizer operators have commuting `+1` eigenspace projectors. -/
theorem stabilizerProjector_commute_of_commute
    (U V : Semantics.Operator H) (hUV : U.comp V = V.comp U) :
    (stabilizerProjector U).comp (stabilizerProjector V) =
      (stabilizerProjector V).comp (stabilizerProjector U) := by
  ext v
  have hUVv : U (V v) = V (U v) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Semantics.Operator H => A v) hUV
  simp [stabilizerProjector, LinearMap.comp_apply, hUVv, smul_add, smul_smul]
  module

private noncomputable def binaryStabilizerProjectorSupport
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (S : Set (Coding.PauliSymplectic.Binary ι))
    (P : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) : Set ι := by
  classical
  exact if hP :
      P ∈ Set.image
        (fun Q : Coding.PauliSymplectic.Binary ι =>
          stabilizerProjector (Coding.PauliSymplectic.toQubitOperator Q)) S then
    {i | i ∈ Coding.PauliSymplectic.support (Classical.choose hP)}
  else
    ∅

/--
Build a local commuting-projector-code interface from explicit binary stabilizer
operator data and explicit Pauli-support locality.
-/
noncomputable def binaryStabilizerLocalProjectorCode
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (geometry : LatticeGeometry ι)
    (S : Set (Coding.PauliSymplectic.Binary ι)) (r : Nat)
    (hcomm : ∀ P, P ∈ S → ∀ Q, Q ∈ S → Coding.PauliSymplectic.Commutes P Q)
    (hinvol : ∀ P, P ∈ S →
      (Coding.PauliSymplectic.toQubitOperator P).comp
        (Coding.PauliSymplectic.toQubitOperator P) = 1)
    (hlocal : ∀ P, P ∈ S →
      BoundedDiameter geometry
        ({i | i ∈ Coding.PauliSymplectic.support P} : Set ι) r) :
    LocalProjectorCode ι (Semantics.Qubit.QubitRegister ι) where
  geometry := geometry
  code := Coding.PauliSymplectic.binaryStabilizerCommonFixedQuantumCode S
  checks :=
    Set.image
      (fun P : Coding.PauliSymplectic.Binary ι =>
        stabilizerProjector (Coding.PauliSymplectic.toQubitOperator P)) S
  support := binaryStabilizerProjectorSupport S
  projectorLocality := r
  projector_checks := by
    intro P hP
    rcases hP with ⟨Q, hQ, rfl⟩
    exact stabilizerProjector_idempotent_of_involutive
      (Coding.PauliSymplectic.toQubitOperator Q) (hinvol Q hQ)
  local_support := by
    intro P hP
    simp [binaryStabilizerProjectorSupport, hP]
    simpa [Coding.PauliSymplectic.mem_support] using
      hlocal (Classical.choose hP) (Classical.choose_spec hP).1
  commuting_checks := by
    intro P hP Q hQ
    rcases hP with ⟨P', hP', rfl⟩
    rcases hQ with ⟨Q', hQ', rfl⟩
    exact stabilizerProjector_commute_of_commute
      (Coding.PauliSymplectic.toQubitOperator P')
      (Coding.PauliSymplectic.toQubitOperator Q') (by
        simpa [Module.End.mul_eq_comp] using
          Coding.PauliSymplectic.toQubitOperator_commute_of_commutes
            P' Q' (hcomm P' hP' Q' hQ'))
  code_eq_fixed_by_checks := by
    intro v
    constructor
    · intro hv P hP
      rcases hP with ⟨Q, hQ, rfl⟩
      exact
        (stabilizerProjector_fixed_iff
          (Coding.PauliSymplectic.toQubitOperator Q) v).2
          ((Coding.PauliSymplectic.mem_binaryStabilizerCommonFixedQuantumCode_carrier
            (S := S) (ψ := v)).1 hv Q hQ)
    · intro hfixed
      exact
        (Coding.PauliSymplectic.mem_binaryStabilizerCommonFixedQuantumCode_carrier
          (S := S) (ψ := v)).2 (by
            intro Q hQ
            exact
              (stabilizerProjector_fixed_iff
                (Coding.PauliSymplectic.toQubitOperator Q) v).1
                (hfixed (P := stabilizerProjector
                  (Coding.PauliSymplectic.toQubitOperator Q)) ⟨Q, hQ, rfl⟩))

/--
Shared framework for exact locality and connectivity tradeoff statements.

The record packages the M3 algebraic-semantic bridge, geometric
commuting-projector locality, graph connectivity, separator-profile data, and
the remaining convention slots that the audited M4 theorem statements must make
explicit. It is not itself a BPT or connectivity-separator theorem.
-/
structure ExactLocalityFramework (F : Type u) (ι : Type v) (H K : Type w)
    [Field F] [Fintype F] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] where
  semanticBridge : Coding.SemanticAlgebraicBridge F ι H K
  localProjectorCode : LocalProjectorCode ι H
  connectivityGraph : ConnectivityGraph ι
  separatorProfileUpperBound : Nat → Nat
  hasSeparatorProfileUpperBound :
    AssumedTwoThirdsSeparationProfileUpperBound connectivityGraph separatorProfileUpperBound
  latticeDimension : Nat
  localDimensionBound : Nat
  distanceConvention : Prop
  asymptoticFamily : Nat → Prop

end Locality
end QEC
