import QEC.Bounds.BPTSeparatedUnion.Assembly.RegionCompressionRaw
import QEC.Bounds.BPTDisentangling.SeparatedUnionBridge

/-! # Generic associator algebra for final-assembly compression -/

noncomputable section

namespace QEC
namespace Bounds

open scoped TensorProduct

universe u

theorem tensorAssociatorUnitary_symm_conj_leftMap_right_one
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) :
    (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.conjOperator
        (TensorProduct.map A (1 : Semantics.Operator (Semantics.CompositeSystem K J))) =
      TensorProduct.map (TensorProduct.map A (1 : Semantics.Operator K))
        (1 : Semantics.Operator J) := by
  rw [show (1 : Semantics.Operator (Semantics.CompositeSystem K J)) =
      TensorProduct.map (1 : Semantics.Operator K) (1 : Semantics.Operator J) by
        symm
        exact TensorProduct.map_one]
  exact BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_conj_tensorMap A
    (1 : Semantics.Operator K) (1 : Semantics.Operator J)

theorem unitary_symm_conj_leftMap_right_one_of_associator_eq
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (O : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)))
    (hO : O = BPTCommutingProjectorModel.tensorAssociatorUnitary H K J)
    (A : Semantics.Operator H) :
    O.symm.conjOperator
        (TensorProduct.map A (1 : Semantics.Operator (Semantics.CompositeSystem K J))) =
      TensorProduct.map (TensorProduct.map A (1 : Semantics.Operator K))
        (1 : Semantics.Operator J) := by
  rw [hO]
  exact tensorAssociatorUnitary_symm_conj_leftMap_right_one A

theorem compression_precompose_unitary_of_eq
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (J : H →ₗ[Complex] K)
    (Jnew : S →ₗ[Complex] K) (hJnew : Jnew = J.comp U.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator K) :
    (LinearMap.adjoint Jnew).comp (P.comp Jnew) =
      U.symm.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
  rw [hJnew]
  exact BPTCommutingProjectorModel.compression_precompose_unitary U J P

theorem embedding_compression_congr
    {S K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (E : S →ₗ[Complex] K) {P Q : Semantics.Operator K} (h : P = Q) :
    (LinearMap.adjoint E).comp (P.comp E) =
      (LinearMap.adjoint E).comp (Q.comp E) := by
  subst Q
  rfl

theorem isometric_lift_congr
    {S K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (E : S →ₗ[Complex] K) {P Q : Semantics.Operator S} (h : P = Q) :
    E.comp (P.comp (LinearMap.adjoint E)) =
      E.comp (Q.comp (LinearMap.adjoint E)) := by
  subst Q
  rfl

def SourceFactorization
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (P A B : Semantics.Operator H) (coefficient : Complex) : Prop :=
  P * A * B * P = coefficient • (P * B * P)

theorem SourceFactorization.eq
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    {P A B : Semantics.Operator H} {coefficient : Complex}
    (h : SourceFactorization P A B coefficient) :
    P * A * B * P = coefficient • (P * B * P) :=
  h

theorem SourceFactorization.conjOperator
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {P A B : Semantics.Operator H} {coefficient : Complex}
    (h : SourceFactorization P A B coefficient)
    (U : Semantics.UnitaryTransport H K) :
    SourceFactorization (U.conjOperator P) (U.conjOperator A) (U.conjOperator B)
      coefficient := by
  unfold SourceFactorization at h ⊢
  have hmapped := congrArg U.conjOperator h
  change U.conjOperator (P * A * B * P) =
    U.conjOperator (coefficient • (P * B * P)) at hmapped
  have hsmul : U.conjOperator (coefficient • (P * B * P)) =
      coefficient • U.conjOperator (P * B * P) :=
    U.conjOperatorLinearMap.map_smul coefficient (P * B * P)
  rw [hsmul] at hmapped
  simpa only [Semantics.UnitaryTransport.conjOperator_mul] using hmapped

theorem source_factorization_projector_congr
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (P Q A B : Semantics.Operator H) (coefficient : Complex)
    (hPQ : P = Q)
    (hfactor : SourceFactorization P A B coefficient) :
    SourceFactorization Q A B coefficient := by
  subst Q
  exact hfactor

theorem reassociated_rankOne_isometric_lift
    {H K J X : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    (E : Semantics.CompositeSystem H (Semantics.CompositeSystem K J) →ₗ[Complex] X)
    (phi : H) (chi : K) (Q : Semantics.Operator J) :
    let O := BPTCommutingProjectorModel.tensorAssociatorUnitary H K J
    let Enew := E.comp O.toLinearEquiv.toLinearMap
    Enew.comp
        ((TensorProduct.map
          (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
            (phi ⊗ₜ[Complex] chi)).toLinearMap Q).comp
          (LinearMap.adjoint Enew)) =
      E.comp
        ((TensorProduct.map
          (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (TensorProduct.map
            (InnerProductSpace.rankOne Complex chi chi).toLinearMap Q)).comp
          (LinearMap.adjoint E)) := by
  dsimp only
  let O := BPTCommutingProjectorModel.tensorAssociatorUnitary H K J
  let Enew := E.comp O.toLinearEquiv.toLinearMap
  let P := TensorProduct.map
    (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    (TensorProduct.map (InnerProductSpace.rankOne Complex chi chi).toLinearMap Q)
  have hRankOne : O.symm.conjOperator P =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
          (phi ⊗ₜ[Complex] chi)).toLinearMap Q := by
    exact BPTCommutingProjectorModel.tensorAssociator_symm_conj_rankOneTensor phi chi Q
  calc
    Enew.comp
        ((TensorProduct.map
          (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
            (phi ⊗ₜ[Complex] chi)).toLinearMap Q).comp
          (LinearMap.adjoint Enew)) =
      Enew.comp ((O.symm.conjOperator P).comp (LinearMap.adjoint Enew)) :=
        isometric_lift_congr Enew hRankOne.symm
    _ = E.comp (P.comp (LinearMap.adjoint E)) := by
      exact BPTCommutingProjectorModel.reassociated_isometric_lift O E P

theorem unitary_conjOperator_congr
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (U : Semantics.UnitaryTransport H H) {P Q : Semantics.Operator H} (h : P = Q) :
    U.conjOperator P = U.conjOperator Q := by
  subst Q
  rfl

set_option maxHeartbeats 1000000 in
theorem precomposed_embedding_isometry_of_eq
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (E : H →ₗ[Complex] K)
    (Enew : S →ₗ[Complex] K) (hEnew : Enew = E.comp U.toLinearEquiv.toLinearMap)
    (hE : (LinearMap.adjoint E).comp E = (1 : Semantics.Operator H)) :
    (LinearMap.adjoint Enew).comp Enew = (1 : Semantics.Operator S) := by
  subst Enew
  have hPre :
      (LinearMap.adjoint (E.comp U.toLinearEquiv.toLinearMap)).comp
          (E.comp U.toLinearEquiv.toLinearMap) =
        U.symm.conjOperator ((LinearMap.adjoint E).comp E) := by
    simpa only [Module.End.one_eq_id, LinearMap.id_comp] using
      BPTCommutingProjectorModel.compression_precompose_unitary U E
      (1 : Semantics.Operator K)
  calc
    (LinearMap.adjoint (E.comp U.toLinearEquiv.toLinearMap)).comp
        (E.comp U.toLinearEquiv.toLinearMap) =
      U.symm.conjOperator ((LinearMap.adjoint E).comp E) := hPre
    _ = U.symm.conjOperator (1 : Semantics.Operator H) := by rw [hE]
    _ = 1 := U.symm.conjOperator_one

set_option maxHeartbeats 1000000 in
theorem intertwining_precompose_associator_right_of_eq
    {H K J T : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    (O : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)))
    (hO : O = BPTCommutingProjectorModel.tensorAssociatorUnitary H K J)
    (E : Semantics.CompositeSystem H (Semantics.CompositeSystem K J) →ₗ[Complex] T)
    (Enew : Semantics.CompositeSystem (Semantics.CompositeSystem H K) J →ₗ[Complex] T)
    (hEnew : Enew = E.comp O.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator T) (R : Semantics.Operator J)
    (hE : P.comp E = E.comp
      (TensorProduct.map (1 : Semantics.Operator H)
        (TensorProduct.map (1 : Semantics.Operator K) R))) :
    P.comp Enew = Enew.comp
      (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R) := by
  subst O
  subst Enew
  have hAssoc := BPTCommutingProjectorModel.tensorAssociator_right_intertwines
    (H := H) (K := K) (J := J) R
  calc
    P.comp (E.comp
        (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap) =
      (P.comp E).comp
        (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap := by
          simp only [LinearMap.comp_assoc]
    _ = (E.comp
        (TensorProduct.map (1 : Semantics.Operator H)
          (TensorProduct.map (1 : Semantics.Operator K) R))).comp
        (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap := by
          rw [hE]
    _ = E.comp
        ((BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap.comp
          (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R)) := by
          simp only [LinearMap.comp_assoc]
          rw [hAssoc]
    _ = (E.comp
        (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap).comp
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R) := by
          simp only [LinearMap.comp_assoc]

end Bounds
end QEC
