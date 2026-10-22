import QEC.Bounds.BPTDisentangling.Joint.BlockTransport

/-!
# BPT first-cut sequential core

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
The first sequential compression of a BV03 block.  A left `B` subtype
embedding is carried through the first-cut isotypic `C` coordinates, then the
actual `B` coordinate change and the final source associator.  This is the
generic shape used to derive `hfirst` from the physical first-cut block.
-/
theorem sequential_firstCut_block_of_left_intertwining
    {A B B' H W N D WB NB : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup B'] [InnerProductSpace Complex B'] [Semantics.FiniteQuantumSystem B']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    (UC : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UB : Semantics.UnitaryTransport B (Semantics.CompositeSystem WB NB))
    (i : B →ₗ[Complex] B')
    (R : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B') H) D))
    (P : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B') W))
    (Q : Semantics.Operator (Semantics.CompositeSystem N D))
    (hblock :
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B') H W N D UC).conjOperator R =
        TensorProduct.map P Q) :
    let K := TensorProduct.map
      (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
        (1 : Semantics.Operator H))
      (1 : Semantics.Operator D)
    let Kleft := TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
      (1 : Semantics.Operator W)
    let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
    let Pleft := TB.conjOperator ((LinearMap.adjoint Kleft).comp (P.comp Kleft))
    let G := composeUnitaryTransport
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B) H W N D UC)
      (composeUnitaryTransport
        (unitaryRTensor TB (Semantics.CompositeSystem N D))
        (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
          (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)))
    G.conjOperator ((LinearMap.adjoint K).comp (R.comp K)) =
      (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)).conjOperator
        (TensorProduct.map Pleft Q) := by
  dsimp
  have hcompressed := unitaryTransport_conj_compression_of_intertwines
    (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B') H W N D UC)
    (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B) H W N D UC)
    (TensorProduct.map
      (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
        (1 : Semantics.Operator H))
      (1 : Semantics.Operator D))
      (TensorProduct.map
        (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
          (1 : Semantics.Operator W))
        (1 : Semantics.Operator (Semantics.CompositeSystem N D)))
    (isotypicSectorBlockTransportLeft_comp_tensorMap_left
      (A := Semantics.CompositeSystem A B)
      (A' := Semantics.CompositeSystem A B')
      (H := H) (W := W) (N := N) (C := D) UC
      (TensorProduct.map (1 : Semantics.Operator A) i))
    R
  rw [hblock] at hcompressed
  rw [tensorMap_left_compression] at hcompressed
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator, hcompressed,
    unitaryRTensor_conj_tensorMap]

/--
Named-interface adapter for the concrete first-cut active block.  The caller
supplies definitional equalities for its named compression, left factor, and
transport; the generic naturality square remains internal to the core proof.
-/
theorem sequential_firstCut_named_block
    {A B B' H W N D WB NB : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup B'] [InnerProductSpace Complex B'] [Semantics.FiniteQuantumSystem B']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    (UC : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UB : Semantics.UnitaryTransport B (Semantics.CompositeSystem WB NB))
    (i : B →ₗ[Complex] B')
    (R : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B') H) D))
    (P : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B') W))
    (Q : Semantics.Operator (Semantics.CompositeSystem N D))
    (Rsequential : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) H) D))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W)))
    (G : Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) H) D)
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem (Semantics.CompositeSystem NB W)
          (Semantics.CompositeSystem N D))))
    (hRsequential :
      let K := TensorProduct.map
        (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
          (1 : Semantics.Operator H))
        (1 : Semantics.Operator D)
      Rsequential = (LinearMap.adjoint K).comp (R.comp K))
    (hPleft :
      let Kleft := TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
        (1 : Semantics.Operator W)
      let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
      Pleft = TB.conjOperator ((LinearMap.adjoint Kleft).comp (P.comp Kleft)))
    (hG :
      let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
      G = composeUnitaryTransport
        (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B) H W N D UC)
        (composeUnitaryTransport
          (unitaryRTensor TB (Semantics.CompositeSystem N D))
          (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
            (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D))))
    (hblock :
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B') H W N D UC).conjOperator R =
        TensorProduct.map P Q) :
    G.conjOperator Rsequential =
      (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)).conjOperator
        (TensorProduct.map Pleft Q) := by
  dsimp only at hRsequential hPleft hG
  subst Rsequential
  subst Pleft
  subst G
  exact sequential_firstCut_block_of_left_intertwining UC UB i R P Q hblock


end BPTCommutingProjectorModel

end Bounds
end QEC
