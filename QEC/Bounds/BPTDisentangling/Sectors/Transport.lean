import QEC.Bounds.BPTDisentangling.Sectors.Embedding

/-!
# BPT compressed sector transport

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
The four-factor coordinate transport obtained by first using the isotypic
unitary in the `AB` block.  It exposes the final source order
`(A tensor W) tensor (N tensor C)`.
-/
noncomputable def isotypicSectorBlockTransportLeft
    (A H W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H) C)
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem N C)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport
        (unitaryRTensor (unitaryLTensor A U) C)
        (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
      (unitaryLTensor A (tensorAssociatorUnitary W N C)))
    (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm

/--
The same four-factor transport, routed first through the `H tensor C` overlap.
This form carries the right BV03 block directly to `1 tensor Q_right`.
-/
noncomputable def isotypicSectorBlockTransportRight
    (A H W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N)) :
    Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H) C)
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem N C)) :=
  composeUnitaryTransport
    (composeUnitaryTransport
      (composeUnitaryTransport
        (tensorAssociatorUnitary A H C)
        (unitaryLTensor A (unitaryRTensor U C)))
      (unitaryLTensor A (tensorAssociatorUnitary W N C)))
    (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm

/--
The two concrete routes through an isotypic block agree.  This is the needed
four-factor associator coherence, proved on tensor generators rather than
assumed as a coherence axiom.
-/
theorem isotypicSectorBlockTransportLeft_eq_right
    (A H W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N)) :
    isotypicSectorBlockTransportLeft A H W N C U =
      isotypicSectorBlockTransportRight A H W N C U := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul middle exterior =>
      induction middle using TensorProduct.induction_on with
      | zero => simp
      | tmul interior sectorVector => rfl
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
The associator route inside the common left block coordinate is the canonical
reassociation `((A tensor W) tensor N) tensor C -> (A tensor W) tensor (N tensor C)`.
This supplies the literal tensor-map equality rather than relying on a
definitional associativity reduction.
-/
theorem isotypicSectorBlockTransportLeft_associator_coherence
    (A W N C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C] :
    composeUnitaryTransport
      (composeUnitaryTransport
        (composeUnitaryTransport
          (unitaryRTensor (tensorAssociatorUnitary A W N) C)
          (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
        (unitaryLTensor A (tensorAssociatorUnitary W N C)))
      (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm =
      tensorAssociatorUnitary (Semantics.CompositeSystem A W) N C := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
  | tmul middle c =>
      induction middle using TensorProduct.induction_on with
      | zero =>
          simp only [TensorProduct.zero_tmul, map_zero]
      | tmul left n =>
          induction left using TensorProduct.induction_on with
          | zero =>
              simp only [TensorProduct.zero_tmul, map_zero]
          | tmul a w => rfl
          | add first second hfirst hsecond =>
              rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
              simpa only [map_add] using
                congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          rw [TensorProduct.add_tmul]
          simpa only [map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

end BPTCommutingProjectorModel

end Bounds
end QEC
