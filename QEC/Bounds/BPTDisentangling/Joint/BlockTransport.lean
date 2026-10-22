import QEC.Bounds.BPTDisentangling.Sectors.Transport

/-!
# BPT generic block transport

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
The coherent `B`-sector block transport is natural for a literal map on its
untouched exterior factor.  In particular, a later `C`-sector compression can
be moved across the `B` coordinate transport without postulating a common
block equation.
-/
theorem isotypicSectorBlockTransportLeft_comp_tensorMap_right
    {A H W N C C' : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup C'] [InnerProductSpace Complex C'] [Semantics.FiniteQuantumSystem C']
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (K : C →ₗ[Complex] C') :
    (isotypicSectorBlockTransportLeft A H W N C' U).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H)) K) =
      (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map (1 : Semantics.Operator N) K)).comp
        (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv.toLinearMap := by
  have hAssoc :
      (tensorAssociatorUnitary W N C').toLinearEquiv.toLinearMap.comp
          (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem W N)) K) =
        (TensorProduct.map (1 : Semantics.Operator W)
          (TensorProduct.map (1 : Semantics.Operator N) K)).comp
          (tensorAssociatorUnitary W N C).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul middle exterior =>
        induction middle using TensorProduct.induction_on with
        | zero => simp
        | tmul left right => rfl
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.add_tmul, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  have hAssocSymm :
      ((tensorAssociatorUnitary A W (Semantics.CompositeSystem N C')).symm.toLinearEquiv.toLinearMap).comp
          (TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (1 : Semantics.Operator W)
              (TensorProduct.map (1 : Semantics.Operator N) K))) =
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
          (TensorProduct.map (1 : Semantics.Operator N) K)).comp
          ((tensorAssociatorUnitary A W
            (Semantics.CompositeSystem N C)).symm.toLinearEquiv.toLinearMap) := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul left middle =>
        induction middle using TensorProduct.induction_on with
        | zero => simp
        | tmul right exterior => rfl
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.tmul_add, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul middle exterior =>
      induction middle using TensorProduct.induction_on with
      | zero => simp
      | tmul interior sectorVector =>
          let z : Semantics.CompositeSystem W N := U.toLinearEquiv sectorVector
          have hinner :
              (TensorProduct.assoc Complex W N C') (z ⊗ₜ[Complex] K exterior) =
                (TensorProduct.map (1 : Semantics.Operator W)
                  (TensorProduct.map (1 : Semantics.Operator N) K))
                  ((TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] exterior)) := by
            have h := congrArg (fun F => F (z ⊗ₜ[Complex] exterior)) hAssoc
            simpa [tensorAssociatorUnitary, LinearMap.comp_apply] using h
          have houter :
              (TensorProduct.assoc Complex A W (Semantics.CompositeSystem N C')).symm
                  (interior ⊗ₜ[Complex]
                    (TensorProduct.map (1 : Semantics.Operator W)
                      (TensorProduct.map (1 : Semantics.Operator N) K))
                    ((TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] exterior))) =
                (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
                  (TensorProduct.map (1 : Semantics.Operator N) K))
                  ((TensorProduct.assoc Complex A W (Semantics.CompositeSystem N C)).symm
                    (interior ⊗ₜ[Complex]
                      (TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] exterior))) := by
            have h := congrArg (fun F =>
                F (interior ⊗ₜ[Complex]
                  (TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] exterior))) hAssocSymm
            simpa [tensorAssociatorUnitary, LinearMap.comp_apply] using h
          change
            (TensorProduct.assoc Complex A W (Semantics.CompositeSystem N C')).symm
                (interior ⊗ₜ[Complex]
                  (TensorProduct.assoc Complex W N C')
                    (z ⊗ₜ[Complex] K exterior)) =
              (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
                (TensorProduct.map (1 : Semantics.Operator N) K))
                ((TensorProduct.assoc Complex A W (Semantics.CompositeSystem N C)).symm
                  (interior ⊗ₜ[Complex]
                    (TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] exterior)))
          calc
            _ = (TensorProduct.assoc Complex A W (Semantics.CompositeSystem N C')).symm
                (interior ⊗ₜ[Complex]
                  (TensorProduct.map (1 : Semantics.Operator W)
                    (TensorProduct.map (1 : Semantics.Operator N) K))
                    ((TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] exterior))) := by
              rw [hinner]
            _ = _ := houter
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/--
The coherent isotypic block transport is also natural for a map on its left
ambient factor.  In the BPT application this transports the active `B`
subtype embedding through the first-cut `C` block, so the first sequential
compression is derived from the actual BV03 equation rather than supplied as
an `hfirst` hypothesis.
-/
theorem isotypicSectorBlockTransportLeft_comp_tensorMap_left
    {A A' H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup A'] [InnerProductSpace Complex A'] [Semantics.FiniteQuantumSystem A']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (K : A →ₗ[Complex] A') :
    (isotypicSectorBlockTransportLeft A' H W N C U).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator H))
          (1 : Semantics.Operator C)) =
      (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator W))
        (1 : Semantics.Operator (Semantics.CompositeSystem N C))).comp
        (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv.toLinearMap := by
  have hAssocSymm :
      ((tensorAssociatorUnitary A' W (Semantics.CompositeSystem N C)).symm.toLinearEquiv.toLinearMap).comp
          (TensorProduct.map K
            (1 : Semantics.Operator (Semantics.CompositeSystem W
              (Semantics.CompositeSystem N C)))) =
        (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator W))
          (1 : Semantics.Operator (Semantics.CompositeSystem N C))).comp
          (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul a wnc =>
        induction wnc using TensorProduct.induction_on with
        | zero => simp
        | tmul w nc => rfl
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.tmul_add, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul ah c =>
      induction ah using TensorProduct.induction_on with
      | zero => simp
      | tmul a h =>
          let z : Semantics.CompositeSystem W N := U.toLinearEquiv h
          have hfinal := congrArg (fun map =>
              map (a ⊗ₜ[Complex]
                (TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] c))) hAssocSymm
          simpa [isotypicSectorBlockTransportLeft, composeUnitaryTransport,
            unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary, z,
            LinearMap.comp_apply] using hfinal
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

/-- Left tensoring conjugates an arbitrary two-factor operator on its right factor. -/
theorem unitaryLTensor_conj_tensorMap
    {H K I : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup I] [InnerProductSpace Complex I] [Semantics.FiniteQuantumSystem I]
    (U : Semantics.UnitaryTransport H K)
    (P : Semantics.Operator I) (Q : Semantics.Operator H) :
    (unitaryLTensor I U).conjOperator (TensorProduct.map P Q) =
      TensorProduct.map P (U.conjOperator Q) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul i h => simp [unitaryLTensor, Semantics.UnitaryTransport.conjOperator]
  | add first second hfirst hsecond => simp [map_add, hfirst, hsecond]

/-- Right tensoring conjugates an arbitrary two-factor operator on its left factor. -/
theorem unitaryRTensor_conj_tensorMap
    {H K I : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup I] [InnerProductSpace Complex I] [Semantics.FiniteQuantumSystem I]
    (U : Semantics.UnitaryTransport H K)
    (P : Semantics.Operator H) (Q : Semantics.Operator I) :
    (unitaryRTensor U I).conjOperator (TensorProduct.map P Q) =
      TensorProduct.map (U.conjOperator P) Q := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul h i => simp [unitaryRTensor, Semantics.UnitaryTransport.conjOperator]
  | add first second hfirst hsecond => simp [map_add, hfirst, hsecond]

/-- Compressing the right factor of a tensor block leaves its left factor unchanged. -/
theorem tensorMap_right_compression
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (K : C →ₗ[Complex] B) :
    (LinearMap.adjoint (TensorProduct.map (1 : Semantics.Operator A) K)).comp
        ((TensorProduct.map P Q).comp (TensorProduct.map (1 : Semantics.Operator A) K)) =
      TensorProduct.map P ((LinearMap.adjoint K).comp (Q.comp K)) := by
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← LinearMap.comp_assoc, ← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rfl

/-- Compressing the left factor of a tensor block leaves its right factor unchanged. -/
theorem tensorMap_left_compression
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (K : C →ₗ[Complex] A) :
    (LinearMap.adjoint (TensorProduct.map K (1 : Semantics.Operator B))).comp
        ((TensorProduct.map P Q).comp (TensorProduct.map K (1 : Semantics.Operator B))) =
      TensorProduct.map ((LinearMap.adjoint K).comp (P.comp K)) Q := by
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← LinearMap.comp_assoc, ← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rfl

/--
Conjugating a compression across an actual intertwining square is the same as
compressing the conjugated operator in the transported subspace coordinates.
This is the generic bridge from a BV03 block equality to the later sequential
`B`/`C` sector compression; neither compressed block is assumed as input.
-/
theorem unitaryTransport_conj_compression_of_intertwines
    {H H' S S' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup H'] [InnerProductSpace Complex H'] [Semantics.FiniteQuantumSystem H']
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup S'] [InnerProductSpace Complex S'] [Semantics.FiniteQuantumSystem S']
    (T : Semantics.UnitaryTransport H H') (Tsub : Semantics.UnitaryTransport S S')
    (K : S →ₗ[Complex] H) (K' : S' →ₗ[Complex] H')
    (hintertwines : T.toLinearEquiv.toLinearMap.comp K = K'.comp Tsub.toLinearEquiv.toLinearMap)
    (R : Semantics.Operator H) :
    Tsub.conjOperator ((LinearMap.adjoint K).comp (R.comp K)) =
      (LinearMap.adjoint K').comp ((T.conjOperator R).comp K') := by
  have hright : (T.toLinearEquiv.toLinearMap.comp K).comp Tsub.symm.toLinearEquiv.toLinearMap = K' := by
    rw [hintertwines, LinearMap.comp_assoc]
    simp
  have hleft : Tsub.toLinearEquiv.toLinearMap.comp
      ((LinearMap.adjoint K).comp T.symm.toLinearEquiv.toLinearMap) = LinearMap.adjoint K' := by
    have hadjoint := congrArg LinearMap.adjoint hright
    have hTsub : LinearMap.adjoint Tsub.symm.toLinearEquiv.toLinearMap =
        Tsub.toLinearEquiv.toLinearMap := by
      simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
        (Semantics.UnitaryTransport.adjoint_toLinearMap Tsub.symm)
    have hT : LinearMap.adjoint T.toLinearEquiv.toLinearMap =
        T.symm.toLinearEquiv.toLinearMap :=
      Semantics.UnitaryTransport.adjoint_toLinearMap T
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, hTsub, hT] at hadjoint
    exact hadjoint
  unfold Semantics.UnitaryTransport.conjOperator
  ext x
  change Tsub (LinearMap.adjoint K (R (K (Tsub.symm x)))) =
    LinearMap.adjoint K' (T (R (T.symm (K' x))))
  have hright_apply : T (K (Tsub.symm x)) = K' x := by
    have h := congrArg (fun map => map x) hright
    simpa [LinearMap.comp_apply] using h
  have hK : K (Tsub.symm x) = T.symm (K' x) := by
    calc
      K (Tsub.symm x) = T.symm (T (K (Tsub.symm x))) := by simp
      _ = T.symm (K' x) := congrArg T.symm hright_apply
  have hleft_apply :
      Tsub (LinearMap.adjoint K (T.symm (T (R (K (Tsub.symm x)))))) =
        LinearMap.adjoint K' (T (R (K (Tsub.symm x)))) := by
    have h := congrArg (fun map => map (T (R (K (Tsub.symm x)))) ) hleft
    simpa [LinearMap.comp_apply] using h
  calc
    Tsub (LinearMap.adjoint K (R (K (Tsub.symm x)))) =
        Tsub (LinearMap.adjoint K (T.symm (T (R (K (Tsub.symm x)))))) := by simp
    _ = LinearMap.adjoint K' (T (R (K (Tsub.symm x)))) := hleft_apply
    _ = LinearMap.adjoint K' (T (R (T.symm (K' x)))) := by rw [hK]


end BPTCommutingProjectorModel

end Bounds
end QEC
