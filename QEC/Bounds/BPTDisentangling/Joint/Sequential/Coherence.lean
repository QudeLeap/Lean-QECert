import QEC.Bounds.BPTDisentangling.Sectors.Transport

/-!
# BPT sequential coordinate coherence

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
The sequential B/C coordinate comparison is checked on literal tensor
generators.  This small pointwise form keeps the two sector transports
available for later reassociation proofs without hiding a tensor-coordinate
assumption in the common-factor assembly.
-/
theorem isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (a : A) (h : H) (c : C) (w : W) (n : N)
    (hU : U h = w ⊗ₜ[Complex] n) :
    isotypicSectorBlockTransportLeft A H W N C U ((a ⊗ₜ[Complex] h) ⊗ₜ[Complex] c) =
      (a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] c) := by
  simp [isotypicSectorBlockTransportLeft, composeUnitaryTransport,
    unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary, hU]

/-- The linear-equivalence view of the preceding tensor-generator transport. -/
@[simp] theorem isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (a : A) (h : H) (c : C) (w : W) (n : N)
    (hU : U.toLinearEquiv h = w ⊗ₜ[Complex] n) :
    (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv
        ((a ⊗ₜ[Complex] h) ⊗ₜ[Complex] c) =
      (a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] c) := by
  exact isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq U a h c w n hU

set_option maxHeartbeats 800000 in
/--
The two sequential sector coordinate systems are coherent after the literal
source reassociation from `((A B) C) D` to `(A B) (C D)`.  This is the
concrete `htransport` used by the BPT common-factor argument.
-/
theorem sequential_isotypicSectorBlockTransportLeft_coherence
    {A H W N C X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2)) :
    composeUnitaryTransport
        (tensorAssociatorUnitary (Semantics.CompositeSystem A H) C D)
        (composeUnitaryTransport
          (isotypicSectorBlockTransportLeft A H W N
            (Semantics.CompositeSystem C D) UB)
          (composeUnitaryTransport
            (unitaryLTensor (Semantics.CompositeSystem A W)
              (unitaryLTensor N
                (composeUnitaryTransport (unitaryRTensor UC D)
                  (tensorAssociatorUnitary X N2 D))))
            (unitaryLTensor (Semantics.CompositeSystem A W)
              (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))) =
      composeUnitaryTransport
        (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A H) C X N2 D UC)
        (composeUnitaryTransport
          (unitaryRTensor (isotypicSectorBlockTransportLeft A H W N X UB)
            (Semantics.CompositeSystem N2 D))
          (tensorAssociatorUnitary (Semantics.CompositeSystem A W)
            (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D))) := by
  apply unitaryTransport_ext
  apply LinearEquiv.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simpa only [map_zero]
  | tmul abc d =>
      induction abc using TensorProduct.induction_on with
      | zero => simpa only [TensorProduct.zero_tmul, map_zero]
      | tmul ab c =>
          induction ab using TensorProduct.induction_on with
          | zero => simpa only [TensorProduct.zero_tmul, map_zero]
          | tmul a h =>
              rcases UB.symm.toLinearEquiv.surjective h with ⟨wn, hwn⟩
              subst h
              induction wn using TensorProduct.induction_on with
              | zero =>
                  simpa only [map_zero, TensorProduct.tmul_zero,
                    TensorProduct.zero_tmul]
              | tmul w n =>
                  rcases UC.symm.toLinearEquiv.surjective c with ⟨xn, hxn⟩
                  subst c
                  induction xn using TensorProduct.induction_on with
                  | zero =>
                      simpa only [map_zero, TensorProduct.tmul_zero,
                        TensorProduct.zero_tmul]
                  | tmul x n2 =>
                      have hUB : UB (UB.symm (w ⊗ₜ[Complex] n)) =
                          w ⊗ₜ[Complex] n := by simp
                      have hUC : UC (UC.symm (x ⊗ₜ[Complex] n2)) =
                          x ⊗ₜ[Complex] n2 := by simp
                      simp only [composeUnitaryTransport_toLinearEquiv_apply]
                      rw [tensorAssociatorUnitary_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A H) C D
                        (a ⊗ₜ[Complex] UB.symm (w ⊗ₜ[Complex] n))
                        (UC.symm (x ⊗ₜ[Complex] n2)) d]
                      rw [isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq UB a
                        (UB.symm (w ⊗ₜ[Complex] n))
                        (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d) w n hUB]
                      rw [unitaryLTensor_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A W)
                        (unitaryLTensor N
                          (composeUnitaryTransport (unitaryRTensor UC D)
                            (tensorAssociatorUnitary X N2 D)))
                        (a ⊗ₜ[Complex] w)
                        (n ⊗ₜ[Complex] (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d))]
                      rw [unitaryLTensor_toLinearEquiv_apply_tmul N
                        (composeUnitaryTransport (unitaryRTensor UC D)
                          (tensorAssociatorUnitary X N2 D)) n
                        (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d)]
                      rw [composeUnitaryTransport_toLinearEquiv_apply
                        (unitaryRTensor UC D) (tensorAssociatorUnitary X N2 D)
                        (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d)]
                      rw [unitaryRTensor_toLinearEquiv_apply_tmul UC D
                        (UC.symm (x ⊗ₜ[Complex] n2)) d, hUC]
                      rw [tensorAssociatorUnitary_toLinearEquiv_apply_tmul X N2 D x n2 d]
                      rw [unitaryLTensor_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A W)
                        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm
                        (a ⊗ₜ[Complex] w)
                        (n ⊗ₜ[Complex] (x ⊗ₜ[Complex] (n2 ⊗ₜ[Complex] d)))]
                      rw [tensorAssociatorUnitary_symm_toLinearEquiv_apply_tmul N X
                        (Semantics.CompositeSystem N2 D) n x (n2 ⊗ₜ[Complex] d)]
                      rw [isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq UC
                        (a ⊗ₜ[Complex] UB.symm (w ⊗ₜ[Complex] n))
                        (UC.symm (x ⊗ₜ[Complex] n2)) d x n2 hUC]
                      rw [unitaryRTensor_toLinearEquiv_apply_tmul
                        (isotypicSectorBlockTransportLeft A H W N X UB)
                        (Semantics.CompositeSystem N2 D)
                        ((a ⊗ₜ[Complex] UB.symm (w ⊗ₜ[Complex] n)) ⊗ₜ[Complex] x)
                        (n2 ⊗ₜ[Complex] d)]
                      rw [isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq UB a
                        (UB.symm (w ⊗ₜ[Complex] n)) x w n hUB]
                      rw [tensorAssociatorUnitary_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A W)
                        (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D)
                        (a ⊗ₜ[Complex] w) (n ⊗ₜ[Complex] x)
                        (n2 ⊗ₜ[Complex] d)]
                  | add first second hfirst hsecond =>
                      rw [map_add]
                      rw [TensorProduct.tmul_add, TensorProduct.add_tmul]
                      rw [map_add, map_add]
                      exact congrArg₂ (· + ·) hfirst hsecond
              | add first second hfirst hsecond =>
                  rw [map_add]
                  rw [TensorProduct.tmul_add, TensorProduct.add_tmul,
                    TensorProduct.add_tmul]
                  rw [map_add, map_add]
                  exact congrArg₂ (· + ·) hfirst hsecond
          | add first second hfirst hsecond =>
              rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
              rw [map_add, map_add]
              exact congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          rw [TensorProduct.add_tmul]
          rw [map_add, map_add]
          exact congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hfirst hsecond

end BPTCommutingProjectorModel

end Bounds
end QEC
