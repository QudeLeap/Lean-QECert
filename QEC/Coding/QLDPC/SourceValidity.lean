import QEC.Coding.QLDPC.Core
/-!
# Source-valid binary CSS stabilizers

This module proves that the independently generated group of binary CSS checks
has the same common fixed space as the declared checks and excludes the negative
identity.
-/

noncomputable section

namespace QEC
namespace Coding

open Classical

universe u w

namespace PauliSymplectic

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A declared stabilizer check belongs to the independently generated group. -/
theorem mem_generatedGroup_of_mem_stabilizers
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P : Binary ι} (hP : P ∈ Q.stabilizers) :
    P ∈ Q.generatedGroup := by
  classical
  unfold StabilizerCode.generatedGroup
  simp only [Set.mem_setOf_eq]
  exact @GeneratedStabilizer.generator ι _
    {S : Binary ι // S ∈ Q.stabilizers} (Fintype.ofFinite _)
    (fun check => check.1) ⟨P, hP⟩

/-- Fixedness under generators extends to their full product-and-adjoint closure. -/
theorem toQubitOperator_fixed_of_generatedStabilizer
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hgenerators : ∀ j, toQubitOperator (generators j) ψ = ψ)
    {P : Binary ι} (hP : GeneratedStabilizer generators P) :
    toQubitOperator P ψ = ψ := by
  induction hP with
  | one => simp [toQubitOperator_one]
  | generator j => exact hgenerators j
  | @mul P Q hP hQ ihP ihQ =>
      rw [toQubitOperator_binaryMul, Module.End.mul_apply, ihQ, ihP]
  | @dagger P hP ihP =>
      rw [toQubitOperator_binaryDagger]
      calc
        LinearMap.adjoint (toQubitOperator P) ψ =
            LinearMap.adjoint (toQubitOperator P) (toQubitOperator P ψ) := by rw [ihP]
        _ = ((LinearMap.adjoint (toQubitOperator P)).comp (toQubitOperator P)) ψ := rfl
        _ = ψ := by rw [toQubitOperator_adjoint_comp_self]; rfl

/-- Testing fixedness on a stabilizer closure is equivalent to testing its generators. -/
theorem fixed_generatedStabilizer_iff_fixed_generators
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι) :
    (∀ P, GeneratedStabilizer generators P → toQubitOperator P ψ = ψ) ↔
      ∀ j, toQubitOperator (generators j) ψ = ψ := by
  constructor
  · intro h j
    exact h (generators j) (.generator j)
  · intro h P hP
    exact toQubitOperator_fixed_of_generatedStabilizer generators h hP

/-- A code's generated group and declared checks have the same common fixed vectors. -/
theorem fixed_generatedGroup_iff_fixed_stabilizers
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (ψ : Semantics.Qubit.QubitRegister ι) :
    (∀ P, P ∈ Q.generatedGroup → toQubitOperator P ψ = ψ) ↔
      ∀ P, P ∈ Q.stabilizers → toQubitOperator P ψ = ψ := by
  constructor
  · intro h P hP
    exact h P (mem_generatedGroup_of_mem_stabilizers Q hP)
  · intro h P hP
    unfold StabilizerCode.generatedGroup at hP
    simp only [Set.mem_setOf_eq] at hP
    induction hP with
    | one => simp [toQubitOperator_one]
    | generator check => exact h check.1 check.2
    | @mul P R hP hR ihP ihR =>
        rw [toQubitOperator_binaryMul, Module.End.mul_apply, ihR, ihP]
    | @dagger P hP ihP =>
        rw [toQubitOperator_binaryDagger]
        calc
          LinearMap.adjoint (toQubitOperator P) ψ =
              LinearMap.adjoint (toQubitOperator P) (toQubitOperator P ψ) := by rw [ihP]
          _ = ((LinearMap.adjoint (toQubitOperator P)).comp (toQubitOperator P)) ψ := rfl
          _ = ψ := by rw [toQubitOperator_adjoint_comp_self]; rfl

/-- Every declared binary CSS check belongs to the independently generated group. -/
theorem binaryCSSCheckSet_subset_generatedGroup
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    binaryCSSCheckSet xCode zCode ≤
      (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup := by
  intro P hP
  apply mem_generatedGroup_of_mem_stabilizers
  simpa [binaryCSSStabilizerCodeOfDualLe] using hP

omit [DecidableEq ι] in
/--
Products and adjoints of dual-contained CSS checks retain trivial phase and
their X/Z components remain in the corresponding classical codes.
-/
theorem generatedStabilizer_css_components
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (hgenerators : ∀ j, generators j ∈ binaryCSSCheckSet xCode zCode)
    {P : Binary ι} (hP : GeneratedStabilizer generators P) :
    P.phase = 0 ∧ P.vector.xPart ∈ xCode.carrier ∧
      P.vector.zPart ∈ zCode.carrier := by
  induction hP with
  | one =>
      exact ⟨rfl, xCode.carrier.zero_mem, zCode.carrier.zero_mem⟩
  | generator j =>
      rcases hgenerators j with ⟨x, hx, hj⟩ | ⟨z, hz, hj⟩
      · rw [hj]
        exact ⟨rfl, hx, zCode.carrier.zero_mem⟩
      · rw [hj]
        exact ⟨rfl, xCode.carrier.zero_mem, hz⟩
  | @mul P Q hP hQ ihP ihQ =>
      rcases ihP with ⟨hPphase, hPx, hPz⟩
      rcases ihQ with ⟨hQphase, hQx, hQz⟩
      have hcross :
          (∑ i, Q.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hQx (hdual hPz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryMul, binaryMulPhase, hPphase, hQphase, hcross]
      · simpa [binaryMul] using xCode.carrier.add_mem hPx hQx
      · simpa [binaryMul] using zCode.carrier.add_mem hPz hQz
  | @dagger P hP ihP =>
      rcases ihP with ⟨hphase, hx, hz⟩
      have hcross :
          (∑ i, P.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hx (hdual hz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryDagger, binaryDaggerPhase, hphase, hcross]
      · simpa [binaryDagger] using hx
      · simpa [binaryDagger] using hz

/--
Every element of a dual-contained CSS generated group retains trivial phase and
has X/Z components in the corresponding classical codes.
-/
theorem binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {P : Binary ι}
    (hP : P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup) :
    P.phase = 0 ∧ P.vector.xPart ∈ xCode.carrier ∧
      P.vector.zPart ∈ zCode.carrier := by
  classical
  unfold StabilizerCode.generatedGroup at hP
  simp only [Set.mem_setOf_eq] at hP
  induction hP with
  | one =>
      exact ⟨rfl, xCode.carrier.zero_mem, zCode.carrier.zero_mem⟩
  | generator check =>
      have hcheck : check.1 ∈ binaryCSSCheckSet xCode zCode := by
        change check.1 ∈ binaryCSSCheckSet xCode zCode
        exact check.2
      rcases hcheck with ⟨x, hx, hcheck⟩ | ⟨z, hz, hcheck⟩
      · rw [hcheck]
        exact ⟨rfl, hx, zCode.carrier.zero_mem⟩
      · rw [hcheck]
        exact ⟨rfl, xCode.carrier.zero_mem, hz⟩
  | @mul P R hP hR ihP ihR =>
      rcases ihP with ⟨hPphase, hPx, hPz⟩
      rcases ihR with ⟨hRphase, hRx, hRz⟩
      have hcross :
          (∑ i, R.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hRx (hdual hPz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryMul, binaryMulPhase, hPphase, hRphase, hcross]
      · simpa [binaryMul] using xCode.carrier.add_mem hPx hRx
      · simpa [binaryMul] using zCode.carrier.add_mem hPz hRz
  | @dagger P hP ihP =>
      rcases ihP with ⟨hphase, hx, hz⟩
      have hcross :
          (∑ i, P.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hx (hdual hz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryDagger, binaryDaggerPhase, hphase, hcross]
      · simpa [binaryDagger] using hx
      · simpa [binaryDagger] using hz

/-- Every element of a dual-contained CSS generated group has trivial phase. -/
theorem binaryCSSStabilizerCodeOfDualLe_generatedGroup_phase_eq_zero
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {P : Binary ι}
    (hP : P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup) :
    P.phase = 0 :=
  (binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
    xCode zCode hdual hP).1

/-- The negative identity is absent from every dual-contained CSS generated group. -/
theorem binarySign_one_not_mem_binaryCSSStabilizerCodeOfDualLe_generatedGroup
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    binarySign (ι := ι) 1 ∉
      (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup := by
  intro hsign
  have hphase :=
    binaryCSSStabilizerCodeOfDualLe_generatedGroup_phase_eq_zero
      xCode zCode hdual hsign
  norm_num [binarySign] at hphase

/-- Dual-contained binary CSS data constructs a source-valid stabilizer code. -/
theorem binaryCSSStabilizerCodeOfDualLe_isSourceValidBinary
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).IsSourceValidBinary := by
  let Q := binaryCSSStabilizerCodeOfDualLe xCode zCode hdual
  constructor
  · exact binarySign_one_not_mem_binaryCSSStabilizerCodeOfDualLe_generatedGroup
      xCode zCode hdual
  · intro ψ
    calc
      ψ ∈ Q.code.carrier ↔
          ∀ P, P ∈ Q.stabilizers → toQubitOperator P ψ = ψ := by
            simp [Q, binaryCSSStabilizerCodeOfDualLe]
      _ ↔ ∀ P, P ∈ Q.generatedGroup → toQubitOperator P ψ = ψ :=
        (fixed_generatedGroup_iff_fixed_stabilizers Q ψ).symm

end PauliSymplectic

namespace ChainComplexData

open PauliSymplectic

/-- A finite binary chain complex induces a source-valid CSS stabilizer code. -/
theorem binaryCSSCode_stabilizer_isSourceValidBinary
    {ι κ C2 : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2) :
    (K.binaryCSSCode).stabilizer.IsSourceValidBinary := by
  simpa [binaryCSSCode] using
    binaryCSSStabilizerCodeOfDualLe_isSourceValidBinary
      K.firstCoboundaryCheckCode K.middleBoundaryCode
      K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual

/-- Package the chain-complex CSS stabilizer together with its proved source validity. -/
noncomputable def binaryCSSSourceValidStabilizer
    {ι κ C2 : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2) :
    StabilizerCode.SourceValidBinary ι :=
  ⟨(K.binaryCSSCode).stabilizer,
    K.binaryCSSCode_stabilizer_isSourceValidBinary⟩

end ChainComplexData
end Coding

namespace QLDPC

open scoped Classical

universe u w

/--
Uniform boundary-row weights and middle-coordinate incidence degrees make a
family of source-valid chain-complex CSS stabilizer codes LDPC.
-/
theorem chainComplexCSSFamily_isLDPC_of_uniform_row_bounds
    {A : Type u} {ι κ lambda : A → Type w}
    [∀ a, Fintype (ι a)]
    [∀ a, Fintype (κ a)] [∀ a, Fintype (lambda a)]
    (K : ∀ a, Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) (κ a))
      (Coding.Word (ZMod 2) (ι a))
      (Coding.Word (ZMod 2) (lambda a)))
    {w : Nat}
    (hrowX : ∀ a k, Coding.HammingWeight
      (Coding.wordLinearMapTranspose (K a).boundary1
        (Pi.single k (1 : ZMod 2))) ≤ w)
    (hrowZ : ∀ a l, Coding.HammingWeight
      ((K a).boundary2 (Pi.single l (1 : ZMod 2))) ≤ w)
    (hdegree : ∀ a q,
      ((chainComplexBoundaryIncidence (K a)).variableSupport q).card ≤ w) :
    IsLDPCStabilizerFamily
      (fun a => (K a).binaryCSSSourceValidStabilizer) := by
  refine ⟨w, fun a => ?_⟩
  refine ⟨chainComplexCSSRowChecks (K a), ?_, ?_, ?_⟩
  · simpa [Coding.ChainComplexData.binaryCSSSourceValidStabilizer] using
      chainComplexCSSRowChecks_generate_stabilizerGroup (K a)
  · intro g hg
    rcases (mem_chainComplexCSSRowChecks (K a) g).1 hg with ⟨c, rfl⟩
    cases c with
    | inl k =>
        rw [chainComplexCSSRowCheck_weight_inl]
        exact hrowX a k
    | inr l =>
        rw [chainComplexCSSRowCheck_weight_inr]
        exact hrowZ a l
  · intro q
    exact (chainComplexCSSRowChecks_qubitCheckDegree_le_incidence (K a) q).trans
      (hdegree a q)

end QLDPC
end QEC
