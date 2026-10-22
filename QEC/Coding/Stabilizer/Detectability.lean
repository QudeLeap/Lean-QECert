import QEC.Semantics.ErrorCorrection.Detectability
import QEC.Coding.Stabilizer.Symplectic
import QEC.Coding.QLDPC.SourceValidity
/-!
# Stabilizer detectability: direct branches

This module connects the source-valid binary stabilizer group to semantic
detectability for the scalar stabilizer branch and the anticommuting branch.
-/

noncomputable section

namespace QEC
namespace Coding

universe u

namespace PauliSymplectic

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Binary commutation is symmetric because the standard form is alternating. -/
theorem commutes_comm (P Q : Binary ι) : Commutes P Q ↔ Commutes Q P := by
  change FiniteSymplectic.form P.vector Q.vector = 0 ↔
    FiniteSymplectic.form Q.vector P.vector = 0
  exact FiniteSymplectic.form_isAlt.isRefl.eq_iff

omit [DecidableEq ι] in
/-- Binary Pauli multiplication is associative in the stored sign convention. -/
theorem binaryMul_assoc (P Q R : Binary ι) :
    binaryMul (binaryMul P Q) R = binaryMul P (binaryMul Q R) := by
  rcases P with ⟨p, ⟨px, pz⟩⟩
  rcases Q with ⟨q, ⟨qx, qz⟩⟩
  rcases R with ⟨r, ⟨rx, rz⟩⟩
  simp [binaryMul, binaryMulPhase]
  constructor
  · simp_rw [mul_add, add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    abel
  · exact ⟨add_assoc _ _ _, add_assoc _ _ _⟩

omit [DecidableEq ι] in
/-- The named binary dagger is also a right inverse. -/
@[simp] theorem binaryMul_binaryDagger_right (P : Binary ι) :
    binaryMul P (binaryDagger P) = binaryOne := by
  rcases P with ⟨phase, ⟨x, z⟩⟩
  have hbit_add_self (a : ZMod 2) : a + a = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
      subst a
      decide
  simp [binaryMul, binaryMulPhase, binaryDagger, binaryDaggerPhase, binaryOne]
  constructor
  · let s : ZMod 2 := ∑ i, x i * z i
    change phase + (phase + s) + s = 0
    calc
      phase + (phase + s) + s = (phase + phase) + (s + s) := by abel
      _ = 0 := by simp [hbit_add_self]
  constructor
  · funext i
    exact hbit_add_self (x i)
  · funext i
    exact hbit_add_self (z i)

/-- A phase-only binary Pauli acts by its stored binary sign scalar. -/
@[simp] theorem toQubitOperator_binarySign (p : ZMod 2) :
    toQubitOperator (binarySign (ι := ι) p) =
      binaryPhaseScalar p •
        (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) := by
  exact toQubitOperator_eq_phase_smul_id_of_vector_eq_zero (by rfl) (by rfl)

end PauliSymplectic

namespace StabilizerCode

open PauliSymplectic

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private theorem binaryOne_mem_generatedGroup
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    binaryOne (ι := ι) ∈ Q.generatedGroup := by
  classical
  letI : Fintype {P : Binary ι // P ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup
  simp only [Set.mem_setOf_eq]
  exact GeneratedStabilizer.one

private theorem binaryMul_mem_generatedGroup
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P R : Binary ι} (hP : P ∈ Q.generatedGroup) (hR : R ∈ Q.generatedGroup) :
    binaryMul P R ∈ Q.generatedGroup := by
  classical
  letI : Fintype {S : Binary ι // S ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup at hP hR ⊢
  simp only [Set.mem_setOf_eq] at hP hR ⊢
  exact GeneratedStabilizer.mul hP hR

/-- The vectors represented by the generated stabilizer form a binary subspace. -/
def generatedVectorSubspace
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι) where
  carrier := {v | ∃ P, P ∈ Q.generatedGroup ∧ P.vector = v}
  zero_mem' := by
    exact ⟨binaryOne, binaryOne_mem_generatedGroup Q, rfl⟩
  add_mem' := by
    rintro _ _ ⟨P, hP, rfl⟩ ⟨R, hR, rfl⟩
    exact ⟨binaryMul P R, binaryMul_mem_generatedGroup Q hP hR, rfl⟩
  smul_mem' := by
    rintro c _ ⟨P, hP, rfl⟩
    by_cases hc : c = 0
    · subst c
      refine ⟨binaryOne, binaryOne_mem_generatedGroup Q, ?_⟩
      rw [zero_smul]
      apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
      simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binaryOne]
    · have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero hc
      subst c
      exact ⟨P, hP, by simp⟩

private theorem commutes_generatedGroup_right_of_mem_stabilizers
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P : Binary ι} (hP : P ∈ Q.stabilizers) {R : Binary ι}
    (hR : R ∈ Q.generatedGroup) : Commutes P R := by
  classical
  letI : Fintype {S : Binary ι // S ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup at hR
  simp only [Set.mem_setOf_eq] at hR
  induction hR with
  | one => exact commutes_binaryOne_right P
  | generator check => exact Q.isotropic P hP check.1 check.2
  | mul _ _ ihP ihR => exact commutes_binaryMul_right ihP ihR
  | dagger _ ihP => exact commutes_binaryDagger_right ihP

/-- The generated stabilizer remains pairwise symplectically commuting. -/
theorem generatedGroup_pairwise_commutes
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P R : Binary ι} (hP : P ∈ Q.generatedGroup) (hR : R ∈ Q.generatedGroup) :
    Commutes P R := by
  classical
  letI : Fintype {S : Binary ι // S ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup at hP
  simp only [Set.mem_setOf_eq] at hP
  induction hP with
  | one => exact (commutes_comm _ _).2 (commutes_binaryOne_right R)
  | generator check =>
      exact commutes_generatedGroup_right_of_mem_stabilizers Q check.2 hR
  | @mul P S _ _ ihP ihS =>
      apply (commutes_comm (binaryMul P S) R).2
      exact commutes_binaryMul_right
        ((commutes_comm P R).1 ihP) ((commutes_comm S R).1 ihS)
  | @dagger P _ ihP =>
      simpa [Commutes, binaryDagger] using ihP

/-- The generated-vector subspace is isotropic. -/
theorem generatedVectorSubspace_isotropic
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Q.generatedVectorSubspace ≤
      FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace := by
  rintro _ ⟨P, hP, rfl⟩ _ ⟨R, hR, rfl⟩
  change FiniteSymplectic.form R.vector P.vector = 0
  exact (commutes_comm P R).1 (generatedGroup_pairwise_commutes Q hP hR)

/-- Membership in the independently generated stabilizer group up to one stored sign. -/
def InGeneratedGroupUpToSign
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) : Prop :=
  ∃ S, S ∈ Q.generatedGroup ∧ BinaryUpToSign E S

/-- The binary normalizer of the independently generated stabilizer group. -/
def InBinaryNormalizer
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) : Prop :=
  ∀ S, S ∈ Q.generatedGroup → Commutes E S

/-- Up-to-sign generated-group membership is exactly vector-subspace membership. -/
theorem vector_mem_generatedVectorSubspace_iff
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    E.vector ∈ Q.generatedVectorSubspace ↔ Q.InGeneratedGroupUpToSign E := by
  constructor
  · rintro ⟨S, hS, hvector⟩
    exact ⟨S, hS, hvector.symm⟩
  · rintro ⟨S, hS, hvector⟩
    exact ⟨S, hS, hvector.symm⟩

/-- Normalizer membership is membership in the generated subspace's orthogonal. -/
theorem vector_mem_orthogonal_iff_inBinaryNormalizer
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    E.vector ∈ FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace ↔
      Q.InBinaryNormalizer E := by
  constructor
  · intro hOrth S hS
    apply (commutes_comm E S).2
    exact hOrth S.vector ⟨S, hS, rfl⟩
  · intro hNormalizer _ hvector
    rcases hvector with ⟨S, hS, rfl⟩
    exact (commutes_comm E S).1 (hNormalizer S hS)

/--
An outside-stabilizer normalizer vector has a normalizer partner with nonzero
symplectic pairing.
-/
theorem exists_inBinaryNormalizer_not_commutes
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {E : Binary ι} (hN : Q.InBinaryNormalizer E)
    (hnotS : ¬ Q.InGeneratedGroupUpToSign E) :
    ∃ F, Q.InBinaryNormalizer F ∧ ¬ Commutes E F := by
  have heOrthogonal :
      E.vector ∈ FiniteSymplectic.form.orthogonal Q.generatedVectorSubspace :=
    (vector_mem_orthogonal_iff_inBinaryNormalizer Q E).2 hN
  have heOutside : E.vector ∉ Q.generatedVectorSubspace := by
    intro he
    exact hnotS ((vector_mem_generatedVectorSubspace_iff Q E).1 he)
  obtain ⟨f, hfOrthogonal, hpair⟩ :=
    FiniteSymplectic.exists_mem_orthogonal_pairing_ne_zero
      Q.generatedVectorSubspace heOrthogonal heOutside
  let F : Binary ι := { phase := 0, vector := f }
  refine ⟨F, ?_, ?_⟩
  · exact (vector_mem_orthogonal_iff_inBinaryNormalizer Q F).1 hfOrthogonal
  · simpa [F, Commutes] using hpair

/-- Failure of code-level normalizer membership has a generated anticommuting witness. -/
theorem not_inBinaryNormalizer_iff_exists_not_commutes
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (E : Binary ι) :
    ¬ Q.InBinaryNormalizer E ↔
      ∃ S, S ∈ Q.generatedGroup ∧ ¬ Commutes E S := by
  classical
  simp [InBinaryNormalizer]

private theorem binaryDagger_mem_generatedGroup
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {S : Binary ι} (hS : S ∈ Q.generatedGroup) :
    binaryDagger S ∈ Q.generatedGroup := by
  classical
  unfold generatedGroup at hS ⊢
  simp only [Set.mem_setOf_eq] at hS ⊢
  exact @GeneratedStabilizer.dagger ι _
    {P : Binary ι // P ∈ Q.stabilizers} (Fintype.ofFinite _)
    (fun check => check.1) S hS

/-- A generated stabilizer element, bundled for finite group averaging. -/
def GeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :=
  {P : Binary ι // P ∈ Q.generatedGroup}

instance instFiniteGeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Finite Q.GeneratedGroupElement :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance instFintypeGeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Fintype Q.GeneratedGroupElement :=
  Fintype.ofFinite _

noncomputable instance instGroupGeneratedGroupElement
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Group Q.GeneratedGroupElement where
  mul P R := ⟨binaryMul P.1 R.1, binaryMul_mem_generatedGroup Q P.2 R.2⟩
  one := ⟨binaryOne, binaryOne_mem_generatedGroup Q⟩
  inv P := ⟨binaryDagger P.1, binaryDagger_mem_generatedGroup Q P.2⟩
  mul_assoc P R S := Subtype.ext (binaryMul_assoc P.1 R.1 S.1)
  one_mul P := Subtype.ext (binaryMul_binaryOne_left P.1)
  mul_one P := Subtype.ext (binaryMul_binaryOne_right P.1)
  inv_mul_cancel P := Subtype.ext (binaryMul_binaryDagger_left P.1)

omit [DecidableEq ι] in
private theorem binaryOne_vector_eq_zero :
    (binaryOne (ι := ι)).vector = (0 : SymplecticVector (ZMod 2) ι) := by
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
  simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binaryOne]

omit [DecidableEq ι] in
private theorem binarySign_vector_eq_zero (p : ZMod 2) :
    (binarySign (ι := ι) p).vector = (0 : SymplecticVector (ZMod 2) ι) := by
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
  simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binarySign]

private theorem generatedGroupElement_eq_one_of_vector_eq_zero
    (Q : SourceValidBinary ι) (P : Q.1.GeneratedGroupElement)
    (hvector : P.1.vector = 0) : P = 1 := by
  by_cases hphase : P.1.phase = 0
  · apply Subtype.ext
    rw [PauliSymplectic.mk.injEq]
    exact ⟨hphase, hvector.trans binaryOne_vector_eq_zero.symm⟩
  · have hphaseOne : P.1.phase = 1 := zmod_two_eq_one_of_ne_zero hphase
    have hsign : P.1 = binarySign (ι := ι) 1 := by
      rw [PauliSymplectic.mk.injEq]
      exact ⟨hphaseOne, hvector.trans (binarySign_vector_eq_zero 1).symm⟩
    exact False.elim (Q.2.1 (hsign ▸ P.2))

private theorem trace_toQubitOperator_eq_zero_of_vector_ne_zero
    {P : Binary ι} (hvector : P.vector ≠ 0) :
    LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (toQubitOperator P) = 0 := by
  have houtside : P.vector ∉ (⊥ : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) := by
    simpa using hvector
  have horthogonal :
      P.vector ∈ FiniteSymplectic.form.orthogonal
        (⊥ : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) := by
    simp
  obtain ⟨r, _hrOrthogonal, hpair⟩ :=
    FiniteSymplectic.exists_mem_orthogonal_pairing_ne_zero
      (⊥ : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι))
      horthogonal houtside
  let R : Binary ι := { phase := 0, vector := r }
  let A := toQubitOperator P
  let B := toQubitOperator R
  let Binv := toQubitOperator (binaryDagger R)
  have hNotCommutes : ¬ Commutes P R := by
    simpa [R, Commutes] using hpair
  have hAB : A * B = -(B * A) := by
    simpa [A, B] using toQubitOperator_anticommute_of_not_commutes P R hNotCommutes
  have hBinvB : Binv * B = 1 := by
    change toQubitOperator (binaryDagger R) * toQubitOperator R = 1
    rw [← toQubitOperator_binaryMul]
    simp [toQubitOperator_one]
  have hBBinv : B * Binv = 1 := by
    change toQubitOperator R * toQubitOperator (binaryDagger R) = 1
    rw [← toQubitOperator_binaryMul]
    simp [toQubitOperator_one]
  let a : Complex := LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) A
  have haNeg : a = -a := by
    calc
      a = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (A * 1) := by
        simp [a]
      _ = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (A * (B * Binv)) := by
        rw [hBBinv]
      _ = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) ((A * B) * Binv) := by
        rw [mul_assoc]
      _ = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (-(B * A) * Binv) := by
        rw [hAB]
      _ = -LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) ((B * A) * Binv) := by
        simp
      _ = -LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (Binv * B * A) := by
        rw [LinearMap.trace_mul_cycle]
      _ = -a := by rw [hBinvB, one_mul]
  have hAdd : a + a = 0 := eq_neg_iff_add_eq_zero.mp haNeg
  have hTwo : (2 : Complex) * a = 0 := by simpa [two_mul] using hAdd
  have haZero : a = 0 := (mul_eq_zero.mp hTwo).resolve_left (by norm_num)
  simpa [a, A] using haZero

/-- The unnormalized finite sum over all generated stabilizer operators. -/
def stabilizerAverage
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  ∑ P : Q.GeneratedGroupElement, toQubitOperator P.1

/-- Left multiplication by a generated stabilizer fixes the finite group sum. -/
theorem toQubitOperator_mul_stabilizerAverage
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (S : Q.GeneratedGroupElement) :
    toQubitOperator S.1 * Q.stabilizerAverage = Q.stabilizerAverage := by
  rw [stabilizerAverage, Finset.mul_sum]
  simp_rw [← toQubitOperator_binaryMul]
  change (∑ P : Q.GeneratedGroupElement, toQubitOperator (S * P).1) =
    ∑ P : Q.GeneratedGroupElement, toQubitOperator P.1
  exact Equiv.sum_comp (Equiv.mulLeft S) (fun P => toQubitOperator P.1)

/-- The stabilizer group sum has the nonzero identity trace. -/
theorem trace_stabilizerAverage
    (Q : SourceValidBinary ι) :
    LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) Q.1.stabilizerAverage =
      (2 ^ Fintype.card ι : Nat) := by
  rw [stabilizerAverage, map_sum]
  rw [Fintype.sum_eq_single (1 : Q.1.GeneratedGroupElement)]
  · change LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι)
      (toQubitOperator (binaryOne (ι := ι))) = _
    rw [toQubitOperator_one, LinearMap.trace_one, Semantics.Qubit.finrank_qubitRegister]
  · intro P hP
    apply trace_toQubitOperator_eq_zero_of_vector_ne_zero
    intro hvector
    exact hP (generatedGroupElement_eq_one_of_vector_eq_zero Q P hvector)

/-- Every source-valid finite binary stabilizer code has a nonzero code vector. -/
theorem exists_nonzero_mem_code (Q : SourceValidBinary ι) :
    ∃ ψ, ψ ∈ Q.1.code.carrier ∧ ψ ≠ 0 := by
  have hAverage : Q.1.stabilizerAverage ≠ 0 := by
    intro hzero
    have htraceZero :
        LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) Q.1.stabilizerAverage = 0 := by
      rw [hzero]
      simp
    rw [trace_stabilizerAverage Q] at htraceZero
    have hpow : ((2 ^ Fintype.card ι : Nat) : Complex) ≠ 0 := by norm_num
    exact hpow htraceZero
  have hExists :
      ∃ φ : Semantics.Qubit.QubitRegister ι, Q.1.stabilizerAverage φ ≠ 0 := by
    by_contra h
    push Not at h
    apply hAverage
    apply LinearMap.ext
    intro φ
    simpa using h φ
  obtain ⟨φ, hφ⟩ := hExists
  let ψ := Q.1.stabilizerAverage φ
  refine ⟨ψ, (Q.2.2 ψ).2 ?_, hφ⟩
  intro P hP
  let S : Q.1.GeneratedGroupElement := ⟨P, hP⟩
  have hfixed := congrArg
    (fun A : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => A φ)
    (toQubitOperator_mul_stabilizerAverage Q.1 S)
  simpa [ψ, S, Module.End.mul_apply] using hfixed

/-- A normalizer Pauli preserves the exact common-fixed code carrier. -/
theorem toQubitOperator_mem_code_of_inBinaryNormalizer
    (Q : SourceValidBinary ι) {P : Binary ι}
    (hN : Q.1.InBinaryNormalizer P)
    {ψ : Semantics.Qubit.QubitRegister ι} (hψ : ψ ∈ Q.1.code.carrier) :
    toQubitOperator P ψ ∈ Q.1.code.carrier := by
  apply (Q.2.2 (toQubitOperator P ψ)).2
  intro S hS
  have hSfix : toQubitOperator S ψ = ψ := ((Q.2.2 ψ).1 hψ) S hS
  have hcommute := toQubitOperator_commute_of_commutes P S (hN S hS)
  calc
    toQubitOperator S (toQubitOperator P ψ) =
        (toQubitOperator S * toQubitOperator P) ψ := by
          simp [Module.End.mul_apply]
    _ = (toQubitOperator P * toQubitOperator S) ψ := by rw [hcommute]
    _ = toQubitOperator P (toQubitOperator S ψ) := by
          simp [Module.End.mul_apply]
    _ = toQubitOperator P ψ := by rw [hSfix]

/-- An interpreted binary Pauli cannot kill a nonzero vector. -/
theorem toQubitOperator_ne_zero_of_ne_zero
    (P : Binary ι) {ψ : Semantics.Qubit.QubitRegister ι} (hψ : ψ ≠ 0) :
    toQubitOperator P ψ ≠ 0 := by
  intro hzero
  have hleft := congrArg
    (fun A : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => A ψ)
    (toQubitOperator_adjoint_comp_self P)
  have : ψ = 0 := by
    simpa [LinearMap.comp_apply, hzero] using hleft.symm
  exact hψ this

/--
For a code-preserving error, the matrix-element detectability scalar is the
actual pointwise scalar action on the code.
-/
theorem scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hdet : Semantics.DetectableOn Q.1.code (toQubitOperator E)) :
    ∃ c : Complex, ∀ ψ, ψ ∈ Q.1.code.carrier →
      toQubitOperator E ψ = c • ψ := by
  rcases hdet with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro ψ hψ
  let d := toQubitOperator E ψ - c • ψ
  have hdmem : d ∈ Q.1.code.carrier := by
    exact Q.1.code.carrier.sub_mem
      (toQubitOperator_mem_code_of_inBinaryNormalizer Q hN hψ)
      (Q.1.code.carrier.smul_mem c hψ)
  have hinner : inner Complex d d = 0 := by
    change inner Complex d (toQubitOperator E ψ - c • ψ) = 0
    rw [inner_sub_right, hc d hdmem ψ hψ]
    rw [inner_smul_right]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)

/-- A logical partner together with a nonzero code witness. -/
theorem exists_normalizer_anticommuting_witness_on_code
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hnotS : ¬ Q.1.InGeneratedGroupUpToSign E) :
    ∃ F ψ,
      Q.1.InBinaryNormalizer F ∧
      ψ ∈ Q.1.code.carrier ∧ ψ ≠ 0 ∧ ¬ Commutes E F := by
  obtain ⟨F, hFN, hNotCommutes⟩ :=
    exists_inBinaryNormalizer_not_commutes Q.1 hN hnotS
  obtain ⟨ψ, hψ, hψne⟩ := exists_nonzero_mem_code Q
  exact ⟨F, ψ, hFN, hψ, hψne, hNotCommutes⟩

/--
A detectable normalizer Pauli of a source-valid binary stabilizer code belongs
to the generated stabilizer up to the stored binary sign.
-/
theorem inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hdet : Semantics.DetectableOn Q.1.code (toQubitOperator E)) :
    Q.1.InGeneratedGroupUpToSign E := by
  by_contra hnotS
  obtain ⟨F, ψ, hFN, hψ, hψne, hNotCommutes⟩ :=
    exists_normalizer_anticommuting_witness_on_code Q E hN hnotS
  obtain ⟨c, hscalar⟩ :=
    scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer Q E hN hdet
  have hFψmem : toQubitOperator F ψ ∈ Q.1.code.carrier :=
    toQubitOperator_mem_code_of_inBinaryNormalizer Q hFN hψ
  have hFψne : toQubitOperator F ψ ≠ 0 :=
    toQubitOperator_ne_zero_of_ne_zero F hψne
  have hanti := toQubitOperator_anticommute_of_not_commutes E F hNotCommutes
  have hcNeg : c • toQubitOperator F ψ = -(c • toQubitOperator F ψ) := by
    calc
      c • toQubitOperator F ψ = toQubitOperator E (toQubitOperator F ψ) :=
        (hscalar (toQubitOperator F ψ) hFψmem).symm
      _ = -(toQubitOperator F (toQubitOperator E ψ)) := by
        have happly := congrArg
          (fun A : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => A ψ) hanti
        simpa [Module.End.mul_apply] using happly
      _ = -(c • toQubitOperator F ψ) := by
        rw [hscalar ψ hψ]
        simp
  have hAdd : c • toQubitOperator F ψ + c • toQubitOperator F ψ = 0 :=
    eq_neg_iff_add_eq_zero.mp hcNeg
  have hTwoSmul : ((2 : Complex) * c) • toQubitOperator F ψ = 0 := by
    simpa [add_smul, two_mul, mul_smul] using hAdd
  have hTwoC : (2 : Complex) * c = 0 :=
    (smul_eq_zero.mp hTwoSmul).resolve_right hFψne
  have hcZero : c = 0 := (mul_eq_zero.mp hTwoC).resolve_left (by norm_num)
  have hEψne : toQubitOperator E ψ ≠ 0 :=
    toQubitOperator_ne_zero_of_ne_zero E hψne
  apply hEψne
  rw [hscalar ψ hψ, hcZero]
  simp

/--
An element of a source-valid generated group, up to one stored sign, acts by
that same sign scalar on every code vector.
-/
theorem scalar_action_on_code_of_inGeneratedGroupUpToSign
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : Q.1.InGeneratedGroupUpToSign E) :
    ∃ p : ZMod 2, ∀ ψ, ψ ∈ Q.1.code.carrier →
      toQubitOperator E ψ = binaryPhaseScalar p • ψ := by
  rcases hE with ⟨S, hS, hUpToSign⟩
  rcases (binaryUpToSign_iff_exists_binarySign E S).1 hUpToSign with ⟨p, hEq⟩
  refine ⟨p, ?_⟩
  intro ψ hψ
  have hSfix : toQubitOperator S ψ = ψ :=
    ((Q.2.2 ψ).1 hψ) S hS
  calc
    toQubitOperator E ψ =
        toQubitOperator (binarySign p) (toQubitOperator S ψ) := by
          rw [hEq, toQubitOperator_binaryMul, Module.End.mul_apply]
    _ = toQubitOperator (binarySign p) ψ := by rw [hSfix]
    _ = binaryPhaseScalar p • ψ := by simp

/--
An error outside the generated-group normalizer has zero matrix elements
between arbitrary vectors in the source-valid code carrier.
-/
theorem matrixElement_eq_zero_of_not_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : ¬ Q.1.InBinaryNormalizer E) :
    ∀ ψ, ψ ∈ Q.1.code.carrier →
      ∀ φ, φ ∈ Q.1.code.carrier →
        inner Complex ψ (toQubitOperator E φ) = 0 := by
  rcases (not_inBinaryNormalizer_iff_exists_not_commutes Q.1 E).1 hE with
    ⟨S, hS, hNotCommutes⟩
  have hSdagger : binaryDagger S ∈ Q.1.generatedGroup :=
    binaryDagger_mem_generatedGroup Q.1 hS
  intro ψ hψ φ hφ
  have hSfixPhi : toQubitOperator S φ = φ :=
    ((Q.2.2 φ).1 hφ) S hS
  have hSdaggerFixPsi : toQubitOperator (binaryDagger S) ψ = ψ :=
    ((Q.2.2 ψ).1 hψ) (binaryDagger S) hSdagger
  let A := toQubitOperator S
  let B := toQubitOperator E
  have hAdjointFixPsi : LinearMap.adjoint A ψ = ψ := by
    change LinearMap.adjoint (toQubitOperator S) ψ = ψ
    rw [adjoint_toQubitOperator_eq_binaryDagger]
    exact hSdaggerFixPsi
  have hAnticommutes : B * A = -(A * B) := by
    simpa [A, B] using
      toQubitOperator_anticommute_of_not_commutes E S hNotCommutes
  have hErrorAction : B φ = -A (B φ) := by
    have hApply := congrArg
      (fun T : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => T φ)
      hAnticommutes
    simpa [A, Module.End.mul_apply, hSfixPhi] using hApply
  let a : Complex := inner Complex ψ (B φ)
  have haNeg : a = -a := by
    calc
      a = inner Complex ψ (-A (B φ)) := by
        exact congrArg (fun v => inner Complex ψ v) hErrorAction
      _ = -inner Complex ψ (A (B φ)) := by simp
      _ = -inner Complex (LinearMap.adjoint A ψ) (B φ) := by
        rw [← LinearMap.adjoint_inner_left]
      _ = -a := by rw [hAdjointFixPsi]
  have hAdd : a + a = 0 := eq_neg_iff_add_eq_zero.mp haNeg
  have hTwo : (2 : Complex) * a = 0 := by
    simpa [two_mul] using hAdd
  have haZero : a = 0 := (mul_eq_zero.mp hTwo).resolve_left (by norm_num)
  simpa [a, B] using haZero

/-- The generated-group-up-to-sign branch is semantically detectable. -/
theorem detectableOn_of_inGeneratedGroupUpToSign
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : Q.1.InGeneratedGroupUpToSign E) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) := by
  rcases scalar_action_on_code_of_inGeneratedGroupUpToSign Q E hE with
    ⟨p, hScalar⟩
  refine ⟨binaryPhaseScalar p, ?_⟩
  intro ψ hψ φ hφ
  rw [hScalar φ hφ]
  simp

/-- The outside-normalizer branch is semantically detectable with scalar zero. -/
theorem detectableOn_of_not_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : ¬ Q.1.InBinaryNormalizer E) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) := by
  refine ⟨0, ?_⟩
  intro ψ hψ φ hφ
  rw [matrixElement_eq_zero_of_not_inBinaryNormalizer Q E hE ψ hψ φ hφ]
  simp

/--
A source-valid binary stabilizer code detects exactly the errors that belong to
the generated stabilizer up to the stored sign or lie outside its normalizer.
-/
theorem detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
    (Q : SourceValidBinary ι) (E : Binary ι) :
    Semantics.DetectableOn Q.1.code (toQubitOperator E) ↔
      Q.1.InGeneratedGroupUpToSign E ∨ ¬ Q.1.InBinaryNormalizer E := by
  constructor
  · intro hdet
    by_cases hN : Q.1.InBinaryNormalizer E
    · exact Or.inl
        (inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer Q E hN hdet)
    · exact Or.inr hN
  · rintro (hGenerated | hOutside)
    · exact detectableOn_of_inGeneratedGroupUpToSign Q E hGenerated
    · exact detectableOn_of_not_inBinaryNormalizer Q E hOutside

end StabilizerCode
end Coding
end QEC
