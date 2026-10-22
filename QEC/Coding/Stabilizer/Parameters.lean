import QEC.Coding.Stabilizer.Distance

/-!
# Finite binary stabilizer parameters

This module derives stabilizer `[[n, k, d]]` data from a source-valid finite
binary stabilizer code and a fixed independent generator presentation. The
encoded-qubit count is computed from the actual normalizer quotient, rather
than stored as a parameter field.

Downstream internal users should import `QEC.Coding.StabilizerParameters`
directly. It is the supported internal API boundary for this proof slice and
does not require an export from `QEC.lean`.

`SemanticStabilizerDistance` is intentionally not identified with the
operational erasure distance `finiteOperationalErasureDistance`; proving a
relation between them remains a distinct downstream proof obligation.
-/

noncomputable section

namespace QEC
namespace Coding

open PauliSymplectic

universe u v

namespace StabilizerCode

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/--
A fixed finite binary generator family for a source-valid stabilizer code.

The presentation names the actual generated Pauli group of the semantic code,
and its vector representatives are required to be linearly independent.
-/
structure BinaryStabilizerPresentation where
  code : SourceValidBinary ι
  generators : κ → Binary ι
  generated_eq : generatedStabilizerSet generators = code.1.generatedGroup
  independent : LinearIndependent (ZMod 2) (fun j => (generators j).vector)

namespace BinaryStabilizerPresentation

/-- The finite number of physical qubits in the presentation. -/
def blockLength (_P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  Fintype.card ι

/-- The concrete semantic code fixed by the presented binary stabilizer group. -/
def semanticCode (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι) :=
  P.code.1.code

/-- The finite support of a selected physical binary Pauli generator. -/
def generatorSupport (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (j : κ) : Finset ι :=
  support (P.generators j)

/-- The generated semantic code is fixed by every selected concrete Pauli generator. -/
theorem semanticCode_fixed_by_generator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ P.semanticCode.carrier) (j : κ) :
    toQubitOperator (P.generators j) ψ = ψ := by
  have hgenerated : P.generators j ∈ P.code.1.generatedGroup := by
    rw [← P.generated_eq]
    exact GeneratedStabilizer.generator j
  exact (P.code.2.2 ψ).1 hψ (P.generators j) hgenerated

/-- The semantic carrier is exactly the common fixed space of the presented group. -/
theorem mem_semanticCode_carrier_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ P.semanticCode.carrier ↔
      ∀ G, GeneratedStabilizer P.generators G → toQubitOperator G ψ = ψ := by
  rw [semanticCode]
  constructor
  · intro hψ G hG
    apply (P.code.2.2 ψ).1 hψ G
    rw [← P.generated_eq]
    exact hG
  · intro hfixed
    apply (P.code.2.2 ψ).2
    intro G hG
    apply hfixed G
    change G ∈ generatedStabilizerSet P.generators
    rw [P.generated_eq]
    exact hG

/-- The real generated vector subspace is the span of the fixed generator vectors. -/
theorem generatedVectorSubspace_eq_span_generators
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.generatedVectorSubspace =
      Submodule.span (ZMod 2) (Set.range (fun j => (P.generators j).vector)) := by
  apply le_antisymm
  · rintro v ⟨G, hG, rfl⟩
    rw [← P.generated_eq] at hG
    induction hG with
    | one =>
        change (0 : SymplecticVector (ZMod 2) ι) ∈
          Submodule.span (ZMod 2) (Set.range fun j => (P.generators j).vector)
        exact Submodule.zero_mem _
    | generator j =>
        exact Submodule.subset_span ⟨j, rfl⟩
    | mul hP hQ ihP ihQ =>
        exact Submodule.add_mem _ ihP ihQ
    | dagger hG ih =>
        simpa [binaryDagger] using ih
  · refine Submodule.span_le.2 ?_
    rintro v ⟨j, rfl⟩
    have hgenerated : P.generators j ∈ P.code.1.generatedGroup := by
      rw [← P.generated_eq]
      exact GeneratedStabilizer.generator j
    exact ⟨P.generators j, hgenerated, rfl⟩

/-- The stabilizer rank is the finite binary rank of its generated vector subspace. -/
def generatorRank (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  Module.finrank (ZMod 2) P.code.1.generatedVectorSubspace

/-- Independence proves that the generator rank is the number of fixed generators. -/
theorem generatorRank_eq_card
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.generatorRank = Fintype.card κ := by
  rw [generatorRank, P.generatedVectorSubspace_eq_span_generators]
  exact finrank_span_eq_card P.independent

/-- The generated stabilizer is viewed as a subspace of its binary normalizer. -/
def stabilizerInNormalizer (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Submodule (ZMod 2)
      (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) :=
  P.code.1.generatedVectorSubspace.comap
    (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace).subtype

/-- The finite binary normalizer quotient that represents logical Pauli degrees of freedom. -/
abbrev logicalPauliSpace (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :=
  (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) ⧸
    P.stabilizerInNormalizer

/-- The logical Pauli-space dimension is a computed, finite binary dimension. -/
def logicalPauliDimension (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  Module.finrank (ZMod 2) P.logicalPauliSpace

/-- The encoded-qubit count is half the logical Pauli-space dimension. -/
def encodedQubits (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Nat :=
  P.logicalPauliDimension / 2

omit [DecidableEq ι] in
private theorem finrank_symplecticVector :
    Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) =
      2 * Fintype.card ι := by
  rw [(SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).finrank_eq,
    Module.finrank_prod, Module.finrank_pi]
  omega

private theorem generatedVectorSubspace_le_normalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.generatedVectorSubspace ≤
      FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace :=
  P.code.1.generatedVectorSubspace_isotropic

private theorem finrank_stabilizerInNormalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank (ZMod 2) P.stabilizerInNormalizer = P.generatorRank := by
  rw [stabilizerInNormalizer, generatorRank]
  exact (Submodule.comapSubtypeEquivOfLe
    (P.generatedVectorSubspace_le_normalizer)).finrank_eq

private theorem finrank_normalizer
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank (ZMod 2)
      (FiniteSymplectic.form.orthogonal P.code.1.generatedVectorSubspace) =
      2 * P.blockLength - P.generatorRank := by
  rw [LinearMap.BilinForm.finrank_orthogonal FiniteSymplectic.form_nondegenerate,
    finrank_symplecticVector, blockLength, generatorRank]

private theorem generatorRank_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.generatorRank ≤ P.blockLength := by
  have hle := Submodule.finrank_mono P.generatedVectorSubspace_le_normalizer
  rw [P.finrank_normalizer] at hle
  change P.generatorRank ≤ 2 * P.blockLength - P.generatorRank at hle
  omega

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (G : P.code.1.GeneratedGroupElement)
    (hvector : G.1.vector = 0) : G = 1 := by
  by_cases hphase : G.1.phase = 0
  · apply Subtype.ext
    rw [PauliSymplectic.mk.injEq]
    exact ⟨hphase, hvector.trans binaryOne_vector_eq_zero.symm⟩
  · have hphaseOne : G.1.phase = 1 := zmod_two_eq_one_of_ne_zero hphase
    have hsign : G.1 = binarySign (ι := ι) 1 := by
      rw [PauliSymplectic.mk.injEq]
      exact ⟨hphaseOne, hvector.trans (binarySign_vector_eq_zero 1).symm⟩
    exact False.elim (P.code.2.1 (hsign ▸ G.2))

private theorem generatedGroupElement_vector_injective
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Function.Injective (fun G : P.code.1.GeneratedGroupElement => G.1.vector) := by
  intro G H hGH
  have hzero : (G * H⁻¹).1.vector = 0 := by
    change (binaryMul G.1 (binaryDagger H.1)).vector = 0
    have hvector : G.1.vector = H.1.vector := hGH
    have hdouble_zero (a : ZMod 2) : a + a = 0 := by
      by_cases ha : a = 0
      · simp [ha]
      · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
        subst a
        decide
    apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
    ext i
    · simpa [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv,
        binaryMul, binaryDagger, hvector] using hdouble_zero (H.1.vector.xPart i)
    · simpa [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv,
        binaryMul, binaryDagger, hvector] using hdouble_zero (H.1.vector.zPart i)
  have hone := generatedGroupElement_eq_one_of_vector_eq_zero P (G * H⁻¹) hzero
  have hEq := congrArg (fun X : P.code.1.GeneratedGroupElement => X * H) hone
  simpa [mul_assoc] using hEq

private noncomputable def generatedGroupElementVectorEquiv
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.code.1.GeneratedGroupElement ≃ P.code.1.generatedVectorSubspace :=
  Equiv.ofBijective
    (fun G => ⟨G.1.vector, ⟨G.1, G.2, rfl⟩⟩)
    ⟨fun G H hGH => generatedGroupElement_vector_injective P (congrArg Subtype.val hGH), by
      rintro ⟨v, G, hG, hvector⟩
      exact ⟨⟨G, hG⟩, Subtype.ext hvector⟩⟩

/-- The faithful source-valid generated group has cardinality `2^r`. -/
theorem card_generatedGroupElement_eq_two_pow_generatorRank
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Fintype.card P.code.1.GeneratedGroupElement = 2 ^ P.generatorRank := by
  letI : Fintype P.code.1.generatedVectorSubspace :=
    Fintype.ofEquiv P.code.1.GeneratedGroupElement P.generatedGroupElementVectorEquiv
  rw [Fintype.card_congr P.generatedGroupElementVectorEquiv]
  rw [Module.card_eq_pow_finrank (K := ZMod 2)
    (V := P.code.1.generatedVectorSubspace), ZMod.card]
  rfl

/-- The normalized finite stabilizer average on the concrete qubit register. -/
private noncomputable def semanticCodeProjector
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  (Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
    P.code.1.stabilizerAverage

private theorem semanticCodeProjector_isProj
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    LinearMap.IsProj P.semanticCode.carrier P.semanticCodeProjector := by
  constructor
  · intro ψ
    apply (P.code.2.2 _).2
    intro G hG
    let S : P.code.1.GeneratedGroupElement := ⟨G, hG⟩
    change toQubitOperator G
      ((Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
        P.code.1.stabilizerAverage ψ) =
      (Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
        P.code.1.stabilizerAverage ψ
    rw [map_smul]
    congr 1
    have haverage := congrArg
      (fun A : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => A ψ)
      (StabilizerCode.toQubitOperator_mul_stabilizerAverage P.code.1 S)
    simpa [S, Module.End.mul_apply] using haverage
  · intro ψ hψ
    have hcard : (Fintype.card P.code.1.GeneratedGroupElement : Complex) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change (Fintype.card P.code.1.GeneratedGroupElement : Complex)⁻¹ •
      P.code.1.stabilizerAverage ψ = ψ
    have hfixed : ∀ G : P.code.1.GeneratedGroupElement,
        toQubitOperator G.1 ψ = ψ := fun G => (P.code.2.2 ψ).1 hψ G.1 G.2
    rw [StabilizerCode.stabilizerAverage, LinearMap.sum_apply]
    simp_rw [hfixed]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul Complex,
      smul_smul, inv_mul_cancel₀ hcard, one_smul]

private theorem trace_semanticCodeProjector
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) P.semanticCodeProjector =
      (2 ^ (P.blockLength - P.generatorRank) : Nat) := by
  rw [semanticCodeProjector, map_smul, StabilizerCode.trace_stabilizerAverage P.code,
    P.card_generatedGroupElement_eq_two_pow_generatorRank, blockLength]
  have hle := P.generatorRank_le_blockLength
  change P.generatorRank ≤ Fintype.card ι at hle
  have hpow := Nat.pow_sub_mul_pow 2 hle
  rw [← hpow, Nat.cast_mul]
  have hnonzero : ((2 ^ P.generatorRank : Nat) : Complex) ≠ 0 := by
    exact_mod_cast pow_ne_zero P.generatorRank (by omega : 2 ≠ 0)
  rw [smul_eq_mul]
  calc
    (↑((2 : Nat) ^ P.generatorRank) : Complex)⁻¹ *
        (↑((2 : Nat) ^ (Fintype.card ι - P.generatorRank)) *
          ↑((2 : Nat) ^ P.generatorRank)) =
        ((↑((2 : Nat) ^ P.generatorRank) : Complex)⁻¹ *
          ↑((2 : Nat) ^ P.generatorRank)) *
          ↑((2 : Nat) ^ (Fintype.card ι - P.generatorRank)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hnonzero, one_mul]

/--
The actual source-valid common-fixed semantic code carrier has the stabilizer
dimension `2^(n-r)`, derived from its normalized finite group average.
-/
theorem semanticCode_finrank_eq_two_pow_blockLength_sub_generatorRank
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank Complex P.semanticCode.carrier =
      2 ^ (P.blockLength - P.generatorRank) := by
  have hfinrank :
      (Module.finrank Complex P.semanticCode.carrier : Complex) =
        (2 ^ (P.blockLength - P.generatorRank) : Nat) :=
    (P.semanticCodeProjector_isProj.trace).symm.trans P.trace_semanticCodeProjector
  exact_mod_cast hfinrank

/-- The normalizer quotient has exactly twice the encoded-qubit dimension. -/
theorem logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.logicalPauliDimension = 2 * (P.blockLength - P.generatorRank) := by
  have hquot := Submodule.finrank_quotient_add_finrank P.stabilizerInNormalizer
  change Module.finrank (ZMod 2) P.logicalPauliSpace =
    2 * (P.blockLength - P.generatorRank)
  rw [P.finrank_stabilizerInNormalizer, P.finrank_normalizer] at hquot
  have hsum : Module.finrank (ZMod 2) P.logicalPauliSpace + P.generatorRank =
      2 * P.blockLength - P.generatorRank := by
    exact hquot
  have hle := P.generatorRank_le_blockLength
  omega

/--
The fully proved stabilizer parameter bridge: a fixed independent finite binary
stabilizer presentation derives its encoded-qubit count from the real
normalizer quotient and its generator rank.
-/
theorem encodedQubits_eq_blockLength_sub_generatorRank
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits = P.blockLength - P.generatorRank := by
  rw [encodedQubits,
    P.logicalPauliDimension_eq_two_mul_blockLength_sub_generatorRank]
  exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) (Nat.mul_comm _ _)

/-- The semantic common-fixed code carrier has dimension `2^k` for the computed `k`. -/
theorem semanticCode_finrank_eq_two_pow_encodedQubits
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Module.finrank Complex P.semanticCode.carrier = 2 ^ P.encodedQubits := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact P.semanticCode_finrank_eq_two_pow_blockLength_sub_generatorRank

end BinaryStabilizerPresentation

/--
Actual finite binary stabilizer `[[n, k, d]]` data. The distance field is
certified by the semantic stabilizer-distance predicate; `n` and `k` are
computed from the presentation rather than stored as independent parameters.
-/
structure StabilizerParameterData where
  presentation : BinaryStabilizerPresentation (ι := ι) (κ := κ)
  distance : Nat
  semanticDistance : SemanticStabilizerDistance presentation.code distance

namespace StabilizerParameterData

/-- The physical block length of semantic stabilizer parameter data. -/
def blockLength (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  D.presentation.blockLength

/-- The computed logical Pauli-space dimension of semantic stabilizer parameter data. -/
def logicalPauliDimension (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  D.presentation.logicalPauliDimension

/-- The computed encoded-qubit count of semantic stabilizer parameter data. -/
def encodedQubits (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  D.presentation.encodedQubits

/-- The finite complex dimension of the actual semantic common-fixed code carrier. -/
def semanticCodeDimension (D : StabilizerParameterData (ι := ι) (κ := κ)) : Nat :=
  Module.finrank Complex D.presentation.semanticCode.carrier

/-- The `[[n,k,d]]` relation follows from the presentation; it is not record data. -/
theorem encodedQubits_eq_blockLength_sub_generatorRank
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.encodedQubits = D.blockLength - D.presentation.generatorRank :=
  D.presentation.encodedQubits_eq_blockLength_sub_generatorRank

/-- The semantic carrier realizes the computed logical dimension as `2^k`. -/
theorem semanticCodeDimension_eq_two_pow_encodedQubits
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.semanticCodeDimension = 2 ^ D.encodedQubits :=
  D.presentation.semanticCode_finrank_eq_two_pow_encodedQubits

/--
Downstream API for #368, #375, and #384: semantic parameter data supplies the
exact rank-derived encoded-qubit count and actual common-fixed carrier
dimension, while `generatorSupport` exposes the binary Pauli support of every
fixed generator without asserting any successor theorem.
-/
theorem parameter_bridge_for_m4_successors
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.blockLength = Fintype.card ι ∧
      D.encodedQubits = D.blockLength - D.presentation.generatorRank ∧
      D.semanticCodeDimension = 2 ^ D.encodedQubits ∧
      SemanticStabilizerDistance D.presentation.code D.distance := by
  exact ⟨rfl, D.encodedQubits_eq_blockLength_sub_generatorRank,
    D.semanticCodeDimension_eq_two_pow_encodedQubits, D.semanticDistance⟩

end StabilizerParameterData
end StabilizerCode
end Coding
end QEC
