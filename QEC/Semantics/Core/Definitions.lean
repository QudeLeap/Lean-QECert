import Mathlib

/-!
# QEC.Semantics

Finite-dimensional semantic foundations for exact quantum error correction.

This module reserves the public namespace for finite systems, operators,
density operators, quantum channels, codes, correctability, and
Knill-Laflamme-style statements.
-/

universe u

namespace QEC
namespace Semantics

open scoped TensorProduct ComplexOrder

/-- A finite quantum system is a finite-dimensional complex inner-product space. -/
abbrev FiniteQuantumSystem (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] : Prop :=
  FiniteDimensional Complex H

/-- Linear operators on a finite quantum system. -/
abbrev Operator (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Type u :=
  Module.End Complex H

example (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Operator H = Module.End Complex H := rfl

noncomputable example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) : Complex :=
  LinearMap.trace Complex H A

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) : Prop :=
  LinearMap.IsPositive A

/-- A density operator is a positive operator with trace one. -/
structure DensityOperator (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] where
  toOperator : Operator H
  positive : LinearMap.IsPositive toOperator
  trace_one : LinearMap.trace Complex H toOperator = 1

namespace DensityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

instance : Coe (DensityOperator H) (Operator H) where
  coe rho := rho.toOperator

theorem positive_toOperator (rho : DensityOperator H) :
    LinearMap.IsPositive rho.toOperator :=
  rho.positive

theorem trace_toOperator (rho : DensityOperator H) :
    LinearMap.trace Complex H rho.toOperator = 1 :=
  rho.trace_one

example : DensityOperator H → Operator H := fun rho => rho

end DensityOperator

/--
A positive trace-preserving operator map is weaker support vocabulary.

Complete positivity is intentionally not asserted here, so this structure is
not a quantum channel or CPTP theorem witness.
-/
structure PositiveTracePreservingMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toPositiveMap : Operator H →ₚ[Complex] Operator K
  trace_preserving : ∀ A : Operator H,
    LinearMap.trace Complex K (toPositiveMap A) = LinearMap.trace Complex H A

namespace PositiveTracePreservingMap

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

noncomputable instance : CoeFun (PositiveTracePreservingMap H K)
    (fun _ => Operator H → Operator K) where
  coe Φ := Φ.toPositiveMap

theorem trace_map (Φ : PositiveTracePreservingMap H K) (A : Operator H) :
    LinearMap.trace Complex K (Φ A) = LinearMap.trace Complex H A :=
  Φ.trace_preserving A

theorem map_positive (Φ : PositiveTracePreservingMap H K) {A : Operator H}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (Φ A) := by
  rw [← LinearMap.nonneg_iff_isPositive] at hA ⊢
  exact PositiveLinearMap.map_nonneg Φ.toPositiveMap hA

noncomputable example {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] : PositiveTracePreservingMap H K → Operator H → Operator K :=
  fun Φ => Φ

end PositiveTracePreservingMap

/-- Block matrices whose entries are operators on a finite quantum system. -/
abbrev OperatorMatrix (n : Nat) (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Type u :=
  Matrix (Fin n) (Fin n) (Operator H)

namespace OperatorMatrix

variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/--
Positivity of a finite block operator matrix, expressed by adjoint symmetry and
nonnegative quadratic forms over finite vectors of system states.
-/
def IsPositive (M : OperatorMatrix n H) : Prop :=
  (∀ i j : Fin n, M j i = LinearMap.adjoint (M i j)) ∧
    ∀ x : Fin n → H,
      0 ≤ Complex.re (∑ i : Fin n, ∑ j : Fin n, inner Complex (M i j (x j)) (x i))

/-- The scalar matrix obtained from a block operator matrix in an orthonormal basis. -/
noncomputable abbrev scalarMatrix {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (b : OrthonormalBasis β Complex H) :
    Matrix (Fin n × β) (Fin n × β) Complex :=
  fun ip jq => inner Complex (M ip.1 jq.1 (b jq.2)) (b ip.2)

/-- The scalar matrix associated to a positive block operator matrix is Hermitian. -/
theorem scalarMatrix_isHermitian {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (hM : IsPositive M)
    (b : OrthonormalBasis β Complex H) :
    (scalarMatrix M b).IsHermitian := by
  classical
  refine Matrix.IsHermitian.ext ?_
  rintro ⟨i, p⟩ ⟨j, q⟩
  simp [scalarMatrix, hM.1 i j, LinearMap.adjoint_inner_right]

/--
The scalar quadratic form is the block quadratic form evaluated on the vector
whose basis coefficients are the conjugates of the scalar test vector.
-/
theorem scalarMatrix_quadratic_eq_block {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (b : OrthonormalBasis β Complex H)
    (c : Fin n × β → Complex) :
    dotProduct (star c) ((scalarMatrix M b).mulVec c) =
      ∑ i : Fin n, ∑ j : Fin n,
        inner Complex (M i j (∑ q : β, star (c (j, q)) • b q))
          (∑ p : β, star (c (i, p)) • b p) := by
  classical
  let F : Fin n → β → Fin n → β → Complex :=
    fun i p j q => c (j, q) * (inner Complex (M i j (b q)) (b p) * star (c (i, p)))
  calc
    dotProduct (star c) ((scalarMatrix M b).mulVec c) =
        ∑ i : Fin n, ∑ p : β, ∑ j : Fin n, ∑ q : β, F i p j q := by
      simp [F, scalarMatrix, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
        Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ p : β, ∑ q : β, F i p j q := by
      apply Finset.sum_congr rfl
      intro _i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        inner Complex (M i j (∑ q : β, star (c (j, q)) • b q))
          (∑ p : β, star (c (i, p)) • b p) := by
      simp [F, map_sum, Finset.sum_mul, mul_assoc, mul_comm]

/--
Positive block operator matrices scalarize to ordinary finite positive
semidefinite matrices after choosing an orthonormal basis.
-/
theorem isPositive_to_scalar_posSemidef {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (hM : IsPositive M)
    (b : OrthonormalBasis β Complex H) :
    (scalarMatrix M b).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (scalarMatrix_isHermitian M hM b) ?_
  intro c
  rw [RCLike.nonneg_iff]
  constructor
  · rw [scalarMatrix_quadratic_eq_block]
    exact hM.2 (fun i => ∑ p : β, star (c (i, p)) • b p)
  · exact Matrix.IsHermitian.im_star_dotProduct_mulVec_self
      (scalarMatrix_isHermitian M hM b) c

/-- Entrywise action of an operator-space linear map on block matrices. -/
def map (Φ : Operator H →ₗ[Complex] Operator K) (M : OperatorMatrix n H) :
    OperatorMatrix n K :=
  fun i j => Φ (M i j)

end OperatorMatrix

/--
Complete positivity for finite-dimensional operator maps.

This is the matrix-amplification definition: every positive finite block
operator matrix over `H` remains positive after applying the map entrywise.
-/
def CompletelyPositive {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Φ : Operator H →ₗ[Complex] Operator K) : Prop :=
  ∀ (n : Nat) (M : OperatorMatrix n H),
    OperatorMatrix.IsPositive M → OperatorMatrix.IsPositive (OperatorMatrix.map Φ M)

/-- A completely positive trace-preserving quantum channel. -/
structure QuantumChannel (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toLinearMap : Operator H →ₗ[Complex] Operator K
  completely_positive : CompletelyPositive toLinearMap
  trace_preserving : ∀ A : Operator H,
    LinearMap.trace Complex K (toLinearMap A) = LinearMap.trace Complex H A

namespace QuantumChannel

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

noncomputable instance : CoeFun (QuantumChannel H K)
    (fun _ => Operator H → Operator K) where
  coe Φ := Φ.toLinearMap

theorem matrix_map_positive (Φ : QuantumChannel H K) (n : Nat) (M : OperatorMatrix n H)
    (hM : OperatorMatrix.IsPositive M) :
    OperatorMatrix.IsPositive (OperatorMatrix.map Φ.toLinearMap M) :=
  Φ.completely_positive n M hM

theorem trace_map (Φ : QuantumChannel H K) (A : Operator H) :
    LinearMap.trace Complex K (Φ A) = LinearMap.trace Complex H A :=
  Φ.trace_preserving A

noncomputable example {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] : QuantumChannel H K → Operator H → Operator K :=
  fun Φ => Φ

end QuantumChannel

/-- The composite system of two finite quantum systems, modeled by Mathlib's tensor product. -/
abbrev CompositeSystem (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] : Type u :=
  H ⊗[Complex] K

/--
The raw finite-dimensional right partial trace, tracing out the second tensor
factor of `H ⊗ K`.

This definition constructs only the underlying linear operator map. Positivity,
trace preservation, complete positivity, CPTP status, and density preservation
are separate proof obligations.
-/
noncomputable def partialTraceRightRaw (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator H :=
  let unwrap :
      Operator (CompositeSystem H K) →ₗ[Complex]
        Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K :=
    (dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).symm.toLinearMap
  let splitDual :
      Module.Dual Complex (CompositeSystem H K) →ₗ[Complex]
        Module.Dual Complex H ⊗[Complex] Module.Dual Complex K :=
    (TensorProduct.dualDistribEquiv Complex H K).symm.toLinearMap
  let split :
      Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K →ₗ[Complex]
        (Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K) :=
    TensorProduct.map splitDual
      (LinearMap.id : CompositeSystem H K →ₗ[Complex] CompositeSystem H K)
  let commute :
      (Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K) →ₗ[Complex]
        (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex]
          (Module.Dual Complex K ⊗[Complex] K) :=
    (TensorProduct.tensorTensorTensorComm Complex
      (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap
  let contractK :
      (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex]
          (Module.Dual Complex K ⊗[Complex] K) →ₗ[Complex]
        (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex] Complex :=
    TensorProduct.map
      (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
        Module.Dual Complex H ⊗[Complex] H)
      (contractLeft Complex K)
  let dropScalar :
      (Module.Dual Complex H ⊗[Complex] H) ⊗[Complex] Complex →ₗ[Complex]
        Module.Dual Complex H ⊗[Complex] H :=
    (TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap
  let rewrap : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex] Operator H :=
    (dualTensorHomEquiv Complex H H).toLinearMap
  rewrap.comp (dropScalar.comp (contractK.comp (commute.comp (split.comp unwrap))))

private noncomputable def tensorRight (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k : K) : H →ₗ[Complex] CompositeSystem H K :=
  (TensorProduct.mk Complex H K).flip k

private theorem tensorRight_adjoint_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k k' : K) (h : H) :
    LinearMap.adjoint (tensorRight H K k) (h ⊗ₜ[Complex] k') =
      (inner Complex k k') • h := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [tensorRight, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

private noncomputable def partialTraceRightCompression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator H :=
  let bK := stdOrthonormalBasis Complex K
  ∑ i : Fin (Module.finrank Complex K),
    let S := tensorRight H K (bK i)
    { toFun := fun A => (LinearMap.adjoint S).comp (A.comp S)
      map_add' := by
        intro A B
        ext x
        simp [LinearMap.comp_apply, map_add]
      map_smul' := by
        intro c A
        ext x
        simp [LinearMap.comp_apply] }

private theorem dual_apply_sum_stdOrthonormalBasis (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (ψ : Module.Dual Complex K) (k : K) :
    (∑ i : Fin (Module.finrank Complex K),
        ψ ((stdOrthonormalBasis Complex K) i) *
          inner Complex ((stdOrthonormalBasis Complex K) i) k) =
      ψ k := by
  let bK := stdOrthonormalBasis Complex K
  calc
    (∑ i : Fin (Module.finrank Complex K), ψ (bK i) * inner Complex (bK i) k)
        = ∑ i : Fin (Module.finrank Complex K), ψ (inner Complex (bK i) k • bK i) := by
          simp [bK, map_smul, mul_comm]
    _ = ψ (∑ i : Fin (Module.finrank Complex K), inner Complex (bK i) k • bK i) := by
          simp [map_sum]
    _ = ψ k := by
          rw [OrthonormalBasis.sum_repr']

private theorem partialTraceRightRaw_contract_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (contractLeft Complex H).comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap))
      =
    (contractLeft Complex (CompositeSystem H K)).comp
      (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
        (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap := by
  apply TensorProduct.ext
  ext φ ψ h k
  simp [mul_comm]

/--
The raw right partial trace preserves trace.

This is proved directly from the tensor contraction defining
`partialTraceRightRaw`; it does not use the `PartialTraceRight` contract fields.
-/
theorem partialTraceRightRaw_trace_preserving (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator (CompositeSystem H K)) :
    LinearMap.trace Complex H ((partialTraceRightRaw H K) A) =
      LinearMap.trace Complex (CompositeSystem H K) A := by
  let eC := dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)
  let x := eC.symm A
  have hA : A = eC x := by
    simp [x, eC]
  rw [hA]
  let splitMap :
      (Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K) →ₗ[Complex]
        ((Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K)) :=
    TensorProduct.map (TensorProduct.dualDistribEquiv Complex H K).symm.toLinearMap
      (LinearMap.id : CompositeSystem H K →ₗ[Complex] CompositeSystem H K)
  have h_contract :=
    congrArg (fun f => f (splitMap x)) (partialTraceRightRaw_contract_split H K)
  simpa [partialTraceRightRaw, eC, splitMap, LinearMap.trace_eq_contract_apply,
    LinearMap.comp_apply, TensorProduct.map_map] using h_contract

private theorem partialTraceRightRaw_split_eq_compression_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    ((dualTensorHomEquiv Complex H H).toLinearMap.comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap)))
      =
    (partialTraceRightCompression H K).comp
      ((dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).toLinearMap.comp
        (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
          (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap) := by
  apply TensorProduct.ext
  ext φ ψ h k z
  simp [partialTraceRightCompression, tensorRight_adjoint_tmul, LinearMap.comp_apply,
    dualTensorHomEquiv, dualTensorHom_apply]
  rw [← dual_apply_sum_stdOrthonormalBasis H K ψ k]
  simp [tensorRight, Finset.mul_sum, Finset.sum_smul, mul_comm, mul_assoc, smul_smul]

private theorem partialTraceRightRaw_eq_compression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    partialTraceRightRaw H K = partialTraceRightCompression H K := by
  apply LinearMap.ext
  intro A
  let eC := dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)
  let x := eC.symm A
  have hA : A = eC x := by
    simp [x, eC]
  rw [hA]
  let splitMap :
      (Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K) →ₗ[Complex]
        ((Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K)) :=
    TensorProduct.map (TensorProduct.dualDistribEquiv Complex H K).symm.toLinearMap
      (LinearMap.id : CompositeSystem H K →ₗ[Complex] CompositeSystem H K)
  have h_split :=
    congrArg (fun f => f (splitMap x)) (partialTraceRightRaw_split_eq_compression_split H K)
  simpa [partialTraceRightRaw, eC, splitMap, LinearMap.comp_apply, TensorProduct.map_map] using h_split

/--
Tracing out the right factor of a local operator tensored with the identity
multiplies it by the dimension of that factor.

This is the finite-dimensional normalization law used by coordinate-subsystem
interfaces.  It follows from the concrete orthonormal-basis compression
construction of `partialTraceRightRaw`.
-/
theorem partialTraceRightRaw_tensor_id (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) :
    (partialTraceRightRaw H K)
        (TensorProduct.map A (LinearMap.id : K →ₗ[Complex] K)) =
      (Module.finrank Complex K : Complex) • A := by
  rw [partialTraceRightRaw_eq_compression]
  ext h
  simp only [partialTraceRightCompression, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.coe_mk]
  change
    (∑ i : Fin (Module.finrank Complex K),
      LinearMap.adjoint
        (tensorRight H K ((stdOrthonormalBasis Complex K) i))
        (A h ⊗ₜ[Complex] (stdOrthonormalBasis Complex K) i)) =
      (Module.finrank Complex K : Complex) • A h
  simp [tensorRight_adjoint_tmul]
  rw [Nat.cast_smul_eq_nsmul]

/--
The raw right partial trace maps positive composite-system operators to
positive operators on the remaining tensor factor.

This is proved by evaluating `partialTraceRightRaw` as a finite sum of
orthonormal-basis compressions and applying positivity of adjoint conjugation.
It does not use the `PartialTraceRight` contract fields.
-/
theorem partialTraceRightRaw_positive (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {A : Operator (CompositeSystem H K)}
    (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive ((partialTraceRightRaw H K) A) := by
  rw [partialTraceRightRaw_eq_compression]
  let T : Fin (Module.finrank Complex K) → Operator H :=
    fun i =>
      let S := tensorRight H K ((stdOrthonormalBasis Complex K) i)
      LinearMap.adjoint S ∘ₗ A ∘ₗ S
  have hT : ∀ i ∈ Finset.univ, LinearMap.IsPositive (T i) := by
    intro i hi
    simp [T]
    exact hA.adjoint_conj (tensorRight H K ((stdOrthonormalBasis Complex K) i))
  have hsum : LinearMap.IsPositive (∑ i, T i) := by
    simpa using LinearMap.isPositive_sum (Finset.univ) hT
  simpa [partialTraceRightCompression, T] using hsum

/--
The raw right partial trace is completely positive.

The proof works at every finite matrix amplification size. It rewrites
`partialTraceRightRaw` as a finite sum of orthonormal-basis compressions, then
expresses each block quadratic form as a finite sum of nonnegative pulled-back
quadratic forms for the original positive block matrix.
-/
theorem partialTraceRightRaw_completely_positive (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    CompletelyPositive (partialTraceRightRaw H K) := by
  classical
  rw [partialTraceRightRaw_eq_compression]
  intro n M hM
  constructor
  · intro i j
    ext x
    simp [OperatorMatrix.map, partialTraceRightCompression, hM.1 i j, LinearMap.adjoint_comp]
  · intro x
    let bK := stdOrthonormalBasis Complex K
    have hQuadratic :
        Complex.re (∑ i : Fin n, ∑ j : Fin n,
          inner Complex
            ((OperatorMatrix.map (partialTraceRightCompression H K) M) i j (x j))
            (x i)) =
        ∑ a : Fin (Module.finrank Complex K), Complex.re
          (∑ i : Fin n, ∑ j : Fin n,
            inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
              ((tensorRight H K (bK a)) (x i))) := by
      calc
        Complex.re (∑ i : Fin n, ∑ j : Fin n,
          inner Complex
            ((OperatorMatrix.map (partialTraceRightCompression H K) M) i j (x j))
            (x i))
            = Complex.re (∑ i : Fin n, ∑ j : Fin n,
                ∑ a : Fin (Module.finrank Complex K),
                  inner Complex
                    ((LinearMap.adjoint (tensorRight H K (bK a)))
                      (M i j ((tensorRight H K (bK a)) (x j))))
                    (x i)) := by
              simp [OperatorMatrix.map, partialTraceRightCompression, bK]
        _ = Complex.re (∑ i : Fin n, ∑ j : Fin n,
                ∑ a : Fin (Module.finrank Complex K),
                  inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
                    ((tensorRight H K (bK a)) (x i))) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro a _ha
              exact LinearMap.adjoint_inner_left (𝕜 := Complex)
                (tensorRight H K (bK a)) (x i)
                (M i j ((tensorRight H K (bK a)) (x j)))
        _ = Complex.re (∑ a : Fin (Module.finrank Complex K),
                ∑ i : Fin n, ∑ j : Fin n,
                  inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
                    ((tensorRight H K (bK a)) (x i))) := by
              congr 1
              calc
                (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin (Module.finrank Complex K),
                  inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
                    ((tensorRight H K (bK a)) (x i)))
                    = ∑ i : Fin n, ∑ a : Fin (Module.finrank Complex K),
                  ∑ j : Fin n,
                  inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
                    ((tensorRight H K (bK a)) (x i)) := by
                      apply Finset.sum_congr rfl
                      intro i _hi
                      rw [Finset.sum_comm]
                _ = ∑ a : Fin (Module.finrank Complex K), ∑ i : Fin n, ∑ j : Fin n,
                  inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
                    ((tensorRight H K (bK a)) (x i)) := by
                      rw [Finset.sum_comm]
        _ = ∑ a : Fin (Module.finrank Complex K), Complex.re
          (∑ i : Fin n, ∑ j : Fin n,
            inner Complex (M i j ((tensorRight H K (bK a)) (x j)))
              ((tensorRight H K (bK a)) (x i))) := by
              rw [Complex.re_sum]
    rw [hQuadratic]
    exact Finset.sum_nonneg (by
      intro a _ha
      exact hM.2 (fun i : Fin n => (tensorRight H K (bK a)) (x i)))

/--
The right partial trace interface traces out the second tensor factor.

This is a property contract for a supplied partial-trace map: it records the
positivity and trace-preservation properties needed by M2. The raw construction
`partialTraceRightRaw` above is not promoted to this contract until those
properties are proved separately.
-/
structure PartialTraceRight (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toMap : Operator (CompositeSystem H K) →ₗ[Complex] Operator H
  map_positive : ∀ {A : Operator (CompositeSystem H K)},
    LinearMap.IsPositive A → LinearMap.IsPositive (toMap A)
  trace_preserving : ∀ A : Operator (CompositeSystem H K),
    LinearMap.trace Complex H (toMap A) = LinearMap.trace Complex (CompositeSystem H K) A

namespace PartialTraceRight

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

noncomputable instance : CoeFun (PartialTraceRight H K)
    (fun _ => Operator (CompositeSystem H K) → Operator H) where
  coe tr := tr.toMap

theorem trace_map (tr : PartialTraceRight H K) (A : Operator (CompositeSystem H K)) :
    LinearMap.trace Complex H (tr A) = LinearMap.trace Complex (CompositeSystem H K) A :=
  tr.trace_preserving A

theorem map_positive_operator (tr : PartialTraceRight H K) {A : Operator (CompositeSystem H K)}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (tr A) :=
  tr.map_positive hA

noncomputable def mapDensity (tr : PartialTraceRight H K)
    (rho : DensityOperator (CompositeSystem H K)) : DensityOperator H where
  toOperator := tr rho.toOperator
  positive := tr.map_positive rho.positive
  trace_one := by
    rw [tr.trace_map, rho.trace_one]

end PartialTraceRight

/-- A quantum code is a code subspace of a finite quantum system. -/
structure QuantumCode (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] where
  carrier : Submodule Complex H

namespace QuantumCode

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

instance : Coe (QuantumCode H) (Submodule Complex H) where
  coe C := C.carrier

theorem mem_carrier (C : QuantumCode H) {v : H} :
    v ∈ C.carrier ↔ v ∈ (C : Submodule Complex H) :=
  Iff.rfl

/-- The semantic dimension of a quantum code is the finrank of its carrier subspace. -/
noncomputable def dimension (C : QuantumCode H) : Nat :=
  Module.finrank Complex C.carrier

/-- Unfolding lemma for the semantic quantum-code dimension. -/
@[simp]
theorem dimension_eq_finrank_carrier (C : QuantumCode H) :
    C.dimension = Module.finrank Complex C.carrier :=
  rfl

end QuantumCode

namespace DensityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/-- A density operator is supported on a code when its range lies in the code carrier. -/
def SupportedOn (C : QuantumCode H) (rho : DensityOperator H) : Prop :=
  ∀ v : H, rho.toOperator v ∈ C.carrier

end DensityOperator

/--
Exact semantic correctability for a code and a specified noise/recovery pair.

The noise and recovery channels may use an intermediate finite system. The
statement stays in the M2 semantic vocabulary: code support is expressed through
`DensityOperator.SupportedOn`, and channels use `QuantumChannel`.
-/
def Correctable (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (C : QuantumCode H) (noise : QuantumChannel H K)
    (recovery : QuantumChannel K H) : Prop :=
  ∀ rho : DensityOperator H,
    DensityOperator.SupportedOn C rho →
      recovery (noise rho.toOperator) = rho.toOperator

/--
The Knill-Laflamme matrix-element criterion over a chosen set of error operators.

This is the M2 criterion surface, not a theorem equating it with correctability.
Source-backed equivalence statements can be added later without changing the
code, channel, or density-operator vocabulary.
-/
def KnillLaflammeCriterion (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (errors : Set (Operator H)) : Prop :=
  ∃ scalar : Operator H → Operator H → Complex,
    ∀ ⦃E : Operator H⦄, E ∈ errors →
      ∀ ⦃F : Operator H⦄, F ∈ errors →
        ∀ x : H, x ∈ C.carrier →
          ∀ y : H, y ∈ C.carrier →
            inner Complex (E x) (F y) = scalar E F * inner Complex x y

/-- A unitary transport between finite quantum systems. -/
structure UnitaryTransport (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  toLinearEquiv : H ≃ₗ[Complex] K
  map_inner : ∀ x y : H,
    inner Complex (toLinearEquiv x) (toLinearEquiv y) = inner Complex x y

namespace UnitaryTransport

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

instance : CoeFun (UnitaryTransport H K) (fun _ => H → K) where
  coe U := U.toLinearEquiv

/-- The inverse unitary transport. -/
noncomputable def symm (U : UnitaryTransport H K) : UnitaryTransport K H where
  toLinearEquiv := U.toLinearEquiv.symm
  map_inner := by
    intro x y
    simpa using (U.map_inner (U.toLinearEquiv.symm x) (U.toLinearEquiv.symm y)).symm

@[simp]
theorem symm_toLinearEquiv (U : UnitaryTransport H K) :
    U.symm.toLinearEquiv = U.toLinearEquiv.symm :=
  rfl

/-- Transport an operator by unitary conjugation. -/
noncomputable def conjOperator (U : UnitaryTransport H K) (A : Operator H) : Operator K :=
  U.toLinearEquiv.toLinearMap.comp (A.comp U.toLinearEquiv.symm.toLinearMap)

/-- Upgrade a unitary transport to Mathlib's linear isometric equivalence. -/
noncomputable def toLinearIsometryEquiv (U : UnitaryTransport H K) : H ≃ₗᵢ[Complex] K :=
  U.toLinearEquiv.isometryOfInner U.map_inner

@[simp]
theorem toLinearIsometryEquiv_toLinearEquiv (U : UnitaryTransport H K) :
    U.toLinearIsometryEquiv.toLinearEquiv = U.toLinearEquiv :=
  rfl

@[simp]
theorem toLinearIsometryEquiv_toLinearMap (U : UnitaryTransport H K) :
    U.toLinearIsometryEquiv.toLinearMap = U.toLinearEquiv.toLinearMap :=
  rfl

theorem adjoint_toLinearMap (U : UnitaryTransport H K) :
    LinearMap.adjoint U.toLinearEquiv.toLinearMap = U.toLinearEquiv.symm.toLinearMap := by
  simpa [toLinearIsometryEquiv] using
    (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm U.toLinearIsometryEquiv)

theorem adjoint_symm_toLinearMap (U : UnitaryTransport H K) :
    LinearMap.adjoint U.toLinearEquiv.symm.toLinearMap = U.toLinearEquiv.toLinearMap := by
  simpa [toLinearIsometryEquiv, LinearIsometryEquiv.toLinearEquiv_symm] using
    (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm U.toLinearIsometryEquiv.symm)

theorem conjOperator_eq_linearEquiv_conj (U : UnitaryTransport H K) (A : Operator H) :
    U.conjOperator A = U.toLinearEquiv.conj A :=
  rfl

@[simp]
theorem conjOperator_apply (U : UnitaryTransport H K) (A : Operator H) (x : K) :
    U.conjOperator A x = U.toLinearEquiv (A (U.toLinearEquiv.symm x)) :=
  rfl

@[simp]
theorem symm_conjOperator_conjOperator (U : UnitaryTransport H K) (A : Operator H) :
    U.symm.conjOperator (U.conjOperator A) = A := by
  ext x
  simp [symm, conjOperator]

@[simp]
theorem conjOperator_symm_conjOperator (U : UnitaryTransport H K) (A : Operator K) :
    U.conjOperator (U.symm.conjOperator A) = A := by
  ext x
  simp [symm, conjOperator]

@[simp]
theorem conjOperator_one (U : UnitaryTransport H K) :
    U.conjOperator (1 : Operator H) = (1 : Operator K) := by
  ext x
  simp [conjOperator]

theorem conjOperator_comp (U : UnitaryTransport H K) (A B : Operator H) :
    U.conjOperator (A.comp B) = (U.conjOperator A).comp (U.conjOperator B) := by
  ext x
  simp [conjOperator]

@[simp]
theorem conjOperator_mul (U : UnitaryTransport H K) (A B : Operator H) :
    U.conjOperator (A * B) = U.conjOperator A * U.conjOperator B := by
  ext x
  simp [conjOperator, Module.End.mul_eq_comp]

@[simp]
theorem conjOperator_adjoint (U : UnitaryTransport H K) (A : Operator H) :
    LinearMap.adjoint (U.conjOperator A) = U.conjOperator (LinearMap.adjoint A) := by
  ext x
  simp [conjOperator, U.adjoint_toLinearMap, U.adjoint_symm_toLinearMap]

theorem trace_conjOperator (U : UnitaryTransport H K) (A : Operator H) :
    LinearMap.trace Complex K (U.conjOperator A) = LinearMap.trace Complex H A := by
  simp [conjOperator_eq_linearEquiv_conj]

theorem isPositive_conjOperator (U : UnitaryTransport H K) {A : Operator H}
    (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive (U.conjOperator A) := by
  have h := (LinearMap.isPositive_linearIsometryEquiv_conj_iff
    (T := A) U.toLinearIsometryEquiv).2 hA
  simpa [conjOperator, toLinearIsometryEquiv] using h

/-- Transport a density operator by unitary conjugation. -/
noncomputable def conjDensity (U : UnitaryTransport H K)
    (rho : DensityOperator H) : DensityOperator K where
  toOperator := U.conjOperator rho.toOperator
  positive := U.isPositive_conjOperator rho.positive
  trace_one := by
    rw [U.trace_conjOperator, rho.trace_one]

@[simp]
theorem conjDensity_toOperator (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    (U.conjDensity rho).toOperator = U.conjOperator rho.toOperator :=
  rfl

theorem conjDensity_trace (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (U.conjDensity rho).toOperator = 1 :=
  (U.conjDensity rho).trace_one

theorem conjDensity_positive (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    LinearMap.IsPositive (U.conjDensity rho).toOperator :=
  (U.conjDensity rho).positive

@[simp]
theorem conjDensity_apply (U : UnitaryTransport H K)
    (rho : DensityOperator H) (x : K) :
    (U.conjDensity rho).toOperator x =
      U.toLinearEquiv (rho.toOperator (U.toLinearEquiv.symm x)) :=
  rfl

end UnitaryTransport

namespace QuantumCode

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

/-- A code is transported to another code by a unitary when code membership is preserved. -/
def TransportedBy (U : UnitaryTransport H K) (C : QuantumCode H) (D : QuantumCode K) :
    Prop :=
  ∀ x : H, x ∈ C.carrier ↔ U x ∈ D.carrier

/-- The image of a quantum-code carrier under a unitary transport. -/
def transport (U : UnitaryTransport H K) (C : QuantumCode H) : QuantumCode K where
  carrier := C.carrier.map U.toLinearEquiv.toLinearMap

theorem mem_transport_carrier_iff_symm (U : UnitaryTransport H K) (C : QuantumCode H)
    {y : K} :
    y ∈ (C.transport U).carrier ↔ U.toLinearEquiv.symm y ∈ C.carrier := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    refine ⟨U.toLinearEquiv.symm y, hy, ?_⟩
    simp

theorem mem_transport_carrier_iff (U : UnitaryTransport H K) (C : QuantumCode H)
    {x : H} :
    U.toLinearEquiv x ∈ (C.transport U).carrier ↔ x ∈ C.carrier := by
  rw [mem_transport_carrier_iff_symm]
  simp

theorem transportedBy_transport (U : UnitaryTransport H K) (C : QuantumCode H) :
    TransportedBy U C (C.transport U) := by
  intro x
  simpa using (mem_transport_carrier_iff U C (x := x)).symm

end QuantumCode

namespace DensityOperator

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem supportedOn_conjDensity_of_transportedBy
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {rho : DensityOperator H} (hCD : QuantumCode.TransportedBy U C D)
    (hρ : SupportedOn C rho) :
    SupportedOn D (U.conjDensity rho) := by
  intro y
  rw [UnitaryTransport.conjDensity_apply]
  exact (hCD (rho.toOperator (U.toLinearEquiv.symm y))).1
    (hρ (U.toLinearEquiv.symm y))

theorem supportedOn_conjDensity_transport
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator H)
    (hρ : SupportedOn C rho) :
    SupportedOn (C.transport U) (U.conjDensity rho) :=
  supportedOn_conjDensity_of_transportedBy U (QuantumCode.transportedBy_transport U C) hρ

theorem supportedOn_conjDensity_transport_iff
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn (C.transport U) (U.conjDensity rho) ↔ SupportedOn C rho := by
  constructor
  · intro hρ x
    have hx := hρ (U.toLinearEquiv x)
    rw [UnitaryTransport.conjDensity_apply] at hx
    simpa using (QuantumCode.mem_transport_carrier_iff U C).1 hx
  · exact supportedOn_conjDensity_transport U C rho

theorem supportedOn_symm_conjDensity_transport_iff
    (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator K) :
    SupportedOn C (U.symm.conjDensity rho) ↔ SupportedOn (C.transport U) rho := by
  constructor
  · intro hρ y
    have hy := hρ (U.toLinearEquiv.symm y)
    rw [UnitaryTransport.conjDensity_apply] at hy
    exact (QuantumCode.mem_transport_carrier_iff_symm U C).2 (by
      simpa [UnitaryTransport.symm] using hy)
  · intro hρ x
    have hx := hρ (U.toLinearEquiv x)
    rw [UnitaryTransport.conjDensity_apply]
    exact (QuantumCode.mem_transport_carrier_iff_symm U C).1 (by
      simpa using hx)

end DensityOperator

/--
The M2 unitary-invariance theorem surface for the Knill-Laflamme criterion.

The proposition records the semantic statement that a unitary transport carries
the criterion for a code and error set to the transported code and conjugated
error set. Proof and source-backed publication can advance this node later
without changing the M2 vocabulary.
-/
noncomputable def UnitaryInvariance (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (C : QuantumCode H) (D : QuantumCode K)
    (errors : Set (Operator H)) : Prop :=
  QuantumCode.TransportedBy U C D →
    KnillLaflammeCriterion H C errors →
      KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors)

end Semantics
end QEC
