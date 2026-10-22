import QEC.Coding.Stabilizer.PauliSemantics
import QEC.Coding.QuditQubitConversion.SelfDualBasis

/-!
# Selected `F1024` qudit to ten-qubit transport

The source identifies the computational basis vector `|β⟩`, with `β : F1024`,
with the ten-qubit basis vector whose bits are the coordinates of `β` in its
selected self-dual basis.  This file records that *specific* identification;
it does not use a cardinality-only equivalence.

The resulting Hilbert-space map is a permutation isometry.  Later declarations
in this file derive source-local Pauli and Clifford transport from it.
-/

noncomputable section

namespace QEC.Coding

open scoped BigOperators

/-- The source-selected conversion from an `F1024` computational label to ten qubit bits. -/
noncomputable def why24ComputationalLabelEquiv :
    F1024 ≃ Semantics.Qubit.Bitstring (Fin 10) :=
  f1024SelectedCoordinates.toEquiv.trans
    (PauliSymplectic.bitstringWordEquiv (Fin 10)).symm

/-- The Hilbert space of one concrete `F1024` computational-basis qudit. -/
abbrev Why24QuditSpace : Type := EuclideanSpace Complex F1024

/-- The Hilbert space of the ten qubits selected by the source basis. -/
abbrev Why24QubitSpace : Type := Semantics.Qubit.QubitRegister (Fin 10)

/-- The computational-basis vector of the selected `F1024` qudit. -/
noncomputable def why24QuditComputationalBasis (β : F1024) : Why24QuditSpace :=
  EuclideanSpace.single β 1

/-- The computational-basis vector of the corresponding ten-qubit register. -/
noncomputable def why24QubitComputationalBasis
    (bits : Semantics.Qubit.Bitstring (Fin 10)) : Why24QubitSpace :=
  EuclideanSpace.single bits 1

/--
The source's computational-basis identification, extended linearly.  It is a
permutation isometry, not an abstract dimension or cardinality argument.
-/
noncomputable def why24QuditQubitBasisIsometry :
    Why24QuditSpace ≃ₗᵢ[Complex] Why24QubitSpace :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex why24ComputationalLabelEquiv

/-- Forward action on every concrete `F1024` computational-basis vector. -/
theorem why24QuditQubitBasisIsometry_apply_basis (β : F1024) :
    why24QuditQubitBasisIsometry (why24QuditComputationalBasis β) =
      why24QubitComputationalBasis (why24ComputationalLabelEquiv β) := by
  exact EuclideanSpace.piLpCongrLeft_single why24ComputationalLabelEquiv β 1

/-- Reverse action on every ten-qubit computational-basis vector. -/
theorem why24QuditQubitBasisIsometry_symm_apply_basis
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24QuditQubitBasisIsometry.symm (why24QubitComputationalBasis bits) =
      why24QuditComputationalBasis (why24ComputationalLabelEquiv.symm bits) := by
  apply why24QuditQubitBasisIsometry.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [why24QuditQubitBasisIsometry_apply_basis]
  simp

/-- The same map, packaged for unitary conjugation of concrete operators. -/
noncomputable def why24QuditQubitUnitary :
    Semantics.UnitaryTransport Why24QuditSpace Why24QubitSpace where
  toLinearEquiv := why24QuditQubitBasisIsometry.toLinearEquiv
  map_inner := why24QuditQubitBasisIsometry.toLinearIsometry.inner_map_map

/-- The bitstring image of an `F1024` label has exactly its selected coordinates. -/
theorem why24ComputationalLabelEquiv_coordinates (β : F1024) :
    PauliSymplectic.bitstringWordEquiv (Fin 10) (why24ComputationalLabelEquiv β) =
      f1024SelectedCoordinates β := by
  exact (PauliSymplectic.bitstringWordEquiv (Fin 10)).apply_symm_apply _

/-- The selected coordinates of the inverse bitstring label recover its binary word. -/
theorem f1024SelectedCoordinates_label_symm
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) =
      PauliSymplectic.bitstringWordEquiv (Fin 10) bits := by
  calc
    f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) =
        PauliSymplectic.bitstringWordEquiv (Fin 10)
          (why24ComputationalLabelEquiv (why24ComputationalLabelEquiv.symm bits)) :=
      (why24ComputationalLabelEquiv_coordinates _).symm
    _ = PauliSymplectic.bitstringWordEquiv (Fin 10) bits := by simp

/-- Pointwise form of the source-selected Hilbert-space relabeling. -/
@[simp] theorem why24QuditQubitBasisIsometry_apply
    (ψ : Why24QuditSpace) (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24QuditQubitBasisIsometry ψ bits =
      ψ (why24ComputationalLabelEquiv.symm bits) :=
  rfl

/-- Pointwise form of the inverse source-selected Hilbert-space relabeling. -/
@[simp] theorem why24QuditQubitBasisIsometry_symm_apply
    (ψ : Why24QubitSpace) (β : F1024) :
    why24QuditQubitBasisIsometry.symm ψ β = ψ (why24ComputationalLabelEquiv β) := by
  have hβ := congrArg (fun φ : Why24QubitSpace => φ (why24ComputationalLabelEquiv β))
    (why24QuditQubitBasisIsometry.apply_symm_apply ψ)
  change why24QuditQubitBasisIsometry
      (why24QuditQubitBasisIsometry.symm ψ) (why24ComputationalLabelEquiv β) =
        ψ (why24ComputationalLabelEquiv β) at hβ
  rw [why24QuditQubitBasisIsometry_apply] at hβ
  simpa only [Equiv.symm_apply_apply] using hβ

/-- The actual field-labelled computational-basis shift `X^β`. -/
noncomputable def why24QuditX (β : F1024) : Semantics.Operator Why24QuditSpace where
  toFun ψ := WithLp.toLp 2 (fun η => ψ (η + β))
  map_add' ψ φ := by
    ext η
    simp
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul]

@[simp] theorem why24QuditX_apply (β : F1024) (ψ : Why24QuditSpace) (η : F1024) :
    why24QuditX β ψ η = ψ (η + β) :=
  rfl

/-- The actual trace-phase operator `Z^γ` for the selected `F1024` qudit. -/
noncomputable def why24QuditZ (γ : F1024) : Semantics.Operator Why24QuditSpace where
  toFun ψ := WithLp.toLp 2 (fun η =>
    PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (γ * η)) * ψ η)
  map_add' ψ φ := by
    ext η
    simp [mul_add]
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul, mul_left_comm]

@[simp] theorem why24QuditZ_apply (γ : F1024) (ψ : Why24QuditSpace) (η : F1024) :
    why24QuditZ γ ψ η =
      PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (γ * η)) * ψ η :=
  rfl

/-- Source-exact label action of a field shift on the ten-qubit bitstring. -/
theorem why24ComputationalLabelEquiv_add (β : F1024)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24ComputationalLabelEquiv (why24ComputationalLabelEquiv.symm bits + β) =
      Semantics.Qubit.flipSupport (PauliSymplectic.binarySupport (f1024SelectedCoordinates β))
        bits := by
  apply (PauliSymplectic.bitstringWordEquiv (Fin 10)).injective
  calc
    PauliSymplectic.bitstringWordEquiv (Fin 10)
        (why24ComputationalLabelEquiv
          (why24ComputationalLabelEquiv.symm bits + β)) =
        f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits + β) :=
      why24ComputationalLabelEquiv_coordinates _
    _ = f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) +
        f1024SelectedCoordinates β := by
      exact f1024SelectedCoordinates.map_add _ _
    _ = PauliSymplectic.bitstringWordEquiv (Fin 10) bits +
        f1024SelectedCoordinates β := by
      rw [f1024SelectedCoordinates_label_symm]
    _ = PauliSymplectic.bitstringWordEquiv (Fin 10)
        (Semantics.Qubit.flipSupport
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) bits) := by
      exact (PauliSymplectic.bitstringWordEquiv_flipSupport
        (f1024SelectedCoordinates β) bits).symm

/-- Conjugating the actual field shift gives the concrete binary-support qubit shift. -/
theorem why24QuditQubitUnitary_conjX (β : F1024) :
    why24QuditQubitUnitary.conjOperator (why24QuditX β) =
      Semantics.Qubit.localXSupport
        (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) := by
  ext ψ bits
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  change why24QuditQubitBasisIsometry
      (why24QuditX β (why24QuditQubitBasisIsometry.symm ψ)) bits =
        Semantics.Qubit.localXSupport
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) ψ bits
  rw [why24QuditQubitBasisIsometry_apply, why24QuditX_apply,
    why24QuditQubitBasisIsometry_symm_apply, Semantics.Qubit.localXSupport_apply]
  exact congrArg ψ (why24ComputationalLabelEquiv_add β bits)

/-- The source's self-dual basis turns the field trace pairing into binary word pairing. -/
theorem f1024SelectedCoordinates_trace_pairing (γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (γ * η) =
      wordPairing (F := ZMod 2) (ι := Fin 10)
        (f1024SelectedCoordinates γ) (f1024SelectedCoordinates η) := by
  let basis := f1024SelectedSelfDualBasis
  have hcoordinate (x : F1024) (i : Fin 10) :
      Algebra.trace (ZMod 2) F1024 (x * basis i) = f1024SelectedCoordinates x i := by
    calc
      Algebra.trace (ZMod 2) F1024 (x * basis i) =
          (basis.traceDual).repr x i := by
            simpa only [Algebra.traceForm_apply] using
              (Module.Basis.traceDual_repr_apply basis x i).symm
      _ = basis.repr x i := by
            rw [show basis.traceDual = basis from f1024SelectedSelfDualBasis_traceDual]
      _ = f1024SelectedCoordinates x i := rfl
  have hsum : ∑ i : Fin 10, f1024SelectedCoordinates η i • basis i = η :=
    basis.sum_repr η
  calc
    Algebra.trace (ZMod 2) F1024 (γ * η) =
        Algebra.trace (ZMod 2) F1024
          (γ * ∑ i : Fin 10, f1024SelectedCoordinates η i • basis i) := by
            rw [hsum]
    _ = ∑ i : Fin 10,
        f1024SelectedCoordinates η i *
          Algebra.trace (ZMod 2) F1024 (γ * basis i) := by
            rw [Finset.mul_sum, map_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Algebra.smul_def]
            rw [show γ *
                (algebraMap (ZMod 2) F1024 (f1024SelectedCoordinates η i) * basis i) =
                algebraMap (ZMod 2) F1024 (f1024SelectedCoordinates η i) *
                  (γ * basis i) by ring]
            rw [← Algebra.smul_def]
            exact (Algebra.trace (ZMod 2) F1024).map_smul _ _
    _ = ∑ i : Fin 10,
        f1024SelectedCoordinates γ i * f1024SelectedCoordinates η i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hcoordinate]
            exact mul_comm _ _
    _ = wordPairing (F := ZMod 2) (ι := Fin 10)
        (f1024SelectedCoordinates γ) (f1024SelectedCoordinates η) := by
            rfl

/-- Conjugating the actual field trace phase gives the concrete binary-support qubit phase. -/
theorem why24QuditQubitUnitary_conjZ (γ : F1024) :
    why24QuditQubitUnitary.conjOperator (why24QuditZ γ) =
      Semantics.Qubit.localZSupport
        (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) := by
  ext ψ bits
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  change why24QuditQubitBasisIsometry
      (why24QuditZ γ (why24QuditQubitBasisIsometry.symm ψ)) bits =
        Semantics.Qubit.localZSupport
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) ψ bits
  rw [why24QuditQubitBasisIsometry_apply, why24QuditZ_apply,
    why24QuditQubitBasisIsometry_symm_apply, Semantics.Qubit.localZSupport_apply]
  simp only [Equiv.apply_symm_apply]
  congr 1
  calc
    PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          (γ * why24ComputationalLabelEquiv.symm bits)) =
        PauliSymplectic.binaryPhaseScalar
          (wordPairing (F := ZMod 2) (ι := Fin 10)
            (f1024SelectedCoordinates γ)
            (f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits))) := by
              rw [f1024SelectedCoordinates_trace_pairing]
    _ = PauliSymplectic.binaryPhaseScalar
          (wordPairing (F := ZMod 2) (ι := Fin 10)
            (f1024SelectedCoordinates γ)
            (PauliSymplectic.bitstringWordEquiv (Fin 10) bits)) := by
              rw [f1024SelectedCoordinates_label_symm]
    _ = Semantics.Qubit.zSupportPhase
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) bits := by
              exact (PauliSymplectic.zSupportPhase_eq_binaryPhaseScalar_wordPairing
                (f1024SelectedCoordinates γ) bits).symm

/-- Source Pauli labels `i^a X^β Z^γ` before the selected-coordinate transport. -/
abbrev Why24FieldPauli : Type := ZMod 4 × F1024 × F1024

/-- Binary Pauli labels after the selected-coordinate transport. -/
abbrev Why24BinaryPauli : Type :=
  ZMod 4 × Word (ZMod 2) (Fin 10) × Word (ZMod 2) (Fin 10)

/-- The source's global `i^a` scalar, represented by the canonical residue in `ZMod 4`. -/
def why24PauliPhase (a : ZMod 4) : Complex := Complex.I ^ a.val

/-- The source-exact label transport: selected self-dual coordinates for both X and Z labels. -/
noncomputable def why24PauliLabelEquiv : Why24FieldPauli ≃ Why24BinaryPauli :=
  Equiv.prodCongr (Equiv.refl (ZMod 4))
    (Equiv.prodCongr f1024SelectedCoordinates.toEquiv f1024SelectedCoordinates.toEquiv)

/-- Concrete `i^a X^β Z^γ` on the one selected `F1024` qudit. -/
noncomputable def why24FieldPauliOperator (P : Why24FieldPauli) :
    Semantics.Operator Why24QuditSpace :=
  why24PauliPhase P.1 • (why24QuditX P.2.1 * why24QuditZ P.2.2)

/-- Concrete `i^a X^b Z^c` on the selected ten-qubit register. -/
noncomputable def why24BinaryPauliOperator (P : Why24BinaryPauli) :
    Semantics.Operator Why24QubitSpace :=
  why24PauliPhase P.1 •
    (Semantics.Qubit.localXSupport (PauliSymplectic.binarySupport P.2.1) *
      Semantics.Qubit.localZSupport (PauliSymplectic.binarySupport P.2.2))

private theorem why24QuditQubitUnitary_conj_smul
    (c : Complex) (A : Semantics.Operator Why24QuditSpace) :
    why24QuditQubitUnitary.conjOperator (c • A) =
      c • why24QuditQubitUnitary.conjOperator A := by
  ext ψ
  simp [Semantics.UnitaryTransport.conjOperator, smul_eq_mul]

/-- The selected-coordinate unitary sends every source-labelled Pauli to its binary label. -/
theorem why24QuditQubitUnitary_conjPauli (P : Why24FieldPauli) :
    why24QuditQubitUnitary.conjOperator (why24FieldPauliOperator P) =
      why24BinaryPauliOperator (why24PauliLabelEquiv P) := by
  rcases P with ⟨a, β, γ⟩
  change why24QuditQubitUnitary.conjOperator
      (why24PauliPhase a • (why24QuditX β * why24QuditZ γ)) =
        why24PauliPhase a •
          (Semantics.Qubit.localXSupport
              (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) *
            Semantics.Qubit.localZSupport
              (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)))
  rw [why24QuditQubitUnitary_conj_smul,
    Semantics.UnitaryTransport.conjOperator_mul, why24QuditQubitUnitary_conjX,
    why24QuditQubitUnitary_conjZ]

/-- Inner-product preservation, used here as the concrete finite-dimensional unitarity predicate. -/
def Why24IsUnitary {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (A : Semantics.Operator H) : Prop :=
  ∀ x y, inner Complex (A x) (A y) = inner Complex x y

/-- A field-side normalizer sends every actual field Pauli to an actual field Pauli by conjugation. -/
def why24FieldNormalizesPaulis (C : Semantics.Operator Why24QuditSpace) : Prop :=
  ∀ P : Why24FieldPauli, ∃ Q : Why24FieldPauli,
    C * why24FieldPauliOperator P * LinearMap.adjoint C = why24FieldPauliOperator Q

/-- A binary-side normalizer sends every actual binary Pauli to an actual binary Pauli by conjugation. -/
def why24BinaryNormalizesPaulis (C : Semantics.Operator Why24QubitSpace) : Prop :=
  ∀ P : Why24BinaryPauli, ∃ Q : Why24BinaryPauli,
    C * why24BinaryPauliOperator P * LinearMap.adjoint C = why24BinaryPauliOperator Q

/-- Source-local Clifford condition on the selected field qudit. -/
def Why24FieldClifford (C : Semantics.Operator Why24QuditSpace) : Prop :=
  Why24IsUnitary C ∧ why24FieldNormalizesPaulis C

/-- Binary Clifford condition on the transported ten-qubit register. -/
def Why24BinaryClifford (C : Semantics.Operator Why24QubitSpace) : Prop :=
  Why24IsUnitary C ∧ why24BinaryNormalizesPaulis C

private theorem why24IsUnitary_conjOperator
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] (U : Semantics.UnitaryTransport H K)
    {C : Semantics.Operator H} (hC : Why24IsUnitary C) :
    Why24IsUnitary (U.conjOperator C) := by
  intro x y
  rw [Semantics.UnitaryTransport.conjOperator_apply,
    Semantics.UnitaryTransport.conjOperator_apply]
  calc
    inner Complex (U (C (U.toLinearEquiv.symm x))) (U (C (U.toLinearEquiv.symm y))) =
        inner Complex (C (U.toLinearEquiv.symm x)) (C (U.toLinearEquiv.symm y)) :=
      U.map_inner _ _
    _ = inner Complex (U.toLinearEquiv.symm x) (U.toLinearEquiv.symm y) :=
      hC _ _
    _ = inner Complex x y :=
      U.symm.map_inner _ _

/-- Conjugation by the selected unitary preserves unitarity in both directions. -/
theorem why24QuditQubitUnitary_conj_isUnitary_iff (C : Semantics.Operator Why24QuditSpace) :
    Why24IsUnitary (why24QuditQubitUnitary.conjOperator C) ↔ Why24IsUnitary C := by
  constructor
  · intro hC
    have hback := why24IsUnitary_conjOperator why24QuditQubitUnitary.symm hC
    simpa using hback
  · exact why24IsUnitary_conjOperator why24QuditQubitUnitary

private theorem why24QuditQubitUnitary_conjOperator_injective
    {A B : Semantics.Operator Why24QuditSpace}
    (h : why24QuditQubitUnitary.conjOperator A = why24QuditQubitUnitary.conjOperator B) :
    A = B := by
  have hback := congrArg (fun T : Semantics.Operator Why24QubitSpace =>
    why24QuditQubitUnitary.symm.conjOperator T) h
  simpa using hback

/-- The concrete field-Pauli normalizer transports to the concrete binary-Pauli normalizer. -/
theorem why24QuditQubitUnitary_normalizesPaulis_iff (C : Semantics.Operator Why24QuditSpace) :
    why24BinaryNormalizesPaulis (why24QuditQubitUnitary.conjOperator C) ↔
      why24FieldNormalizesPaulis C := by
  constructor
  · intro hC P
    obtain ⟨Q, hQ⟩ := hC (why24PauliLabelEquiv P)
    refine ⟨why24PauliLabelEquiv.symm Q, ?_⟩
    apply why24QuditQubitUnitary_conjOperator_injective
    calc
      why24QuditQubitUnitary.conjOperator
          (C * why24FieldPauliOperator P * LinearMap.adjoint C) =
          why24QuditQubitUnitary.conjOperator C *
            why24BinaryPauliOperator (why24PauliLabelEquiv P) *
              LinearMap.adjoint (why24QuditQubitUnitary.conjOperator C) := by
            rw [Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_adjoint,
              why24QuditQubitUnitary_conjPauli]
      _ = why24BinaryPauliOperator Q := hQ
      _ = why24QuditQubitUnitary.conjOperator
          (why24FieldPauliOperator (why24PauliLabelEquiv.symm Q)) := by
            rw [why24QuditQubitUnitary_conjPauli]
            simp
  · intro hC P
    obtain ⟨Q, hQ⟩ := hC (why24PauliLabelEquiv.symm P)
    refine ⟨why24PauliLabelEquiv Q, ?_⟩
    calc
      why24QuditQubitUnitary.conjOperator C * why24BinaryPauliOperator P *
          LinearMap.adjoint (why24QuditQubitUnitary.conjOperator C) =
          why24QuditQubitUnitary.conjOperator C *
            why24QuditQubitUnitary.conjOperator
              (why24FieldPauliOperator (why24PauliLabelEquiv.symm P)) *
              LinearMap.adjoint (why24QuditQubitUnitary.conjOperator C) := by
            rw [why24QuditQubitUnitary_conjPauli]
            simp
      _ = why24QuditQubitUnitary.conjOperator
          (C * why24FieldPauliOperator (why24PauliLabelEquiv.symm P) *
            LinearMap.adjoint C) := by
            rw [Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_adjoint]
      _ = why24QuditQubitUnitary.conjOperator (why24FieldPauliOperator Q) :=
            congrArg why24QuditQubitUnitary.conjOperator hQ
      _ = why24BinaryPauliOperator (why24PauliLabelEquiv Q) :=
            why24QuditQubitUnitary_conjPauli Q

/-- The selected-coordinate transport preserves the source-local Clifford normalizer exactly. -/
theorem why24QuditQubitUnitary_clifford_iff (C : Semantics.Operator Why24QuditSpace) :
    Why24BinaryClifford (why24QuditQubitUnitary.conjOperator C) ↔ Why24FieldClifford C := by
  simp only [Why24BinaryClifford, Why24FieldClifford,
    why24QuditQubitUnitary_conj_isUnitary_iff,
    why24QuditQubitUnitary_normalizesPaulis_iff]

/-- The identity is a concrete field-side Clifford normalizer. -/
theorem why24FieldClifford_one :
    Why24FieldClifford (1 : Semantics.Operator Why24QuditSpace) := by
  constructor
  · intro x y
    simp
  · intro P
    exact ⟨P, by simp⟩

/-- Transporting the concrete field identity yields a concrete binary Clifford normalizer. -/
theorem why24QuditQubitUnitary_conj_one_clifford :
    Why24BinaryClifford
      (why24QuditQubitUnitary.conjOperator (1 : Semantics.Operator Why24QuditSpace)) :=
  why24QuditQubitUnitary_clifford_iff _ |>.mpr why24FieldClifford_one

end QEC.Coding
