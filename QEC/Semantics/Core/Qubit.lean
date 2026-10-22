import QEC.Semantics.Core.Definitions
/-!
# QEC.Semantics.Qubit

Concrete finite qubit Hilbert spaces and Pauli operators.

The binary convention in this module is the computational-basis convention:
`0` is the `+1` eigenbit for `Z`, `1` is the `-1` eigenbit for `Z`, and
`X` flips the bit. Thus, on the same qubit, `X * Z = - Z * X`.

This module is internal API infrastructure for later Pauli-symplectic semantics.
It supplies concrete operators and algebraic API lemmas, but does not define
the coordinate-to-operator map for Pauli-symplectic data.
-/

noncomputable section

namespace QEC
namespace Semantics
namespace Qubit

open Classical
open scoped BigOperators ComplexOrder

universe u

/-- The one-qubit Hilbert space with computational basis indexed by `Fin 2`. -/
abbrev QubitSpace : Type :=
  EuclideanSpace Complex (Fin 2)

/-- Binary computational-basis labels for a finite qubit register. -/
abbrev Bitstring (ι : Type u) : Type u :=
  ι → Fin 2

/-- The finite qubit register Hilbert space with basis indexed by bitstrings. -/
abbrev QubitRegister (ι : Type u) [Fintype ι] : Type u :=
  EuclideanSpace Complex (Bitstring ι)

/-- The finite bitstrings over `ι` have `2 ^ Fintype.card ι` elements. -/
@[simp]
theorem card_bitstring (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Fintype.card (Bitstring ι) = 2 ^ Fintype.card ι := by
  change Fintype.card (ι → Fin 2) = 2 ^ Fintype.card ι
  rw [Fintype.card_fun]
  simp

/-- Cardinality form that avoids exposing a decidable-equality assumption. -/
@[simp]
theorem natCard_bitstring (ι : Type u) [Fintype ι] :
    Nat.card (Bitstring ι) = 2 ^ Fintype.card ι := by
  change Nat.card (ι → Fin 2) = 2 ^ Fintype.card ι
  rw [Nat.card_fun]
  simp

/-- A finite qubit register has complex finrank `2 ^ Fintype.card ι`. -/
@[simp]
theorem finrank_qubitRegister (ι : Type u) [Fintype ι] :
    Module.finrank Complex (QubitRegister ι) = 2 ^ Fintype.card ι := by
  classical
  change Module.finrank Complex (EuclideanSpace Complex (Bitstring ι)) =
    2 ^ Fintype.card ι
  rw [finrank_euclideanSpace]
  exact card_bitstring ι

/-- Flip a binary basis bit. -/
def flipBit (b : Fin 2) : Fin 2 :=
  if b = 0 then 1 else 0

@[simp] theorem flipBit_zero : flipBit 0 = 1 := by
  simp [flipBit]

@[simp] theorem flipBit_one : flipBit 1 = 0 := by
  simp [flipBit]

@[simp] theorem flipBit_flip (b : Fin 2) : flipBit (flipBit b) = b := by
  fin_cases b <;> simp

/-- The `Z` eigenvalue attached to a computational-basis bit. -/
def zPhase (b : Fin 2) : Complex :=
  if b = 0 then 1 else -1

@[simp] theorem zPhase_zero : zPhase 0 = 1 := by
  simp [zPhase]

@[simp] theorem zPhase_one : zPhase 1 = -1 := by
  simp [zPhase]

@[simp] theorem zPhase_flipBit (b : Fin 2) : zPhase (flipBit b) = -zPhase b := by
  fin_cases b <;> simp [zPhase]

@[simp] theorem zPhase_sq (b : Fin 2) : zPhase b * zPhase b = 1 := by
  fin_cases b <;> simp [zPhase]

@[simp] theorem zPhase_star (b : Fin 2) : star (zPhase b) = zPhase b := by
  fin_cases b <;> simp [zPhase]

/-- Flip one coordinate of a computational-basis bitstring. -/
def flipAt {ι : Type u} [DecidableEq ι] (i : ι) (bits : Bitstring ι) :
    Bitstring ι :=
  Function.update bits i (flipBit (bits i))

@[simp] theorem flipAt_apply_self {ι : Type u} [DecidableEq ι]
    (i : ι) (bits : Bitstring ι) :
    flipAt i bits i = flipBit (bits i) := by
  simp [flipAt]

theorem flipAt_apply_ne {ι : Type u} [DecidableEq ι]
    {i j : ι} (bits : Bitstring ι) (h : j ≠ i) :
    flipAt i bits j = bits j := by
  simp [flipAt, h]

@[simp] theorem flipAt_flipAt {ι : Type u} [DecidableEq ι]
    (i : ι) (bits : Bitstring ι) :
    flipAt i (flipAt i bits) = bits := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

theorem flipAt_commute {ι : Type u} [DecidableEq ι]
    (i j : ι) (bits : Bitstring ι) :
    flipAt i (flipAt j bits) = flipAt j (flipAt i bits) := by
  by_cases hij : i = j
  · subst j
    simp
  · funext k
    by_cases hki : k = i
    · subst k
      simp [flipAt, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp [flipAt, hki, hij]
      · simp [flipAt, hki, hkj]

/-- Single-qubit Pauli `X` in the computational basis. -/
def pauliXMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  fun row col => if row = flipBit col then 1 else 0

/-- Single-qubit Pauli `Y` in the computational basis. -/
def pauliYMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  fun row col =>
    if row = 0 ∧ col = 1 then -Complex.I
    else if row = 1 ∧ col = 0 then Complex.I
    else 0

/-- Single-qubit Pauli `Z` in the computational basis. -/
def pauliZMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  fun row col => if row = col then zPhase col else 0

/-- Single-qubit identity operator. -/
def pauliI : Operator QubitSpace :=
  1

/-- Single-qubit Pauli `X` operator. -/
def pauliX : Operator QubitSpace :=
  Matrix.toEuclideanLin pauliXMatrix

/-- Single-qubit Pauli `Y` operator. -/
def pauliY : Operator QubitSpace :=
  Matrix.toEuclideanLin pauliYMatrix

/-- Single-qubit Pauli `Z` operator. -/
def pauliZ : Operator QubitSpace :=
  Matrix.toEuclideanLin pauliZMatrix

@[simp] theorem pauliI_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliI ψ b = ψ b :=
  rfl

@[simp] theorem pauliX_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliX ψ b = ψ (flipBit b) := by
  fin_cases b <;> simp [pauliX, pauliXMatrix, Matrix.mulVec, dotProduct, flipBit]

@[simp] theorem pauliY_apply_zero (ψ : QubitSpace) :
    pauliY ψ 0 = -Complex.I * ψ 1 := by
  simp [pauliY, pauliYMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem pauliY_apply_one (ψ : QubitSpace) :
    pauliY ψ 1 = Complex.I * ψ 0 := by
  simp [pauliY, pauliYMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem pauliY_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliY ψ b = if b = 0 then -Complex.I * ψ 1 else Complex.I * ψ 0 := by
  fin_cases b <;> simp

@[simp] theorem pauliZ_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliZ ψ b = zPhase b * ψ b := by
  fin_cases b <;> simp [pauliZ, pauliZMatrix, Matrix.mulVec, dotProduct, zPhase]

theorem pauliI_square : pauliI * pauliI = pauliI := by
  simp [pauliI]

theorem pauliX_square : pauliX * pauliX = 1 := by
  ext ψ b
  simp [Module.End.mul_apply]

theorem pauliY_square : pauliY * pauliY = 1 := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply] <;>
    rw [← mul_assoc, Complex.I_mul_I] <;> ring

theorem pauliZ_square : pauliZ * pauliZ = 1 := by
  ext ψ b
  simp only [Module.End.mul_apply, pauliZ_apply]
  rw [← mul_assoc, zPhase_sq, one_mul]
  rfl

theorem pauliXMatrix_conjTranspose : pauliXMatrix.conjTranspose = pauliXMatrix := by
  ext row col
  change star (pauliXMatrix col row) = pauliXMatrix row col
  fin_cases row <;> fin_cases col <;> simp [pauliXMatrix, flipBit]

theorem pauliYMatrix_conjTranspose : pauliYMatrix.conjTranspose = pauliYMatrix := by
  ext row col
  change star (pauliYMatrix col row) = pauliYMatrix row col
  fin_cases row <;> fin_cases col <;> simp [pauliYMatrix]

theorem pauliZMatrix_conjTranspose : pauliZMatrix.conjTranspose = pauliZMatrix := by
  ext row col
  change star (pauliZMatrix col row) = pauliZMatrix row col
  by_cases h : row = col
  · subst col
    simp [pauliZMatrix]
  · have hc : ¬ col = row := fun hc => h hc.symm
    simp [pauliZMatrix, h, hc]

theorem pauliI_adjoint : LinearMap.adjoint pauliI = pauliI := by
  simp [pauliI]

theorem pauliX_adjoint : LinearMap.adjoint pauliX = pauliX := by
  change LinearMap.adjoint (Matrix.toEuclideanLin pauliXMatrix) =
    Matrix.toEuclideanLin pauliXMatrix
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint pauliXMatrix,
    pauliXMatrix_conjTranspose]

theorem pauliY_adjoint : LinearMap.adjoint pauliY = pauliY := by
  change LinearMap.adjoint (Matrix.toEuclideanLin pauliYMatrix) =
    Matrix.toEuclideanLin pauliYMatrix
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint pauliYMatrix,
    pauliYMatrix_conjTranspose]

theorem pauliZ_adjoint : LinearMap.adjoint pauliZ = pauliZ := by
  change LinearMap.adjoint (Matrix.toEuclideanLin pauliZMatrix) =
    Matrix.toEuclideanLin pauliZMatrix
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint pauliZMatrix,
    pauliZMatrix_conjTranspose]

theorem pauliX_pauliZ_sameSite_anticommute :
    pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext ψ b
  simp [Module.End.mul_apply]

theorem pauliX_pauliY : pauliX * pauliY = Complex.I • pauliZ := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]

theorem pauliY_pauliX : pauliY * pauliX = -Complex.I • pauliZ := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]

theorem pauliY_pauliZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]

theorem pauliZ_pauliY : pauliZ * pauliY = -Complex.I • pauliX := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply]

theorem pauliZ_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply] <;>
    rw [← mul_assoc, Complex.I_mul_I] <;> ring

theorem pauliX_pauliZ : pauliX * pauliZ = -Complex.I • pauliY := by
  ext ψ b
  fin_cases b <;> simp [Module.End.mul_apply] <;>
    rw [← mul_assoc, Complex.I_mul_I] <;> ring

theorem pauliI_trace :
    LinearMap.trace Complex QubitSpace pauliI = (2 : Complex) := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliI, LinearMap.toMatrix_one]
  change Matrix.trace (1 : Matrix (Fin 2) (Fin 2) Complex) = 2
  simp [Matrix.trace]

theorem pauliX_trace : LinearMap.trace Complex QubitSpace pauliX = 0 := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliX, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.toMatrix_toLin]
  change Matrix.trace pauliXMatrix = 0
  simp [Matrix.trace, pauliXMatrix, flipBit]

theorem pauliY_trace : LinearMap.trace Complex QubitSpace pauliY = 0 := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliY, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.toMatrix_toLin]
  change Matrix.trace pauliYMatrix = 0
  simp [Matrix.trace, pauliYMatrix]

theorem pauliZ_trace : LinearMap.trace Complex QubitSpace pauliZ = 0 := by
  rw [LinearMap.trace_eq_matrix_trace Complex
    (EuclideanSpace.basisFun (Fin 2) Complex).toBasis]
  rw [pauliZ, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.toMatrix_toLin]
  change Matrix.trace pauliZMatrix = 0
  simp [Matrix.trace, pauliZMatrix, zPhase]

theorem pauliX_pauliX_trace :
    LinearMap.trace Complex QubitSpace (pauliX * pauliX) = (2 : Complex) := by
  rw [pauliX_square]
  change LinearMap.trace Complex QubitSpace pauliI = 2
  exact pauliI_trace

theorem pauliX_pauliY_trace :
    LinearMap.trace Complex QubitSpace (pauliX * pauliY) = 0 := by
  rw [pauliX_pauliY]
  simp [pauliZ_trace]

theorem pauliX_pauliZ_trace :
    LinearMap.trace Complex QubitSpace (pauliX * pauliZ) = 0 := by
  rw [pauliX_pauliZ]
  simp [pauliY_trace]

theorem pauliY_pauliX_trace :
    LinearMap.trace Complex QubitSpace (pauliY * pauliX) = 0 := by
  rw [pauliY_pauliX]
  simp [pauliZ_trace]

theorem pauliY_pauliY_trace :
    LinearMap.trace Complex QubitSpace (pauliY * pauliY) = (2 : Complex) := by
  rw [pauliY_square]
  change LinearMap.trace Complex QubitSpace pauliI = 2
  exact pauliI_trace

theorem pauliY_pauliZ_trace :
    LinearMap.trace Complex QubitSpace (pauliY * pauliZ) = 0 := by
  rw [pauliY_pauliZ]
  simp [pauliX_trace]

theorem pauliZ_pauliX_trace :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliX) = 0 := by
  rw [pauliZ_pauliX]
  simp [pauliY_trace]

theorem pauliZ_pauliY_trace :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliY) = 0 := by
  rw [pauliZ_pauliY]
  simp [pauliX_trace]

theorem pauliZ_pauliZ_trace :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliZ) = (2 : Complex) := by
  rw [pauliZ_square]
  change LinearMap.trace Complex QubitSpace pauliI = 2
  exact pauliI_trace

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Matrix for a local `X` operator on a finite qubit register. -/
def localXMatrix (i : ι) : Matrix (Bitstring ι) (Bitstring ι) Complex :=
  fun row col => if row = flipAt i col then 1 else 0

/-- Matrix for a local `Z` operator on a finite qubit register. -/
def localZMatrix (i : ι) : Matrix (Bitstring ι) (Bitstring ι) Complex :=
  fun row col => if row = col then zPhase (col i) else 0

/-- Local `X` tensor-lift acting on qubit `i`. -/
def localX (i : ι) : Operator (QubitRegister ι) := by
  classical
  exact Matrix.toEuclideanLin (localXMatrix i)

/-- Local `Z` tensor-lift acting on qubit `i`. -/
def localZ (i : ι) : Operator (QubitRegister ι) := by
  classical
  exact Matrix.toEuclideanLin (localZMatrix i)

@[simp] theorem localX_apply (i : ι) (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localX i ψ bits = ψ (flipAt i bits) := by
  classical
  simp only [localX, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  change (∑ x, (localXMatrix i bits x) * ψ.ofLp x) = ψ.ofLp (flipAt i bits)
  rw [Finset.sum_eq_single (flipAt i bits)]
  · simp [localXMatrix]
  · intro b _ hbne
    have hnot : ¬ bits = flipAt i b := by
      intro h
      have hb : flipAt i bits = b := by
        simp [h]
      exact hbne hb.symm
    simp [localXMatrix, hnot]
  · intro hnot
    simp at hnot

@[simp] theorem localZ_apply (i : ι) (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localZ i ψ bits = zPhase (bits i) * ψ bits := by
  classical
  simp only [localZ, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  change (∑ x, (localZMatrix i bits x) * ψ.ofLp x) = zPhase (bits i) * ψ.ofLp bits
  rw [Finset.sum_eq_single bits]
  · simp [localZMatrix]
  · intro b _ hbne
    have hne : ¬ bits = b := fun h => hbne h.symm
    simp [localZMatrix, hne]
  · intro hnot
    simp at hnot

theorem localX_square (i : ι) : localX i * localX i = 1 := by
  ext ψ bits
  simp [Module.End.mul_apply]

theorem localZ_square (i : ι) : localZ i * localZ i = 1 := by
  ext ψ bits
  simp only [Module.End.mul_apply, localZ_apply]
  rw [← mul_assoc, zPhase_sq, one_mul]
  rfl

theorem localXMatrix_conjTranspose (i : ι) :
    (localXMatrix i).conjTranspose = localXMatrix i := by
  classical
  ext row col
  change star (localXMatrix i col row) = localXMatrix i row col
  by_cases h : row = flipAt i col
  · have hc : col = flipAt i row := by
      rw [h, flipAt_flipAt]
    have hleft : localXMatrix i col row = 1 := by
      unfold localXMatrix
      exact if_pos hc
    have hright : localXMatrix i row col = 1 := by
      unfold localXMatrix
      exact if_pos h
    rw [hleft, hright]
    simp
  · have hc : ¬ col = flipAt i row := by
      intro hc
      apply h
      rw [hc, flipAt_flipAt]
    have hleft : localXMatrix i col row = 0 := by
      unfold localXMatrix
      exact if_neg hc
    have hright : localXMatrix i row col = 0 := by
      unfold localXMatrix
      exact if_neg h
    rw [hleft, hright]
    simp

omit [DecidableEq ι] in
theorem localZMatrix_conjTranspose (i : ι) :
    (localZMatrix i).conjTranspose = localZMatrix i := by
  classical
  ext row col
  change star (localZMatrix i col row) = localZMatrix i row col
  by_cases h : row = col
  · subst col
    simp [localZMatrix]
  · have hc : ¬ col = row := fun hc => h hc.symm
    simp [localZMatrix, h, hc]

theorem localX_adjoint (i : ι) : LinearMap.adjoint (localX i) = localX i := by
  classical
  change LinearMap.adjoint (Matrix.toEuclideanLin (localXMatrix i)) =
    Matrix.toEuclideanLin (localXMatrix i)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint (localXMatrix i),
    localXMatrix_conjTranspose]

theorem localZ_adjoint (i : ι) : LinearMap.adjoint (localZ i) = localZ i := by
  classical
  change LinearMap.adjoint (Matrix.toEuclideanLin (localZMatrix i)) =
    Matrix.toEuclideanLin (localZMatrix i)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint (localZMatrix i),
    localZMatrix_conjTranspose]

theorem localX_localZ_sameSite_anticommute (i : ι) :
    localX i * localZ i = -(localZ i * localX i) := by
  ext ψ bits
  simp [Module.End.mul_apply]

theorem localX_localZ_commute_of_ne {i j : ι} (h : i ≠ j) :
    localX i * localZ j = localZ j * localX i := by
  ext ψ bits
  have hj : j ≠ i := h.symm
  simp [Module.End.mul_apply, flipAt_apply_ne bits hj]

theorem localZ_localX_commute_of_ne {i j : ι} (h : i ≠ j) :
    localZ i * localX j = localX j * localZ i := by
  exact (localX_localZ_commute_of_ne (i := j) (j := i) h.symm).symm

theorem localX_localX_commute (i j : ι) :
    localX i * localX j = localX j * localX i := by
  ext ψ bits
  simp [Module.End.mul_apply, flipAt_commute]

theorem localZ_localZ_commute (i j : ι) :
    localZ i * localZ j = localZ j * localZ i := by
  ext ψ bits
  simp [Module.End.mul_apply, mul_left_comm]

/-- Flip every coordinate in a finite support. -/
def flipSupport (s : Finset ι) (bits : Bitstring ι) : Bitstring ι :=
  fun i => if i ∈ s then flipBit (bits i) else bits i

omit [Fintype ι] in
@[simp] theorem flipSupport_empty (bits : Bitstring ι) :
    flipSupport (∅ : Finset ι) bits = bits := by
  funext i
  simp [flipSupport]

omit [Fintype ι] in
theorem flipSupport_insert (s : Finset ι) {i : ι} (h : i ∉ s)
    (bits : Bitstring ι) :
    flipSupport (insert i s) bits = flipSupport s (flipAt i bits) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipSupport, h]
  · by_cases hjs : j ∈ s
    · simp [flipSupport, hji, hjs, flipAt_apply_ne bits hji]
    · simp [flipSupport, hji, hjs, flipAt_apply_ne bits hji]

omit [Fintype ι] in
theorem flipSupport_singleton (i : ι) (bits : Bitstring ι) :
    flipSupport ({i} : Finset ι) bits = flipAt i bits := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flipSupport, flipAt]
  · simp [flipSupport, flipAt, h]

/-- Product of `Z` eigenvalue phases over a support. -/
def zSupportPhase (s : Finset ι) (bits : Bitstring ι) : Complex :=
  ∏ i ∈ s, zPhase (bits i)

/-- Sign picked up when an `X` support passes a `Z` support. -/
def supportPhaseSign (xSupport zSupport : Finset ι) : Complex :=
  ∏ i ∈ zSupport, if i ∈ xSupport then (-1 : Complex) else 1

/-- The support-level `X` operator, defined by flipping all supported bits. -/
def localXSupport (s : Finset ι) : Operator (QubitRegister ι) where
  toFun ψ := WithLp.toLp 2 (fun bits => ψ (flipSupport s bits))
  map_add' ψ φ := by
    ext bits
    simp
  map_smul' c ψ := by
    ext bits
    simp

/-- The support-level `Z` operator, defined by multiplying basis amplitudes by a phase. -/
def localZSupport (s : Finset ι) : Operator (QubitRegister ι) where
  toFun ψ := WithLp.toLp 2 (fun bits => zSupportPhase s bits * ψ bits)
  map_add' ψ φ := by
    ext bits
    simp [mul_add]
  map_smul' c ψ := by
    ext bits
    simp [smul_eq_mul, mul_left_comm]

@[simp] theorem localXSupport_apply (s : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localXSupport s ψ bits = ψ (flipSupport s bits) :=
  rfl

@[simp] theorem localZSupport_apply (s : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localZSupport s ψ bits = zSupportPhase s bits * ψ bits :=
  rfl

theorem localXSupport_singleton (i : ι) :
    localXSupport ({i} : Finset ι) = localX i := by
  ext ψ bits
  simp [flipSupport_singleton]

theorem localZSupport_singleton (i : ι) :
    localZSupport ({i} : Finset ι) = localZ i := by
  ext ψ bits
  simp [zSupportPhase]

theorem localXSupport_insert (s : Finset ι) {i : ι} (h : i ∉ s) :
    localXSupport (insert i s) = localX i * localXSupport s := by
  ext ψ bits
  simp [Module.End.mul_apply, flipSupport_insert s h]

theorem localZSupport_insert (s : Finset ι) {i : ι} (h : i ∉ s) :
    localZSupport (insert i s) = localZ i * localZSupport s := by
  ext ψ bits
  simp [Module.End.mul_apply, zSupportPhase, h, mul_assoc]

omit [Fintype ι] in
theorem zSupportPhase_flipSupport (xSupport zSupport : Finset ι)
    (bits : Bitstring ι) :
    zSupportPhase zSupport (flipSupport xSupport bits) =
      supportPhaseSign xSupport zSupport * zSupportPhase zSupport bits := by
  simp only [zSupportPhase, supportPhaseSign]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hix : i ∈ xSupport
  · simp [flipSupport, hix]
  · simp [flipSupport, hix]

theorem localXSupport_localZSupport_apply (xSupport zSupport : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    (localXSupport xSupport * localZSupport zSupport) ψ bits =
      zSupportPhase zSupport (flipSupport xSupport bits) *
        ψ (flipSupport xSupport bits) := by
  simp [Module.End.mul_apply]

theorem localZSupport_localXSupport_apply (xSupport zSupport : Finset ι)
    (ψ : QubitRegister ι) (bits : Bitstring ι) :
    (localZSupport zSupport * localXSupport xSupport) ψ bits =
      zSupportPhase zSupport bits * ψ (flipSupport xSupport bits) := by
  simp [Module.End.mul_apply]

theorem localXSupport_localZSupport_phase (xSupport zSupport : Finset ι) :
    localXSupport xSupport * localZSupport zSupport =
      supportPhaseSign xSupport zSupport •
        (localZSupport zSupport * localXSupport xSupport) := by
  ext ψ bits
  simp [zSupportPhase_flipSupport, mul_assoc]

end Qubit
end Semantics
end QEC
