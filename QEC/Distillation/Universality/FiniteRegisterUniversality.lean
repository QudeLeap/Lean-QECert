import QEC.Distillation.Universality.AdaptiveIdealClifford
import QEC.Distillation.Universality.GeneratedUniversality
import QEC.Distillation.TwoQubitOperations.Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-register lifts of generated one-qubit gates

This internal module gives concrete finite-register matrix semantics for an
explicit circuit built from arbitrary one-qubit target gates and exact
distinct-wire XOR gates. Its terminal approximation theorem ranges over the
transparent circuit syntax below. It does not assert a decomposition of an
arbitrary register unitary into those primitives.

The approximation route is topological: a projective closure representative
of each one-qubit target is carried through the continuous concrete local
lift, exact XOR gates are register generators, and sequential composition is
closed in the resulting topological subgroup. Consequently no invalid
entrywise-norm telescoping estimate is used.
-/

noncomputable section

universe u

namespace QEC
namespace Distillation
namespace FiniteRegisterUniversality

open Semantics Semantics.Qubit
open GeneratedUniversality
open scoped Kronecker

variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]

/-- The wires other than a distinguished local wire. -/
abbrev OtherWires (wire : Wire) : Type u := {other : Wire // other ≠ wire}

/-- Split a register basis index into the selected wire and its complement. -/
def splitAtWire (wire : Wire) (bits : Bitstring Wire) :
    Fin 2 × Bitstring (OtherWires wire) :=
  (bits wire, fun other => bits other)

/-- Reassemble a selected-wire bit and complement bits into a register index. -/
def mergeAtWire (wire : Wire)
    (bits : Fin 2 × Bitstring (OtherWires wire)) : Bitstring Wire :=
  fun candidate => if h : candidate = wire then bits.1 else bits.2 ⟨candidate, h⟩

/-- The concrete basis-index equivalence used to lift a one-qubit matrix. -/
def singleQubitIndexEquiv (wire : Wire) :
    Bitstring Wire ≃ Fin 2 × Bitstring (OtherWires wire) where
  toFun := splitAtWire wire
  invFun := mergeAtWire wire
  left_inv := by
    intro bits
    funext candidate
    by_cases h : candidate = wire <;> simp [splitAtWire, mergeAtWire, h]
  right_inv := by
    rintro ⟨selected, rest⟩
    apply Prod.ext
    · simp [splitAtWire, mergeAtWire]
    · funext other
      simp [splitAtWire, mergeAtWire, other.property]

/-- The matrix acting by a one-qubit matrix on `wire` and by identity elsewhere. -/
noncomputable def singleQubitLiftMatrix (wire : Wire)
    (gate : Matrix (Fin 2) (Fin 2) Complex) :
    Matrix (Bitstring Wire) (Bitstring Wire) Complex :=
  Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
    (gate ⊗ₖ (1 : Matrix (Bitstring (OtherWires wire))
      (Bitstring (OtherWires wire)) Complex))

/-- The selected-wire matrix lift is complex-linear on the ambient matrix space. -/
noncomputable def singleQubitLiftLinear (wire : Wire) :
    Matrix (Fin 2) (Fin 2) Complex →ₗ[Complex]
      Matrix (Bitstring Wire) (Bitstring Wire) Complex where
  toFun := singleQubitLiftMatrix wire
  map_add' := by
    intro left right
    simp [singleQubitLiftMatrix, Matrix.add_kronecker, Matrix.submatrix_add]
  map_smul' := by
    intro scalar gate
    simp [singleQubitLiftMatrix, Matrix.smul_kronecker, Matrix.submatrix_smul]

/-- A concrete one-qubit unitary lifted to a selected finite register wire. -/
noncomputable def singleQubitLift (wire : Wire)
    (gate : UnitaryGate (Fin 2)) : UnitaryGate (Bitstring Wire) := by
  refine ⟨singleQubitLiftMatrix wire gate, ?_⟩
  let indexEquiv := (singleQubitIndexEquiv wire).symm
  let localMatrix : Matrix (Fin 2) (Fin 2) Complex := gate
  let restIdentity : Matrix (Bitstring (OtherWires wire))
      (Bitstring (OtherWires wire)) Complex := 1
  have hlocal : localMatrix ⊗ₖ restIdentity ∈
      Matrix.unitaryGroup (Fin 2 × Bitstring (OtherWires wire)) Complex :=
    Matrix.kronecker_mem_unitary gate.property (Submonoid.one_mem _)
  apply Matrix.mem_unitaryGroup_iff.mpr
  change Matrix.reindex indexEquiv indexEquiv (localMatrix ⊗ₖ restIdentity) *
      star (Matrix.reindex indexEquiv indexEquiv (localMatrix ⊗ₖ restIdentity)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  have hlocalEquation :
      (localMatrix ⊗ₖ restIdentity) *
        (localMatrix ⊗ₖ restIdentity).conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hlocal)
  calc
    Matrix.reindex indexEquiv indexEquiv (localMatrix ⊗ₖ restIdentity) *
        Matrix.reindex indexEquiv indexEquiv
          (localMatrix ⊗ₖ restIdentity).conjTranspose =
      Matrix.reindex indexEquiv indexEquiv
        ((localMatrix ⊗ₖ restIdentity) *
          (localMatrix ⊗ₖ restIdentity).conjTranspose) := by
      exact Matrix.reindexLinearEquiv_mul Complex Complex
        indexEquiv indexEquiv indexEquiv _ _
    _ = Matrix.reindex indexEquiv indexEquiv 1 :=
      congrArg (Matrix.reindex indexEquiv indexEquiv) hlocalEquation
    _ = 1 := Matrix.reindexLinearEquiv_one Complex Complex indexEquiv

/-- The local lift preserves the identity matrix. -/
theorem singleQubitLift_one (wire : Wire) :
    singleQubitLift wire (1 : UnitaryGate (Fin 2)) = 1 := by
  apply Subtype.ext
  change Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      ((1 : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex)) = 1
  rw [Matrix.one_kronecker_one]
  exact Matrix.reindexLinearEquiv_one Complex Complex (singleQubitIndexEquiv wire).symm

/-- The local lift preserves sequential multiplication of one-qubit gates. -/
theorem singleQubitLift_mul (wire : Wire) (left right : UnitaryGate (Fin 2)) :
    singleQubitLift wire (left * right) =
      singleQubitLift wire left * singleQubitLift wire right := by
  apply Subtype.ext
  change Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      (((left : Matrix (Fin 2) (Fin 2) Complex) *
        (right : Matrix (Fin 2) (Fin 2) Complex)) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex)) =
      Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
        ((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
          (1 : Matrix (Bitstring (OtherWires wire))
            (Bitstring (OtherWires wire)) Complex)) *
      Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
        ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
          (1 : Matrix (Bitstring (OtherWires wire))
            (Bitstring (OtherWires wire)) Complex))
  let indexEquiv := (singleQubitIndexEquiv wire).symm
  let restIdentity : Matrix (Bitstring (OtherWires wire))
      (Bitstring (OtherWires wire)) Complex := 1
  calc
    Matrix.reindex indexEquiv indexEquiv
        (((left : Matrix (Fin 2) (Fin 2) Complex) *
          (right : Matrix (Fin 2) (Fin 2) Complex)) ⊗ₖ restIdentity) =
        Matrix.reindex indexEquiv indexEquiv
          (((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity) *
            ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity)) := by
      congr 1
      rw [← Matrix.mul_kronecker_mul]
      simp [restIdentity]
    _ = Matrix.reindex indexEquiv indexEquiv
          ((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity) *
        Matrix.reindex indexEquiv indexEquiv
          ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity) := by
      exact (Matrix.reindexLinearEquiv_mul Complex Complex
        indexEquiv indexEquiv indexEquiv _ _).symm

/-- The selected-wire lift as a group homomorphism. -/
noncomputable def singleQubitLiftHom (wire : Wire) :
    UnitaryGate (Fin 2) →* UnitaryGate (Bitstring Wire) where
  toFun := singleQubitLift wire
  map_one' := singleQubitLift_one wire
  map_mul' := singleQubitLift_mul wire

/-- The local lift preserves inversion. -/
theorem singleQubitLift_inv (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    singleQubitLift wire gate⁻¹ = (singleQubitLift wire gate)⁻¹ :=
  (singleQubitLiftHom wire).map_inv gate

/-- The concrete selected-wire lift is continuous in its one-qubit input. -/
theorem continuous_singleQubitLift (wire : Wire) :
    Continuous (singleQubitLift wire) := by
  apply Continuous.subtype_mk
  change Continuous (fun gate : UnitaryGate (Fin 2) =>
    singleQubitLiftMatrix wire (gate : Matrix (Fin 2) (Fin 2) Complex))
  exact (singleQubitLiftLinear wire).continuous_of_finiteDimensional.comp
    continuous_subtype_val

/-- Lifting a global phase on a one-qubit gate gives the same global phase on
the finite register. -/
theorem globalPhaseEquivalent_singleQubitLift (wire : Wire)
    {left right : UnitaryGate (Fin 2)}
    (hphase : GlobalPhaseEquivalent left right) :
    GlobalPhaseEquivalent (singleQubitLift wire left) (singleQubitLift wire right) := by
  rcases hphase with ⟨scalar, hnorm, hmatrix⟩
  refine ⟨scalar, hnorm, ?_⟩
  change Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex)) =
    scalar • Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      ((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex))
  rw [hmatrix, Matrix.smul_kronecker]
  rfl

/-- Toggle `target` precisely when the control bit is one. -/
def registerXorBitstring (control target : Wire) (_ : control ≠ target)
    (bits : Bitstring Wire) : Bitstring Wire :=
  fun wire => if wire = target then
    TwoQubit.controlledXBit (bits control) (bits target)
  else bits wire

@[simp] theorem registerXorBitstring_control (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorBitstring control target hdistinct bits control = bits control := by
  simp [registerXorBitstring, hdistinct]

@[simp] theorem registerXorBitstring_target (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorBitstring control target hdistinct bits target =
      TwoQubit.controlledXBit (bits control) (bits target) := by
  simp [registerXorBitstring]

@[simp] theorem registerXorBitstring_involutive (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorBitstring control target hdistinct
      (registerXorBitstring control target hdistinct bits) = bits := by
  funext wire
  by_cases htarget : wire = target
  · subst wire
    simp [registerXorBitstring, hdistinct,
      TwoQubit.controlledXBit_involutive]
  · simp [registerXorBitstring, htarget]

/-- The exact XOR action is a permutation of computational-basis labels. -/
def registerXorBitstringEquiv (control target : Wire) (hdistinct : control ≠ target) :
    Equiv.Perm (Bitstring Wire) where
  toFun := registerXorBitstring control target hdistinct
  invFun := registerXorBitstring control target hdistinct
  left_inv := registerXorBitstring_involutive control target hdistinct
  right_inv := registerXorBitstring_involutive control target hdistinct

/-- The exact basis transport of the concrete finite-register XOR
permutation. -/
noncomputable def registerXorTransport (control target : Wire)
    (hdistinct : control ≠ target) :
    UnitaryTransport (QubitRegister Wire) (QubitRegister Wire) := by
  let basis := EuclideanSpace.basisFun (Bitstring Wire) Complex
  let U := basis.equiv basis (registerXorBitstringEquiv control target hdistinct)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

@[simp] theorem registerXorTransport_apply_basis (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorTransport control target hdistinct
        (EuclideanSpace.basisFun (Bitstring Wire) Complex bits) =
      EuclideanSpace.basisFun (Bitstring Wire) Complex
        (registerXorBitstring control target hdistinct bits) := by
  dsimp [registerXorTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl

/-- Package an exact computational-basis permutation as a unitary gate. -/
noncomputable def permutationGate {n : Type u} [Fintype n] [DecidableEq n]
    (permutation : Equiv.Perm n) : UnitaryGate n := by
  refine ⟨permutation.permMatrix Complex, ?_⟩
  apply Matrix.mem_unitaryGroup_iff.mpr
  change permutation.permMatrix Complex *
      (permutation.permMatrix Complex).conjTranspose = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- The concrete finite-register XOR/CNOT gate on distinct wires. -/
noncomputable def registerXorGate (control target : Wire)
    (hdistinct : control ≠ target) : UnitaryGate (Bitstring Wire) :=
  permutationGate (registerXorBitstringEquiv control target hdistinct)

/-- The gate and transport share exactly the same explicit basis permutation. -/
@[simp] theorem registerXorGate_matrix (control target : Wire)
    (hdistinct : control ≠ target) :
    (registerXorGate control target hdistinct :
      Matrix (Bitstring Wire) (Bitstring Wire) Complex) =
      (registerXorBitstringEquiv control target hdistinct).permMatrix Complex :=
  rfl

/-- On a two-wire register, the basis-index permutation is exactly the XOR
coordinate permutation of the concrete #586 transport. -/
theorem registerXorBitstring_finTwo (bits : Bitstring (Fin 2)) :
    registerXorBitstring (0 : Fin 2) 1 (by decide) bits =
      TwoQubit.xorBitstring bits := by
  funext wire
  fin_cases wire <;>
    simp [registerXorBitstring, TwoQubit.xorBitstring, TwoQubit.pairBitstring]

/-- On every two-qubit computational-basis vector, the generic XOR transport
has exactly the #586 `xorTransport` action. -/
theorem registerXorTransport_finTwo_apply_basis (bits : Bitstring (Fin 2)) :
    registerXorTransport (0 : Fin 2) 1 (by decide)
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      TwoQubit.xorTransport
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) := by
  rw [registerXorTransport_apply_basis, TwoQubit.xorTransport_apply_basis,
    registerXorBitstring_finTwo]

/-- The exact XOR gate is one of the concrete finite-register generators. -/
def finiteRegisterGenerators (generators : Set (UnitaryGate (Fin 2))) :
    Set (UnitaryGate (Bitstring Wire)) :=
  {gate | ∃ wire : Wire, ∃ sourceGate : UnitaryGate (Fin 2),
    sourceGate ∈ generators ∧ gate = singleQubitLift wire sourceGate} ∪
  {gate | ∃ control target : Wire, ∃ hdistinct : control ≠ target,
    gate = registerXorGate control target hdistinct}

theorem singleQubitLift_mem_finiteRegisterGenerators
    (generators : Set (UnitaryGate (Fin 2))) (wire : Wire)
    {gate : UnitaryGate (Fin 2)} (hgate : gate ∈ generators) :
    singleQubitLift wire gate ∈ finiteRegisterGenerators generators :=
  Or.inl ⟨wire, gate, hgate, rfl⟩

theorem registerXorGate_mem_finiteRegisterGenerators
    (generators : Set (UnitaryGate (Fin 2))) (control target : Wire)
    (hdistinct : control ≠ target) :
    registerXorGate control target hdistinct ∈ finiteRegisterGenerators generators :=
  Or.inr ⟨control, target, hdistinct, rfl⟩

/-- A local lift sends the subgroup generated by the source one-qubit set into
the subgroup generated by the concrete register lifts. -/
theorem singleQubitLift_mapsTo_generatedUnitarySubgroup
    (generators : Set (UnitaryGate (Fin 2))) (wire : Wire) :
    Set.MapsTo (singleQubitLift wire)
      (generatedUnitarySubgroup generators)
      (generatedUnitarySubgroup (finiteRegisterGenerators (Wire := Wire) generators)) := by
  intro gate hgate
  change gate ∈ Subgroup.closure generators at hgate
  change singleQubitLift wire gate ∈
    Subgroup.closure (finiteRegisterGenerators (Wire := Wire) generators)
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hgate
  · intro sourceGate hsourceGate
    exact Subgroup.subset_closure
      (singleQubitLift_mem_finiteRegisterGenerators generators wire hsourceGate)
  · simpa only [singleQubitLift_one] using
      (Subgroup.closure (finiteRegisterGenerators (Wire := Wire) generators)).one_mem
  · intro left right _ _ hleft hright
    simpa only [singleQubitLift_mul] using
      (Subgroup.closure (finiteRegisterGenerators (Wire := Wire) generators)).mul_mem
        hleft hright
  · intro sourceGate _ hsourceGate
    simpa only [singleQubitLift_inv] using
      (Subgroup.closure (finiteRegisterGenerators (Wire := Wire) generators)).inv_mem
        hsourceGate

/-- A closure representative of a one-qubit gate remains a closure
representative after the continuous concrete local lift. -/
theorem singleQubitLift_mem_generatedUnitaryTopologicalClosure
    (generators : Set (UnitaryGate (Fin 2))) (wire : Wire)
    {gate : UnitaryGate (Fin 2)}
    (hgate : gate ∈ generatedUnitaryTopologicalClosure generators) :
    singleQubitLift wire gate ∈
      generatedUnitaryTopologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators) :=
  map_mem_closure (continuous_singleQubitLift wire) hgate
    (singleQubitLift_mapsTo_generatedUnitarySubgroup generators wire)

/-- Transparent finite-register circuit syntax. `compose first second` means
execute `first` and then `second`, matching the sequential convention of
`AdaptiveIdealClifford.unitaryCompose`. -/
inductive FiniteRegisterCircuit (Wire : Type u) [Fintype Wire] [DecidableEq Wire] where
  | identity : FiniteRegisterCircuit Wire
  | oneQubit (wire : Wire) (gate : UnitaryGate (Fin 2)) : FiniteRegisterCircuit Wire
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      FiniteRegisterCircuit Wire
  | compose (first second : FiniteRegisterCircuit Wire) : FiniteRegisterCircuit Wire

namespace FiniteRegisterCircuit

variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]

/-- Concrete unitary semantics of a finite register circuit. -/
noncomputable def unitary : FiniteRegisterCircuit Wire → UnitaryGate (Bitstring Wire)
  | .identity => 1
  | .oneQubit wire gate => singleQubitLift wire gate
  | .xor control target hdistinct => registerXorGate control target hdistinct
  | .compose first second => second.unitary * first.unitary

@[simp] theorem unitary_identity :
    (identity : FiniteRegisterCircuit Wire).unitary = 1 :=
  rfl

@[simp] theorem unitary_oneQubit (wire : Wire) (gate : UnitaryGate (Fin 2)) :
    (oneQubit wire gate : FiniteRegisterCircuit Wire).unitary =
      singleQubitLift wire gate :=
  rfl

@[simp] theorem unitary_xor (control target : Wire) (hdistinct : control ≠ target) :
    (xor control target hdistinct : FiniteRegisterCircuit Wire).unitary =
      registerXorGate control target hdistinct :=
  rfl

@[simp] theorem unitary_compose (first second : FiniteRegisterCircuit Wire) :
    (compose first second).unitary = second.unitary * first.unitary :=
  rfl

/-- Every explicit circuit has a representative in the register generated
closure, modulo one register-global phase, whenever the one-qubit source set
is projectively dense. -/
theorem finiteRegisterCircuit_has_projectiveClosureRepresentative
    (generators : Set (UnitaryGate (Fin 2)))
    (hdense : ProjectivelyGeneratedDense generators)
    (circuit : FiniteRegisterCircuit Wire) :
    ∃ representative : UnitaryGate (Bitstring Wire),
      representative ∈ generatedUnitaryTopologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators) ∧
      GlobalPhaseEquivalent circuit.unitary representative := by
  induction circuit with
  | identity =>
      refine ⟨1, ?_, globalPhaseEquivalent_refl 1⟩
      exact generatedUnitarySubgroup_subset_topologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators)
        (generatedUnitarySubgroup
          (finiteRegisterGenerators (Wire := Wire) generators)).one_mem
  | oneQubit wire gate =>
      rcases hdense gate with ⟨representative, hrepresentative, hphase⟩
      refine ⟨singleQubitLift wire representative, ?_, ?_⟩
      · exact singleQubitLift_mem_generatedUnitaryTopologicalClosure generators wire
          hrepresentative
      · exact globalPhaseEquivalent_singleQubitLift wire hphase
  | xor control target hdistinct =>
      refine ⟨registerXorGate control target hdistinct, ?_,
        globalPhaseEquivalent_refl _⟩
      apply generatedUnitarySubgroup_subset_topologicalClosure
        (finiteRegisterGenerators (Wire := Wire) generators)
      exact Subgroup.subset_closure
        (registerXorGate_mem_finiteRegisterGenerators generators control target hdistinct)
  | compose first second hfirst hsecond =>
      rcases hfirst with ⟨firstRepresentative, hfirstMem, hfirstPhase⟩
      rcases hsecond with ⟨secondRepresentative, hsecondMem, hsecondPhase⟩
      refine ⟨secondRepresentative * firstRepresentative, ?_, ?_⟩
      · change secondRepresentative * firstRepresentative ∈
          (generatedUnitarySubgroup
            (finiteRegisterGenerators (Wire := Wire) generators)).topologicalClosure
        exact (generatedUnitarySubgroup
          (finiteRegisterGenerators (Wire := Wire) generators)).topologicalClosure.mul_mem
            hsecondMem hfirstMem
      · exact globalPhaseEquivalent_mul hsecondPhase hfirstPhase

/-- The projective closure representative of an explicit circuit yields a
finite-precision approximation at every positive requested precision. -/
theorem finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
    (generators : Set (UnitaryGate (Fin 2)))
    (hdense : ProjectivelyGeneratedDense generators)
    (circuit : FiniteRegisterCircuit Wire) (precision : Real) (hprecision : 0 < precision) :
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) generators) circuit.unitary precision := by
  rcases finiteRegisterCircuit_has_projectiveClosureRepresentative
    generators hdense circuit with
    ⟨representative, hrepresentative, hphase⟩
  exact approximatesModuloPhase_of_globalPhaseEquivalent_mem_generatedUnitaryTopologicalClosure
    hphase hrepresentative hprecision

end FiniteRegisterCircuit
end FiniteRegisterUniversality
end Distillation
end QEC
