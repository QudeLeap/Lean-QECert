import QEC.Semantics.Instruments.Core
/-!
# Finite sequential instrument composition

This module constructs finite sequential instruments from their Kraus
operators. The second instrument is selected by the observed outcome of the
first; completeness and total Born mass are derived rather than stored.
-/

universe u v w x y

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder TensorProduct

noncomputable section

namespace FiniteInstrument

variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/--
Sequentially bind a finite instrument to a finite family of second
instruments selected by the first observed outcome.

The Hilbert spaces may change across the two stages. The terminal observable
outcome remembers both finite observations.
-/
noncomputable def bind (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L) :
    FiniteInstrument (κ × κ') (Sigma Ξ) H L where
  kraus :=
    { operator index :=
      ((J (I.observe index.1)).kraus.operator index.2).comp
        (I.kraus.operator index.1) }
  observe := fun index =>
    ⟨I.observe index.1, (J (I.observe index.1)).observe index.2⟩

/-- A composite raw Kraus branch is the selected second branch after the first. -/
theorem bind_kraus_operator (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ') :
    (I.bind J).kraus.operator (firstIndex, secondIndex) =
      ((J (I.observe firstIndex)).kraus.operator secondIndex).comp
        (I.kraus.operator firstIndex) :=
  rfl

/-- A retained composite observation is exactly the selected second branch
applied to the retained first branch.  The predecessor branch remains
unnormalized, so this identity introduces no conditional-state division. -/
theorem bind_branchOperator (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (firstOutcome : Ω) (secondOutcome : Ξ firstOutcome) (A : Operator H) :
    (I.bind J).branchOperator ⟨firstOutcome, secondOutcome⟩ A =
      (J firstOutcome).branchOperator secondOutcome
        (I.branchOperator firstOutcome A) := by
  classical
  unfold branchOperator
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro secondIndex _
  by_cases hsecond : (J firstOutcome).observe secondIndex = secondOutcome
  · rw [if_pos hsecond]
    ext vector
    simp only [bind, LinearMap.adjoint_comp, LinearMap.comp_apply,
      LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro firstIndex _
    by_cases hfirst : I.observe firstIndex = firstOutcome
    · subst firstOutcome
      simp [hsecond, LinearMap.comp_apply]
    · simp [hfirst]
  · rw [if_neg hsecond]
    apply Finset.sum_eq_zero
    intro firstIndex _
    by_cases hfirst : I.observe firstIndex = firstOutcome
    · subst firstOutcome
      have hobserve :
          (I.bind J).observe (firstIndex, secondIndex) ≠
            ⟨I.observe firstIndex, secondOutcome⟩ := by
        intro heq
        change
          (⟨I.observe firstIndex,
              (J (I.observe firstIndex)).observe secondIndex⟩ : Sigma Ξ) =
            ⟨I.observe firstIndex, secondOutcome⟩ at heq
        cases heq
        exact hsecond rfl
      rw [if_neg hobserve]
    · have hcomposite :
          (⟨I.observe firstIndex,
              (J (I.observe firstIndex)).observe secondIndex⟩ : Sigma Ξ) ≠
            ⟨firstOutcome, secondOutcome⟩ := by
        intro heq
        exact hfirst (congrArg Sigma.fst heq)
      have hobserve :
          (I.bind J).observe (firstIndex, secondIndex) ≠
            ⟨firstOutcome, secondOutcome⟩ := by
        simpa only [bind] using hcomposite
      rw [if_neg hobserve]

/-- The composite induced map is the finite sum of outcome-selected second maps. -/
theorem bind_inducedMap_apply (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (A : Operator H) :
    (I.bind J).kraus.inducedMap A =
      ∑ firstIndex : κ,
        (J (I.observe firstIndex)).kraus.inducedMap
          ((I.kraus.operator firstIndex).comp
            (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by
  ext x
  simp only [FiniteKrausFamily.inducedMap_apply, bind,
    LinearMap.adjoint_comp, LinearMap.comp_apply, LinearMap.sum_apply,
    Fintype.sum_prod_type]

/-- Completeness is preserved by outcome-selected finite sequential binding. -/
theorem bind_complete (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) :
    (I.bind J).kraus.Complete := by
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [I.bind_inducedMap_apply J A, map_sum]
  calc
    (∑ firstIndex : κ,
        LinearMap.trace Complex L
          ((J (I.observe firstIndex)).kraus.inducedMap
            ((I.kraus.operator firstIndex).comp
              (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))))) =
        ∑ firstIndex : κ,
          LinearMap.trace Complex K
            ((I.kraus.operator firstIndex).comp
              (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by
          apply Finset.sum_congr rfl
          intro firstIndex _
          exact
            (J (I.observe firstIndex)).kraus.inducedMap_trace_preserving
              (hJ (I.observe firstIndex)) _
    _ = LinearMap.trace Complex K (I.kraus.inducedMap A) := by
          rw [FiniteKrausFamily.inducedMap_apply, map_sum]
    _ = LinearMap.trace Complex H A :=
          I.kraus.inducedMap_trace_preserving hI A

/-- Complete sequential binding has normalized total observable Born mass. -/
theorem bind_sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome, (I.bind J).bornWeight outcome rho = 1 :=
  (I.bind J).sum_bornWeight_eq_one (I.bind_complete J hI hJ) rho

section Tensor

variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

private theorem tensorMap_sum_sum (a : κ → Operator H) (b : κ' → Operator R) :
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
      ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
  classical
  have hleft (s : Finset κ) :
      TensorProduct.map (∑ i ∈ s, a i) (∑ j, b j) =
        ∑ i ∈ s, TensorProduct.map (a i) (∑ j, b j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
  have hright (i : κ) (t : Finset κ') :
      TensorProduct.map (a i) (∑ j ∈ t, b j) =
        ∑ j ∈ t, TensorProduct.map (a i) (b j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
        simp [Finset.sum_insert hj, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
        ∑ i, TensorProduct.map (a i) (∑ j, b j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ

/--
Run two finite instruments on disjoint tensor factors.

Every composite Kraus operator is the actual tensor product of one left and
one right Kraus operator, and the visible outcome records both observations.
-/
noncomputable def tensor (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S) :
    FiniteInstrument (κ × κ') (Ω × Ω')
      (CompositeSystem H R) (CompositeSystem K S) where
  kraus :=
    { operator index :=
      TensorProduct.map (I.kraus.operator index.1) (J.kraus.operator index.2) }
  observe := fun index => (I.observe index.1, J.observe index.2)

/-- A raw parallel Kraus branch is the tensor product of its two disjoint branches. -/
theorem tensor_kraus_operator (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (leftIndex : κ) (rightIndex : κ') :
    (I.tensor J).kraus.operator (leftIndex, rightIndex) =
      TensorProduct.map (I.kraus.operator leftIndex) (J.kraus.operator rightIndex) :=
  rfl

/-- The observable outcome of a parallel branch is the pair of its observations. -/
theorem tensor_observe (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (leftIndex : κ) (rightIndex : κ') :
    (I.tensor J).observe (leftIndex, rightIndex) =
      (I.observe leftIndex, J.observe rightIndex) :=
  rfl

/-- Completeness is preserved by disjoint tensor composition of finite instruments. -/
theorem tensor_complete (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete) :
    (I.tensor J).kraus.Complete := by
  classical
  rw [FiniteKrausFamily.Complete]
  calc
    (∑ index : κ × κ',
        (LinearMap.adjoint ((I.tensor J).kraus.operator index)).comp
          ((I.tensor J).kraus.operator index)) =
        ∑ leftIndex, ∑ rightIndex,
          TensorProduct.map
            ((LinearMap.adjoint (I.kraus.operator leftIndex)).comp
              (I.kraus.operator leftIndex))
            ((LinearMap.adjoint (J.kraus.operator rightIndex)).comp
              (J.kraus.operator rightIndex)) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro leftIndex _
          apply Finset.sum_congr rfl
          intro rightIndex _
          simp only [tensor]
          rw [TensorProduct.adjoint_map, ← TensorProduct.map_comp]
    _ = TensorProduct.map
        (∑ leftIndex,
          (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
            (I.kraus.operator leftIndex))
        (∑ rightIndex,
          (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
            (J.kraus.operator rightIndex)) := by
          rw [tensorMap_sum_sum]
    _ = TensorProduct.map (1 : Operator H) (1 : Operator R) := by
          rw [hI, hJ]
    _ = 1 := TensorProduct.map_one

/-- Complete parallel composition has normalized total observable Born mass. -/
theorem tensor_sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    ∑ outcome, (I.tensor J).bornWeight outcome rho = 1 :=
  (I.tensor J).sum_bornWeight_eq_one (I.tensor_complete J hI hJ) rho

end Tensor

section TensorPower

/-- The recursively accumulated raw-index and observed-outcome history. -/
def tensorPowerHistory (α : Type v) : Nat → Type v
  | 0 => PUnit
  | n + 1 => α × tensorPowerHistory α n

instance tensorPowerHistoryFintype (α : Type v) [Fintype α] (n : Nat) :
    Fintype (tensorPowerHistory α n) := by
  induction n with
  | zero =>
      simpa [tensorPowerHistory] using (inferInstance : Fintype PUnit)
  | succ n ih =>
      simpa [tensorPowerHistory] using
        (inferInstance : Fintype (α × tensorPowerHistory α n))

/--
A finite-dimensional complex Hilbert carrier with its concrete structures.

Packaging the structures lets tensor-power carriers recurse through Mathlib's
actual tensor product without asking typeclass search to unfold an open natural
number.
-/
structure TensorPowerSystem where
  carrier : Type u
  normedAddCommGroup : NormedAddCommGroup carrier
  innerProductSpace : @InnerProductSpace Complex carrier (inferInstance : RCLike Complex)
    normedAddCommGroup.toSeminormedAddCommGroup
  finiteDimensional :
    letI : NormedAddCommGroup carrier := normedAddCommGroup
    letI : InnerProductSpace Complex carrier := innerProductSpace
    FiniteQuantumSystem carrier

noncomputable instance (S : TensorPowerSystem) : NormedAddCommGroup S.carrier :=
  S.normedAddCommGroup

noncomputable instance (S : TensorPowerSystem) : InnerProductSpace Complex S.carrier :=
  S.innerProductSpace

noncomputable instance (S : TensorPowerSystem) : FiniteQuantumSystem S.carrier :=
  S.finiteDimensional

@[reducible] private noncomputable def tensorPowerSystemOf (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] : TensorPowerSystem := by
  let normed : NormedAddCommGroup H := inferInstance
  letI : NormedAddCommGroup H := normed
  let inner : InnerProductSpace Complex H := inferInstance
  letI : InnerProductSpace Complex H := inner
  let finite : FiniteQuantumSystem H := inferInstance
  exact
    { carrier := H
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }

/-- The concrete one-dimensional complex tensor unit used at depth zero. -/
@[reducible] private noncomputable def tensorUnitSystem : TensorPowerSystem := by
  let normed : NormedAddCommGroup (EuclideanSpace Complex (ULift.{u} (Fin 1))) :=
    inferInstance
  letI : NormedAddCommGroup (EuclideanSpace Complex (ULift.{u} (Fin 1))) := normed
  let inner : InnerProductSpace Complex (EuclideanSpace Complex (ULift.{u} (Fin 1))) :=
    inferInstance
  letI : InnerProductSpace Complex (EuclideanSpace Complex (ULift.{u} (Fin 1))) := inner
  let finite : FiniteQuantumSystem (EuclideanSpace Complex (ULift.{u} (Fin 1))) :=
    inferInstance
  exact
    { carrier := EuclideanSpace Complex (ULift.{u} (Fin 1))
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }

@[reducible] private noncomputable def tensorPowerSystemTensor (S T : TensorPowerSystem) :
    TensorPowerSystem := by
  letI : NormedAddCommGroup S.carrier := S.normedAddCommGroup
  letI : InnerProductSpace Complex S.carrier := S.innerProductSpace
  letI : FiniteQuantumSystem S.carrier := S.finiteDimensional
  letI : NormedAddCommGroup T.carrier := T.normedAddCommGroup
  letI : InnerProductSpace Complex T.carrier := T.innerProductSpace
  letI : FiniteQuantumSystem T.carrier := T.finiteDimensional
  let normed : NormedAddCommGroup (S.carrier ⊗[Complex] T.carrier) := inferInstance
  letI : NormedAddCommGroup (S.carrier ⊗[Complex] T.carrier) := normed
  let inner : InnerProductSpace Complex (S.carrier ⊗[Complex] T.carrier) := inferInstance
  letI : InnerProductSpace Complex (S.carrier ⊗[Complex] T.carrier) := inner
  let finite : FiniteQuantumSystem (S.carrier ⊗[Complex] T.carrier) := inferInstance
  exact
    { carrier := S.carrier ⊗[Complex] T.carrier
      normedAddCommGroup := normed
      innerProductSpace := inner
      finiteDimensional := finite }

/--
The actual recursively tensorized carrier: the tensor unit at zero and a new
left factor at every successor.
-/
@[reducible] noncomputable def tensorPowerSystem (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] : Nat → TensorPowerSystem
  | 0 => tensorUnitSystem
  | n + 1 => tensorPowerSystemTensor (tensorPowerSystemOf H) (tensorPowerSystem H n)

/-- The carrier underlying `tensorPowerSystem`. -/
abbrev tensorPowerCarrier (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] (n : Nat) : Type u :=
  (tensorPowerSystem H n).carrier

/-- The literal one-branch identity instrument on the concrete tensor unit. -/
noncomputable def tensorUnitInstrument :
    FiniteInstrument PUnit PUnit tensorUnitSystem.carrier tensorUnitSystem.carrier where
  kraus := { operator _ := 1 }
  observe := fun _ => PUnit.unit

theorem tensorUnitInstrument_kraus_operator :
    tensorUnitInstrument.kraus.operator PUnit.unit = 1 :=
  rfl

theorem tensorUnitInstrument_complete : tensorUnitInstrument.kraus.Complete := by
  rw [FiniteKrausFamily.Complete]
  ext x
  simp [tensorUnitInstrument]

/--
The homogeneous finite tensor power of one instrument. Its zero-th level is
the literal tensor-unit identity instrument, and its successor is exactly the
compiled binary `tensor` construction.
-/
noncomputable def tensorPower (I : FiniteInstrument κ Ω H K) : (n : Nat) →
    FiniteInstrument (tensorPowerHistory κ n) (tensorPowerHistory Ω n)
      (tensorPowerCarrier H n) (tensorPowerCarrier K n)
  | 0 => tensorUnitInstrument
  | n + 1 => I.tensor (tensorPower I n)

/-- Depth zero has the literal identity raw branch on the tensor unit. -/
theorem tensorPower_zero_kraus_operator (I : FiniteInstrument κ Ω H K) :
    (I.tensorPower 0).kraus.operator PUnit.unit = 1 :=
  rfl

/-- A successor raw branch is the supplied head branch tensored with its history tail. -/
theorem tensorPower_kraus_operator_succ (I : FiniteInstrument κ Ω H K)
    (n : Nat) (head : κ) (tail : tensorPowerHistory κ n) :
    (I.tensorPower (n + 1)).kraus.operator (head, tail) =
      TensorProduct.map (I.kraus.operator head)
        ((I.tensorPower n).kraus.operator tail) :=
  rfl

/-- A successor observation keeps the supplied head outcome and its history tail. -/
theorem tensorPower_observe_succ (I : FiniteInstrument κ Ω H K)
    (n : Nat) (head : κ) (tail : tensorPowerHistory κ n) :
    (I.tensorPower (n + 1)).observe (head, tail) =
      (I.observe head, (I.tensorPower n).observe tail) :=
  rfl

/-- Completeness follows by recursion from unit identity and binary tensor completeness. -/
theorem tensorPower_complete (I : FiniteInstrument κ Ω H K)
    (hI : I.kraus.Complete) (n : Nat) :
    (I.tensorPower n).kraus.Complete := by
  induction n with
  | zero => exact tensorUnitInstrument_complete
  | succ n ih => exact I.tensor_complete (I.tensorPower n) hI ih

/-- Complete homogeneous tensor powers have normalized total observable Born mass. -/
theorem tensorPower_sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (hI : I.kraus.Complete) (n : Nat)
    (rho : DensityOperator (tensorPowerCarrier H n)) :
    ∑ outcome, (I.tensorPower n).bornWeight outcome rho = 1 :=
  (I.tensorPower n).sum_bornWeight_eq_one (I.tensorPower_complete hI n) rho

end TensorPower

end FiniteInstrument

end
end Semantics
end QEC
