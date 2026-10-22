import QEC.Coding.Stabilizer.Measurement

/-!
# Finite joint stabilizer measurement

This module builds the joint syndrome measurement of a finite pairwise
commuting family of signed Hermitian binary Paulis.  Products are formed with
`Finset.noncommProd`: the multiplication remains noncommutative in the type,
and the required pairwise commutation proof is carried explicitly.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PauliSymplectic

open Semantics
open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- A joint measurement outcome assigns one visible sign to every check. -/
abbrev JointSyndrome (κ : Type v) := κ → StabilizerOutcome

/-- The single-check factor selected by a joint syndrome. -/
def jointStabilizerFactor (checks : κ → Binary ι)
    (syndrome : JointSyndrome κ) (check : κ) :
    Operator (Qubit.QubitRegister ι) :=
  stabilizerProjector (checks check) (syndrome check)

/-- Symplectic pairwise commutation gives concrete commutation of all factors. -/
theorem jointStabilizerFactor_commute
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (left right : κ) (syndromeLeft syndromeRight : JointSyndrome κ) :
    Commute (jointStabilizerFactor checks syndromeLeft left)
      (jointStabilizerFactor checks syndromeRight right) := by
  unfold jointStabilizerFactor stabilizerProjector
  have hoperator :
      toHermitianQubitOperator (checks left) *
          toHermitianQubitOperator (checks right) =
        toHermitianQubitOperator (checks right) *
          toHermitianQubitOperator (checks left) :=
    toHermitianQubitOperator_commute_of_commutes
      (checks left) (checks right) (hcomm left right)
  change
    ((1 / 2 : Complex) •
        (1 + (syndromeLeft left).sign •
          toHermitianQubitOperator (checks left))) *
      ((1 / 2 : Complex) •
        (1 + (syndromeRight right).sign •
          toHermitianQubitOperator (checks right))) =
    ((1 / 2 : Complex) •
        (1 + (syndromeRight right).sign •
          toHermitianQubitOperator (checks right))) *
      ((1 / 2 : Complex) •
        (1 + (syndromeLeft left).sign •
          toHermitianQubitOperator (checks left)))
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul_comm]
  rw [hoperator]
  module

/-- Every selected single-check factor is self-adjoint. -/
private theorem jointStabilizerFactor_adjoint
    (checks : κ → Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    LinearMap.adjoint (jointStabilizerFactor checks syndrome check) =
      jointStabilizerFactor checks syndrome check :=
  stabilizerProjector_adjoint (checks check) (syndrome check)

/-- The finite check family supplies the pairwise witness needed by `noncommProd`. -/
private theorem jointStabilizerFactor_pairwise
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    (selected : Set κ).Pairwise
      (Function.onFun Commute (jointStabilizerFactor checks syndrome)) := by
  intro left _ right _ _
  exact jointStabilizerFactor_commute checks hcomm left right syndrome syndrome

/--
The literal joint syndrome projector
`Π_λ = ∏ⱼ (I + λⱼ Sⱼ) / 2`.

The `noncommProd` retains multiplication in the operator algebra; its explicit
pairwise witness is the formal record that symplectic commutation justifies
the order-independent finite product.
-/
noncomputable def jointStabilizerProjector
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    Operator (Qubit.QubitRegister ι) :=
  Finset.univ.noncommProd (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)

/-- Finite products of the selected commuting spectral factors are self-adjoint. -/
private theorem jointStabilizerProjectorOn_adjoint
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    LinearMap.adjoint
        (selected.noncommProd (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome selected)) =
      selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | insert check selected hnotmem induction =>
      have hrest : (selected : Set κ).Pairwise
          (Function.onFun Commute (jointStabilizerFactor checks syndrome)) :=
        (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := selected.noncommProd (jointStabilizerFactor checks syndrome) hrest
      have hfactor : (insert check selected).noncommProd
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) =
          jointStabilizerFactor checks syndrome check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem selected check
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) hnotmem]
      have hcommRest : Commute (jointStabilizerFactor checks syndrome check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute selected (jointStabilizerFactor checks syndrome) hrest
          (jointStabilizerFactor checks syndrome check)
          (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
      calc
        LinearMap.adjoint ((insert check selected).noncommProd
            (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected))) =
            LinearMap.adjoint (jointStabilizerFactor checks syndrome check * productRest) := by
              rw [hfactor]
        _ = LinearMap.adjoint productRest *
            LinearMap.adjoint (jointStabilizerFactor checks syndrome check) := by
              rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]
        _ = productRest * jointStabilizerFactor checks syndrome check := by
              rw [show LinearMap.adjoint productRest = productRest by
                dsimp [productRest]
                exact induction, jointStabilizerFactor_adjoint]
        _ = jointStabilizerFactor checks syndrome check * productRest := hcommRest.eq.symm
        _ = (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) :=
              hfactor.symm

/-- Every joint syndrome projector is self-adjoint. -/
theorem jointStabilizerProjector_adjoint
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    LinearMap.adjoint (jointStabilizerProjector checks hcomm syndrome) =
      jointStabilizerProjector checks hcomm syndrome :=
  jointStabilizerProjectorOn_adjoint checks hcomm syndrome Finset.univ

/-- Every selected single-check factor is idempotent. -/
private theorem jointStabilizerFactor_idempotent
    (checks : κ → Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerFactor checks syndrome check *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerFactor checks syndrome check :=
  stabilizerProjector_idempotent (checks check) (syndrome check)

/-- A finite noncommutative product of the commuting spectral factors is idempotent. -/
private theorem jointStabilizerProjectorOn_idempotent
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) *
      selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) =
      selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | insert check selected hnotmem induction =>
      have hrest : (selected : Set κ).Pairwise
          (Function.onFun Commute (jointStabilizerFactor checks syndrome)) :=
        (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := selected.noncommProd (jointStabilizerFactor checks syndrome) hrest
      have hfactor : (insert check selected).noncommProd
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) =
          jointStabilizerFactor checks syndrome check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem selected check
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) hnotmem]
      have hcommRest : Commute (jointStabilizerFactor checks syndrome check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute selected (jointStabilizerFactor checks syndrome) hrest
          (jointStabilizerFactor checks syndrome check)
          (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
      calc
        (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) *
          (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) =
            (jointStabilizerFactor checks syndrome check * productRest) *
              (jointStabilizerFactor checks syndrome check * productRest) := by rw [hfactor]
        _ = jointStabilizerFactor checks syndrome check *
              (productRest * jointStabilizerFactor checks syndrome check) * productRest := by
              simp only [mul_assoc]
        _ = jointStabilizerFactor checks syndrome check *
              (jointStabilizerFactor checks syndrome check * productRest) * productRest := by
              rw [hcommRest.eq]
        _ = (jointStabilizerFactor checks syndrome check *
              jointStabilizerFactor checks syndrome check) * (productRest * productRest) := by
              simp only [mul_assoc]
        _ = jointStabilizerFactor checks syndrome check * productRest := by
              rw [jointStabilizerFactor_idempotent]
              rw [show productRest * productRest = productRest by
                dsimp [productRest]
                exact induction]
        _ = (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) :=
              hfactor.symm

/-- Every joint syndrome projector is idempotent. -/
theorem jointStabilizerProjector_idempotent
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome :=
  jointStabilizerProjectorOn_idempotent checks hcomm syndrome Finset.univ

/-- Multiplying the joint projector by one of its selected factors changes nothing. -/
private theorem jointStabilizerProjector_mul_factor
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerProjector checks hcomm syndrome := by
  classical
  let reduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome (Finset.univ.erase check))
  have hfactor : reduced * jointStabilizerFactor checks syndrome check =
      jointStabilizerProjector checks hcomm syndrome := by
    simpa [reduced, jointStabilizerProjector] using
      (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
        (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ))
  calc
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerFactor checks syndrome check =
        (reduced * jointStabilizerFactor checks syndrome check) *
          jointStabilizerFactor checks syndrome check := by rw [hfactor]
    _ = reduced *
        (jointStabilizerFactor checks syndrome check *
          jointStabilizerFactor checks syndrome check) := by rw [mul_assoc]
    _ = reduced * jointStabilizerFactor checks syndrome check := by
        rw [jointStabilizerFactor_idempotent]
    _ = jointStabilizerProjector checks hcomm syndrome := hfactor

/-- Each selected factor also fixes the joint projector from the left. -/
private theorem jointStabilizerFactor_mul_jointStabilizerProjector
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerFactor checks syndrome check *
        jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome := by
  have hcommProduct : Commute (jointStabilizerFactor checks syndrome check)
      (jointStabilizerProjector checks hcomm syndrome) := by
    unfold jointStabilizerProjector
    exact Finset.noncommProd_commute Finset.univ
      (jointStabilizerFactor checks syndrome)
      (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)
      (jointStabilizerFactor checks syndrome check)
      (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
  rw [hcommProduct.eq]
  exact jointStabilizerProjector_mul_factor checks hcomm syndrome check

/-- A selected one-check projector is an eigenprojector for its Hermitian Pauli. -/
private theorem jointStabilizerFactor_eigen
    (checks : κ → Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator (checks check) *
        jointStabilizerFactor checks syndrome check =
      (syndrome check).sign • jointStabilizerFactor checks syndrome check := by
  unfold jointStabilizerFactor stabilizerProjector
  cases outcome : syndrome check <;>
    simp only [outcome, StabilizerOutcome.sign, smul_mul_assoc,
      mul_smul_comm, mul_add, mul_one, toHermitianQubitOperator_square] <;>
    module

/-- Each check acts on its joint spectral projector by the selected eigenvalue. -/
theorem jointStabilizerProjector_eigen
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator (checks check) *
        jointStabilizerProjector checks hcomm syndrome =
      (syndrome check).sign • jointStabilizerProjector checks hcomm syndrome := by
  let factor := jointStabilizerFactor checks syndrome check
  have hfactor : factor * jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome :=
    jointStabilizerFactor_mul_jointStabilizerProjector checks hcomm syndrome check
  calc
    toHermitianQubitOperator (checks check) *
        jointStabilizerProjector checks hcomm syndrome =
      toHermitianQubitOperator (checks check) *
        (factor * jointStabilizerProjector checks hcomm syndrome) := by rw [hfactor]
    _ = (toHermitianQubitOperator (checks check) * factor) *
        jointStabilizerProjector checks hcomm syndrome := by rw [mul_assoc]
    _ = ((syndrome check).sign • factor) *
        jointStabilizerProjector checks hcomm syndrome := by
      rw [show toHermitianQubitOperator (checks check) * factor =
        (syndrome check).sign • factor by
          dsimp [factor]
          exact jointStabilizerFactor_eigen checks syndrome check]
    _ = (syndrome check).sign •
        (factor * jointStabilizerProjector checks hcomm syndrome) := by
      rw [smul_mul_assoc]
    _ = (syndrome check).sign • jointStabilizerProjector checks hcomm syndrome := by
      rw [hfactor]

/-- A vector fixed by every selected spectral factor is fixed by their joint projector. -/
private theorem jointStabilizerProjector_apply_eq_self_of_factor_fixed
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (psi : Qubit.QubitRegister ι)
    (hfixed : ∀ check, jointStabilizerFactor checks syndrome check psi = psi) :
    jointStabilizerProjector checks hcomm syndrome psi = psi := by
  unfold jointStabilizerProjector
  refine Finset.noncommProd_induction Finset.univ
    (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)
    (fun product => product psi = psi) ?_ ?_ ?_
  · intro A B hA hB
    simp only [Module.End.mul_apply, hB, hA]
  · rfl
  · intro check _
    exact hfixed check

/--
The joint projector fixes exactly the simultaneous signed eigenspace of the
commuting Hermitian binary checks.
-/
theorem jointStabilizerProjector_fixed_iff
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (psi : Qubit.QubitRegister ι) :
    jointStabilizerProjector checks hcomm syndrome psi = psi ↔
      ∀ check, toHermitianQubitOperator (checks check) psi =
        (syndrome check).sign • psi := by
  constructor
  · intro hfixed check
    apply (stabilizerProjector_fixed_iff (checks check) (syndrome check) psi).1
    have hfactor := congrArg (fun operator : Operator (Qubit.QubitRegister ι) => operator psi)
      (jointStabilizerFactor_mul_jointStabilizerProjector checks hcomm syndrome check)
    change jointStabilizerFactor checks syndrome check
        (jointStabilizerProjector checks hcomm syndrome psi) =
      jointStabilizerProjector checks hcomm syndrome psi at hfactor
    calc
      jointStabilizerFactor checks syndrome check psi =
          jointStabilizerFactor checks syndrome check
            (jointStabilizerProjector checks hcomm syndrome psi) := by rw [hfixed]
      _ = jointStabilizerProjector checks hcomm syndrome psi := hfactor
      _ = psi := hfixed
  · intro heigen
    apply jointStabilizerProjector_apply_eq_self_of_factor_fixed checks hcomm syndrome psi
    intro check
    exact (stabilizerProjector_fixed_iff (checks check) (syndrome check) psi).2 (heigen check)

/-- Distinct binary outcomes are precisely opposite outcomes. -/
private theorem StabilizerOutcome.eq_opposite_of_ne
    (left right : StabilizerOutcome) (hne : left ≠ right) :
    right = left.opposite := by
  cases left <;> cases right <;>
    simp [StabilizerOutcome.opposite] at hne ⊢

/-- Isolate one selected spectral factor at the right of its finite product. -/
private theorem jointStabilizerProjector_erase_mul
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    (Finset.univ.erase check).noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome (Finset.univ.erase check)) *
      jointStabilizerFactor checks syndrome check =
        jointStabilizerProjector checks hcomm syndrome := by
  classical
  simpa [jointStabilizerProjector] using
    (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
      (jointStabilizerFactor checks syndrome)
      (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ))

/-- Distinct joint syndromes differ at at least one finite check. -/
private theorem exists_check_of_jointSyndrome_ne
    (left right : JointSyndrome κ) (hne : left ≠ right) :
    ∃ check, left check ≠ right check := by
  classical
  by_contra hnone
  push_neg at hnone
  exact hne (funext hnone)

/-- Different joint syndromes have zero product in the displayed order. -/
theorem jointStabilizerProjector_mul_of_ne
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndromeLeft syndromeRight : JointSyndrome κ) (hne : syndromeLeft ≠ syndromeRight) :
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight = 0 := by
  classical
  obtain ⟨check, hcheck⟩ :=
    exists_check_of_jointSyndrome_ne syndromeLeft syndromeRight hne
  have hopposite : syndromeRight check = (syndromeLeft check).opposite :=
    StabilizerOutcome.eq_opposite_of_ne (syndromeLeft check) (syndromeRight check) hcheck
  let leftReduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndromeLeft)
    (jointStabilizerFactor_pairwise checks hcomm syndromeLeft (Finset.univ.erase check))
  let rightReduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndromeRight)
    (jointStabilizerFactor_pairwise checks hcomm syndromeRight (Finset.univ.erase check))
  have hleftFactor : leftReduced * jointStabilizerFactor checks syndromeLeft check =
      jointStabilizerProjector checks hcomm syndromeLeft := by
    exact jointStabilizerProjector_erase_mul checks hcomm syndromeLeft check
  have hrightFactor : rightReduced * jointStabilizerFactor checks syndromeRight check =
      jointStabilizerProjector checks hcomm syndromeRight := by
    exact jointStabilizerProjector_erase_mul checks hcomm syndromeRight check
  have hcross : Commute (jointStabilizerFactor checks syndromeLeft check) rightReduced := by
    dsimp [rightReduced]
    exact Finset.noncommProd_commute (Finset.univ.erase check)
      (jointStabilizerFactor checks syndromeRight)
      (jointStabilizerFactor_pairwise checks hcomm syndromeRight (Finset.univ.erase check))
      (jointStabilizerFactor checks syndromeLeft check)
      (fun other _ =>
        jointStabilizerFactor_commute checks hcomm check other syndromeLeft syndromeRight)
  have hsingle : jointStabilizerFactor checks syndromeLeft check *
      jointStabilizerFactor checks syndromeRight check = 0 := by
    change stabilizerProjector (checks check) (syndromeLeft check) *
        stabilizerProjector (checks check) (syndromeRight check) = 0
    rw [hopposite]
    exact stabilizerProjector_mul_opposite (checks check) (syndromeLeft check)
  calc
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight =
        (leftReduced * jointStabilizerFactor checks syndromeLeft check) *
          (rightReduced * jointStabilizerFactor checks syndromeRight check) := by
            rw [hleftFactor, hrightFactor]
    _ = leftReduced *
        (jointStabilizerFactor checks syndromeLeft check * rightReduced) *
          jointStabilizerFactor checks syndromeRight check := by
            simp only [mul_assoc]
    _ = leftReduced *
        (rightReduced * jointStabilizerFactor checks syndromeLeft check) *
          jointStabilizerFactor checks syndromeRight check := by
            rw [hcross.eq]
    _ = (leftReduced * rightReduced) *
        (jointStabilizerFactor checks syndromeLeft check *
          jointStabilizerFactor checks syndromeRight check) := by
            simp only [mul_assoc]
    _ = 0 := by rw [hsingle, mul_zero]

/-- Different joint syndromes have zero product in the reverse displayed order. -/
theorem jointStabilizerProjector_mul_of_ne_reverse
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndromeLeft syndromeRight : JointSyndrome κ) (hne : syndromeLeft ≠ syndromeRight) :
    jointStabilizerProjector checks hcomm syndromeRight *
      jointStabilizerProjector checks hcomm syndromeLeft = 0 :=
  jointStabilizerProjector_mul_of_ne checks hcomm syndromeRight syndromeLeft hne.symm

/-- The factor associated to a partial syndrome, extended by the identity away from its support. -/
private def jointStabilizerPartialFactor (checks : κ → Binary ι)
    (selected : Finset κ) (syndrome : ∀ check, check ∈ selected → StabilizerOutcome)
    (check : κ) : Operator (Qubit.QubitRegister ι) :=
  if hmem : check ∈ selected then
    stabilizerProjector (checks check) (syndrome check hmem)
  else 1

/-- A finite product of the factors selected by a partial syndrome. -/
private noncomputable def jointStabilizerPartialProjector (checks : κ → Binary ι)
    (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (selected : Finset κ) (syndrome : ∀ check, check ∈ selected → StabilizerOutcome) :
    Operator (Qubit.QubitRegister ι) :=
  selected.noncommProd (jointStabilizerPartialFactor checks selected syndrome) (by
    intro left hleft right hright _
    change jointStabilizerPartialFactor checks selected syndrome left *
        jointStabilizerPartialFactor checks selected syndrome right =
      jointStabilizerPartialFactor checks selected syndrome right *
        jointStabilizerPartialFactor checks selected syndrome left
    let totalSyndrome : JointSyndrome κ :=
      fun check => if hmem : check ∈ selected then syndrome check hmem else .positive
    have hleft' : left ∈ selected := by simpa using hleft
    have hright' : right ∈ selected := by simpa using hright
    have hleftFactor : jointStabilizerPartialFactor checks selected syndrome left =
        jointStabilizerFactor checks totalSyndrome left := by
      unfold jointStabilizerPartialFactor jointStabilizerFactor
      rw [dif_pos hleft']
      simp only [totalSyndrome, dif_pos hleft']
    have hrightFactor : jointStabilizerPartialFactor checks selected syndrome right =
        jointStabilizerFactor checks totalSyndrome right := by
      unfold jointStabilizerPartialFactor jointStabilizerFactor
      rw [dif_pos hright']
      simp only [totalSyndrome, dif_pos hright']
    rw [hleftFactor, hrightFactor]
    exact jointStabilizerFactor_commute checks hcomm left right totalSyndrome totalSyndrome)

/-- Extending a partial syndrome by one check splits off exactly that spectral factor. -/
private theorem jointStabilizerPartialProjector_insert
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (check : κ) (selected : Finset κ) (hnotmem : check ∉ selected)
    (outcome : StabilizerOutcome)
    (syndrome : ∀ other, other ∈ selected → StabilizerOutcome) :
    jointStabilizerPartialProjector checks hcomm (insert check selected)
        (Finset.prodPiInsert (s := selected) (a := check)
          (fun _ => StabilizerOutcome) (outcome, syndrome)) =
      stabilizerProjector (checks check) outcome *
        jointStabilizerPartialProjector checks hcomm selected syndrome := by
  classical
  let extended := Finset.prodPiInsert (s := selected) (a := check)
    (fun _ => StabilizerOutcome) (outcome, syndrome)
  let insertedFactor := jointStabilizerPartialFactor checks (insert check selected) extended
  let remainingFactor := jointStabilizerPartialFactor checks selected syndrome
  have hcheck : insertedFactor check = stabilizerProjector (checks check) outcome := by
    simp [insertedFactor, extended, jointStabilizerPartialFactor,
      Finset.prodPiInsert]
  have hremaining : ∀ other ∈ selected, insertedFactor other = remainingFactor other := by
    intro other hother
    have hne : other ≠ check := by
      intro heq
      subst other
      exact hnotmem hother
    simp only [insertedFactor, remainingFactor, extended, jointStabilizerPartialFactor,
      dif_pos (Finset.mem_insert_of_mem hother), dif_pos hother,
      Finset.prodPiInsert, dif_neg hne]
  change (insert check selected).noncommProd insertedFactor _ =
    stabilizerProjector (checks check) outcome * selected.noncommProd remainingFactor _
  have hpair : (↑(insert check selected) : Set κ).Pairwise
      (Function.onFun Commute insertedFactor) := by
    intro left hleft right hright _
    change left ∈ insert check selected at hleft
    change right ∈ insert check selected at hright
    simp only [Function.onFun, insertedFactor, jointStabilizerPartialFactor,
      dif_pos hleft, dif_pos hright]
    simpa only [jointStabilizerFactor] using
      jointStabilizerFactor_commute checks hcomm left right
        (fun _ => extended left hleft) (fun _ => extended right hright)
  have hrest := hpair.mono (fun _ => Finset.mem_insert_of_mem)
  trans insertedFactor check * selected.noncommProd insertedFactor hrest
  · exact Finset.noncommProd_insert_of_notMem selected check insertedFactor hpair hnotmem
  rw [hcheck]
  congr 1
  exact Finset.noncommProd_congr rfl hremaining hrest

/-- The two one-check spectral projectors sum to the identity. -/
private theorem sum_stabilizerProjector_eq_one (P : Binary ι) :
    ∑ outcome : StabilizerOutcome, stabilizerProjector P outcome = 1 := by
  rw [show (Finset.univ : Finset StabilizerOutcome) = {.positive, .negative} by decide]
  simpa [StabilizerOutcome.opposite] using stabilizerProjector_add_opposite P .positive

/-- Summing all partial syndrome projectors resolves the identity. -/
private theorem sum_jointStabilizerPartialProjector_eq_one
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (selected : Finset κ) :
    ∑ syndrome : (∀ check, check ∈ selected → StabilizerOutcome),
      jointStabilizerPartialProjector checks hcomm selected syndrome = 1 := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      let emptySyndrome : ∀ check, check ∈ (∅ : Finset κ) → StabilizerOutcome :=
        fun _ hmem => (by simpa using hmem : False).elim
      letI : Unique (∀ check, check ∈ (∅ : Finset κ) → StabilizerOutcome) :=
        { default := emptySyndrome
          uniq := by
            intro syndrome
            funext check hmem
            exact (by simpa using hmem : False).elim }
      rw [Fintype.sum_unique]
      exact Finset.noncommProd_empty _ _
  | insert check selected hnotmem induction =>
      let split := Finset.insertPiProdEquiv (fun _ : κ => StabilizerOutcome) hnotmem
      calc
        ∑ syndrome : (∀ other, other ∈ insert check selected → StabilizerOutcome),
            jointStabilizerPartialProjector checks hcomm (insert check selected) syndrome =
          ∑ data : StabilizerOutcome ×
              (∀ other, other ∈ selected → StabilizerOutcome),
            jointStabilizerPartialProjector checks hcomm (insert check selected)
              (split.symm data) := by
                simpa using split.sum_comp (fun data =>
                  jointStabilizerPartialProjector checks hcomm (insert check selected)
                    (split.symm data))
        _ = ∑ data : StabilizerOutcome ×
              (∀ other, other ∈ selected → StabilizerOutcome),
            stabilizerProjector (checks check) data.1 *
              jointStabilizerPartialProjector checks hcomm selected data.2 := by
                apply Fintype.sum_congr
                intro data
                exact jointStabilizerPartialProjector_insert
                  checks hcomm check selected hnotmem data.1 data.2
        _ = ∑ outcome : StabilizerOutcome,
              ∑ syndrome : (∀ other, other ∈ selected → StabilizerOutcome),
                stabilizerProjector (checks check) outcome *
                  jointStabilizerPartialProjector checks hcomm selected syndrome := by
                rw [Fintype.sum_prod_type]
        _ = (∑ outcome : StabilizerOutcome, stabilizerProjector (checks check) outcome) *
              ∑ syndrome : (∀ other, other ∈ selected → StabilizerOutcome),
                jointStabilizerPartialProjector checks hcomm selected syndrome := by
                rw [Fintype.sum_mul_sum]
        _ = 1 := by rw [sum_stabilizerProjector_eq_one, induction, one_mul]

/-- Restricting a total syndrome to the full finite set leaves its projector unchanged. -/
private theorem jointStabilizerPartialProjector_univ
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    jointStabilizerPartialProjector checks hcomm Finset.univ
        (fun check _ => syndrome check) =
      jointStabilizerProjector checks hcomm syndrome := by
  unfold jointStabilizerPartialProjector jointStabilizerProjector
  exact Finset.noncommProd_congr rfl (by
    intro check hmem
    simp [jointStabilizerPartialFactor, jointStabilizerFactor]) _

/-- A total syndrome is equivalent to its restriction to the full finite check set. -/
private def jointSyndromeUnivEquiv :
    JointSyndrome κ ≃ (∀ check, check ∈ (Finset.univ : Finset κ) → StabilizerOutcome) where
  toFun syndrome check _ := syndrome check
  invFun syndrome check := syndrome check (Finset.mem_univ check)
  left_inv _ := rfl
  right_inv syndrome := by
    funext check hmem
    rfl

/-- The finite joint-syndrome projectors resolve the identity. -/
theorem sum_jointStabilizerProjector_eq_one
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    ∑ syndrome : JointSyndrome κ, jointStabilizerProjector checks hcomm syndrome = 1 := by
  classical
  let equiv := jointSyndromeUnivEquiv (κ := κ)
  calc
    ∑ syndrome : JointSyndrome κ, jointStabilizerProjector checks hcomm syndrome =
        ∑ restricted : (∀ check, check ∈ (Finset.univ : Finset κ) → StabilizerOutcome),
          jointStabilizerProjector checks hcomm (equiv.symm restricted) := by
            simpa using equiv.sum_comp (fun restricted =>
              jointStabilizerProjector checks hcomm (equiv.symm restricted))
    _ = ∑ restricted : (∀ check, check ∈ (Finset.univ : Finset κ) → StabilizerOutcome),
          jointStabilizerPartialProjector checks hcomm Finset.univ restricted := by
            apply Fintype.sum_congr
            intro restricted
            exact (jointStabilizerPartialProjector_univ
              checks hcomm (equiv.symm restricted)).symm
    _ = 1 := sum_jointStabilizerPartialProjector_eq_one checks hcomm Finset.univ

/-- The joint syndrome projectors as a concrete same-space Kraus family. -/
def jointStabilizerKrausFamily
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    FiniteKrausFamily (JointSyndrome κ)
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  operator := jointStabilizerProjector checks hcomm

@[simp]
theorem jointStabilizerKrausFamily_operator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    (jointStabilizerKrausFamily checks hcomm).operator syndrome =
      jointStabilizerProjector checks hcomm syndrome :=
  rfl

/-- The finite joint projector resolution gives Kraus completeness. -/
theorem jointStabilizerKrausFamily_complete
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    (jointStabilizerKrausFamily checks hcomm).Complete := by
  classical
  unfold FiniteKrausFamily.Complete
  simp only [jointStabilizerKrausFamily_operator, jointStabilizerProjector_adjoint]
  change
    (∑ syndrome : JointSyndrome κ,
      jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerProjector checks hcomm syndrome) = 1
  calc
    (∑ syndrome : JointSyndrome κ,
      jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerProjector checks hcomm syndrome) =
        ∑ syndrome : JointSyndrome κ, jointStabilizerProjector checks hcomm syndrome := by
          apply Finset.sum_congr rfl
          intro syndrome _
          exact jointStabilizerProjector_idempotent checks hcomm syndrome
    _ = 1 := sum_jointStabilizerProjector_eq_one checks hcomm

/-- The complete joint stabilizer measurement with its full visible syndrome. -/
def jointStabilizerInstrument
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    FiniteInstrument (JointSyndrome κ) (JointSyndrome κ)
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  kraus := jointStabilizerKrausFamily checks hcomm
  observe := fun syndrome => syndrome

@[simp]
theorem jointStabilizerInstrument_kraus
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    (jointStabilizerInstrument checks hcomm).kraus =
      jointStabilizerKrausFamily checks hcomm :=
  rfl

@[simp]
theorem jointStabilizerInstrument_observe
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    (jointStabilizerInstrument checks hcomm).observe syndrome = syndrome :=
  rfl

/-- A joint syndrome branch is literal nondestructive joint-projector compression. -/
theorem jointStabilizerInstrument_branchOperator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (A : Operator (Qubit.QubitRegister ι)) :
    (jointStabilizerInstrument checks hcomm).branchOperator syndrome A =
      jointStabilizerProjector checks hcomm syndrome * A *
        jointStabilizerProjector checks hcomm syndrome := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  simp only [jointStabilizerInstrument_observe, jointStabilizerInstrument_kraus,
    jointStabilizerKrausFamily_operator, jointStabilizerProjector_adjoint]
  simp only [eq_comm]
  simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Joint stabilizer Born weights are nonnegative. -/
theorem jointStabilizerBornWeight_nonneg
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι)) :
    0 ≤ (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho :=
  (jointStabilizerInstrument checks hcomm).bornWeight_nonneg syndrome rho

/-- The finite joint stabilizer Born weights sum to one. -/
theorem sum_jointStabilizerBornWeight_eq_one
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    ∑ syndrome : JointSyndrome κ,
        (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho = 1 :=
  (jointStabilizerInstrument checks hcomm).sum_bornWeight_eq_one
    (jointStabilizerKrausFamily_complete checks hcomm) rho

/-- A zero joint-syndrome Born weight leaves an explicit zero raw branch. -/
theorem jointStabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hzero : (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho = 0) :
    (jointStabilizerInstrument checks hcomm).branchOperator syndrome rho.toOperator = 0 :=
  (jointStabilizerInstrument checks hcomm).branchOperator_eq_zero_of_bornWeight_eq_zero
    syndrome rho hzero

/-- The normalized state of a strictly positive joint-syndrome branch. -/
def jointStabilizerConditionalDensity
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho) :
    DensityOperator (Qubit.QubitRegister ι) :=
  (jointStabilizerInstrument checks hcomm).conditionalDensity syndrome rho hpos

@[simp]
theorem jointStabilizerConditionalDensity_toOperator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho) :
    (jointStabilizerConditionalDensity checks hcomm syndrome rho hpos).toOperator =
      (((jointStabilizerInstrument checks hcomm).bornWeight syndrome rho : Complex)⁻¹) •
        (jointStabilizerProjector checks hcomm syndrome * rho.toOperator *
          jointStabilizerProjector checks hcomm syndrome) := by
  rw [jointStabilizerConditionalDensity,
    FiniteInstrument.conditionalDensity_toOperator,
    jointStabilizerInstrument_branchOperator]

/--
Positive-mass conditional joint-syndrome branches reconstruct the unconditioned
complete measurement channel; zero-mass outcomes are omitted only through the
generic proved zero-branch law.
-/
theorem sum_positive_jointStabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    (∑ syndrome : {syndrome : JointSyndrome κ //
        0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho},
      ((jointStabilizerInstrument checks hcomm).bornWeight syndrome.1 rho : Complex) •
        (jointStabilizerConditionalDensity checks hcomm syndrome.1 rho syndrome.2).toOperator) =
      (((jointStabilizerKrausFamily checks hcomm).toQuantumChannel
        (jointStabilizerKrausFamily_complete checks hcomm)).mapDensity rho).toOperator := by
  simpa [jointStabilizerConditionalDensity] using
    FiniteInstrument.sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
      (jointStabilizerInstrument checks hcomm)
      (jointStabilizerKrausFamily_complete checks hcomm) rho

/-- A noncommutative product depends only on its multiset of commuting factors. -/
private theorem multiset_noncommProd_eq_of_eq
    {α : Type*} [Monoid α] (left right : Multiset α)
    (hleft : {element | element ∈ left}.Pairwise Commute)
    (hright : {element | element ∈ right}.Pairwise Commute)
    (heq : left = right) :
    left.noncommProd hleft = right.noncommProd hright := by
  subst right
  rfl

/-- Reindexing a finite check family along an equivalence leaves its joint projector unchanged. -/
theorem jointStabilizerProjector_reindex
    {κ' : Type v} [Fintype κ'] [DecidableEq κ']
    (equiv : κ ≃ κ') (checks : κ → Binary ι)
    (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector
        (fun check' => checks (equiv.symm check'))
        (fun left right => hcomm (equiv.symm left) (equiv.symm right))
        (fun check' => syndrome (equiv.symm check')) := by
  classical
  unfold jointStabilizerProjector Finset.noncommProd
  have hmultiset :
      Multiset.map (jointStabilizerFactor checks syndrome) Finset.univ.val =
        Multiset.map
          (jointStabilizerFactor
            (fun check' => checks (equiv.symm check'))
            (fun check' => syndrome (equiv.symm check')))
          Finset.univ.val := by
    rw [← Multiset.map_univ_val_equiv equiv]
    rw [Multiset.map_map]
    congr 1
    funext check
    simp [jointStabilizerFactor]
  exact multiset_noncommProd_eq_of_eq _ _ _ _ hmultiset

end PauliSymplectic
end Coding
end QEC
