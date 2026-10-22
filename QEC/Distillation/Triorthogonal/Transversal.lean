import QEC.Distillation.Triorthogonal.CSS
/-!
# Explicit diagonal gates for BH12 triorthogonal codes

Phase-normalized diagonal transports, honest support-indexed local factors,
and the raw sitewise transversal `T` layer used by the corrected BH12 action.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace Triorthogonal

open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

universe u

variable {Index : Type u} [Fintype Index] [DecidableEq Index]

/-- Canonical lift of one binary bit to the phase-exponent ring `ℤ/8ℤ`. -/
def bitLift8 (x : ZMod 2) : ZMod 8 := x.val

/-- Canonical lift of one binary bit to the single-site correction ring `ℤ/4ℤ`. -/
def bitLift4 (x : ZMod 2) : ZMod 4 := x.val

@[simp] theorem bitLift4_mul (x y : ZMod 2) :
    bitLift4 (x * y) = bitLift4 x * bitLift4 y := by
  fin_cases x <;> fin_cases y <;> decide

@[simp] theorem bitLift8_mul_self (x : ZMod 2) :
    bitLift8 x * bitLift8 x = bitLift8 x := by
  fin_cases x <;> decide

/-- Lifting binary XOR to `ℤ/8ℤ` produces the usual inclusion-exclusion step. -/
theorem bitLift8_add (x y : ZMod 2) :
    bitLift8 (x + y) = bitLift8 x + bitLift8 y - 2 * bitLift8 x * bitLift8 y := by
  fin_cases x <;> fin_cases y <;> decide

/-- First elementary Boolean sum, evaluated in `ℤ/8ℤ`. -/
def booleanElementaryOne : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => bitLift8 x + booleanElementaryOne xs

/-- Second elementary Boolean sum, evaluated in `ℤ/8ℤ`. -/
def booleanElementaryTwo : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => bitLift8 x * booleanElementaryOne xs + booleanElementaryTwo xs

/-- Third elementary Boolean sum, evaluated in `ℤ/8ℤ`. -/
def booleanElementaryThree : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => bitLift8 x * booleanElementaryTwo xs + booleanElementaryThree xs

/-- XOR of a finite list of binary bits. -/
def booleanXor : List (ZMod 2) → ZMod 2
  | [] => 0
  | x :: xs => x + booleanXor xs

/-- BH12 parity expansion truncated exactly modulo eight. -/
theorem bitLift8_booleanXor (xs : List (ZMod 2)) :
    bitLift8 (booleanXor xs) =
      booleanElementaryOne xs - 2 * booleanElementaryTwo xs +
        4 * booleanElementaryThree xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [booleanXor, bitLift8_add, ih]
      simp only [booleanElementaryOne, booleanElementaryTwo, booleanElementaryThree]
      ring_nf
      have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
      rw [h8, mul_zero]
      simp

/-- Hamming weight is the sum of canonical binary lifts in `ℤ/8ℤ`. -/
theorem hammingWeight_cast8 (x : Word (ZMod 2) Index) :
    (HammingWeight x : ZMod 8) = ∑ p, bitLift8 (x p) := by
  classical
  simp only [HammingWeight, hammingSupport]
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hx : x p = 0
  · simp [hx, bitLift8]
  · have hval : (x p).val = 1 := by
      have hpos : 0 < (x p).val :=
        Nat.pos_of_ne_zero ((ZMod.val_eq_zero (x p)).not.mpr hx)
      have hlt : (x p).val < 2 := ZMod.val_lt (x p)
      omega
    simp [hx, bitLift8, hval]

@[simp] theorem bitLift8_mul (x y : ZMod 2) :
    bitLift8 (x * y) = bitLift8 x * bitLift8 y := by
  fin_cases x <;> fin_cases y <;> decide

/-- Exact pair overlap, now viewed as a phase exponent modulo eight. -/
theorem pairOverlap_cast8 (x y : Word (ZMod 2) Index) :
    (BinaryRowFamily.pairOverlap x y : ZMod 8) =
      ∑ p, bitLift8 (x p) * bitLift8 (y p) := by
  classical
  rw [BinaryRowFamily.pairOverlap, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact bitLift8_mul (x p) (y p)

/-- Exact triple overlap, now viewed as a phase exponent modulo eight. -/
theorem tripleOverlap_cast8 (x y z : Word (ZMod 2) Index) :
    (BinaryRowFamily.tripleOverlap x y z : ZMod 8) =
      ∑ p, bitLift8 (x p) * bitLift8 (y p) * bitLift8 (z p) := by
  classical
  rw [BinaryRowFamily.tripleOverlap, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  change bitLift8 (x p * y p * z p) =
    bitLift8 (x p) * bitLift8 (y p) * bitLift8 (z p)
  rw [bitLift8_mul, bitLift8_mul]

/-- Pointwise XOR of a finite list of binary words. -/
def wordListXor : List (Word (ZMod 2) Index) → Word (ZMod 2) Index
  | [] => 0
  | x :: xs => x + wordListXor xs

@[simp] theorem wordListXor_apply
    (xs : List (Word (ZMod 2) Index)) (p : Index) :
    wordListXor xs p = booleanXor (xs.map fun x => x p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [wordListXor, booleanXor, ih]

/-- Sum of the individual weights of a word list in `ℤ/8ℤ`. -/
def wordWeightSum8 : List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | x :: xs => (HammingWeight x : ZMod 8) + wordWeightSum8 xs

/-- Sum over unordered pairs in list order of their exact overlaps. -/
def wordPairSum8 : List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | x :: xs =>
      (xs.map fun y => (BinaryRowFamily.pairOverlap x y : ZMod 8)).sum +
        wordPairSum8 xs

/-- Triple-overlap sum with the first two words fixed. -/
def fixedPairTripleSum8 (x y : Word (ZMod 2) Index) :
    List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | z :: zs =>
      (BinaryRowFamily.tripleOverlap x y z : ZMod 8) +
        fixedPairTripleSum8 x y zs

/-- Triple-overlap sum with the first word fixed. -/
def fixedTripleSum8 (x : Word (ZMod 2) Index) :
    List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | y :: ys => fixedPairTripleSum8 x y ys + fixedTripleSum8 x ys

/-- Sum over unordered triples in list order of their exact overlaps. -/
def wordTripleSum8 : List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | x :: xs => fixedTripleSum8 x xs + wordTripleSum8 xs

private def wordElementaryOne8 (xs : List (Word (ZMod 2) Index)) : ZMod 8 :=
  ∑ p, booleanElementaryOne (xs.map fun x => x p)

private def wordElementaryTwo8 (xs : List (Word (ZMod 2) Index)) : ZMod 8 :=
  ∑ p, booleanElementaryTwo (xs.map fun x => x p)

private def wordElementaryThree8 (xs : List (Word (ZMod 2) Index)) : ZMod 8 :=
  ∑ p, booleanElementaryThree (xs.map fun x => x p)

private theorem elementaryOne_eq_weightSum8
    (xs : List (Word (ZMod 2) Index)) :
    wordElementaryOne8 xs = wordWeightSum8 xs := by
  induction xs with
  | nil => simp [wordElementaryOne8, wordWeightSum8, booleanElementaryOne]
  | cons x xs ih =>
      simp only [wordElementaryOne8, List.map_cons, booleanElementaryOne,
        Finset.sum_add_distrib]
      rw [← hammingWeight_cast8]
      change (HammingWeight x : ZMod 8) + wordElementaryOne8 xs =
        wordWeightSum8 (x :: xs)
      rw [ih]
      rfl

private theorem headElementaryOne_eq_pairSum
    (x : Word (ZMod 2) Index) (xs : List (Word (ZMod 2) Index)) :
    (∑ p, bitLift8 (x p) * booleanElementaryOne (xs.map fun y => y p)) =
      (xs.map fun y => (BinaryRowFamily.pairOverlap x y : ZMod 8)).sum := by
  induction xs with
  | nil => simp [booleanElementaryOne]
  | cons y ys ih =>
      simp only [List.map_cons, booleanElementaryOne, mul_add, Finset.sum_add_distrib,
        List.sum_cons]
      rw [← pairOverlap_cast8, ih]

private theorem elementaryTwo_eq_pairSum8
    (xs : List (Word (ZMod 2) Index)) :
    wordElementaryTwo8 xs = wordPairSum8 xs := by
  induction xs with
  | nil => simp [wordElementaryTwo8, wordPairSum8, booleanElementaryTwo]
  | cons x xs ih =>
      simp only [wordElementaryTwo8, List.map_cons, booleanElementaryTwo,
        Finset.sum_add_distrib]
      rw [headElementaryOne_eq_pairSum]
      change (xs.map fun y => (BinaryRowFamily.pairOverlap x y : ZMod 8)).sum +
        wordElementaryTwo8 xs = wordPairSum8 (x :: xs)
      rw [ih]
      rfl

private theorem fixedTwoElementaryOne_eq_tripleSum
    (x y : Word (ZMod 2) Index) (xs : List (Word (ZMod 2) Index)) :
    (∑ p, bitLift8 (x p) * bitLift8 (y p) *
      booleanElementaryOne (xs.map fun z => z p)) =
      fixedPairTripleSum8 x y xs := by
  induction xs with
  | nil => simp [booleanElementaryOne, fixedPairTripleSum8]
  | cons z zs ih =>
      simp only [List.map_cons, booleanElementaryOne, mul_add, Finset.sum_add_distrib,
        fixedPairTripleSum8]
      rw [← tripleOverlap_cast8, ih]

private theorem headElementaryTwo_eq_tripleSum
    (x : Word (ZMod 2) Index) (xs : List (Word (ZMod 2) Index)) :
    (∑ p, bitLift8 (x p) * booleanElementaryTwo (xs.map fun y => y p)) =
      fixedTripleSum8 x xs := by
  induction xs with
  | nil => simp [booleanElementaryTwo, fixedTripleSum8]
  | cons y ys ih =>
      simp only [List.map_cons, booleanElementaryTwo, mul_add, Finset.sum_add_distrib,
        fixedTripleSum8]
      simp_rw [← mul_assoc]
      rw [fixedTwoElementaryOne_eq_tripleSum, ih]

private theorem elementaryThree_eq_tripleSum8
    (xs : List (Word (ZMod 2) Index)) :
    wordElementaryThree8 xs = wordTripleSum8 xs := by
  induction xs with
  | nil => simp [wordElementaryThree8, wordTripleSum8, booleanElementaryThree]
  | cons x xs ih =>
      simp only [wordElementaryThree8, List.map_cons, booleanElementaryThree,
        Finset.sum_add_distrib]
      rw [headElementaryTwo_eq_tripleSum]
      change fixedTripleSum8 x xs + wordElementaryThree8 xs =
        wordTripleSum8 (x :: xs)
      rw [ih]
      rfl

/-- Exact finite-list inclusion-exclusion formula for binary Hamming weight modulo eight. -/
theorem hammingWeight_wordListXor_mod8
    (xs : List (Word (ZMod 2) Index)) :
    (HammingWeight (wordListXor xs) : ZMod 8) =
      wordWeightSum8 xs - 2 * wordPairSum8 xs + 4 * wordTripleSum8 xs := by
  rw [hammingWeight_cast8]
  calc
    ∑ p, bitLift8 (wordListXor xs p) =
        ∑ p, (booleanElementaryOne (xs.map fun x => x p) -
          2 * booleanElementaryTwo (xs.map fun x => x p) +
          4 * booleanElementaryThree (xs.map fun x => x p)) := by
            apply Finset.sum_congr rfl
            intro p _hp
            rw [wordListXor_apply, bitLift8_booleanXor]
    _ = wordElementaryOne8 xs - 2 * wordElementaryTwo8 xs +
        4 * wordElementaryThree8 xs := by
          simp only [wordElementaryOne8, wordElementaryTwo8, wordElementaryThree8]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.mul_sum]
    _ = wordWeightSum8 xs - 2 * wordPairSum8 xs + 4 * wordTripleSum8 xs := by
          rw [elementaryOne_eq_weightSum8, elementaryTwo_eq_pairSum8,
            elementaryThree_eq_tripleSum8]

/-- A `T`-phase exponent depends only on its residue modulo eight. -/
theorem phaseAmplitude_pi_div_four_int_eq_of_cast_eq
    (m n : Int) (h : (m : ZMod 8) = (n : ZMod 8)) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (m : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) := by
  have hmod : m ≡ n [ZMOD (8 : Int)] :=
    (ZMod.intCast_eq_intCast_iff m n 8).mp h
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  have hnm : n = m + 8 * k := by omega
  have hangle :
      Real.pi / 4 * (n : Real) =
        Real.pi / 4 * (m : Real) + (2 * Real.pi) * (k : Real) := by
    rw [hnm]
    push_cast
    ring
  rw [hangle, OneQubitMagic.phaseAmplitude_add,
    OneQubitMagic.phaseAmplitude_two_pi_mul_int, mul_one]

/-- Natural `T`-phase exponents with equal residues give equal complex phases. -/
theorem phaseAmplitude_pi_div_four_nat_eq_of_cast_eq
    (m n : Nat) (h : (m : ZMod 8) = (n : ZMod 8)) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (m : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) := by
  apply phaseAmplitude_pi_div_four_int_eq_of_cast_eq (m : Int) (n : Int)
  simpa using h

/-- Replace a natural exponent by its canonical `ℤ/8ℤ` representative. -/
theorem phaseAmplitude_pi_div_four_eq_residue (n : Nat) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * ((n : ZMod 8).val : Real)) := by
  apply phaseAmplitude_pi_div_four_nat_eq_of_cast_eq
  exact (ZMod.natCast_zmod_val (n : ZMod 8)).symm

/-- Transport a proved modulo-eight exponent identity to the corresponding complex phase. -/
theorem phaseAmplitude_pi_div_four_eq_of_natCast_eq
    (n : Nat) (e : ZMod 8) (h : (n : ZMod 8) = e) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (e.val : Real)) := by
  apply phaseAmplitude_pi_div_four_nat_eq_of_cast_eq
  rw [h]
  exact (ZMod.natCast_zmod_val e).symm

/-- Pointwise multiplication by `exp(i angle(bits))`, as a linear equivalence. -/
noncomputable def diagonalPhaseLinearEquiv (angle : Qubit.Bitstring Index → Real) :
    Qubit.QubitRegister Index ≃ₗ[Complex] Qubit.QubitRegister Index where
  toFun psi := WithLp.toLp 2 fun bits =>
    OneQubitMagic.phaseAmplitude (angle bits) * psi bits
  invFun psi := WithLp.toLp 2 fun bits =>
    OneQubitMagic.phaseAmplitude (-angle bits) * psi bits
  left_inv := by
    intro psi
    ext bits
    change OneQubitMagic.phaseAmplitude (-angle bits) *
        (OneQubitMagic.phaseAmplitude (angle bits) * psi bits) = psi bits
    rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
    simp
  right_inv := by
    intro psi
    ext bits
    change OneQubitMagic.phaseAmplitude (angle bits) *
        (OneQubitMagic.phaseAmplitude (-angle bits) * psi bits) = psi bits
    rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
    simp
  map_add' := by
    intro psi chi
    ext bits
    change OneQubitMagic.phaseAmplitude (angle bits) * (psi bits + chi bits) =
      OneQubitMagic.phaseAmplitude (angle bits) * psi bits +
        OneQubitMagic.phaseAmplitude (angle bits) * chi bits
    ring
  map_smul' := by
    intro scalar psi
    ext bits
    change OneQubitMagic.phaseAmplitude (angle bits) * (scalar * psi bits) =
      scalar * (OneQubitMagic.phaseAmplitude (angle bits) * psi bits)
    ring

@[simp] theorem diagonalPhaseLinearEquiv_apply
    (angle : Qubit.Bitstring Index → Real) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    diagonalPhaseLinearEquiv angle psi bits =
      OneQubitMagic.phaseAmplitude (angle bits) * psi bits :=
  rfl

/-- A phase-normalized diagonal unitary on a finite qubit register. -/
noncomputable def diagonalPhaseTransport (angle : Qubit.Bitstring Index → Real) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) where
  toLinearEquiv := diagonalPhaseLinearEquiv angle
  map_inner := by
    intro psi chi
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro bits _hbits
    simp only [diagonalPhaseLinearEquiv_apply, RCLike.inner_apply, map_mul]
    calc
      (OneQubitMagic.phaseAmplitude (angle bits) * chi bits) *
          (starRingEnd Complex (OneQubitMagic.phaseAmplitude (angle bits)) *
            starRingEnd Complex (psi bits)) =
        (OneQubitMagic.phaseAmplitude (angle bits) *
            starRingEnd Complex (OneQubitMagic.phaseAmplitude (angle bits))) *
          (chi bits * starRingEnd Complex (psi bits)) := by ring
      _ = chi bits * starRingEnd Complex (psi bits) := by
        rw [starRingEnd_apply, OneQubitMagic.phaseAmplitude_mul_conj]
        simp

@[simp] theorem diagonalPhaseTransport_apply
    (angle : Qubit.Bitstring Index → Real) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    diagonalPhaseTransport angle psi bits =
      OneQubitMagic.phaseAmplitude (angle bits) * psi bits :=
  rfl

/-- Real-valued phase functions whose values depend only on a declared support. -/
structure LocalDiagonalPhase (support : Finset Index) where
  angle : Qubit.Bitstring Index → Real
  depends_on_support : ∀ bits bits',
    (∀ j ∈ support, bits j = bits' j) → angle bits = angle bits'

/-- The finite physical-gate model of support-indexed diagonal phase gates. -/
noncomputable def diagonalPhaseGateModel :
    FinitePhysicalGateModel Index (Qubit.QubitRegister Index) where
  LocalGate := LocalDiagonalPhase
  realize gate := diagonalPhaseTransport gate.angle

/-- A one-site phase by angle `theta`, with its exact singleton support. -/
def singleSiteLocalPhase (theta : Real) (j : Index) :
    LocalDiagonalPhase ({j} : Finset Index) where
  angle bits := theta * (bits j).val
  depends_on_support := by
    intro bits bits' h
    rw [h j (by simp)]

/-- A one-site phase transport; `theta = π/4` is `T`, `theta = -π/2` is `S†`. -/
noncomputable def singleSitePhaseTransport (theta : Real) (j : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  diagonalPhaseTransport (singleSiteLocalPhase theta j).angle

@[simp] theorem singleSitePhaseTransport_apply
    (theta : Real) (j : Index) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    singleSitePhaseTransport theta j psi bits =
      OneQubitMagic.phaseAmplitude (theta * (bits j).val) * psi bits :=
  rfl

/-- The phase-normalized physical `T` gate on site `j`. -/
noncomputable def physicalT (j : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  singleSitePhaseTransport (Real.pi / 4) j

/-- The phase-normalized physical inverse-`S` gate on site `j`. -/
noncomputable def physicalInverseS (j : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  singleSitePhaseTransport (-Real.pi / 2) j

/-- A controlled-`Z` phase on the explicitly declared pair support. -/
def controlledZLocalPhase (p q : Index) :
    LocalDiagonalPhase ({p, q} : Finset Index) where
  angle bits := Real.pi * (bits p).val * (bits q).val
  depends_on_support := by
    intro bits bits' h
    rw [h p (by simp), h q (by simp)]

/-- The phase-normalized controlled-`Z` transport on sites `p,q`. -/
noncomputable def physicalControlledZ (p q : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  diagonalPhaseTransport (controlledZLocalPhase p q).angle

@[simp] theorem physicalControlledZ_apply
    (p q : Index) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    physicalControlledZ p q psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi * (bits p).val * (bits q).val) * psi bits :=
  rfl

/-- Canonical enumeration of a finite site type. -/
noncomputable def siteEquivFin (Index : Type u) [Fintype Index] :
    Fin (Fintype.card Index) ≃ Index :=
  (Fintype.equivFin Index).symm

/-- The raw all-site phase transport, literally composed from singleton
factors of one common angle. -/
noncomputable def allSitePhase (theta : Real) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card Index) =>
    singleSitePhaseTransport theta (siteEquivFin Index j)

/-- The raw all-site `T` transport as the `theta = π/4` specialization. -/
noncomputable def allSiteT :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  allSitePhase (Index := Index) (Real.pi / 4)

/-- Honest singleton-support transversality data for one common all-site
phase angle. -/
noncomputable def allSitePhaseTransversality (theta : Real) :
    SitewiseTransversalityData (diagonalPhaseGateModel (Index := Index))
      (allSitePhase (Index := Index) theta) where
  factorCount := Fintype.card Index
  support j := {siteEquivFin Index j}
  factor j := singleSiteLocalPhase theta (siteEquivFin Index j)
  pairwise_disjoint := by
    intro i j hij
    simp only [Finset.disjoint_singleton]
    exact (siteEquivFin Index).injective.ne hij
  realizes := rfl
  support_card_le_one := by
    intro j
    simp

/-- Honest singleton-support transversality data for the raw all-site `T`. -/
noncomputable def allSiteTTransversality :
    SitewiseTransversalityData (diagonalPhaseGateModel (Index := Index))
      (allSiteT (Index := Index)) :=
  allSitePhaseTransversality (Index := Index) (Real.pi / 4)

/-- One explicit BH12 physical Clifford correction atom. -/
inductive CliffordCorrectionAtom (Index : Type u)
  | inverseS (p : Index)
  | controlledZ (p q : Index)

namespace CliffordCorrectionAtom

/-- The literal physical support of a correction atom. -/
def support : CliffordCorrectionAtom Index → Finset Index
  | .inverseS p => {p}
  | .controlledZ p q => {p, q}

/-- A correction atom as an allowed support-indexed diagonal gate. -/
def localGate (a : CliffordCorrectionAtom Index) : LocalDiagonalPhase a.support :=
  match a with
  | .inverseS p => singleSiteLocalPhase (-Real.pi / 2) p
  | .controlledZ p q => controlledZLocalPhase p q

/-- Realization of a correction atom on the original physical register. -/
noncomputable def realized (a : CliffordCorrectionAtom Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  (diagonalPhaseGateModel (Index := Index)).realize a.localGate

/-- Real phase angle contributed by one correction atom on a bitstring. -/
def angle (a : CliffordCorrectionAtom Index) (bits : Qubit.Bitstring Index) : Real :=
  match a with
  | .inverseS p => -Real.pi / 2 * (bits p).val
  | .controlledZ p q => Real.pi * (bits p).val * (bits q).val

@[simp] theorem realized_apply (a : CliffordCorrectionAtom Index)
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    a.realized psi bits = OneQubitMagic.phaseAmplitude (a.angle bits) * psi bits := by
  cases a <;> rfl

end CliffordCorrectionAtom

/-- Unordered pairs obtained from a list, in head-before-tail order. -/
def unorderedPairs : List Index → List (Index × Index)
  | [] => []
  | p :: ps => ps.map (p, ·) ++ unorderedPairs ps

/-- Sum of lifted products over unordered pairs of a binary list. -/
def bitPairSum8 : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => (xs.map fun y => bitLift8 x * bitLift8 y).sum + bitPairSum8 xs

private theorem mul_list_sum {R : Type*} [Semiring R] (a : R) (xs : List R) :
    a * xs.sum = (xs.map fun x => a * x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

theorem booleanElementaryOne_eq_sum (xs : List (ZMod 2)) :
    booleanElementaryOne xs = (xs.map bitLift8).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [booleanElementaryOne, ih]

theorem booleanElementaryTwo_eq_bitPairSum8 (xs : List (ZMod 2)) :
    booleanElementaryTwo xs = bitPairSum8 xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [booleanElementaryTwo, bitPairSum8]
      rw [booleanElementaryOne_eq_sum, ih, mul_list_sum]
      rw [List.map_map]
      rfl

/-- Twice a binary XOR has only linear and quadratic terms modulo eight. -/
theorem two_mul_bitLift8_booleanXor (xs : List (ZMod 2)) :
    2 * bitLift8 (booleanXor xs) =
      2 * (xs.map bitLift8).sum - 4 * bitPairSum8 xs := by
  rw [bitLift8_booleanXor, booleanElementaryOne_eq_sum,
    booleanElementaryTwo_eq_bitPairSum8]
  have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
  ring_nf
  simp [h8]

/-- Four times a binary XOR is linear modulo eight. -/
theorem four_mul_bitLift8_booleanXor (xs : List (ZMod 2)) :
    4 * bitLift8 (booleanXor xs) = 4 * (xs.map bitLift8).sum := by
  rw [bitLift8_booleanXor, booleanElementaryOne_eq_sum]
  have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
  have h16 : (16 : ZMod 8) = 0 := by decide
  ring_nf
  simp [h8, h16]

/-- Four times a product of XORs is the product of the lifted linear sums. -/
theorem four_mul_bitLift8_booleanXor_mul (xs ys : List (ZMod 2)) :
    4 * bitLift8 (booleanXor xs) * bitLift8 (booleanXor ys) =
      4 * (xs.map bitLift8).sum * (ys.map bitLift8).sum := by
  calc
    4 * bitLift8 (booleanXor xs) * bitLift8 (booleanXor ys) =
        (4 * (xs.map bitLift8).sum) * bitLift8 (booleanXor ys) := by
          rw [four_mul_bitLift8_booleanXor]
    _ = (xs.map bitLift8).sum *
        (4 * bitLift8 (booleanXor ys)) := by ring
    _ = (xs.map bitLift8).sum * (4 * (ys.map bitLift8).sum) := by
          rw [four_mul_bitLift8_booleanXor]
    _ = _ := by ring

theorem booleanXor_eq_sum (xs : List (ZMod 2)) :
    booleanXor xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [booleanXor, ih]

theorem unorderedPairs_map {A B : Type*} (f : A → B) (xs : List A) :
    unorderedPairs (xs.map f) =
      (unorderedPairs xs).map fun pq => (f pq.1, f pq.2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [unorderedPairs, ih, List.map_append, List.map_map]

theorem bitPairSum8_eq_unorderedPairs (xs : List (ZMod 2)) :
    bitPairSum8 xs =
      ((unorderedPairs xs).map fun pq => bitLift8 pq.1 * bitLift8 pq.2).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [bitPairSum8, unorderedPairs, List.map_append, List.sum_append,
        List.map_map, ih]
      rfl

private theorem list_sum_map_add {A R : Type*} [AddCommMonoid R]
    (xs : List A) (f g : A → R) :
    (xs.map fun x => f x + g x).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, add_left_comm]

/-- Cross terms contributed by unordered pairs in a product of two list sums. -/
def pairMulCrossSum {A R : Type*} [CommRing R]
    (f g : A → R) : List A → R
  | [] => 0
  | x :: xs =>
      (xs.map fun y => f x * g y + f y * g x).sum + pairMulCrossSum f g xs

private theorem list_sum_mul_sum_split_cross {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    (xs.map f).sum * (xs.map g).sum =
      (xs.map fun x => f x * g x).sum + pairMulCrossSum f g xs := by
  induction xs with
  | nil => simp [pairMulCrossSum]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, pairMulCrossSum]
      have hf : f x * (xs.map g).sum = (xs.map fun y => f x * g y).sum :=
        by simpa [List.map_map, Function.comp_def] using mul_list_sum (f x) (xs.map g)
      have hg : (xs.map f).sum * g x = (xs.map fun y => f y * g x).sum := by
        rw [mul_comm]
        simpa [mul_comm, List.map_map, Function.comp_def] using mul_list_sum (g x) (xs.map f)
      calc
        (f x + (xs.map f).sum) * (g x + (xs.map g).sum) =
            f x * g x + f x * (xs.map g).sum +
              (xs.map f).sum * g x + (xs.map f).sum * (xs.map g).sum := by ring
        _ = f x * g x + (xs.map fun x => f x * g x).sum +
              ((xs.map fun y => f x * g y + f y * g x).sum +
                pairMulCrossSum f g xs) := by
              rw [ih, hf, hg, list_sum_map_add]
              ring

private theorem pairMulCrossSum_eq_unorderedPairs {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    pairMulCrossSum f g xs =
      ((unorderedPairs xs).map fun pq =>
        f pq.1 * g pq.2 + f pq.2 * g pq.1).sum := by
  induction xs with
  | nil => simp [pairMulCrossSum, unorderedPairs]
  | cons x xs ih =>
      simp only [pairMulCrossSum, unorderedPairs, List.map_append,
        List.sum_append, List.map_map, ih]
      rfl

/-- A product of two list sums split into diagonal and unordered cross terms. -/
theorem list_sum_mul_sum_split_pairs {A R : Type*} [CommRing R]
    (xs : List A) (f g : A → R) :
    (xs.map f).sum * (xs.map g).sum =
      (xs.map fun x => f x * g x).sum +
        ((unorderedPairs xs).map fun pq =>
          f pq.1 * g pq.2 + f pq.2 * g pq.1).sum := by
  rw [list_sum_mul_sum_split_cross, pairMulCrossSum_eq_unorderedPairs]

private theorem list_sum_comm {A B R : Type*} [AddCommMonoid R]
    (xs : List A) (ys : List B) (f : A → B → R) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, list_sum_map_add]

private theorem list_sum_map_mul_right {A R : Type*} [Semiring R]
    (xs : List A) (f : A → R) (a : R) :
    (xs.map fun x => f x * a).sum = (xs.map f).sum * a := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_mul]

private theorem list_sum_map_sub {A R : Type*} [AddCommGroup R]
    (xs : List A) (f g : A → R) :
    (xs.map fun x => f x - g x).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel

/-- Canonical list of physical sites. -/
noncomputable def siteList (Index : Type u) [Fintype Index] : List Index :=
  List.ofFn (siteEquivFin Index)

/-- Canonical list of unordered pairs of physical sites. -/
noncomputable def sitePairList (Index : Type u) [Fintype Index] :
    List (Index × Index) :=
  unorderedPairs (siteList Index)

/-- Number of occupied sites in the canonical finite site enumeration. -/
def siteBitCount (bits : Qubit.Bitstring Index) : Nat :=
  ((siteList Index).map fun p => (bits p).val).sum

theorem siteBitCount_eq_hammingWeight (bits : Qubit.Bitstring Index) :
    siteBitCount bits = HammingWeight (bitstringWordEquiv Index bits) := by
  classical
  simp only [siteBitCount, siteList]
  rw [← List.sum_toFinset _ (List.nodup_ofFn.mpr (siteEquivFin Index).injective)]
  rw [← Fin.univ_image_def]
  have himage : Finset.image (siteEquivFin Index) Finset.univ = Finset.univ := by
    ext p
    simp
  rw [himage]
  simp only [HammingWeight, hammingSupport, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  change (bits p).val = if bits p ≠ 0 then 1 else 0
  by_cases hp : bits p = 0
  · rw [if_neg (not_ne_iff.mpr hp)]
    simp [hp]
  · rw [if_pos hp]
    have hval0 : (bits p).val ≠ 0 := by
      intro hval
      apply hp
      apply Fin.ext
      simpa using hval
    have hpos : 0 < (bits p).val := Nat.pos_of_ne_zero hval0
    have hlt : (bits p).val < 2 := (bits p).isLt
    omega

private theorem composeSingleSitePhase_apply
    (theta : Real) (sites : List Index) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    UnitaryTransport.composeList (sites.map (singleSitePhaseTransport theta)) psi bits =
      OneQubitMagic.phaseAmplitude
        (theta *
          (((sites.map fun p => (bits p).val).sum : Nat) : Real)) *
        psi bits := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons p ps ih =>
      change UnitaryTransport.composeList (ps.map (singleSitePhaseTransport theta))
          (singleSitePhaseTransport theta p psi) bits = _
      rw [ih]
      change OneQubitMagic.phaseAmplitude
          (theta * (((ps.map fun q => (bits q).val).sum : Nat) : Real)) *
            (OneQubitMagic.phaseAmplitude (theta * (bits p).val) *
              psi bits) = _
      rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
      congr 2
      simp only [List.map_cons, List.sum_cons]
      push_cast
      ring

/-- The raw all-site phase layer contributes exactly the physical
Hamming-weight phase. -/
theorem allSitePhase_apply
    (theta : Real)
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    allSitePhase theta psi bits =
      OneQubitMagic.phaseAmplitude
        (theta *
          (HammingWeight (bitstringWordEquiv Index bits) : Real)) *
        psi bits := by
  rw [allSitePhase, UnitaryTransport.composeFamily]
  have hlist :
    List.ofFn (fun j : Fin (Fintype.card Index) =>
        singleSitePhaseTransport theta (siteEquivFin Index j)) =
        (siteList Index).map (singleSitePhaseTransport theta) := by
    rw [siteList, List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist]
  rw [composeSingleSitePhase_apply]
  change OneQubitMagic.phaseAmplitude
      (theta * (siteBitCount bits : Real)) * psi bits = _
  rw [siteBitCount_eq_hammingWeight]

/-- The raw all-site `T` layer contributes exactly the physical Hamming-weight phase. -/
theorem allSiteT_apply
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    allSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 *
          (HammingWeight (bitstringWordEquiv Index bits) : Real)) *
        psi bits := by
  simpa [allSiteT] using
    (allSitePhase_apply (Index := Index) (Real.pi / 4) psi bits)

/--
The transparent ordered correction list: inverse-`S` multiplicities are read
modulo four and controlled-`Z` multiplicities modulo two.
-/
noncomputable def cliffordCorrectionAtoms
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2) :
    List (CliffordCorrectionAtom Index) :=
  ((siteList Index).flatMap fun p =>
      List.replicate (single p).val (.inverseS p)) ++
    ((sitePairList Index).flatMap fun pq =>
      List.replicate (pair pq.1 pq.2).val (.controlledZ pq.1 pq.2))

/-- Ordered composition of the explicit, possibly overlapping correction atoms. -/
noncomputable def cliffordCorrection
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  UnitaryTransport.composeList
    ((cliffordCorrectionAtoms single pair).map CliffordCorrectionAtom.realized)

def atomAngleSum (atoms : List (CliffordCorrectionAtom Index))
    (bits : Qubit.Bitstring Index) : Real :=
  (atoms.map fun a => a.angle bits).sum

@[simp] theorem atomAngleSum_append
    (xs ys : List (CliffordCorrectionAtom Index)) (bits : Qubit.Bitstring Index) :
    atomAngleSum (xs ++ ys) bits = atomAngleSum xs bits + atomAngleSum ys bits := by
  simp [atomAngleSum]

theorem composeAtoms_apply (atoms : List (CliffordCorrectionAtom Index))
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    UnitaryTransport.composeList (atoms.map CliffordCorrectionAtom.realized) psi bits =
      OneQubitMagic.phaseAmplitude (atomAngleSum atoms bits) * psi bits := by
  induction atoms generalizing psi with
  | nil => simp [UnitaryTransport.composeList, atomAngleSum]
  | cons a atoms ih =>
      change UnitaryTransport.composeList (atoms.map CliffordCorrectionAtom.realized)
        (a.realized psi) bits = _
      rw [ih, CliffordCorrectionAtom.realized_apply]
      simp only [atomAngleSum, List.map_cons, List.sum_cons,
        OneQubitMagic.phaseAmplitude_add]
      ring

private theorem atomAngleSum_flatMap_replicate
    {A : Type*} (xs : List A) (n : A → Nat)
    (atom : A → CliffordCorrectionAtom Index) (bits : Qubit.Bitstring Index) :
    atomAngleSum (xs.flatMap fun x => List.replicate (n x) (atom x)) bits =
      (xs.map fun x => (n x : Real) * (atom x).angle bits).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [atomAngleSum, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate, List.map_cons,
        List.sum_cons]
      change n x • (atom x).angle bits +
        atomAngleSum (xs.flatMap fun x => List.replicate (n x) (atom x)) bits = _
      rw [ih]
      simp [nsmul_eq_mul]

/-- Explicit total angle of the physical inverse-`S`/controlled-`Z` list. -/
noncomputable def cliffordCorrectionAngle
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2)
    (bits : Qubit.Bitstring Index) : Real :=
  ((siteList Index).map fun p =>
      ((single p).val : Real) * (-Real.pi / 2 * (bits p).val)).sum +
    ((sitePairList Index).map fun pq =>
      ((pair pq.1 pq.2).val : Real) *
        (Real.pi * (bits pq.1).val * (bits pq.2).val)).sum

theorem atomAngleSum_correctionAtoms
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2)
    (bits : Qubit.Bitstring Index) :
    atomAngleSum (cliffordCorrectionAtoms single pair) bits =
      cliffordCorrectionAngle single pair bits := by
  rw [show cliffordCorrectionAtoms single pair =
      ((siteList Index).flatMap fun p =>
        List.replicate (single p).val (.inverseS p)) ++
      ((sitePairList Index).flatMap fun pq =>
        List.replicate (pair pq.1 pq.2).val (.controlledZ pq.1 pq.2)) by rfl]
  rw [atomAngleSum_append, atomAngleSum_flatMap_replicate,
    atomAngleSum_flatMap_replicate]
  rfl

/-- Pointwise phase of the explicit physical correction composition. -/
@[simp] theorem cliffordCorrection_apply
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2)
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    cliffordCorrection single pair psi bits =
      OneQubitMagic.phaseAmplitude (cliffordCorrectionAngle single pair bits) * psi bits := by
  rw [cliffordCorrection, composeAtoms_apply, atomAngleSum_correctionAtoms]

universe uO uE uC

namespace BinaryRowFamily

variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]

/-- A canonical finite index type for a basis of the possibly dependent even-row span. -/
abbrev EvenBasisIndex (R : BinaryRowFamily OddRow EvenRow Col) :=
  Fin (Module.finrank (ZMod 2) R.evenCode.carrier)

/-- A chosen basis of the even-row span; no independence of the supplied even rows is assumed. -/
noncomputable def evenBasis (R : BinaryRowFamily OddRow EvenRow Col) :
    Module.Basis R.EvenBasisIndex (ZMod 2) R.evenCode.carrier :=
  Module.finBasis (ZMod 2) R.evenCode.carrier

/-- The reduced independent row presentation: all odd rows followed by an even-span basis. -/
noncomputable def reducedRow (R : BinaryRowFamily OddRow EvenRow Col) :
    Sum OddRow R.EvenBasisIndex → Word (ZMod 2) Col :=
  Sum.elim R.oddRow fun b => R.evenBasis b

theorem span_evenBasis_eq_evenCode
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Submodule.span (ZMod 2)
        (Set.range fun b : R.EvenBasisIndex =>
          (R.evenBasis b : Word (ZMod 2) Col)) =
      R.evenCode.carrier := by
  rw [show Set.range (fun b : R.EvenBasisIndex =>
      (R.evenBasis b : Word (ZMod 2) Col)) =
      R.evenCode.carrier.subtype '' Set.range R.evenBasis by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨R.evenBasis b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩]
  rw [← Submodule.map_span, (R.evenBasis).span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- The reduced rows are independent even when the supplied even rows are dependent. -/
theorem reducedRows_linearIndependent
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    LinearIndependent (ZMod 2) R.reducedRow := by
  change LinearIndependent (ZMod 2)
    (Sum.elim R.oddRow
      (fun b : R.EvenBasisIndex => (R.evenBasis b : Word (ZMod 2) Col)))
  apply LinearIndependent.sum_type
  · exact R.oddRows_linearIndependent hR
  · exact (R.evenBasis).linearIndependent.map'
      R.evenCode.carrier.subtype R.evenCode.carrier.ker_subtype
  · simpa [oddCode, R.span_evenBasis_eq_evenCode] using
      (R.evenCode_disjoint_oddCode hR).symm

/-- Linear synthesis of physical words from reduced-row coefficients. -/
noncomputable def reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) (Sum OddRow R.EvenBasisIndex) →ₗ[ZMod 2]
      Word (ZMod 2) Col :=
  Fintype.linearCombination (ZMod 2) R.reducedRow

@[simp] theorem reducedCombination_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    R.reducedCombination c = ∑ r, c r • R.reducedRow r :=
  Fintype.linearCombination_apply (ZMod 2) R.reducedRow c

theorem reducedCombination_injective
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Function.Injective R.reducedCombination := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  apply funext
  intro r
  exact (Fintype.linearIndependent_iff.mp (R.reducedRows_linearIndependent hR))
    c (by simpa using hc) r

/-- A concrete ambient left inverse `B` recovering reduced-row coefficients. -/
noncomputable def rowCoefficientMap
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) Col →ₗ[ZMod 2]
      Word (ZMod 2) (Sum OddRow R.EvenBasisIndex) :=
  R.reducedCombination.leftInverse

@[simp] theorem rowCoefficientMap_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    R.rowCoefficientMap (R.reducedCombination c) = c :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (R.reducedCombination_injective hR)) c

/-- Matrix entries of the chosen left inverse `B`, in the physical standard basis. -/
noncomputable def rowCoefficientEntry
    (R : BinaryRowFamily OddRow EvenRow Col)
    (r : Sum OddRow R.EvenBasisIndex) (p : Col) : ZMod 2 :=
  R.rowCoefficientMap (Pi.single p 1) r

/-- The left inverse is the finite matrix with entries `rowCoefficientEntry`. -/
theorem rowCoefficientMap_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (f : Word (ZMod 2) Col) (r : Sum OddRow R.EvenBasisIndex) :
    R.rowCoefficientMap f r =
      ∑ p, R.rowCoefficientEntry r p * f p := by
  classical
  have hf :
      R.rowCoefficientMap f =
        ∑ p, f p • R.rowCoefficientMap
          (Pi.single p (1 : ZMod 2) : Word (ZMod 2) Col) := by
    calc
      R.rowCoefficientMap f =
          R.rowCoefficientMap
            (∑ p, Pi.single p (f p) : Word (ZMod 2) Col) := by
              rw [word_eq_sum_single]
      _ = ∑ p, R.rowCoefficientMap
          (Pi.single p (f p) : Word (ZMod 2) Col) := by rw [map_sum]
      _ = ∑ p, f p • R.rowCoefficientMap
          (Pi.single p (1 : ZMod 2) : Word (ZMod 2) Col) := by
            apply Finset.sum_congr rfl
            intro p _hp
            rw [← map_smul]
            congr 1
            rw [← Pi.single_smul]
            simp
  rw [hf, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, rowCoefficientEntry]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- Physical-site summands whose XOR recovers one chosen `B`-coordinate. -/
noncomputable def coefficientBitList
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : Sum OddRow R.EvenBasisIndex) : List (ZMod 2) :=
  (siteList Col).map fun p => R.rowCoefficientEntry r p * f p

/-- The `B`-coordinate is the XOR of its physical-site matrix summands. -/
theorem booleanXor_coefficientBitList
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : Sum OddRow R.EvenBasisIndex) :
    booleanXor (R.coefficientBitList f r) = R.rowCoefficientMap f r := by
  rw [booleanXor_eq_sum]
  simp only [coefficientBitList, siteList, List.map_ofFn, List.sum_ofFn]
  rw [R.rowCoefficientMap_apply]
  exact Fintype.sum_equiv (siteEquivFin Col) _ _ (fun _ => rfl)

/-- Cubic binary pairing underlying exact triple-overlap parity. -/
def wordTriplePairing (x y z : Word (ZMod 2) Col) : ZMod 2 :=
  ∑ p, x p * y p * z p

theorem wordTriplePairing_eq_cast (x y z : Word (ZMod 2) Col) :
    wordTriplePairing x y z = (tripleOverlap x y z : ZMod 2) := by
  rw [tripleOverlap_cast]
  rfl

theorem wordTriplePairing_add_left (x x' y z : Word (ZMod 2) Col) :
    wordTriplePairing (x + x') y z =
      wordTriplePairing x y z + wordTriplePairing x' y z := by
  classical
  simp only [wordTriplePairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem wordTriplePairing_smul_left
    (c : ZMod 2) (x y z : Word (ZMod 2) Col) :
    wordTriplePairing (c • x) y z = c * wordTriplePairing x y z := by
  classical
  simp only [wordTriplePairing, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

@[simp] theorem wordTriplePairing_zero_left (y z : Word (ZMod 2) Col) :
    wordTriplePairing 0 y z = 0 := by
  simp [wordTriplePairing]

theorem wordTriplePairing_swap_left (x y z : Word (ZMod 2) Col) :
    wordTriplePairing x y z = wordTriplePairing y x z := by
  classical
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem wordTriplePairing_rotate (x y z : Word (ZMod 2) Col) :
    wordTriplePairing x y z = wordTriplePairing z x y := by
  classical
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem wordTriplePairing_self_left (x z : Word (ZMod 2) Col) :
    wordTriplePairing x x z = wordPairing x z := by
  classical
  simp only [wordTriplePairing, wordPairing_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro p _hp
  have hmul_self : ∀ q : ZMod 2, q * q = q := by
    intro q
    fin_cases q
    · exact zero_mul (0 : ZMod 2)
    · exact one_mul (1 : ZMod 2)
  rw [hmul_self]

private theorem wordTriplePairing_span_left
    {A : Type*} (v : A → Word (ZMod 2) Col)
    (y z : Word (ZMod 2) Col)
    (h : ∀ i, wordTriplePairing (v i) y z = 0)
    {x : Word (ZMod 2) Col}
    (hx : x ∈ Submodule.span (ZMod 2) (Set.range v)) :
    wordTriplePairing x y z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact h i
  | zero => simp
  | add x x' _ _ hx hx' =>
      rw [wordTriplePairing_add_left, hx, hx', add_zero]
  | smul c x _ hx =>
      rw [wordTriplePairing_smul_left, hx, mul_zero]

private theorem wordTriplePairing_eq_zero_of_even
    {x y z : Word (ZMod 2) Col}
    (h : Even (tripleOverlap x y z)) :
    wordTriplePairing x y z = 0 := by
  rw [wordTriplePairing_eq_cast]
  exact ZMod.natCast_eq_zero_iff_even.mpr h

private theorem evenRow_evenRow_row_triplePairing
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (b₁ b₂ : EvenRow) (r : Sum OddRow EvenRow) :
    wordTriplePairing (R.evenRow b₁) (R.evenRow b₂) (R.row r) = 0 := by
  by_cases h₁₂ : b₁ = b₂
  · subst b₂
    rw [wordTriplePairing_self_left]
    exact R.wordPairing_evenCode_rowCode hR
      (R.evenRow_mem_evenCode b₁) (R.row_mem_rowCode r)
  · rcases r with a | b₃
    · apply wordTriplePairing_eq_zero_of_even
      exact hR.triple_even (.inr b₁) (.inr b₂) (.inl a)
        (by simpa using h₁₂) (by simp) (by simp)
    · by_cases h₁₃ : b₁ = b₃
      · subst b₃
        change wordTriplePairing (R.evenRow b₁) (R.evenRow b₂)
          (R.evenRow b₁) = 0
        rw [wordTriplePairing_rotate, wordTriplePairing_self_left,
          R.evenRow_pairing hR]
      · by_cases h₂₃ : b₂ = b₃
        · subst b₃
          change wordTriplePairing (R.evenRow b₁) (R.evenRow b₂)
            (R.evenRow b₂) = 0
          rw [wordTriplePairing_swap_left, wordTriplePairing_rotate,
            wordTriplePairing_self_left, R.evenRow_pairing hR]
        · apply wordTriplePairing_eq_zero_of_even
          exact hR.triple_even (.inr b₁) (.inr b₂) (.inr b₃)
            (by simpa using h₁₂) (by simpa using h₁₃)
              (by simpa using h₂₃)

/-- Two even-span words have zero cubic pairing with the whole row span. -/
theorem wordTriplePairing_evenCode_evenCode_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x y z : Word (ZMod 2) Col}
    (hx : x ∈ R.evenCode.carrier) (hy : y ∈ R.evenCode.carrier)
    (hz : z ∈ R.rowCode.carrier) : wordTriplePairing x y z = 0 := by
  apply wordTriplePairing_span_left R.evenRow y z (fun b₁ => ?_) hx
  rw [wordTriplePairing_swap_left]
  apply wordTriplePairing_span_left R.evenRow (R.evenRow b₁) z
    (fun b₂ => ?_) hy
  rw [wordTriplePairing_rotate]
  apply wordTriplePairing_span_left R.row (R.evenRow b₂) (R.evenRow b₁)
    (fun r => ?_) hz
  simpa only [wordTriplePairing_rotate] using
    (evenRow_evenRow_row_triplePairing R hR b₂ b₁ r)

/-- An even-span word has zero cubic pairing with two distinct odd rows. -/
theorem wordTriplePairing_evenCode_distinct_oddRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    {a b : OddRow} (hab : a ≠ b) :
    wordTriplePairing x (R.oddRow a) (R.oddRow b) = 0 := by
  apply wordTriplePairing_span_left R.evenRow (R.oddRow a) (R.oddRow b)
    (fun e => ?_) hx
  apply wordTriplePairing_eq_zero_of_even
  exact hR.triple_even (.inr e) (.inl a) (.inl b)
    (by simp) (by simp) (by simpa using hab)

private theorem evenBasis_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (b : R.EvenBasisIndex) :
    (R.evenBasis b : Word (ZMod 2) Col) ∈ R.rowCode.carrier := by
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.mem_sup_left (R.evenBasis b).property

/-- Pairwise-distinct reduced rows retain the BH12 cubic parity relation. -/
theorem reducedRow_triplePairing_eq_zero
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s t : Sum OddRow R.EvenBasisIndex}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    wordTriplePairing (R.reducedRow r) (R.reducedRow s) (R.reducedRow t) = 0 := by
  rcases r with a | e₁
  · rcases s with b | e₂
    · rcases t with c | e₃
      · apply wordTriplePairing_eq_zero_of_even
        exact hR.triple_even (.inl a) (.inl b) (.inl c)
          (by simpa using hrs) (by simpa using hrt) (by simpa using hst)
      · rw [wordTriplePairing_rotate]
        exact wordTriplePairing_evenCode_distinct_oddRows R hR
          (R.evenBasis e₃).property (by simpa using hrs)
    · rcases t with c | e₃
      · rw [wordTriplePairing_swap_left]
        exact wordTriplePairing_evenCode_distinct_oddRows R hR
          (R.evenBasis e₂).property (by simpa using hrt)
      · rw [wordTriplePairing_swap_left, wordTriplePairing_rotate]
        exact wordTriplePairing_evenCode_evenCode_rowCode R hR
          (R.evenBasis e₃).property (R.evenBasis e₂).property
            (R.row_mem_rowCode (.inl a))
  · rcases s with b | e₂
    · rcases t with c | e₃
      · exact wordTriplePairing_evenCode_distinct_oddRows R hR
          (R.evenBasis e₁).property (by simpa using hst)
      · rw [wordTriplePairing_rotate]
        exact wordTriplePairing_evenCode_evenCode_rowCode R hR
          (R.evenBasis e₃).property (R.evenBasis e₁).property
            (R.row_mem_rowCode (.inl b))
    · rcases t with c | e₃
      · exact wordTriplePairing_evenCode_evenCode_rowCode R hR
          (R.evenBasis e₁).property (R.evenBasis e₂).property
            (R.row_mem_rowCode (.inl c))
      · exact wordTriplePairing_evenCode_evenCode_rowCode R hR
          (R.evenBasis e₁).property (R.evenBasis e₂).property
            (evenBasis_mem_rowCode R e₃)

theorem reducedRow_triple_even
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s t : Sum OddRow R.EvenBasisIndex}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Even (tripleOverlap (R.reducedRow r) (R.reducedRow s) (R.reducedRow t)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, tripleOverlap_cast]
  exact reducedRow_triplePairing_eq_zero R hR hrs hrt hst

private theorem tripleOverlap_smul_even
    {x y z : Word (ZMod 2) Col} (hx hy hz : ZMod 2)
    (h : Even (tripleOverlap x y z)) :
    Even (tripleOverlap (hx • x) (hy • y) (hz • z)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, tripleOverlap_cast]
  have hzero : (∑ p, x p * y p * z p) = 0 := by
    rw [← tripleOverlap_cast]
    exact ZMod.natCast_eq_zero_iff_even.mpr h
  calc
    ∑ p, (hx • x) p * (hy • y) p * (hz • z) p =
        hx * hy * hz * ∑ p, x p * y p * z p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
    _ = 0 := by rw [hzero, mul_zero]

private theorem four_mul_natCast8_eq_zero_of_even
    {n : Nat} (h : Even n) : (4 : ZMod 8) * (n : ZMod 8) = 0 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_add]
  ring_nf
  have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
  simp [h8]

private theorem four_mul_fixedPairTripleSum8_eq_zero
    {A : Type*} [DecidableEq A]
    (v : A → Word (ZMod 2) Col) (c : A → ZMod 2)
    (r s : A) (rs : List A)
    (hrs : r ≠ s) (hr : r ∉ rs) (hs : s ∉ rs)
    (htriple : ∀ {r s t : A}, r ≠ s → r ≠ t → s ≠ t →
      Even (tripleOverlap (v r) (v s) (v t))) :
    (4 : ZMod 8) * fixedPairTripleSum8 (c r • v r) (c s • v s)
      (rs.map fun t => c t • v t) = 0 := by
  induction rs with
  | nil => simp [fixedPairTripleSum8]
  | cons t ts ih =>
      have hrt : r ≠ t := by
        intro hrt
        apply hr
        simp [hrt]
      have hst : s ≠ t := by
        intro hst
        apply hs
        simp [hst]
      have hrts : r ∉ ts := by
        intro hmem
        exact hr (by simp [hmem])
      have hsts : s ∉ ts := by
        intro hmem
        exact hs (by simp [hmem])
      have hterm :
          (4 : ZMod 8) *
            (tripleOverlap (c r • v r) (c s • v s) (c t • v t) : ZMod 8) = 0 :=
        four_mul_natCast8_eq_zero_of_even
          (tripleOverlap_smul_even (c r) (c s) (c t)
            (htriple hrs hrt hst))
      simp only [List.map_cons, fixedPairTripleSum8, mul_add]
      rw [hterm, ih hrts hsts, add_zero]

private theorem four_mul_fixedTripleSum8_eq_zero
    {A : Type*} [DecidableEq A]
    (v : A → Word (ZMod 2) Col) (c : A → ZMod 2)
    (r : A) (rs : List A) (hr : r ∉ rs) (hnd : rs.Nodup)
    (htriple : ∀ {r s t : A}, r ≠ s → r ≠ t → s ≠ t →
      Even (tripleOverlap (v r) (v s) (v t))) :
    (4 : ZMod 8) * fixedTripleSum8 (c r • v r)
      (rs.map fun s => c s • v s) = 0 := by
  induction rs with
  | nil => simp [fixedTripleSum8]
  | cons s ss ih =>
      have hrs : r ≠ s := by
        intro hrs
        apply hr
        simp [hrs]
      have hrss : r ∉ ss := by
        intro hmem
        exact hr (by simp [hmem])
      have hsss : s ∉ ss := (List.nodup_cons.mp hnd).1
      have hndss : ss.Nodup := (List.nodup_cons.mp hnd).2
      simp only [List.map_cons, fixedTripleSum8, mul_add]
      rw [four_mul_fixedPairTripleSum8_eq_zero v c r s ss hrs hrss hsss htriple,
        ih hrss hndss, add_zero]

private theorem four_mul_wordTripleSum8_eq_zero
    {A : Type*} [DecidableEq A]
    (v : A → Word (ZMod 2) Col) (c : A → ZMod 2)
    (rs : List A) (hnd : rs.Nodup)
    (htriple : ∀ {r s t : A}, r ≠ s → r ≠ t → s ≠ t →
      Even (tripleOverlap (v r) (v s) (v t))) :
    (4 : ZMod 8) * wordTripleSum8 (rs.map fun r => c r • v r) = 0 := by
  induction rs with
  | nil => simp [wordTripleSum8]
  | cons r rs ih =>
      have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
      have hndrs : rs.Nodup := (List.nodup_cons.mp hnd).2
      simp only [List.map_cons, wordTripleSum8, mul_add]
      rw [four_mul_fixedTripleSum8_eq_zero v c r rs hr hndrs htriple,
        ih hndrs, add_zero]

/-- Canonical finite ordering of the independent reduced rows. -/
noncomputable def reducedRowEquivFin (R : BinaryRowFamily OddRow EvenRow Col) :
    Fin (Fintype.card (Sum OddRow R.EvenBasisIndex)) ≃ Sum OddRow R.EvenBasisIndex :=
  (Fintype.equivFin (Sum OddRow R.EvenBasisIndex)).symm

/-- The canonical list of reduced-row indices. -/
noncomputable def reducedRowIndexList
    (R : BinaryRowFamily OddRow EvenRow Col) : List (Sum OddRow R.EvenBasisIndex) :=
  List.ofFn R.reducedRowEquivFin

/-- Coefficient-scaled reduced rows in their canonical finite ordering. -/
noncomputable def reducedWordList
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    List (Word (ZMod 2) Col) :=
  R.reducedRowIndexList.map fun r => c r • R.reducedRow r

theorem reducedRowIndexList_nodup
    (R : BinaryRowFamily OddRow EvenRow Col) : R.reducedRowIndexList.Nodup := by
  exact List.nodup_ofFn_ofInjective R.reducedRowEquivFin.injective

private theorem wordListXor_eq_sum (xs : List (Word (ZMod 2) Col)) :
    wordListXor xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [wordListXor, ih]

@[simp] theorem wordListXor_reducedWordList
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    wordListXor (R.reducedWordList c) = R.reducedCombination c := by
  rw [wordListXor_eq_sum]
  simp only [reducedWordList, reducedRowIndexList, List.map_ofFn, List.sum_ofFn]
  rw [R.reducedCombination_apply]
  exact Fintype.sum_equiv R.reducedRowEquivFin _ _ (fun _ => rfl)

theorem reducedWordList_tripleTerm_eq_zero
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    (4 : ZMod 8) * wordTripleSum8 (R.reducedWordList c) = 0 := by
  exact four_mul_wordTripleSum8_eq_zero R.reducedRow c R.reducedRowIndexList
    R.reducedRowIndexList_nodup
      (fun hrs hrt hst => R.reducedRow_triple_even hR hrs hrt hst)

/-- BH12 reduced-row weight polynomial modulo eight, with the cubic term eliminated. -/
theorem hammingWeight_reducedCombination_mod8
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    (HammingWeight (R.reducedCombination c) : ZMod 8) =
      wordWeightSum8 (R.reducedWordList c) -
        2 * wordPairSum8 (R.reducedWordList c) := by
  rw [← R.wordListXor_reducedWordList c, hammingWeight_wordListXor_mod8,
    R.reducedWordList_tripleTerm_eq_zero hR c, add_zero]

/-- Index type of the chosen independent reduced-row presentation. -/
abbrev ReducedRowIndex (R : BinaryRowFamily OddRow EvenRow Col) :=
  Sum OddRow R.EvenBasisIndex

/-- Logical parity contribution of a reduced row: one for odd rows, zero for even rows. -/
def reducedRowParity (R : BinaryRowFamily OddRow EvenRow Col) :
    R.ReducedRowIndex → Nat
  | .inl _ => 1
  | .inr _ => 0

/-- BH12 coefficient `Γ_r = (|g^r| - δ_r)/2`. -/
def rowGamma (R : BinaryRowFamily OddRow EvenRow Col)
    (r : R.ReducedRowIndex) : Nat :=
  (HammingWeight (R.reducedRow r) - R.reducedRowParity r) / 2

private theorem evenCode_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    x ∈ R.rowCode.carrier := by
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.mem_sup_left hx

theorem hammingWeight_even_of_mem_evenCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    Even (HammingWeight x) := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← pairOverlap_self_eq_hammingWeight,
    pairOverlap_cast]
  exact R.wordPairing_evenCode_rowCode hR hx (evenCode_mem_rowCode R hx)

theorem reducedRow_weight_eq
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (r : R.ReducedRowIndex) :
    HammingWeight (R.reducedRow r) =
      R.reducedRowParity r + 2 * R.rowGamma r := by
  rcases r with a | e
  · obtain ⟨k, hk⟩ := hR.odd_weight a
    change HammingWeight (R.oddRow a) =
      R.reducedRowParity (.inl a) + 2 * R.rowGamma (.inl a)
    change HammingWeight (R.oddRow a) =
      1 + 2 * ((HammingWeight (R.oddRow a) - 1) / 2)
    rw [hk]
    omega
  · have heven := R.hammingWeight_even_of_mem_evenCode hR (R.evenBasis e).property
    obtain ⟨k, hk⟩ := heven
    change HammingWeight (R.evenBasis e : Word (ZMod 2) Col) =
      R.reducedRowParity (.inr e) + 2 * R.rowGamma (.inr e)
    change HammingWeight (R.evenBasis e : Word (ZMod 2) Col) =
      0 + 2 * ((HammingWeight (R.evenBasis e : Word (ZMod 2) Col) - 0) / 2)
    rw [hk]
    omega

theorem reducedRow_pairing_eq_zero_of_ne
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s : R.ReducedRowIndex} (hrs : r ≠ s) :
    wordPairing (R.reducedRow r) (R.reducedRow s) = 0 := by
  rcases r with a | e₁
  · rcases s with b | e₂
    · have hab : a ≠ b := by simpa using hrs
      simpa [reducedRow, R.oddRow_pairing hR, hab]
    · simpa [reducedRow, wordPairing_apply, dotProduct, mul_comm] using
        (R.wordPairing_evenCode_oddCode hR (R.evenBasis e₂).property
          (R.oddRow_mem_oddCode a))
  · rcases s with b | e₂
    · exact R.wordPairing_evenCode_oddCode hR (R.evenBasis e₁).property
          (R.oddRow_mem_oddCode b)
    · exact R.wordPairing_evenCode_rowCode hR (R.evenBasis e₁).property
          (evenCode_mem_rowCode R (R.evenBasis e₂).property)

theorem reducedRow_pair_even
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s : R.ReducedRowIndex} (hrs : r ≠ s) :
    Even (pairOverlap (R.reducedRow r) (R.reducedRow s)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, pairOverlap_cast]
  exact R.reducedRow_pairing_eq_zero_of_ne hR hrs

/-- BH12 coefficient `Γ_{rs} = |g^r ∧ g^s|/2`. -/
def rowPairGamma (R : BinaryRowFamily OddRow EvenRow Col)
    (r s : R.ReducedRowIndex) : Nat :=
  pairOverlap (R.reducedRow r) (R.reducedRow s) / 2

theorem reducedRow_pairOverlap_eq
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s : R.ReducedRowIndex} (hrs : r ≠ s) :
    pairOverlap (R.reducedRow r) (R.reducedRow s) = 2 * R.rowPairGamma r s := by
  obtain ⟨k, hk⟩ := R.reducedRow_pair_even hR hrs
  simp only [rowPairGamma]
  omega

theorem hammingWeight_smul_cast8 (c : ZMod 2) (x : Word (ZMod 2) Col) :
    (HammingWeight (c • x) : ZMod 8) =
      bitLift8 c * (HammingWeight x : ZMod 8) := by
  rw [hammingWeight_cast8, hammingWeight_cast8, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [Pi.smul_apply, smul_eq_mul, bitLift8_mul]

theorem pairOverlap_smul_cast8
    (c d : ZMod 2) (x y : Word (ZMod 2) Col) :
    (pairOverlap (c • x) (d • y) : ZMod 8) =
      bitLift8 c * bitLift8 d * (pairOverlap x y : ZMod 8) := by
  rw [pairOverlap_cast8, pairOverlap_cast8, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [Pi.smul_apply, smul_eq_mul, bitLift8_mul]
  ring

/-- Logical odd-row exponent on an ordered reduced-row sublist. -/
def logicalExponent8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) : ZMod 8 :=
  (rs.map fun r => (R.reducedRowParity r : ZMod 8) * bitLift8 (c r)).sum

/-- Linear `Γ_r` part of the residual Clifford exponent. -/
def rowGammaLinear8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) : ZMod 8 :=
  (rs.map fun r => (R.rowGamma r : ZMod 8) * bitLift8 (c r)).sum

/-- Quadratic `Γ_{rs}` part, ordered without duplicate pairs. -/
def rowGammaPair8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : List R.ReducedRowIndex → ZMod 8
  | [] => 0
  | r :: rs =>
      (rs.map fun s => (R.rowPairGamma r s : ZMod 8) *
        bitLift8 (c r) * bitLift8 (c s)).sum + R.rowGammaPair8 c rs

/-- Degree-two BH12 residual exponent `2ΣΓ_r c_r - 4ΣΓ_{rs}c_rc_s`. -/
def rowCliffordExponent8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : ZMod 8 :=
  2 * R.rowGammaLinear8 c R.reducedRowIndexList -
    4 * R.rowGammaPair8 c R.reducedRowIndexList

private theorem wordWeightSum8_reducedRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) :
    wordWeightSum8 (rs.map fun r => c r • R.reducedRow r) =
      R.logicalExponent8 c rs + 2 * R.rowGammaLinear8 c rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, wordWeightSum8]
      rw [hammingWeight_smul_cast8, R.reducedRow_weight_eq hR r]
      push_cast
      change bitLift8 (c r) *
          ((R.reducedRowParity r : ZMod 8) + 2 * (R.rowGamma r : ZMod 8)) +
          wordWeightSum8 (rs.map fun r => c r • R.reducedRow r) =
        ((R.reducedRowParity r : ZMod 8) * bitLift8 (c r) +
          R.logicalExponent8 c rs) +
        2 * ((R.rowGamma r : ZMod 8) * bitLift8 (c r) +
          R.rowGammaLinear8 c rs)
      rw [ih]
      ring

private theorem headPairSum8_reducedRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (r : R.ReducedRowIndex) (rs : List R.ReducedRowIndex) (hr : r ∉ rs) :
    ((rs.map fun s => c s • R.reducedRow s).map fun y =>
      (pairOverlap (c r • R.reducedRow r) y : ZMod 8)).sum =
      2 * (rs.map fun s => (R.rowPairGamma r s : ZMod 8) *
        bitLift8 (c r) * bitLift8 (c s)).sum := by
  induction rs with
  | nil => simp
  | cons s ss ih =>
      have hrs : r ≠ s := by
        intro hrs
        exact hr (by simp [hrs])
      have hrss : r ∉ ss := by
        intro hmem
        exact hr (by simp [hmem])
      simp only [List.map_cons, List.sum_cons]
      rw [pairOverlap_smul_cast8, R.reducedRow_pairOverlap_eq hR hrs]
      push_cast
      rw [ih hrss]
      ring

private theorem wordPairSum8_reducedRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (rs : List R.ReducedRowIndex) (hnd : rs.Nodup) :
    wordPairSum8 (rs.map fun r => c r • R.reducedRow r) =
      2 * R.rowGammaPair8 c rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
      have hndrs : rs.Nodup := (List.nodup_cons.mp hnd).2
      simp only [List.map_cons, wordPairSum8, rowGammaPair8]
      rw [headPairSum8_reducedRows R hR c r rs hr, ih hndrs]
      ring

/-- The exact reduced weight is a logical term plus a degree-two Clifford exponent. -/
theorem hammingWeight_reducedCombination_phasePolynomial
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    (HammingWeight (R.reducedCombination c) : ZMod 8) =
      R.logicalExponent8 c R.reducedRowIndexList + R.rowCliffordExponent8 c := by
  rw [R.hammingWeight_reducedCombination_mod8 hR]
  change wordWeightSum8
      (R.reducedRowIndexList.map fun r => c r • R.reducedRow r) -
      2 * wordPairSum8
        (R.reducedRowIndexList.map fun r => c r • R.reducedRow r) = _
  rw [wordWeightSum8_reducedRows R hR c,
    wordPairSum8_reducedRows R hR c R.reducedRowIndexList
      R.reducedRowIndexList_nodup]
  simp only [rowCliffordExponent8]
  ring

/-- The raw modulo-eight coefficient whose reduction modulo four is `lambdaSingle`. -/
private noncomputable def lambdaSingle8
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) : ZMod 8 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p)).sum -
    2 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientEntry rs.1 p) *
          bitLift8 (R.rowCoefficientEntry rs.2 p)).sum

/-- The raw modulo-eight coefficient whose reduction modulo two is `lambdaPair`. -/
private noncomputable def lambdaPair8
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) : ZMod 8 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 8) *
        bitLift8 (R.rowCoefficientEntry r p) *
          bitLift8 (R.rowCoefficientEntry r q)).sum -
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        (bitLift8 (R.rowCoefficientEntry rs.1 p) *
            bitLift8 (R.rowCoefficientEntry rs.2 q) +
          bitLift8 (R.rowCoefficientEntry rs.2 p) *
            bitLift8 (R.rowCoefficientEntry rs.1 q))).sum

/--
BH12 single-site correction multiplicity
`Λ_p = Σ_r Γ_r B_{rp} - 2 Σ_{r<s} Γ_{rs} B_{rp} B_{sp}` modulo four.
-/
noncomputable def lambdaSingle
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) : ZMod 4 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 4) * bitLift4 (R.rowCoefficientEntry r p)).sum -
    2 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 4) *
        bitLift4 (R.rowCoefficientEntry rs.1 p) *
          bitLift4 (R.rowCoefficientEntry rs.2 p)).sum

/--
BH12 pair correction multiplicity
`Λ_pq = Σ_r Γ_r B_{rp}B_{rq} - Σ_{r<s} Γ_{rs}
(B_{rp}B_{sq}+B_{sp}B_{rq})` modulo two.
-/
noncomputable def lambdaPair
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) : ZMod 2 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 2) * R.rowCoefficientEntry r p *
        R.rowCoefficientEntry r q).sum -
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 2) *
        (R.rowCoefficientEntry rs.1 p * R.rowCoefficientEntry rs.2 q +
          R.rowCoefficientEntry rs.2 p * R.rowCoefficientEntry rs.1 q)).sum

private theorem lambdaSingle8_cast4
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) :
    ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) (R.lambdaSingle8 p) =
      R.lambdaSingle p := by
  let phi : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)
  have hbit (b : ZMod 2) : phi (bitLift8 b) = bitLift4 b := by
    fin_cases b <;> decide
  have hlinear :
      ((R.reducedRowIndexList.map fun r => (R.rowGamma r : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry r p)).map phi).sum =
        (R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 4) * bitLift4 (R.rowCoefficientEntry r p)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    simp [Function.comp_apply, hbit]
  have hquadratic :
      (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).map phi).sum =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 4) *
            bitLift4 (R.rowCoefficientEntry rs.1 p) *
              bitLift4 (R.rowCoefficientEntry rs.2 p)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro rs _hrs
    simp [Function.comp_apply, hbit]
  change phi
      ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p)).sum -
        2 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).sum) = _
  rw [map_sub, map_mul,
    map_list_sum phi
      (R.reducedRowIndexList.map fun r =>
        (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p)),
    map_list_sum phi
      ((unorderedPairs R.reducedRowIndexList).map fun rs =>
        (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry rs.1 p) *
            bitLift8 (R.rowCoefficientEntry rs.2 p))]
  rw [hlinear, hquadratic]
  simp [lambdaSingle]
  rw [show phi 2 = (2 : ZMod 4) by decide]

private theorem lambdaPair8_cast2
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) :
    ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (R.lambdaPair8 p q) =
      R.lambdaPair p q := by
  let phi : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
  have hbit (b : ZMod 2) : phi (bitLift8 b) = b := by
    change phi (b.val : ZMod 8) = b
    rw [map_natCast]
    exact ZMod.natCast_zmod_val b
  have hlinear :
      ((R.reducedRowIndexList.map fun r => (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r p) *
              bitLift8 (R.rowCoefficientEntry r q)).map phi).sum =
        (R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 2) * R.rowCoefficientEntry r p *
            R.rowCoefficientEntry r q).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    simp [Function.comp_apply, hbit]
  have hquadratic :
      (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 q) +
              bitLift8 (R.rowCoefficientEntry rs.2 p) *
                bitLift8 (R.rowCoefficientEntry rs.1 q))).map phi).sum =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 2) *
            (R.rowCoefficientEntry rs.1 p * R.rowCoefficientEntry rs.2 q +
              R.rowCoefficientEntry rs.2 p * R.rowCoefficientEntry rs.1 q)).sum := by
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro rs _hrs
    simp [Function.comp_apply, hbit]
  change phi
      ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p) *
            bitLift8 (R.rowCoefficientEntry r q)).sum -
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 q) +
              bitLift8 (R.rowCoefficientEntry rs.2 p) *
                bitLift8 (R.rowCoefficientEntry rs.1 q))).sum) = _
  rw [map_sub,
    map_list_sum phi
      (R.reducedRowIndexList.map fun r =>
        (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p) *
          bitLift8 (R.rowCoefficientEntry r q)),
    map_list_sum phi
      ((unorderedPairs R.reducedRowIndexList).map fun rs =>
        (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          (bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 q) +
            bitLift8 (R.rowCoefficientEntry rs.2 p) *
              bitLift8 (R.rowCoefficientEntry rs.1 q)))]
  rw [hlinear, hquadratic]
  simp [lambdaPair]

private theorem two_mul_eq_val4_of_cast_eq
    (x : ZMod 8) (y : ZMod 4)
    (h : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) x = y) :
    2 * x = 2 * (y.val : ZMod 8) := by
  subst y
  fin_cases x <;> decide

private theorem four_mul_eq_val2_of_cast_eq
    (x : ZMod 8) (y : ZMod 2)
    (h : ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) x = y) :
    4 * x = 4 * (y.val : ZMod 8) := by
  subst y
  fin_cases x <;> decide

private theorem two_mul_lambdaSingle8
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) :
    2 * R.lambdaSingle8 p = 2 * ((R.lambdaSingle p).val : ZMod 8) :=
  two_mul_eq_val4_of_cast_eq _ _ (R.lambdaSingle8_cast4 p)

private theorem four_mul_lambdaPair8
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) :
    4 * R.lambdaPair8 p q = 4 * ((R.lambdaPair p q).val : ZMod 8) :=
  four_mul_eq_val2_of_cast_eq _ _ (R.lambdaPair8_cast2 p q)

private theorem rowGammaPair8_eq_unorderedPairs
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) :
    R.rowGammaPair8 c rs =
      ((unorderedPairs rs).map fun pq =>
        (R.rowPairGamma pq.1 pq.2 : ZMod 8) *
          bitLift8 (c pq.1) * bitLift8 (c pq.2)).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [rowGammaPair8, unorderedPairs, List.map_append, List.sum_append,
        List.map_map, ih]
      rfl

private theorem coefficientBitList_liftSum8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    ((R.coefficientBitList f r).map bitLift8).sum =
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum := by
  simp only [coefficientBitList, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _hp
  simpa only [Function.comp_apply] using
    bitLift8_mul (R.rowCoefficientEntry r p) (f p)

private theorem coefficientBitList_pairSum8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    bitPairSum8 (R.coefficientBitList f r) =
      ((sitePairList Col).map fun pq =>
        (bitLift8 (R.rowCoefficientEntry r pq.1) * bitLift8 (f pq.1)) *
          (bitLift8 (R.rowCoefficientEntry r pq.2) * bitLift8 (f pq.2))).sum := by
  rw [bitPairSum8_eq_unorderedPairs]
  simp only [coefficientBitList, unorderedPairs_map, sitePairList, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pq _hpq
  change bitLift8 (R.rowCoefficientEntry r pq.1 * f pq.1) *
      bitLift8 (R.rowCoefficientEntry r pq.2 * f pq.2) = _
  rw [bitLift8_mul, bitLift8_mul]

private theorem linearCoordinate_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r) =
      2 * (R.rowGamma r : ZMod 8) *
          ((siteList Col).map fun p =>
            bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum -
        4 * (R.rowGamma r : ZMod 8) *
          ((sitePairList Col).map fun pq =>
            (bitLift8 (R.rowCoefficientEntry r pq.1) * bitLift8 (f pq.1)) *
              (bitLift8 (R.rowCoefficientEntry r pq.2) *
                bitLift8 (f pq.2))).sum := by
  rw [← R.booleanXor_coefficientBitList f r]
  rw [show 2 * (R.rowGamma r : ZMod 8) *
      bitLift8 (booleanXor (R.coefficientBitList f r)) =
      (R.rowGamma r : ZMod 8) *
        (2 * bitLift8 (booleanXor (R.coefficientBitList f r))) by ring]
  rw [two_mul_bitLift8_booleanXor, R.coefficientBitList_liftSum8 f r,
    R.coefficientBitList_pairSum8 f r]
  ring

private theorem quadraticCoordinate_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r s : R.ReducedRowIndex) :
    4 * bitLift8 (R.rowCoefficientMap f r) *
        bitLift8 (R.rowCoefficientMap f s) =
      4 * ((siteList Col).map fun p =>
        (bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)) *
          (bitLift8 (R.rowCoefficientEntry s p) * bitLift8 (f p))).sum +
      4 * ((sitePairList Col).map fun pq =>
        (bitLift8 (R.rowCoefficientEntry r pq.1) * bitLift8 (f pq.1)) *
            (bitLift8 (R.rowCoefficientEntry s pq.2) * bitLift8 (f pq.2)) +
          (bitLift8 (R.rowCoefficientEntry r pq.2) * bitLift8 (f pq.2)) *
            (bitLift8 (R.rowCoefficientEntry s pq.1) * bitLift8 (f pq.1))).sum := by
  rw [← R.booleanXor_coefficientBitList f r,
    ← R.booleanXor_coefficientBitList f s,
    four_mul_bitLift8_booleanXor_mul,
    R.coefficientBitList_liftSum8 f r,
    R.coefficientBitList_liftSum8 f s]
  rw [show 4 *
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum *
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry s p) * bitLift8 (f p)).sum =
      4 * (((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum *
      ((siteList Col).map fun p =>
        bitLift8 (R.rowCoefficientEntry s p) * bitLift8 (f p)).sum) by ring]
  rw [list_sum_mul_sum_split_pairs, mul_add]
  simp only [sitePairList]

private theorem linearCoordinate_expand8_siteSums
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : R.ReducedRowIndex) :
    2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r) =
      ((siteList Col).map fun p =>
        2 * (R.rowGamma r : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum -
      ((sitePairList Col).map fun pq =>
        4 * (R.rowGamma r : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry r pq.1) *
            bitLift8 (R.rowCoefficientEntry r pq.2) *
              bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  rw [R.linearCoordinate_expand8 f r]
  rw [mul_list_sum, mul_list_sum]
  apply congrArg₂ (· - ·)
  · rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    simp only [Function.comp_apply]
    ring
  · rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pq _hpq
    simp only [Function.comp_apply]
    ring

private theorem linearCoordinates_sum_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    (R.reducedRowIndexList.map fun r =>
      2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r)).sum =
      2 * ((siteList Col).map fun p =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r p)).sum) * bitLift8 (f p)).sum -
      4 * ((sitePairList Col).map fun pq =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r pq.1) *
              bitLift8 (R.rowCoefficientEntry r pq.2)).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  calc
    (R.reducedRowIndexList.map fun r =>
        2 * (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientMap f r)).sum =
        (R.reducedRowIndexList.map fun r =>
          ((siteList Col).map fun p =>
            2 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum -
          ((sitePairList Col).map fun pq =>
            4 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r pq.1) *
                bitLift8 (R.rowCoefficientEntry r pq.2) *
                  bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro r _hr
            exact R.linearCoordinate_expand8_siteSums f r
    _ = ((siteList Col).map fun p =>
          (R.reducedRowIndexList.map fun r =>
            2 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r p) * bitLift8 (f p)).sum).sum -
        ((sitePairList Col).map fun pq =>
          (R.reducedRowIndexList.map fun r =>
            4 * (R.rowGamma r : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry r pq.1) *
                bitLift8 (R.rowCoefficientEntry r pq.2) *
                  bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            rw [list_sum_map_sub,
              list_sum_comm R.reducedRowIndexList (siteList Col),
              list_sum_comm R.reducedRowIndexList (sitePairList Col)]
    _ = _ := by
      apply congrArg₂ (· - ·)
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right]
        have hscale :
            (R.reducedRowIndexList.map fun r =>
              2 * (R.rowGamma r : ZMod 8) *
                bitLift8 (R.rowCoefficientEntry r p)).sum =
              2 * (R.reducedRowIndexList.map fun r =>
                (R.rowGamma r : ZMod 8) *
                  bitLift8 (R.rowCoefficientEntry r p)).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r _hr
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro pq _hpq
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right, list_sum_map_mul_right]
        have hscale :
            (R.reducedRowIndexList.map fun r =>
              4 * (R.rowGamma r : ZMod 8) *
                bitLift8 (R.rowCoefficientEntry r pq.1) *
                  bitLift8 (R.rowCoefficientEntry r pq.2)).sum =
              4 * (R.reducedRowIndexList.map fun r =>
                (R.rowGamma r : ZMod 8) *
                  bitLift8 (R.rowCoefficientEntry r pq.1) *
                    bitLift8 (R.rowCoefficientEntry r pq.2)).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r _hr
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring

private theorem quadraticCoordinate_expand8_siteSums
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (rs : R.ReducedRowIndex × R.ReducedRowIndex) :
    4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientMap f rs.1) *
          bitLift8 (R.rowCoefficientMap f rs.2) =
      ((siteList Col).map fun p =>
        4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          bitLift8 (R.rowCoefficientEntry rs.1 p) *
            bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p)).sum +
      ((sitePairList Col).map fun pq =>
        4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
              bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
            bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
              bitLift8 (R.rowCoefficientEntry rs.1 pq.2)) *
            bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  calc
    4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientMap f rs.1) *
          bitLift8 (R.rowCoefficientMap f rs.2) =
        (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          (4 * bitLift8 (R.rowCoefficientMap f rs.1) *
            bitLift8 (R.rowCoefficientMap f rs.2)) := by ring
    _ = (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        (4 * ((siteList Col).map fun p =>
          (bitLift8 (R.rowCoefficientEntry rs.1 p) * bitLift8 (f p)) *
            (bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p))).sum +
        4 * ((sitePairList Col).map fun pq =>
          (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) * bitLift8 (f pq.1)) *
              (bitLift8 (R.rowCoefficientEntry rs.2 pq.2) * bitLift8 (f pq.2)) +
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.2) * bitLift8 (f pq.2)) *
              (bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                bitLift8 (f pq.1))).sum) := by
          rw [R.quadraticCoordinate_expand8 f rs.1 rs.2]
    _ = (4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8)) *
          ((siteList Col).map fun p =>
            (bitLift8 (R.rowCoefficientEntry rs.1 p) * bitLift8 (f p)) *
              (bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p))).sum +
        (4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8)) *
          ((sitePairList Col).map fun pq =>
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) * bitLift8 (f pq.1)) *
                (bitLift8 (R.rowCoefficientEntry rs.2 pq.2) * bitLift8 (f pq.2)) +
              (bitLift8 (R.rowCoefficientEntry rs.1 pq.2) * bitLift8 (f pq.2)) *
                (bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                  bitLift8 (f pq.1))).sum := by ring
    _ = _ := by
      rw [mul_list_sum, mul_list_sum, List.map_map, List.map_map]
      apply congrArg₂ (· + ·)
      · apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        simp only [Function.comp_apply]
        ring_nf
        simp only [pow_two, bitLift8_mul_self]
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pq _hpq
        simp only [Function.comp_apply]
        ring

private theorem quadraticCoordinates_sum_expand8
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientMap f rs.1) *
          bitLift8 (R.rowCoefficientMap f rs.2)).sum =
      4 * ((siteList Col).map fun p =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).sum) * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
              bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  calc
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
        4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
          bitLift8 (R.rowCoefficientMap f rs.1) *
            bitLift8 (R.rowCoefficientMap f rs.2)).sum =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          ((siteList Col).map fun p =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p)).sum +
          ((sitePairList Col).map fun pq =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.1 pq.2)) *
                bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro rs _hrs
            exact R.quadraticCoordinate_expand8_siteSums f rs
    _ = ((siteList Col).map fun p =>
          ((unorderedPairs R.reducedRowIndexList).map fun rs =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              bitLift8 (R.rowCoefficientEntry rs.1 p) *
                bitLift8 (R.rowCoefficientEntry rs.2 p) * bitLift8 (f p)).sum).sum +
        ((sitePairList Col).map fun pq =>
          ((unorderedPairs R.reducedRowIndexList).map fun rs =>
            4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
              (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                  bitLift8 (R.rowCoefficientEntry rs.1 pq.2)) *
                bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum).sum := by
            rw [list_sum_map_add,
              list_sum_comm (unorderedPairs R.reducedRowIndexList) (siteList Col),
              list_sum_comm (unorderedPairs R.reducedRowIndexList)
                (sitePairList Col)]
    _ = _ := by
      apply congrArg₂ (· + ·)
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro p _hp
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right]
        have hscale :
            ((unorderedPairs R.reducedRowIndexList).map fun rs =>
              4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                bitLift8 (R.rowCoefficientEntry rs.1 p) *
                  bitLift8 (R.rowCoefficientEntry rs.2 p)).sum =
              4 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
                (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                  bitLift8 (R.rowCoefficientEntry rs.1 p) *
                    bitLift8 (R.rowCoefficientEntry rs.2 p)).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro rs _hrs
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring
      · rw [mul_list_sum, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro pq _hpq
        simp only [Function.comp_apply]
        rw [list_sum_map_mul_right, list_sum_map_mul_right]
        have hscale :
            ((unorderedPairs R.reducedRowIndexList).map fun rs =>
              4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                    bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                  bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                    bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum =
              4 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
                (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
                  (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                      bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
                    bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                      bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum := by
          rw [mul_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro rs _hrs
          simp only [Function.comp_apply]
          ring
        rw [hscale]
        ring

private theorem lambdaSingle8_siteSum
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    2 * ((siteList Col).map fun p => R.lambdaSingle8 p * bitLift8 (f p)).sum =
      2 * ((siteList Col).map fun p =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r p)).sum) * bitLift8 (f p)).sum -
      4 * ((siteList Col).map fun p =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry rs.1 p) *
              bitLift8 (R.rowCoefficientEntry rs.2 p)).sum) * bitLift8 (f p)).sum := by
  rw [mul_list_sum, mul_list_sum, mul_list_sum,
    List.map_map, List.map_map, List.map_map]
  rw [← list_sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _hp
  simp only [Function.comp_apply, lambdaSingle8]
  ring

private theorem lambdaPair8_sitePairSum
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    4 * ((sitePairList Col).map fun pq =>
      R.lambdaPair8 pq.1 pq.2 * bitLift8 (f pq.1) *
        bitLift8 (f pq.2)).sum =
      4 * ((sitePairList Col).map fun pq =>
        ((R.reducedRowIndexList.map fun r =>
          (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientEntry r pq.1) *
              bitLift8 (R.rowCoefficientEntry r pq.2)).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum -
      4 * ((sitePairList Col).map fun pq =>
        (((unorderedPairs R.reducedRowIndexList).map fun rs =>
          (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            (bitLift8 (R.rowCoefficientEntry rs.1 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.2 pq.2) +
              bitLift8 (R.rowCoefficientEntry rs.2 pq.1) *
                bitLift8 (R.rowCoefficientEntry rs.1 pq.2))).sum) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  rw [mul_list_sum, mul_list_sum, mul_list_sum,
    List.map_map, List.map_map, List.map_map]
  rw [← list_sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pq _hpq
  simp only [Function.comp_apply, lambdaPair8]
  ring

private theorem rowCliffordExponent8_physical_raw
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    R.rowCliffordExponent8 (R.rowCoefficientMap f) =
      2 * ((siteList Col).map fun p =>
        R.lambdaSingle8 p * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        R.lambdaPair8 pq.1 pq.2 * bitLift8 (f pq.1) *
          bitLift8 (f pq.2)).sum := by
  have hlinear :
      2 * R.rowGammaLinear8 (R.rowCoefficientMap f) R.reducedRowIndexList =
        (R.reducedRowIndexList.map fun r =>
          2 * (R.rowGamma r : ZMod 8) *
            bitLift8 (R.rowCoefficientMap f r)).sum := by
    simp only [rowGammaLinear8]
    rw [mul_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    simp only [Function.comp_apply]
    ring
  have hquadratic :
      4 * R.rowGammaPair8 (R.rowCoefficientMap f) R.reducedRowIndexList =
        ((unorderedPairs R.reducedRowIndexList).map fun rs =>
          4 * (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
            bitLift8 (R.rowCoefficientMap f rs.1) *
              bitLift8 (R.rowCoefficientMap f rs.2)).sum := by
    rw [R.rowGammaPair8_eq_unorderedPairs]
    rw [mul_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro rs _hrs
    simp only [Function.comp_apply]
    ring
  simp only [rowCliffordExponent8]
  rw [hlinear, hquadratic, R.linearCoordinates_sum_expand8 f,
    R.quadraticCoordinates_sum_expand8 f,
    R.lambdaSingle8_siteSum f, R.lambdaPair8_sitePairSum f]
  ring_nf
  have hnegFour (x : ZMod 8) : -(x * 4) = x * 4 := by
    calc
      -(x * 4) = x * (-4) := by ring
      _ = x * 4 := by rw [show (-4 : ZMod 8) = 4 by decide]
  simp only [sub_eq_add_neg]
  simp_rw [hnegFour]

/--
The complete BH12 Boolean residual exponent expressed on physical sites:
diagonal terms use `lambdaSingle`, and canonical unordered site pairs use `lambdaPair`.
-/
theorem rowCliffordExponent8_physical
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col) :
    R.rowCliffordExponent8 (R.rowCoefficientMap f) =
      2 * ((siteList Col).map fun p =>
        ((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)).sum +
      4 * ((sitePairList Col).map fun pq =>
        ((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum := by
  rw [R.rowCliffordExponent8_physical_raw f]
  apply congrArg₂ (· + ·)
  · rw [mul_list_sum, mul_list_sum, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    simp only [Function.comp_apply]
    calc
      2 * (R.lambdaSingle8 p * bitLift8 (f p)) =
          (2 * R.lambdaSingle8 p) * bitLift8 (f p) := by ring
      _ = (2 * ((R.lambdaSingle p).val : ZMod 8)) * bitLift8 (f p) := by
        rw [R.two_mul_lambdaSingle8 p]
      _ = 2 * (((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)) := by ring
  · rw [mul_list_sum, mul_list_sum, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pq _hpq
    simp only [Function.comp_apply]
    calc
      4 * (R.lambdaPair8 pq.1 pq.2 * bitLift8 (f pq.1) *
          bitLift8 (f pq.2)) =
          (4 * R.lambdaPair8 pq.1 pq.2) * bitLift8 (f pq.1) *
            bitLift8 (f pq.2) := by ring
      _ = (4 * ((R.lambdaPair pq.1 pq.2).val : ZMod 8)) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2) := by
        rw [R.four_mul_lambdaPair8 pq.1 pq.2]
      _ = 4 * (((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
          bitLift8 (f pq.1) * bitLift8 (f pq.2)) := by ring

/-- Physical Clifford-correction exponent in `ℤ/8ℤ`. -/
def correctionExponent8
    (R : BinaryRowFamily OddRow EvenRow Col)
    (f : Word (ZMod 2) Col) : ZMod 8 :=
  -2 * ((siteList Col).map fun p =>
      ((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)).sum +
    4 * ((sitePairList Col).map fun pq =>
      ((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
        bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum

/-- The physical inverse-`S`/controlled-`Z` exponent cancels the BH12 residual. -/
theorem rowCliffordExponent8_add_correctionExponent8
    (R : BinaryRowFamily OddRow EvenRow Col)
    (f : Word (ZMod 2) Col) :
    R.rowCliffordExponent8 (R.rowCoefficientMap f) +
        R.correctionExponent8 f = 0 := by
  rw [R.rowCliffordExponent8_physical f]
  simp only [correctionExponent8]
  have h8 : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
  ring_nf
  simp [h8]

/-- Integer lift of the explicit physical correction exponent. -/
def correctionExponentInt
    (R : BinaryRowFamily OddRow EvenRow Col)
    (bits : Qubit.Bitstring Col) : Int :=
  -2 * ((siteList Col).map fun p =>
      ((R.lambdaSingle p).val : Int) * (bits p).val).sum +
    4 * ((sitePairList Col).map fun pq =>
      ((R.lambdaPair pq.1 pq.2).val : Int) *
        (bits pq.1).val * (bits pq.2).val).sum

private theorem bitLift8_finTwo (b : Fin 2) :
    bitLift8 (b : ZMod 2) = (b.val : ZMod 8) := by
  fin_cases b <;> decide

theorem correctionExponentInt_cast8
    (R : BinaryRowFamily OddRow EvenRow Col)
    (bits : Qubit.Bitstring Col) :
    (R.correctionExponentInt bits : ZMod 8) =
      R.correctionExponent8 (bitstringWordEquiv Col bits) := by
  simp only [correctionExponentInt, correctionExponent8]
  push_cast
  simp only [List.map_map, bitstringWordEquiv_apply]
  congr 1
  · congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    simp only [Function.comp_apply]
    push_cast
    rw [bitLift8_finTwo]
  · congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro pq _hpq
    simp only [Function.comp_apply]
    push_cast
    rw [bitLift8_finTwo, bitLift8_finTwo]

theorem cliffordCorrectionAngle_eq_correctionExponentInt
    (R : BinaryRowFamily OddRow EvenRow Col)
    (bits : Qubit.Bitstring Col) :
    cliffordCorrectionAngle R.lambdaSingle R.lambdaPair bits =
      Real.pi / 4 * (R.correctionExponentInt bits : Real) := by
  simp only [cliffordCorrectionAngle, correctionExponentInt]
  push_cast
  rw [mul_add]
  congr 1
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _hp
    simp only [Function.comp_apply]
    push_cast
    ring
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    simp only [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro pq _hpq
    simp only [Function.comp_apply]
    push_cast
    ring

/-- The explicit BH12 inverse-`S`/controlled-`Z` correction. -/
noncomputable def physicalCliffordCorrection
    (R : BinaryRowFamily OddRow EvenRow Col) :
    UnitaryTransport (Qubit.QubitRegister Col) (Qubit.QubitRegister Col) :=
  cliffordCorrection R.lambdaSingle R.lambdaPair

@[simp] theorem physicalCliffordCorrection_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col) :
    R.physicalCliffordCorrection psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 * (R.correctionExponentInt bits : Real)) * psi bits := by
  rw [physicalCliffordCorrection, cliffordCorrection_apply,
    R.cliffordCorrectionAngle_eq_correctionExponentInt bits]

/-- The raw all-site `T` layer followed by the explicit BH12 Clifford correction. -/
noncomputable def correctedAllSiteT
    (R : BinaryRowFamily OddRow EvenRow Col) :
    UnitaryTransport (Qubit.QubitRegister Col) (Qubit.QubitRegister Col) :=
  (allSiteT (Index := Col)).trans R.physicalCliffordCorrection

/-- Integer exponent of the corrected physical layer on one basis bitstring. -/
def correctedExponentInt
    (R : BinaryRowFamily OddRow EvenRow Col)
    (bits : Qubit.Bitstring Col) : Int :=
  (HammingWeight (bitstringWordEquiv Col bits) : Int) +
    R.correctionExponentInt bits

@[simp] theorem correctedAllSiteT_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col) :
    R.correctedAllSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 * (R.correctedExponentInt bits : Real)) * psi bits := by
  rw [correctedAllSiteT, UnitaryTransport.trans_apply,
    physicalCliffordCorrection_apply, allSiteT_apply]
  rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
  congr 2
  simp only [correctedExponentInt]
  push_cast
  ring

theorem correctedExponentInt_cast8_of_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    (R.correctedExponentInt bits : ZMod 8) =
      R.logicalExponent8 c R.reducedRowIndexList := by
  simp only [correctedExponentInt]
  push_cast
  rw [R.correctionExponentInt_cast8 bits, hbits,
    R.hammingWeight_reducedCombination_phasePolynomial hR c]
  have hcancel :=
    R.rowCliffordExponent8_add_correctionExponent8 (R.reducedCombination c)
  rw [R.rowCoefficientMap_reducedCombination hR c] at hcancel
  rw [add_assoc, hcancel, add_zero]

/--
On every reduced-row combination, corrected transversal `T` leaves exactly
the odd-row logical phase exponent.
-/
theorem correctedAllSiteT_apply_of_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    R.correctedAllSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 *
          ((R.logicalExponent8 c R.reducedRowIndexList).val : Real)) *
        psi bits := by
  rw [R.correctedAllSiteT_apply]
  have hphase := phaseAmplitude_pi_div_four_int_eq_of_cast_eq
    (R.correctedExponentInt bits)
    ((R.logicalExponent8 c R.reducedRowIndexList).val : Int) (by
      rw [R.correctedExponentInt_cast8_of_reducedCombination hR bits c hbits]
      simpa using ZMod.natCast_zmod_val
        (R.logicalExponent8 c R.reducedRowIndexList))
  rw [hphase]
  norm_cast

/-- The independent reduced rows span exactly the original total row code. -/
theorem span_reducedRows_eq_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Submodule.span (ZMod 2) (Set.range R.reducedRow) = R.rowCode.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨r, rfl⟩
    rcases r with a | b
    · exact R.row_mem_rowCode (.inl a)
    · rw [R.rowCode_eq_evenCode_sup_oddCode]
      exact Submodule.mem_sup_left (R.evenBasis b).property
  · rw [R.rowCode_eq_evenCode_sup_oddCode]
    apply sup_le
    · rw [← R.span_evenBasis_eq_evenCode]
      apply Submodule.span_mono
      rintro x ⟨b, rfl⟩
      exact ⟨Sum.inr b, rfl⟩
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl a, rfl⟩

theorem range_reducedCombination_eq_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) :
    LinearMap.range R.reducedCombination = R.rowCode.carrier := by
  rw [reducedCombination, Fintype.range_linearCombination,
    R.span_reducedRows_eq_rowCode]

theorem exists_reducedCombination_of_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    {f : Word (ZMod 2) Col} (hf : f ∈ R.rowCode.carrier) :
    ∃ c : Word (ZMod 2) R.ReducedRowIndex,
      R.reducedCombination c = f := by
  have hrange : f ∈ LinearMap.range R.reducedCombination := by
    rw [R.range_reducedCombination_eq_rowCode]
    exact hf
  exact hrange

theorem rowCode_le_dual_dual
    (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.carrier ≤ R.rowCode.dual.dual.carrier :=
  LinearCode.le_dual_of_le_dual R.rowCode R.rowCode.dual le_rfl

theorem rowCode_dual_dual_eq
    (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.dual.dual.carrier = R.rowCode.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (R.rowCode_le_dual_dual)
  change Dimension R.rowCode = Dimension R.rowCode.dual.dual
  have h₁ := R.rowCode.dimension_add_dual_dimension_eq_length
  have h₂ := R.rowCode.dual.dimension_add_dual_dimension_eq_length
  omega

/-- Odd logical coordinates extracted from a reduced-row coefficient word. -/
def oddCoefficients (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : Word (ZMod 2) OddRow :=
  fun a => c (.inl a)

/-- Even-span component of a reduced-row coefficient word. -/
def evenPart (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : Word (ZMod 2) Col :=
  ∑ b, c (.inr b) • (R.evenBasis b : Word (ZMod 2) Col)

theorem evenPart_mem_evenCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.evenPart c ∈ R.evenCode.carrier := by
  exact Submodule.sum_mem R.evenCode.carrier (fun b _ =>
    R.evenCode.carrier.smul_mem _ (R.evenBasis b).property)

theorem reducedCombination_eq_oddCombination_add_evenPart
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.reducedCombination c =
      R.oddCombination (R.oddCoefficients c) + R.evenPart c := by
  rw [R.reducedCombination_apply, Fintype.sum_sum_type,
    R.oddCombination_apply]
  rfl

theorem reducedCombination_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.reducedCombination c ∈ R.rowCode.carrier := by
  rw [R.reducedCombination_eq_oddCombination_add_evenPart]
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right (R.oddCombination_mem_oddCode (R.oddCoefficients c)))
    (Submodule.mem_sup_left (R.evenPart_mem_evenCode c))

theorem reducedCombination_mem_dual_dual
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.reducedCombination c ∈ R.rowCode.dual.dual.carrier :=
  R.rowCode_le_dual_dual (R.reducedCombination_mem_rowCode c)

/-- A reduced word represents precisely the quotient class of its odd coordinates. -/
theorem quotient_mk_reducedCombination_eq_oddWordToLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    Submodule.Quotient.mk
        (⟨R.reducedCombination c, R.reducedCombination_mem_dual_dual c⟩ :
          R.rowCode.dual.dual.carrier) =
      R.oddWordToLogicalQuotient (R.oddCoefficients c) := by
  rw [oddWordToLogicalQuotient]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  change R.reducedCombination c - R.oddCombination (R.oddCoefficients c) ∈
    R.evenCode.carrier
  rw [R.reducedCombination_eq_oddCombination_add_evenPart]
  simpa using R.evenPart_mem_evenCode c

/-- Computational logical label carried by the odd reduced-row coordinates. -/
def reducedLogicalBits
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : Qubit.Bitstring OddRow :=
  (bitstringWordEquiv OddRow).symm (R.oddCoefficients c)

theorem logicalBasisEquiv_symm_mk_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    (R.logicalBasisEquivLogicalQuotient hR).symm
        (Submodule.Quotient.mk
          (⟨R.reducedCombination c, R.reducedCombination_mem_dual_dual c⟩ :
            R.rowCode.dual.dual.carrier)) =
      R.reducedLogicalBits c := by
  apply (R.logicalBasisEquivLogicalQuotient hR).injective
  rw [Equiv.apply_symm_apply]
  rw [R.quotient_mk_reducedCombination_eq_oddWordToLogicalQuotient c]
  simp [logicalBasisEquivLogicalQuotient, reducedLogicalBits]

/-- The residual logical exponent is the Hamming weight of the odd coordinates. -/
theorem logicalExponent8_eq_hammingWeight_oddCoefficients
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.logicalExponent8 c R.reducedRowIndexList =
      (HammingWeight (R.oddCoefficients c) : ZMod 8) := by
  rw [logicalExponent8]
  rw [← List.sum_toFinset _ R.reducedRowIndexList_nodup]
  have hset : R.reducedRowIndexList.toFinset = Finset.univ := by
    rw [reducedRowIndexList, ← Fin.univ_image_def]
    ext r
    simp
  rw [hset, Fintype.sum_sum_type]
  rw [hammingWeight_cast8]
  simp [reducedRowParity, oddCoefficients]

@[simp] theorem bitstringWordEquiv_reducedLogicalBits
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    bitstringWordEquiv OddRow (R.reducedLogicalBits c) =
      R.oddCoefficients c := by
  simp [reducedLogicalBits]

theorem correctedAllSiteT_apply_of_reducedCombination_oddWeight
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    R.correctedAllSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 * (HammingWeight (R.oddCoefficients c) : Real)) *
        psi bits := by
  rw [R.correctedAllSiteT_apply_of_reducedCombination hR psi bits c hbits]
  have hphase := phaseAmplitude_pi_div_four_eq_of_natCast_eq
    (HammingWeight (R.oddCoefficients c))
    (R.logicalExponent8 c R.reducedRowIndexList)
    (R.logicalExponent8_eq_hammingWeight_oddCoefficients c).symm
  rw [← hphase]

/-- Simultaneous logical `T` acts diagonally on each computational basis state. -/
theorem allSiteT_logicalComputationalState
    (label : Qubit.Bitstring OddRow) :
    (allSiteT (Index := OddRow)) (logicalComputationalState label) =
      OneQubitMagic.phaseAmplitude
          (Real.pi / 4 *
            (HammingWeight (bitstringWordEquiv OddRow label) : Real)) •
        logicalComputationalState label := by
  ext bits
  rw [allSiteT_apply]
  simp only [logicalComputationalState_apply]
  by_cases hlabel : label = bits
  · subst bits
    simp
  · simp [hlabel]

/-- Every encoded computational basis state has the matching corrected `T` eigenphase. -/
theorem correctedAllSiteT_encodedComputationalState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) :
    R.correctedAllSiteT
        (R.encodedComputationalState hR label : Qubit.QubitRegister Col) =
      OneQubitMagic.phaseAmplitude
          (Real.pi / 4 *
            (HammingWeight (bitstringWordEquiv OddRow label) : Real)) •
        (R.encodedComputationalState hR label : Qubit.QubitRegister Col) := by
  ext bits
  by_cases hmem :
      bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier
  · have hrow : bitstringWordEquiv Col bits ∈ R.rowCode.carrier := by
      rw [← R.rowCode_dual_dual_eq]
      exact hmem
    obtain ⟨c, hc⟩ := R.exists_reducedCombination_of_mem_rowCode hrow
    rw [R.correctedAllSiteT_apply_of_reducedCombination_oddWeight hR _ bits c hc.symm]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [R.encodedComputationalState_apply_of_mem hR label hmem]
    have hsub :
        (⟨bitstringWordEquiv Col bits, hmem⟩ :
          R.rowCode.dual.dual.carrier) =
        ⟨R.reducedCombination c, R.reducedCombination_mem_dual_dual c⟩ := by
      apply Subtype.ext
      exact hc.symm
    have hlogical :
        (R.logicalBasisEquivLogicalQuotient hR).symm
            (Submodule.Quotient.mk
              (⟨bitstringWordEquiv Col bits, hmem⟩ :
                R.rowCode.dual.dual.carrier)) =
          R.reducedLogicalBits c := by
      rw [hsub]
      exact R.logicalBasisEquiv_symm_mk_reducedCombination hR c
    rw [hlogical]
    by_cases hlabel : label = R.reducedLogicalBits c
    · subst label
      rw [if_pos rfl, R.bitstringWordEquiv_reducedLogicalBits c]
    · simp [hlabel]
  · rw [R.correctedAllSiteT_apply]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [R.encodedComputationalState_apply_of_not_mem hR label hmem]
    simp

/-- Corrected physical `T` intertwines encoding on every computational basis state. -/
theorem correctedAllSiteT_intertwines_logicalComputationalState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) :
    R.correctedAllSiteT
        (R.encoding hR (logicalComputationalState label) : Qubit.QubitRegister Col) =
      (R.encoding hR
        ((allSiteT (Index := OddRow)) (logicalComputationalState label)) :
          Qubit.QubitRegister Col) := by
  change R.correctedAllSiteT
      (R.encodedComputationalState hR label : Qubit.QubitRegister Col) = _
  rw [R.correctedAllSiteT_encodedComputationalState hR label,
    allSiteT_logicalComputationalState]
  rw [map_smul]
  rfl

/-- Corrected physical `T` intertwines the encoding on every logical state. -/
theorem correctedAllSiteT_intertwines_encoding
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister OddRow) :
    R.correctedAllSiteT
        (R.encoding hR psi : Qubit.QubitRegister Col) =
      (R.encoding hR ((allSiteT (Index := OddRow)) psi) :
        Qubit.QubitRegister Col) := by
  let encodeAmbient :
      Qubit.QubitRegister OddRow →ₗ[Complex] Qubit.QubitRegister Col :=
    R.cssQuantumCode.carrier.subtype.comp (R.encoding hR).toLinearMap
  have hlinear :
      R.correctedAllSiteT.toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp (allSiteT (Index := OddRow)).toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Qubit.Bitstring OddRow) Complex).toBasis.ext
    intro label
    change R.correctedAllSiteT
        (R.encoding hR (logicalComputationalState label) :
          Qubit.QubitRegister Col) =
      (R.encoding hR
        ((allSiteT (Index := OddRow)) (logicalComputationalState label)) :
          Qubit.QubitRegister Col)
    exact R.correctedAllSiteT_intertwines_logicalComputationalState hR label
  exact LinearMap.congr_fun hlinear psi

universe v

/-- The exact corrected BH12 transversal implementation equation. -/
theorem correctedAllSiteT_implements_logicalAllSiteT
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    (R.encodedCode hR).ImplementsLogicalGate R.correctedAllSiteT
      (allSiteT (Index := LogicalRow)) := by
  intro psi
  change R.correctedAllSiteT
      (R.encoding hR psi : Qubit.QubitRegister PhysicalCol) =
    (R.encoding hR ((allSiteT (Index := LogicalRow)) psi) :
      Qubit.QubitRegister PhysicalCol)
  exact R.correctedAllSiteT_intertwines_encoding hR psi

end BinaryRowFamily

end Triorthogonal
end Distillation
end QEC
