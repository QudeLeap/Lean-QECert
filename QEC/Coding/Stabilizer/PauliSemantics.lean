import QEC.Coding.Core.Definitions
import QEC.Semantics.ErrorCorrection.CodeSupport
import QEC.Semantics.ErrorCorrection.KLRecovery
import QEC.Semantics.Channels.Kraus
import QEC.Semantics.Channels.KrausKnillLaflamme
import QEC.Semantics.Core.Qubit
/-!
# Binary Pauli operator semantics

This module is an internal bridge from binary Pauli-symplectic coordinates to
the concrete finite qubit-register operators supplied by `QEC.Semantics.Qubit`.

Convention: the Pauli phase bit is binary. `0 : ZMod 2` is interpreted as the
global scalar `+1`, and `1 : ZMod 2` is interpreted as `-1`. Coordinates are
ordered as `X` support followed by `Z` support, so the nontrivial product phase
comes from moving a left `Z` support past a right `X` support.
-/

noncomputable section

namespace QEC
namespace Semantics
namespace Qubit

open Classical
open scoped BigOperators

universe u

variable {ι : Type u}

/-- Flipping two finite supports commutes on computational-basis bitstrings. -/
theorem flipSupport_commute [DecidableEq ι] (s t : Finset ι) (bits : Bitstring ι) :
    flipSupport s (flipSupport t bits) = flipSupport t (flipSupport s bits) := by
  funext i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp [flipSupport, his, hit]

variable [Fintype ι] [DecidableEq ι]

/-- Support-level `X` operators commute. -/
theorem localXSupport_commute (s t : Finset ι) :
    localXSupport s * localXSupport t = localXSupport t * localXSupport s := by
  ext ψ bits
  simp [Module.End.mul_apply, flipSupport_commute]

/-- Support-level `Z` operators commute. -/
theorem localZSupport_commute (s t : Finset ι) :
    localZSupport s * localZSupport t = localZSupport t * localZSupport s := by
  ext ψ bits
  simp [Module.End.mul_apply, mul_left_comm]

@[simp] theorem localXSupport_empty :
    localXSupport (∅ : Finset ι) = 1 := by
  ext ψ bits
  simp

@[simp] theorem localZSupport_empty :
    localZSupport (∅ : Finset ι) = 1 := by
  ext ψ bits
  simp [localZSupport, zSupportPhase]

omit [Fintype ι] in
/-- The support swap sign is its own inverse. -/
theorem supportPhaseSign_mul_self (xSupport zSupport : Finset ι) :
    supportPhaseSign xSupport zSupport * supportPhaseSign xSupport zSupport = 1 := by
  simp only [supportPhaseSign]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _hi
  by_cases hix : i ∈ xSupport <;> simp [hix]

/-- Moving a support-level `Z` past a support-level `X` gives the same binary sign. -/
theorem localZSupport_localXSupport_phase (xSupport zSupport : Finset ι) :
    localZSupport zSupport * localXSupport xSupport =
      supportPhaseSign xSupport zSupport •
        (localXSupport xSupport * localZSupport zSupport) := by
  ext ψ bits
  simp [Module.End.mul_apply, zSupportPhase_flipSupport, smul_eq_mul, mul_assoc]
  rw [← mul_assoc, supportPhaseSign_mul_self, one_mul]

/-- Support-level `X` operators are self-adjoint. -/
theorem localXSupport_adjoint (s : Finset ι) :
    LinearMap.adjoint (localXSupport s) = localXSupport s := by
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his hs
    calc
      LinearMap.adjoint (localXSupport (insert i s))
          = LinearMap.adjoint (localX i * localXSupport s) := by
              rw [localXSupport_insert s his]
      _ = LinearMap.adjoint (localXSupport s) * LinearMap.adjoint (localX i) := by
              simp [Module.End.mul_eq_comp]
      _ = localXSupport s * localX i := by
              rw [hs, localX_adjoint]
      _ = localX i * localXSupport s := by
              simpa [localXSupport_singleton] using
                (localXSupport_commute s ({i} : Finset ι))
      _ = localXSupport (insert i s) := by
              rw [localXSupport_insert s his]

/-- Support-level `Z` operators are self-adjoint. -/
theorem localZSupport_adjoint (s : Finset ι) :
    LinearMap.adjoint (localZSupport s) = localZSupport s := by
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his hs
    calc
      LinearMap.adjoint (localZSupport (insert i s))
          = LinearMap.adjoint (localZ i * localZSupport s) := by
              rw [localZSupport_insert s his]
      _ = LinearMap.adjoint (localZSupport s) * LinearMap.adjoint (localZ i) := by
              simp [Module.End.mul_eq_comp]
      _ = localZSupport s * localZ i := by
              rw [hs, localZ_adjoint]
      _ = localZ i * localZSupport s := by
              simpa [localZSupport_singleton] using
                (localZSupport_commute s ({i} : Finset ι))
      _ = localZSupport (insert i s) := by
              rw [localZSupport_insert s his]

end Qubit
end Semantics

namespace Coding

open Classical
open scoped BigOperators

universe u w

namespace PauliSymplectic

variable {ι : Type u} [Fintype ι]

/-- The support of a binary word, i.e. the coordinates whose `ZMod 2` bit is one. -/
def binarySupport (x : Word (ZMod 2) ι) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 0

@[simp] theorem mem_binarySupport (x : Word (ZMod 2) ι) (i : ι) :
    i ∈ binarySupport x ↔ x i ≠ 0 := by
  simp [binarySupport]

@[simp] theorem binarySupport_zero :
    binarySupport (0 : Word (ZMod 2) ι) = ∅ := by
  ext i
  simp [binarySupport]

private theorem zmod_two_add_ne_zero_iff (a b : ZMod 2) :
    a + b ≠ 0 ↔ (a ≠ 0 ∧ ¬ b ≠ 0) ∨ (¬ a ≠ 0 ∧ b ≠ 0) := by
  revert a b
  decide

/-- Binary support addition is symmetric difference, stated coordinatewise. -/
theorem mem_binarySupport_add (x y : Word (ZMod 2) ι) (i : ι) :
    i ∈ binarySupport (x + y) ↔
      (i ∈ binarySupport x ∧ i ∉ binarySupport y) ∨
        (i ∉ binarySupport x ∧ i ∈ binarySupport y) := by
  simpa [binarySupport] using zmod_two_add_ne_zero_iff (x i) (y i)

/-- Binary global phase convention: `0` means `+1`, and `1` means `-1`. -/
def binaryPhaseScalar (p : ZMod 2) : Complex :=
  if p = 0 then 1 else -1

@[simp] theorem binaryPhaseScalar_zero : binaryPhaseScalar 0 = 1 := by
  simp [binaryPhaseScalar]

@[simp] theorem binaryPhaseScalar_one : binaryPhaseScalar 1 = -1 := by
  norm_num [binaryPhaseScalar]

theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · contradiction
  · rfl

theorem binaryPhaseScalar_add (a b : ZMod 2) :
    binaryPhaseScalar (a + b) = binaryPhaseScalar a * binaryPhaseScalar b := by
  by_cases ha : a = 0
  · subst a
    simp [binaryPhaseScalar]
  · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
    subst a
    by_cases hb : b = 0
    · subst b
      simp [binaryPhaseScalar]
    · have hb1 : b = 1 := zmod_two_eq_one_of_ne_zero hb
      subst b
      have hone : (1 : ZMod 2) + 1 = 0 := by decide
      simp [binaryPhaseScalar, hone]

theorem binaryPhaseScalar_sum {α : Type u} (s : Finset α) (f : α → ZMod 2) :
    binaryPhaseScalar (Finset.sum s f) =
      Finset.prod s (fun i => binaryPhaseScalar (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp [binaryPhaseScalar]
  · intro a s ha hs
    simp [ha, hs, binaryPhaseScalar_add]

/-- The binary phase scalar is `1` exactly on the zero phase bit. -/
theorem binaryPhaseScalar_eq_one_iff (p : ZMod 2) :
    binaryPhaseScalar p = 1 ↔ p = 0 := by
  fin_cases p <;> norm_num [binaryPhaseScalar]

theorem binaryPhaseScalar_eq_neg_of_add_ne_zero (a b : ZMod 2)
    (h : a + b ≠ 0) :
    binaryPhaseScalar a = -binaryPhaseScalar b := by
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by
      intro hb
      exact h (by simp [hb])
    have hb1 : b = 1 := zmod_two_eq_one_of_ne_zero hb
    subst b
    simp [binaryPhaseScalar]
  · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
    subst a
    by_cases hb : b = 0
    · subst b
      simp [binaryPhaseScalar]
    · have hb1 : b = 1 := zmod_two_eq_one_of_ne_zero hb
      subst b
      have hsum : (1 : ZMod 2) + 1 = 0 := by decide
      exact False.elim (h hsum)

private theorem finTwo_to_zmodTwo_to_fin (b : Fin 2) :
    (if (b : ZMod 2) = 0 then (0 : Fin 2) else 1) = b := by
  fin_cases b
  · change (if (((0 : Fin 2) : ZMod 2) = 0) then (0 : Fin 2) else 1) = 0
    simp
  · have h : (((1 : Fin 2) : ZMod 2) ≠ 0) := by decide
    change (if (((1 : Fin 2) : ZMod 2) = 0) then (0 : Fin 2) else 1) = 1
    simp [h]

private theorem zmodTwo_to_finTwo_to_zmod (a : ZMod 2) :
    (((if a = 0 then (0 : Fin 2) else 1) : Fin 2) : ZMod 2) = a := by
  fin_cases a
  · change (((if (0 : ZMod 2) = 0 then (0 : Fin 2) else 1) : Fin 2) : ZMod 2) = 0
    simp
  · have h : (1 : ZMod 2) ≠ 0 := by decide
    change (((if (1 : ZMod 2) = 0 then (0 : Fin 2) else 1) : Fin 2) : ZMod 2) = 1
    simp [h]

private theorem finTwo_flipBit_to_zmodTwo (b : Fin 2) :
    ((Semantics.Qubit.flipBit b : Fin 2) : ZMod 2) = (b : ZMod 2) + 1 := by
  fin_cases b
  · change ((Semantics.Qubit.flipBit (0 : Fin 2) : Fin 2) : ZMod 2) =
      ((0 : Fin 2) : ZMod 2) + 1
    norm_num [Semantics.Qubit.flipBit]
  · have h : ((1 : Fin 2) : ZMod 2) + 1 = 0 := by decide
    change ((Semantics.Qubit.flipBit (1 : Fin 2) : Fin 2) : ZMod 2) =
      ((1 : Fin 2) : ZMod 2) + 1
    rw [h]
    norm_num [Semantics.Qubit.flipBit]

private theorem zPhase_eq_binaryPhaseScalar_finTwo (b : Fin 2) :
    Semantics.Qubit.zPhase b = binaryPhaseScalar (b : ZMod 2) := by
  fin_cases b
  · change (1 : Complex) = binaryPhaseScalar (0 : ZMod 2)
    exact binaryPhaseScalar_zero.symm
  · change (-1 : Complex) = binaryPhaseScalar (1 : ZMod 2)
    exact binaryPhaseScalar_one.symm

/--
Coordinatewise equivalence between computational-basis bitstrings and binary
words. The inverse sends the unique nonzero binary field element to bit `1`.
-/
noncomputable def bitstringWordEquiv (ι : Type u) [Fintype ι] :
    Semantics.Qubit.Bitstring ι ≃ Word (ZMod 2) ι where
  toFun bits := fun i => (bits i : ZMod 2)
  invFun x := fun i => if x i = 0 then 0 else 1
  left_inv := by
    intro bits
    funext i
    exact finTwo_to_zmodTwo_to_fin (bits i)
  right_inv := by
    intro x
    funext i
    exact zmodTwo_to_finTwo_to_zmod (x i)

@[simp] theorem bitstringWordEquiv_apply
    (bits : Semantics.Qubit.Bitstring ι) (i : ι) :
    bitstringWordEquiv ι bits i = (bits i : ZMod 2) :=
  rfl

/--
Flipping the support of a binary word is the same computational-basis action as
adding that word after converting the bitstring to a binary word.
-/
theorem bitstringWordEquiv_flipSupport [DecidableEq ι]
    (x : Word (ZMod 2) ι) (bits : Semantics.Qubit.Bitstring ι) :
    bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) =
      bitstringWordEquiv ι bits + x := by
  funext i
  simp only [Pi.add_apply, bitstringWordEquiv_apply, Semantics.Qubit.flipSupport]
  by_cases hxi : x i = 0
  · have hi : i ∉ binarySupport x := by simp [binarySupport, hxi]
    rw [if_neg hi, hxi]
    exact (@add_zero (ZMod 2) _ (bits i)).symm
  · have hxi_one : x i = 1 := zmod_two_eq_one_of_ne_zero hxi
    have hi : i ∈ binarySupport x := by
      simp [binarySupport, hxi_one]
    rw [if_pos hi, hxi_one]
    exact finTwo_flipBit_to_zmodTwo (bits i)

/--
The support-level `Z` phase is the binary phase scalar of the dot product with
the converted computational-basis word.
-/
theorem zSupportPhase_eq_binaryPhaseScalar_wordPairing
    (z : Word (ZMod 2) ι) (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport z) bits =
      binaryPhaseScalar
        (wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits)) := by
  rw [Semantics.Qubit.zSupportPhase, binarySupport, wordPairing_apply, dotProduct]
  rw [Finset.prod_filter, binaryPhaseScalar_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hzi : z i = 0
  · rw [hzi, zero_mul, binaryPhaseScalar_zero]
    simp
  · have hzi_one : z i = 1 := zmod_two_eq_one_of_ne_zero hzi
    calc
      (if z i ≠ 0 then Semantics.Qubit.zPhase (bits i) else 1) =
          Semantics.Qubit.zPhase (bits i) := by
            simp [hzi]
      _ = binaryPhaseScalar (bitstringWordEquiv ι bits i) :=
            zPhase_eq_binaryPhaseScalar_finTwo (bits i)
      _ = binaryPhaseScalar (z i * bitstringWordEquiv ι bits i) := by
            rw [hzi_one, one_mul]

/--
A binary `Z` support fixes a computational basis label exactly when the binary
word pairing with that label is zero.
-/
theorem zSupportPhase_eq_one_iff_wordPairing_eq_zero [DecidableEq ι]
    (z : Word (ZMod 2) ι) (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport z) bits = 1 ↔
      wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits) = 0 := by
  rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing]
  exact binaryPhaseScalar_eq_one_iff _

variable [DecidableEq ι]

/-- Binary Pauli-symplectic coordinates. -/
abbrev Binary (ι : Type u) [Fintype ι] :=
  PauliSymplectic (ZMod 2) ι

/-- Binary Pauli coordinates are equivalent to a finite phase/X/Z tuple. -/
noncomputable def binaryEquivPhaseXPartZPart :
    Binary ι ≃ ZMod 2 × Word (ZMod 2) ι × Word (ZMod 2) ι where
  toFun P := (P.phase, P.vector.xPart, P.vector.zPart)
  invFun p := { phase := p.1, vector := { xPart := p.2.1, zPart := p.2.2 } }
  left_inv := by
    intro P
    rcases P with ⟨phase, vector⟩
    rcases vector with ⟨x, z⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨phase, x, z⟩
    rfl

noncomputable instance instFintypeBinary : Fintype (Binary ι) :=
  Fintype.ofEquiv (ZMod 2 × Word (ZMod 2) ι × Word (ZMod 2) ι)
    (binaryEquivPhaseXPartZPart (ι := ι)).symm

/-- Binary CSS `X` check: an `X` word with zero `Z` component and trivial phase. -/
abbrev cssXCheck (x : Word (ZMod 2) ι) : Binary ι :=
  { phase := 0, vector := { xPart := x, zPart := 0 } }

/-- Binary CSS `Z` check: a `Z` word with zero `X` component and trivial phase. -/
abbrev cssZCheck (z : Word (ZMod 2) ι) : Binary ι :=
  { phase := 0, vector := { xPart := 0, zPart := z } }

/-- The scoped binary CSS stabilizer checks generated by X/Z classical codewords. -/
def binaryCSSCheckSet (xCode zCode : LinearCode (ZMod 2) ι) : Set (Binary ι) :=
  {P | (∃ x, x ∈ xCode.carrier ∧ P = cssXCheck x) ∨
       (∃ z, z ∈ zCode.carrier ∧ P = cssZCheck z)}

/-- The `X` support of a binary Pauli-symplectic representative. -/
def xSupport (P : Binary ι) : Finset ι :=
  binarySupport P.vector.xPart

/-- The `Z` support of a binary Pauli-symplectic representative. -/
def zSupport (P : Binary ι) : Finset ι :=
  binarySupport P.vector.zPart

/-- The total coordinate support of a binary Pauli-symplectic representative. -/
def support (P : Binary ι) : Finset ι :=
  xSupport P ∪ zSupport P

@[simp] theorem mem_support (P : Binary ι) (i : ι) :
    i ∈ support P ↔ i ∈ xSupport P ∨ i ∈ zSupport P := by
  simp [support]

/-- The binary Pauli weight is the size of its total X/Z coordinate support. -/
def weight (P : Binary ι) : Nat :=
  (support P).card

/-- The identity binary Pauli representative. -/
def binaryOne : Binary ι :=
  { phase := 0, vector := { xPart := 0, zPart := 0 } }

@[simp] theorem support_binaryOne :
    support (binaryOne (ι := ι)) = ∅ := by
  ext i
  simp [binaryOne, support, xSupport, zSupport, binarySupport]

@[simp] theorem weight_binaryOne :
    weight (binaryOne (ι := ι)) = 0 := by
  simp [weight]

/-- Finite binary Pauli representatives whose total support has size at most `B`. -/
def scopedByWeightFinset (B : Nat) : Finset (Binary ι) :=
  Finset.univ.filter fun P => weight P ≤ B

/-- Binary Pauli representatives scoped by a total-support weight bound. -/
def scopedByWeight (B : Nat) : Set (Binary ι) :=
  {P | P ∈ scopedByWeightFinset (ι := ι) B}

@[simp] theorem mem_scopedByWeight (B : Nat) (P : Binary ι) :
    P ∈ scopedByWeight (ι := ι) B ↔ weight P ≤ B := by
  simp [scopedByWeight, scopedByWeightFinset]

@[simp] theorem support_cssXCheck (x : Word (ZMod 2) ι) :
    support (cssXCheck x) = hammingSupport x := by
  ext i
  simp [support, xSupport, zSupport, binarySupport, hammingSupport]

@[simp] theorem support_cssZCheck (z : Word (ZMod 2) ι) :
    support (cssZCheck z) = hammingSupport z := by
  ext i
  simp [support, xSupport, zSupport, binarySupport, hammingSupport]

@[simp] theorem weight_cssXCheck_eq_hammingWeight (x : Word (ZMod 2) ι) :
    weight (cssXCheck x) = HammingWeight x := by
  simp [weight, HammingWeight]

@[simp] theorem weight_cssZCheck_eq_hammingWeight (z : Word (ZMod 2) ι) :
    weight (cssZCheck z) = HammingWeight z := by
  simp [weight, HammingWeight]

/-- The `X` coordinate Hamming weight is bounded by total binary Pauli weight. -/
theorem hammingWeight_xPart_le_weight (P : Binary ι) :
    HammingWeight P.vector.xPart ≤ weight P := by
  calc
    HammingWeight P.vector.xPart = (xSupport P).card := by
      simp [HammingWeight, hammingSupport, xSupport, binarySupport]
    _ ≤ (support P).card :=
      Finset.card_le_card (by
        intro i hi
        exact (mem_support P i).2 (Or.inl hi))
    _ = weight P := rfl

/-- The `Z` coordinate Hamming weight is bounded by total binary Pauli weight. -/
theorem hammingWeight_zPart_le_weight (P : Binary ι) :
    HammingWeight P.vector.zPart ≤ weight P := by
  calc
    HammingWeight P.vector.zPart = (zSupport P).card := by
      simp [HammingWeight, hammingSupport, zSupport, binarySupport]
    _ ≤ (support P).card :=
      Finset.card_le_card (by
        intro i hi
        exact (mem_support P i).2 (Or.inr hi))
    _ = weight P := rfl

/-- The support-overlap phase from moving the `Z` word past the `X` word. -/
def binarySwapPhase (x z : Word (ZMod 2) ι) : Complex :=
  Semantics.Qubit.supportPhaseSign (binarySupport x) (binarySupport z)

@[simp] theorem binaryPhaseScalar_star (p : ZMod 2) :
    star (binaryPhaseScalar p) = binaryPhaseScalar p := by
  by_cases hp : p = 0
  · simp [binaryPhaseScalar, hp]
  · have hp1 : p = 1 := zmod_two_eq_one_of_ne_zero hp
    subst p
    norm_num [binaryPhaseScalar]

/-- The phase bit convention for multiplying binary Pauli representatives. -/
def binaryMulPhase (P Q : Binary ι) : ZMod 2 :=
  P.phase + Q.phase + Finset.sum Finset.univ (fun i => Q.vector.xPart i * P.vector.zPart i)

/-- Binary Pauli multiplication in the fixed `phase * X * Z` convention. -/
def binaryMul (P Q : Binary ι) : Binary ι :=
  { phase := binaryMulPhase P Q
    vector := { xPart := P.vector.xPart + Q.vector.xPart
                zPart := P.vector.zPart + Q.vector.zPart } }

omit [DecidableEq ι] in
@[simp] theorem binaryMul_cssXCheck (x y : Word (ZMod 2) ι) :
    binaryMul (cssXCheck x) (cssXCheck y) = cssXCheck (x + y) := by
  simp [binaryMul, binaryMulPhase]

omit [DecidableEq ι] in
@[simp] theorem binaryMul_cssZCheck (z w : Word (ZMod 2) ι) :
    binaryMul (cssZCheck z) (cssZCheck w) = cssZCheck (z + w) := by
  simp [binaryMul, binaryMulPhase]

/-- The phase bit convention for the adjoint/inverse binary Pauli representative. -/
def binaryDaggerPhase (P : Binary ι) : ZMod 2 :=
  P.phase + Finset.sum Finset.univ (fun i => P.vector.xPart i * P.vector.zPart i)

/-- Binary Pauli adjoint representative in the fixed `phase * X * Z` convention. -/
def binaryDagger (P : Binary ι) : Binary ι :=
  { phase := binaryDaggerPhase P
    vector := P.vector }

omit [DecidableEq ι] in
@[simp] theorem binaryDagger_binaryOne :
    binaryDagger (binaryOne (ι := ι)) = binaryOne := by
  simp [binaryDagger, binaryDaggerPhase, binaryOne]

omit [DecidableEq ι] in
@[simp] theorem binaryDagger_cssXCheck (x : Word (ZMod 2) ι) :
    binaryDagger (cssXCheck x) = cssXCheck x := by
  simp [binaryDagger, binaryDaggerPhase, cssXCheck]

omit [DecidableEq ι] in
@[simp] theorem binaryDagger_cssZCheck (z : Word (ZMod 2) ι) :
    binaryDagger (cssZCheck z) = cssZCheck z := by
  simp [binaryDagger, binaryDaggerPhase, cssZCheck]

omit [DecidableEq ι] in
@[simp] theorem binaryMul_binaryOne_left (P : Binary ι) :
    binaryMul (binaryOne (ι := ι)) P = P := by
  rcases P with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  simp [binaryMul, binaryMulPhase, binaryOne]

omit [DecidableEq ι] in
@[simp] theorem binaryMul_binaryOne_right (P : Binary ι) :
    binaryMul P (binaryOne (ι := ι)) = P := by
  rcases P with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  simp [binaryMul, binaryMulPhase, binaryOne]

omit [DecidableEq ι] in
@[simp] theorem binaryMul_binaryDagger_left (P : Binary ι) :
    binaryMul (binaryDagger P) P = binaryOne := by
  rcases P with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  have hbit_add_self (a : ZMod 2) : a + a = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
      subst a
      decide
  simp [binaryMul, binaryMulPhase, binaryDagger, binaryDaggerPhase, binaryOne]
  constructor
  · let s : ZMod 2 := ∑ i, x i * z i
    change phase + s + phase + s = 0
    calc
      phase + s + phase + s = (phase + phase) + (s + s) := by abel
      _ = 0 := by simp [hbit_add_self]
  constructor
  · funext i
    exact hbit_add_self (x i)
  · funext i
    exact hbit_add_self (z i)

theorem binaryPhaseScalar_mul_eq_supportFactor (x z : Word (ZMod 2) ι) (i : ι) :
    binaryPhaseScalar (x i * z i) =
      (if i ∈ binarySupport z then
        if i ∈ binarySupport x then (-1 : Complex) else 1
      else 1) := by
  by_cases hx0 : x i = 0
  · simp [binaryPhaseScalar, binarySupport, hx0]
  · have hx1 : x i = 1 := zmod_two_eq_one_of_ne_zero hx0
    by_cases hz0 : z i = 0
    · simp [binaryPhaseScalar, binarySupport, hx1, hz0]
    · have hz1 : z i = 1 := zmod_two_eq_one_of_ne_zero hz0
      simp [binaryPhaseScalar, binarySupport, hx1, hz1]

theorem binarySwapPhase_eq_binaryPhaseScalar_sum_mul (x z : Word (ZMod 2) ι) :
    binarySwapPhase x z =
      binaryPhaseScalar (Finset.sum Finset.univ fun i => x i * z i) := by
  rw [binarySwapPhase, Semantics.Qubit.supportPhaseSign, binaryPhaseScalar_sum]
  rw [binarySupport]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _hi
  simpa [binarySupport] using (binaryPhaseScalar_mul_eq_supportFactor x z i).symm

theorem binaryPhaseScalar_binaryMulPhase (P Q : Binary ι) :
    binaryPhaseScalar (binaryMulPhase P Q) =
      binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
        binarySwapPhase Q.vector.xPart P.vector.zPart := by
  simp [binaryMulPhase, binaryPhaseScalar_add,
    binarySwapPhase_eq_binaryPhaseScalar_sum_mul, mul_assoc]

theorem binaryPhaseScalar_binaryDaggerPhase (P : Binary ι) :
    binaryPhaseScalar (binaryDaggerPhase P) =
      binaryPhaseScalar P.phase * binarySwapPhase P.vector.xPart P.vector.zPart := by
  simp [binaryDaggerPhase, binaryPhaseScalar_add,
    binarySwapPhase_eq_binaryPhaseScalar_sum_mul]

theorem localXSupport_binarySupport_add (x y : Word (ZMod 2) ι) :
    Semantics.Qubit.localXSupport (binarySupport (x + y)) =
      Semantics.Qubit.localXSupport (binarySupport x) *
        Semantics.Qubit.localXSupport (binarySupport y) := by
  ext ψ bits
  simp [Module.End.mul_apply]
  apply congrArg (fun bits' => ψ bits')
  funext i
  by_cases hxi : x i = 0
  · by_cases hyi : y i = 0
    · simp [Semantics.Qubit.flipSupport, binarySupport, hxi, hyi]
    · have hyi1 : y i = 1 := zmod_two_eq_one_of_ne_zero hyi
      simp [Semantics.Qubit.flipSupport, binarySupport, hxi, hyi1]
  · have hxi1 : x i = 1 := zmod_two_eq_one_of_ne_zero hxi
    by_cases hyi : y i = 0
    · simp [Semantics.Qubit.flipSupport, binarySupport, hxi1, hyi]
    · have hyi1 : y i = 1 := zmod_two_eq_one_of_ne_zero hyi
      have hsum : (1 : ZMod 2) + 1 = 0 := by decide
      simp [Semantics.Qubit.flipSupport, binarySupport, hxi1, hyi1, hsum]

omit [DecidableEq ι] in
theorem zSupportPhase_binarySupport_add (x y : Word (ZMod 2) ι)
    (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport (x + y)) bits =
      Semantics.Qubit.zSupportPhase (binarySupport x) bits *
        Semantics.Qubit.zSupportPhase (binarySupport y) bits := by
  simp only [Semantics.Qubit.zSupportPhase, binarySupport]
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hxi : x i = 0
  · by_cases hyi : y i = 0
    · simp [hxi, hyi]
    · have hyi1 : y i = 1 := zmod_two_eq_one_of_ne_zero hyi
      simp [hxi, hyi1]
  · have hxi1 : x i = 1 := zmod_two_eq_one_of_ne_zero hxi
    by_cases hyi : y i = 0
    · simp [hxi1, hyi]
    · have hyi1 : y i = 1 := zmod_two_eq_one_of_ne_zero hyi
      have hsum : (1 : ZMod 2) + 1 = 0 := by decide
      simp [hxi1, hyi1, hsum, Semantics.Qubit.zPhase_sq]

theorem localZSupport_binarySupport_add (x y : Word (ZMod 2) ι) :
    Semantics.Qubit.localZSupport (binarySupport (x + y)) =
      Semantics.Qubit.localZSupport (binarySupport x) *
        Semantics.Qubit.localZSupport (binarySupport y) := by
  ext ψ bits
  simp [Module.End.mul_apply, zSupportPhase_binarySupport_add, mul_assoc]

theorem support_binaryMul_subset (P Q : Binary ι) :
    support (binaryMul P Q) ⊆ support P ∪ support Q := by
  intro i hi
  rw [mem_support] at hi
  rw [Finset.mem_union]
  rcases hi with hix | hiz
  · have hxs := (mem_binarySupport_add P.vector.xPart Q.vector.xPart i).1
      (by simpa [binaryMul, xSupport] using hix)
    rcases hxs with ⟨hP, _hQ⟩ | ⟨_hP, hQ⟩
    · left
      exact (mem_support P i).2 (Or.inl hP)
    · right
      exact (mem_support Q i).2 (Or.inl hQ)
  · have hzs := (mem_binarySupport_add P.vector.zPart Q.vector.zPart i).1
      (by simpa [binaryMul, zSupport] using hiz)
    rcases hzs with ⟨hP, _hQ⟩ | ⟨_hP, hQ⟩
    · left
      exact (mem_support P i).2 (Or.inr hP)
    · right
      exact (mem_support Q i).2 (Or.inr hQ)

theorem weight_binaryMul_le (P Q : Binary ι) :
    weight (binaryMul P Q) ≤ weight P + weight Q := by
  calc
    weight (binaryMul P Q) = (support (binaryMul P Q)).card := rfl
    _ ≤ (support P ∪ support Q).card :=
      Finset.card_le_card (support_binaryMul_subset P Q)
    _ ≤ (support P).card + (support Q).card :=
      Finset.card_union_le (support P) (support Q)
    _ = weight P + weight Q := rfl

theorem support_mul_subset (P Q : Binary ι) :
    support (binaryMul P Q) ⊆ support P ∪ support Q :=
  support_binaryMul_subset P Q

theorem weight_mul_le (P Q : Binary ι) :
    weight (binaryMul P Q) ≤ weight P + weight Q :=
  weight_binaryMul_le P Q

@[simp] theorem support_binaryDagger (P : Binary ι) :
    support (binaryDagger P) = support P := by
  rfl

@[simp] theorem weight_binaryDagger (P : Binary ι) :
    weight (binaryDagger P) = weight P := by
  rfl

theorem support_dagger (P : Binary ι) :
    support (binaryDagger P) = support P :=
  support_binaryDagger P

theorem weight_dagger (P : Binary ι) :
    weight (binaryDagger P) = weight P :=
  weight_binaryDagger P

theorem mem_scopedByWeight_binaryMul {B C : Nat} {P Q : Binary ι}
    (hP : P ∈ scopedByWeight (ι := ι) B)
    (hQ : Q ∈ scopedByWeight (ι := ι) C) :
    binaryMul P Q ∈ scopedByWeight (ι := ι) (B + C) := by
  rw [mem_scopedByWeight] at hP hQ ⊢
  exact le_trans (weight_binaryMul_le P Q) (Nat.add_le_add hP hQ)

theorem mem_scopedByWeight_binaryDagger {B : Nat} {P : Binary ι}
    (hP : P ∈ scopedByWeight (ι := ι) B) :
    binaryDagger P ∈ scopedByWeight (ι := ι) B := by
  simpa using hP

/--
Interpret binary Pauli-symplectic coordinates as concrete qubit-register
operators in the convention `phase * X(xSupport) * Z(zSupport)`.
-/
def toQubitOperator (P : Binary ι) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  binaryPhaseScalar P.phase •
    (Semantics.Qubit.localXSupport (xSupport P) *
      Semantics.Qubit.localZSupport (zSupport P))

@[simp] theorem toQubitOperator_apply (P : Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι) (bits : Semantics.Qubit.Bitstring ι) :
    toQubitOperator P ψ bits =
      binaryPhaseScalar P.phase *
        (Semantics.Qubit.zSupportPhase (zSupport P)
          (Semantics.Qubit.flipSupport (xSupport P) bits) *
            ψ (Semantics.Qubit.flipSupport (xSupport P) bits)) := by
  simp [toQubitOperator, Module.End.mul_apply, smul_eq_mul]

/-- Semantic operators represented by binary Paulis with total support at most `B`. -/
def scopedErrorOperators (B : Nat) :
    Set (Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :=
  Set.image toQubitOperator (scopedByWeight (ι := ι) B)

theorem mem_scopedErrorOperators_iff (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ scopedErrorOperators (ι := ι) B ↔
      ∃ P : Binary ι, P ∈ scopedByWeight (ι := ι) B ∧ toQubitOperator P = E := by
  rfl

/-- The finite same-space Kraus family indexed by scoped binary Paulis. -/
noncomputable def scopedErrorFamily (B : Nat) :
    Semantics.FiniteKrausFamily {P : Binary ι // P ∈ scopedByWeight (ι := ι) B}
      (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι) where
  operator P := toQubitOperator P.1

theorem scopedErrorFamily_sameSpaceErrorSet (B : Nat) :
    (scopedErrorFamily (ι := ι) B).sameSpaceErrorSet =
      scopedErrorOperators (ι := ι) B := by
  ext E
  constructor
  · intro hE
    rcases ((scopedErrorFamily (ι := ι) B).mem_sameSpaceErrorSet_iff E).1 hE with
      ⟨P, hP⟩
    exact ⟨P.1, P.2, by simpa [scopedErrorFamily] using hP⟩
  · rintro ⟨P, hP, rfl⟩
    exact ((scopedErrorFamily (ι := ι) B).mem_sameSpaceErrorSet_iff
      (toQubitOperator P)).2 ⟨⟨P, hP⟩, by simp [scopedErrorFamily]⟩

theorem mem_scopedErrorFamily_sameSpaceErrorSet_iff (B : Nat)
    (E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :
    E ∈ (scopedErrorFamily (ι := ι) B).sameSpaceErrorSet ↔
      E ∈ scopedErrorOperators (ι := ι) B := by
  rw [scopedErrorFamily_sameSpaceErrorSet]

theorem toQubitOperator_one :
    toQubitOperator (binaryOne (ι := ι)) = 1 := by
  ext ψ bits
  simp [toQubitOperator, binaryOne, xSupport, zSupport]

/-- If a binary Pauli has no X/Z support, its semantic operator is only its global phase. -/
theorem toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
    {P : Binary ι}
    (hx : P.vector.xPart = 0)
    (hz : P.vector.zPart = 0) :
    toQubitOperator P =
      binaryPhaseScalar P.phase •
        (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) := by
  ext ψ bits
  simp [toQubitOperator, xSupport, zSupport, hx, hz]

/-- The binary support phase for moving a concrete `Z` support past a concrete `X` support. -/
theorem zSupport_mul_xSupport_phase (z x : Word (ZMod 2) ι) :
    Semantics.Qubit.localZSupport (binarySupport z) *
        Semantics.Qubit.localXSupport (binarySupport x) =
      binarySwapPhase x z •
        (Semantics.Qubit.localXSupport (binarySupport x) *
          Semantics.Qubit.localZSupport (binarySupport z)) := by
  simpa [binarySwapPhase] using
    (Semantics.Qubit.localZSupport_localXSupport_phase
      (xSupport := binarySupport x) (zSupport := binarySupport z))

/--
Normal-order product relation for binary support-level Paulis:
`(X x1 * Z z1) * (X x2 * Z z2)` is `X x1 * X x2 * Z z1 * Z z2`
with exactly the phase obtained by moving `z1` past `x2`.
-/
theorem xzSupport_mul_xzSupport_normal_order
    (x1 z1 x2 z2 : Word (ZMod 2) ι) :
    ((Semantics.Qubit.localXSupport (binarySupport x1) *
          Semantics.Qubit.localZSupport (binarySupport z1)) *
        (Semantics.Qubit.localXSupport (binarySupport x2) *
          Semantics.Qubit.localZSupport (binarySupport z2))) =
      binarySwapPhase x2 z1 •
        ((Semantics.Qubit.localXSupport (binarySupport x1) *
            Semantics.Qubit.localXSupport (binarySupport x2)) *
          (Semantics.Qubit.localZSupport (binarySupport z1) *
            Semantics.Qubit.localZSupport (binarySupport z2))) := by
  calc
    ((Semantics.Qubit.localXSupport (binarySupport x1) *
          Semantics.Qubit.localZSupport (binarySupport z1)) *
        (Semantics.Qubit.localXSupport (binarySupport x2) *
          Semantics.Qubit.localZSupport (binarySupport z2)))
        = Semantics.Qubit.localXSupport (binarySupport x1) *
            (Semantics.Qubit.localZSupport (binarySupport z1) *
              Semantics.Qubit.localXSupport (binarySupport x2)) *
              Semantics.Qubit.localZSupport (binarySupport z2) := by
          simp [mul_assoc]
    _ = Semantics.Qubit.localXSupport (binarySupport x1) *
          (binarySwapPhase x2 z1 •
            (Semantics.Qubit.localXSupport (binarySupport x2) *
              Semantics.Qubit.localZSupport (binarySupport z1))) *
            Semantics.Qubit.localZSupport (binarySupport z2) := by
          rw [show
            Semantics.Qubit.localZSupport (binarySupport z1) *
                Semantics.Qubit.localXSupport (binarySupport x2) =
              binarySwapPhase x2 z1 •
                (Semantics.Qubit.localXSupport (binarySupport x2) *
                  Semantics.Qubit.localZSupport (binarySupport z1)) from by
            simpa [binarySwapPhase] using
              (Semantics.Qubit.localZSupport_localXSupport_phase
                (xSupport := binarySupport x2) (zSupport := binarySupport z1))]
    _ = binarySwapPhase x2 z1 •
        ((Semantics.Qubit.localXSupport (binarySupport x1) *
            Semantics.Qubit.localXSupport (binarySupport x2)) *
          (Semantics.Qubit.localZSupport (binarySupport z1) *
            Semantics.Qubit.localZSupport (binarySupport z2))) := by
          simp [mul_assoc]

/-- Raw product expansion for interpreted binary Pauli-symplectic representatives. -/
theorem toQubitOperator_mul_expand (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q =
      (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localZSupport (zSupport P)) *
          (Semantics.Qubit.localXSupport (xSupport Q) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by
  simp [toQubitOperator, smul_smul, mul_assoc, mul_comm]

/--
Downstream-facing product/phase bridge for binary Pauli-symplectic
representatives. This is the operator-level fact consumed before proving a
commutation theorem: the only nontrivial product phase is the support-overlap
sign from moving `P`'s `Z` support past `Q`'s `X` support.
-/
theorem toQubitOperator_mul_normal_order (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q =
      (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase Q.vector.xPart P.vector.zPart) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localXSupport (xSupport Q)) *
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by
  calc
    toQubitOperator P * toQubitOperator Q =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase) •
          ((Semantics.Qubit.localXSupport (xSupport P) *
              Semantics.Qubit.localZSupport (zSupport P)) *
            (Semantics.Qubit.localXSupport (xSupport Q) *
              Semantics.Qubit.localZSupport (zSupport Q))) :=
      toQubitOperator_mul_expand P Q
    _ = (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase) •
          (binarySwapPhase Q.vector.xPart P.vector.zPart •
            ((Semantics.Qubit.localXSupport (xSupport P) *
                Semantics.Qubit.localXSupport (xSupport Q)) *
              (Semantics.Qubit.localZSupport (zSupport P) *
                Semantics.Qubit.localZSupport (zSupport Q)))) := by
      rw [show
        ((Semantics.Qubit.localXSupport (xSupport P) *
              Semantics.Qubit.localZSupport (zSupport P)) *
            (Semantics.Qubit.localXSupport (xSupport Q) *
              Semantics.Qubit.localZSupport (zSupport Q))) =
          binarySwapPhase Q.vector.xPart P.vector.zPart •
            ((Semantics.Qubit.localXSupport (xSupport P) *
                Semantics.Qubit.localXSupport (xSupport Q)) *
              (Semantics.Qubit.localZSupport (zSupport P) *
                Semantics.Qubit.localZSupport (zSupport Q))) from by
        simpa [xSupport, zSupport] using
          (xzSupport_mul_xzSupport_normal_order
            (x1 := P.vector.xPart) (z1 := P.vector.zPart)
            (x2 := Q.vector.xPart) (z2 := Q.vector.zPart))]
    _ = (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase Q.vector.xPart P.vector.zPart) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localXSupport (xSupport Q)) *
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by
      simp [smul_smul, mul_assoc]

/--
The named binary product representative matches concrete qubit-register
operator composition.
-/
theorem toQubitOperator_binaryMul (P Q : Binary ι) :
    toQubitOperator (binaryMul P Q) = toQubitOperator P * toQubitOperator Q := by
  calc
    toQubitOperator (binaryMul P Q) =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase Q.vector.xPart P.vector.zPart) •
          ((Semantics.Qubit.localXSupport (xSupport P) *
              Semantics.Qubit.localXSupport (xSupport Q)) *
            (Semantics.Qubit.localZSupport (zSupport P) *
              Semantics.Qubit.localZSupport (zSupport Q))) := by
          simp [toQubitOperator, binaryMul, xSupport, zSupport,
            binaryPhaseScalar_binaryMulPhase, localXSupport_binarySupport_add,
            localZSupport_binarySupport_add]
    _ = toQubitOperator P * toQubitOperator Q :=
          (toQubitOperator_mul_normal_order P Q).symm

theorem toQubitOperator_mul_binaryMul (P Q : Binary ι) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator (binaryMul P Q) :=
  (toQubitOperator_binaryMul P Q).symm

/--
The named binary dagger representative matches the adjoint of the interpreted
qubit-register operator.
-/
theorem adjoint_toQubitOperator_eq_binaryDagger (P : Binary ι) :
    LinearMap.adjoint (toQubitOperator P) = toQubitOperator (binaryDagger P) := by
  let X := Semantics.Qubit.localXSupport (xSupport P)
  let Z := Semantics.Qubit.localZSupport (zSupport P)
  have hAdjXZ : LinearMap.adjoint (X * Z) = Z * X := by
    simp [X, Z, Module.End.mul_eq_comp, Semantics.Qubit.localXSupport_adjoint,
      Semantics.Qubit.localZSupport_adjoint]
  calc
    LinearMap.adjoint (toQubitOperator P) =
        binaryPhaseScalar P.phase •
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localXSupport (xSupport P)) := by
          calc
            LinearMap.adjoint (toQubitOperator P)
                = star (binaryPhaseScalar P.phase) • LinearMap.adjoint (X * Z) := by
                    change
                      LinearMap.adjoint (binaryPhaseScalar P.phase • (X * Z)) =
                        star (binaryPhaseScalar P.phase) • LinearMap.adjoint (X * Z)
                    exact
                      map_smulₛₗ
                        (LinearMap.adjoint :
                          (Semantics.Operator (Semantics.Qubit.QubitRegister ι)) ≃ₗ⋆[Complex]
                            Semantics.Operator (Semantics.Qubit.QubitRegister ι))
                        (binaryPhaseScalar P.phase) (X * Z)
            _ = binaryPhaseScalar P.phase •
                (Semantics.Qubit.localZSupport (zSupport P) *
                  Semantics.Qubit.localXSupport (xSupport P)) := by
                    simp [hAdjXZ, X, Z]
    _ = binaryPhaseScalar P.phase •
        (binarySwapPhase P.vector.xPart P.vector.zPart •
          (Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localZSupport (zSupport P))) := by
          rw [show
            Semantics.Qubit.localZSupport (zSupport P) *
                Semantics.Qubit.localXSupport (xSupport P) =
              binarySwapPhase P.vector.xPart P.vector.zPart •
                (Semantics.Qubit.localXSupport (xSupport P) *
                  Semantics.Qubit.localZSupport (zSupport P)) from by
            simpa [binarySwapPhase, xSupport, zSupport] using
              (Semantics.Qubit.localZSupport_localXSupport_phase
                (xSupport := binarySupport P.vector.xPart)
                (zSupport := binarySupport P.vector.zPart))]
    _ = toQubitOperator (binaryDagger P) := by
          simp [toQubitOperator, binaryDagger, xSupport, zSupport,
            binaryPhaseScalar_binaryDaggerPhase, smul_smul]

theorem toQubitOperator_binaryDagger (P : Binary ι) :
    toQubitOperator (binaryDagger P) = LinearMap.adjoint (toQubitOperator P) :=
  (adjoint_toQubitOperator_eq_binaryDagger P).symm

/-- Interpreted binary Paulis are normalized at the finite-operator level. -/
theorem toQubitOperator_adjoint_comp_self (P : Binary ι) :
    (LinearMap.adjoint (toQubitOperator P)).comp (toQubitOperator P) = 1 := by
  rw [← toQubitOperator_binaryDagger P]
  change toQubitOperator (binaryDagger P) * toQubitOperator P = 1
  rw [← toQubitOperator_binaryMul (binaryDagger P) P]
  simp [toQubitOperator_one]

/-- Phase-only relative Paulis give the scalar branch of the KL matrix element. -/
theorem matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
    {E F : Binary ι}
    (hx : (binaryMul (binaryDagger E) F).vector.xPart = 0)
    (hz : (binaryMul (binaryDagger E) F).vector.zPart = 0)
    {ψ φ : Semantics.Qubit.QubitRegister ι} :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
      binaryPhaseScalar (binaryMul (binaryDagger E) F).phase * inner Complex ψ φ := by
  let R := binaryMul (binaryDagger E) F
  have hrelInner :
      inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
        inner Complex ψ (toQubitOperator R φ) := by
    calc
      inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
          inner Complex ψ (LinearMap.adjoint (toQubitOperator E) (toQubitOperator F φ)) := by
            simpa using
              (LinearMap.adjoint_inner_right (𝕜 := Complex) (toQubitOperator E) ψ
                (toQubitOperator F φ)).symm
      _ = inner Complex ψ (toQubitOperator (binaryDagger E) (toQubitOperator F φ)) := by
            rw [← toQubitOperator_binaryDagger E]
      _ = inner Complex ψ ((toQubitOperator (binaryDagger E) * toQubitOperator F) φ) := by
            simp [Module.End.mul_apply]
      _ = inner Complex ψ (toQubitOperator R φ) := by
            rw [← toQubitOperator_binaryMul (binaryDagger E) F]
  have hphase :
      toQubitOperator R =
        binaryPhaseScalar R.phase •
          (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :=
    toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
      (P := R) (by simpa [R] using hx) (by simpa [R] using hz)
  calc
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
        inner Complex ψ (toQubitOperator R φ) := hrelInner
    _ = inner Complex ψ
        ((binaryPhaseScalar R.phase •
          (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι))) φ) := by
          rw [hphase]
    _ = binaryPhaseScalar R.phase * inner Complex ψ φ := by
          simp

theorem scopedErrorOperators_mul_mem {B C : Nat}
    {E F : Semantics.Operator (Semantics.Qubit.QubitRegister ι)}
    (hE : E ∈ scopedErrorOperators (ι := ι) B)
    (hF : F ∈ scopedErrorOperators (ι := ι) C) :
    E * F ∈ scopedErrorOperators (ι := ι) (B + C) := by
  rw [mem_scopedErrorOperators_iff] at hE hF ⊢
  rcases hE with ⟨P, hP, rfl⟩
  rcases hF with ⟨Q, hQ, rfl⟩
  exact ⟨binaryMul P Q, mem_scopedByWeight_binaryMul hP hQ, toQubitOperator_binaryMul P Q⟩

theorem scopedErrorOperators_adjoint_mem {B : Nat}
    {E : Semantics.Operator (Semantics.Qubit.QubitRegister ι)}
    (hE : E ∈ scopedErrorOperators (ι := ι) B) :
    LinearMap.adjoint E ∈ scopedErrorOperators (ι := ι) B := by
  rw [mem_scopedErrorOperators_iff] at hE ⊢
  rcases hE with ⟨P, hP, rfl⟩
  exact ⟨binaryDagger P, mem_scopedByWeight_binaryDagger hP, toQubitOperator_binaryDagger P⟩

theorem binarySwapPhase_eq_of_symplecticForm_eq_zero (P Q : Binary ι)
    (h : symplecticForm P.vector Q.vector = 0) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      binarySwapPhase P.vector.xPart Q.vector.zPart := by
  rw [binarySwapPhase_eq_binaryPhaseScalar_sum_mul,
    binarySwapPhase_eq_binaryPhaseScalar_sum_mul]
  apply congrArg binaryPhaseScalar
  have hdot :
      Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) =
        Finset.sum Finset.univ (fun i => P.vector.zPart i * Q.vector.xPart i) := by
    have hsub :
        Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) -
            Finset.sum Finset.univ (fun i => P.vector.zPart i * Q.vector.xPart i) = 0 := by
      simpa [symplecticForm, Finset.sum_sub_distrib] using h
    exact sub_eq_zero.mp hsub
  calc
    Finset.sum Finset.univ (fun i => Q.vector.xPart i * P.vector.zPart i)
        = Finset.sum Finset.univ (fun i => P.vector.zPart i * Q.vector.xPart i) := by
          simp [mul_comm]
    _ = Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) := hdot.symm

theorem binarySwapPhase_eq_of_commutes (P Q : Binary ι)
    (h : Commutes P Q) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      binarySwapPhase P.vector.xPart Q.vector.zPart :=
  binarySwapPhase_eq_of_symplecticForm_eq_zero P Q h

theorem toQubitOperator_commute_of_binarySwapPhase_eq (P Q : Binary ι)
    (hphase :
      binarySwapPhase Q.vector.xPart P.vector.zPart =
        binarySwapPhase P.vector.xPart Q.vector.zPart) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P := by
  let XP := Semantics.Qubit.localXSupport (xSupport P)
  let XQ := Semantics.Qubit.localXSupport (xSupport Q)
  let ZP := Semantics.Qubit.localZSupport (zSupport P)
  let ZQ := Semantics.Qubit.localZSupport (zSupport Q)
  have hxcomm : XP * XQ = XQ * XP := by
    simpa [XP, XQ] using Semantics.Qubit.localXSupport_commute (xSupport P) (xSupport Q)
  have hzcomm : ZP * ZQ = ZQ * ZP := by
    simpa [ZP, ZQ] using Semantics.Qubit.localZSupport_commute (zSupport P) (zSupport Q)
  have hscalar :
      binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase P.vector.xPart Q.vector.zPart =
        binaryPhaseScalar Q.phase * binaryPhaseScalar P.phase *
          binarySwapPhase P.vector.xPart Q.vector.zPart := by
    ring
  calc
    toQubitOperator P * toQubitOperator Q =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase Q.vector.xPart P.vector.zPart) •
          ((XP * XQ) * (ZP * ZQ)) := by
            simpa [XP, XQ, ZP, ZQ] using toQubitOperator_mul_normal_order P Q
    _ = (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase P.vector.xPart Q.vector.zPart) •
          ((XP * XQ) * (ZP * ZQ)) := by
            rw [hphase]
    _ = (binaryPhaseScalar Q.phase * binaryPhaseScalar P.phase *
            binarySwapPhase P.vector.xPart Q.vector.zPart) •
          ((XQ * XP) * (ZQ * ZP)) := by
            rw [hscalar, hxcomm, hzcomm]
    _ = toQubitOperator Q * toQubitOperator P := by
            simpa [XP, XQ, ZP, ZQ] using (toQubitOperator_mul_normal_order Q P).symm

/--
Binary symplectic commutation implies concrete commutation of the interpreted
finite qubit-register Pauli operators.
-/
theorem toQubitOperator_commute_of_commutes (P Q : Binary ι) (h : Commutes P Q) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P :=
  toQubitOperator_commute_of_binarySwapPhase_eq P Q
    (binarySwapPhase_eq_of_commutes P Q h)

theorem binarySwapPhase_eq_neg_of_not_commutes (P Q : Binary ι)
    (h : ¬ Commutes P Q) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      -binarySwapPhase P.vector.xPart Q.vector.zPart := by
  rw [binarySwapPhase_eq_binaryPhaseScalar_sum_mul,
    binarySwapPhase_eq_binaryPhaseScalar_sum_mul]
  apply binaryPhaseScalar_eq_neg_of_add_ne_zero
  have hsymp_ne : symplecticForm P.vector Q.vector ≠ 0 := by
    simpa [Commutes] using h
  have hsymp_eq :
      symplecticForm P.vector Q.vector =
        Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) +
          Finset.sum Finset.univ (fun i => Q.vector.xPart i * P.vector.zPart i) := by
    simp [symplecticForm, CharTwo.sub_eq_add, Finset.sum_add_distrib, mul_comm]
  intro hzero
  apply hsymp_ne
  rw [hsymp_eq]
  simpa [add_comm] using hzero

/--
Binary noncommutation gives concrete anticommutation of the interpreted finite
qubit-register Pauli operators.
-/
theorem toQubitOperator_anticommute_of_not_commutes (P Q : Binary ι)
    (h : ¬ Commutes P Q) :
    toQubitOperator P * toQubitOperator Q = -(toQubitOperator Q * toQubitOperator P) := by
  let XP := Semantics.Qubit.localXSupport (xSupport P)
  let XQ := Semantics.Qubit.localXSupport (xSupport Q)
  let ZP := Semantics.Qubit.localZSupport (zSupport P)
  let ZQ := Semantics.Qubit.localZSupport (zSupport Q)
  have hxcomm : XP * XQ = XQ * XP := by
    simpa [XP, XQ] using Semantics.Qubit.localXSupport_commute (xSupport P) (xSupport Q)
  have hzcomm : ZP * ZQ = ZQ * ZP := by
    simpa [ZP, ZQ] using Semantics.Qubit.localZSupport_commute (zSupport P) (zSupport Q)
  have hswap := binarySwapPhase_eq_neg_of_not_commutes P Q h
  have hscalar :
      binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase Q.vector.xPart P.vector.zPart =
        -(binaryPhaseScalar Q.phase * binaryPhaseScalar P.phase *
          binarySwapPhase P.vector.xPart Q.vector.zPart) := by
    rw [hswap]
    ring
  calc
    toQubitOperator P * toQubitOperator Q =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase Q.vector.xPart P.vector.zPart) •
          ((XP * XQ) * (ZP * ZQ)) := by
            simpa [XP, XQ, ZP, ZQ] using toQubitOperator_mul_normal_order P Q
    _ = -((binaryPhaseScalar Q.phase * binaryPhaseScalar P.phase *
            binarySwapPhase P.vector.xPart Q.vector.zPart) •
          ((XQ * XP) * (ZQ * ZP))) := by
            rw [hscalar, hxcomm, hzcomm]
            simp
    _ = -(toQubitOperator Q * toQubitOperator P) := by
            rw [toQubitOperator_mul_normal_order Q P]

/--
Binary CSS X/Z checks commute as concrete qubit-register operators when their
CSS-shaped symplectic form vanishes.
-/
theorem cssXCheck_toQubitOperator_commute_cssZCheck_of_symplecticForm_eq_zero
    {x z : Word (ZMod 2) ι}
    (h :
      symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
        ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by
  exact toQubitOperator_commute_of_commutes (cssXCheck x) (cssZCheck z) (by
    simpa [cssXCheck, cssZCheck, Commutes] using h)

/--
Binary CSS X/Z checks commute as concrete qubit-register operators when their
finite-coordinate binary word pairing is zero.
-/
theorem cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
    {x z : Word (ZMod 2) ι}
    (h : wordPairing (F := ZMod 2) (ι := ι) x z = 0) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by
  exact cssXCheck_toQubitOperator_commute_cssZCheck_of_symplecticForm_eq_zero
    (by simpa [symplecticForm_x_zero_zero_z_eq_wordPairing] using h)

/--
Binary CSS X/Z checks commute as concrete qubit-register operators when the
`Z` word lies in the dual of the classical code containing the `X` word.
-/
theorem cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by
  exact cssXCheck_toQubitOperator_commute_cssZCheck_of_symplecticForm_eq_zero
    (LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual C hx hz)

/--
Binary CSS X/Z checks commute as concrete qubit-register operators under the
dual-containment convention `zCode ≤ xCode.dual`.
-/
theorem cssXCheck_toQubitOperator_commute_cssZCheck_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier) :
    toQubitOperator (cssXCheck x) * toQubitOperator (cssZCheck z) =
      toQubitOperator (cssZCheck z) * toQubitOperator (cssXCheck x) := by
  exact cssXCheck_toQubitOperator_commute_cssZCheck_of_mem_dual xCode hx (hdual hz)

omit [DecidableEq ι] in
/-- Binary CSS X checks commute algebraically in Pauli-symplectic coordinates. -/
theorem cssXCheck_commutes_cssXCheck (x y : Word (ZMod 2) ι) :
    Commutes (cssXCheck x) (cssXCheck y) := by
  simp [Commutes, symplecticForm]

omit [DecidableEq ι] in
/-- Binary CSS Z checks commute algebraically in Pauli-symplectic coordinates. -/
theorem cssZCheck_commutes_cssZCheck (z w : Word (ZMod 2) ι) :
    Commutes (cssZCheck z) (cssZCheck w) := by
  simp [Commutes, symplecticForm]

omit [DecidableEq ι] in
/--
Binary CSS X/Z checks commute algebraically when the `Z` word lies in the dual
of the classical code containing the `X` word.
-/
theorem cssXCheck_commutes_cssZCheck_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    Commutes (cssXCheck x) (cssZCheck z) := by
  exact
    (by
      simpa [cssXCheck, cssZCheck, Commutes] using
        LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual C hx hz)

omit [DecidableEq ι] in
/-- Binary CSS X/Z checks commute algebraically under `zCode ≤ xCode.dual`. -/
theorem cssXCheck_commutes_cssZCheck_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier) :
    Commutes (cssXCheck x) (cssZCheck z) :=
  cssXCheck_commutes_cssZCheck_of_mem_dual xCode hx (hdual hz)

omit [DecidableEq ι] in
/--
Binary CSS Z/X checks commute algebraically in the reverse orientation. The
proof explicitly reduces the reversed symplectic form to the negated X/Z form.
-/
theorem cssZCheck_commutes_cssXCheck_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    Commutes (cssZCheck z) (cssXCheck x) := by
  have hXZ :
      symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0 :=
    LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual C hx hz
  rw [cssZCheck, cssXCheck, Commutes]
  calc
    symplecticForm ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι)
        ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
        = -symplecticForm
            ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
            ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) := by
          simp [symplecticForm, mul_comm]
    _ = 0 := by
          simp [hXZ]

omit [DecidableEq ι] in
/-- Binary CSS Z/X checks commute algebraically under `zCode ≤ xCode.dual`. -/
theorem cssZCheck_commutes_cssXCheck_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hz : z ∈ zCode.carrier) (hx : x ∈ xCode.carrier) :
    Commutes (cssZCheck z) (cssXCheck x) :=
  cssZCheck_commutes_cssXCheck_of_mem_dual xCode hx (hdual hz)

omit [DecidableEq ι] in
/-- If a word is not in a binary code dual, some codeword has nonzero pairing with it. -/
theorem exists_carrier_wordPairing_ne_zero_of_not_mem_dual
    (C : LinearCode (ZMod 2) ι) {x : Word (ZMod 2) ι}
    (hx : x ∉ C.dual.carrier) :
    ∃ c, c ∈ C.carrier ∧ wordPairing (F := ZMod 2) (ι := ι) x c ≠ 0 := by
  classical
  have hnotOrth :
      ¬ ∀ c : Word (ZMod 2) ι, c ∈ C.carrier →
        wordPairing (F := ZMod 2) (ι := ι) x c = 0 := by
    intro horth
    exact hx ((C.mem_dual x).2 horth)
  rcases not_forall.mp hnotOrth with ⟨c, hc⟩
  have hc' :
      c ∈ C.carrier ∧ wordPairing (F := ZMod 2) (ι := ι) x c ≠ 0 :=
    Classical.not_imp.mp hc
  exact ⟨c, hc'.1, hc'.2⟩

omit [DecidableEq ι] in
/--
A low-weight nonzero pure `X` word fails to commute with some `Z` check when
the dual minimum distance of the `Z` code is larger than the word weight.
-/
theorem exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
    (zCode : LinearCode (ZMod 2) ι) {dX : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    ∃ z, z ∈ zCode.carrier ∧ ¬ Commutes (cssXCheck x) (cssZCheck z) := by
  have hxNotDual : x ∉ zCode.dual.carrier :=
    not_mem_carrier_of_hammingWeight_lt_minimumDistance (C := zCode.dual) hminX hx0 hxlt
  rcases exists_carrier_wordPairing_ne_zero_of_not_mem_dual zCode hxNotDual with
    ⟨z, hz, hpair⟩
  refine ⟨z, hz, ?_⟩
  intro hcomm
  exact hpair (by
    simpa [cssXCheck, cssZCheck, Commutes, symplecticForm_x_zero_zero_z_eq_wordPairing]
      using hcomm)

omit [DecidableEq ι] in
/--
A low-weight nonzero pure `Z` word fails to commute with some `X` check when
the dual minimum distance of the `X` code is larger than the word weight.
-/
theorem exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    ∃ x, x ∈ xCode.carrier ∧ ¬ Commutes (cssZCheck z) (cssXCheck x) := by
  have hzNotDual : z ∉ xCode.dual.carrier :=
    not_mem_carrier_of_hammingWeight_lt_minimumDistance (C := xCode.dual) hminZ hz0 hzlt
  rcases exists_carrier_wordPairing_ne_zero_of_not_mem_dual xCode hzNotDual with
    ⟨x, hx, hpair⟩
  refine ⟨x, hx, ?_⟩
  intro hcomm
  have hrev :
      symplecticForm
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι)
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι) = 0 := by
    simpa [cssZCheck, cssXCheck, Commutes] using hcomm
  have hrev_eq :
      symplecticForm
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι)
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι) =
        -symplecticForm
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) := by
    simp [symplecticForm, mul_comm]
  have hsymp :
      symplecticForm
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0 := by
    have hneg :
        -symplecticForm
          ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0 := by
      rwa [← hrev_eq]
    exact neg_eq_zero.mp hneg
  have hpairXZ : wordPairing (F := ZMod 2) (ι := ι) x z = 0 := by
    simpa [symplecticForm_x_zero_zero_z_eq_wordPairing] using hsymp
  exact hpair (by
    simpa [wordPairing_apply, dotProduct_comm] using hpairXZ)

/--
Membership in the binary stabilizer generated by a finite family.  The closure
is stated directly because the binary Pauli multiplication API is intentionally
kept local rather than installed as a global group instance.
-/
inductive GeneratedStabilizer {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) : Binary ι → Prop
  | one : GeneratedStabilizer generators (binaryOne (ι := ι))
  | generator (j : κ) : GeneratedStabilizer generators (generators j)
  | mul {P Q : Binary ι} : GeneratedStabilizer generators P →
      GeneratedStabilizer generators Q →
      GeneratedStabilizer generators (binaryMul P Q)
  | dagger {P : Binary ι} : GeneratedStabilizer generators P →
      GeneratedStabilizer generators (binaryDagger P)

/-- The generated binary stabilizer as a set of Pauli representatives. -/
def generatedStabilizerSet {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) : Set (Binary ι) :=
  {P | GeneratedStabilizer generators P}

omit [DecidableEq ι] in
@[simp] theorem commutes_binaryOne_right (E : Binary ι) :
    Commutes E (binaryOne (ι := ι)) := by
  simp [Commutes, binaryOne, symplecticForm]

omit [DecidableEq ι] in
/-- Commutation with two binary Paulis is preserved by their product. -/
theorem commutes_binaryMul_right {E P Q : Binary ι}
    (hP : Commutes E P) (hQ : Commutes E Q) :
    Commutes E (binaryMul P Q) := by
  have hsplit :
      symplecticForm E.vector (binaryMul P Q).vector =
        symplecticForm E.vector P.vector + symplecticForm E.vector Q.vector := by
    simp only [binaryMul, symplecticForm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.add_apply]
    ring
  rw [Commutes, hsplit, hP, hQ]
  simp

omit [DecidableEq ι] in
/-- Commutation is unchanged by replacing a binary Pauli by its dagger. -/
theorem commutes_binaryDagger_right {E P : Binary ι} (hP : Commutes E P) :
    Commutes E (binaryDagger P) := by
  simpa [Commutes, binaryDagger] using hP

/--
The Pauli normalizer/centralizer predicate `N(S)`: an error commutes with every
representative in the stabilizer generated by `generators`.
-/
def InStabilizerNormalizer {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E : Binary ι) : Prop :=
  ∀ S, GeneratedStabilizer generators S → Commutes E S

/-- The binary stabilizer normalizer/centralizer as a set. -/
def stabilizerNormalizer {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) : Set (Binary ι) :=
  {E | InStabilizerNormalizer generators E}

omit [DecidableEq ι] in
/-- It suffices to test normalizer membership on the selected generators. -/
theorem inStabilizerNormalizer_iff_commutes_generators
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    InStabilizerNormalizer generators E ↔ ∀ j, Commutes E (generators j) := by
  constructor
  · intro h j
    exact h (generators j) (.generator j)
  · intro h S hS
    induction hS with
    | one => exact commutes_binaryOne_right E
    | generator j => exact h j
    | mul hP hQ ihP ihQ => exact commutes_binaryMul_right ihP ihQ
    | dagger hP ihP => exact commutes_binaryDagger_right ihP

/-- A phase-only binary Pauli, representing the global sign `(-1)^phase`. -/
def binarySign (phase : ZMod 2) : Binary ι :=
  { phase := phase, vector := { xPart := 0, zPart := 0 } }

/--
Binary Pauli representatives agree up to global sign exactly when their
symplectic vectors agree.  The stored `ZMod 2` phase bit is deliberately
quotiented, while the X/Z action is retained.
-/
def BinaryUpToSign (P Q : Binary ι) : Prop :=
  P.vector = Q.vector

omit [DecidableEq ι] in
@[refl] theorem binaryUpToSign_refl (P : Binary ι) : BinaryUpToSign P P := rfl

omit [DecidableEq ι] in
@[symm] theorem binaryUpToSign_symm {P Q : Binary ι} :
    BinaryUpToSign P Q → BinaryUpToSign Q P :=
  Eq.symm

omit [DecidableEq ι] in
@[trans] theorem binaryUpToSign_trans {P Q R : Binary ι} :
    BinaryUpToSign P Q → BinaryUpToSign Q R → BinaryUpToSign P R :=
  Eq.trans

omit [DecidableEq ι] in
/-- `BinaryUpToSign` is precisely multiplication by one of the two global signs. -/
theorem binaryUpToSign_iff_exists_binarySign (P Q : Binary ι) :
    BinaryUpToSign P Q ↔ ∃ phase : ZMod 2, P = binaryMul (binarySign phase) Q := by
  constructor
  · intro h
    rcases P with ⟨p, v⟩
    rcases Q with ⟨q, w⟩
    change v = w at h
    subst w
    refine ⟨p - q, ?_⟩
    simp [binaryMul, binaryMulPhase, binarySign]
  · rintro ⟨phase, rfl⟩
    simp [BinaryUpToSign, binaryMul, binarySign]

omit [DecidableEq ι] in
@[simp] theorem binaryUpToSign_binaryDagger (P : Binary ι) :
    BinaryUpToSign (binaryDagger P) P := rfl

omit [DecidableEq ι] in
/--
The source's `E_a E_b = ± E_a† E_b` convention is represented by equality of
the binary X/Z vectors, with the possible sign difference retained in `phase`.
-/
theorem binaryMul_upToSign_binaryMul_dagger_left (E F : Binary ι) :
    BinaryUpToSign (binaryMul E F) (binaryMul (binaryDagger E) F) := rfl

omit [DecidableEq ι] in
/-- Commutation is invariant under the binary global-sign quotient. -/
theorem commutes_iff_of_binaryUpToSign_left {P Q R : Binary ι}
    (h : BinaryUpToSign P Q) : Commutes P R ↔ Commutes Q R := by
  change symplecticForm P.vector R.vector = 0 ↔
    symplecticForm Q.vector R.vector = 0
  rw [h]

/-- Membership in the generated stabilizer, modulo the explicit binary sign bit. -/
def InGeneratedStabilizerUpToSign {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E : Binary ι) : Prop :=
  ∃ S, GeneratedStabilizer generators S ∧ BinaryUpToSign E S

/--
Two errors are stabilizer-equivalent when their relative Pauli is in the
generated stabilizer up to the binary global-sign convention.
-/
def StabilizerEquivalent {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E F : Binary ι) : Prop :=
  InGeneratedStabilizerUpToSign generators (binaryMul (binaryDagger E) F)

/-- Source-facing name for a stabilizer-equivalent, hence degenerate, error pair. -/
def DegenerateErrorPair {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E F : Binary ι) : Prop :=
  StabilizerEquivalent generators E F

omit [DecidableEq ι] in
/--
The relative-error definition of stabilizer equivalence is exactly the source's
`E * F` membership statement once the possible binary global sign is quotiented.
-/
theorem stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    StabilizerEquivalent generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by
  constructor
  · rintro ⟨S, hS, hRelative⟩
    exact ⟨S, hS,
      binaryUpToSign_trans (binaryMul_upToSign_binaryMul_dagger_left E F) hRelative⟩
  · rintro ⟨S, hS, hProduct⟩
    exact ⟨S, hS,
      binaryUpToSign_trans
        (binaryUpToSign_symm (binaryMul_upToSign_binaryMul_dagger_left E F)) hProduct⟩

omit [DecidableEq ι] in
/-- Source-facing degeneracy in either pair-product convention. -/
theorem degenerateErrorPair_iff_binaryMul_mem_generated_upToSign
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    DegenerateErrorPair generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by
  exact stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign generators E F

/-- The source syndrome bit `f_M(E)` in the binary commutation convention. -/
def stabilizerSyndromeBit (M E : Binary ι) : ZMod 2 :=
  symplecticForm E.vector M.vector

/-- The finite generator-indexed syndrome vector `f(E)`. -/
def stabilizerSyndrome {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E : Binary ι) : κ → ZMod 2 :=
  fun j => stabilizerSyndromeBit (generators j) E

omit [DecidableEq ι] in
@[simp] theorem stabilizerSyndrome_apply
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (E : Binary ι) (j : κ) :
    stabilizerSyndrome generators E j = stabilizerSyndromeBit (generators j) E := rfl

omit [DecidableEq ι] in
/-- A syndrome bit is zero exactly for commuting binary Paulis. -/
theorem stabilizerSyndromeBit_eq_zero_iff_commutes (M E : Binary ι) :
    stabilizerSyndromeBit M E = 0 ↔ Commutes E M :=
  Iff.rfl

omit [DecidableEq ι] in
/-- A syndrome bit is one exactly for anticommuting binary Paulis. -/
theorem stabilizerSyndromeBit_eq_one_iff_not_commutes (M E : Binary ι) :
    stabilizerSyndromeBit M E = 1 ↔ ¬ Commutes E M := by
  constructor
  · intro hOne hCommutes
    have hZero := (stabilizerSyndromeBit_eq_zero_iff_commutes M E).2 hCommutes
    rw [hZero] at hOne
    exact zero_ne_one hOne
  · intro hNotCommutes
    apply zmod_two_eq_one_of_ne_zero
    intro hZero
    exact hNotCommutes ((stabilizerSyndromeBit_eq_zero_iff_commutes M E).1 hZero)

/-- A zero syndrome bit gives concrete commutation of the represented operators. -/
theorem toQubitOperator_commute_of_stabilizerSyndromeBit_eq_zero
    (M E : Binary ι) (h : stabilizerSyndromeBit M E = 0) :
    toQubitOperator E * toQubitOperator M = toQubitOperator M * toQubitOperator E := by
  exact toQubitOperator_commute_of_commutes E M
    ((stabilizerSyndromeBit_eq_zero_iff_commutes M E).1 h)

/-- A one syndrome bit gives concrete anticommutation of the represented operators. -/
theorem toQubitOperator_anticommute_of_stabilizerSyndromeBit_eq_one
    (M E : Binary ι) (h : stabilizerSyndromeBit M E = 1) :
    toQubitOperator E * toQubitOperator M =
      -(toQubitOperator M * toQubitOperator E) := by
  exact toQubitOperator_anticommute_of_not_commutes E M
    ((stabilizerSyndromeBit_eq_one_iff_not_commutes M E).1 h)

omit [DecidableEq ι] in
/-- The syndrome bit ignores exactly the explicit binary global sign. -/
theorem stabilizerSyndromeBit_eq_of_binaryUpToSign {E F M : Binary ι}
    (h : BinaryUpToSign E F) :
    stabilizerSyndromeBit M E = stabilizerSyndromeBit M F := by
  change E.vector = F.vector at h
  rw [stabilizerSyndromeBit, stabilizerSyndromeBit, h]

omit [DecidableEq ι] in
/-- The finite generator syndrome is additive under binary Pauli multiplication. -/
private theorem stabilizerSyndrome_binaryMul
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (A B : Binary ι) :
    stabilizerSyndrome generators (binaryMul A B) =
      stabilizerSyndrome generators A + stabilizerSyndrome generators B := by
  funext j
  simp only [stabilizerSyndrome_apply, Pi.add_apply, stabilizerSyndromeBit,
    binaryMul, symplecticForm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [DecidableEq ι] in
/--
The finite stabilizer syndrome laws: zero syndrome characterizes the generated
stabilizer normalizer, equal syndromes characterize a zero product syndrome,
and the source product has the same syndrome as the relative product under the
binary global-phase convention.  This is the source-exact bundled realization
of [Gott97, Ch. 3, error syndrome and Pauli pair-product convention].
-/
theorem stabilizerSyndrome_map_properties
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E A B : Binary ι) :
    (stabilizerSyndrome generators E = 0 ↔
      InStabilizerNormalizer generators E) ∧
    (stabilizerSyndrome generators A = stabilizerSyndrome generators B ↔
      stabilizerSyndrome generators (binaryMul A B) = 0) ∧
    stabilizerSyndrome generators (binaryMul A B) =
      stabilizerSyndrome generators (binaryMul (binaryDagger A) B) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hZero
      apply (inStabilizerNormalizer_iff_commutes_generators generators E).2
      intro j
      apply (stabilizerSyndromeBit_eq_zero_iff_commutes (generators j) E).1
      simpa [stabilizerSyndrome] using congrFun hZero j
    · intro hNormalizer
      funext j
      exact (stabilizerSyndromeBit_eq_zero_iff_commutes (generators j) E).2
        ((inStabilizerNormalizer_iff_commutes_generators generators E).1
          hNormalizer j)
  · rw [stabilizerSyndrome_binaryMul]
    constructor
    · intro hEqual
      rw [hEqual]
      funext j
      exact CharTwo.add_self_eq_zero _
    · intro hSum
      funext j
      apply CharTwo.add_eq_zero.mp
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun hSum j
  · funext j
    exact stabilizerSyndromeBit_eq_of_binaryUpToSign
      (binaryMul_upToSign_binaryMul_dagger_left A B)

omit [DecidableEq ι] in
/-- A check set distinguishes a binary Pauli representative from identity. -/
def checkDistinguishes (checks : Set (Binary ι)) (E : Binary ι) : Prop :=
  ∃ S, S ∈ checks ∧ ¬ Commutes E S

omit [DecidableEq ι] in
/--
Pair-level check separation, phrased through the binary representative of
`E† * F`. This is internal vocabulary, not a public syndrome theorem.
-/
def syndromeSeparatedByCheckSet (checks : Set (Binary ι))
    (E F : Binary ι) : Prop :=
  checkDistinguishes checks (binaryMul (binaryDagger E) F)

omit [DecidableEq ι] in
/-- Existential check separation is exactly the existence of a one syndrome bit. -/
theorem checkDistinguishes_range_iff_exists_syndromeBit_eq_one
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (Set.range generators) E ↔
      ∃ j, stabilizerSyndromeBit (generators j) E = 1 := by
  constructor
  · rintro ⟨M, ⟨j, rfl⟩, hNotCommutes⟩
    exact ⟨j, (stabilizerSyndromeBit_eq_one_iff_not_commutes _ _).2 hNotCommutes⟩
  · rintro ⟨j, hOne⟩
    exact ⟨generators j, ⟨j, rfl⟩,
      (stabilizerSyndromeBit_eq_one_iff_not_commutes _ _).1 hOne⟩

omit [DecidableEq ι] in
/-- A generator range distinguishes an error exactly when its syndrome is nonzero. -/
theorem checkDistinguishes_range_iff_syndrome_ne_zero
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (Set.range generators) E ↔
      stabilizerSyndrome generators E ≠ 0 := by
  constructor
  · rintro ⟨M, ⟨j, rfl⟩, hNotCommutes⟩ hZero
    have hBitZero : stabilizerSyndromeBit (generators j) E = 0 := by
      simpa [stabilizerSyndrome] using congrFun hZero j
    exact hNotCommutes ((stabilizerSyndromeBit_eq_zero_iff_commutes _ _).1 hBitZero)
  · intro hSyndrome
    by_contra hDistinguishes
    apply hSyndrome
    funext j
    apply (stabilizerSyndromeBit_eq_zero_iff_commutes _ _).2
    by_contra hNotCommutes
    exact hDistinguishes ⟨generators j, ⟨j, rfl⟩, hNotCommutes⟩

omit [DecidableEq ι] in
/--
The legacy pair-separation predicate over the generator range is exactly a
nonzero syndrome for the relative binary Pauli.
-/
theorem syndromeSeparatedByCheckSet_range_iff_relative_syndrome_ne_zero
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    syndromeSeparatedByCheckSet (Set.range generators) E F ↔
      stabilizerSyndrome generators (binaryMul (binaryDagger E) F) ≠ 0 := by
  exact checkDistinguishes_range_iff_syndrome_ne_zero generators
    (binaryMul (binaryDagger E) F)

omit [DecidableEq ι] in
/-- Failure of normalizer membership is witnessed by a generated stabilizer check. -/
theorem not_inStabilizerNormalizer_iff_checkDistinguishes_generatedStabilizerSet
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    ¬ InStabilizerNormalizer generators E ↔
      checkDistinguishes (generatedStabilizerSet generators) E := by
  classical
  simp [InStabilizerNormalizer, checkDistinguishes, generatedStabilizerSet]

omit [DecidableEq ι] in
/--
A generated stabilizer distinguishes an error exactly when the selected finite
generator family does.  The reverse direction uses closure of commutation under
products and daggers rather than assuming a stored normalizer property.
-/
theorem checkDistinguishes_generatedStabilizerSet_iff_range
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (generatedStabilizerSet generators) E ↔
      checkDistinguishes (Set.range generators) E := by
  constructor
  · rintro ⟨S, hS, hNotCommutes⟩
    by_contra hRange
    have hNormalizer : InStabilizerNormalizer generators E :=
      (inStabilizerNormalizer_iff_commutes_generators generators E).2 (by
        intro j
        by_contra hNotGenerator
        exact hRange ⟨generators j, ⟨j, rfl⟩, hNotGenerator⟩)
    exact hNotCommutes (hNormalizer S hS)
  · rintro ⟨M, ⟨j, rfl⟩, hNotCommutes⟩
    exact ⟨generators j, GeneratedStabilizer.generator j, hNotCommutes⟩

omit [DecidableEq ι] in
/-- Full generated-stabilizer separation is equivalent to a nonzero syndrome. -/
theorem checkDistinguishes_generatedStabilizerSet_iff_syndrome_ne_zero
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (generatedStabilizerSet generators) E ↔
      stabilizerSyndrome generators E ≠ 0 := by
  rw [checkDistinguishes_generatedStabilizerSet_iff_range]
  exact checkDistinguishes_range_iff_syndrome_ne_zero generators E

omit [DecidableEq ι] in
/--
The legacy pair-separation predicate over the generated stabilizer is exactly a
nonzero generator syndrome for the relative binary Pauli.
-/
theorem syndromeSeparatedByCheckSet_generatedStabilizerSet_iff_relative_syndrome_ne_zero
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    syndromeSeparatedByCheckSet (generatedStabilizerSet generators) E F ↔
      stabilizerSyndrome generators (binaryMul (binaryDagger E) F) ≠ 0 := by
  exact checkDistinguishes_generatedStabilizerSet_iff_syndrome_ne_zero generators
    (binaryMul (binaryDagger E) F)

omit [DecidableEq ι] in
/--
A low-weight nonzero pure `X` word is distinguished from identity by some
`Z` check in the binary CSS check set.
-/
theorem checkDistinguishes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode zCode : LinearCode (ZMod 2) ι) {dX : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) (cssXCheck x) := by
  rcases
      exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
        zCode hminX hx0 hxlt with
    ⟨z, hz, hnotCommutes⟩
  exact ⟨cssZCheck z, Or.inr ⟨z, hz, rfl⟩, hnotCommutes⟩

omit [DecidableEq ι] in
/--
A low-weight nonzero pure `Z` word is distinguished from identity by some
`X` check in the binary CSS check set.
-/
theorem checkDistinguishes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode zCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) (cssZCheck z) := by
  rcases
      exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
        xCode hminZ hz0 hzlt with
    ⟨x, hx, hnotCommutes⟩
  exact ⟨cssXCheck x, Or.inl ⟨x, hx, rfl⟩, hnotCommutes⟩

/--
A nontrivial low-weight binary Pauli representative is distinguished by a CSS
check under the dual minimum-distance hypotheses.
-/
theorem checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
    (xCode zCode : LinearCode (ZMod 2) ι) {dX dZ : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    {P : Binary ι}
    (hP : P.vector.xPart ≠ 0 ∨ P.vector.zPart ≠ 0)
    (hwt : weight P < min dX dZ) :
    checkDistinguishes (binaryCSSCheckSet xCode zCode) P := by
  rcases hP with hx0 | hz0
  · have hxltMin : HammingWeight P.vector.xPart < min dX dZ :=
      lt_of_le_of_lt (hammingWeight_xPart_le_weight P) hwt
    have hxlt : HammingWeight P.vector.xPart < dX :=
      lt_of_lt_of_le hxltMin (Nat.min_le_left dX dZ)
    rcases
        exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
          zCode hminX hx0 hxlt with
      ⟨z, hz, hnotCommutes⟩
    refine ⟨cssZCheck z, Or.inr ⟨z, hz, rfl⟩, ?_⟩
    intro hcomm
    exact hnotCommutes (by
      simpa [cssXCheck, cssZCheck, Commutes, symplecticForm] using hcomm)
  · have hzltMin : HammingWeight P.vector.zPart < min dX dZ :=
      lt_of_le_of_lt (hammingWeight_zPart_le_weight P) hwt
    have hzlt : HammingWeight P.vector.zPart < dZ :=
      lt_of_lt_of_le hzltMin (Nat.min_le_right dX dZ)
    rcases
        exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
          xCode hminZ hz0 hzlt with
      ⟨x, hx, hnotCommutes⟩
    refine ⟨cssXCheck x, Or.inl ⟨x, hx, rfl⟩, ?_⟩
    intro hcomm
    exact hnotCommutes (by
      simpa [cssZCheck, cssXCheck, Commutes, symplecticForm] using hcomm)

omit [DecidableEq ι] in
/--
Identity versus a low-weight nonzero pure `X` error is separated by a CSS
check under the dual-distance hypothesis.
-/
theorem syndromeSeparated_binaryOne_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode zCode : LinearCode (ZMod 2) ι) {dX : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode)
      (binaryOne (ι := ι)) (cssXCheck x) := by
  simpa [syndromeSeparatedByCheckSet] using
    checkDistinguishes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
      xCode zCode hminX hx0 hxlt

omit [DecidableEq ι] in
/--
Identity versus a low-weight nonzero pure `Z` error is separated by a CSS
check under the dual-distance hypothesis.
-/
theorem syndromeSeparated_binaryOne_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
    (xCode zCode : LinearCode (ZMod 2) ι) {dZ : Nat}
    (hminZ : MinimumDistance xCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode)
      (binaryOne (ι := ι)) (cssZCheck z) := by
  simpa [syndromeSeparatedByCheckSet] using
    checkDistinguishes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
      xCode zCode hminZ hz0 hzlt

/--
Two scoped low-weight binary Pauli representatives are separated by a CSS check
when their relative representative `E† * F` has a nontrivial X or Z component.
-/
theorem syndromeSeparatedByCheckSet_of_scopedByWeight_pair
    (xCode zCode : LinearCode (ZMod 2) ι) {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    {E F : Binary ι}
    (hE : E ∈ scopedByWeight (ι := ι) t)
    (hF : F ∈ scopedByWeight (ι := ι) t)
    (hnontrivial :
      (binaryMul (binaryDagger E) F).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E) F).vector.zPart ≠ 0) :
    syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode) E F := by
  rw [mem_scopedByWeight] at hE hF
  have hmulLe :
      weight (binaryMul (binaryDagger E) F) ≤ t + t := by
    calc
      weight (binaryMul (binaryDagger E) F) ≤ weight (binaryDagger E) + weight F :=
        weight_binaryMul_le (binaryDagger E) F
      _ = weight E + weight F := by
        simp
      _ ≤ t + t :=
        Nat.add_le_add hE hF
  have htt : t + t < min dX dZ := by
    simpa [two_mul] using hbound
  have hwt : weight (binaryMul (binaryDagger E) F) < min dX dZ :=
    lt_of_le_of_lt hmulLe htt
  simpa [syndromeSeparatedByCheckSet] using
    checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
      xCode zCode hminX hminZ hnontrivial hwt

omit [DecidableEq ι] in
/--
The scoped binary CSS check set is pairwise commuting from the explicit
dual-containment hypothesis `zCode ≤ xCode.dual`.
-/
theorem binaryCSSCheckSet_pairwise_commutes_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
      ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode → Commutes P Q := by
  intro P hP Q hQ
  rw [binaryCSSCheckSet] at hP hQ
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · rcases hQ with ⟨y, _hy, rfl⟩ | ⟨w, hw, rfl⟩
    · exact cssXCheck_commutes_cssXCheck x y
    · exact cssXCheck_commutes_cssZCheck_of_dual_le xCode zCode hdual hx hw
  · rcases hQ with ⟨y, hy, rfl⟩ | ⟨w, _hw, rfl⟩
    · exact cssZCheck_commutes_cssXCheck_of_dual_le xCode zCode hdual hz hy
    · exact cssZCheck_commutes_cssZCheck z w

omit [DecidableEq ι] in
/--
The combined binary CSS check set is pairwise commuting exactly when the `Z`
row code lies in the dual of the `X` row code. The reverse containment is
equivalent by `LinearCode.le_dual_iff_le_dual`, so no second containment
hypothesis is needed.
-/
theorem binaryCSSCheckSet_pairwise_commutes_iff_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι) :
    (∀ P ∈ binaryCSSCheckSet xCode zCode,
      ∀ Q ∈ binaryCSSCheckSet xCode zCode, Commutes P Q) ↔
      zCode.carrier ≤ xCode.dual.carrier := by
  constructor
  · intro hcommutes z hz
    refine (xCode.mem_dual z).2 ?_
    intro x hx
    have hcommutesXZ : Commutes (cssXCheck x) (cssZCheck z) :=
      hcommutes
        (cssXCheck x) (Or.inl ⟨x, hx, rfl⟩)
        (cssZCheck z) (Or.inr ⟨z, hz, rfl⟩)
    have hpairXZ : wordPairing (F := ZMod 2) (ι := ι) x z = 0 := by
      simpa [cssXCheck, cssZCheck, Commutes,
        symplecticForm_x_zero_zero_z_eq_wordPairing] using hcommutesXZ
    simpa [wordPairing_apply, dotProduct_comm] using hpairXZ
  · exact binaryCSSCheckSet_pairwise_commutes_of_dual_le xCode zCode

omit [DecidableEq ι] in
/--
The binary CSS `X` code, pulled back as a submodule of the `Z`-dual carrier.
Under dual containment it is equivalent to `xCode.carrier`; without that
hypothesis it is the actual intersection with `zCode.dual.carrier`.
-/
noncomputable def binaryCSSXCodeInZDual
    (xCode zCode : LinearCode (ZMod 2) ι) :
    Submodule (ZMod 2) zCode.dual.carrier :=
  xCode.carrier.comap zCode.dual.carrier.subtype

omit [DecidableEq ι] in
/--
Dual containment `zCode ≤ xCode.dual` places the `X` code inside the `Z` dual.
The inclusion is derived from `LinearCode.le_dual_of_le_dual`, not assumed.
-/
noncomputable def binaryCSSXCodeInZDualEquiv
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    binaryCSSXCodeInZDual xCode zCode ≃ₗ[ZMod 2] xCode.carrier :=
  Submodule.comapSubtypeEquivOfLe
    (LinearCode.le_dual_of_le_dual xCode zCode hdual)

omit [DecidableEq ι] in
/-- Algebraic binary CSS logical-basis quotient `zCode.dual / xCode`. -/
noncomputable abbrev binaryCSSLogicalBasisQuotient
    (xCode zCode : LinearCode (ZMod 2) ι) :=
  zCode.dual.carrier ⧸ binaryCSSXCodeInZDual xCode zCode

omit [DecidableEq ι] in
@[simp] theorem finrank_binaryCSSXCodeInZDual_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank (ZMod 2) (binaryCSSXCodeInZDual xCode zCode) =
      Dimension xCode := by
  rw [Dimension_eq_finrank_carrier]
  exact (binaryCSSXCodeInZDualEquiv xCode zCode hdual).finrank_eq

omit [DecidableEq ι] in
/--
The algebraic binary CSS logical-basis quotient has dimension
`n - dim xCode - dim zCode`.
-/
theorem finrank_binaryCSSLogicalBasisQuotient_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank (ZMod 2) (binaryCSSLogicalBasisQuotient xCode zCode) =
      Length (ZMod 2) ι - Dimension xCode - Dimension zCode := by
  have hquot :=
    Submodule.finrank_quotient_add_finrank (binaryCSSXCodeInZDual xCode zCode)
  rw [finrank_binaryCSSXCodeInZDual_eq xCode zCode hdual,
    ← Dimension_eq_finrank_carrier zCode.dual,
    LinearCode.dual_dimension_eq_length_sub_dimension] at hquot
  rw [Nat.sub_right_comm]
  rw [← hquot]
  exact (Nat.add_sub_cancel_right _ _).symm

/--
Family-level bridge from pairwise binary symplectic commutation to pairwise
commutation of the interpreted finite qubit-register operators.
-/
theorem pairwise_toQubitOperator_commute_of_commutes
    {S : Set (Binary ι)}
    (hS : ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S → Commutes P Q) :
    ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S →
      toQubitOperator P * toQubitOperator Q =
        toQubitOperator Q * toQubitOperator P := by
  intro P hP Q hQ
  exact toQubitOperator_commute_of_commutes P Q (hS P hP Q hQ)

/--
The common fixed submodule of a binary stabilizer family, interpreted as
concrete qubit-register operators.
-/
def binaryStabilizerFixedSubmodule (S : Set (Binary ι)) :
    Submodule Complex (Semantics.Qubit.QubitRegister ι) where
  carrier := {ψ | ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ}
  zero_mem' := by
    intro P _hP
    simp
  add_mem' := by
    intro ψ φ hψ hφ P hP
    rw [map_add, hψ P hP, hφ P hP]
  smul_mem' := by
    intro c ψ hψ P hP
    rw [map_smul, hψ P hP]

@[simp] theorem mem_binaryStabilizerFixedSubmodule
    (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ binaryStabilizerFixedSubmodule S ↔
      ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ :=
  Iff.rfl

/-- The semantic quantum-code carrier determined by a binary stabilizer family. -/
def binaryStabilizerCommonFixedQuantumCode (S : Set (Binary ι)) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι) where
  carrier := binaryStabilizerFixedSubmodule S

@[simp] theorem mem_binaryStabilizerCommonFixedQuantumCode_carrier
    (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ (binaryStabilizerCommonFixedQuantumCode S).carrier ↔
      ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ :=
  Iff.rfl

/--
Projecting onto the constructed semantic code lands in the common fixed space.
This is the #131 projector-support API applied to the stabilizer fixed carrier.
-/
theorem binaryStabilizerCommonFixedQuantumCode_projector_fixed
    (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ∀ P : Binary ι, P ∈ S →
      toQubitOperator P ((binaryStabilizerCommonFixedQuantumCode S).projector ψ) =
        (binaryStabilizerCommonFixedQuantumCode S).projector ψ := by
  intro P hP
  exact
    (mem_binaryStabilizerCommonFixedQuantumCode_carrier
      (S := S) (ψ := (binaryStabilizerCommonFixedQuantumCode S).projector ψ)).1
      ((binaryStabilizerCommonFixedQuantumCode S).projector_mem_carrier ψ) P hP

/--
Commuting binary stabilizer data determines the semantic common-fixed
`QuantumCode` carrier and supplies the concrete operator commutation bridge.
-/
theorem exists_binaryStabilizerCommonFixedQuantumCode_of_commutes
    {S : Set (Binary ι)}
    (hS : ∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S → Commutes P Q) :
    ∃ C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι),
      (∀ ψ, ψ ∈ C.carrier ↔ ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ) ∧
      (∀ P : Binary ι, P ∈ S → ∀ Q : Binary ι, Q ∈ S →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P) := by
  refine ⟨binaryStabilizerCommonFixedQuantumCode S, ?_, ?_⟩
  · intro ψ
    exact mem_binaryStabilizerCommonFixedQuantumCode_carrier (S := S) (ψ := ψ)
  · exact pairwise_toQubitOperator_commute_of_commutes hS

/--
Binary stabilizer-code specialization: the algebraic isotropic stabilizer field
is used only as input to the operator-level family bridge above.
-/
theorem pairwise_toQubitOperator_commute_of_stabilizerCode
    (S : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    ∀ P : Binary ι, P ∈ S.stabilizers → ∀ Q : Binary ι, Q ∈ S.stabilizers →
      toQubitOperator P * toQubitOperator Q =
        toQubitOperator Q * toQubitOperator P :=
  pairwise_toQubitOperator_commute_of_commutes S.isotropic

/--
Construct the binary CSS stabilizer code directly from scoped classical X/Z
codeword data and dual containment.
-/
def binaryCSSStabilizerCodeOfDualLe
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι) where
  stabilizers := binaryCSSCheckSet xCode zCode
  code := binaryStabilizerCommonFixedQuantumCode (binaryCSSCheckSet xCode zCode)
  isotropic := binaryCSSCheckSet_pairwise_commutes_of_dual_le xCode zCode hdual

/--
The stabilizer code constructed from binary CSS data has pairwise commuting
concrete qubit-register operators.
-/
theorem binaryCSSStabilizerCodeOfDualLe_pairwise_toQubitOperator_commute
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι,
      P ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).stabilizers →
      ∀ Q : Binary ι,
        Q ∈ (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).stabilizers →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P :=
  pairwise_toQubitOperator_commute_of_stabilizerCode
    (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual)

/-- CSS checks are interpreted as self-adjoint qubit-register operators. -/
theorem adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet
    (xCode zCode : LinearCode (ZMod 2) ι) {S : Binary ι}
    (hS : S ∈ binaryCSSCheckSet xCode zCode) :
    LinearMap.adjoint (toQubitOperator S) = toQubitOperator S := by
  rw [adjoint_toQubitOperator_eq_binaryDagger]
  rcases hS with ⟨x, _hx, rfl⟩ | ⟨z, _hz, rfl⟩
  · simp
  · simp

/--
The semantic `QuantumCode` carrier determined directly by scoped binary CSS data
and dual containment.
-/
noncomputable def binaryCSSQuantumCodeOfDualLe
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι) :=
  (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).code

@[simp] theorem mem_binaryCSSQuantumCodeOfDualLe_carrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier ↔
      ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode → toQubitOperator P ψ = ψ := by
  simp [binaryCSSQuantumCodeOfDualLe, binaryCSSStabilizerCodeOfDualLe]

/--
A CSS check that distinguishes `P` from identity forces the corresponding
matrix element to vanish on the semantic binary CSS common-fixed carrier.
-/
theorem inner_toQubitOperator_eq_zero_of_checkDistinguishes
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {P : Binary ι}
    (hsep : checkDistinguishes (binaryCSSCheckSet xCode zCode) P)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator P ψ) φ = 0 := by
  rcases hsep with ⟨S, hS, hnotCommutes⟩
  let A := toQubitOperator S
  let B := toQubitOperator P
  have hAadj : LinearMap.adjoint A = A := by
    simpa [A] using adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet xCode zCode hS
  have hψS : A ψ = ψ := by
    simpa [A] using
      (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ).1 hψ S hS
  have hφS : A φ = φ := by
    simpa [A] using
      (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual φ).1 hφ S hS
  have hanti : B * A = -(A * B) := by
    simpa [A, B] using toQubitOperator_anticommute_of_not_commutes P S hnotCommutes
  have hanti' : A * B = -(B * A) := by
    rw [hanti]
    simp
  have hABψ : A (B ψ) = -B ψ := by
    have happ := congrArg
      (fun T : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => T ψ) hanti'
    simpa [Module.End.mul_apply, hψS] using happ
  let a : Complex := inner Complex (B ψ) φ
  have ha_neg : a = -a := by
    calc
      a = inner Complex (B ψ) (A φ) := by
          simp [a, hφS]
      _ = inner Complex (LinearMap.adjoint A (B ψ)) φ := by
          simpa using (LinearMap.adjoint_inner_left (𝕜 := Complex) A φ (B ψ)).symm
      _ = inner Complex (A (B ψ)) φ := by
          rw [hAadj]
      _ = inner Complex (-B ψ) φ := by
          rw [hABψ]
      _ = -a := by
          simp [a]
  have hadd : a + a = 0 := eq_neg_iff_add_eq_zero.mp ha_neg
  have htwo : (2 : Complex) * a = 0 := by
    simpa [two_mul] using hadd
  have hzero : a = 0 := (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa [a, B] using hzero

/--
Pair version of the matrix-element-zero bridge, phrased through the existing
binary product/dagger representative of `E† * F`.
-/
theorem matrixElement_zero_of_syndromeSeparatedByCheckSet
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {E F : Binary ι}
    (hsep : syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode) E F)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) = 0 := by
  let R := binaryMul (binaryDagger E) F
  have hrelInner :
      inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
        inner Complex ψ (toQubitOperator R φ) := by
    calc
      inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
          inner Complex ψ (LinearMap.adjoint (toQubitOperator E) (toQubitOperator F φ)) := by
            simpa using
              (LinearMap.adjoint_inner_right (𝕜 := Complex) (toQubitOperator E) ψ
                (toQubitOperator F φ)).symm
      _ = inner Complex ψ (toQubitOperator (binaryDagger E) (toQubitOperator F φ)) := by
            rw [← toQubitOperator_binaryDagger E]
      _ = inner Complex ψ ((toQubitOperator (binaryDagger E) * toQubitOperator F) φ) := by
            simp [Module.End.mul_apply]
      _ = inner Complex ψ (toQubitOperator R φ) := by
            rw [← toQubitOperator_binaryMul (binaryDagger E) F]
  have hrelZero : inner Complex (toQubitOperator R φ) ψ = 0 := by
    exact inner_toQubitOperator_eq_zero_of_checkDistinguishes xCode zCode hdual
      (P := R) (by simpa [R, syndromeSeparatedByCheckSet] using hsep) hφ hψ
  have hflipZero : inner Complex ψ (toQubitOperator R φ) = 0 := by
    have hconj := congrArg star hrelZero
    simpa [inner_conj_symm] using hconj
  simpa [hrelInner] using hflipZero

/--
Scoped low-weight pair version obtained by combining #177's check separation
theorem with the matrix-element bridge.
-/
theorem matrixElement_zero_of_scopedByWeight_pair
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    {E F : Binary ι}
    (hE : E ∈ scopedByWeight (ι := ι) t)
    (hF : F ∈ scopedByWeight (ι := ι) t)
    (hnontrivial :
      (binaryMul (binaryDagger E) F).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E) F).vector.zPart ≠ 0)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) = 0 :=
  matrixElement_zero_of_syndromeSeparatedByCheckSet xCode zCode hdual
    (syndromeSeparatedByCheckSet_of_scopedByWeight_pair
      xCode zCode hminX hminZ hbound hE hF hnontrivial)
    hψ hφ

/-- The concrete scalar matrix for the scoped binary-Pauli finite-Kraus family. -/
noncomputable def scopedErrorFamilyKLScalar (t : Nat)
    (E F : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}) : Complex :=
  if (binaryMul (binaryDagger E.1) F.1).vector.xPart = 0 ∧
      (binaryMul (binaryDagger E.1) F.1).vector.zPart = 0 then
    binaryPhaseScalar (binaryMul (binaryDagger E.1) F.1).phase
  else
    0

/-- The scoped binary CSS Pauli family satisfies the indexed finite-Kraus KL scalar condition. -/
theorem scopedErrorFamily_indexedKnillLaflammeConditionWithScalar
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ) :
    Semantics.FiniteKrausFamily.IndexedKnillLaflammeConditionWithScalar
      (scopedErrorFamily (ι := ι) t)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (scopedErrorFamilyKLScalar (ι := ι) t) := by
  intro E F ψ hψ φ hφ
  dsimp [scopedErrorFamily, scopedErrorFamilyKLScalar]
  by_cases hzero :
      (binaryMul (binaryDagger E.1) F.1).vector.xPart = 0 ∧
      (binaryMul (binaryDagger E.1) F.1).vector.zPart = 0
  · have hphase := matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
      (E := E.1) (F := F.1) hzero.1 hzero.2 (ψ := ψ) (φ := φ)
    simpa [hzero] using hphase
  · have hnontrivial :
      (binaryMul (binaryDagger E.1) F.1).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E.1) F.1).vector.zPart ≠ 0 := by
        by_cases hx : (binaryMul (binaryDagger E.1) F.1).vector.xPart = 0
        · right
          intro hz
          exact hzero ⟨hx, hz⟩
        · exact Or.inl hx
    have hzeroME := matrixElement_zero_of_scopedByWeight_pair
      xCode zCode hdual hminX hminZ hbound E.2 F.2 hnontrivial hψ hφ
    simpa [hzero] using hzeroME

/-- The scoped binary CSS Pauli family satisfies the M2 same-space finite-Kraus KL predicate. -/
theorem scopedErrorFamily_sameSpaceKnillLaflammeCriterion
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ) :
    (scopedErrorFamily (ι := ι) t).sameSpaceKnillLaflammeCriterion
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual) := by
  exact
    ((Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
      (scopedErrorFamily (ι := ι) t)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)).2
        ⟨scopedErrorFamilyKLScalar (ι := ι) t,
          scopedErrorFamily_indexedKnillLaflammeConditionWithScalar
            xCode zCode hdual hminX hminZ hbound⟩)

/--
Vectors in the semantic binary CSS carrier are invariant under the concrete
support flip generated by any `X`-check codeword.
-/
theorem binaryCSSQuantumCodeOfDualLe_apply_flipSupport_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    {x : Word (ZMod 2) ι} (hx : x ∈ xCode.carrier)
    (bits : Semantics.Qubit.Bitstring ι) :
    ψ (Semantics.Qubit.flipSupport (binarySupport x) bits) = ψ bits := by
  have hfixed :
      toQubitOperator (cssXCheck x) ψ = ψ :=
    (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ).1 hψ
      (cssXCheck x) (Or.inl ⟨x, hx, rfl⟩)
  have hbits : toQubitOperator (cssXCheck x) ψ bits = ψ bits := by
    simpa using congrArg (fun φ : Semantics.Qubit.QubitRegister ι => φ bits) hfixed
  simpa [cssXCheck, xSupport, zSupport, Semantics.Qubit.zSupportPhase] using hbits

/-- Amplitude-weighted scoped binary-Pauli finite-Kraus noise. -/
noncomputable def scopedAmplitudeErrorFamily (t : Nat)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex) :
    Semantics.FiniteKrausFamily {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}
      (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι) :=
  (scopedErrorFamily (ι := ι) t).scale amp

@[simp]
theorem scopedAmplitudeErrorFamily_operator (t : Nat)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}) :
    (scopedAmplitudeErrorFamily (ι := ι) t amp).operator P =
      amp P • toQubitOperator P.1 :=
  rfl

/-- Amplitude normalization gives finite-Kraus completeness. -/
theorem scopedAmplitudeErrorFamily_complete
    {t : Nat}
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (hamp : ∑ P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t},
      star (amp P) * amp P = 1) :
    (scopedAmplitudeErrorFamily (ι := ι) t amp).Complete := by
  refine Semantics.FiniteKrausFamily.scale_complete_of_adjoint_square_sum
    (scopedErrorFamily (ι := ι) t) amp ?_
  ext ψ bits
  have hbits := congrArg (fun c : Complex => c * ψ bits) hamp
  simpa [scopedErrorFamily, toQubitOperator_adjoint_comp_self, Finset.sum_mul] using hbits

/-- The scoped binary CSS Pauli KL scalar condition transfers through amplitudes. -/
theorem scopedAmplitudeErrorFamily_indexedKnillLaflammeConditionWithScalar
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex) :
    Semantics.FiniteKrausFamily.IndexedKnillLaflammeConditionWithScalar
      (scopedAmplitudeErrorFamily (ι := ι) t amp)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (fun E F => star (amp E) * amp F * scopedErrorFamilyKLScalar (ι := ι) t E F) := by
  simpa [scopedAmplitudeErrorFamily] using
    (Semantics.FiniteKrausFamily.scale_indexedKnillLaflammeConditionWithScalar
      (E := scopedErrorFamily (ι := ι) t)
      (C := binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (amp := amp)
      (scalar := scopedErrorFamilyKLScalar (ι := ι) t)
      (scopedErrorFamily_indexedKnillLaflammeConditionWithScalar
        xCode zCode hdual hminX hminZ hbound))

/-- The amplitude-weighted scoped Pauli family satisfies the same-space KL predicate. -/
theorem scopedAmplitudeErrorFamily_sameSpaceKnillLaflammeCriterion
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex) :
    (scopedAmplitudeErrorFamily (ι := ι) t amp).sameSpaceKnillLaflammeCriterion
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual) := by
  exact
    ((Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
      (scopedAmplitudeErrorFamily (ι := ι) t amp)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)).2
        ⟨fun E F => star (amp E) * amp F *
            scopedErrorFamilyKLScalar (ι := ι) t E F,
          scopedAmplitudeErrorFamily_indexedKnillLaflammeConditionWithScalar
            xCode zCode hdual hminX hminZ hbound amp⟩)

/-- Normalized amplitude-weighted scoped Pauli finite-Kraus noise has a recovery. -/
theorem scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (hamp : ∑ P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t},
      star (amp P) * amp P = 1) :
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
      Semantics.FiniteKrausCorrectable
        {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}
        (Semantics.Qubit.QubitRegister ι)
        (Semantics.Qubit.QubitRegister ι)
        (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
        (scopedAmplitudeErrorFamily (ι := ι) t amp)
        recovery := by
  exact
    Semantics.FiniteKrausFamily.exists_recovery_of_sameSpaceKnillLaflammeCriterion
      (scopedAmplitudeErrorFamily (ι := ι) t amp)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (scopedAmplitudeErrorFamily_complete (ι := ι) amp hamp)
      (scopedAmplitudeErrorFamily_sameSpaceKnillLaflammeCriterion
        xCode zCode hdual hminX hminZ hbound amp)

/--
Normalized amplitude-weighted scoped Pauli noise has an ordinary bundled-channel
semantic recovery for the induced CPTP channel.
-/
theorem scopedAmplitudeErrorFamily_exists_correctable_toQuantumChannel
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (hamp : ∑ P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t},
      star (amp P) * amp P = 1) :
    ∃ hnoise : (scopedAmplitudeErrorFamily (ι := ι) t amp).Complete,
      ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.Correctable
          (Semantics.Qubit.QubitRegister ι)
          (Semantics.Qubit.QubitRegister ι)
          (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
          ((scopedAmplitudeErrorFamily (ι := ι) t amp).toQuantumChannel hnoise)
          recovery := by
  exact
    (Semantics.exists_finiteKrausCorrectable_iff_exists_correctable_toQuantumChannel
      (C := binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (noise := scopedAmplitudeErrorFamily (ι := ι) t amp)).1
      (scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
        xCode zCode hdual hminX hminZ hbound amp hamp)

/--
The `Z` checks force every carrier vector to vanish outside the classical dual
`zCode.dual`.
-/
theorem binaryCSSQuantumCodeOfDualLe_apply_eq_zero_of_not_mem_zDual
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    {bits : Semantics.Qubit.Bitstring ι}
    (hbits : bitstringWordEquiv ι bits ∉ zCode.dual.carrier) :
    ψ bits = 0 := by
  rcases exists_carrier_wordPairing_ne_zero_of_not_mem_dual zCode hbits with
    ⟨z, hz, hpair⟩
  have hfixed :
      toQubitOperator (cssZCheck z) ψ = ψ :=
    (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ).1 hψ
      (cssZCheck z) (Or.inr ⟨z, hz, rfl⟩)
  have hbitsFixed : toQubitOperator (cssZCheck z) ψ bits = ψ bits := by
    simpa using congrArg (fun φ : Semantics.Qubit.QubitRegister ι => φ bits) hfixed
  have hphase_mul :
      Semantics.Qubit.zSupportPhase (binarySupport z) bits * ψ bits = ψ bits := by
    simpa [cssZCheck, xSupport, zSupport] using hbitsFixed
  have hpair' :
      wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits) ≠ 0 := by
    intro hzero
    exact hpair (by simpa [wordPairing_apply, dotProduct_comm] using hzero)
  have hphase_ne_one :
      Semantics.Qubit.zSupportPhase (binarySupport z) bits ≠ 1 := by
    intro hphase
    exact hpair' ((zSupportPhase_eq_one_iff_wordPairing_eq_zero z bits).1 hphase)
  have hfactor_ne_zero :
      Semantics.Qubit.zSupportPhase (binarySupport z) bits - 1 ≠ 0 := by
    intro hzero
    exact hphase_ne_one (sub_eq_zero.mp hzero)
  have hmul_zero :
      (Semantics.Qubit.zSupportPhase (binarySupport z) bits - 1) * ψ bits = 0 := by
    rw [sub_mul, one_mul, hphase_mul, sub_self]
  exact (mul_eq_zero.mp hmul_zero).resolve_left hfactor_ne_zero

/--
Carrier amplitudes agree on equal classes of the logical-basis quotient
`zCode.dual / xCode`.
-/
theorem binaryCSSQuantumCodeOfDualLe_apply_eq_of_quotient_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    {u v : zCode.dual.carrier}
    (h : Submodule.Quotient.mk u =
      (Submodule.Quotient.mk v : binaryCSSLogicalBasisQuotient xCode zCode)) :
    ψ ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
      ψ ((bitstringWordEquiv ι).symm (v : Word (ZMod 2) ι)) := by
  have hdiff :
      u - v ∈ binaryCSSXCodeInZDual xCode zCode :=
    (Submodule.Quotient.eq (binaryCSSXCodeInZDual xCode zCode)).1 h
  have hx : ((u : Word (ZMod 2) ι) - (v : Word (ZMod 2) ι)) ∈ xCode.carrier := by
    change ((u - v : zCode.dual.carrier) : Word (ZMod 2) ι) ∈ xCode.carrier at hdiff
    exact hdiff
  have hbits :
      Semantics.Qubit.flipSupport
          (binarySupport ((u : Word (ZMod 2) ι) - (v : Word (ZMod 2) ι)))
          ((bitstringWordEquiv ι).symm (v : Word (ZMod 2) ι)) =
        (bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι) := by
    apply (bitstringWordEquiv ι).injective
    rw [bitstringWordEquiv_flipSupport]
    simp [sub_eq_add_neg, add_left_comm]
  have hflip :=
    binaryCSSQuantumCodeOfDualLe_apply_flipSupport_eq
      xCode zCode hdual hψ hx ((bitstringWordEquiv ι).symm (v : Word (ZMod 2) ι))
  simpa [hbits] using hflip

/--
Reconstruct a qubit-register vector from amplitudes on the algebraic logical
basis quotient: labels outside `zCode.dual` get amplitude `0`, and labels in
the dual are evaluated at their quotient class.
-/
noncomputable def binaryCSSLogicalBasisQuotientToQubitRegister
    (xCode zCode : LinearCode (ZMod 2) ι) :
    EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) →ₗ[Complex]
      Semantics.Qubit.QubitRegister ι where
  toFun φ := WithLp.toLp 2 fun bits =>
    if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
      φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
    else
      0
  map_add' := by
    intro φ χ
    ext bits
    change
      (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          (φ + χ) (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0) =
        (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0) +
        (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          χ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0)
    by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
    · rw [dif_pos hbits, dif_pos hbits, dif_pos hbits]
      rfl
    · rw [dif_neg hbits, dif_neg hbits, dif_neg hbits]
      simp
  map_smul' := by
    intro a φ
    ext bits
    change
      (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          (a • φ) (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0) =
        a *
          (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
            φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
          else
            0)
    by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
    · rw [dif_pos hbits, dif_pos hbits]
      rfl
    · rw [dif_neg hbits, dif_neg hbits]
      simp

omit [DecidableEq ι] in
@[simp] theorem binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    (xCode zCode : LinearCode (ZMod 2) ι)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {bits : Semantics.Qubit.Bitstring ι}
    (hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits =
      φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩) := by
  change
    (if h : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
        φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, h⟩)
      else
        0) =
      φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
  rw [dif_pos hbits]

omit [DecidableEq ι] in
@[simp] theorem binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
    (xCode zCode : LinearCode (ZMod 2) ι)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {bits : Semantics.Qubit.Bitstring ι}
    (hbits : bitstringWordEquiv ι bits ∉ zCode.dual.carrier) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits = 0 := by
  change
    (if h : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
        φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, h⟩)
      else
        0) =
      0
  rw [dif_neg hbits]

/--
The reconstructed quotient vector is invariant under `X`-check support flips.
-/
theorem binaryCSSLogicalBasisQuotientToQubitRegister_apply_flipSupport_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {x : Word (ZMod 2) ι} (hx : x ∈ xCode.carrier)
    (bits : Semantics.Qubit.Bitstring ι) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ
        (Semantics.Qubit.flipSupport (binarySupport x) bits) =
      binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits := by
  have hxDual : x ∈ zCode.dual.carrier :=
    LinearCode.le_dual_of_le_dual xCode zCode hdual hx
  by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
  · have hflip :
        bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) ∈
          zCode.dual.carrier := by
      rw [bitstringWordEquiv_flipSupport]
      exact zCode.dual.carrier.add_mem hbits hxDual
    rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode φ hflip,
      binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode φ hbits]
    apply congrArg φ
    rw [Submodule.Quotient.eq]
    change
      (bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) -
          bitstringWordEquiv ι bits) ∈ xCode.carrier
    simpa [bitstringWordEquiv_flipSupport, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hx
  · have hflip :
        bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) ∉
          zCode.dual.carrier := by
      intro hflipMem
      apply hbits
      have hsum : bitstringWordEquiv ι bits + x ∈ zCode.dual.carrier := by
        simpa [bitstringWordEquiv_flipSupport] using hflipMem
      have hsub : bitstringWordEquiv ι bits + x - x ∈ zCode.dual.carrier :=
        zCode.dual.carrier.sub_mem hsum hxDual
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
    rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode φ hflip,
      binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode φ hbits]

/--
The reconstructed quotient vector is fixed by every `Z` check from `zCode`.
-/
theorem zSupportPhase_mul_binaryCSSLogicalBasisQuotientToQubitRegister_apply
    (xCode zCode : LinearCode (ZMod 2) ι)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {z : Word (ZMod 2) ι} (hz : z ∈ zCode.carrier)
    (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport z) bits *
        binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits =
      binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits := by
  by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
  · have hpair :
        wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits) = 0 := by
      have horth := zCode.orthogonal_of_mem_dual hbits hz
      simpa [wordPairing_apply, dotProduct_comm] using horth
    have hphase : Semantics.Qubit.zSupportPhase (binarySupport z) bits = 1 :=
      (zSupportPhase_eq_one_iff_wordPairing_eq_zero z bits).2 hpair
    simp [hphase]
  · rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode φ hbits]
    simp

theorem binaryCSSLogicalBasisQuotientToQubitRegister_mem_carrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode)) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ ∈
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier := by
  rw [mem_binaryCSSQuantumCodeOfDualLe_carrier]
  intro P hP
  ext bits
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · simpa [cssXCheck, xSupport, zSupport, Semantics.Qubit.zSupportPhase] using
      binaryCSSLogicalBasisQuotientToQubitRegister_apply_flipSupport_eq
        xCode zCode hdual φ hx bits
  · simpa [cssZCheck, xSupport, zSupport] using
      zSupportPhase_mul_binaryCSSLogicalBasisQuotientToQubitRegister_apply
        xCode zCode φ hz bits

/-- Reconstructed quotient amplitudes as an element of the actual CSS carrier. -/
noncomputable def binaryCSSLogicalBasisQuotientToCarrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) →ₗ[Complex]
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier :=
  (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode).codRestrict
    (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier
    (binaryCSSLogicalBasisQuotientToQubitRegister_mem_carrier xCode zCode hdual)

/--
Evaluate a carrier vector on quotient classes. This is well-defined because
carrier amplitudes agree on `xCode`-cosets inside `zCode.dual`.
-/
noncomputable def binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier →ₗ[Complex]
      EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) where
  toFun ψ := WithLp.toLp 2 fun q =>
    Quotient.liftOn q
      (fun u : zCode.dual.carrier =>
        (ψ : Semantics.Qubit.QubitRegister ι)
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)))
      (fun u v h => by
        exact binaryCSSQuantumCodeOfDualLe_apply_eq_of_quotient_eq
          xCode zCode hdual ψ.2 (Quotient.sound h))
  map_add' := by
    intro ψ φ
    ext q
    refine Submodule.Quotient.induction_on
      (p := binaryCSSXCodeInZDual xCode zCode) q ?_
    intro u
    change
      (↑(ψ + φ) : Semantics.Qubit.QubitRegister ι)
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
        (ψ : Semantics.Qubit.QubitRegister ι)
            ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) +
          (φ : Semantics.Qubit.QubitRegister ι)
            ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι))
    rfl
  map_smul' := by
    intro a ψ
    ext q
    refine Submodule.Quotient.induction_on
      (p := binaryCSSXCodeInZDual xCode zCode) q ?_
    intro u
    change
      (↑(a • ψ) : Semantics.Qubit.QubitRegister ι)
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
        a *
          (ψ : Semantics.Qubit.QubitRegister ι)
            ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι))
    rfl

@[simp] theorem binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient_apply_mk
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (ψ : (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (u : zCode.dual.carrier) :
    binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient xCode zCode hdual ψ
        (Submodule.Quotient.mk u : binaryCSSLogicalBasisQuotient xCode zCode) =
      (ψ : Semantics.Qubit.QubitRegister ι)
        ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) := by
  rfl

/--
The actual common-fixed binary CSS carrier is linearly equivalent to amplitudes
indexed by the logical-basis quotient `zCode.dual / xCode`.
-/
noncomputable def binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier ≃ₗ[Complex]
      EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) where
  toFun ψ := binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
    xCode zCode hdual ψ
  invFun φ := binaryCSSLogicalBasisQuotientToCarrier xCode zCode hdual φ
  left_inv := by
    intro ψ
    ext bits
    by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
    · change
        binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode
            (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
              xCode zCode hdual ψ) bits =
          (ψ : Semantics.Qubit.QubitRegister ι) bits
      rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode
        (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient xCode zCode hdual ψ)
        hbits]
      rw [binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient_apply_mk]
      simp
    · have hzero :=
        binaryCSSQuantumCodeOfDualLe_apply_eq_zero_of_not_mem_zDual
          xCode zCode hdual ψ.2 hbits
      change
        binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode
            (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
              xCode zCode hdual ψ) bits =
          (ψ : Semantics.Qubit.QubitRegister ι) bits
      rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode
        (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient xCode zCode hdual ψ)
        hbits]
      simp [hzero]
  right_inv := by
    intro φ
    ext q
    refine Submodule.Quotient.induction_on
      (p := binaryCSSXCodeInZDual xCode zCode) q ?_
    intro u
    rw [binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient_apply_mk]
    have hu :
        bitstringWordEquiv ι ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) ∈
          zCode.dual.carrier := by
      rw [Equiv.apply_symm_apply]
      exact u.property
    change
      binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
        φ (Submodule.Quotient.mk u)
    rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode φ hu]
    apply congrArg (fun q : binaryCSSLogicalBasisQuotient xCode zCode => φ q)
    congr 1
    apply Subtype.ext
    simp
  map_add' := by
    intro ψ φ
    exact (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
      xCode zCode hdual).map_add ψ φ
  map_smul' := by
    intro a ψ
    exact (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
      xCode zCode hdual).map_smul a ψ

/--
Dimension formula for the actual semantic binary CSS common-fixed carrier.
-/
theorem binaryCSSQuantumCodeOfDualLe_finrank_carrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank Complex
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier =
    2 ^ (Length (ZMod 2) ι - Dimension xCode - Dimension zCode) := by
  rw [(binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
    xCode zCode hdual).finrank_eq]
  rw [finrank_euclideanSpace]
  rw [Module.card_eq_pow_finrank
    (K := ZMod 2) (V := binaryCSSLogicalBasisQuotient xCode zCode)]
  rw [finrank_binaryCSSLogicalBasisQuotient_eq xCode zCode hdual]
  norm_num [ZMod.card]

/--
The scoped binary CSS semantic code inherits concrete operator commutation from
dual containment.
-/
theorem binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
      ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode →
        toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P :=
  pairwise_toQubitOperator_commute_of_commutes
    (binaryCSSCheckSet_pairwise_commutes_of_dual_le xCode zCode hdual)

/--
Raw binary CSS data satisfying dual containment realizes a semantic quantum-code
carrier whose elements are exactly the common fixed vectors of the generated
binary CSS checks, and those checks commute as concrete qubit-register
operators.
-/
theorem exists_binaryCSSSemanticQuantumCodeOfDualLe
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∃ C : Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι),
      (∀ ψ, ψ ∈ C.carrier ↔
        ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode → toQubitOperator P ψ = ψ) ∧
      (∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
        ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode →
          toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P) := by
  refine ⟨binaryCSSQuantumCodeOfDualLe xCode zCode hdual, ?_, ?_⟩
  · intro ψ
    exact mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ
  · exact binaryCSSQuantumCodeOfDualLe_pairwise_toQubitOperator_commute xCode zCode hdual

end PauliSymplectic

namespace ChainComplexData

/--
A low-weight nonzero pure `X` word fails to commute with some middle-boundary
`Z` check when the middle-boundary code's dual minimum distance is larger than
the word weight.
-/
theorem exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_middleBoundaryDualMinimumDistance
    {ι κ C2 : Type u} [Fintype ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2)
    {dX : Nat}
    (hminX : MinimumDistance K.middleBoundaryCode.dual dX)
    {x : Word (ZMod 2) ι} (hx0 : x ≠ 0) (hxlt : HammingWeight x < dX) :
    ∃ z, z ∈ K.middleBoundaryCode.carrier ∧
      ¬ PauliSymplectic.Commutes
        (PauliSymplectic.cssXCheck x) (PauliSymplectic.cssZCheck z) := by
  exact
    PauliSymplectic.exists_z_check_not_commutes_cssXCheck_of_hammingWeight_lt_dualMinimumDistance
      K.middleBoundaryCode hminX hx0 hxlt

/--
A low-weight nonzero pure `Z` word fails to commute with some first-coboundary
`X` check when the first-coboundary code's dual minimum distance is larger than
the word weight.
-/
theorem exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_firstCoboundaryDualMinimumDistance
    {ι κ C2 : Type u} [Fintype ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2)
    {dZ : Nat}
    (hminZ : MinimumDistance K.firstCoboundaryCheckCode.dual dZ)
    {z : Word (ZMod 2) ι} (hz0 : z ≠ 0) (hzlt : HammingWeight z < dZ) :
    ∃ x, x ∈ K.firstCoboundaryCheckCode.carrier ∧
      ¬ PauliSymplectic.Commutes
        (PauliSymplectic.cssZCheck z) (PauliSymplectic.cssXCheck x) := by
  exact
    PauliSymplectic.exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
      K.firstCoboundaryCheckCode hminZ hz0 hzlt

/--
Binary finite-coordinate chain-complex data determines the CSS code generated
by its coboundary X-check code and middle-boundary Z-check code.
-/
noncomputable def binaryCSSCode
    {ι κ C2 : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2) :
    CSSCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι) where
  xCode := K.firstCoboundaryCheckCode
  zCode := K.middleBoundaryCode
  stabilizer :=
    PauliSymplectic.binaryCSSStabilizerCodeOfDualLe K.firstCoboundaryCheckCode
      K.middleBoundaryCode K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual
  orthogonal := K.firstCoboundaryCheckCode_orthogonal_middleBoundaryCode

/--
For a finite based binary chain complex, the associated CSS code has pure-X
logical quotient equivalent to middle cohomology and pure-Z logical quotient
equivalent to middle homology, with the displayed equations recording the
action on representatives. Exact minima in the two logical sectors give
algebraic CSS distance `min dX dZ`.

This uses the source's transpose orientation directly and does not identify
homology and cohomology through a Hamming-weight-preserving pairing.

[BE20, Sections II.A-II.B]
-/
theorem binaryCSSCode_homologicalDistance
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) (Word (ZMod 2) lambda))
    {dX dZ : Nat}
    (hX : PureXLogicalMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode dX)
    (hZ : PureZLogicalMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode dZ) :
    (∀ x : K.middleBoundaryCode.dual.carrier,
      K.pureXLogicalQuotientEquivMiddleCohomology (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (K.middleBoundaryDualEquivMiddleCocycleCode x)) ∧
    (∀ z : K.firstCoboundaryCheckCode.dual.carrier,
      K.pureZLogicalQuotientEquivMiddleHomology (Submodule.Quotient.mk z) =
        Submodule.Quotient.mk (K.firstCoboundaryDualEquivMiddleCycleCode z)) ∧
    AlgebraicCSSMinimumDistance
      (K.binaryCSSCode).xCode (K.binaryCSSCode).zCode (min dX dZ) := by
  exact ⟨K.pureXLogicalQuotientEquivMiddleCohomology_mk,
    K.pureZLogicalQuotientEquivMiddleHomology_mk,
    algebraicCSSMinimumDistance_of_sector_minima hX hZ⟩

/--
The semantic carrier dimension of the binary CSS code generated by a
finite-coordinate chain complex is `2` to the middle-homology dimension.
-/
theorem binaryCSSCode_finrank_stabilizer_code_carrier_eq_pow_finrank_middleHomology
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) K.middleHomology := by
  rw [binaryCSSCode]
  change Module.finrank Complex
      (PauliSymplectic.binaryCSSQuantumCodeOfDualLe K.firstCoboundaryCheckCode
        K.middleBoundaryCode K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual).carrier =
    2 ^ Module.finrank (ZMod 2) K.middleHomology
  rw [PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier]
  rw [K.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology]

end ChainComplexData
end Coding
end QEC
