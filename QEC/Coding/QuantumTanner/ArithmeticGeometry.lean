import QEC.Coding.ExpanderCodes.QuadraticTorusIndex
import QEC.Coding.QuantumTanner.Goodness

/-!
# Finite quaternion arithmetic square geometry

The two generator sets below have their injectivity, inverse permutations,
equal degree, and total nonconjugacy proved from the constant-field quaternion
construction [DEL21, Section 6.2]. The square complex is then constructed by
its four corners [LZ22, Section 3.1]. No PSL₂ identification, cofinal family,
or Ramanujan estimate is assumed to follow merely from these finite objects.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.ArithmeticGeometry

open QEC.Coding.ExpanderCodes.QuaternionGenerators

universe v

variable {F K : Type v} [Field F] [Field K] [Fintype K]

instance finiteProjectiveGroup (epsilon y : K) : Fintype (ProjectiveGroup epsilon y) := by
  classical
  letI : Finite (Model epsilon y) := Finite.of_equiv (K × K × K × K)
    (QuaternionAlgebra.equivProd epsilon 0 (1 + y)).symm
  exact Fintype.ofFinite _

abbrev LeftIndex (f : F →+* K) (epsilon : F) (y : K)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) := constantLeftSet f epsilon y hY hOne

abbrev RightIndex (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :=
  constantRightSet f epsilon y hEpsilon hY hOne

instance finiteLeftIndex (f : F →+* K) (epsilon : F) (y : K)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Fintype (LeftIndex f epsilon y hY hOne) := by
  classical
  exact Fintype.ofFinite _

instance finiteRightIndex (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Fintype (RightIndex f epsilon y hEpsilon hY hOne) := by
  classical
  exact Fintype.ofFinite _

/-- Inversion on an actual inverse-closed subset is an involutive permutation. -/
def inversePerm {H : Type*} [Group H] (S : Set H)
    (hInverse : ∀ g ∈ S, g⁻¹ ∈ S) : Equiv.Perm S where
  toFun g := ⟨g.val⁻¹, hInverse g.val g.property⟩
  invFun g := ⟨g.val⁻¹, hInverse g.val g.property⟩
  left_inv g := by apply Subtype.ext; simp
  right_inv g := by apply Subtype.ext; simp

def leftInverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Equiv.Perm (LeftIndex f epsilon y hY hOne) :=
  inversePerm _ (fun _ hg => constantLeftSet_inv_mem f epsilon y hEpsilon hY hOne hg)

def rightInverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Equiv.Perm (RightIndex f epsilon y hEpsilon hY hOne) :=
  inversePerm _ (fun _ hg => constantRightSet_inv_mem f epsilon y hEpsilon hY hOne hg)

theorem leftIndex_card (f : F →+* K) (epsilon : F) (y : K) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Fintype.card (LeftIndex f epsilon y hY hOne) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_constant_conjugacySet f epsilon y hNonSquare hEpsilon hY hOne hTwo

theorem rightIndex_card (f : F →+* K) (epsilon : F) (y : K) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Fintype.card (RightIndex f epsilon y hEpsilon hY hOne) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_constant_prime_conjugacySet f epsilon y hNonSquare hEpsilon hY hOne hTwo

/-- The four-corner square complex of the two concrete arithmetic generator sets. -/
def squareComplex (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    LeftRightCayleySquareComplex (ProjectiveGroup (f epsilon) y)
      (LeftIndex f epsilon y hY hOne) (RightIndex f epsilon y hEpsilon hY hOne)
      (CayleySquare
        (Subtype.val : LeftIndex f epsilon y hY hOne → ProjectiveGroup (f epsilon) y)
        (Subtype.val : RightIndex f epsilon y hEpsilon hY hOne → ProjectiveGroup (f epsilon) y)) :=
  cayleySquareComplex
    (Subtype.val : LeftIndex f epsilon y hY hOne → ProjectiveGroup (f epsilon) y)
    (Subtype.val : RightIndex f epsilon y hEpsilon hY hOne → ProjectiveGroup (f epsilon) y)
    (leftInverse f epsilon y hEpsilon hY hOne)
    (rightInverse f epsilon y hEpsilon hY hOne)
    Subtype.val_injective Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
    (fun g a b => constantSets_total_nonconjugacy f epsilon y hEpsilon hY hOne hTwo
      a.property b.property g)

/-- The constructed incidence links satisfy the transport laws used in the distance proof. -/
theorem squareComplex_hasCayleyLinkIdentities (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    (squareComplex f epsilon y hEpsilon hY hOne hTwo).HasCayleyLinkIdentities := by
  unfold squareComplex
  exact cayleySquareComplex_hasCayleyLinkIdentities
    (Subtype.val : LeftIndex f epsilon y hY hOne → ProjectiveGroup (f epsilon) y)
    (Subtype.val : RightIndex f epsilon y hEpsilon hY hOne → ProjectiveGroup (f epsilon) y)
    (leftInverse f epsilon y hEpsilon hY hOne)
    (rightInverse f epsilon y hEpsilon hY hOne)
    Subtype.val_injective Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
    (fun g a b => constantSets_total_nonconjugacy f epsilon y hEpsilon hY hOne hTwo
      a.property b.property g)

/-- The same four-corner geometry with constant-field indices, so its local
code coordinates and inverse permutations are fixed across specializations. -/
def indexedSquareComplex [Fintype F] (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    LeftRightCayleySquareComplex (ProjectiveGroup (f epsilon) y)
      (TorusIndex epsilon) (TorusIndex epsilon)
      (CayleySquare (indexedLeft f epsilon y hTwoF hY hOne hTwo)
        (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo)) :=
  cayleySquareComplex
    (indexedLeft f epsilon y hTwoF hY hOne hTwo)
    (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (indexedLeft_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeft_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (fun g a b => indexed_total_nonconjugacy f epsilon y hEpsilon hTwoF hY hOne hTwo a b g)

theorem indexedSquareComplex_hasCayleyLinkIdentities [Fintype F]
    (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    (indexedSquareComplex f epsilon y hEpsilon hTwoF hY hOne hTwo).HasCayleyLinkIdentities := by
  unfold indexedSquareComplex
  exact cayleySquareComplex_hasCayleyLinkIdentities
    (indexedLeft f epsilon y hTwoF hY hOne hTwo)
    (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (indexedLeft_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeft_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (fun g a b => indexed_total_nonconjugacy f epsilon y hEpsilon hTwoF hY hOne hTwo a b g)

end QEC.Coding.QuantumTanner.ArithmeticGeometry
