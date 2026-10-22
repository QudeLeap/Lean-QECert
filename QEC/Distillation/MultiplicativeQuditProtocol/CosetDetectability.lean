import QEC.Distillation.MultiplicativeQuditProtocol.CSSShortening
import QEC.Semantics.ErrorCorrection.Detectability

/-!
# Local matrix elements of the actual shortened coset encoder

Complement separation removes off-diagonal terms. Local surjectivity of the
shortened kernel then makes the remaining diagonal sum independent of the
logical label by translation, proving semantic error detectability.
-/

noncomputable section

namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput

open Coding Semantics
open scoped BigOperators

universe u

variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]

local instance : DecidableEq Logical := Classical.decEq _
local instance : DecidableEq (Word F Logical) := Classical.decEq _
local instance : Fintype (Word F Logical) := Fintype.ofFinite _

/-- Once complementary coordinates distinguish all coset summands, a local
operator has no off-diagonal logical matrix elements. -/
theorem coset_inner_operator_eq_zero (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (u v : Word F Logical) (huv : u ≠ v) :
    inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet v)) = 0 := by
  unfold shortenedCosetKet
  rw [map_smul, map_sum, inner_smul_left, inner_smul_right, inner_sum]
  have hz : ∀ k : data.H0,
      inner Complex (∑ h : data.H0, registerBasisKet (data.shortenedCosetLabel u h))
        (E (registerBasisKet (data.shortenedCosetLabel v k))) = 0 := by
    intro k
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro h _
    apply hlocal
    by_contra! hbad
    exact huv (hsep u v h k hbad).1
  simp_rw [hz]
  simp

/-- Complement separation reduces each diagonal logical matrix element to
the actual single sum of local computational-basis expectations. -/
theorem coset_inner_operator_eq_diagonal_sum (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (u : Word F Logical) :
    inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet u)) =
      star (cosetNormalization data.H0) * cosetNormalization data.H0 *
        ∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
          (E (registerBasisKet (data.shortenedCosetLabel u h))) := by
  unfold shortenedCosetKet
  rw [map_smul, map_sum, inner_smul_left, inner_smul_right, inner_sum, ← mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_inner]
  apply Finset.sum_eq_single k
  · intro h _ hne
    apply hlocal
    by_contra! hbad
    exact hne (hsep u u h k hbad).2
  · simp

/-- Translation of the actual kernel sum removes the logical representative
from every locally supported diagonal expectation. -/
theorem coset_diagonal_sum_eq_zero_label (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (honto : Function.Surjective (fun h : data.H0 =>
      fun j : S => data.puncture h.val.val j.val))
    (hdiag : ∀ x y : Word F data.PivotComplement,
      (∀ j, j ∈ S → x j = y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet x)) =
          inner Complex (registerBasisKet y) (E (registerBasisKet y)))
    (u : Word F Logical) :
    (∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
      (E (registerBasisKet (data.shortenedCosetLabel u h)))) =
    ∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel 0 h))
      (E (registerBasisKet (data.shortenedCosetLabel 0 h))) := by
  obtain ⟨shift, hshift⟩ := honto (fun j => data.puncturedLogicalWord u j.val)
  apply Fintype.sum_equiv (Equiv.addRight shift)
  intro h
  apply hdiag
  intro j hj
  have hs := congrFun hshift ⟨j, hj⟩
  change data.puncture shift.val.val j = data.puncturedLogicalWord u j at hs
  change data.puncturedLogicalWord u j + data.puncture h.val.val j =
    data.puncturedLogicalWord 0 j + data.puncture (h + shift).val.val j
  have hz : data.puncturedLogicalWord 0 = 0 := by
    simp [puncturedLogicalWord, systematicLogicalWord]
  rw [hz]
  change data.puncturedLogicalWord u j + h.val.val j.val =
    0 + (h.val.val j.val + shift.val.val j.val)
  change shift.val.val j.val = data.puncturedLogicalWord u j at hs
  rw [hs]
  simp [add_comm]

/-- Complement separation and local interpolation prove detectability on the
entire semantic range carrier, not only on its computational codewords. -/
theorem detectableOn_of_coset_locality (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (honto : Function.Surjective (fun h : data.H0 =>
      fun j : S => data.puncture h.val.val j.val))
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (hdiag : ∀ x y : Word F data.PivotComplement,
      (∀ j, j ∈ S → x j = y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet x)) =
          inner Complex (registerBasisKet y) (E (registerBasisKet y))) :
    DetectableOn data.quantumCode E := by
  let c := inner Complex (data.shortenedCosetKet 0) (E (data.shortenedCosetKet 0))
  have hmatrix (u v : Word F Logical) :
      inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet v)) =
        c * inner Complex (data.shortenedCosetKet u) (data.shortenedCosetKet v) := by
    by_cases huv : u = v
    · subst v
      rw [data.shortenedCosetKet_inner, if_pos rfl, mul_one]
      change _ = inner Complex (data.shortenedCosetKet 0) (E (data.shortenedCosetKet 0))
      rw [data.coset_inner_operator_eq_diagonal_sum E S hsep hlocal u,
        data.coset_inner_operator_eq_diagonal_sum E S hsep hlocal 0,
        data.coset_diagonal_sum_eq_zero_label E S honto hdiag u]
    · rw [data.coset_inner_operator_eq_zero E S hsep hlocal u v huv,
        data.shortenedCosetKet_inner, if_neg huv, mul_zero]
  refine ⟨c, ?_⟩
  rintro x ⟨psi, rfl⟩ y ⟨chi, rfl⟩
  change inner Complex
      (∑ u : Word F Logical, psi u • data.shortenedCosetKet u)
      (E (∑ v : Word F Logical, chi v • data.shortenedCosetKet v)) =
    c * inner Complex
      (∑ u : Word F Logical, psi u • data.shortenedCosetKet u)
      (∑ v : Word F Logical, chi v • data.shortenedCosetKet v)
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  rw [hmatrix]
  ring

end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
