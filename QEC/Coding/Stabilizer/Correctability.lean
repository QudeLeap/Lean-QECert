import QEC.Coding.Stabilizer.Detectability

/-!
# Stabilizer error-set correctability

This module connects complete finite Kraus families of scaled binary Pauli
operators to the support-sensitive stabilizer pair-product criterion.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PauliSymplectic

open scoped ComplexConjugate

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The finite Kraus family `K_a = amp a * E_a` represented on the qubit register. -/
def binaryPauliKrausFamily {α : Type v} [Fintype α]
    (E : α → Binary ι) (amp : α → Complex) :
    Semantics.FiniteKrausFamily α
      (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι) := by
  classical
  exact { operator := fun a => amp a • toQubitOperator (E a) }

@[simp]
theorem binaryPauliKrausFamily_operator {α : Type v} [Fintype α]
    (E : α → Binary ι) (amp : α → Complex) (a : α) :
    (binaryPauliKrausFamily E amp).operator a = amp a • toQubitOperator (E a) := by
  classical
  rfl

private theorem inner_toQubitOperator_pair_eq_relative
    (A B : Binary ι) (x y : Semantics.Qubit.QubitRegister ι) :
    inner Complex (toQubitOperator A x) (toQubitOperator B y) =
      inner Complex x (toQubitOperator (binaryMul (binaryDagger A) B) y) := by
  classical
  calc
    inner Complex (toQubitOperator A x) (toQubitOperator B y) =
        inner Complex x
          (LinearMap.adjoint (toQubitOperator A) (toQubitOperator B y)) := by
      simpa using
        (LinearMap.adjoint_inner_right (𝕜 := Complex) (toQubitOperator A) x
          (toQubitOperator B y)).symm
    _ = inner Complex x (toQubitOperator (binaryMul (binaryDagger A) B) y) := by
      rw [adjoint_toQubitOperator_eq_binaryDagger, toQubitOperator_binaryMul]
      rfl

end PauliSymplectic

namespace StabilizerCode

open PauliSymplectic

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/--
The same-space Knill-Laflamme criterion for a scaled binary Pauli Kraus family
is exactly the stabilizer pair-product criterion on its nonzero-amplitude
support.
-/
theorem binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
    {α : Type v} [Fintype α]
    (Q : SourceValidBinary ι) (E : α → Binary ι) (amp : α → Complex) :
    (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion Q.1.code ↔
      ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
        Q.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (E a)) (E b)) ∨
          ¬ Q.1.InBinaryNormalizer
            (binaryMul (binaryDagger (E a)) (E b)) := by
  classical
  constructor
  · intro hKL
    rcases
        ((binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
          Q.1.code).1 hKL with
      ⟨scalar, hscalar⟩
    intro a b ha hb
    apply
      (detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
        Q (binaryMul (binaryDagger (E a)) (E b))).1
    refine ⟨scalar a b / (star (amp a) * amp b), ?_⟩
    intro x hx y hy
    have hscale_ne : star (amp a) * amp b ≠ 0 :=
      mul_ne_zero (star_ne_zero.mpr ha) hb
    have hab := hscalar a b x hx y hy
    have hscaled :
        (star (amp a) * amp b) *
            inner Complex x
              (toQubitOperator (binaryMul (binaryDagger (E a)) (E b)) y) =
          scalar a b * inner Complex x y := by
      calc
        (star (amp a) * amp b) *
              inner Complex x
                (toQubitOperator (binaryMul (binaryDagger (E a)) (E b)) y) =
            inner Complex
              ((binaryPauliKrausFamily E amp).operator a x)
              ((binaryPauliKrausFamily E amp).operator b y) := by
                rw [binaryPauliKrausFamily_operator, binaryPauliKrausFamily_operator]
                rw [← inner_toQubitOperator_pair_eq_relative]
                simp
                ring
        _ = scalar a b * inner Complex x y := hab
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hscale_ne).2
    simpa [mul_comm] using hscaled
  · intro hpairs
    have hscalarExists :
        ∀ a b : α, ∃ c : Complex,
          amp a ≠ 0 → amp b ≠ 0 →
            Semantics.DetectableOnWithScalar Q.1.code
              (toQubitOperator (binaryMul (binaryDagger (E a)) (E b))) c := by
      intro a b
      by_cases ha : amp a = 0
      · exact ⟨0, fun ha' _ => False.elim (ha' ha)⟩
      by_cases hb : amp b = 0
      · exact ⟨0, fun _ hb' => False.elim (hb' hb)⟩
      rcases
          (detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
            Q (binaryMul (binaryDagger (E a)) (E b))).2 (hpairs a b ha hb) with
        ⟨c, hc⟩
      exact ⟨c, fun _ _ => hc⟩
    choose scalar hscalar using hscalarExists
    rw [(binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
      Q.1.code]
    refine ⟨fun a b => star (amp a) * amp b * scalar a b, ?_⟩
    intro a b x hx y hy
    by_cases ha : amp a = 0
    · simp [ha]
    by_cases hb : amp b = 0
    · simp [hb]
    calc
      inner Complex
          ((binaryPauliKrausFamily E amp).operator a x)
          ((binaryPauliKrausFamily E amp).operator b y) =
          (star (amp a) * amp b) *
            inner Complex (toQubitOperator (E a) x) (toQubitOperator (E b) y) := by
              rw [binaryPauliKrausFamily_operator, binaryPauliKrausFamily_operator]
              simp
              ring
      _ = (star (amp a) * amp b) *
            inner Complex x
              (toQubitOperator (binaryMul (binaryDagger (E a)) (E b)) y) := by
              rw [inner_toQubitOperator_pair_eq_relative]
      _ = (star (amp a) * amp b) * (scalar a b * inner Complex x y) := by
              rw [hscalar a b ha hb x hx y hy]
      _ = (star (amp a) * amp b * scalar a b) * inner Complex x y := by
              ring

/--
A complete finite Kraus family of scaled binary Pauli operators is correctable
by a CPTP recovery exactly when every relative Pauli on the nonzero-amplitude
support is stabilizer-degenerate or outside the binary normalizer.

This is the source-exact realization of [Gott97, Ch. 2, Eq. (2.5); Ch. 3,
stabilizer error-set criterion] and [KL96, Theorem 2.1].
-/
theorem exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
    {α : Type v} [Fintype α]
    (Q : SourceValidBinary ι) (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    (∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
      Semantics.FiniteKrausCorrectable α
        (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
        Q.1.code (binaryPauliKrausFamily E amp) recovery) ↔
    ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
      Q.1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (E a)) (E b)) ∨
      ¬ Q.1.InBinaryNormalizer
          (binaryMul (binaryDagger (E a)) (E b)) := by
  rw [← (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
    Q.1.code hcomplete]
  exact
    binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
      Q E amp

end StabilizerCode
end Coding
end QEC
