import QEC.Coding.QuditQubitConversion.Transport

/-!
# Concrete WHY24 diagonal gates through `U₁^(7)`

The private WHY24 source defines `U_β^(n)` on a concrete `F1024` qudit by the
trace phase `(-1)^(Tr (β η^n))`.  This module realizes that definition on the
selected computational basis, rather than assuming a hierarchy action.
-/

noncomputable section

namespace QEC.Coding

open scoped BigOperators

/-- The source's diagonal `U_β^(n)` operator on the concrete `F1024` qudit. -/
noncomputable def why24U (β : F1024) (n : ℕ) : Semantics.Operator Why24QuditSpace where
  toFun ψ := WithLp.toLp 2 (fun η =>
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * ψ η)
  map_add' ψ φ := by
    ext η
    simp [mul_add]
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul, mul_left_comm]

@[simp] theorem why24U_apply (β : F1024) (n : ℕ)
    (ψ : Why24QuditSpace) (η : F1024) :
    why24U β n ψ η =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * ψ η :=
  rfl

/-- Every binary trace phase is real. -/
private theorem why24_binaryPhaseScalar_conj (p : ZMod 2) :
    star (PauliSymplectic.binaryPhaseScalar p) = PauliSymplectic.binaryPhaseScalar p := by
  by_cases hp : p = 0 <;> simp [PauliSymplectic.binaryPhaseScalar, hp]

/-- Every binary trace phase is an involutive complex scalar. -/
private theorem why24_binaryPhaseScalar_mul_self (p : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar p * PauliSymplectic.binaryPhaseScalar p = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add, CharTwo.add_self_eq_zero,
    PauliSymplectic.binaryPhaseScalar_zero]

/-- The source diagonal is self-adjoint because its phases are real signs. -/
private theorem why24U_isSymmetric (β : F1024) (n : ℕ) :
    (why24U β n).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro η _
  simp only [why24U_apply, RCLike.inner_apply']
  change star (PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * x η) * y η =
    star (x η) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * y η)
  rw [star_mul, why24_binaryPhaseScalar_conj]
  ring

/-- The concrete adjoint of the source diagonal is itself. -/
theorem why24U_adjoint (β : F1024) (n : ℕ) :
    LinearMap.adjoint (why24U β n) = why24U β n :=
  (why24U_isSymmetric β n).adjoint_eq

/-- Applying a source diagonal twice is the identity operator. -/
theorem why24U_mul_self (β : F1024) (n : ℕ) :
    why24U β n * why24U β n = 1 := by
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply]
  rw [← mul_assoc, why24_binaryPhaseScalar_mul_self, one_mul]
  rfl

/-- The source diagonal preserves the concrete qudit inner product. -/
theorem why24U_isUnitary (β : F1024) (n : ℕ) :
    Why24IsUnitary (why24U β n) := by
  intro x y
  calc
    inner Complex (why24U β n x) (why24U β n y) =
        inner Complex x (LinearMap.adjoint (why24U β n) (why24U β n y)) := by
          rw [LinearMap.adjoint_inner_right]
    _ = inner Complex x ((why24U β n * why24U β n) y) := by
          rw [why24U_adjoint]
          rfl
    _ = inner Complex x y := by simp [why24U_mul_self]

/-- Source-exact action of `U_β^(n)` on a concrete computational-basis ket. -/
theorem why24U_apply_basis (β : F1024) (n : ℕ) (η : F1024) :
    why24U β n (why24QuditComputationalBasis η) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) •
        why24QuditComputationalBasis η := by
  ext ξ
  by_cases hξη : ξ = η
  · subst ξ
    simp [why24QuditComputationalBasis, why24U_apply, smul_eq_mul]
  · simp [why24QuditComputationalBasis, why24U_apply, hξη]

/-- The inverse Frobenius square root used by the WHY24 source over `F1024`. -/
def why24FrobeniusRootTwo (x : F1024) : F1024 := x ^ 512

/-- The inverse Frobenius fourth root used by the WHY24 source over `F1024`. -/
def why24FrobeniusRootFour (x : F1024) : F1024 := x ^ 256

private theorem why24_f1024_pow_card (x : F1024) : x ^ 1024 = x := by
  rw [← f1024_card]
  exact FiniteField.pow_card x

/-- The chosen square-root representative squares to its input in `F1024`. -/
theorem why24FrobeniusRootTwo_sq (x : F1024) : why24FrobeniusRootTwo x ^ 2 = x := by
  change (x ^ 512) ^ 2 = x
  rw [← pow_mul]
  norm_num
  exact why24_f1024_pow_card x

/-- The chosen fourth-root representative has fourth power equal to its input in `F1024`. -/
theorem why24FrobeniusRootFour_pow_four (x : F1024) :
    why24FrobeniusRootFour x ^ 4 = x := by
  change (x ^ 256) ^ 4 = x
  rw [← pow_mul]
  norm_num
  exact why24_f1024_pow_card x

/-- The absolute trace is invariant under a Frobenius square on the concrete field. -/
theorem why24_trace_sq (x : F1024) :
    Algebra.trace (ZMod 2) F1024 (x ^ 2) = Algebra.trace (ZMod 2) F1024 x := by
  apply (algebraMap (ZMod 2) F1024).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, f1024_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  norm_num
  rw [why24_f1024_pow_card]
  ring

/-- Trace equality obtained by squaring one argument in the concrete field. -/
private theorem why24_trace_eq_of_sq {x y : F1024} (hxy : x ^ 2 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  rw [← why24_trace_sq x, hxy]

/-- Trace equality obtained by fourth-powering one argument in the concrete field. -/
private theorem why24_trace_eq_of_pow_four {x y : F1024} (hxy : x ^ 4 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  calc
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 (x ^ 2) :=
      (why24_trace_sq x).symm
    _ = Algebra.trace (ZMod 2) F1024 ((x ^ 2) ^ 2) :=
      (why24_trace_sq (x ^ 2)).symm
    _ = Algebra.trace (ZMod 2) F1024 (x ^ 4) := by ring_nf
    _ = Algebra.trace (ZMod 2) F1024 y := by rw [hxy]

private theorem why24_trace_u_three_conjugation (β γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (β * η ^ 3) +
      Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 3) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 3) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 2) * η) := by
  have hsquare : (why24FrobeniusRootTwo (β * γ) * η) ^ 2 = β * γ * η ^ 2 := by
    calc
      (why24FrobeniusRootTwo (β * γ) * η) ^ 2 =
          why24FrobeniusRootTwo (β * γ) ^ 2 * η ^ 2 := by rw [mul_pow]
      _ = β * γ * η ^ 2 := by rw [why24FrobeniusRootTwo_sq]
  have hroot :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 2) :=
    why24_trace_eq_of_sq hsquare
  have htwo : (2 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  have hthree : (3 : F1024) = 1 := by
    calc
      (3 : F1024) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwo]; ring
  have hbinomial : β * (η + γ) ^ 3 =
      β * η ^ 3 + β * γ ^ 3 + β * γ * η ^ 2 + β * γ ^ 2 * η := by
    ring_nf
    rw [hthree]
    ring
  rw [hbinomial, map_add, map_add, map_add]
  rw [show (why24FrobeniusRootTwo (β * γ) + β * γ ^ 2) * η =
      why24FrobeniusRootTwo (β * γ) * η + β * γ ^ 2 * η by ring, map_add]
  rw [hroot]
  let a : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * η ^ 3)
  let b : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 3)
  let c : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 2)
  let d : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 2 * η)
  change a + (a + b + c + d) = b + (c + d)
  calc
    a + (a + b + c + d) = (a + a) + b + c + d := by ac_rfl
    _ = 0 + b + c + d := by rw [CharTwo.add_self_eq_zero]
    _ = b + (c + d) := by ac_rfl

/-- Source-derived conjugation of a concrete field shift by `U_β^(3)`. -/
theorem why24U_conjX_three (β γ : F1024) :
    why24U β 3 * why24QuditX γ * LinearMap.adjoint (why24U β 3) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 3)) •
        (why24QuditX γ *
          why24QuditZ (why24FrobeniusRootTwo (β * γ) + β * γ ^ 2)) := by
  rw [why24U_adjoint]
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditX_apply, why24QuditZ_apply]
  change PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ 3)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 3)) * ψ (η + γ)) =
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * γ ^ 3)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 2) * (η + γ))) *
        ψ (η + γ))
  rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc]
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  conv_rhs => rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hshift : η + γ + γ = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have htrace := why24_trace_u_three_conjugation β γ (η + γ)
  rw [hshift] at htrace
  have htrace' :
      Algebra.trace (ZMod 2) F1024 (β * η ^ 3) +
        Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 3) =
          Algebra.trace (ZMod 2) F1024 (β * γ ^ 3) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 2) * (η + γ)) := by
    rw [add_comm]
    exact htrace
  rw [htrace']

private theorem why24_trace_u_five_conjugation (β γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (β * η ^ 5) +
      Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 5) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 5) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * η) := by
  have hpowfour : (why24FrobeniusRootFour (β * γ) * η) ^ 4 = β * γ * η ^ 4 := by
    calc
      (why24FrobeniusRootFour (β * γ) * η) ^ 4 =
          why24FrobeniusRootFour (β * γ) ^ 4 * η ^ 4 := by rw [mul_pow]
      _ = β * γ * η ^ 4 := by rw [why24FrobeniusRootFour_pow_four]
  have hroot :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootFour (β * γ) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 4) :=
    why24_trace_eq_of_pow_four hpowfour
  have htwo : (2 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  have hfive : (5 : F1024) = 1 := by
    calc
      (5 : F1024) = 2 * 2 + 1 := by norm_num
      _ = 1 := by rw [htwo]; ring
  have hten : (10 : F1024) = 0 := by
    calc
      (10 : F1024) = 5 * 2 := by norm_num
      _ = 0 := by rw [htwo, mul_zero]
  have hbinomial : β * (η + γ) ^ 5 =
      β * η ^ 5 + β * γ ^ 5 + β * γ * η ^ 4 + β * γ ^ 4 * η := by
    ring_nf
    rw [hfive, hten]
    ring
  rw [hbinomial, map_add, map_add, map_add]
  rw [show (why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * η =
      why24FrobeniusRootFour (β * γ) * η + β * γ ^ 4 * η by ring, map_add]
  rw [hroot]
  let a : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * η ^ 5)
  let b : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)
  let c : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 4)
  let d : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 4 * η)
  change a + (a + b + c + d) = b + (c + d)
  calc
    a + (a + b + c + d) = (a + a) + b + c + d := by ac_rfl
    _ = 0 + b + c + d := by rw [CharTwo.add_self_eq_zero]
    _ = b + (c + d) := by ac_rfl

/-- Source-derived conjugation of a concrete field shift by `U_β^(5)`. -/
theorem why24U_conjX_five (β γ : F1024) :
    why24U β 5 * why24QuditX γ * LinearMap.adjoint (why24U β 5) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)) •
        (why24QuditX γ *
          why24QuditZ (why24FrobeniusRootFour (β * γ) + β * γ ^ 4)) := by
  rw [why24U_adjoint]
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditX_apply]
  change PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ 5)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 5)) * ψ (η + γ)) =
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * (η + γ))) *
        ψ (η + γ))
  rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc]
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  conv_rhs => rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hshift : η + γ + γ = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have htrace := why24_trace_u_five_conjugation β γ (η + γ)
  rw [hshift] at htrace
  have htrace' :
      Algebra.trace (ZMod 2) F1024 (β * η ^ 5) +
        Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 5) =
          Algebra.trace (ZMod 2) F1024 (β * γ ^ 5) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * (η + γ)) := by
    rw [add_comm]
    exact htrace
  rw [htrace']

/-- Concrete trace phases multiply according to addition of their field labels. -/
theorem why24QuditZ_mul (γ δ : F1024) :
    why24QuditZ γ * why24QuditZ δ = why24QuditZ (γ + δ) := by
  ext ψ η
  simp only [Module.End.mul_apply, why24QuditZ_apply]
  rw [← mul_assoc, ← PauliSymplectic.binaryPhaseScalar_add]
  congr 2
  rw [show (γ + δ) * η = γ * η + δ * η by ring, map_add]

/-- Every source diagonal commutes with every concrete trace-phase `Z` operator. -/
theorem why24U_mul_qZ (β : F1024) (n : ℕ) (γ : F1024) :
    why24U β n * why24QuditZ γ = why24QuditZ γ * why24U β n := by
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditZ_apply]
  ring

private theorem why24PauliPhase_add_two_mul (a : ZMod 4) (t : ZMod 2) :
    why24PauliPhase (a + 2 * (t.val : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar t := by
  fin_cases t
  · change why24PauliPhase (a + 2 * (0 : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar 0
    simp [why24PauliPhase]
  · change why24PauliPhase (a + 2 * (1 : ZMod 4)) =
      why24PauliPhase a * PauliSymplectic.binaryPhaseScalar 1
    rw [PauliSymplectic.binaryPhaseScalar_one]
    fin_cases a
    · change Complex.I ^ 2 = Complex.I ^ 0 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 3 = Complex.I ^ 1 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 0 = Complex.I ^ 2 * (-1)
      norm_num [pow_succ, Complex.I_sq]
    · change Complex.I ^ 1 = Complex.I ^ 3 * (-1)
      norm_num [pow_succ, Complex.I_sq]

private theorem why24U_conjPauli_three (β : F1024) (a : ZMod 4)
    (b c : F1024) :
    why24U β 3 * why24FieldPauliOperator (a, b, c) * LinearMap.adjoint (why24U β 3) =
      why24FieldPauliOperator
        (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 3)).val : ZMod 4), b,
          why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c) := by
  change why24U β 3 *
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        LinearMap.adjoint (why24U β 3) = _
  rw [show why24U β 3 * (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
      LinearMap.adjoint (why24U β 3) = why24PauliPhase a •
        (why24U β 3 * why24QuditX b * why24QuditZ c *
          LinearMap.adjoint (why24U β 3)) by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]]
  have hcomm := why24U_mul_qZ β 3 c
  have hcommAdj : why24QuditZ c * LinearMap.adjoint (why24U β 3) =
      LinearMap.adjoint (why24U β 3) * why24QuditZ c := by
    rw [why24U_adjoint]
    exact hcomm.symm
  rw [show why24U β 3 * why24QuditX b * why24QuditZ c *
      LinearMap.adjoint (why24U β 3) =
      (why24U β 3 * why24QuditX b * LinearMap.adjoint (why24U β 3)) *
        why24QuditZ c by
        calc
          why24U β 3 * why24QuditX b * why24QuditZ c *
              LinearMap.adjoint (why24U β 3) =
              (why24U β 3 * why24QuditX b) *
                (why24QuditZ c * LinearMap.adjoint (why24U β 3)) := by
                rw [mul_assoc]
          _ = (why24U β 3 * why24QuditX b) *
              (LinearMap.adjoint (why24U β 3) * why24QuditZ c) := by
                rw [hcommAdj]
          _ = (why24U β 3 * why24QuditX b * LinearMap.adjoint (why24U β 3)) *
              why24QuditZ c := by
                simp only [mul_assoc]]
  rw [why24U_conjX_three]
  rw [smul_mul_assoc]
  rw [show (why24QuditX b *
      why24QuditZ (why24FrobeniusRootTwo (β * b) + β * b ^ 2)) * why24QuditZ c =
      why24QuditX b *
        why24QuditZ (why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c) by
      rw [mul_assoc, why24QuditZ_mul]]
  change why24PauliPhase a •
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * b ^ 3)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c))) =
    why24PauliPhase
      (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 3)).val : ZMod 4)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c))
  rw [why24PauliPhase_add_two_mul, mul_smul]

/-- The concrete `U_β^(3)` diagonal is a field-Pauli Clifford normalizer. -/
theorem why24U_fieldClifford_three (β : F1024) : Why24FieldClifford (why24U β 3) := by
  constructor
  · exact why24U_isUnitary β 3
  · rintro ⟨a, b, c⟩
    refine ⟨(a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 3)).val : ZMod 4), b,
      why24FrobeniusRootTwo (β * b) + β * b ^ 2 + c), ?_⟩
    exact why24U_conjPauli_three β a b c

/-- The concrete diagonal selected by the source for the `U₁^(7)` gate. -/
abbrev why24UOneSeven : Semantics.Operator Why24QuditSpace := why24U (1 : F1024) 7

/-- Translation by a field label is symmetric on the concrete finite qudit space. -/
private theorem why24QuditX_isSymmetric (β : F1024) :
    (why24QuditX β).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, why24QuditX_apply, RCLike.inner_apply']
  exact Fintype.sum_equiv (Equiv.addRight β)
    (fun η => star (x (η + β)) * y η)
    (fun η => star (x η) * y (η + β)) (by
      intro η
      change star (x (η + β)) * y η =
        star (x (η + β)) * y ((η + β) + β)
      rw [show (η + β) + β = η by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]])

/-- The field shift is self-adjoint because the characteristic is two. -/
private theorem why24QuditX_adjoint (β : F1024) :
    LinearMap.adjoint (why24QuditX β) = why24QuditX β :=
  (why24QuditX_isSymmetric β).adjoint_eq

/-- The field trace phase is the first source diagonal. -/
private theorem why24QuditZ_eq_u_one (γ : F1024) :
    why24QuditZ γ = why24U γ 1 := by
  ext ψ η
  simp [why24QuditZ_apply, why24U_apply]

/-- The field trace phase is self-adjoint. -/
private theorem why24QuditZ_adjoint (γ : F1024) :
    LinearMap.adjoint (why24QuditZ γ) = why24QuditZ γ := by
  rw [why24QuditZ_eq_u_one, why24U_adjoint]

/-- Concrete field shifts compose by addition of their field labels. -/
private theorem why24QuditX_mul (β γ : F1024) :
    why24QuditX β * why24QuditX γ = why24QuditX (β + γ) := by
  ext ψ η
  simp only [Module.End.mul_apply, why24QuditX_apply]
  rw [add_assoc]

/-- Moving a trace phase past a field shift produces its actual binary trace sign. -/
private theorem why24QuditZ_mul_qX (c b : F1024) :
    why24QuditZ c * why24QuditX b =
      PauliSymplectic.binaryPhaseScalar (Algebra.trace (ZMod 2) F1024 (c * b)) •
        (why24QuditX b * why24QuditZ c) := by
  ext ψ η
  simp only [Module.End.mul_apply, why24QuditZ_apply, why24QuditX_apply,
    LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← PauliSymplectic.binaryPhaseScalar_add]
  congr 2
  rw [show c * (η + b) = c * η + c * b by ring, map_add]
  let u : ZMod 2 := Algebra.trace (ZMod 2) F1024 (c * η)
  let v : ZMod 2 := Algebra.trace (ZMod 2) F1024 (c * b)
  change u = v + (u + v)
  calc
    u = 0 + u := (zero_add u).symm
    _ = (v + v) + u := by rw [CharTwo.add_self_eq_zero]
    _ = v + (u + v) := by ac_rfl

/-- The source's fourth-root phase obeys multiplication in its literal residue labels. -/
private theorem why24PauliPhase_add (a b : ZMod 4) :
    why24PauliPhase (a + b) = why24PauliPhase a * why24PauliPhase b := by
  fin_cases a <;> fin_cases b
  · change Complex.I ^ 0 = Complex.I ^ 0 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 0 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 0 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 0 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 1 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 1 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 1 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 0 = Complex.I ^ 1 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 2 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 2 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 0 = Complex.I ^ 2 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 2 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 3 = Complex.I ^ 3 * Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 0 = Complex.I ^ 3 * Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 1 = Complex.I ^ 3 * Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = Complex.I ^ 3 * Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]

/-- Conjugating a literal source phase gives the inverse residue label. -/
private theorem why24PauliPhase_star (a : ZMod 4) :
    star (why24PauliPhase a) = why24PauliPhase (-a) := by
  fin_cases a
  · change star (Complex.I ^ 0) = Complex.I ^ 0
    norm_num [pow_succ, Complex.I_sq]
  · change star (Complex.I ^ 1) = Complex.I ^ 3
    norm_num [pow_succ, Complex.I_sq]
  · change star (Complex.I ^ 2) = Complex.I ^ 2
    norm_num [pow_succ, Complex.I_sq]
  · change star (Complex.I ^ 3) = Complex.I ^ 1
    norm_num [pow_succ, Complex.I_sq]

/-- A binary trace sign is the corresponding even fourth-root phase. -/
private theorem why24PauliPhase_two_trace (t : ZMod 2) :
    why24PauliPhase (2 * (t.val : ZMod 4)) =
      PauliSymplectic.binaryPhaseScalar t := by
  fin_cases t
  · change Complex.I ^ 0 = (1 : Complex)
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = (-1 : Complex)
    norm_num [pow_succ, Complex.I_sq]

/-- The actual source field-Pauli product label. -/
private def why24FieldPauliMul (P Q : Why24FieldPauli) : Why24FieldPauli :=
  (P.1 + Q.1 + 2 *
      ((Algebra.trace (ZMod 2) F1024 (P.2.2 * Q.2.1)).val : ZMod 4),
    P.2.1 + Q.2.1, P.2.2 + Q.2.2)

/-- The actual source field-Pauli adjoint label. -/
private def why24FieldPauliDagger (P : Why24FieldPauli) : Why24FieldPauli :=
  (-P.1 + 2 *
      ((Algebra.trace (ZMod 2) F1024 (P.2.1 * P.2.2)).val : ZMod 4),
    P.2.1, P.2.2)

/-- A zero-phase, zero-`Z` field Pauli is the concrete field shift. -/
private theorem why24FieldPauliOperator_X (β : F1024) :
    why24FieldPauliOperator (0, β, 0) = why24QuditX β := by
  ext ψ η
  simp [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
    why24QuditX_apply, why24QuditZ_apply, smul_eq_mul]

/-- A zero-phase, zero-`X` field Pauli is the concrete trace phase. -/
private theorem why24FieldPauliOperator_Z (γ : F1024) :
    why24FieldPauliOperator (0, 0, γ) = why24QuditZ γ := by
  ext ψ η
  simp [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
    why24QuditX_apply, why24QuditZ_apply, smul_eq_mul]

/-- A zero-vector field Pauli is its literal fourth-root phase. -/
private theorem why24FieldPauliOperator_phase (a : ZMod 4) :
    why24FieldPauliOperator (a, 0, 0) =
      why24PauliPhase a • (1 : Semantics.Operator Why24QuditSpace) := by
  ext ψ η
  simp [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
    why24QuditX_apply, why24QuditZ_apply, smul_eq_mul]

/-- The sign-corrected product of two concrete shift--phase field operators. -/
private theorem why24QuditXZ_mul (b c e f : F1024) :
    (why24QuditX b * why24QuditZ c) * (why24QuditX e * why24QuditZ f) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (c * e)) •
        (why24QuditX (b + e) * why24QuditZ (c + f)) := by
  calc
    (why24QuditX b * why24QuditZ c) *
        (why24QuditX e * why24QuditZ f) =
        why24QuditX b * (why24QuditZ c * why24QuditX e) * why24QuditZ f := by
          simp only [mul_assoc]
    _ = why24QuditX b *
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 (c * e)) •
          (why24QuditX e * why24QuditZ c)) * why24QuditZ f := by
          rw [why24QuditZ_mul_qX]
    _ = PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (c * e)) •
        ((why24QuditX b * why24QuditX e) *
          (why24QuditZ c * why24QuditZ f)) := by
          rw [mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
    _ = PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (c * e)) •
        (why24QuditX (b + e) * why24QuditZ (c + f)) := by
          rw [why24QuditX_mul, why24QuditZ_mul]

/-- Literal field-Pauli labels are closed under composition. -/
private theorem why24FieldPauliOperator_mul (P Q : Why24FieldPauli) :
    why24FieldPauliOperator (why24FieldPauliMul P Q) =
      why24FieldPauliOperator P * why24FieldPauliOperator Q := by
  rcases P with ⟨a, b, c⟩
  rcases Q with ⟨d, e, f⟩
  change why24PauliPhase
      (a + d + 2 * ((Algebra.trace (ZMod 2) F1024 (c * e)).val : ZMod 4)) •
      (why24QuditX (b + e) * why24QuditZ (c + f)) =
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        (why24PauliPhase d • (why24QuditX e * why24QuditZ f))
  rw [show
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        (why24PauliPhase d • (why24QuditX e * why24QuditZ f)) =
        (why24PauliPhase a * why24PauliPhase d) •
          ((why24QuditX b * why24QuditZ c) *
            (why24QuditX e * why24QuditZ f)) by
      rw [smul_mul_smul_comm], why24QuditXZ_mul, smul_smul,
    ← why24PauliPhase_two_trace, ← why24PauliPhase_add,
    ← why24PauliPhase_add]

/-- Literal field-Pauli labels are closed under adjoints. -/
private theorem why24FieldPauliOperator_adjoint (P : Why24FieldPauli) :
    why24FieldPauliOperator (why24FieldPauliDagger P) =
      LinearMap.adjoint (why24FieldPauliOperator P) := by
  rcases P with ⟨a, b, c⟩
  change why24PauliPhase
      (-a + 2 * ((Algebra.trace (ZMod 2) F1024 (b * c)).val : ZMod 4)) •
      (why24QuditX b * why24QuditZ c) =
        LinearMap.adjoint
          (why24PauliPhase a • (why24QuditX b * why24QuditZ c))
  rw [show LinearMap.adjoint
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) =
      star (why24PauliPhase a) •
        (why24QuditZ c * why24QuditX b) by
      calc
        LinearMap.adjoint
            (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) =
            star (why24PauliPhase a) •
              LinearMap.adjoint (why24QuditX b * why24QuditZ c) := by
                exact map_smulₛₗ
                  (LinearMap.adjoint :
                    Semantics.Operator Why24QuditSpace ≃ₗ⋆[Complex]
                      Semantics.Operator Why24QuditSpace)
                  (why24PauliPhase a) (why24QuditX b * why24QuditZ c)
        _ = star (why24PauliPhase a) •
            (why24QuditZ c * why24QuditX b) := by
              rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
                ← Module.End.mul_eq_comp, why24QuditX_adjoint,
                why24QuditZ_adjoint]]
  rw [why24QuditZ_mul_qX, smul_smul, why24PauliPhase_star,
    ← why24PauliPhase_two_trace, ← why24PauliPhase_add]
  ring_nf

/-- Actual field Paulis normalize actual field Paulis under conjugation. -/
private theorem why24FieldPauliOperator_conj (P Q : Why24FieldPauli) :
    ∃ R : Why24FieldPauli,
      why24FieldPauliOperator P * why24FieldPauliOperator Q *
        LinearMap.adjoint (why24FieldPauliOperator P) = why24FieldPauliOperator R := by
  refine ⟨why24FieldPauliMul (why24FieldPauliMul P Q) (why24FieldPauliDagger P), ?_⟩
  rw [why24FieldPauliOperator_mul, why24FieldPauliOperator_mul,
    why24FieldPauliOperator_adjoint]

/-- The fifth source diagonal normalizes every literal field Pauli. -/
private theorem why24U_conjPauli_five (β : F1024) (a : ZMod 4)
    (b c : F1024) :
    why24U β 5 * why24FieldPauliOperator (a, b, c) * LinearMap.adjoint (why24U β 5) =
      why24FieldPauliOperator
        (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 5)).val : ZMod 4), b,
          why24FrobeniusRootFour (β * b) + β * b ^ 4 + c) := by
  change why24U β 5 *
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        LinearMap.adjoint (why24U β 5) = _
  rw [show why24U β 5 * (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
      LinearMap.adjoint (why24U β 5) = why24PauliPhase a •
        (why24U β 5 * why24QuditX b * why24QuditZ c *
          LinearMap.adjoint (why24U β 5)) by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]]
  have hcomm := why24U_mul_qZ β 5 c
  have hcommAdj : why24QuditZ c * LinearMap.adjoint (why24U β 5) =
      LinearMap.adjoint (why24U β 5) * why24QuditZ c := by
    rw [why24U_adjoint]
    exact hcomm.symm
  rw [show why24U β 5 * why24QuditX b * why24QuditZ c *
      LinearMap.adjoint (why24U β 5) =
      (why24U β 5 * why24QuditX b * LinearMap.adjoint (why24U β 5)) *
        why24QuditZ c by
        calc
          why24U β 5 * why24QuditX b * why24QuditZ c *
              LinearMap.adjoint (why24U β 5) =
              (why24U β 5 * why24QuditX b) *
                (why24QuditZ c * LinearMap.adjoint (why24U β 5)) := by
                rw [mul_assoc]
          _ = (why24U β 5 * why24QuditX b) *
              (LinearMap.adjoint (why24U β 5) * why24QuditZ c) := by
                rw [hcommAdj]
          _ = (why24U β 5 * why24QuditX b * LinearMap.adjoint (why24U β 5)) *
              why24QuditZ c := by
                simp only [mul_assoc]]
  rw [why24U_conjX_five]
  rw [smul_mul_assoc]
  rw [show (why24QuditX b *
      why24QuditZ (why24FrobeniusRootFour (β * b) + β * b ^ 4)) * why24QuditZ c =
      why24QuditX b *
        why24QuditZ (why24FrobeniusRootFour (β * b) + β * b ^ 4 + c) by
      rw [mul_assoc, why24QuditZ_mul]]
  change why24PauliPhase a •
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * b ^ 5)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootFour (β * b) + β * b ^ 4 + c))) =
    why24PauliPhase
      (a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 5)).val : ZMod 4)) •
        (why24QuditX b *
          why24QuditZ
            (why24FrobeniusRootFour (β * b) + β * b ^ 4 + c))
  rw [why24PauliPhase_add_two_mul, mul_smul]

/-- The concrete `U_β^(5)` diagonal is a field-Pauli Clifford normalizer. -/
private theorem why24U_fieldClifford_five (β : F1024) : Why24FieldClifford (why24U β 5) := by
  constructor
  · exact why24U_isUnitary β 5
  · rintro ⟨a, b, c⟩
    refine ⟨(a + 2 * ((Algebra.trace (ZMod 2) F1024 (β * b ^ 5)).val : ZMod 4), b,
      why24FrobeniusRootFour (β * b) + β * b ^ 4 + c), ?_⟩
    exact why24U_conjPauli_five β a b c

/--
The source-local Clifford hierarchy: level one consists of the actual literal
field Paulis, and every higher level is specified by literal Pauli conjugation.
This deliberately records no abstract or stored hierarchy membership.
-/
def why24InCliffordHierarchy : Nat → Semantics.Operator Why24QuditSpace → Prop
  | 0, _ => False
  | 1, C => ∃ P : Why24FieldPauli, C = why24FieldPauliOperator P
  | n + 2, C => ∀ P : Why24FieldPauli, ∃ D : Semantics.Operator Why24QuditSpace,
      why24InCliffordHierarchy (n + 1) D ∧
        C * why24FieldPauliOperator P * LinearMap.adjoint C = D

/-- Level two is exactly the concrete field-Pauli normalizer action. -/
private theorem why24InCliffordHierarchy_two_of_normalizes
    {C : Semantics.Operator Why24QuditSpace}
    (hC : why24FieldNormalizesPaulis C) : why24InCliffordHierarchy 2 C := by
  intro P
  obtain ⟨Q, hQ⟩ := hC P
  exact ⟨why24FieldPauliOperator Q, ⟨Q, rfl⟩, hQ⟩

/-- Actual field Paulis themselves inhabit level two by their literal group action. -/
private theorem why24FieldPauli_inCliffordHierarchy_two (P : Why24FieldPauli) :
    why24InCliffordHierarchy 2 (why24FieldPauliOperator P) := by
  intro Q
  obtain ⟨R, hR⟩ := why24FieldPauliOperator_conj P Q
  exact ⟨why24FieldPauliOperator R, ⟨R, rfl⟩, hR⟩

/-- Products of level-two source-local hierarchy operators remain at level two. -/
private theorem why24InCliffordHierarchy_two_mul
    {A B : Semantics.Operator Why24QuditSpace}
    (hA : why24InCliffordHierarchy 2 A)
    (hB : why24InCliffordHierarchy 2 B) :
    why24InCliffordHierarchy 2 (A * B) := by
  intro P
  obtain ⟨Q, ⟨q, hQ⟩, hBQ⟩ := hB P
  obtain ⟨R, hR, hAR⟩ := hA q
  refine ⟨R, hR, ?_⟩
  rw [show LinearMap.adjoint (A * B) = LinearMap.adjoint B * LinearMap.adjoint A by
      rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]]
  calc
    A * B * why24FieldPauliOperator P *
        (LinearMap.adjoint B * LinearMap.adjoint A) =
        A * (B * why24FieldPauliOperator P * LinearMap.adjoint B) *
          LinearMap.adjoint A := by
            simp only [mul_assoc]
    _ = A * Q * LinearMap.adjoint A := by rw [hBQ]
    _ = A * why24FieldPauliOperator q * LinearMap.adjoint A := by rw [hQ]
    _ = R := hAR

/-- Scalar source signs are literal level-two field Paulis. -/
private theorem why24BinaryPhase_inCliffordHierarchy_two (t : ZMod 2) :
    why24InCliffordHierarchy 2
      (PauliSymplectic.binaryPhaseScalar t • (1 : Semantics.Operator Why24QuditSpace)) := by
  rw [show PauliSymplectic.binaryPhaseScalar t • (1 : Semantics.Operator Why24QuditSpace) =
      why24FieldPauliOperator (2 * (t.val : ZMod 4), 0, 0) by
        change PauliSymplectic.binaryPhaseScalar t • (1 : Semantics.Operator Why24QuditSpace) =
          why24PauliPhase (2 * (t.val : ZMod 4)) •
            (why24QuditX 0 * why24QuditZ 0)
        rw [why24PauliPhase_two_trace]
        ext ψ η
        simp [why24QuditX_apply, why24QuditZ_apply]]
  exact why24FieldPauli_inCliffordHierarchy_two _

/-- Every cubic source diagonal lies at level two of the literal hierarchy. -/
private theorem why24U_three_inCliffordHierarchy_two (β : F1024) :
    why24InCliffordHierarchy 2 (why24U β 3) :=
  why24InCliffordHierarchy_two_of_normalizes (why24U_fieldClifford_three β).2

/-- Every quintic source diagonal lies at level two of the literal hierarchy. -/
private theorem why24U_five_inCliffordHierarchy_two (β : F1024) :
    why24InCliffordHierarchy 2 (why24U β 5) :=
  why24InCliffordHierarchy_two_of_normalizes (why24U_fieldClifford_five β).2

private theorem why24_trace_u_seven_conjugation (β γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (β * η ^ 7) +
      Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 7) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * η ^ 3) +
          Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * η ^ 5) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootFour (β * γ ^ 3) +
                why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * η) := by
  have hsix : (why24FrobeniusRootTwo (β * γ) * η ^ 3) ^ 2 = β * γ * η ^ 6 := by
    calc
      (why24FrobeniusRootTwo (β * γ) * η ^ 3) ^ 2 =
          why24FrobeniusRootTwo (β * γ) ^ 2 * (η ^ 3) ^ 2 := by rw [mul_pow]
      _ = β * γ * η ^ 6 := by rw [why24FrobeniusRootTwo_sq]; ring
  have hfour : (why24FrobeniusRootFour (β * γ ^ 3) * η) ^ 4 =
      β * γ ^ 3 * η ^ 4 := by
    calc
      (why24FrobeniusRootFour (β * γ ^ 3) * η) ^ 4 =
          why24FrobeniusRootFour (β * γ ^ 3) ^ 4 * η ^ 4 := by rw [mul_pow]
      _ = β * γ ^ 3 * η ^ 4 := by rw [why24FrobeniusRootFour_pow_four]
  have htwo : (why24FrobeniusRootTwo (β * γ ^ 5) * η) ^ 2 =
      β * γ ^ 5 * η ^ 2 := by
    calc
      (why24FrobeniusRootTwo (β * γ ^ 5) * η) ^ 2 =
          why24FrobeniusRootTwo (β * γ ^ 5) ^ 2 * η ^ 2 := by rw [mul_pow]
      _ = β * γ ^ 5 * η ^ 2 := by rw [why24FrobeniusRootTwo_sq]
  have hrootSix :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ) * η ^ 3) =
        Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 6) :=
    why24_trace_eq_of_sq hsix
  have hrootFour :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootFour (β * γ ^ 3) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 3 * η ^ 4) :=
    why24_trace_eq_of_pow_four hfour
  have hrootTwo :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ ^ 5) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 5 * η ^ 2) :=
    why24_trace_eq_of_sq htwo
  have htwoChar : (2 : F1024) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  have hthree : (3 : F1024) = 1 := by
    calc
      (3 : F1024) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hfive : (5 : F1024) = 1 := by
    calc
      (5 : F1024) = 2 * 2 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hseven : (7 : F1024) = 1 := by
    calc
      (7 : F1024) = 2 * 3 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have htwentyOne : (21 : F1024) = 1 := by
    calc
      (21 : F1024) = 2 * 10 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hthirtyFive : (35 : F1024) = 1 := by
    calc
      (35 : F1024) = 2 * 17 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hbinomial : β * (η + γ) ^ 7 =
      β * η ^ 7 + β * γ ^ 7 + β * γ * η ^ 6 + β * γ ^ 2 * η ^ 5 +
        β * γ ^ 3 * η ^ 4 + β * γ ^ 4 * η ^ 3 + β * γ ^ 5 * η ^ 2 +
          β * γ ^ 6 * η := by
    ring_nf
    rw [hseven, htwentyOne, hthirtyFive]
    ring
  rw [hbinomial]
  repeat' rw [map_add]
  rw [show (why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * η ^ 3 =
      why24FrobeniusRootTwo (β * γ) * η ^ 3 + β * γ ^ 4 * η ^ 3 by ring,
    show (why24FrobeniusRootFour (β * γ ^ 3) +
        why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * η =
      why24FrobeniusRootFour (β * γ ^ 3) * η +
        why24FrobeniusRootTwo (β * γ ^ 5) * η + β * γ ^ 6 * η by ring]
  repeat' rw [map_add]
  rw [hrootSix, hrootFour, hrootTwo]
  let a : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * η ^ 7)
  let b : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)
  let c : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 6)
  let d : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 2 * η ^ 5)
  let e : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 3 * η ^ 4)
  let f : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 4 * η ^ 3)
  let g : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 5 * η ^ 2)
  let h : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 6 * η)
  change a + (a + b + c + d + e + f + g + h) = b + (c + f) + d + (e + g + h)
  calc
    a + (a + b + c + d + e + f + g + h) =
        (a + a) + b + c + d + e + f + g + h := by ac_rfl
    _ = b + (c + f) + d + (e + g + h) := by
      rw [CharTwo.add_self_eq_zero]
      ac_rfl

/-- Source-exact seventh-power conjugation of a concrete field shift. -/
private theorem why24U_conjX_seven (β γ : F1024) :
    why24U β 7 * why24QuditX γ * LinearMap.adjoint (why24U β 7) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)) •
        (why24QuditX γ *
          why24U (why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) 3 *
          why24U (β * γ ^ 2) 5 *
          why24QuditZ
            (why24FrobeniusRootFour (β * γ ^ 3) +
              why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6)) := by
  rw [why24U_adjoint]
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditX_apply, why24QuditZ_apply,
    smul_eq_mul]
  change PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ 7)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7)) * ψ (η + γ)) =
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * (η + γ) ^ 3)) *
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * (η + γ) ^ 5)) *
          (PauliSymplectic.binaryPhaseScalar
            (Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ ^ 3) +
                why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * (η + γ))) *
            ψ (η + γ))))
  rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  repeat' rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hshift : η + γ + γ = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have htrace := why24_trace_u_seven_conjugation β γ (η + γ)
  rw [hshift] at htrace
  have htrace' :
      Algebra.trace (ZMod 2) F1024 (β * η ^ 7) +
        Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7) =
          Algebra.trace (ZMod 2) F1024 (β * γ ^ 7) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * (η + γ) ^ 3) +
            Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * (η + γ) ^ 5) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ ^ 3) +
                  why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * (η + γ)) := by
    rw [add_comm]
    exact htrace
  rw [htrace']

/-- The zero-labelled source diagonal is the identity. -/
private theorem why24U_zero (n : ℕ) :
    why24U (0 : F1024) n = 1 := by
  ext ψ η
  simp [why24U_apply]

/-- The source's displayed `γ = 1` seventh-power conjugation. -/
theorem why24UOneSeven_conjX_one :
    why24UOneSeven * why24QuditX (1 : F1024) * LinearMap.adjoint why24UOneSeven =
      PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) ^ 7)) •
        (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 * why24QuditZ (1 : F1024)) := by
  simpa [why24UOneSeven, why24FrobeniusRootTwo, why24FrobeniusRootFour,
    why24U_zero, CharTwo.add_self_eq_zero, mul_assoc] using
    why24U_conjX_seven (1 : F1024) (1 : F1024)

private theorem why24QuditX_inCliffordHierarchy_two (γ : F1024) :
    why24InCliffordHierarchy 2 (why24QuditX γ) := by
  rw [← why24FieldPauliOperator_X]
  exact why24FieldPauli_inCliffordHierarchy_two _

private theorem why24QuditZ_inCliffordHierarchy_two (γ : F1024) :
    why24InCliffordHierarchy 2 (why24QuditZ γ) := by
  rw [← why24FieldPauliOperator_Z]
  exact why24FieldPauli_inCliffordHierarchy_two _

private theorem why24FieldPhase_inCliffordHierarchy_two (a : ZMod 4) :
    why24InCliffordHierarchy 2
      (why24PauliPhase a • (1 : Semantics.Operator Why24QuditSpace)) := by
  rw [← why24FieldPauliOperator_phase]
  exact why24FieldPauli_inCliffordHierarchy_two _

private theorem why24U_conjPauli_seven (β : F1024) (a : ZMod 4)
    (b c : F1024) :
    why24U β 7 * why24FieldPauliOperator (a, b, c) * LinearMap.adjoint (why24U β 7) =
      why24PauliPhase a •
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 (β * b ^ 7)) •
          (why24QuditX b *
            why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
            why24U (β * b ^ 2) 5 *
            why24QuditZ
              (why24FrobeniusRootFour (β * b ^ 3) +
                why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6 + c))) := by
  change why24U β 7 *
      (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
        LinearMap.adjoint (why24U β 7) = _
  rw [show why24U β 7 * (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) *
      LinearMap.adjoint (why24U β 7) = why24PauliPhase a •
        (why24U β 7 * why24QuditX b * why24QuditZ c *
          LinearMap.adjoint (why24U β 7)) by
      simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]]
  have hcomm := why24U_mul_qZ β 7 c
  have hcommAdj : why24QuditZ c * LinearMap.adjoint (why24U β 7) =
      LinearMap.adjoint (why24U β 7) * why24QuditZ c := by
    rw [why24U_adjoint]
    exact hcomm.symm
  rw [show why24U β 7 * why24QuditX b * why24QuditZ c *
      LinearMap.adjoint (why24U β 7) =
      (why24U β 7 * why24QuditX b * LinearMap.adjoint (why24U β 7)) *
        why24QuditZ c by
        calc
          why24U β 7 * why24QuditX b * why24QuditZ c *
              LinearMap.adjoint (why24U β 7) =
              (why24U β 7 * why24QuditX b) *
                (why24QuditZ c * LinearMap.adjoint (why24U β 7)) := by
                rw [mul_assoc]
          _ = (why24U β 7 * why24QuditX b) *
              (LinearMap.adjoint (why24U β 7) * why24QuditZ c) := by
                rw [hcommAdj]
          _ = (why24U β 7 * why24QuditX b * LinearMap.adjoint (why24U β 7)) *
              why24QuditZ c := by
                simp only [mul_assoc]]
  rw [why24U_conjX_seven]
  rw [smul_mul_assoc]
  have hZ :
      (why24QuditX b *
        why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
        why24U (β * b ^ 2) 5 *
        why24QuditZ
          (why24FrobeniusRootFour (β * b ^ 3) +
            why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6)) * why24QuditZ c =
      why24QuditX b *
        why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
        why24U (β * b ^ 2) 5 *
        why24QuditZ
          (why24FrobeniusRootFour (β * b ^ 3) +
            why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6 + c) := by
    calc
      (why24QuditX b *
        why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
        why24U (β * b ^ 2) 5 *
        why24QuditZ
          (why24FrobeniusRootFour (β * b ^ 3) +
            why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6)) * why24QuditZ c =
        why24QuditX b *
          why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
          why24U (β * b ^ 2) 5 *
          (why24QuditZ
            (why24FrobeniusRootFour (β * b ^ 3) +
              why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6) * why24QuditZ c) := by
            simp only [mul_assoc]
      _ = why24QuditX b *
          why24U (why24FrobeniusRootTwo (β * b) + β * b ^ 4) 3 *
          why24U (β * b ^ 2) 5 *
          why24QuditZ
            (why24FrobeniusRootFour (β * b ^ 3) +
              why24FrobeniusRootTwo (β * b ^ 5) + β * b ^ 6 + c) := by
            rw [why24QuditZ_mul]
  rw [hZ]

/-- The selected `U₁^(7)` lies at literal field-Clifford hierarchy level three. -/
theorem why24UOneSeven_in_cliffordHierarchy_three :
    why24InCliffordHierarchy 3 why24UOneSeven := by
  intro P
  rcases P with ⟨a, b, c⟩
  let traceBit : ZMod 2 := Algebra.trace (ZMod 2) F1024 ((1 : F1024) * b ^ 7)
  let A : F1024 := why24FrobeniusRootTwo ((1 : F1024) * b) + (1 : F1024) * b ^ 4
  let B : F1024 := (1 : F1024) * b ^ 2
  let C : F1024 := why24FrobeniusRootFour ((1 : F1024) * b ^ 3) +
    why24FrobeniusRootTwo ((1 : F1024) * b ^ 5) + (1 : F1024) * b ^ 6 + c
  refine ⟨why24FieldPauliOperator
      (a + 2 * (traceBit.val : ZMod 4), 0, 0) *
        why24QuditX b * why24U A 3 * why24U B 5 * why24QuditZ C, ?_, ?_⟩
  · apply why24InCliffordHierarchy_two_mul
    · apply why24InCliffordHierarchy_two_mul
      · apply why24InCliffordHierarchy_two_mul
        · apply why24InCliffordHierarchy_two_mul
          · exact why24FieldPauli_inCliffordHierarchy_two _
          · exact why24QuditX_inCliffordHierarchy_two b
        · exact why24U_three_inCliffordHierarchy_two A
      · exact why24U_five_inCliffordHierarchy_two B
    · exact why24QuditZ_inCliffordHierarchy_two C
  · rw [why24U_conjPauli_seven]
    change why24PauliPhase a •
      (PauliSymplectic.binaryPhaseScalar traceBit •
        (why24QuditX b * why24U A 3 * why24U B 5 * why24QuditZ C)) = _
    rw [why24FieldPauliOperator_phase]
    rw [why24PauliPhase_add, why24PauliPhase_two_trace]
    simp only [smul_mul_assoc, smul_smul, one_mul]

private theorem why24Alpha_pow_eq_mk (k : ℕ) :
    f1024Alpha ^ k = AdjoinRoot.mk f1024Modulus (Polynomial.X ^ k) := by
  simp [f1024Alpha, ← AdjoinRoot.mk_X]

private theorem why24_square_residue (p r q : Polynomial (ZMod 2))
    (h : p ^ 2 = f1024Modulus * q + r) :
    (AdjoinRoot.mk f1024Modulus p) ^ 2 = AdjoinRoot.mk f1024Modulus r := by
  rw [← (AdjoinRoot.mk f1024Modulus).map_pow, h, map_add, map_mul,
    AdjoinRoot.mk_self, zero_mul, zero_add]

/-- The explicit `F1024` witness used below is computed in the source's fixed
degree-ten quotient, rather than inferred from the paper's informal argument. -/
private theorem why24FrobeniusRootFour_alpha :
    why24FrobeniusRootFour f1024Alpha =
      AdjoinRoot.mk f1024Modulus
        (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X) := by
  have h0 : f1024Alpha ^ 16 =
      AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 9 + Polynomial.X ^ 6) := by
    calc
      f1024Alpha ^ 16 = (f1024Alpha ^ 8) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 8)) ^ 2 := by
        rw [why24Alpha_pow_eq_mk]
      _ = AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 9 + Polynomial.X ^ 6) := by
        apply why24_square_residue (Polynomial.X ^ 8)
          (Polynomial.X ^ 9 + Polynomial.X ^ 6) (Polynomial.X ^ 6)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h1 : f1024Alpha ^ 32 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X) := by
    calc
      f1024Alpha ^ 32 = (f1024Alpha ^ 16) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus (Polynomial.X ^ 9 + Polynomial.X ^ 6)) ^ 2 := by rw [h0]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X) := by
        apply why24_square_residue (Polynomial.X ^ 9 + Polynomial.X ^ 6)
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)
          (Polynomial.X ^ 8 + Polynomial.X ^ 2 + Polynomial.X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h2 : f1024Alpha ^ 64 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
        Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) := by
    calc
      f1024Alpha ^ 64 = (f1024Alpha ^ 32) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)) ^ 2 := by rw [h1]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) := by
        apply why24_square_residue
          (Polynomial.X ^ 8 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1) (Polynomial.X ^ 6 + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h3 : f1024Alpha ^ 128 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1) := by
    calc
      f1024Alpha ^ 128 = (f1024Alpha ^ 64) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1)) ^ 2 := by rw [h2]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1) := by
        apply why24_square_residue
          (Polynomial.X ^ 9 + Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 4 +
            Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1)
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1)
          (Polynomial.X ^ 8 + Polynomial.X ^ 6 + Polynomial.X ^ 2 + Polynomial.X)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  have h4 : f1024Alpha ^ 256 = AdjoinRoot.mk f1024Modulus
      (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X) := by
    calc
      f1024Alpha ^ 256 = (f1024Alpha ^ 128) ^ 2 := by ring
      _ = (AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1)) ^ 2 := by rw [h3]
      _ = AdjoinRoot.mk f1024Modulus
          (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X) := by
        apply why24_square_residue
          (Polynomial.X ^ 9 + Polynomial.X ^ 5 + Polynomial.X ^ 2 + Polynomial.X + 1)
          (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X)
          (Polynomial.X ^ 8 + Polynomial.X + 1)
        simp only [f1024Modulus]
        ring_nf
        reduce_mod_char
  exact h4

private theorem why24_rootFour_alpha_add_alpha_pow_four_ne_zero :
    why24FrobeniusRootFour f1024Alpha + f1024Alpha ^ 4 ≠ 0 := by
  rw [why24FrobeniusRootFour_alpha, why24Alpha_pow_eq_mk]
  simp only [map_add, map_pow, AdjoinRoot.mk_X]
  intro hzero
  have hdiv : f1024Modulus ∣
      Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.X ^ 4 :=
    AdjoinRoot.mk_eq_zero.mp hzero
  have hpoly_ne :
      (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.X ^ 4 : Polynomial (ZMod 2)) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun f : Polynomial (ZMod 2) => f.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at hcoeff
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv hpoly_ne
  have htarget_degree :
      (Polynomial.X ^ 8 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.X ^ 4 : Polynomial (ZMod 2)).natDegree ≤ 8 := by
    apply Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_add_le_of_degree_le
          (Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)) (by simp))
        (by simp))
      (by simp)
  rw [f1024Modulus_natDegree] at hdegree
  omega

private theorem exists_why24_trace_mul_ne_zero {d : F1024} (hd : d ≠ 0) :
    ∃ η : F1024, Algebra.trace (ZMod 2) F1024 (d * η) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hd
  apply f1024SelectedCoordinates.injective
  funext i
  have hcoordinate :
      Algebra.trace (ZMod 2) F1024 (d * f1024SelectedSelfDualBasis i) =
        f1024SelectedCoordinates d i := by
    calc
      Algebra.trace (ZMod 2) F1024 (d * f1024SelectedSelfDualBasis i) =
          (f1024SelectedSelfDualBasis.traceDual).repr d i := by
            simpa only [Algebra.traceForm_apply] using
              (Module.Basis.traceDual_repr_apply f1024SelectedSelfDualBasis d i).symm
      _ = f1024SelectedSelfDualBasis.repr d i := by
            rw [f1024SelectedSelfDualBasis_traceDual]
      _ = f1024SelectedCoordinates d i := rfl
  simpa using hcoordinate.symm.trans (h (f1024SelectedSelfDualBasis i))

private theorem why24QuditX_zero : why24QuditX (0 : F1024) = 1 := by
  ext ψ η
  simp [why24QuditX_apply]

private theorem why24QuditZ_zero : why24QuditZ (0 : F1024) = 1 := by
  ext ψ η
  simp [why24QuditZ_apply]

private theorem why24QuditX_mul_self (b : F1024) :
    why24QuditX b * why24QuditX b = 1 := by
  rw [why24QuditX_mul, CharTwo.add_self_eq_zero, why24QuditX_zero]

private theorem why24QuditZ_mul_self (c : F1024) :
    why24QuditZ c * why24QuditZ c = 1 := by
  rw [why24QuditZ_mul, CharTwo.add_self_eq_zero, why24QuditZ_zero]

/-- Conjugating a shift by a literal source Pauli has no remaining `Z` label. -/
private theorem why24FieldPauliOperator_conjX (P : Why24FieldPauli) (γ : F1024) :
    ∃ a : ZMod 4,
      why24FieldPauliOperator P * why24QuditX γ *
        LinearMap.adjoint (why24FieldPauliOperator P) =
          why24FieldPauliOperator (a, γ, 0) := by
  rcases P with ⟨a, b, c⟩
  let Xlabel : Why24FieldPauli := (0, γ, 0)
  let R : Why24FieldPauli :=
    why24FieldPauliMul
      (why24FieldPauliMul (a, b, c) Xlabel)
      (why24FieldPauliDagger (a, b, c))
  have hX : why24QuditX γ = why24FieldPauliOperator Xlabel := by
    simpa [Xlabel] using (why24FieldPauliOperator_X γ).symm
  have hR :
      why24FieldPauliOperator (a, b, c) * why24FieldPauliOperator Xlabel *
        LinearMap.adjoint (why24FieldPauliOperator (a, b, c)) =
          why24FieldPauliOperator R := by
    simp only [R]
    rw [why24FieldPauliOperator_mul, why24FieldPauliOperator_mul,
      why24FieldPauliOperator_adjoint]
  have hlabel : b + γ + b = γ := by
    calc
      b + γ + b = γ + (b + b) := by ac_rfl
      _ = γ := by rw [CharTwo.add_self_eq_zero, add_zero]
  refine ⟨R.1, ?_⟩
  rw [hX]
  calc
    why24FieldPauliOperator (a, b, c) * why24FieldPauliOperator Xlabel *
        LinearMap.adjoint (why24FieldPauliOperator (a, b, c)) =
        why24FieldPauliOperator R := hR
    _ = why24FieldPauliOperator (R.1, γ, 0) := by
      congr 1
      simp [R, Xlabel, why24FieldPauliMul, why24FieldPauliDagger,
        CharTwo.add_self_eq_zero, hlabel]

/-- The explicit root-four witness makes the fifth source diagonal non-Pauli. -/
private theorem why24U_five_not_fieldPauli :
    ¬ ∃ P : Why24FieldPauli, why24U (1 : F1024) 5 = why24FieldPauliOperator P := by
  intro hpauli
  rcases hpauli with ⟨P, hP⟩
  let d : F1024 := why24FrobeniusRootFour f1024Alpha + f1024Alpha ^ 4
  have hd : d ≠ 0 := by
    simpa [d] using why24_rootFour_alpha_add_alpha_pow_four_ne_zero
  obtain ⟨η, hη⟩ := exists_why24_trace_mul_ne_zero hd
  obtain ⟨a, ha⟩ := why24FieldPauliOperator_conjX P f1024Alpha
  have hconj := why24U_conjX_five (1 : F1024) f1024Alpha
  rw [hP] at hconj
  have heq : why24FieldPauliOperator (a, f1024Alpha, 0) =
      PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) •
        (why24QuditX f1024Alpha * why24QuditZ d) := by
    calc
      why24FieldPauliOperator (a, f1024Alpha, 0) =
          why24FieldPauliOperator P * why24QuditX f1024Alpha *
            LinearMap.adjoint (why24FieldPauliOperator P) := ha.symm
      _ = PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) •
          (why24QuditX f1024Alpha * why24QuditZ d) := by
            simpa [d, mul_assoc] using hconj
  have hbase := congrArg
    (fun T : Semantics.Operator Why24QuditSpace =>
      T (why24QuditComputationalBasis (0 : F1024)) f1024Alpha) heq
  have hshift : (η + f1024Alpha) + f1024Alpha = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hpoint := congrArg
    (fun T : Semantics.Operator Why24QuditSpace =>
      T (why24QuditComputationalBasis η) (η + f1024Alpha)) heq
  have hbase' : why24PauliPhase a =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) := by
    simpa [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
      why24QuditX_apply, why24QuditZ_apply, why24QuditComputationalBasis,
      PiLp.single_apply, smul_eq_mul, CharTwo.add_self_eq_zero] using hbase
  have hpoint' : why24PauliPhase a =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5)) *
        PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 (d * η)) := by
    simpa [why24FieldPauliOperator, why24PauliPhase, Module.End.mul_apply,
      why24QuditX_apply, why24QuditZ_apply, why24QuditComputationalBasis,
      PiLp.single_apply, smul_eq_mul, hshift] using hpoint
  let s : Complex := PauliSymplectic.binaryPhaseScalar
    (Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5))
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    by_cases ht : Algebra.trace (ZMod 2) F1024 (f1024Alpha ^ 5) = 0
    · simp [PauliSymplectic.binaryPhaseScalar, ht]
    · have htRaw :
        Algebra.trace (ZMod 2) F1024 ((1 : F1024) * f1024Alpha ^ 5) ≠ 0 := by
          simpa only [one_mul] using ht
      rw [PauliSymplectic.zmod_two_eq_one_of_ne_zero htRaw]
      simp
  have hphase : PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (d * η)) = 1 := by
    apply mul_left_cancel₀ hs_ne
    simpa only [mul_one] using hpoint'.symm.trans hbase'
  apply hη
  exact (PauliSymplectic.binaryPhaseScalar_eq_one_iff _).mp hphase

private theorem why24U_five_is_fieldPauli_of_u7_normalizes
    (hU : why24FieldNormalizesPaulis why24UOneSeven) :
    ∃ P : Why24FieldPauli, why24U (1 : F1024) 5 = why24FieldPauliOperator P := by
  let t : ZMod 2 := Algebra.trace (ZMod 2) F1024 ((1 : F1024) ^ 7)
  let Xlabel : Why24FieldPauli := (0, (1 : F1024), 0)
  obtain ⟨Q, hQ⟩ := hU Xlabel
  have hX : why24FieldPauliOperator Xlabel = why24QuditX (1 : F1024) := by
    simpa [Xlabel] using why24FieldPauliOperator_X (1 : F1024)
  have hconj : PauliSymplectic.binaryPhaseScalar t •
      (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 * why24QuditZ (1 : F1024)) =
        why24FieldPauliOperator Q := by
    calc
      PauliSymplectic.binaryPhaseScalar t •
          (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
            why24QuditZ (1 : F1024)) =
          why24UOneSeven * why24QuditX (1 : F1024) *
            LinearMap.adjoint why24UOneSeven := by
              simpa [t] using why24UOneSeven_conjX_one.symm
      _ = why24FieldPauliOperator Q := by simpa [hX] using hQ
  have hsign : why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
      why24QuditZ (1 : F1024) =
        PauliSymplectic.binaryPhaseScalar t • why24FieldPauliOperator Q := by
    calc
      why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
          why24QuditZ (1 : F1024) =
          (1 : Complex) •
            (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
              why24QuditZ (1 : F1024)) := by simp
      _ = (PauliSymplectic.binaryPhaseScalar t *
          PauliSymplectic.binaryPhaseScalar t) •
            (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
              why24QuditZ (1 : F1024)) := by
                rw [why24_binaryPhaseScalar_mul_self]
      _ = PauliSymplectic.binaryPhaseScalar t •
          (PauliSymplectic.binaryPhaseScalar t •
            (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
              why24QuditZ (1 : F1024))) := by rw [smul_smul]
      _ = PauliSymplectic.binaryPhaseScalar t • why24FieldPauliOperator Q := by
            rw [hconj]
  rcases Q with ⟨a, b, c⟩
  let phaseLabel : Why24FieldPauli := (a + 2 * (t.val : ZMod 4), b, c)
  have hphase : PauliSymplectic.binaryPhaseScalar t •
      why24FieldPauliOperator (a, b, c) = why24FieldPauliOperator phaseLabel := by
    change PauliSymplectic.binaryPhaseScalar t •
        (why24PauliPhase a • (why24QuditX b * why24QuditZ c)) =
      why24PauliPhase (a + 2 * (t.val : ZMod 4)) •
        (why24QuditX b * why24QuditZ c)
    rw [smul_smul, ← why24PauliPhase_two_trace,
      mul_comm (why24PauliPhase (2 * (t.val : ZMod 4))) (why24PauliPhase a),
      ← why24PauliPhase_add]
  let Zlabel : Why24FieldPauli := (0, 0, (1 : F1024))
  refine ⟨why24FieldPauliMul
      (why24FieldPauliMul Xlabel phaseLabel) Zlabel, ?_⟩
  calc
    why24U (1 : F1024) 5 =
        (1 : Semantics.Operator Why24QuditSpace) * why24U (1 : F1024) 5 *
          (1 : Semantics.Operator Why24QuditSpace) := by simp
    _ = (why24QuditX (1 : F1024) * why24QuditX (1 : F1024)) *
        why24U (1 : F1024) 5 *
        (why24QuditZ (1 : F1024) * why24QuditZ (1 : F1024)) := by
          rw [why24QuditX_mul_self, why24QuditZ_mul_self]
    _ = why24QuditX (1 : F1024) *
        (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 *
          why24QuditZ (1 : F1024)) * why24QuditZ (1 : F1024) := by
          simp only [mul_assoc]
    _ = why24QuditX (1 : F1024) *
        (PauliSymplectic.binaryPhaseScalar t • why24FieldPauliOperator (a, b, c)) *
          why24QuditZ (1 : F1024) := by rw [hsign]
    _ = why24QuditX (1 : F1024) * why24FieldPauliOperator phaseLabel *
          why24QuditZ (1 : F1024) := by rw [hphase]
    _ = why24FieldPauliOperator
        (why24FieldPauliMul (why24FieldPauliMul Xlabel phaseLabel) Zlabel) := by
            rw [← hX, ← why24FieldPauliOperator_Z]
            simp only [Zlabel]
            rw [← why24FieldPauliOperator_mul, ← why24FieldPauliOperator_mul]

/-- The source-selected seventh-power diagonal is not a field Pauli normalizer. -/
theorem why24UOneSeven_not_fieldClifford : ¬ Why24FieldClifford why24UOneSeven := by
  intro hclifford
  apply why24U_five_not_fieldPauli
  exact why24U_five_is_fieldPauli_of_u7_normalizes hclifford.2

/-- The concrete selected ten-qubit transport of the source's `U₁^(7)` diagonal. -/
noncomputable def why24QubitUOneSeven : Semantics.Operator Why24QubitSpace :=
  why24QuditQubitUnitary.conjOperator why24UOneSeven

/-- The transported qubit operator is definitionally the concrete conjugate. -/
theorem why24QuditQubitUnitary_conjUOneSeven :
    why24QuditQubitUnitary.conjOperator why24UOneSeven = why24QubitUOneSeven := rfl

end QEC.Coding
