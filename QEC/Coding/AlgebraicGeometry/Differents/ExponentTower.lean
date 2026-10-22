import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Different exponents in a tower of Dedekind domains

This file isolates the tower calculation used in the source-faithful
Garcia--Stichtenoth normal-closure argument.  It first takes multiplicities in
Mathlib's transitivity identity for the different ideal.  It then proves that
the weak different formula `d = 2 * (e - 1)` is preserved by composition.

No Garcia--Stichtenoth ramification hypothesis, normal-closure different,
genus, canonical divisor, or asymptotic conclusion is stored here.
-/

open Module

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private theorem two_mul_sub_one_tower_arithmetic
    (e₁ e₂ : ℕ) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) :
    2 * (e₂ - 1) + e₂ * (2 * (e₁ - 1)) =
      2 * (e₁ * e₂ - 1) := by
  obtain ⟨e₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he₁
  obtain ⟨e₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he₂
  simp only [Nat.succ_sub_one]
  have hproduct : Nat.succ e₁ * Nat.succ e₂ =
      Nat.succ (e₁ * e₂ + e₁ + e₂) := by
    simp only [Nat.succ_eq_add_one]
    ring
  rw [hproduct, Nat.succ_sub_one]
  simp only [Nat.succ_eq_add_one]
  ring

/-- Multiplicity form of transitivity of the different ideal at a nonzero
prime chain `p ⊂ P ⊂ Q`. -/
theorem differentIdeal_multiplicity_tower
    (A B C : Type*)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [FaithfulSMul B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [P.IsPrime] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hp : p ≠ ⊥) :
    multiplicity Q (differentIdeal A C) =
      multiplicity Q (differentIdeal B C) +
        P.ramificationIdx' Q * multiplicity P (differentIdeal A B) := by
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  letI : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  have hP_ne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hQ_ne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hP_ne Q
  have hP_prime : Prime P := Ideal.prime_of_isPrime hP_ne inferInstance
  have hQ_prime : Prime Q := Ideal.prime_of_isPrime hQ_ne inferInstance
  have hAC_ne : differentIdeal A C ≠ ⊥ := differentIdeal_ne_bot
  have hBC_ne : differentIdeal B C ≠ ⊥ := differentIdeal_ne_bot
  have hAB_ne : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hAC_finite : FiniteMultiplicity Q (differentIdeal A C) :=
    FiniteMultiplicity.of_prime_left hQ_prime hAC_ne
  have hBC_finite : FiniteMultiplicity Q (differentIdeal B C) :=
    FiniteMultiplicity.of_prime_left hQ_prime hBC_ne
  have hAB_finite : FiniteMultiplicity P (differentIdeal A B) :=
    FiniteMultiplicity.of_prime_left hP_prime hAB_ne
  have hemultiplicity :
      emultiplicity Q (differentIdeal A C) =
        emultiplicity Q (differentIdeal B C) +
          P.ramificationIdx' Q * emultiplicity P (differentIdeal A B) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal A B C]
    rw [emultiplicity_mul hQ_prime]
    rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
      hAB_ne hP_prime.irreducible hQ_prime.irreducible hQ_ne]
  rw [hAC_finite.emultiplicity_eq_multiplicity,
    hBC_finite.emultiplicity_eq_multiplicity,
    hAB_finite.emultiplicity_eq_multiplicity] at hemultiplicity
  exact_mod_cast hemultiplicity

/-- If both stages in a nonzero prime chain have weak different exponent
`2 * (e - 1)`, then the composite stage has the same formula. -/
theorem differentIdeal_multiplicity_eq_two_mul_ramificationIdx_sub_one_tower
    (A B C : Type*)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [FaithfulSMul B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [P.IsPrime] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hp : p ≠ ⊥)
    (hAB : multiplicity P (differentIdeal A B) =
      2 * (p.ramificationIdx' P - 1))
    (hBC : multiplicity Q (differentIdeal B C) =
      2 * (P.ramificationIdx' Q - 1)) :
    multiplicity Q (differentIdeal A C) =
      2 * (p.ramificationIdx' Q - 1) := by
  have hP_ne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have heAB_ne : p.ramificationIdx' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  have heBC_ne : P.ramificationIdx' Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q hP_ne
  rw [differentIdeal_multiplicity_tower A B C p P Q hp, hAB, hBC,
    Ideal.ramificationIdx_algebra_tower' p P Q]
  exact two_mul_sub_one_tower_arithmetic
    (p.ramificationIdx' P) (P.ramificationIdx' Q) heAB_ne heBC_ne

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
