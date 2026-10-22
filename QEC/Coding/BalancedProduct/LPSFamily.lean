import QEC.Coding.BalancedProduct.LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The unbounded admissible LPS family used by BE20

This file closes the arithmetic family assembly that is independent of the
LPS spectral theorem.  Dirichlet's theorem supplies primes congruent to `3`
modulo `401`; quadratic reciprocity turns that congruence into the required
Legendre-symbol condition.  We also compute the exact order of `PGL(2,q)` and
the two quotient Tanner coordinate counts.

No spectral, Tanner, distance, locality, or terminal parameter statement is
accepted as data here.
-/

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSFamily

open Matrix
open LPSGraph LPSTanner LPSQuotientTanner

/-- An arithmetic index for the concrete BE20 LPS family.  This record stores
only decidable number-theoretic facts; in particular it contains no spectral
or coding-theoretic premise. -/
structure AdmissiblePrime401 where
  q : Nat
  prime : q.Prime
  gt40 : 40 < q
  legendre : @legendreSym q ⟨prime⟩ 401 = -1

instance (a : AdmissiblePrime401) : Fact a.q.Prime := ⟨a.prime⟩

/-- The one approved external boundary, uniformly quantified over the actual
prime family.  It is a transparent abbreviation for the graph-only Rayleigh
statement and stores no derived Tanner or code conclusion. -/
def LPS401FamilyRayleighBound : Prop :=
  ∀ (q : Nat) (hqPrime : q.Prime) (hq40 : 40 < q)
    (hq : @legendreSym q ⟨hqPrime⟩ 401 = -1),
    @LPS401RayleighBound q ⟨hqPrime⟩ hq

/-- There are admissible BE20 primes above every natural bound.  The residue
class `3 mod 401` is coprime to `401`; because `401 = 1 mod 4`, quadratic
reciprocity identifies `(401/q)` with `(q/401)`, whose value at `3` is `-1`. -/
theorem exists_admissiblePrime401_gt (B : Nat) :
    ∃ a : AdmissiblePrime401, B < a.q := by
  obtain ⟨q, hqB, hqPrime, hqMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B 401)
      (q := 401) (a := 3) (by norm_num) (by norm_num)
  haveI : Fact q.Prime := ⟨hqPrime⟩
  haveI : Fact (401 : Nat).Prime := ⟨by native_decide⟩
  have hq40 : 40 < q := by omega
  have hLegendre : @legendreSym q ⟨hqPrime⟩ 401 = -1 := by
    change legendreSym q (401 : ℤ) = -1
    have hqr : legendreSym q (401 : ℤ) = legendreSym 401 (q : ℤ) :=
      legendreSym.quadratic_reciprocity_one_mod_four
        (p := 401) (q := q) (by norm_num) (by omega)
    rw [hqr, legendreSym.mod]
    have hmod : q % 401 = 3 := hqMod
    rw [← Int.natCast_mod, hmod]
    exact (by native_decide :
      @legendreSym 401 ⟨by native_decide⟩ 3 = -1)
  exact ⟨⟨q, hqPrime, hq40, hLegendre⟩,
    lt_of_le_of_lt (Nat.le_max_left B 401) hqB⟩

/-- A deterministic (noncomputable) admissible prime above `B`. -/
noncomputable def admissiblePrime401At (B : Nat) : AdmissiblePrime401 :=
  Classical.choose (exists_admissiblePrime401_gt B)

theorem lt_admissiblePrime401At (B : Nat) :
    B < (admissiblePrime401At B).q :=
  Classical.choose_spec (exists_admissiblePrime401_gt B)

/-- Exact order of the concrete LPS vertex group. -/
theorem card_pgl_two_zmod
    (q : Nat) [Fact q.Prime] (hq40 : 40 < q) :
    Fintype.card (PGL(2, ZMod q)) = q * (q ^ 2 - 1) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI : Fintype (GL (Fin 2) (ZMod q)) :=
    Fintype.ofInjective Units.val Units.val_injective
  have hscalar : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (ZMod q)ˣ →* GL (Fin 2) (ZMod q)) := by
    intro u v huv
    apply Units.ext
    have hentry := congrArg
      (fun A : GL (Fin 2) (ZMod q) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) huv
    simpa using hentry
  have hcenter :
      Nat.card (Subgroup.center (GL (Fin 2) (ZMod q))) = q - 1 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card (ZMod q)ˣ :=
        (Nat.card_congr (Equiv.ofInjective _ hscalar)).symm
      _ = q - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hGL : Nat.card (GL (Fin 2) (ZMod q)) =
      (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field (n := 2)]
    simp [ZMod.card]
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (GL (Fin 2) (ZMod q)))
  change Nat.card (GL (Fin 2) (ZMod q)) =
    Nat.card (PGL(2, ZMod q)) *
      Nat.card (Subgroup.center (GL (Fin 2) (ZMod q))) at hquot
  rw [hGL, hcenter] at hquot
  have hfactor : q ^ 2 - q = q * (q - 1) := by
    simp [pow_two, Nat.mul_sub_left_distrib]
  rw [hfactor, Nat.card_eq_fintype_card] at hquot
  apply Nat.mul_right_cancel (by omega : 0 < q - 1)
  calc
    Fintype.card PGL(2, ZMod q) * (q - 1) =
        (q ^ 2 - 1) * (q * (q - 1)) := hquot.symm
    _ = (q * (q ^ 2 - 1)) * (q - 1) := by ring

/-- Exact LPS vertex count in the notation of the Tanner construction. -/
theorem card_vertex401
    (q : Nat) [Fact q.Prime] (hq40 : 40 < q) :
    Fintype.card (Vertex401 q) = q * (q ^ 2 - 1) :=
  card_pgl_two_zmod q hq40

/-- The free cyclic quotient has exactly `201(q^2-1)` Tanner bits. -/
theorem card_edgeOrbit401
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (EdgeOrbit401 q hq) = 201 * (q ^ 2 - 1) := by
  have hqpos : 0 < q := by omega
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    q * Fintype.card (EdgeOrbit401 q hq) =
        Fintype.card (Edge401 q hq) :=
      (card_edge401_eq_cyclic_mul_edgeOrbit q hq).symm
    _ = 201 * Fintype.card (Vertex401 q) :=
      LPSTannerExpansion.card_edge401_eq q hq40 hq
    _ = q * (201 * (q ^ 2 - 1)) := by
      rw [card_vertex401 q hq40]
      ring

/-- The free cyclic quotient has exactly `200(q^2-1)` Tanner checks. -/
theorem card_checkOrbit401
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) :
    Fintype.card (CheckOrbit401 q) = 200 * (q ^ 2 - 1) := by
  have hqpos : 0 < q := by omega
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    q * Fintype.card (CheckOrbit401 q) =
        Fintype.card (Check401 q) :=
      (card_check401_eq_cyclic_mul_checkOrbit q).symm
    _ = 200 * Fintype.card (Vertex401 q) :=
      LPSTannerExpansion.card_check401_eq q
    _ = q * (200 * (q ^ 2 - 1)) := by
      rw [card_vertex401 q hq40]
      ring

/-- The quotient Tanner rank-nullity gap is exactly `q^2-1`. -/
theorem card_edgeOrbit401_sub_checkOrbit401
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (EdgeOrbit401 q hq) -
        Fintype.card (CheckOrbit401 q) = q ^ 2 - 1 := by
  rw [card_edgeOrbit401 q hq40 hq, card_checkOrbit401 q hq40]
  omega

/-- The corrected BE20 blocklength is the exact cubic polynomial
`401 q (q^2-1)`. -/
theorem lpsHorizontalSubsystem_blocklength_eq_polynomial
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
          (Cyclic.CyclicGroup q)) =
      401 * q * (q ^ 2 - 1) := by
  rw [lpsHorizontalSubsystem_blocklength_eq q hq40 hq,
    card_vertex401 q hq40]
  ring

/-- The horizontal logical dimension is at least the exact quotient
rank-nullity gap `q^2-1`. -/
theorem lpsHorizontalSubsystem_logicalQubits_lowerBound_polynomial
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    let hOdd : Odd q :=
      (Fact.out : q.Prime).odd_of_ne_two (by omega)
    let D := HorizontalSubsystem.horizontalSubsystem
      (lpsTannerGroupAlgebraMatrix q hq40 hq)
      (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)
    q ^ 2 - 1 ≤ D.logicalQubits := by
  classical
  dsimp only
  rw [← card_edgeOrbit401_sub_checkOrbit401 q hq40 hq]
  exact lpsHorizontalSubsystem_logicalQubits_lowerBound q hq40 hq

/-- The horizontal logical dimension is at most the quotient Tanner bit
count, hence at most `201(q^2-1)`. -/
theorem lpsHorizontalSubsystem_logicalQubits_upperBound_polynomial
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    let hOdd : Odd q :=
      (Fact.out : q.Prime).odd_of_ne_two (by omega)
    let D := HorizontalSubsystem.horizontalSubsystem
      (lpsTannerGroupAlgebraMatrix q hq40 hq)
      (Cyclic.cyclicGenerator q)
      (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)
    D.logicalQubits ≤ 201 * (q ^ 2 - 1) := by
  classical
  dsimp only
  rw [HorizontalSubsystem.horizontalSubsystem_logicalQubits,
    HorizontalSubsystem.finrank_quotientTannerComplex_middleHomology_eq_ker]
  calc
    Module.finrank (ZMod 2)
        (LinearMap.ker (HorizontalSubsystem.quotientBoundary
          (lpsTannerGroupAlgebraMatrix q hq40 hq))) ≤
        Module.finrank (ZMod 2)
          (Word (ZMod 2) (EdgeOrbit401 q hq)) :=
      Submodule.finrank_le _
    _ = Fintype.card (EdgeOrbit401 q hq) := by simp
    _ = 201 * (q ^ 2 - 1) := card_edgeOrbit401 q hq40 hq

end QEC.Coding.BalancedProduct.LPSFamily
