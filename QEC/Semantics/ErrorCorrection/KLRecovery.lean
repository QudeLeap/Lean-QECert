import QEC.Semantics.Channels.KrausKnillLaflamme
import QEC.Semantics.Channels.ChoiKraus
/-!
# Finite-Kraus Knill-Laflamme recovery prerequisites

This module records proved algebraic facts needed by the finite-Kraus
Knill-Laflamme recovery construction.  It deliberately does not assert a
recovery channel before the projection/partial-isometry construction is
formalized.
-/

universe u v w

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

namespace FiniteKrausFamily

variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/--
For complete finite Kraus noise, indexed KL projector data has normalized
diagonal scalar sum on the code projector.

This is the scalar-normalization step needed before building a CPTP recovery
from the KL Gram data.
-/
theorem indexedProjectorConditionWithScalar_complete_diagonal_sum
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hE : E.Complete)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    (∑ i : ι, scalar i i) • C.projector = C.projector := by
  ext x
  calc
    ((∑ i : ι, scalar i i) • C.projector) x
        = ((∑ i : ι, scalar i i • C.projector) : Operator H) x := by
          rw [Finset.sum_smul]
    _ = ∑ i : ι, ((scalar i i • C.projector) x) := by
          simp
    _ = ∑ i : ι,
          (((C.projector.comp
            ((LinearMap.adjoint (E.operator i)).comp (E.operator i))).comp
              C.projector) x) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact congrArg (fun A : Operator H => A x) (hKL i i).symm
    _ = C.projector
          ((∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))
            (C.projector x)) := by
          simp [LinearMap.comp_apply, Finset.sum_apply]
    _ = C.projector x := by
          rw [hE]
          exact C.projector_eq_self_of_mem (C.projector_mem_carrier x)

/--
Indexed KL projector data is Hermitian on the code projector.  The equality is
kept at projector level so it remains valid for degenerate code carriers.
-/
theorem indexedProjectorConditionWithScalar_adjoint_projector
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar)
    (i j : ι) :
    star (scalar i j) • C.projector = scalar j i • C.projector := by
  have hij := hKL i j
  have hadj := congrArg LinearMap.adjoint hij
  have hAdjLeft :
      LinearMap.adjoint
          ((C.projector.comp ((LinearMap.adjoint (E.operator i)).comp
            (E.operator j))).comp C.projector) =
        (C.projector.comp ((LinearMap.adjoint (E.operator j)).comp
            (E.operator i))).comp C.projector := by
    ext x
    simp [LinearMap.adjoint_comp, C.projector_adjoint_eq_self,
      LinearMap.comp_apply]
  have hAdjRight :
      LinearMap.adjoint (scalar i j • C.projector) =
        star (scalar i j) • C.projector := by
    simpa [C.projector_adjoint_eq_self] using
      (map_smulₛₗ (LinearMap.adjoint : (Operator H) ≃ₗ⋆[Complex] Operator H)
        (scalar i j) C.projector)
  calc
    star (scalar i j) • C.projector
        = LinearMap.adjoint (scalar i j • C.projector) := hAdjRight.symm
    _ = LinearMap.adjoint
          ((C.projector.comp ((LinearMap.adjoint (E.operator i)).comp
            (E.operator j))).comp C.projector) := by
          rw [hij]
    _ = (C.projector.comp ((LinearMap.adjoint (E.operator j)).comp
            (E.operator i))).comp C.projector := hAdjLeft
    _ = scalar j i • C.projector := hKL j i

/--
The matrix-element indexed KL scalar data for a complete family has normalized
diagonal scalar sum on the code projector.
-/
theorem indexedConditionWithScalar_complete_diagonal_sum
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hE : E.Complete)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (∑ i : ι, scalar i i) • C.projector = C.projector :=
  indexedProjectorConditionWithScalar_complete_diagonal_sum hE
    (indexedProjectorConditionWithScalar_of_indexedConditionWithScalar hKL)

/--
Same-space finite-Kraus KL data can be represented by indexed scalars whose
diagonal sum is normalized on the code projector whenever the noise is complete.
-/
theorem sameSpaceKnillLaflammeCriterion_exists_indexed_scalar_complete_diagonal_sum
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeConditionWithScalar E C scalar ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).1 hKL with
    ⟨scalar, hscalar⟩
  exact ⟨scalar, hscalar,
    indexedConditionWithScalar_complete_diagonal_sum hE hscalar⟩

/--
Same-space finite-Kraus KL data for complete noise admits indexed projector
scalars with the two algebraic properties needed by the recovery construction:
normalized diagonal sum and Hermitian symmetry on the code projector.
-/
theorem sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_recoveryData
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector ∧
        ∀ i j : ι, star (scalar i j) • C.projector = scalar j i • C.projector := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation C).1 hKL with
    ⟨scalar, hscalar⟩
  exact ⟨scalar, hscalar,
    indexedProjectorConditionWithScalar_complete_diagonal_sum hE hscalar,
    indexedProjectorConditionWithScalar_adjoint_projector hscalar⟩

/--
If the code carrier is empty, the semantic correction obligation is vacuous.

This lemma isolates the degenerate branch of the KL-implies-correctable proof:
no density operator can have trace one and range in the bottom carrier.
-/
theorem correctable_id_of_carrier_eq_bot
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete) (hC : C.carrier = ⊥) :
    Correctable H H C (E.toQuantumChannel hE) (QuantumChannel.id H) := by
  intro rho hρ
  have hrho_zero : rho.toOperator = 0 := by
    ext v
    have hv : rho.toOperator v ∈ (⊥ : Submodule Complex H) := by
      simpa [hC] using hρ v
    simpa using hv
  have htrace_zero : LinearMap.trace Complex H rho.toOperator = 0 := by
    rw [hrho_zero]
    simp
  have hcontr : (1 : Complex) = 0 := by
    rw [rho.trace_one] at htrace_zero
    exact htrace_zero
  exact False.elim ((one_ne_zero : (1 : Complex) ≠ 0) hcontr)

/--
On a nonzero code carrier, indexed KL scalar data is a Hermitian matrix.

The proof evaluates the KL relation on a fixed nonzero code vector and cancels
its nonzero self-inner-product.
-/
theorem indexedConditionWithScalar_isHermitian_of_carrier_ne_bot
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hC : C.carrier ≠ ⊥)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (Matrix.of fun i j => scalar i j).IsHermitian := by
  classical
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hC with ⟨z, hzC, hz_ne⟩
  apply Matrix.IsHermitian.ext
  intro i j
  have hij := hKL i j z hzC z hzC
  have hji := hKL j i z hzC z hzC
  have hinner_ne : inner Complex z z ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hz_norm_ne : ‖z‖ ≠ 0 := by
      simpa [norm_eq_zero] using hz_ne
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz_norm_ne)
  have hstar :
      star (inner Complex (E.operator j z) (E.operator i z)) =
        inner Complex (E.operator i z) (E.operator j z) := by
    simp
  have hscalar :
      star (scalar j i * inner Complex z z) =
        scalar i j * inner Complex z z := by
    rw [← hji, hstar, hij]
  have hinner_self : star (inner Complex z z) = inner Complex z z := by
    simp
  rw [star_mul, hinner_self] at hscalar
  have hscalar' :
      star (scalar j i) * inner Complex z z =
        scalar i j * inner Complex z z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscalar
  exact mul_right_cancel₀ hinner_ne hscalar'

/--
On a nonzero code carrier, indexed KL scalar data is positive semidefinite.

The scalar matrix is a nonnegative scalar multiple of the Gram matrix of the
vectors `E_i z` for any fixed nonzero code vector `z`.
-/
theorem indexedConditionWithScalar_posSemidef_of_carrier_ne_bot
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hC : C.carrier ≠ ⊥)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (Matrix.of fun i j => scalar i j).PosSemidef := by
  classical
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hC with ⟨z, hzC, hz_ne⟩
  let G : Matrix ι ι Complex := Matrix.gram Complex (fun i => E.operator i z)
  have hinner_ne : inner Complex z z ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hz_norm_ne : ‖z‖ ≠ 0 := by
      simpa [norm_eq_zero] using hz_ne
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz_norm_ne)
  have hinner_nonneg : 0 ≤ inner Complex z z := by
    rw [inner_self_eq_norm_sq_to_K]
    positivity
  have hEq :
      (Matrix.of fun i j => scalar i j) = (inner Complex z z)⁻¹ • G := by
    ext i j
    have hij := hKL i j z hzC z hzC
    have hscalar :
        scalar i j =
          (inner Complex z z)⁻¹ * inner Complex (E.operator i z) (E.operator j z) := by
      rw [hij]
      field_simp [hinner_ne]
    simp [G, hscalar]
  rw [hEq]
  exact (Matrix.posSemidef_gram Complex (fun i => E.operator i z)).smul
    ((inv_nonneg).2 hinner_nonneg)

/--
Same-space finite-Kraus KL data for complete noise has normalized projector
scalar data whose scalar matrix is positive semidefinite on a nonzero code.

This packages the algebraic input needed before the spectral diagonalization
step of the recovery construction.
-/
theorem sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hC : C.carrier ≠ ⊥)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar ∧
        (Matrix.of fun i j => scalar i j).PosSemidef ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector ∧
        ∀ i j : ι, star (scalar i j) • C.projector = scalar j i • C.projector := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation C).1 hKL with
    ⟨scalar, hscalar⟩
  exact ⟨scalar, hscalar,
    indexedConditionWithScalar_posSemidef_of_carrier_ne_bot hC
      (indexedConditionWithScalar_of_indexedProjectorConditionWithScalar hscalar),
    indexedProjectorConditionWithScalar_complete_diagonal_sum hE hscalar,
    indexedProjectorConditionWithScalar_adjoint_projector hscalar⟩

/--
Source-style forward KL calculation from explicit recovery branches.

If a finite recovery Kraus family is complete and every composite branch
`R_r E_i` acts as a scalar on the code carrier, then the same-space finite-Kraus
Knill-Laflamme condition follows.  This is only the algebraic endgame for the
correctable-implies-KL direction; deriving these branch scalars from an
arbitrary `QuantumChannel` recovery remains a separate proof obligation.
-/
theorem sameSpaceKnillLaflammeCriterion_of_recovery_branch_scalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (branchScalar : κ → ι → Complex)
    (hbranch : ∀ r i (x : H), x ∈ C.carrier →
      R r (E.operator i x) = branchScalar r i • x) :
    E.sameSpaceKnillLaflammeCriterion C := by
  classical
  rw [E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C]
  refine ⟨fun i j => ∑ r : κ, star (branchScalar r i) * branchScalar r j, ?_⟩
  intro i j x hx y hy
  calc
    inner Complex (E.operator i x) (E.operator j y)
        = inner Complex (((∑ r : κ, (LinearMap.adjoint (R r)).comp (R r))
            (E.operator i x))) (E.operator j y) := by
          rw [hR_complete]
          simp
    _ = ∑ r : κ,
          inner Complex (((LinearMap.adjoint (R r)).comp (R r)) (E.operator i x))
            (E.operator j y) := by
          simp [Finset.sum_apply]
    _ = ∑ r : κ, inner Complex (R r (E.operator i x)) (R r (E.operator j y)) := by
          apply Finset.sum_congr rfl
          intro r _hr
          simpa [LinearMap.comp_apply] using
            (LinearMap.adjoint_inner_left (𝕜 := Complex) (R r)
              (E.operator j y) (R r (E.operator i x)))
    _ = ∑ r : κ, (star (branchScalar r i) * branchScalar r j) *
          inner Complex x y := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [hbranch r i x hx, hbranch r j y hy]
          simp [mul_left_comm, mul_comm]
    _ = (∑ r : κ, star (branchScalar r i) * branchScalar r j) *
          inner Complex x y := by
          rw [Finset.sum_mul]

/--
If a linear operator sends every code vector into its own one-dimensional span,
then it is scalar on the whole code carrier.
-/
theorem operator_scalar_on_code_of_forall_mem_span
    (A : Operator H) (C : QuantumCode H)
    (hline : ∀ (x : H), x ∈ C.carrier → A x ∈ Complex ∙ x) :
    ∃ scalar : Complex, ∀ (x : H), x ∈ C.carrier → A x = scalar • x := by
  classical
  let fC : C.carrier →ₗ[Complex] C.carrier :=
    { toFun := fun x => ⟨A (x : H), by
        rcases Submodule.mem_span_singleton.mp (hline (x : H) x.prop) with ⟨a, ha⟩
        rw [← ha]
        exact C.carrier.smul_mem a x.prop⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact A.map_add (x : H) (y : H)
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact A.map_smul a (x : H) }
  have hdep : ∀ v : C.carrier, ¬ LinearIndependent Complex ![v, fC v] := by
    intro v
    have hvspan : fC v ∈ Complex ∙ v := by
      rcases Submodule.mem_span_singleton.mp (hline (v : H) v.prop) with ⟨a, ha⟩
      exact Submodule.mem_span_singleton.mpr ⟨a, by
        apply Subtype.ext
        simpa [fC] using ha⟩
    intro hli
    rw [linearIndependent_fin2] at hli
    rcases Submodule.mem_span_singleton.mp hvspan with ⟨a, ha⟩
    by_cases ha0 : a = 0
    · have hfzero : fC v = 0 := by
        rw [← ha, ha0, zero_smul]
      exact hli.1 hfzero
    · have hv_eq : a⁻¹ • fC v = v := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      exact hli.2 a⁻¹ hv_eq
  rcases LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := fC) hdep with
    ⟨scalar, hscalar⟩
  refine ⟨scalar, ?_⟩
  intro x hx
  have happly := congrArg (fun f : C.carrier →ₗ[Complex] C.carrier => f ⟨x, hx⟩) hscalar
  have happly_val := congrArg Subtype.val happly
  simpa [fC] using happly_val

/--
For a pure code state recovered exactly by finite Kraus branches, each composite
branch vector lies in the span of the input code vector.
-/
theorem recovery_branch_mem_span_of_finiteKraus_correctedBy
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
        rho.toOperator)
    (r : κ) (i : ι) {x : H} (hxC : x ∈ C.carrier) :
    R r (E.operator i x) ∈ Complex ∙ x := by
  classical
  by_cases hx0 : x = 0
  · subst x
    simp
  let rho : DensityOperator H := DensityOperator.pureOfNonzero x hx0
  let term : κ → ι → Operator H := fun r i =>
    ((R r).comp (E.operator i)).comp
      (rho.toOperator.comp (LinearMap.adjoint ((R r).comp (E.operator i))))
  have hsum : (∑ r : κ, ∑ i : ι, term r i) = rho.toOperator := by
    calc
      (∑ r : κ, ∑ i : ι, term r i)
          = ∑ r : κ, (R r).comp
              ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r))) := by
            ext y
            simp [term, FiniteKrausFamily.inducedMap_apply,
              LinearMap.adjoint_comp, Finset.sum_apply]
      _ = rho.toOperator := hcorrect rho (DensityOperator.pureOfNonzero_supportedOn hx0 hxC)
  have hmem_double : R r (E.operator i x) ∈ (Complex ∙ x)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hxy : inner Complex x y = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hy
    have hρy : rho.toOperator y = 0 := by
      simp [rho, hxy]
    have hquad : (∑ r : κ, ∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hyop := congrArg (fun A : Operator H => inner Complex (A y) y) hsum
      simpa [term, Finset.sum_apply, hρy] using hyop
    have hterm_pos : ∀ r i, LinearMap.IsPositive (term r i) := by
      intro r i
      change LinearMap.IsPositive
        (((R r).comp (E.operator i)).comp
          ((DensityOperator.pureOfNonzero x hx0).toOperator.comp
            (LinearMap.adjoint ((R r).comp (E.operator i)))))
      rw [DensityOperator.comp_pureOfNonzero_adjoint]
      have hpos : LinearMap.IsPositive
          (((InnerProductSpace.rankOne Complex (((R r).comp (E.operator i)) x)
            (((R r).comp (E.operator i)) x) : H →L[Complex] H) :
            H →ₗ[Complex] H)) := by
        exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := Complex)
          (((R r).comp (E.operator i)) x)).toLinearMap
      have hinner_nonneg : 0 ≤ inner Complex x x := by
        rw [inner_self_eq_norm_sq_to_K]
        positivity
      exact hpos.smul_of_nonneg ((inv_nonneg).2 hinner_nonneg)
    have h_outer_zero : (∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hfun : (fun r : κ => ∑ i : ι, inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro r
          exact Finset.sum_nonneg (by
            intro i _hi
            exact (hterm_pos r i).inner_nonneg_left y))).mp hquad
      exact congrFun hfun r
    have h_inner_zero : inner Complex ((term r i) y) y = 0 := by
      have hfun : (fun i : ι => inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro i
          exact (hterm_pos r i).inner_nonneg_left y)).mp h_outer_zero
      exact congrFun hfun i
    let A : Operator H := (R r).comp (E.operator i)
    have h_inner_rank :
        inner Complex
          (((((inner Complex x x)⁻¹ •
            (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
              H →ₗ[Complex] H))) : H →ₗ[Complex] H) y)) y = 0 := by
      have hterm_eq := DensityOperator.comp_pureOfNonzero_adjoint A x hx0
      rw [← hterm_eq]
      simpa [A, term, rho] using h_inner_zero
    have hc_ne : (inner Complex x x)⁻¹ ≠ 0 := inv_ne_zero (inner_self_ne_zero.mpr hx0)
    have h' :
        (inner Complex x x)⁻¹ * (inner Complex (A x) y * inner Complex y (A x)) = 0 := by
      simpa [inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using h_inner_rank
    have hprod : inner Complex (A x) y * inner Complex y (A x) = 0 := by
      exact (mul_eq_zero.mp h').resolve_left hc_ne
    have hAxy : inner Complex (A x) y = 0 := by
      rcases mul_eq_zero.mp hprod with hz | hy'
      · exact hz
      · exact inner_eq_zero_symm.mp hy'
    simpa [A, LinearMap.comp_apply] using hAxy
  rw [Submodule.orthogonal_orthogonal] at hmem_double
  exact hmem_double

/--
KL96 `theorem:linear` bridge for the project finite-Kraus recovery semantics:
exact correction of code-supported density operators by finite recovery
branches forces each composite branch `R_r E_i` to be scalar on the code.
-/
theorem exists_recovery_branch_scalar_of_finiteKraus_correctedBy
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (_hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
        rho.toOperator) :
    ∃ branchScalar : κ → ι → Complex,
      ∀ r i (x : H), x ∈ C.carrier →
        R r (E.operator i x) = branchScalar r i • x := by
  classical
  have hscalar : ∀ r i : _, ∃ scalar : Complex,
      ∀ (x : H), x ∈ C.carrier → ((R r).comp (E.operator i)) x = scalar • x := by
    intro r i
    exact operator_scalar_on_code_of_forall_mem_span ((R r).comp (E.operator i)) C
      (fun x hx => recovery_branch_mem_span_of_finiteKraus_correctedBy E C R hcorrect r i hx)
  choose branchScalar hbranch using hscalar
  refine ⟨branchScalar, ?_⟩
  intro r i x hx
  simpa [LinearMap.comp_apply] using hbranch r i x hx

/--
KL96 forward direction for the project finite-dimensional same-space
finite-Kraus semantics.

Correctability by an arbitrary CPTP `QuantumChannel` recovery implies the
same-space finite-Kraus Knill-Laflamme condition.  The proof first chooses a
finite Kraus representation of the recovery channel, transports the exact
correction equation through that representation, applies the KL96 branch-scalar
bridge, and then runs the explicit branch-scalar KL calculation.
-/
theorem sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (recovery : QuantumChannel H H)
    (h : FiniteKrausCorrectable ι H H C E recovery) :
    E.sameSpaceKnillLaflammeCriterion C := by
  classical
  rcases h with ⟨_hE_complete, hcorrected⟩
  rcases QuantumChannel.exists_finiteKrausFamily_representation recovery with
    ⟨m, R, hR_complete, hR_map⟩
  have hcorrect_finite : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : Fin m, (R.operator r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R.operator r)))) =
        rho.toOperator := by
    intro rho hρ
    calc
      (∑ r : Fin m, (R.operator r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R.operator r))))
          = R.inducedMap (E.inducedMap rho.toOperator) := by
            exact (FiniteKrausFamily.inducedMap_apply R
              (E.inducedMap rho.toOperator)).symm
      _ = recovery.toLinearMap (E.inducedMap rho.toOperator) := by
            rw [hR_map]
      _ = rho.toOperator := hcorrected rho hρ
  rcases exists_recovery_branch_scalar_of_finiteKraus_correctedBy
      E C R.operator hR_complete hcorrect_finite with
    ⟨branchScalar, hbranch⟩
  exact sameSpaceKnillLaflammeCriterion_of_recovery_branch_scalar
    E C R.operator hR_complete branchScalar hbranch

section IndexUnitaryMix

variable [DecidableEq ι]

/-- Mix a finite Kraus family by a matrix on its index space. -/
noncomputable def indexMix
    (E : FiniteKrausFamily ι H H) (U : Matrix ι ι Complex) :
    FiniteKrausFamily ι H H where
  operator a := ∑ i : ι, U i a • E.operator i

omit [DecidableEq ι] in
theorem indexMix_operator (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    (E.indexMix U).operator a = ∑ i : ι, U i a • E.operator i :=
  rfl

omit [DecidableEq ι] in
theorem indexMix_operator_adjoint (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    LinearMap.adjoint ((E.indexMix U).operator a) =
      ∑ i : ι, star (U i a) • LinearMap.adjoint (E.operator i) := by
  simp [indexMix, map_sum, map_smulₛₗ]

/-- Mix a finite Kraus family by a unitary matrix on its index space. -/
noncomputable def indexUnitaryMix
    (E : FiniteKrausFamily ι H H) (U : Matrix.unitaryGroup ι Complex) :
    FiniteKrausFamily ι H H :=
  E.indexMix (U : Matrix ι ι Complex)

theorem unitaryGroup_sum_star_col_mul_col
    (U : Matrix.unitaryGroup ι Complex) (i j : ι) :
    (∑ a : ι,
      star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) =
      if i = j then 1 else 0 := by
  classical
  have h := congrArg (fun M : Matrix ι ι Complex => M j i)
    (Unitary.coe_mul_star_self U)
  have hsum :
      (∑ a : ι,
        (U : Matrix ι ι Complex) j a *
          star ((U : Matrix ι ι Complex) i a)) =
        if j = i then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    (∑ a : ι,
      star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a)
        = ∑ a : ι,
            (U : Matrix ι ι Complex) j a *
              star ((U : Matrix ι ι Complex) i a) := by
              apply Finset.sum_congr rfl
              intro a _ha
              ring
    _ = if j = i then 1 else 0 := hsum
    _ = if i = j then 1 else 0 := by
      by_cases hij : i = j <;> simp [hij, eq_comm]

theorem unitaryGroup_sum_col_mul_star_col
    (U : Matrix.unitaryGroup ι Complex) (i j : ι) :
    (∑ a : ι,
      (U : Matrix ι ι Complex) i a *
        star ((U : Matrix ι ι Complex) j a)) =
      if i = j then 1 else 0 := by
  classical
  have h := congrArg (fun M : Matrix ι ι Complex => M i j)
    (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem unitaryGroup_sum_star_col_mul_col_smul
    {M : Type*} [AddCommMonoid M] [Module Complex M]
    (U : Matrix.unitaryGroup ι Complex) (B : ι → ι → M) :
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      (star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) • B i j) =
      ∑ i : ι, B i i := by
  classical
  calc
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      (star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) • B i j)
        = ∑ i : ι, ∑ a : ι, ∑ j : ι,
            (star ((U : Matrix ι ι Complex) i a) *
              (U : Matrix ι ι Complex) j a) • B i j := by
              rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι, ∑ a : ι,
            (star ((U : Matrix ι ι Complex) i a) *
              (U : Matrix ι ι Complex) j a) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι,
            (∑ a : ι,
              star ((U : Matrix ι ι Complex) i a) *
                (U : Matrix ι ι Complex) j a) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Finset.sum_smul]
    _ = ∑ i : ι, ∑ j : ι, (if i = j then 1 else 0 : Complex) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [unitaryGroup_sum_star_col_mul_col]
    _ = ∑ i : ι, B i i := by
              simp

theorem unitaryGroup_sum_col_mul_star_col_smul
    {M : Type*} [AddCommMonoid M] [Module Complex M]
    (U : Matrix.unitaryGroup ι Complex) (B : ι → ι → M) :
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      ((U : Matrix ι ι Complex) i a *
        star ((U : Matrix ι ι Complex) j a)) • B i j) =
      ∑ i : ι, B i i := by
  classical
  calc
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      ((U : Matrix ι ι Complex) i a *
        star ((U : Matrix ι ι Complex) j a)) • B i j)
        = ∑ i : ι, ∑ a : ι, ∑ j : ι,
            ((U : Matrix ι ι Complex) i a *
              star ((U : Matrix ι ι Complex) j a)) • B i j := by
              rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι, ∑ a : ι,
            ((U : Matrix ι ι Complex) i a *
              star ((U : Matrix ι ι Complex) j a)) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι,
            (∑ a : ι,
              (U : Matrix ι ι Complex) i a *
                star ((U : Matrix ι ι Complex) j a)) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Finset.sum_smul]
    _ = ∑ i : ι, ∑ j : ι, (if i = j then 1 else 0 : Complex) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [unitaryGroup_sum_col_mul_star_col]
    _ = ∑ i : ι, B i i := by
              simp

theorem indexUnitaryMix_complete (E : FiniteKrausFamily ι H H)
    (U : Matrix.unitaryGroup ι Complex) (hE : E.Complete) :
    (E.indexUnitaryMix U).Complete := by
  classical
  unfold Complete indexUnitaryMix
  rw [← hE]
  ext x
  calc
    (∑ a : ι,
      (LinearMap.adjoint ((E.indexMix (U : Matrix ι ι Complex)).operator a)).comp
        ((E.indexMix (U : Matrix ι ι Complex)).operator a)) x
        = ∑ a : ι, ∑ i : ι, ∑ j : ι,
            (star ((U : Matrix ι ι Complex) i a) *
              (U : Matrix ι ι Complex) j a) •
              (LinearMap.adjoint (E.operator i) (E.operator j x)) := by
              simp [indexMix, map_sum, map_smulₛₗ, Finset.sum_apply,
                Finset.smul_sum, smul_smul]
    _ = ∑ i : ι, LinearMap.adjoint (E.operator i) (E.operator i x) := by
              simpa using
                (unitaryGroup_sum_star_col_mul_col_smul U
                  (fun i j => LinearMap.adjoint (E.operator i) (E.operator j x)))
    _ = (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i)) x := by
              simp [Finset.sum_apply]

theorem indexUnitaryMix_inducedMap_eq (E : FiniteKrausFamily ι H H)
    (U : Matrix.unitaryGroup ι Complex) (A : Operator H) :
    (E.indexUnitaryMix U).inducedMap A = E.inducedMap A := by
  classical
  ext x
  calc
    ((E.indexUnitaryMix U).inducedMap A) x
        = ∑ a : ι, ∑ i : ι, ∑ j : ι,
            ((U : Matrix ι ι Complex) i a *
              star ((U : Matrix ι ι Complex) j a)) •
              (E.operator i (A (LinearMap.adjoint (E.operator j) x))) := by
              simp [indexUnitaryMix, indexMix, inducedMap_apply, map_sum, map_smulₛₗ,
                Finset.sum_apply, Finset.smul_sum, smul_smul]
    _ = ∑ i : ι, E.operator i (A (LinearMap.adjoint (E.operator i) x)) := by
              simpa using
                (unitaryGroup_sum_col_mul_star_col_smul U
                  (fun i j => E.operator i (A (LinearMap.adjoint (E.operator j) x))))
    _ = (E.inducedMap A) x := by
              simp [inducedMap_apply, Finset.sum_apply]

theorem indexUnitaryMix_indexedProjectorConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (U : Matrix.unitaryGroup ι Complex)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    IndexedKnillLaflammeProjectorConditionWithScalar (E.indexUnitaryMix U) C
      (fun a b : ι =>
        ((star (U : Matrix ι ι Complex)) * (Matrix.of fun i j => scalar i j) *
          (U : Matrix ι ι Complex)) a b) := by
  classical
  intro a b
  ext x
  calc
    (((C.projector.comp
      ((LinearMap.adjoint ((E.indexUnitaryMix U).operator a)).comp
        ((E.indexUnitaryMix U).operator b))).comp C.projector) x)
        = (∑ j : ι, ∑ i : ι,
            ((U : Matrix ι ι Complex) j b *
              star ((U : Matrix ι ι Complex) i a)) •
              (((C.projector.comp
                ((LinearMap.adjoint (E.operator i)).comp (E.operator j))).comp
                  C.projector) x)) := by
              simp [indexUnitaryMix, indexMix, map_sum, map_smulₛₗ,
                LinearMap.comp_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
    _ = (∑ j : ι, ∑ i : ι,
            ((U : Matrix ι ι Complex) j b *
              star ((U : Matrix ι ι Complex) i a)) •
              ((scalar i j • C.projector) x)) := by
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro i _hi
              rw [hKL i j]
    _ = (((∑ j : ι, ∑ i : ι,
            scalar i j * ((U : Matrix ι ι Complex) j b *
              star ((U : Matrix ι ι Complex) i a))) • C.projector) x) := by
              simp [Finset.sum_smul, smul_smul, mul_comm]
    _ = ((((star (U : Matrix ι ι Complex)) * (Matrix.of fun i j => scalar i j) *
          (U : Matrix ι ι Complex)) a b) • C.projector) x := by
              have hmatrix :
                  (((star (U : Matrix ι ι Complex)) *
                    (Matrix.of fun i j => scalar i j) *
                    (U : Matrix ι ι Complex)) a b) =
                    ∑ j : ι, ∑ i : ι,
                      scalar i j * ((U : Matrix ι ι Complex) j b *
                        star ((U : Matrix ι ι Complex) i a)) := by
                calc
                  (((star (U : Matrix ι ι Complex)) *
                    (Matrix.of fun i j => scalar i j) *
                    (U : Matrix ι ι Complex)) a b)
                      = ∑ j : ι,
                          (∑ i : ι,
                            star ((U : Matrix ι ι Complex) i a) * scalar i j) *
                            (U : Matrix ι ι Complex) j b := by
                            simp [Matrix.mul_apply]
                  _ = ∑ j : ι, ∑ i : ι,
                      (star ((U : Matrix ι ι Complex) i a) * scalar i j) *
                        (U : Matrix ι ι Complex) j b := by
                        apply Finset.sum_congr rfl
                        intro j _hj
                        rw [Finset.sum_mul]
                  _ = ∑ j : ι, ∑ i : ι,
                      scalar i j * ((U : Matrix ι ι Complex) j b *
                        star ((U : Matrix ι ι Complex) i a)) := by
                        apply Finset.sum_congr rfl
                        intro j _hj
                        apply Finset.sum_congr rfl
                        intro i _hi
                        ring
              rw [hmatrix]

theorem indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hPSD : (Matrix.of fun i j => scalar i j).PosSemidef)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    ∃ U : Matrix.unitaryGroup ι Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar (E.indexUnitaryMix U) C
        (fun a b : ι =>
          Matrix.diagonal (fun i : ι =>
            (hPSD.1.eigenvalues i : Complex)) a b) ∧
      ∀ i : ι, 0 ≤ hPSD.1.eigenvalues i := by
  classical
  let A : Matrix ι ι Complex := Matrix.of fun i j => scalar i j
  let U : Matrix.unitaryGroup ι Complex := hPSD.1.eigenvectorUnitary
  refine ⟨U, ?_, Matrix.PosSemidef.eigenvalues_nonneg hPSD⟩
  have hmix := indexUnitaryMix_indexedProjectorConditionWithScalar
    (E := E) (C := C) (scalar := scalar) U hKL
  have hdiag :
      (star (U : Matrix ι ι Complex)) * A * (U : Matrix ι ι Complex) =
        Matrix.diagonal (fun i : ι => (hPSD.1.eigenvalues i : Complex)) := by
    have hspectral := hPSD.1.conjStarAlgAut_star_eigenvectorUnitary
    simpa [A, U, Unitary.conjStarAlgAut_apply, Function.comp_def] using hspectral
  intro a b
  simpa [A, hdiag] using hmix a b

end IndexUnitaryMix

section DiagonalRecovery

variable [DecidableEq ι]

theorem diagonalProjectorConditionWithScalar_apply
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (i j : ι) :
    (C.projector.comp ((LinearMap.adjoint (F.operator i)).comp (F.operator j))).comp
        C.projector =
      (if i = j then (lambda i : Complex) else 0) • C.projector := by
  simpa [Matrix.diagonal_apply] using hKL i j

theorem diagonalRecovery_left_branch
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a : {i : ι // lambda i ≠ 0}) (i : ι) :
    (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
        C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
        ((F.operator i).comp C.projector)) : Operator H) =
      if a.1 = i then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by
  classical
  have hbranch := diagonalProjectorConditionWithScalar_apply hKL a.1 i
  have hsqrt_mul :
      ((Real.sqrt (lambda a.1) : Complex)⁻¹ * (lambda a.1 : Complex)) =
        (Real.sqrt (lambda a.1) : Complex) := by
    have hpos : 0 < lambda a.1 := lt_of_le_of_ne (hlambda_nonneg a.1) (Ne.symm a.2)
    have hsqrt_ne : (Real.sqrt (lambda a.1) : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hpos))
    have hsquare :
        (Real.sqrt (lambda a.1) : Complex) * (Real.sqrt (lambda a.1) : Complex) =
          (lambda a.1 : Complex) := by
      have hsquareR : Real.sqrt (lambda a.1) * Real.sqrt (lambda a.1) = lambda a.1 := by
        simpa [sq] using Real.sq_sqrt (hlambda_nonneg a.1)
      exact_mod_cast hsquareR
    rw [← hsquare]
    exact inv_mul_cancel_left₀ hsqrt_ne _
  by_cases hai : a.1 = i
  · subst i
    calc
      (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
          C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
          ((F.operator a.1).comp C.projector)) : Operator H)
          = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
              ((C.projector.comp
                ((LinearMap.adjoint (F.operator a.1)).comp (F.operator a.1))).comp
                  C.projector) := by
                ext x
                simp [LinearMap.comp_apply]
      _ = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
            ((lambda a.1 : Complex) • C.projector) := by
            rw [hbranch]
            simp
      _ = (Real.sqrt (lambda a.1) : Complex) • C.projector := by
            rw [smul_smul, hsqrt_mul]
      _ = if a.1 = a.1 then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by
            simp
  · calc
      (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
          C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
          ((F.operator i).comp C.projector)) : Operator H)
          = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
              ((C.projector.comp
                ((LinearMap.adjoint (F.operator a.1)).comp (F.operator i))).comp
                  C.projector) := by
                ext x
                simp [LinearMap.comp_apply]
      _ = ((Real.sqrt (lambda a.1) : Complex)⁻¹) •
            ((0 : Complex) • C.projector) := by
            rw [hbranch]
            simp [hai]
      _ = 0 := by
            simp
      _ = if a.1 = i then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by
            simp [hai]

theorem diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    {i : ι} (hzero : lambda i = 0) :
    (F.operator i).comp C.projector = 0 := by
  let A : Operator H := (F.operator i).comp C.projector
  have hAdjComp : (LinearMap.adjoint A).comp A = 0 := by
    have hii := diagonalProjectorConditionWithScalar_apply hKL i i
    calc
      (LinearMap.adjoint A).comp A
          = (C.projector.comp
              ((LinearMap.adjoint (F.operator i)).comp (F.operator i))).comp
                C.projector := by
                ext x
                simp [A, LinearMap.adjoint_comp, C.projector_adjoint_eq_self,
                  LinearMap.comp_apply]
      _ = ((lambda i : Complex) • C.projector) := by
            simpa using hii
      _ = 0 := by
            simp [hzero]
  ext x
  have hxker : x ∈ LinearMap.ker ((LinearMap.adjoint A).comp A) := by
    simp [hAdjComp]
  have hxkerA : x ∈ LinearMap.ker A := by
    simpa [LinearMap.ker_adjoint_comp_self] using hxker
  simpa [A] using hxkerA

noncomputable def diagonalRecoveryOperator
    (C : QuantumCode H) (F : FiniteKrausFamily ι H H) (lambda : ι → ℝ)
    (i : ι) : Operator H :=
  if lambda i = 0 then 0
  else ((Real.sqrt (lambda i) : Complex)⁻¹) •
    C.projector.comp (LinearMap.adjoint (F.operator i))

theorem diagonalRecoveryOperator_branch
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a i : ι) :
    ((diagonalRecoveryOperator C F lambda a).comp
        ((F.operator i).comp C.projector) : Operator H) =
      if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0 := by
  classical
  by_cases hzero : lambda a = 0
  · by_cases hai : a = i
    · subst i
      simp [diagonalRecoveryOperator, hzero]
    · simp [diagonalRecoveryOperator, hzero, hai]
  · let aa : {i : ι // lambda i ≠ 0} := ⟨a, hzero⟩
    have hsub := diagonalRecovery_left_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL aa i
    simpa [diagonalRecoveryOperator, hzero, aa] using hsub

theorem diagonalRecoveryOperator_branch_adjoint
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a i : ι) :
    (C.projector.comp (LinearMap.adjoint (F.operator i))).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)) =
      if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0 := by
  classical
  have h := congrArg LinearMap.adjoint
    (diagonalRecoveryOperator_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a i)
  by_cases hai : a = i
  · subst a
    have hR :
        LinearMap.adjoint
            (if i = i then (Real.sqrt (lambda i) : Complex) • C.projector else 0) =
          (Real.sqrt (lambda i) : Complex) • C.projector := by
      calc
        LinearMap.adjoint
            (if i = i then (Real.sqrt (lambda i) : Complex) • C.projector else 0)
            = LinearMap.adjoint ((Real.sqrt (lambda i) : Complex) • C.projector) := by
              simp
        _ = star (Real.sqrt (lambda i) : Complex) • LinearMap.adjoint C.projector := by
              exact map_smulₛₗ
                (LinearMap.adjoint : (Operator H) ≃ₗ⋆[Complex] Operator H)
                (Real.sqrt (lambda i) : Complex) C.projector
        _ = (Real.sqrt (lambda i) : Complex) • C.projector := by
              simp [C.projector_adjoint_eq_self]
    simpa [LinearMap.adjoint_comp, C.projector_adjoint_eq_self] using h.trans hR
  · have hR :
        LinearMap.adjoint
            (if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0) =
          0 := by
      simp [hai]
    simpa [hai, LinearMap.adjoint_comp, C.projector_adjoint_eq_self] using h.trans hR

theorem diagonalRecoveryOperator_density_branch
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho)
    (a i : ι) :
    (diagonalRecoveryOperator C F lambda a).comp
        ((F.operator i).comp
          (rho.toOperator.comp
            ((LinearMap.adjoint (F.operator i)).comp
              (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))) =
      if a = i then (lambda i : Complex) • rho.toOperator else 0 := by
  classical
  let R := diagonalRecoveryOperator C F lambda a
  have hleft := diagonalRecoveryOperator_branch
    (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a i
  have hright := diagonalRecoveryOperator_branch_adjoint
    (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a i
  have hPρ := DensityOperator.supportedOn_projector_comp_eq_self C rho hρ
  have hρP := DensityOperator.supportedOn_comp_projector_eq_self C rho hρ
  have hPρ_apply : ∀ x : H, C.projector (rho.toOperator x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hPρ
  have hρP_apply : ∀ x : H, rho.toOperator (C.projector x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hρP
  have hinsert :
      R.comp
          ((F.operator i).comp
            (rho.toOperator.comp
              ((LinearMap.adjoint (F.operator i)).comp
                (LinearMap.adjoint R)))) =
        (R.comp ((F.operator i).comp C.projector)).comp
          (rho.toOperator.comp
            ((C.projector.comp (LinearMap.adjoint (F.operator i))).comp
              (LinearMap.adjoint R))) := by
    ext x
    simp [R, LinearMap.comp_apply, hPρ_apply, hρP_apply]
  by_cases hai : a = i
  · subst a
    have hsquareR : Real.sqrt (lambda i) * Real.sqrt (lambda i) = lambda i := by
      simpa [sq] using Real.sq_sqrt (hlambda_nonneg i)
    rw [hinsert]
    rw [hleft, hright]
    ext x
    simp [LinearMap.comp_apply, hPρ_apply, hρP_apply, smul_smul]
    exact congrArg (fun r : ℝ => (r : Complex) • rho.toOperator x) hsquareR
  · rw [hinsert]
    rw [hleft, hright]
    simp [hai]

omit [DecidableEq ι] in
theorem diagonalRecoveryOperator_projector_comp
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H) (lambda : ι → ℝ)
    (a : ι) :
    C.projector.comp (diagonalRecoveryOperator C F lambda a) =
      diagonalRecoveryOperator C F lambda a := by
  classical
  unfold diagonalRecoveryOperator
  split
  · ext x
    simp
  · ext x
    simp [LinearMap.comp_apply]
    have hPP := congrArg
      (fun A : Operator H => A ((LinearMap.adjoint (F.operator a)) x))
      C.projector_idempotent
    simpa [LinearMap.comp_apply] using
      congrArg (fun y : H => ((Real.sqrt (lambda a) : Complex)⁻¹) • y) hPP

omit [DecidableEq ι] in
theorem diagonalRecoveryOperator_adjoint_of_ne_zero
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    {a : ι} (ha : lambda a ≠ 0) :
    LinearMap.adjoint (diagonalRecoveryOperator C F lambda a) =
      ((Real.sqrt (lambda a) : Complex)⁻¹) •
        (F.operator a).comp C.projector := by
  classical
  unfold diagonalRecoveryOperator
  rw [if_neg ha]
  let c : Complex := (Real.sqrt (lambda a) : Complex)⁻¹
  have hAdjS :
      LinearMap.adjoint (c • C.projector.comp (LinearMap.adjoint (F.operator a))) =
        star c • LinearMap.adjoint (C.projector.comp (LinearMap.adjoint (F.operator a))) :=
    map_smulₛₗ
      (LinearMap.adjoint : (Operator H) ≃ₗ⋆[Complex] Operator H)
      c (C.projector.comp (LinearMap.adjoint (F.operator a)))
  have hc : star c = c := by
    simp [c]
  calc
    LinearMap.adjoint (c • C.projector.comp (LinearMap.adjoint (F.operator a)))
        = star c • LinearMap.adjoint (C.projector.comp (LinearMap.adjoint (F.operator a))) :=
          hAdjS
    _ = c • (F.operator a).comp C.projector := by
          simp [hc, LinearMap.adjoint_comp, C.projector_adjoint_eq_self, c]

theorem diagonalRecoveryOperator_cross
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a b : ι) :
    (diagonalRecoveryOperator C F lambda a).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda b)) =
      if a = b then
        if lambda a = 0 then 0 else C.projector
      else 0 := by
  classical
  by_cases hb : lambda b = 0
  · unfold diagonalRecoveryOperator
    rw [if_pos hb]
    by_cases hab : a = b
    · subst a
      simp [hb]
    · simp [hab]
  · have hbpos : 0 < lambda b := lt_of_le_of_ne (hlambda_nonneg b) (Ne.symm hb)
    have hsqrt_pos_R : 0 < Real.sqrt (lambda b) := Real.sqrt_pos.2 hbpos
    have hsqrt_ne_R : Real.sqrt (lambda b) ≠ 0 :=
      ne_of_gt hsqrt_pos_R
    have hsqrt_ne_C : (Real.sqrt (lambda b) : Complex) ≠ 0 := by
      exact_mod_cast hsqrt_ne_R
    have hAdj := diagonalRecoveryOperator_adjoint_of_ne_zero
      (F := F) (C := C) (lambda := lambda) (a := b) hb
    have hbranch := diagonalRecoveryOperator_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a b
    rw [hAdj]
    calc
      (diagonalRecoveryOperator C F lambda a).comp
          (((Real.sqrt (lambda b) : Complex)⁻¹) •
            (F.operator b).comp C.projector)
          = ((Real.sqrt (lambda b) : Complex)⁻¹) •
              ((diagonalRecoveryOperator C F lambda a).comp
                ((F.operator b).comp C.projector)) := by
              ext x
              simp [LinearMap.comp_apply]
      _ = ((Real.sqrt (lambda b) : Complex)⁻¹) •
            (if a = b then (Real.sqrt (lambda a) : Complex) • C.projector else 0) := by
              rw [hbranch]
      _ = if a = b then
            if lambda a = 0 then 0 else C.projector
          else 0 := by
              by_cases hab : a = b
              · subst a
                simp [hb]
                ext x
                change ((Real.sqrt (lambda b) : Complex)⁻¹) •
                    ((Real.sqrt (lambda b) : Complex) • C.projector x) =
                  C.projector x
                rw [smul_smul, inv_mul_cancel₀ hsqrt_ne_C]
                simp
              · simp [hab]

theorem diagonalRecoveryProjectionTerm_mul
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a b : ι) :
    (((LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
      ((LinearMap.adjoint (diagonalRecoveryOperator C F lambda b)).comp
        (diagonalRecoveryOperator C F lambda b))) =
      if a = b then
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)
      else 0 := by
  classical
  let Ra := diagonalRecoveryOperator C F lambda a
  let Rb := diagonalRecoveryOperator C F lambda b
  have hcross := diagonalRecoveryOperator_cross
    (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a b
  by_cases hab : a = b
  · subst b
    by_cases ha0 : lambda a = 0
    · unfold diagonalRecoveryOperator
      rw [if_pos ha0]
      simp
    · have hcross_aa :
          Ra.comp (LinearMap.adjoint Ra) = C.projector := by
        simpa [Ra, ha0] using hcross
      have hP := diagonalRecoveryOperator_projector_comp F C lambda a
      rw [if_pos rfl]
      ext x
      calc
        (((LinearMap.adjoint Ra).comp Ra).comp
          ((LinearMap.adjoint Ra).comp Ra)) x
            = (LinearMap.adjoint Ra)
                ((Ra.comp (LinearMap.adjoint Ra)) (Ra x)) := by
                simp [LinearMap.comp_apply]
        _ = (LinearMap.adjoint Ra) (C.projector (Ra x)) := by
                rw [hcross_aa]
        _ = (LinearMap.adjoint Ra) (Ra x) := by
                have hPx := congrArg (fun A : Operator H => A x) hP
                simpa [Ra, LinearMap.comp_apply] using
                  congrArg (fun y : H => (LinearMap.adjoint Ra) y) hPx
        _ = ((LinearMap.adjoint Ra).comp Ra) x := by
                simp [LinearMap.comp_apply]
  · have hcross_ab :
        Ra.comp (LinearMap.adjoint Rb) = 0 := by
      simpa [Ra, Rb, hab] using hcross
    rw [if_neg hab]
    ext x
    calc
      (((LinearMap.adjoint Ra).comp Ra).comp
        ((LinearMap.adjoint Rb).comp Rb)) x
          = (LinearMap.adjoint Ra)
              ((Ra.comp (LinearMap.adjoint Rb)) (Rb x)) := by
              simp [LinearMap.comp_apply]
      _ = 0 := by
              rw [hcross_ab]
              simp

omit [DecidableEq ι] in
theorem diagonalRecoveryProjectionTerm_adjoint
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H) (lambda : ι → ℝ)
    (a : ι) :
    LinearMap.adjoint
        ((LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)) =
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a) := by
  simp [LinearMap.adjoint_comp]

omit [DecidableEq ι] in
theorem diagonalRecoveryProjectionSum_adjoint
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H) (lambda : ι → ℝ) :
    LinearMap.adjoint
        (∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)) =
      ∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  exact diagonalRecoveryProjectionTerm_adjoint F C lambda a

theorem diagonalRecoveryProjectionSum_idempotent
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j)) :
    (∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
      (∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)) =
    ∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a) := by
  classical
  let T : ι → Operator H := fun a =>
    (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
      (diagonalRecoveryOperator C F lambda a)
  calc
    (∑ a : ι, T a).comp (∑ b : ι, T b)
        = ∑ a : ι, ∑ b : ι, (T b).comp (T a) := by
            ext x
            simp [T, Finset.sum_apply, LinearMap.comp_apply]
    _ = ∑ a : ι, ∑ b : ι, if b = a then T b else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro b _hb
            rw [diagonalRecoveryProjectionTerm_mul
              (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL b a]
    _ = ∑ a : ι, T a := by
            ext x
            simp [T]

theorem diagonalRecoveryOperator_branches
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (hdiag_sum : (∑ i : ι, (lambda i : Complex)) • C.projector = C.projector)
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho) :
    (∑ a : ι, (diagonalRecoveryOperator C F lambda a).comp
      ((F.inducedMap rho.toOperator).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)))) =
      rho.toOperator := by
  classical
  have hPρ := DensityOperator.supportedOn_projector_comp_eq_self C rho hρ
  have hPρ_apply : ∀ x : H, C.projector (rho.toOperator x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hPρ
  have hweight_rho :
      (∑ i : ι, (lambda i : Complex)) • rho.toOperator = rho.toOperator := by
    ext x
    have hx := congrArg (fun A : Operator H => A (rho.toOperator x)) hdiag_sum
    simpa [hPρ_apply x] using hx
  calc
    (∑ a : ι, (diagonalRecoveryOperator C F lambda a).comp
      ((F.inducedMap rho.toOperator).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))
        = ∑ a : ι, ∑ i : ι,
            (diagonalRecoveryOperator C F lambda a).comp
              ((F.operator i).comp
                (rho.toOperator.comp
                  ((LinearMap.adjoint (F.operator i)).comp
                    (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))) := by
            ext x
            simp [FiniteKrausFamily.inducedMap_apply, Finset.sum_apply]
    _ = ∑ a : ι, ∑ i : ι,
          if a = i then (lambda i : Complex) • rho.toOperator else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro i _hi
            exact diagonalRecoveryOperator_density_branch
              (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL rho hρ a i
    _ = ∑ i : ι, (lambda i : Complex) • rho.toOperator := by
            ext x
            simp
    _ = rho.toOperator := by
            rw [← Finset.sum_smul]
            exact hweight_rho

theorem diagonalRecoveryProjectionSum_error_projector
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (i : ι) :
    (∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
        ((F.operator i).comp C.projector) =
      (F.operator i).comp C.projector := by
  classical
  let R : ι → Operator H := fun a => diagonalRecoveryOperator C F lambda a
  let T : ι → Operator H := fun a => (LinearMap.adjoint (R a)).comp (R a)
  by_cases hi0 : lambda i = 0
  · have hzero := diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
      (F := F) (C := C) (lambda := lambda) hKL hi0
    rw [hzero]
    ext x
    simp
  · have hipos : 0 < lambda i := lt_of_le_of_ne (hlambda_nonneg i) (Ne.symm hi0)
    have hsqrt_pos_R : 0 < Real.sqrt (lambda i) := Real.sqrt_pos.2 hipos
    have hsqrt_ne_R : Real.sqrt (lambda i) ≠ 0 := ne_of_gt hsqrt_pos_R
    have hsqrt_ne_C : (Real.sqrt (lambda i) : Complex) ≠ 0 := by
      exact_mod_cast hsqrt_ne_R
    have hadj := diagonalRecoveryOperator_adjoint_of_ne_zero
      (F := F) (C := C) (lambda := lambda) (a := i) hi0
    have hbranch := diagonalRecoveryOperator_branch
      (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL
    calc
      (∑ a : ι, T a).comp ((F.operator i).comp C.projector)
          = ∑ a : ι, (LinearMap.adjoint (R a)).comp
              ((R a).comp ((F.operator i).comp C.projector)) := by
              ext x
              simp [T, R, Finset.sum_apply, LinearMap.comp_apply]
      _ = ∑ a : ι, (LinearMap.adjoint (R a)).comp
              (if a = i then (Real.sqrt (lambda a) : Complex) • C.projector else 0) := by
              apply Finset.sum_congr rfl
              intro a _ha
              rw [hbranch a i]
      _ = (LinearMap.adjoint (R i)).comp
              ((Real.sqrt (lambda i) : Complex) • C.projector) := by
              simpa using
                (Finset.sum_eq_single (s := Finset.univ)
                  (f := fun a : ι =>
                    (LinearMap.adjoint (R a)).comp
                      (if a = i then
                        (Real.sqrt (lambda a) : Complex) • C.projector
                      else 0))
                  i
                  (by
                    intro b _hb hbi
                    simp [hbi])
                  (by
                    intro hi
                    simp at hi))
      _ = (F.operator i).comp C.projector := by
              change (LinearMap.adjoint (diagonalRecoveryOperator C F lambda i)).comp
                  ((Real.sqrt (lambda i) : Complex) • C.projector) =
                (F.operator i).comp C.projector
              rw [hadj]
              ext x
              have hscalar :
                  ((Real.sqrt (lambda i) : Complex)⁻¹) *
                      (Real.sqrt (lambda i) : Complex) = 1 :=
                inv_mul_cancel₀ hsqrt_ne_C
              have hP := congrArg (fun A : Operator H => A x) C.projector_idempotent
              simp [LinearMap.comp_apply]
              rw [show C.projector (C.projector x) = C.projector x by
                simpa [LinearMap.comp_apply] using hP]
              change ((Real.sqrt (lambda i) : Complex)⁻¹) •
                  ((Real.sqrt (lambda i) : Complex) •
                    (F.operator i) (C.projector x)) =
                (F.operator i) (C.projector x)
              rw [smul_smul, hscalar]
              simp

theorem diagonalRecoveryProjectionSum_residual
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho) :
    let S : Operator H :=
      ∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)
    (1 - S).comp
      ((F.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) = 0 := by
  classical
  intro S
  have hS_adjoint :
      LinearMap.adjoint S = S := by
    exact diagonalRecoveryProjectionSum_adjoint F C lambda
  have hResidualAdjoint : LinearMap.adjoint (1 - S : Operator H) = 1 - S := by
    rw [map_sub, LinearMap.adjoint_one, hS_adjoint]
  have hPρ := DensityOperator.supportedOn_projector_comp_eq_self C rho hρ
  have hPρ_apply : ∀ x : H, C.projector (rho.toOperator x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hPρ
  have hleft_kill :
      (1 - S).comp (F.inducedMap rho.toOperator) = 0 := by
    calc
      (1 - S).comp (F.inducedMap rho.toOperator)
          = ∑ i : ι, (1 - S).comp
              (((F.operator i).comp C.projector).comp
                (rho.toOperator.comp (LinearMap.adjoint (F.operator i)))) := by
              ext x
              simp [FiniteKrausFamily.inducedMap_apply, Finset.sum_apply,
                LinearMap.comp_apply, S, hPρ_apply]
      _ = 0 := by
              apply Finset.sum_eq_zero
              intro i _hi
              let B : Operator H := rho.toOperator.comp (LinearMap.adjoint (F.operator i))
              have hSi := diagonalRecoveryProjectionSum_error_projector
                (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL i
              have hkill :
                  (1 - S).comp ((F.operator i).comp C.projector) = 0 := by
                change (1 -
                    (∑ a : ι,
                      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
                        (diagonalRecoveryOperator C F lambda a))).comp
                    ((F.operator i).comp C.projector) = 0
                ext y
                have hy := congrArg (fun A : Operator H => A y) hSi
                simp [LinearMap.comp_apply] at hy ⊢
                exact sub_eq_zero.mpr hy.symm
              calc
                (1 - S).comp (((F.operator i).comp C.projector).comp B)
                    = ((1 - S).comp ((F.operator i).comp C.projector)).comp B := by
                    ext y
                    simp [B, LinearMap.comp_apply]
                _ = 0 := by
                    rw [hkill]
                    ext y
                    simp
  rw [hResidualAdjoint]
  ext x
  have hx := congrArg (fun A : Operator H => A ((1 - S) x)) hleft_kill
  simpa [LinearMap.comp_apply] using hx

end DiagonalRecovery

/--
Projection-sum recovery builder.

If a finite family of raw recovery Kraus operators has adjoint-square sum `S`,
`S` is an orthogonal projection, the finite recovery branches correct the
noise on code-supported density operators, and the residual branch `1 - S`
kills those same noisy states, then adding the residual branch packages the
data into a CPTP recovery channel.

This theorem is the final packaging/calculation layer below the full
Knill-Laflamme recovery construction.  It still requires separate mathematics
to produce the recovery Kraus operators from the KL scalar data.
-/
theorem exists_recovery_of_projectionSumRecoveryData
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (R : κ → KrausOperator H H)
    (S : Operator H)
    (hS_sum : S = ∑ a : κ, (LinearMap.adjoint (R a)).comp (R a))
    (hS_adjoint : LinearMap.adjoint S = S)
    (hS_idempotent : S.comp S = S)
    (hbranches : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ a : κ, (R a).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R a)))) =
          rho.toOperator)
    (hresidual : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (1 - S).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) = 0) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C E recovery := by
  classical
  let recoveryKraus : FiniteKrausFamily (Option κ) H H :=
    { operator := fun a =>
        match a with
        | none => 1 - S
        | some k => R k }
  have hResidualAdjoint : LinearMap.adjoint (1 - S : Operator H) = 1 - S := by
    rw [map_sub, LinearMap.adjoint_one, hS_adjoint]
  have hResidualSquare :
      (LinearMap.adjoint (1 - S : Operator H)).comp (1 - S) = 1 - S := by
    rw [hResidualAdjoint]
    ext x
    have hx := congrArg (fun A : Operator H => A x) hS_idempotent
    simp [LinearMap.comp_apply] at hx ⊢
    rw [hx]
    simp
  have hRecoveryComplete : recoveryKraus.Complete := by
    unfold FiniteKrausFamily.Complete
    dsimp [recoveryKraus]
    rw [Fintype.sum_option]
    rw [hResidualSquare]
    rw [← hS_sum]
    ext x
    simp [sub_eq_add_neg]
  refine ⟨recoveryKraus.toQuantumChannel hRecoveryComplete, hE, ?_⟩
  intro rho hρ
  change recoveryKraus.inducedMap (E.inducedMap rho.toOperator) = rho.toOperator
  rw [FiniteKrausFamily.inducedMap_apply]
  dsimp [recoveryKraus]
  rw [Fintype.sum_option]
  change (1 - S).comp
      ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) +
      (∑ a : κ, (R a).comp
        ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R a)))) =
      rho.toOperator
  rw [hresidual rho hρ]
  rw [hbranches rho hρ]
  simp

theorem exists_recovery_of_diagonalProjectorConditionWithScalar
    [DecidableEq ι]
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hF : F.Complete)
    {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j)) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C F recovery := by
  classical
  let R : ι → KrausOperator H H := fun a => diagonalRecoveryOperator C F lambda a
  let S : Operator H :=
    ∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)
  have hdiag_sum :
      (∑ i : ι, (lambda i : Complex)) • C.projector = C.projector :=
    by
      simpa [Matrix.diagonal_apply] using
        (indexedProjectorConditionWithScalar_complete_diagonal_sum hF hKL)
  exact exists_recovery_of_projectionSumRecoveryData
    (E := F) (C := C) hF R S
    (by rfl)
    (by
      change LinearMap.adjoint
          (∑ a : ι,
            (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
              (diagonalRecoveryOperator C F lambda a)) =
        ∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)
      exact diagonalRecoveryProjectionSum_adjoint F C lambda)
    (by
      change
        (∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)).comp
          (∑ a : ι,
            (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
              (diagonalRecoveryOperator C F lambda a)) =
        ∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)
      exact diagonalRecoveryProjectionSum_idempotent
        (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL)
    (by
      intro rho hρ
      exact diagonalRecoveryOperator_branches
        (F := F) (C := C) (lambda := lambda)
        hlambda_nonneg hKL hdiag_sum rho hρ)
    (by
      intro rho hρ
      exact diagonalRecoveryProjectionSum_residual
        (F := F) (C := C) (lambda := lambda)
        hlambda_nonneg hKL rho hρ)

theorem exists_recovery_of_sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C E recovery := by
  classical
  by_cases hCbot : C.carrier = ⊥
  · refine ⟨QuantumChannel.id H, hE, ?_⟩
    exact (E.correctedBy_iff_correctable_toQuantumChannel hE C (QuantumChannel.id H)).2
      (correctable_id_of_carrier_eq_bot E C hE hCbot)
  · rcases sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
      E C hE hCbot hKL with
      ⟨scalar, hscalarKL, hPSD, _hdiag, _hherm⟩
    rcases indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
      (E := E) (C := C) (scalar := scalar) hPSD hscalarKL with
      ⟨U, hdiagKL, hlambda_nonneg⟩
    let F : FiniteKrausFamily ι H H := E.indexUnitaryMix U
    let lambda : ι → ℝ := fun i => hPSD.1.eigenvalues i
    have hF : F.Complete := by
      simpa [F] using indexUnitaryMix_complete E U hE
    have hdiagKL' :
        IndexedKnillLaflammeProjectorConditionWithScalar F C
          (fun a b : ι =>
            Matrix.diagonal (fun i : ι => (lambda i : Complex)) a b) := by
      simpa [F, lambda] using hdiagKL
    have hlambda_nonneg' : ∀ i : ι, 0 ≤ lambda i := by
      simpa [lambda] using hlambda_nonneg
    rcases exists_recovery_of_diagonalProjectorConditionWithScalar
      F C hF (lambda := lambda) hlambda_nonneg' hdiagKL' with
      ⟨recovery, hrecF⟩
    refine ⟨recovery, hE, ?_⟩
    intro rho hρ
    have hcorrectF := hrecF.2 rho hρ
    have hmap := indexUnitaryMix_inducedMap_eq E U rho.toOperator
    simpa [F, hmap] using hcorrectF

/--
KL96 equivalence for the project finite-dimensional same-space finite-Kraus
semantics.

A complete finite Kraus family satisfies the Knill-Laflamme condition on a
quantum code iff there exists an arbitrary CPTP `QuantumChannel` recovery that
makes the code correctable for that family.
-/
theorem sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (hE : E.Complete) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      ∃ recovery : QuantumChannel H H, FiniteKrausCorrectable ι H H C E recovery := by
  constructor
  · intro hKL
    exact exists_recovery_of_sameSpaceKnillLaflammeCriterion E C hE hKL
  · rintro ⟨recovery, hcorrectable⟩
    exact sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable E C recovery hcorrectable

/--
The finite-dimensional same-space Knill-Laflamme criterion with both sides
expanded for public use.

For a complete finite Kraus family, the indexed matrix-element condition is
equivalent to existence of a CPTP recovery that reverses its operator-sum map
on every density operator supported on the code.
-/
theorem matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (hE : E.Complete) :
    (∃ scalar : ι → ι → Complex,
      ∀ i j : ι,
        ∀ x : H, x ∈ C.carrier →
          ∀ y : H, y ∈ C.carrier →
            inner Complex (E.operator i x) (E.operator j y) =
              scalar i j * inner Complex x y) ↔
      ∃ recovery : QuantumChannel H H,
        ∀ rho : DensityOperator H,
          DensityOperator.SupportedOn C rho →
            recovery (E.inducedMap rho.toOperator) = rho.toOperator := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    have hKL : E.sameSpaceKnillLaflammeCriterion C :=
      (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).2
        ⟨scalar, hscalar⟩
    rcases exists_recovery_of_sameSpaceKnillLaflammeCriterion E C hE hKL with
      ⟨recovery, _, hcorrected⟩
    exact ⟨recovery, hcorrected⟩
  · rintro ⟨recovery, hcorrected⟩
    have hKL : E.sameSpaceKnillLaflammeCriterion C :=
      sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
        E C recovery ⟨hE, hcorrected⟩
    exact (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).1 hKL

end FiniteKrausFamily

end

end Semantics
end QEC
