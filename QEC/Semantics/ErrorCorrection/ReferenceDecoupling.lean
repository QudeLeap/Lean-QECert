import QEC.Semantics.Entropy.Purification
import QEC.Semantics.Entropy.MatrixRelative
import QEC.Semantics.ErrorCorrection.QuditReplacement
import QEC.Semantics.ErrorCorrection.KLRecovery
import QEC.Semantics.ErrorCorrection.Detectability
/-!
# Finite heterogeneous erasure reference decoupling

This module keeps the recovery-to-reference step at the typed erasure
interface.  In particular, the finite branch calculation below has input
`H` and erased output `K`; it never converts the erasure into a same-space
Knill--Laflamme assertion.
-/

noncomputable section

namespace QEC
namespace Semantics

open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct

universe u v w

namespace DensityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

/-- An explicit finite-dimensional purification of a density operator. -/
structure FinitePurification (rho : DensityOperator H) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref] where
  vector : CompositeSystem H Ref
  normSq_one : ‖vector‖ ^ 2 = 1
  rightMarginal_eq : (rightMarginal (pureDensity vector normSq_one)).toOperator = rho.toOperator

end DensityOperator

/-!
The next two lemmas are deliberately stated with a potentially different
erasure output space `K`.  They are the density-state to branch/polarization
bridge used below; no same-space Knill--Laflamme criterion is involved.
-/
namespace FiniteKrausFamily

variable {H : Type u} {K : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [Fintype ι] [Fintype κ]

/--
For a heterogeneous finite Kraus noise family followed by finite recovery
branches, exact correction of every supported density forces every composite
branch to preserve the ray of each code vector.
-/
theorem recovery_branch_mem_span_of_heterogeneous_correctedBy
    (E : FiniteKrausFamily ι H K) (C : QuantumCode H)
    (R : κ → K →ₗ[Complex] H)
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
      _ = rho.toOperator := hcorrect rho
        (DensityOperator.pureOfNonzero_supportedOn hx0 hxC)
  have hmem_double : R r (E.operator i x) ∈ (Complex ∙ x)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hxy : inner Complex x y = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hy
    have hRhoY : rho.toOperator y = 0 := by
      simp [rho, hxy]
    have hquad : (∑ r : κ, ∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hyop := congrArg (fun A : Operator H => inner Complex (A y) y) hsum
      simpa [term, Finset.sum_apply, hRhoY] using hyop
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
    have houter_zero : (∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hfun : (fun r : κ => ∑ i : ι, inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro r
          exact Finset.sum_nonneg (by
            intro i _hi
            exact (hterm_pos r i).inner_nonneg_left y))).mp hquad
      exact congrFun hfun r
    have hinner_zero : inner Complex ((term r i) y) y = 0 := by
      have hfun : (fun i : ι => inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro i
          exact (hterm_pos r i).inner_nonneg_left y)).mp houter_zero
      exact congrFun hfun i
    let A : Operator H := (R r).comp (E.operator i)
    have hinner_rank :
        inner Complex
          (((((inner Complex x x)⁻¹ •
            (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
              H →ₗ[Complex] H))) : H →ₗ[Complex] H) y)) y = 0 := by
      have hterm_eq := DensityOperator.comp_pureOfNonzero_adjoint A x hx0
      rw [← hterm_eq]
      simpa [A, term, rho] using hinner_zero
    have hc_ne : (inner Complex x x)⁻¹ ≠ 0 := inv_ne_zero (inner_self_ne_zero.mpr hx0)
    have h' :
        (inner Complex x x)⁻¹ * (inner Complex (A x) y * inner Complex y (A x)) = 0 := by
      simpa [inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using hinner_rank
    have hprod : inner Complex (A x) y * inner Complex y (A x) = 0 := by
      exact (mul_eq_zero.mp h').resolve_left hc_ne
    have hAxy : inner Complex (A x) y = 0 := by
      rcases mul_eq_zero.mp hprod with hz | hy'
      · exact hz
      · exact inner_eq_zero_symm.mp hy'
    simpa [A, LinearMap.comp_apply] using hAxy
  rw [Submodule.orthogonal_orthogonal] at hmem_double
  exact hmem_double

/-- Exact correction polarizes to scalar overlap equations for a heterogeneous noise family. -/
theorem exists_heterogeneous_matrix_element_scalars_of_correctedBy
    (E : FiniteKrausFamily ι H K) (C : QuantumCode H)
    (R : κ → K →ₗ[Complex] H)
    (hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
          rho.toOperator) :
    ∃ scalar : ι → ι → Complex,
      ∀ i j (x : H), x ∈ C.carrier → ∀ y : H, y ∈ C.carrier →
        inner Complex (E.operator i x) (E.operator j y) =
          scalar i j * inner Complex x y := by
  classical
  have hscalar : ∀ r i : _, ∃ a : Complex,
      ∀ x : H, x ∈ C.carrier → R r (E.operator i x) = a • x := by
    intro r i
    exact operator_scalar_on_code_of_forall_mem_span ((R r).comp (E.operator i)) C
      (fun x hx => recovery_branch_mem_span_of_heterogeneous_correctedBy
        E C R hcorrect r i hx)
  choose a ha using hscalar
  refine ⟨fun i j => ∑ r : κ, star (a r i) * a r j, ?_⟩
  intro i j x hx y hy
  calc
    inner Complex (E.operator i x) (E.operator j y) =
        inner Complex (E.operator i x)
          ((∑ r : κ, (LinearMap.adjoint (R r)).comp (R r)) (E.operator j y)) := by
            rw [hR_complete]
            rfl
    _ = ∑ r : κ, inner Complex (R r (E.operator i x)) (R r (E.operator j y)) := by
          rw [LinearMap.sum_apply]
          change inner Complex (E.operator i x)
            (∑ r : κ, LinearMap.adjoint (R r) (R r (E.operator j y))) = _
          rw [inner_sum]
          apply Finset.sum_congr rfl
          intro r _
          exact LinearMap.adjoint_inner_right (𝕜 := Complex)
            (R r) (E.operator i x) (R r (E.operator j y))
    _ = ∑ r : κ, (star (a r i) * a r j) * inner Complex x y := by
          apply Finset.sum_congr rfl
          intro r _
          rw [ha r i x hx, ha r j y hy]
          simp
          ring
    _ = (∑ r : κ, star (a r i) * a r j) * inner Complex x y := by
          rw [Finset.sum_mul]

end FiniteKrausFamily

namespace QuditSubsystem

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

/-!
## Concrete erasure branches

The branch family below is the literal basis contraction of the selected
tensor factor.  It is kept separate from recovery branches so that the
heterogeneous `global register -> complement` type remains explicit.
-/

/-- The identity unitary transport, used only to keep finite Kraus transport typed. -/
noncomputable def identityTransport (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H] : UnitaryTransport H H where
  toLinearEquiv := LinearEquiv.refl Complex H
  map_inner := by intro x y; rfl

/-- Contract a selected basis vector after the concrete global factorization. -/
noncomputable def erasureFactorizedKraus (S : QuditSubsystem q) :
    FiniteKrausFamily (Fin (Module.finrank Complex S.selectedSystem))
      S.factorizedSystem S.complementSystem where
  operator := fun a => LinearMap.adjoint
    (S.prepareFactorizedBranch ((stdOrthonormalBasis Complex S.selectedSystem) a))

/-- Contract a selected basis vector after the concrete global factorization. -/
noncomputable def erasureKraus (S : QuditSubsystem q) :
    FiniteKrausFamily (Fin (Module.finrank Complex S.selectedSystem))
      (Qudit.QuditRegister q) S.complementSystem :=
  S.erasureFactorizedKraus.unitaryTransport
      S.registerFactorization.symm (identityTransport S.complementSystem)

@[simp]
theorem erasureKraus_operator (S : QuditSubsystem q)
    (a : Fin (Module.finrank Complex S.selectedSystem)) :
    (S.erasureKraus).operator a =
      (LinearMap.adjoint
        (S.prepareFactorizedBranch ((stdOrthonormalBasis Complex S.selectedSystem) a))).comp
        S.registerFactorization.toLinearEquiv.toLinearMap := by
  rfl

/- The adjoint of preparation contracts its selected tensor vector. -/
theorem adjoint_prepareFactorizedBranch_apply_tmul_reference
    (S : QuditSubsystem q) (u h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.prepareFactorizedBranch u) (h ⊗ₜ[Complex] k) =
      (inner Complex u h) • k := by
  apply (ext_iff_inner_left Complex).mpr
  intro l
  rw [LinearMap.adjoint_inner_right]
  simp [S.prepareFactorizedBranch_apply, TensorProduct.inner_tmul, inner_smul_right]

/- A prepared branch followed by its adjoint is the selected matrix unit. -/
theorem prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
    (S : QuditSubsystem q) (u v : S.selectedSystem) :
    (S.prepareFactorizedBranch u).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch v)) =
      S.extendLocal (InnerProductSpace.rankOne Complex u v).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      rw [LinearMap.comp_apply,
        S.adjoint_prepareFactorizedBranch_apply_tmul_reference,
        S.prepareFactorizedBranch_apply, S.extendLocal_apply_tmul]
      simp [InnerProductSpace.rankOne_apply, TensorProduct.smul_tmul']
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

/- Extending the selected identity is the factorized identity. -/
theorem extendLocal_one_reference (S : QuditSubsystem q) :
    S.extendLocal (1 : Operator S.selectedSystem) = 1 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k => simp [S.extendLocal_apply_tmul]
  | add x y hx hy => simp [hx, hy]

/- The factored erasure branch family is complete. -/
theorem erasureKraus_complete (S : QuditSubsystem q) :
    (S.erasureKraus).Complete := by
  let b := stdOrthonormalBasis Complex S.selectedSystem
  have hfactorized : S.erasureFactorizedKraus.Complete := by
    rw [FiniteKrausFamily.Complete]
    calc
      ∑ a, (LinearMap.adjoint (S.erasureFactorizedKraus.operator a)).comp
          (S.erasureFactorizedKraus.operator a) =
          ∑ a, S.extendLocal (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro a _
            simpa only [erasureFactorizedKraus, LinearMap.adjoint_adjoint] using
              S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
                (b a) (b a)
      _ = S.extendLocal (∑ a,
          (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) := by
            symm
            unfold QuditSubsystem.extendLocal
            induction (Finset.univ : Finset (Fin (Module.finrank Complex S.selectedSystem)))
                using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
                rw [Finset.sum_insert ha, TensorProduct.map_add_left, ih,
                  Finset.sum_insert ha]
      _ = S.extendLocal 1 := by
            congr 1
            simpa [Module.End.one_eq_id] using congrArg ContinuousLinearMap.toLinearMap
              (OrthonormalBasis.sum_rankOne_eq_id b)
      _ = 1 := S.extendLocal_one_reference
  change (S.erasureFactorizedKraus.unitaryTransport S.registerFactorization.symm
    (identityTransport S.complementSystem)).Complete
  exact S.erasureFactorizedKraus.unitaryTransport_complete S.registerFactorization.symm
    (identityTransport S.complementSystem) hfactorized

/- A Kraus sandwich maps a rank-one operator to the rank one of its images. -/
theorem comp_rankOne_comp_adjoint_reference {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (x y : H) :
    L.comp ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L x) (L y)).toLinearMap := by
  ext z
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

/- The diagonal coefficient contraction of an orthonormal basis. -/
theorem sum_star_inner_mul_inner_eq_inner {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H) (x y : H) :
    (∑ a : κ, star (inner Complex (b a) x) * inner Complex (b a) y) =
      inner Complex x y := by
  calc
    (∑ a : κ, star (inner Complex (b a) x) * inner Complex (b a) y) =
        ∑ a : κ, inner Complex x (inner Complex (b a) y • b a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [inner_smul_right]
          rw [← inner_conj_symm]
          simp
          ring
    _ = inner Complex x (∑ a : κ, inner Complex (b a) y • b a) := by
          rw [inner_sum]
    _ = inner Complex x y := by rw [b.sum_repr']

/- Tensoring a rank-one operator commutes with scalar multiplication. -/
theorem smul_tensorMap_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (c : Complex) (x y : H) (u v : K) :
    c • (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] u)
      (y ⊗ₜ[Complex] v)).toLinearMap =
      TensorProduct.map (c • (InnerProductSpace.rankOne Complex x y).toLinearMap)
        (InnerProductSpace.rankOne Complex u v).toLinearMap := by
  rw [TensorProduct.map_smul_left, tensorMap_rankOne]

/- The literal basis contractions induce the concrete factorized erasure channel. -/
theorem erasureFactorizedKraus_inducedMap_rankOne_tmul
    (S : QuditSubsystem q) (h h' : S.selectedSystem)
    (k k' : S.complementSystem) :
    S.erasureFactorizedKraus.inducedMap
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by
  let b := stdOrthonormalBasis Complex S.selectedSystem
  rw [FiniteKrausFamily.inducedMap_apply]
  have hterm (a : Fin (Module.finrank Complex S.selectedSystem)) :
      (S.erasureFactorizedKraus.operator a).comp
        ((InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
          (h' ⊗ₜ[Complex] k')).toLinearMap.comp
          (LinearMap.adjoint (S.erasureFactorizedKraus.operator a))) =
        (InnerProductSpace.rankOne Complex
          ((inner Complex (b a) h) • k)
          ((inner Complex (b a) h') • k')).toLinearMap := by
    rw [comp_rankOne_comp_adjoint_reference]
    simp only [erasureFactorizedKraus]
    rw [S.adjoint_prepareFactorizedBranch_apply_tmul_reference,
      S.adjoint_prepareFactorizedBranch_apply_tmul_reference]
  have hsum : (∑ i, (S.erasureFactorizedKraus.operator i).comp
      ((InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap.comp
        (LinearMap.adjoint (S.erasureFactorizedKraus.operator i))) =
      ∑ i, (InnerProductSpace.rankOne Complex
        ((inner Complex (b i) h) • k)
        ((inner Complex (b i) h') • k')).toLinearMap) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i
  rw [hsum]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  calc
    (∑ x, inner Complex ((inner Complex (b x) h') • k') z •
        ((inner Complex (b x) h) • k)) =
        (∑ x, star (inner Complex (b x) h') * inner Complex (b x) h) •
          (inner Complex k' z • k) := by
            calc
              (∑ x, inner Complex ((inner Complex (b x) h') • k') z •
                  ((inner Complex (b x) h) • k)) =
                  ∑ x, (star (inner Complex (b x) h') * inner Complex (b x) h) •
                    (inner Complex k' z • k) := by
                      apply Finset.sum_congr rfl
                      intro x _
                      rw [inner_smul_left]
                      simp only [smul_smul]
                      congr 1
                      simp only [starRingEnd_apply]
                      ring
              _ = (∑ x, star (inner Complex (b x) h') * inner Complex (b x) h) •
                  (inner Complex k' z • k) := by
                    rw [Finset.sum_smul]
    _ = (inner Complex h' h) • (inner Complex k' z • k) := by
          rw [sum_star_inner_mul_inner_eq_inner b h' h]
    _ = ((inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap) z := by
          simp [InnerProductSpace.rankOne_apply, smul_smul]

/- The concrete factored erasure contracts the selected tensor factor. -/
theorem erasureChannel_rankOne_tmul_reference (S : QuditSubsystem q)
    (h h' : S.selectedSystem) (k k' : S.complementSystem) :
    S.erasureChannel
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by
  simp only [erasureChannel, QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [conjOperator_rankOne S.factorSwap]
  simp only [S.factorSwap_apply_tmul]
  exact partialTraceRightRaw_rankOne_tmul S.complementSystem S.selectedSystem k k' h h'

/- The factorized finite Kraus family is exactly the concrete factorized erasure channel. -/
theorem erasureFactorizedKraus_inducedMap_eq_erasureChannel (S : QuditSubsystem q) :
    S.erasureFactorizedKraus.inducedMap = S.erasureChannel.toLinearMap := by
  let bSelected := stdOrthonormalBasis Complex S.selectedSystem
  let bComplement := stdOrthonormalBasis Complex S.complementSystem
  apply linearMap_ext_of_rankOne_basis (bSelected.tensorProduct bComplement)
  intro i j
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  simp only [OrthonormalBasis.tensorProduct_apply']
  exact (S.erasureFactorizedKraus_inducedMap_rankOne_tmul
    (bSelected i) (bSelected j) (bComplement k) (bComplement l)).trans
      (S.erasureChannel_rankOne_tmul_reference
        (bSelected i) (bSelected j) (bComplement k) (bComplement l)).symm

/- The complete finite branch package agrees with factorized erasure as a CPTP channel. -/
theorem erasureFactorizedKraus_toQuantumChannel_eq_erasureChannel
    (S : QuditSubsystem q) (hComplete : S.erasureFactorizedKraus.Complete) :
    S.erasureFactorizedKraus.toQuantumChannel hComplete = S.erasureChannel := by
  apply quantumChannel_ext
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  exact S.erasureFactorizedKraus_inducedMap_eq_erasureChannel

/- Transporting the factorized family back gives the literal global erasure map. -/
theorem erasureKraus_inducedMap_eq_erasureChannelFromRegister (S : QuditSubsystem q) :
    S.erasureKraus.inducedMap = S.erasureChannelFromRegister.toLinearMap := by
  apply LinearMap.ext
  intro A
  change (S.erasureFactorizedKraus.unitaryTransport S.registerFactorization.symm
    (identityTransport S.complementSystem)).inducedMap A = _
  rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply]
  rw [S.erasureFactorizedKraus_inducedMap_eq_erasureChannel]
  simp [identityTransport, UnitaryTransport.conjOperator, UnitaryTransport.symm,
    QuditSubsystem.erasureChannelFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]

/- The complete global branch package is the concrete global erasure channel. -/
theorem erasureKraus_toQuantumChannel_eq_erasureChannelFromRegister
    (S : QuditSubsystem q) (hComplete : S.erasureKraus.Complete) :
    S.erasureKraus.toQuantumChannel hComplete = S.erasureChannelFromRegister := by
  apply quantumChannel_ext
  rw [FiniteKrausFamily.toQuantumChannel_toLinearMap]
  exact S.erasureKraus_inducedMap_eq_erasureChannelFromRegister

/- Cross products of global erasure branches are the concrete selected matrix units. -/
theorem erasureKraus_adjoint_comp (S : QuditSubsystem q)
    (i j : Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.erasureKraus).operator i)).comp
      ((S.erasureKraus).operator j) =
      S.extendLocalToRegister (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex S.selectedSystem) i)
        ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap := by
  let U := S.registerFactorization.symm
  have hFactor := S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch_reference
    ((stdOrthonormalBasis Complex S.selectedSystem) i)
    ((stdOrthonormalBasis Complex S.selectedSystem) j)
  apply LinearMap.ext
  intro x
  calc
    ((LinearMap.adjoint ((S.erasureKraus).operator i)).comp
        ((S.erasureKraus).operator j)) x =
        U (((LinearMap.adjoint ((S.erasureFactorizedKraus).operator i)).comp
          ((S.erasureFactorizedKraus).operator j)) (U.symm x)) := by
            simp [erasureKraus, U, FiniteKrausFamily.unitaryTransport,
              identityTransport, LinearMap.comp_apply,
              S.registerFactorization.adjoint_toLinearMap]
    _ = U ((S.extendLocal (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex S.selectedSystem) i)
        ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap) (U.symm x)) := by
            congr 1
            simpa only [erasureFactorizedKraus, LinearMap.adjoint_adjoint] using
              congrArg (fun f : Operator S.factorizedSystem => f (U.symm x)) hFactor
    _ = (S.extendLocalToRegister (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex S.selectedSystem) i)
        ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap) x := by
            simp [U, extendLocalToRegister, UnitaryTransport.conjOperator]

/- Correctability of concrete erasure polarizes to overlaps of its heterogeneous branches. -/
theorem erasureRecovery_matrixElement_scalars (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery) :
    ∃ scalar : Fin (Module.finrank Complex S.selectedSystem) →
        Fin (Module.finrank Complex S.selectedSystem) → Complex,
      ∀ i j (x : Qudit.QuditRegister q), x ∈ C.carrier →
        ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
          inner Complex ((S.erasureKraus).operator i x)
            ((S.erasureKraus).operator j y) =
              scalar i j * inner Complex x y := by
  classical
  rcases QuantumChannel.exists_finiteKrausFamily_representation recovery with
    ⟨m, R, hR_complete, hR_map⟩
  apply FiniteKrausFamily.exists_heterogeneous_matrix_element_scalars_of_correctedBy
    S.erasureKraus C R.operator hR_complete
  intro rho hRho
  calc
    (∑ r : Fin m, (R.operator r).comp
        ((S.erasureKraus.inducedMap rho.toOperator).comp
          (LinearMap.adjoint (R.operator r)))) =
        R.inducedMap (S.erasureKraus.inducedMap rho.toOperator) := by
          exact (FiniteKrausFamily.inducedMap_apply R
            (S.erasureKraus.inducedMap rho.toOperator)).symm
    _ = recovery.toLinearMap (S.erasureKraus.inducedMap rho.toOperator) := by
          rw [hR_map]
    _ = recovery (S.erasureChannelFromRegister rho.toOperator) := by
          rw [S.erasureKraus_inducedMap_eq_erasureChannelFromRegister]
    _ = rho.toOperator := hcorrect rho hRho

/- Each selected basis matrix unit is detectable directly from erasure recovery. -/
theorem erasureRecovery_rankOne_detectableOnWithScalar (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (i j : Fin (Module.finrank Complex S.selectedSystem)) :
    ∃ scalar : Complex,
      DetectableOnWithScalar C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) i)
          ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap)
        scalar := by
  rcases S.erasureRecovery_matrixElement_scalars C recovery hcorrect with ⟨scalar, hscalar⟩
  refine ⟨scalar i j, ?_⟩
  intro x hx y hy
  calc
    inner Complex x
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) i)
          ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap y) =
        inner Complex x
          (((LinearMap.adjoint ((S.erasureKraus).operator i)).comp
            ((S.erasureKraus).operator j)) y) := by
              rw [S.erasureKraus_adjoint_comp i j]
    _ = inner Complex ((S.erasureKraus).operator i x)
          ((S.erasureKraus).operator j y) := by
            rw [LinearMap.comp_apply]
            exact LinearMap.adjoint_inner_right (𝕜 := Complex)
              ((S.erasureKraus).operator i) x ((S.erasureKraus).operator j y)
    _ = scalar i j * inner Complex x y := hscalar i j x hx y hy

/- Identity extension is complex-linear in the local selected operator. -/
theorem extendLocalToRegister_smul_reference (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (a • A) = a • S.extendLocalToRegister A := by
  unfold extendLocalToRegister extendLocal
  rw [TensorProduct.map_smul_left]
  ext x
  simp [UnitaryTransport.conjOperator]

/- Identity extension preserves addition of selected operators. -/
theorem extendLocalToRegister_add_reference (S : QuditSubsystem q)
    (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A + B) =
      S.extendLocalToRegister A + S.extendLocalToRegister B := by
  unfold extendLocalToRegister extendLocal
  rw [TensorProduct.map_add_left]
  ext x
  simp [UnitaryTransport.conjOperator]

/- Identity extension sends the zero selected operator to zero. -/
theorem extendLocalToRegister_zero_reference (S : QuditSubsystem q) :
    S.extendLocalToRegister (0 : Operator S.selectedSystem) = 0 := by
  unfold extendLocalToRegister extendLocal
  rw [TensorProduct.map_zero_left]
  simp [UnitaryTransport.conjOperator]

/- Identity extension preserves finite sums of selected operators. -/
theorem extendLocalToRegister_sum_reference (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocalToRegister (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocalToRegister (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [S.extendLocalToRegister_zero_reference]
  | insert i s his ih =>
      calc
        S.extendLocalToRegister (∑ j ∈ insert i s, f j) =
            S.extendLocalToRegister (f i + ∑ j ∈ s, f j) := by
              rw [Finset.sum_insert his]
        _ = S.extendLocalToRegister (f i) +
            S.extendLocalToRegister (∑ j ∈ s, f j) :=
              S.extendLocalToRegister_add_reference _ _
        _ = S.extendLocalToRegister (f i) + ∑ j ∈ s,
            S.extendLocalToRegister (f j) := by rw [ih]
        _ = ∑ j ∈ insert i s, S.extendLocalToRegister (f j) := by
              rw [Finset.sum_insert his]

/- Expand a finite selected operator in all matrix units of an orthonormal basis. -/
theorem operator_eq_sum_rankOne_matrix_basis_reference {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
      (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
  calc
    A = ∑ i : κ, (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap :=
      operator_eq_sum_rankOne_basis H b A
    _ = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
        (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          ext x
          simp only [LinearMap.sum_apply, LinearMap.smul_apply]
          change inner Complex (b i) x • A (b i) =
            ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j)
          calc
            inner Complex (b i) x • A (b i) = inner Complex (b i) x •
                ∑ j : κ, inner Complex (b j) (A (b i)) • b j := by
                  rw [b.sum_repr']
            _ = ∑ j : κ, inner Complex (b j) (A (b i)) •
                (inner Complex (b i) x • b j) := by
                  rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  simp [smul_smul, mul_comm]

/- Exact erasure recovery makes every selected operator detectable on the code. -/
theorem erasureRecovery_allSelected_detectableOn (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (A : Operator S.selectedSystem) :
    DetectableOn C (S.extendLocalToRegister A) := by
  classical
  let b := stdOrthonormalBasis Complex S.selectedSystem
  choose scalar hscalar using fun i j =>
    S.erasureRecovery_rankOne_detectableOnWithScalar C recovery hcorrect i j
  rw [operator_eq_sum_rankOne_matrix_basis_reference b A]
  rw [S.extendLocalToRegister_sum_reference Finset.univ]
  simp_rw [S.extendLocalToRegister_sum_reference]
  simp_rw [S.extendLocalToRegister_smul_reference]
  refine ⟨∑ i, ∑ j, inner Complex (b j) (A (b i)) * scalar j i, ?_⟩
  intro x hx y hy
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
  calc
    (∑ x_1, ∑ x_2,
        inner Complex (b x_2) (A (b x_1)) *
          inner Complex x
            (S.extendLocalToRegister
              ((InnerProductSpace.rankOne Complex (b x_2) (b x_1)).toLinearMap) y)) =
        ∑ i, ∑ j, inner Complex (b j) (A (b i)) *
          (scalar j i * inner Complex x y) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [hscalar j i x hx y hy]
    _ = (∑ i, ∑ j, inner Complex (b j) (A (b i)) * scalar j i) *
        inner Complex x y := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring

/- The component orthogonal to a code carrier is removed by its projector. -/
theorem one_sub_projector_apply_mem_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (C : QuantumCode H) (z : H) :
    ((1 - C.projector : Operator H) z) ∈ C.carrierᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  have hprojected : inner Complex (C.projector z) y = inner Complex z y := by
    calc
      inner Complex (C.projector z) y =
          inner Complex z (LinearMap.adjoint C.projector y) :=
            (LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector z y).symm
      _ = inner Complex z (C.projector y) := by
            rw [C.projector_adjoint_eq_self]
      _ = inner Complex z y := by rw [C.projector_eq_self_of_mem hy]
  change inner Complex (z - C.projector z) y = 0
  rw [inner_sub_left, hprojected]
  ring

/- Support of a pure state's right marginal puts each reference coefficient in the code. -/
theorem rightTensorCoefficients_mem_carrier_of_rightMarginal_supportedOn
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (C : QuantumCode H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1)
    (hsupported : DensityOperator.SupportedOn C
      (rightMarginal (pureDensity psi hpsi)))
    (j : Fin (Module.finrank Complex K)) :
    rightTensorCoefficients b psi j ∈ C.carrier := by
  classical
  let a : Fin (Module.finrank Complex K) → H := rightTensorCoefficients b psi
  let rho := rightMarginal (pureDensity psi hpsi)
  have hgram : rho.toOperator = ∑ k,
      (InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap := by
    calc
      rho.toOperator = (rightAmplitude b psi).comp (LinearMap.adjoint (rightAmplitude b psi)) :=
        rightMarginal_pureDensity_toOperator b psi hpsi
      _ = ∑ k, (InnerProductSpace.rankOne Complex
          (rightAmplitude b psi (b k)) (rightAmplitude b psi (b k))).toLinearMap :=
        comp_adjoint_eq_sum_rankOne b (rightAmplitude b psi)
      _ = ∑ k, (InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap := by
        apply Finset.sum_congr rfl
        intro k _
        simp [a, rightAmplitude_apply_basis]
  let v : H := (1 - C.projector : Operator H) (a j)
  have hvorth : v ∈ C.carrierᗮ := by
    simpa [v] using one_sub_projector_apply_mem_orthogonal C (a j)
  have hquad : (∑ k, inner Complex
      ((InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap v) v) = 0 := by
    have hrange : rho.toOperator v ∈ C.carrier := by
      exact hsupported v
    have hinner : inner Complex v (rho.toOperator v) = 0 :=
      (Submodule.mem_orthogonal' C.carrier v).1 hvorth (rho.toOperator v) hrange
    have hinner' : inner Complex (rho.toOperator v) v = 0 := by
      calc
        inner Complex (rho.toOperator v) v = star (inner Complex v (rho.toOperator v)) :=
          (inner_conj_symm (rho.toOperator v) v).symm
        _ = star 0 := congrArg star hinner
        _ = 0 := star_zero Complex
    rw [hgram] at hinner'
    rw [LinearMap.sum_apply, sum_inner] at hinner'
    exact hinner'
  have hterm_pos : ∀ k, LinearMap.IsPositive
      ((InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap : Operator H) := by
    intro k
    exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := Complex) (a k)).toLinearMap
  have hterm_zero : inner Complex
      ((InnerProductSpace.rankOne Complex (a j) (a j)).toLinearMap v) v = 0 := by
    have hfun : (fun k => inner Complex
        ((InnerProductSpace.rankOne Complex (a k) (a k)).toLinearMap v) v) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (by
        intro k
        exact (hterm_pos k).inner_nonneg_left v)).mp hquad
    exact congrFun hfun j
  have hajv : inner Complex (a j) v = 0 := by
    have hproduct : inner Complex (a j) v * inner Complex v (a j) = 0 := by
      simpa [InnerProductSpace.rankOne_apply] using hterm_zero
    rcases mul_eq_zero.mp hproduct with hzero | hzero
    · exact hzero
    · exact inner_eq_zero_symm.mp hzero
  have hprojected_mem : C.projector (a j) ∈ C.carrier :=
    C.projector_mem_carrier (a j)
  have hprojected_orthogonal : inner Complex (C.projector (a j)) v = 0 := by
    have hright : inner Complex v (C.projector (a j)) = 0 :=
      (Submodule.mem_orthogonal' C.carrier v).1 hvorth
        (C.projector (a j)) hprojected_mem
    calc
      inner Complex (C.projector (a j)) v =
          star (inner Complex v (C.projector (a j))) :=
            (inner_conj_symm (C.projector (a j)) v).symm
      _ = star 0 := congrArg star hright
      _ = 0 := star_zero Complex
  have hsplit : a j = C.projector (a j) + v := by
    change a j = C.projector (a j) + (a j - C.projector (a j))
    module
  have hvself : inner Complex v v = 0 := by
    have hdecompose : inner Complex (a j) v =
        inner Complex (C.projector (a j)) v + inner Complex v v := by
      calc
        inner Complex (a j) v = inner Complex (C.projector (a j) + v) v := by
          rw [← hsplit]
        _ = inner Complex (C.projector (a j)) v + inner Complex v v :=
          inner_add_left _ _ _
    rw [hajv, hprojected_orthogonal] at hdecompose
    simpa using hdecompose.symm
  have hvzero : v = 0 := by
    by_contra hne
    exact (inner_self_ne_zero.mpr hne) hvself
  apply (C.projector_eq_self_iff_mem).1
  change C.projector (a j) = a j
  change a j - C.projector (a j) = 0 at hvzero
  exact (sub_eq_zero.mp hvzero).symm

/- The selected partial trace is adjoint, under finite trace pairing, to local extension. -/
theorem selectedPartialTraceFromRegister_trace_pairing (S : QuditSubsystem q)
    (A : Operator (Qudit.QuditRegister q)) (X : Operator S.selectedSystem) :
    LinearMap.trace Complex S.selectedSystem
      ((S.selectedPartialTraceFromRegister A).comp X) =
      LinearMap.trace Complex (Qudit.QuditRegister q)
        (A.comp (S.extendLocalToRegister X)) := by
  let U := S.registerFactorization
  let T : Operator S.factorizedSystem :=
    TensorProduct.map X (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)
  let b : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex S.complementSystem)))
      Complex S.complementSystem :=
    (stdOrthonormalBasis Complex S.complementSystem).reindex Equiv.ulift.symm
  change LinearMap.trace Complex S.selectedSystem
      ((partialTraceRightRaw S.selectedSystem S.complementSystem
        (U.conjOperator A)).comp X) = _
  rw [FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
    b (U.conjOperator A) X]
  have hconj : (U.conjOperator A).comp T =
      U.conjOperator (A.comp (U.symm.conjOperator T)) := by
    simp [U, T, UnitaryTransport.conjOperator, LinearMap.comp_assoc]
  rw [hconj, U.trace_conjOperator]
  change LinearMap.trace Complex (Qudit.QuditRegister q)
    (A.comp (S.extendLocalToRegister X)) = _
  rfl

/- A detectable selected observable has the same trace on every supported density. -/
theorem trace_comp_eq_scalar_of_supported_detectableOnWithScalar
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (C : QuantumCode H) (E : Operator H) (c : Complex)
    (hdetect : DetectableOnWithScalar C E c) (rho : DensityOperator H)
    (hsupported : DensityOperator.SupportedOn C rho) :
    LinearMap.trace Complex H (E.comp rho.toOperator) = c := by
  have hleft := DensityOperator.supportedOn_projector_comp_eq_self C rho hsupported
  have hright := DensityOperator.supportedOn_comp_projector_eq_self C rho hsupported
  have hcompression := projectorEquation_of_detectableOnWithScalar hdetect
  calc
    LinearMap.trace Complex H (E.comp rho.toOperator) =
        LinearMap.trace Complex H
          (((C.projector.comp E).comp C.projector).comp rho.toOperator) := by
            symm
            calc
              LinearMap.trace Complex H
                  (((C.projector.comp E).comp C.projector).comp rho.toOperator) =
                  LinearMap.trace Complex H (C.projector.comp (E.comp rho.toOperator)) := by
                    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hleft]
              _ = LinearMap.trace Complex H ((E.comp rho.toOperator).comp C.projector) :=
                    (LinearMap.trace_comp_comm' C.projector (E.comp rho.toOperator)).symm
              _ = LinearMap.trace Complex H (E.comp (rho.toOperator.comp C.projector)) := by
                    rw [LinearMap.comp_assoc]
              _ = LinearMap.trace Complex H (E.comp rho.toOperator) := by rw [hright]
    _ = LinearMap.trace Complex H ((c • C.projector).comp rho.toOperator) := by
          rw [hcompression]
    _ = c := by
          rw [LinearMap.smul_comp, hleft, map_smul, rho.trace_one]
          ring

/- The finite trace pairing with a rank-one probe is its corresponding matrix entry. -/
theorem trace_comp_rankOne
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (Z : Operator H) (v u : H) :
    LinearMap.trace Complex H
      (Z.comp (InnerProductSpace.rankOne Complex v u).toLinearMap) =
      inner Complex u (Z v) := by
  have hcomp : Z.comp (InnerProductSpace.rankOne Complex v u).toLinearMap =
      (InnerProductSpace.rankOne Complex (Z v) u).toLinearMap := by
    ext z
    simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply]
  rw [hcomp, InnerProductSpace.trace_rankOne]

/- Reversing the order of a rank-one factor gives the expected carrier matrix element. -/
theorem trace_rankOne_comp
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (E : Operator H) (x y : H) :
    LinearMap.trace Complex H
      ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) =
      inner Complex y (E x) := by
  calc
    LinearMap.trace Complex H
        ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) =
        LinearMap.trace Complex H
          (E.comp (InnerProductSpace.rankOne Complex x y).toLinearMap) :=
            (LinearMap.trace_comp_comm'
              (InnerProductSpace.rankOne Complex x y).toLinearMap E).symm
    _ = inner Complex y (E x) := trace_comp_rankOne E x y

/- A code cross term has the selected marginal fixed by its carrier inner product. -/
theorem selectedPartialTraceFromRegister_rankOne_eq_smul_selectedMarginal
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho)
    (x y : Qudit.QuditRegister q) (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) :
    S.selectedPartialTraceFromRegister
      (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  let X : Operator S.selectedSystem :=
    (InnerProductSpace.rankOne Complex v u).toLinearMap
  rcases S.erasureRecovery_allSelected_detectableOn C recovery hcorrect X with ⟨c, hdetect⟩
  have htrace_rho : LinearMap.trace Complex S.selectedSystem
      ((S.selectedPartialTraceFromRegister rho.toOperator).comp X) = c := by
    calc
      LinearMap.trace Complex S.selectedSystem
          ((S.selectedPartialTraceFromRegister rho.toOperator).comp X) =
          LinearMap.trace Complex (Qudit.QuditRegister q)
            (rho.toOperator.comp (S.extendLocalToRegister X)) :=
              S.selectedPartialTraceFromRegister_trace_pairing rho.toOperator X
      _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((S.extendLocalToRegister X).comp rho.toOperator) :=
            (LinearMap.trace_comp_comm' rho.toOperator (S.extendLocalToRegister X)).symm
      _ = c := trace_comp_eq_scalar_of_supported_detectableOnWithScalar C
        (S.extendLocalToRegister X) c hdetect rho hsupported
  calc
    inner Complex u
        (S.selectedPartialTraceFromRegister
          (InnerProductSpace.rankOne Complex x y).toLinearMap v) =
        LinearMap.trace Complex S.selectedSystem
          ((S.selectedPartialTraceFromRegister
            (InnerProductSpace.rankOne Complex x y).toLinearMap).comp X) := by
              simpa [X] using
                (trace_comp_rankOne
                  (S.selectedPartialTraceFromRegister
                    (InnerProductSpace.rankOne Complex x y).toLinearMap) v u).symm
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
        ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp
          (S.extendLocalToRegister X)) :=
            S.selectedPartialTraceFromRegister_trace_pairing
              (InnerProductSpace.rankOne Complex x y).toLinearMap X
    _ = inner Complex y ((S.extendLocalToRegister X) x) :=
          trace_rankOne_comp (S.extendLocalToRegister X) x y
    _ = c * inner Complex y x := hdetect y hy x hx
    _ = (inner Complex y x) * c := by ring
    _ = (inner Complex y x) * LinearMap.trace Complex S.selectedSystem
        ((S.selectedPartialTraceFromRegister rho.toOperator).comp X) := by
          rw [htrace_rho]
    _ = LinearMap.trace Complex S.selectedSystem
        (((inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator).comp X) := by
          simp [LinearMap.smul_comp, smul_eq_mul]
    _ = inner Complex u
        (((inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator) v) := by
          simpa [X] using
            trace_comp_rankOne
              ((inner Complex y x) • S.selectedPartialTraceFromRegister rho.toOperator) v u

section TensorReordering

variable (S : QuditSubsystem q)
variable (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]

/-- The concrete permutation `(M tensor B) tensor Ref -> (M tensor Ref) tensor B`. -/
noncomputable def selectedReferenceReordering :
    UnitaryTransport
      (CompositeSystem S.factorizedSystem Ref)
      (CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem) := by
  let e1 := TensorProduct.assocIsometry Complex S.selectedSystem S.complementSystem Ref
  let e2 := (TensorProduct.commIsometry Complex S.complementSystem Ref).lTensor
    S.selectedSystem
  let e3 := (TensorProduct.assocIsometry Complex S.selectedSystem Ref
    S.complementSystem).symm
  let e := e1.trans (e2.trans e3)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        simpa [e, e1, e2, e3] using e.inner_map_map x y }

@[simp]
theorem selectedReferenceReordering_apply_tmul
    (selected : S.selectedSystem) (complement : S.complementSystem) (ref : Ref) :
    S.selectedReferenceReordering Ref ((selected ⊗ₜ[Complex] complement) ⊗ₜ[Complex] ref) =
      (selected ⊗ₜ[Complex] ref) ⊗ₜ[Complex] complement := by
  rfl

/-- The global-register factorization extended by an untouched reference factor. -/
noncomputable def registerFactorizationWithReference :
    UnitaryTransport
      (CompositeSystem (Qudit.QuditRegister q) Ref)
      (CompositeSystem S.factorizedSystem Ref) := by
  let e := S.registerFactorization.toLinearIsometryEquiv.rTensor Ref
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        change inner Complex (e x) (e y) = inner Complex x y
        exact e.inner_map_map x y }

@[simp]
theorem registerFactorizationWithReference_apply_tmul
    (global : Qudit.QuditRegister q) (ref : Ref) :
    S.registerFactorizationWithReference Ref (global ⊗ₜ[Complex] ref) =
      (S.registerFactorization global) ⊗ₜ[Complex] ref := by
  rfl

/-- The concrete global permutation used before tracing the complementary register. -/
noncomputable def selectedReferenceTransport :
    UnitaryTransport
      (CompositeSystem (Qudit.QuditRegister q) Ref)
      (CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem) := by
  let e := (S.registerFactorizationWithReference Ref).toLinearIsometryEquiv.trans
    (S.selectedReferenceReordering Ref).toLinearIsometryEquiv
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_inner := by
        intro x y
        change inner Complex (e x) (e y) = inner Complex x y
        exact e.inner_map_map x y }

@[simp]
theorem selectedReferenceTransport_apply_tmul
    (global : Qudit.QuditRegister q) (ref : Ref) :
    S.selectedReferenceTransport Ref (global ⊗ₜ[Complex] ref) =
      S.selectedReferenceReordering Ref ((S.registerFactorization global) ⊗ₜ[Complex] ref) := by
  rfl

/-- Trace out the complementary register after putting the selected and reference factors together. -/
noncomputable def selectedReferenceMarginal
  (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    DensityOperator (CompositeSystem S.selectedSystem Ref) :=
  (partialTraceRightRaw_cptp (CompositeSystem S.selectedSystem Ref) S.complementSystem).mapDensity
    ((QuantumChannel.unitaryConj
      (S.selectedReferenceTransport Ref)).mapDensity omega)

end TensorReordering

/- The selected/reference raw marginal is a linear operator-space map. -/
noncomputable def selectedReferenceRaw (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref] :
    Operator (CompositeSystem (Qudit.QuditRegister q) Ref) →ₗ[Complex]
      Operator (CompositeSystem S.selectedSystem Ref) :=
  (partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem).comp
    (S.selectedReferenceTransport Ref).conjOperatorLinearMap

/- Extending a global operator by a reference matrix unit commutes with selected tracing. -/
set_option maxHeartbeats 800000 in
theorem selectedReferenceRaw_extension (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref] (A : Operator (Qudit.QuditRegister q))
    (r s : Ref) :
    partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      ((S.selectedReferenceTransport Ref).conjOperator
        (TensorProduct.map A (InnerProductSpace.rankOne Complex r s).toLinearMap)) =
      TensorProduct.map (S.selectedPartialTraceFromRegister A)
        (InnerProductSpace.rankOne Complex r s).toLinearMap := by
  classical
  change S.selectedReferenceRaw Ref
    (TensorProduct.map A (InnerProductSpace.rankOne Complex r s).toLinearMap) = _
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex]
      Operator (CompositeSystem S.selectedSystem Ref) :=
    {
    toFun := fun Z => S.selectedReferenceRaw Ref
      (TensorProduct.map Z (InnerProductSpace.rankOne Complex r s).toLinearMap)
    map_add' := by
      intro X Y
      rw [TensorProduct.map_add_left]
      exact (S.selectedReferenceRaw Ref).map_add _ _
    map_smul' := by
      intro a X
      rw [TensorProduct.map_smul_left]
      exact (S.selectedReferenceRaw Ref).map_smul a _
    }
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex]
      Operator (CompositeSystem S.selectedSystem Ref) :=
    {
    toFun := fun Z => TensorProduct.map (S.selectedPartialTraceFromRegister Z)
      (InnerProductSpace.rankOne Complex r s).toLinearMap
    map_add' := by
      intro X Y
      simp [TensorProduct.map_add_left]
    map_smul' := by
      intro a X
      simp [TensorProduct.map_smul_left]
    }
  have hmaps : Phi = Psi := by
    let b := EuclideanSpace.basisFun (Qudit.Label q) Complex
    apply linearMap_ext_of_rankOne_basis b Phi Psi
    intro x y
    dsimp [Phi, Psi]
    change partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      ((S.selectedReferenceTransport Ref).conjOperator
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex (b x) (b y)).toLinearMap
          (InnerProductSpace.rankOne Complex r s).toLinearMap)) = _
    rw [tensorMap_rankOne]
    rw [conjOperator_rankOne]
    have hxr : S.selectedReferenceTransport Ref ((b x) ⊗ₜ[Complex] r) =
        S.selectedReferenceReordering Ref ((S.registerFactorization (b x)) ⊗ₜ[Complex] r) := rfl
    have hys : S.selectedReferenceTransport Ref ((b y) ⊗ₜ[Complex] s) =
        S.selectedReferenceReordering Ref ((S.registerFactorization (b y)) ⊗ₜ[Complex] s) := rfl
    have htransport :
        (InnerProductSpace.rankOne Complex
          (S.selectedReferenceTransport Ref ((b x) ⊗ₜ[Complex] r))
          (S.selectedReferenceTransport Ref ((b y) ⊗ₜ[Complex] s))).toLinearMap =
        (InnerProductSpace.rankOne Complex
          (S.selectedReferenceReordering Ref
            ((S.registerFactorization (b x)) ⊗ₜ[Complex] r))
          (S.selectedReferenceReordering Ref
            ((S.registerFactorization (b y)) ⊗ₜ[Complex] s))).toLinearMap := by
      rfl
    rw [htransport]
    let ux : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        ((S.registerFactorization (b x)) ⊗ₜ[Complex] r)
    let uy : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        ((S.registerFactorization (b y)) ⊗ₜ[Complex] s)
    let vx : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        (((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel x).1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
            (S.splitLabel x).2)) ⊗ₜ[Complex] r)
    let vy : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        (((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel y).1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
            (S.splitLabel y).2)) ⊗ₜ[Complex] s)
    change partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      (InnerProductSpace.rankOne Complex ux uy).toLinearMap = _
    have hfactorX : ux = vx := by
      dsimp [ux, vx]
      exact congrArg
        (fun z : S.factorizedSystem =>
          S.selectedReferenceReordering Ref (z ⊗ₜ[Complex] r))
        (S.registerFactorization_apply_basis x)
    have hfactorY : uy = vy := by
      dsimp [uy, vy]
      exact congrArg
        (fun z : S.factorizedSystem =>
          S.selectedReferenceReordering Ref (z ⊗ₜ[Complex] s))
        (S.registerFactorization_apply_basis y)
    have hfactorRank :
        (InnerProductSpace.rankOne Complex ux uy).toLinearMap =
          (InnerProductSpace.rankOne Complex vx vy).toLinearMap := by
      rw [hfactorX, hfactorY]
    refine (congrArg
      (partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem)
      hfactorRank).trans ?_
    let wx : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel x).1) ⊗ₜ[Complex] r) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel x).2)
    let wy : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel y).1) ⊗ₜ[Complex] s) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel y).2)
    have hreordering :
        (InnerProductSpace.rankOne Complex vx vy).toLinearMap =
          (InnerProductSpace.rankOne Complex wx wy).toLinearMap := by
      rfl
    refine (congrArg
      (partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem)
      hreordering).trans ?_
    dsimp [wx, wy]
    rw [partialTraceRightRaw_rankOne_tmul]
    let mx : S.selectedSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1
    let my : S.selectedSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1
    let bx : S.complementSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2
    let by_ : S.complementSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2
    have hselected :
        S.selectedPartialTraceFromRegister
          (InnerProductSpace.rankOne Complex (b x) (b y)).toLinearMap =
          (inner Complex by_ bx) • (InnerProductSpace.rankOne Complex mx my).toLinearMap := by
      simp only [selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
        QuantumChannel.unitaryConj_apply]
      rw [conjOperator_rankOne S.registerFactorization]
      change partialTraceRightRaw S.selectedSystem S.complementSystem
        (InnerProductSpace.rankOne Complex
          ((S.registerFactorization (b x)))
          ((S.registerFactorization (b y)))).toLinearMap = _
      have hfactor :
          (InnerProductSpace.rankOne Complex
            (S.registerFactorization (b x))
            (S.registerFactorization (b y))).toLinearMap =
          (InnerProductSpace.rankOne Complex
            (mx ⊗ₜ[Complex] bx) (my ⊗ₜ[Complex] by_)).toLinearMap := by
        dsimp [mx, my, bx, by_]
        rw [S.registerFactorization_apply_basis x,
          S.registerFactorization_apply_basis y]
      refine (congrArg
        (partialTraceRightRaw S.selectedSystem S.complementSystem) hfactor).trans ?_
      rw [partialTraceRightRaw_rankOne_tmul]
    rw [hselected]
    change (inner Complex by_ bx) •
        (InnerProductSpace.rankOne Complex (mx ⊗ₜ[Complex] r)
          (my ⊗ₜ[Complex] s)).toLinearMap =
      TensorProduct.map ((inner Complex by_ bx) •
        (InnerProductSpace.rankOne Complex mx my).toLinearMap)
        (InnerProductSpace.rankOne Complex r s).toLinearMap
    exact smul_tensorMap_rankOne (inner Complex by_ bx) mx my r s
  exact congrArg (fun F : Operator (Qudit.QuditRegister q) →ₗ[Complex]
    Operator (CompositeSystem S.selectedSystem Ref) => F A) hmaps

/- The selected/reference marginal of a pure state is its finite coefficient double sum. -/
theorem selectedReferenceMarginal_pureDensity_toOperator_sum (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
    (b : OrthonormalBasis (Fin (Module.finrank Complex Ref)) Complex Ref)
    (psi : CompositeSystem (Qudit.QuditRegister q) Ref) (hpsi : ‖psi‖ ^ 2 = 1) :
    (S.selectedReferenceMarginal Ref (pureDensity psi hpsi)).toOperator =
      ∑ i, ∑ j,
        TensorProduct.map
          (S.selectedPartialTraceFromRegister
            (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
              (rightTensorCoefficients b psi j)).toLinearMap)
          (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by
  change partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
    ((S.selectedReferenceTransport Ref).conjOperator
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap) = _
  change S.selectedReferenceRaw Ref
    (InnerProductSpace.rankOne Complex psi psi).toLinearMap = _
  conv_lhs => rw [← sum_rightTensorCoefficients_tmul b psi]
  rw [rankOne_sum_sum]
  rw [map_sum (S.selectedReferenceRaw Ref) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum (S.selectedReferenceRaw Ref) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro j _
  rw [← tensorMap_rankOne]
  exact S.selectedReferenceRaw_extension Ref
    (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
      (rightTensorCoefficients b psi j)).toLinearMap (b i) (b j)

/- Tensoring a fixed finite operator distributes over a finite right-hand sum. -/
theorem tensorMap_sum_right_reference {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {κ : Type v} [Fintype κ] (A : Operator H) (f : κ → Operator K) :
    TensorProduct.map A (∑ i, f i) = ∑ i, TensorProduct.map A (f i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.sum_insert his, TensorProduct.map_add_right, ih,
        Finset.sum_insert his]

/- Tensoring a fixed finite operator distributes over a finite left-hand sum. -/
theorem tensorMap_sum_left_reference {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {κ : Type v} [Fintype κ] (f : κ → Operator H) (A : Operator K) :
    TensorProduct.map (∑ i, f i) A = ∑ i, TensorProduct.map (f i) A := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.sum_insert his, TensorProduct.map_add_left, ih,
        Finset.sum_insert his]

/- Preparing a normalized pure selected state tensors it with the retained operator. -/
theorem prepareFactorized_pureDensity_apply (S : QuditSubsystem q)
    (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1) (A : Operator S.complementSystem) :
    S.prepareFactorized (pureDensity u hu) A =
      TensorProduct.map (InnerProductSpace.rankOne Complex u u).toLinearMap A := by
  let b := stdOrthonormalBasis Complex S.complementSystem
  rw [operator_eq_sum_rankOne_basis S.complementSystem b A]
  simp only [map_sum]
  rw [tensorMap_sum_right_reference]
  apply Finset.sum_congr rfl
  intro i _
  rw [S.prepareFactorized_apply_rankOne]
  calc
    (∑ k, (InnerProductSpace.rankOne Complex
      (S.densityEnsembleVectors (pureDensity u hu) k ⊗ₜ[Complex] (A (b i)))
      (S.densityEnsembleVectors (pureDensity u hu) k ⊗ₜ[Complex] (b i))).toLinearMap) =
        ∑ k, TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (S.densityEnsembleVectors (pureDensity u hu) k)
            (S.densityEnsembleVectors (pureDensity u hu) k)).toLinearMap
          (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro k _
            rw [tensorMap_rankOne]
    _ = TensorProduct.map (∑ k,
        (InnerProductSpace.rankOne Complex
          (S.densityEnsembleVectors (pureDensity u hu) k)
          (S.densityEnsembleVectors (pureDensity u hu) k)).toLinearMap)
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
          rw [tensorMap_sum_left_reference]
    _ = TensorProduct.map (pureDensity u hu).toOperator
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
          rw [← S.densityEnsemble_specification]
    _ = TensorProduct.map (InnerProductSpace.rankOne Complex u u).toLinearMap
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
          rw [pureDensity_toOperator]

/-- Pure selected preparation is the concrete isometric branch sandwich. -/
theorem prepareFactorized_pureDensity_eq_branch_sandwich (S : QuditSubsystem q)
    (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1) (A : Operator S.complementSystem) :
    S.prepareFactorized (pureDensity u hu) A =
      (S.prepareFactorizedBranch u).comp
        (A.comp (LinearMap.adjoint (S.prepareFactorizedBranch u))) := by
  rw [S.prepareFactorized_pureDensity_apply u hu]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        S.adjoint_prepareFactorizedBranch_apply_tmul_reference,
        S.prepareFactorizedBranch_apply]
      simp [InnerProductSpace.rankOne_apply, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [map_add, hx, hy]

/--
An operator-valued density supported on the range of a normalized preparation
branch is fixed by concrete erasure followed by preparation of that branch.
-/
theorem prepareFactorized_erasure_fixed_of_supportedOn_branch
    (S : QuditSubsystem q) (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1)
    (rho : DensityOperator S.factorizedSystem)
    (hsupported : ∀ z : S.factorizedSystem,
      rho.toOperator z ∈ LinearMap.range (S.prepareFactorizedBranch u)) :
    S.prepareFactorized (pureDensity u hu) (S.erasureChannel rho.toOperator) =
      rho.toOperator := by
  have huinner : inner Complex u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hcast := congrArg (fun t : ℝ => (t : Complex)) hu
    simpa using hcast
  have hisometry :
      (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
        (S.prepareFactorizedBranch u) = 1 := by
    rw [S.adjoint_prepareFactorizedBranch_comp, huinner, one_smul]
  have hleft :
      (S.prepareFactorizedBranch u).comp
        ((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp rho.toOperator) =
        rho.toOperator := by
    apply LinearMap.ext
    intro z
    rcases hsupported z with ⟨k, hk⟩
    simp only [LinearMap.comp_apply]
    rw [← hk]
    have hk' := congrArg (fun T : Operator S.complementSystem => T k) hisometry
    simpa [LinearMap.comp_apply] using
      congrArg (fun v : S.complementSystem => S.prepareFactorizedBranch u v) hk'
  have hright :
      rho.toOperator.comp
        ((S.prepareFactorizedBranch u).comp
          (LinearMap.adjoint (S.prepareFactorizedBranch u))) = rho.toOperator := by
    have hadjoint := congrArg LinearMap.adjoint hleft
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc,
      rho.toOperator_adjoint_eq_self] using hadjoint
  let compressed : Operator S.complementSystem :=
    (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
      (rho.toOperator.comp (S.prepareFactorizedBranch u))
  have hfactor :
      (S.prepareFactorizedBranch u).comp
        (compressed.comp (LinearMap.adjoint (S.prepareFactorizedBranch u))) =
        rho.toOperator := by
    change (S.prepareFactorizedBranch u).comp
        (((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
          (rho.toOperator.comp (S.prepareFactorizedBranch u))).comp
          (LinearMap.adjoint (S.prepareFactorizedBranch u))) = rho.toOperator
    calc
      (S.prepareFactorizedBranch u).comp
          (((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
            (rho.toOperator.comp (S.prepareFactorizedBranch u))).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch u))) =
          ((S.prepareFactorizedBranch u).comp
            ((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp rho.toOperator)).comp
            ((S.prepareFactorizedBranch u).comp
              (LinearMap.adjoint (S.prepareFactorizedBranch u))) := by
              apply LinearMap.ext
              intro z
              rfl
      _ = rho.toOperator.comp
          ((S.prepareFactorizedBranch u).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch u))) := by rw [hleft]
      _ = rho.toOperator := hright
  have hprepared :
      S.prepareFactorized (pureDensity u hu) compressed = rho.toOperator := by
    rw [S.prepareFactorized_pureDensity_eq_branch_sandwich u hu]
    exact hfactor
  calc
    S.prepareFactorized (pureDensity u hu) (S.erasureChannel rho.toOperator) =
        S.prepareFactorized (pureDensity u hu)
          (S.erasureChannel
            (S.prepareFactorized (pureDensity u hu) compressed)) := by rw [hprepared]
    _ = S.prepareFactorized (pureDensity u hu) compressed := by
      rw [S.erasureChannel_prepareFactorized_apply]
    _ = rho.toOperator := hprepared

/- Global selected preparation of a normalized pure state is the concrete tensor preparation. -/
theorem prepareSelected_pureDensity_apply (S : QuditSubsystem q)
    (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1) (A : Operator S.complementSystem) :
    S.prepareSelected (pureDensity u hu) A =
      S.registerFactorization.symm.conjOperator
        (TensorProduct.map (InnerProductSpace.rankOne Complex u u).toLinearMap A) := by
  simp only [prepareSelected, QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [S.prepareFactorized_pureDensity_apply u hu A]

/-
Proof-closure inventory:
* finite Kraus branches for the concrete erasure channel and their exact
  recovery composition;
* pure-branch sandwiching and a supported-range erase/prepare fixed-point
  calculation, used by the full `|0>_M tensor B` fixture;
* heterogeneous polarization of recovery-induced branch overlaps;
* expansion into selected matrix units, yielding selected-observable
  detectability on the code;
* coefficient-wise code support for an arbitrary finite purification; and
* the concrete selected/reference partial-trace calculation and tensor
  factorization.

Downstream handoff: #389 can consume the factorization theorem as its recovery
to no-information bridge.  The later #388 entropy consequences remain a
separate downstream proof obligation.
-/
/--
Exact recovery from concrete finite qudit erasure forces the selected
subsystem of every finite purification to factor from its arbitrary reference.
-/
theorem erasureRecovery_implies_selectedReferenceMarginal_factorizes
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
    (purification : DensityOperator.FinitePurification rho Ref) :
    S.selectedReferenceMarginal Ref
      (pureDensity purification.vector purification.normSq_one) =
      tensorDensity (S.selectedPartialTraceFromRegister.mapDensity rho)
        (leftMarginal (pureDensity purification.vector purification.normSq_one)) := by
  classical
  let psi := purification.vector
  have hpsi : ‖psi‖ ^ 2 = 1 := purification.normSq_one
  have hright : (rightMarginal (pureDensity psi hpsi)).toOperator = rho.toOperator := by
    simpa [psi] using purification.rightMarginal_eq
  have hpure_supported : DensityOperator.SupportedOn C (rightMarginal (pureDensity psi hpsi)) := by
    intro z
    rw [hright]
    exact hsupported z
  let b := stdOrthonormalBasis Complex Ref
  have hcoefficient (i : Fin (Module.finrank Complex Ref)) :
      rightTensorCoefficients b psi i ∈ C.carrier :=
    rightTensorCoefficients_mem_carrier_of_rightMarginal_supportedOn C b psi hpsi
      hpure_supported i
  apply DensityOperator.ext_toOperator
  change (S.selectedReferenceMarginal Ref (pureDensity psi hpsi)).toOperator = _
  rw [S.selectedReferenceMarginal_pureDensity_toOperator_sum Ref b psi hpsi]
  rw [tensorDensity_toOperator, leftMarginal_pureDensity_toOperator_sum b psi hpsi]
  change (∑ i, ∑ j,
    TensorProduct.map
      (S.selectedPartialTraceFromRegister
        (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
          (rightTensorCoefficients b psi j)).toLinearMap)
      (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) = _
  calc
    (∑ i, ∑ j,
      TensorProduct.map
        (S.selectedPartialTraceFromRegister
          (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
            (rightTensorCoefficients b psi j)).toLinearMap)
        (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) =
        ∑ i, ∑ j,
          (inner Complex (rightTensorCoefficients b psi j)
            (rightTensorCoefficients b psi i)) •
            TensorProduct.map (S.selectedPartialTraceFromRegister rho.toOperator)
              (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [S.selectedPartialTraceFromRegister_rankOne_eq_smul_selectedMarginal
            C recovery hcorrect rho hsupported
            (rightTensorCoefficients b psi i) (rightTensorCoefficients b psi j)
            (hcoefficient i) (hcoefficient j)]
          rw [TensorProduct.map_smul_left]
    _ = TensorProduct.map (S.selectedPartialTraceFromRegister rho.toOperator)
        (∑ i, ∑ j,
          (inner Complex (rightTensorCoefficients b psi j)
            (rightTensorCoefficients b psi i)) •
            (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) := by
          symm
          rw [tensorMap_sum_right_reference]
          apply Finset.sum_congr rfl
          intro i _
          rw [tensorMap_sum_right_reference]
          apply Finset.sum_congr rfl
          intro j _
          rw [TensorProduct.map_smul_right]

end QuditSubsystem

end Semantics
end QEC
