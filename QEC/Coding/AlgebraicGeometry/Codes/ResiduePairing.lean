import QEC.Coding.AlgebraicGeometry.Codes.Code
import QEC.Coding.AlgebraicGeometry.Residues.Global.FunctionFieldGlobalResidue
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PrincipalShift

/-!
# Evaluation pairing from a specified normalized differential

The differential here is supplied as an actual object with proved residues,
not identified with a separately chosen canonical representative. If
`G + H <= div(eta) + D`, the global residue theorem makes the two evaluation
codes orthogonal. This is the pairing argument behind [Sti06, Proposition
4.3] and [Ngu24, Theorem: AG multiplication family].
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators
open FunctionFieldDifferential

noncomputable section

variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]

local instance residuePairingConstantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
local instance residuePairingConstantTower : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap (Polynomial k) F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F (Polynomial.C c))

variable {ι : Type*} [Fintype ι]

/-- Pairing vanishes by applying the global residue theorem to `xy eta`. -/
theorem agEvaluation_pairing_eq_zero_of_residue
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ differentialDivisor eta heta + evaluationDivisor Q)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule H) :
    wordPairing (agEvaluationLinearMap G Q hG x) (agEvaluationLinearMap H Q hH y) = 0 := by
  classical
  by_cases hx : (x : F) = 0
  · have hx0 : x = 0 := Subtype.ext hx
    simp [hx0, wordPairing]
  by_cases hy : (y : F) = 0
  · have hy0 : y = 0 := Subtype.ext hy
    simp [hy0, wordPairing]
  have hxy : (x : F) * (y : F) ≠ 0 := mul_ne_zero hx hy
  have hDzero (P : GlobalPlace k F) (hP : ¬ ∃ j, (Q j).place = P) :
      evaluationDivisor Q P = 0 := by
    exact zeroCoordinateDivisor_apply_eq_zero_of_not_mem Q Finset.univ P
      (fun j _ hj => hP ⟨j, hj⟩)
  have hDle (P : GlobalPlace k F) : evaluationDivisor Q P ≤ 1 := by
    by_cases hP : ∃ j, (Q j).place = P
    · obtain ⟨j, rfl⟩ := hP
      rw [evaluationDivisor_apply_at Q hQ]
    · rw [hDzero P hP]
      norm_num
  have horder (P : GlobalPlace k F) :
      -(evaluationDivisor Q P) ≤
        P.order ((x : F) * (y : F)) + differentialOrder P eta heta := by
    have hxP := (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp
      x.property P
    have hyP := (GlobalPlace.mem_riemannRochSubmodule_iff_order_add_nonnegative H hy).mp
      y.property P
    have h := hGH P
    simp only [Finsupp.add_apply, differentialDivisor_apply] at h
    rw [GlobalPlace.order_mul P hx hy]
    omega
  let omega : Differential k F := ((x : F) * (y : F)) • eta
  have homega : Differential.IsGlobalSimplePole omega := by
    intro P
    apply (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      P ((x : F) * (y : F)) hxy eta heta).mpr
    exact le_trans (neg_le_neg (hDle P)) (horder P)
  have hregular (P : GlobalPlace k F) (hP : ¬ ∃ j, (Q j).place = P) :
      omega ∈ Differential.localDifferentialLattice P := by
    apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
      P ((x : F) * (y : F)) hxy eta heta).mpr
    have h := horder P
    simpa only [hDzero P hP, neg_zero] using h
  let residues := Differential.globalSimplePoleResidue omega homega
  have hcoefficient (j : ι) : residues (Q j).place =
      agEvaluationLinearMap G Q hG x j * agEvaluationLinearMap H Q hH y j := by
    let P := (Q j).place
    letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
    letI : FiniteDimensional k P.residueField := GlobalPlace.residueField_finiteDimensional P
    have hxReg : GlobalPlace.RegularAt P (x : F) := by
      have h := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp x.property P
      have hport := h
      simp only [P, hG j, WithZero.exp_zero] at hport ⊢
      exact hport
    have hyReg : GlobalPlace.RegularAt P (y : F) := by
      have h := (GlobalPlace.mem_riemannRochSubmodule_iff H (y : F)).mp y.property P
      have hport := h
      simp only [P, hH j, WithZero.exp_zero] at hport ⊢
      exact hport
    let xO : P.valuationRing := ⟨x, (GlobalPlace.mem_valuationRing_iff P _).mpr hxReg⟩
    let yO : P.valuationRing := ⟨y, (GlobalPlace.mem_valuationRing_iff P _).mpr hyReg⟩
    let xyO : P.valuationRing := xO * yO
    have hsub : (⟨omega, homega P⟩ : Differential.simplePoleDifferentialLattice P) =
        xyO • etaAt j := by
      apply Subtype.ext
      change ((x : F) * (y : F)) • eta = ((x : F) * (y : F)) • (etaAt j : Differential k F)
      rw [hAt]
    have hresProduct : Differential.simplePoleResidue P ⟨omega, homega P⟩ = P.residue xyO := by
      rw [hsub, Differential.simplePoleResidue_smul, hres, mul_one]
    have heval : P.residue xyO = algebraMap k P.residueField ((Q j).evaluate xyO) := by
      symm
      change P.constantsToResidue ((Q j).evaluate xyO) = P.residue xyO
      rw [← (Q j).constantsEquiv_apply]
      exact (Q j).constantsEquiv.apply_symm_apply _
    have hfinrank : Module.finrank k P.residueField = 1 := by
      apply Module.finrank_of_bijective_algebraMap
      exact (Q j).constantsToResidue_bijective
    change Algebra.trace k P.residueField
      (Differential.simplePoleResidue P ⟨omega, homega P⟩) = _
    rw [hresProduct, heval, Algebra.trace_algebraMap, hfinrank, one_smul]
    change (Q j).evaluate (xO * yO) = _
    rw [map_mul]
    rfl
  have hsupport : residues.support ⊆ Finset.univ.image (fun j => (Q j).place) := by
    intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_contra hnot
    have hz := Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      P omega (homega P) (hregular P hnot)
    exact Finsupp.mem_support_iff.mp hP hz
  have hsum : residues.sum (fun _ c => c) = ∑ j : ι, residues (Q j).place := by
    rw [Finsupp.sum_of_support_subset residues hsupport (fun _ c => c) (fun _ _ => rfl)]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hQ hab
  have hz := Differential.globalSimplePoleResidueSum_eq_zero (k := k) (F := F) omega homega
  change residues.sum (fun _ c => c) = 0 at hz
  rw [hsum] at hz
  change (∑ j : ι, agEvaluationLinearMap G Q hG x j * agEvaluationLinearMap H Q hH y j) = 0
  simpa only [hcoefficient] using hz

/-- Divisor domination and the actual unit residues give code orthogonality. -/
theorem agEvaluation_le_dual_of_residue
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ differentialDivisor eta heta + evaluationDivisor Q) :
    (agEvaluationCode H Q hH).carrier ≤ (agEvaluationCode G Q hG).dual.carrier := by
  rintro y ⟨fy, rfl⟩
  apply ((agEvaluationCode G Q hG).mem_dual _).mpr
  rintro x ⟨fx, rfl⟩
  have h := agEvaluation_pairing_eq_zero_of_residue k F G H Q hQ hG hH
    eta heta etaAt hAt hres hGH fx fy
  change (∑ j : ι, agEvaluationLinearMap H Q hH fy j * agEvaluationLinearMap G Q hG fx j) = 0
  change (∑ j : ι, agEvaluationLinearMap G Q hG fx j * agEvaluationLinearMap H Q hH fy j) = 0 at h
  simpa only [mul_comm] using h

end

end QEC.Coding.AlgebraicGeometry
