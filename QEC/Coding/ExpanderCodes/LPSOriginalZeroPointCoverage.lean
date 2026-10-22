import QEC.Coding.AlgebraicGeometry.Places.PolynomialMaximalPoints
import QEC.Coding.ExpanderCodes.LPSOriginalPoleClearingAway
import QEC.Coding.ExpanderCodes.LPSOriginalNormalizationLocalRings
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Every original zero-chart maximal ideal comes from an actual interior point

Contract an arbitrary maximal ideal of the SAME original integral closure
of C[j] in C(j,jN) to a polynomial evaluation ideal at a. The actual interior
j fibre is finite. If none of its genuine evaluation kernels were the given
ideal, finite prime avoidance produces a nonzero element with order zero
on the fibre. Clear poles of its inverse away from that fibre. The resulting
nonzero polynomial value contradicts the contracted ideal. This proves
coverage even when the analytic fibre is initially empty.

Derived internal/API PK22 ex:Xpq closure, pinned main.tex484–486, for #449.
This proves zero-chart maximal-point coverage, not reciprocal-chart coverage,
global regular-differential/GAGA comparison, good reduction, Hecke/Frobenius/
Weil, or the exact arbitrary-finite-field explicit good quantum family.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalZeroCoverageDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalZeroCoverageDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalZeroCoverageDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalZeroCoverageDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

lemma lpsOriginalZeroNormalChart_allMaximalPoints (M : Ideal R) [M.IsMaximal] :
    ∃ x : Q, M = RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)) := by
  classical
  let E (x : Q) : R →+* ℂ := lpsOriginalZeroNormalChartEvaluation N hpos hN (Sum.inl x)
    (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)
  let C : Ideal P := M.comap (algebraMap P R)
  let : C.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  obtain ⟨α,hα⟩ := complexPolynomialMaximal_exists_eval C
  have hbase (p : P) : algebraMap P R p ∈ M ↔ p.eval α = 0 := hα p
  have hXmem : algebraMap P R (Polynomial.X - Polynomial.C α) ∈ M :=
    (hbase _).mpr (by simp)
  have hinj : Function.Injective (algebraMap P K) :=
    (algebraMap J K).injective.comp (IsFractionRing.injective P J)
  have hXne : algebraMap P R (Polynomial.X - Polynomial.C α) ≠ 0 := by
    intro hz
    have hval := congrArg Subtype.val hz
    change algebraMap P K (Polynomial.X - Polynomial.C α) = 0 at hval
    exact Polynomial.X_sub_C_ne_zero α (hinj (hval.trans (map_zero _).symm))
  have hMbot : M ≠ ⊥ := by intro hz; rw [hz,Ideal.mem_bot] at hXmem;exact hXne hXmem
  by_contra hcoverage
  push Not at hcoverage
  let Y : Set Q := {x | lpsOriginalFilledJ N (Sum.inl x) = α}
  have hY : Y.Finite := lpsOriginalJFibre_finite N hpos hN α
  let S : Set (Ideal R) := insert ⊥ ((fun x : Q => RingHom.ker (E x)) '' Y)
  have hS : S.Finite := (hY.image _).insert _
  have hprime : ∀ I ∈ S, I.IsPrime := by
    intro I hI
    obtain rfl | ⟨x,hx,rfl⟩ := hI
    · infer_instance
    · exact (lpsOriginalZeroEvaluation_ker_isMaximal N hpos hN (Sum.inl x)
        (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x)).isPrime
  have houtside : M ∉ S := by
    intro hM
    obtain hz | ⟨x,hx,hEq⟩ := hM
    · exact hMbot hz
    · exact hcoverage x hEq.symm
  obtain ⟨g,hg,havoid⟩ := finitePrimeAvoidance M S hS hprime houtside
  have hg0 : g ≠ 0 := by simpa only [Ideal.mem_bot] using havoid ⊥ (Set.mem_insert _ _)
  have hgv0 : g.val ≠ 0 := by intro hz;apply hg0;exact Subtype.ext hz
  have hgorder (x : Q) (hx : lpsOriginalFilledJ N (Sum.inl x) = α) :
      lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) g.val = 0 := by
    have hnot : E x g ≠ 0 := havoid (RingHom.ker (E x))
      (Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩)
    have hle : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) g.val ≤ 0 := by
      apply le_of_not_gt
      intro hp
      exact hnot ((lpsOriginalZeroEvaluation_eq_zero_iff_order_pos N hpos hN (Sum.inl x)
        (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) g).mpr hp)
    exact le_antisymm hle ((lpsOriginalField_integral_iff_noInteriorPole N hpos hN g.val).mp g.property x)
  have hinv (x : Q) (hx : lpsOriginalFilledJ N (Sum.inl x) = α) :
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) g.val⁻¹ := by
    rw [AddValuation.map_inv,hgorder x hx,neg_zero]
  obtain ⟨H,hHα,hHint⟩ := lpsOriginalField_polynomial_clear_away N hpos hN g.val⁻¹ α hinv
  let b : R := ⟨algebraMap P K H*g.val⁻¹,hHint⟩
  have hgb : g*b = algebraMap P R H := by
    apply Subtype.ext
    change g.val*(algebraMap P K H*g.val⁻¹) = algebraMap P K H
    calc
      _ = algebraMap P K H*(g.val*g.val⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hgv0,mul_one]
  have hHM : algebraMap P R H ∈ M := by rw [←hgb];exact M.mul_mem_right b hg
  exact hHα ((hbase H).mp hHM)

end
end QEC.Coding.TannerLiftedProduct
