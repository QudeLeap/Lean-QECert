import QEC.Coding.ExpanderCodes.LPSOriginalInfinityPoleClearingAway
import QEC.Coding.AlgebraicGeometry.Places.PolynomialMaximalPoints
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Every original reciprocal maximal ideal is an actual point

Contract an arbitrary maximal ideal to polynomial evaluation, apply finite prime avoidance including the zero ideal, and clear poles of the selected inverse away from its actual fibre. A nonzero base-polynomial value then contradicts membership in the contracted ideal. No point coverage is assumed.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Global point injectivity, differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityPointCoverageDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance LPSOriginalInfinityPointCoverageDictionary002 : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

/-- Every maximal ideal of the same original reciprocal integral closure is an existing actual infinity evaluation kernel. -/
lemma lpsOriginalInfinityNormalChart_allMaximalPoints (M : Ideal R) [M.IsMaximal] :
    ∃ x : S, M = RingHom.ker
      (lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property) := by
  classical
  let E (x : S) : R →+* ℂ := lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
  let β := lpsOriginalInfinityCoordinate N hpos hN
  let C : Ideal P := M.comap (algebraMap P R)
  let : C.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  obtain ⟨α,hα⟩ := complexPolynomialMaximal_exists_eval C
  have hbase (p : P) : algebraMap P R p ∈ M ↔ p.eval α = 0 := hα p
  have hXmem : algebraMap P R (Polynomial.X - Polynomial.C α) ∈ M :=
    (hbase _).mpr (by simp)
  have hinj : Function.Injective (algebraMap P K) :=
    lpsOriginalReciprocalPolynomialMap_injective N hpos
  have hXne : algebraMap P R (Polynomial.X - Polynomial.C α) ≠ 0 := by
    intro hz
    have hval := congrArg Subtype.val hz
    change algebraMap P K (Polynomial.X - Polynomial.C α) = 0 at hval
    exact Polynomial.X_sub_C_ne_zero α (hinj (hval.trans (map_zero _).symm))
  have hMbot : M ≠ ⊥ := by intro hz; rw [hz,Ideal.mem_bot] at hXmem;exact hXne hXmem
  by_contra hcoverage
  push Not at hcoverage
  let Y : Set S := {x | β x = α}
  have hY : Y.Finite := lpsOriginalInfinityCoordinate_fibre_finite N hpos hN α
  let I : Set (Ideal R) := insert ⊥ ((fun x : S => RingHom.ker (E x)) '' Y)
  have hI : I.Finite := (hY.image _).insert _
  have hprime : ∀ i ∈ I, i.IsPrime := by
    intro i hi
    obtain rfl | ⟨x,hx,rfl⟩ := hi
    · infer_instance
    · exact (lpsOriginalInfinityEvaluation_ker_isMaximal N hpos hN x.val x.property).isPrime
  have houtside : M ∉ I := by
    intro hM
    obtain hz | ⟨x,hx,hEq⟩ := hM
    · exact hMbot hz
    · exact hcoverage x hEq.symm
  obtain ⟨g,hg,havoid⟩ := finitePrimeAvoidance M I hI hprime houtside
  have hg0 : g ≠ 0 := by simpa only [Ideal.mem_bot] using havoid ⊥ (Set.mem_insert _ _)
  have hgv0 : g.val ≠ 0 := by intro hz;apply hg0;exact Subtype.ext hz
  have hgorder (x : S) (hx : β x = α) :
      lpsOriginalFieldLocalOrder N hN hpos x.val g.val = 0 := by
    have hnot : E x g ≠ 0 := havoid (RingHom.ker (E x))
      (Set.mem_insert_of_mem _ ⟨x,hx,rfl⟩)
    have hle : lpsOriginalFieldLocalOrder N hN hpos x.val g.val ≤ 0 := by
      apply le_of_not_gt
      intro hp
      exact hnot ((lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN
        x.val x.property g).mpr hp)
    exact le_antisymm hle (lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x.val x.property g)
  have hinv (x : S) (hx : β x = α) :
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val g.val⁻¹ := by
    rw [AddValuation.map_inv,hgorder x hx,neg_zero]
  obtain ⟨H,hHα,hHint⟩ := lpsOriginalField_reciprocal_polynomial_clear_away
    N hpos hN g.val⁻¹ α hinv
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
