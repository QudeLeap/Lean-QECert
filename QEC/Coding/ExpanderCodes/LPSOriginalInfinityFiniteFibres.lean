import QEC.Coding.ExpanderCodes.LPSOriginalInfinityRegularPoints
import QEC.Coding.ExpanderCodes.LPSOriginalFiniteInteriorFibres

/-!
# Actual reciprocal fibres and negative orders are finite

Actual finite interior j fibres and the finite cusp type give finite coordinate fibres and finite negative-order sets on the genuine reciprocal domain. The already proved reciprocal criterion holds on exactly this domain.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Global point injectivity, differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityFiniteFibresDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance LPSOriginalInfinityFiniteFibresDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalInfinityFiniteFibresDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalInfinityFiniteFibresDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

/-- Every actual infinity-coordinate fibre is finite using genuine interior j fibres and finite cusps. -/
lemma lpsOriginalInfinityCoordinate_fibre_finite (α : ℂ) :
    {x : S | lpsOriginalInfinityCoordinate N hpos hN x = α}.Finite := by
  let U : Set (LPSOriginalFilledCurve N) :=
    Sum.inl '' {y : Q | lpsOriginalFilledJ N (Sum.inl y) = α⁻¹} ∪
      Sum.inr '' (Set.univ : Set C)
  have hu : U.Finite :=
    ((lpsOriginalJFibre_finite N hpos hN α⁻¹).image Sum.inl).union
      ((Set.toFinite (Set.univ : Set C)).image Sum.inr)
  apply (hu.preimage Subtype.val_injective.injOn).subset
  rintro ⟨x,hx⟩ hα
  cases x with
  | inl y =>
    have hy := lpsOriginalInfinityRegular_interior_nonzero N hpos hN y hx
    have hv : (lpsOriginalFilledJ N (Sum.inl y))⁻¹ = α :=
      (lpsOriginalInfinityCoordinate_interior N hpos hN y hy).symm.trans hα
    exact Or.inl ⟨y,by change lpsOriginalFilledJ N (Sum.inl y) = α⁻¹; rw [←hv,inv_inv],rfl⟩
  | inr c => exact Or.inr ⟨c,Set.mem_univ _,rfl⟩

/-- An arbitrary element of the original generated field has finitely many negative orders on the actual reciprocal domain. -/
lemma lpsOriginalField_negativeInfinityOrders_finite (f : K) :
    {x : S | lpsOriginalFieldLocalOrder N hN hpos x.val f < 0}.Finite := by
  let U : Set (LPSOriginalFilledCurve N) :=
    Sum.inl '' {y : Q | lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) f < 0} ∪
      Sum.inr '' (Set.univ : Set C)
  have hu : U.Finite :=
    ((lpsOriginalField_negativeInteriorOrders_finite N hpos hN f).image Sum.inl).union
      ((Set.toFinite (Set.univ : Set C)).image Sum.inr)
  apply (hu.preimage Subtype.val_injective.injOn).subset
  rintro ⟨x,hx⟩ hbad
  cases x with
  | inl y => exact Or.inl ⟨y,hbad,rfl⟩
  | inr c => exact Or.inr ⟨c,Set.mem_univ _,rfl⟩

/-- Same-field reciprocal integrality is exactly nonnegative order at every point of the actual reciprocal domain. -/
lemma lpsOriginalField_reciprocal_integral_iff_regularPoints (f : K) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f ↔
      ∀ x : S, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f := by
  rw [lpsOriginalField_reciprocal_integral_iff_noPole N hpos hN f]
  constructor
  · rintro ⟨hi,hc⟩ ⟨x,hx⟩
    cases x with
    | inl y => exact hi y (lpsOriginalInfinityRegular_interior_nonzero N hpos hN y hx)
    | inr c => exact hc c
  · intro h
    exact ⟨fun y hy => h ⟨Sum.inl y,
      lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN y hy⟩,
      fun c => h ⟨Sum.inr c,lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c⟩⟩

end
end QEC.Coding.TannerLiftedProduct
