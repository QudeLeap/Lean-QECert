import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import QEC.Coding.AlgebraicGeometry.Adeles.CompletedGlobalAdele

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Completed global ideles

This file constructs the standard ideles of a global function field as the
restricted product of the multiplicative groups of its completed local fields
with respect to the local unit groups.  It also constructs the diagonal copy
of the global units, the continuous local-component maps, and the open subgroup
of ideles integral away from an arbitrary finite set of places.

The construction is equivalent, as a group, to the units of the completed
global adele ring.  No local compactness, Haar measure, automorphic
decomposition, or spectral conclusion is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Filter
open scoped RestrictedProduct WithZero

noncomputable section

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

/-- The unit group of the completed valuation ring at `P`, viewed as a
subgroup of the multiplicative group of the completed local field. -/
abbrev LocalUnitGroup (P : GlobalPlace k F) : Subgroup P.LocalCompletionˣ :=
  (Submonoid.ofClass P.LocalIntegerRing).units

/-- Every local unit group is open in the multiplicative local field. -/
theorem isOpen_localUnitGroup (P : GlobalPlace k F) :
    IsOpen (P.LocalUnitGroup : Set P.LocalCompletionˣ) := by
  apply Submonoid.isOpen_units
  exact Valued.isOpen_valuationSubring P.LocalCompletion

instance localUnitGroupOpenFact :
    Fact (∀ P : GlobalPlace k F,
      IsOpen (P.LocalUnitGroup : Set P.LocalCompletionˣ)) :=
  ⟨isOpen_localUnitGroup⟩

/-- The completed global idele group, in its standard restricted-product
topology. -/
abbrev CompletedGlobalIdele : Type _ :=
  Πʳ P : GlobalPlace k F, [P.LocalCompletionˣ, P.LocalUnitGroup]

/-- The canonical group embedding of global units into the units of one local
completion. -/
def completionUnitsEmbedding (P : GlobalPlace k F) : Fˣ →* P.LocalCompletionˣ :=
  Units.map P.completionEmbedding.toMonoidHom

@[simp]
theorem completionUnitsEmbedding_apply (P : GlobalPlace k F) (u : Fˣ) :
    (P.completionUnitsEmbedding u : P.LocalCompletion) =
      P.completionEmbedding (u : F) :=
  rfl

section Diagonal

variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

/-- The diagonal embedding of the global multiplicative group into the ideles.
Both a unit and its inverse are integral at all but finitely many places. -/
def completedIdeleDiagonal : Fˣ →* CompletedGlobalIdele (k := k) (F := F) where
  toFun u := ⟨fun P ↦ P.completionUnitsEmbedding u, by
    filter_upwards
      [eventually_mem_valuationRing (k := k) (F := F) (u : F),
       eventually_mem_valuationRing (k := k) (F := F) ((u⁻¹ : Fˣ) : F)]
      with P hu huInv
    change P.completionUnitsEmbedding u ∈
      (Submonoid.ofClass P.LocalIntegerRing).units
    rw [Submonoid.mem_units_iff]
    constructor
    · exact (completionEmbedding_mem_localIntegerRing_iff P (u : F)).mpr hu
    · exact (completionEmbedding_mem_localIntegerRing_iff P
          ((u⁻¹ : Fˣ) : F)).mpr huInv⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro P
    exact map_one P.completionUnitsEmbedding
  map_mul' u v := by
    apply RestrictedProduct.ext
    intro P
    exact map_mul P.completionUnitsEmbedding u v

@[simp]
theorem completedIdeleDiagonal_apply (u : Fˣ) (P : GlobalPlace k F) :
    completedIdeleDiagonal (k := k) (F := F) u P =
      P.completionUnitsEmbedding u :=
  rfl

end Diagonal

/-- Evaluation at a place as a continuous homomorphism of multiplicative
groups. -/
def completedIdeleAt (P : GlobalPlace k F) :
    CompletedGlobalIdele (k := k) (F := F) →ₜ* P.LocalCompletionˣ where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := RestrictedProduct.continuous_eval P

@[simp]
theorem completedIdeleAt_apply (P : GlobalPlace k F)
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    completedIdeleAt (k := k) (F := F) P x = x P :=
  rfl

/-- The standard ideles are algebraically the units of the completed global
adele ring. -/
def completedAdeleUnitsEquivIdele :
    (CompletedGlobalAdele (k := k) (F := F))ˣ ≃*
      CompletedGlobalIdele (k := k) (F := F) :=
  RestrictedProduct.unitsEquiv (fun P : GlobalPlace k F ↦ P.LocalCompletion)

@[simp]
theorem completedAdeleUnitsEquivIdele_apply
    (x : (CompletedGlobalAdele (k := k) (F := F))ˣ)
    (P : GlobalPlace k F) :
    completedAdeleUnitsEquivIdele (k := k) (F := F) x P = x.1 P :=
  rfl

section DiagonalCompatibility

variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

/-- The idelic diagonal is exactly the image of the adelic diagonal on units;
the adele and idele constructions therefore share one global embedding. -/
theorem completedAdeleUnitsEquivIdele_map_completedDiagonal (u : Fˣ) :
    completedAdeleUnitsEquivIdele (k := k) (F := F)
        (Units.map (completedDiagonal (k := k) (F := F)).toMonoidHom u) =
      completedIdeleDiagonal (k := k) (F := F) u := by
  apply RestrictedProduct.ext
  intro P
  rfl

/-- Local evaluation of the global idele diagonal is the corresponding local
completion embedding. -/
@[simp]
theorem completedIdeleAt_diagonal (u : Fˣ) (P : GlobalPlace k F) :
    completedIdeleAt (k := k) (F := F) P
        (completedIdeleDiagonal (k := k) (F := F) u) =
      P.completionUnitsEmbedding u :=
  rfl

end DiagonalCompatibility

/-- The finite set of places where an idele is not a local unit. -/
def ideleNonintegralPlaces
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    Finset (GlobalPlace k F) :=
  (Filter.eventually_cofinite.mp x.property).toFinset

@[simp]
theorem mem_ideleNonintegralPlaces_iff
    (x : CompletedGlobalIdele (k := k) (F := F))
    (P : GlobalPlace k F) :
    P ∈ ideleNonintegralPlaces x ↔ x P ∉ P.LocalUnitGroup := by
  classical
  change P ∈ (Filter.eventually_cofinite.mp x.property).toFinset ↔
    x.1 P ∉ P.LocalUnitGroup
  rw [Set.Finite.mem_toFinset]
  change (x.1 P ∉ P.LocalUnitGroup) ↔ (x.1 P ∉ P.LocalUnitGroup)
  rfl

/-- Ideles integral outside the finite set `S`.  Components at places in `S`
are unrestricted. -/
def completedIntegralIdeleSubgroup
    (S : Finset (GlobalPlace k F)) :
    Subgroup (CompletedGlobalIdele (k := k) (F := F)) where
  carrier := {x | ∀ P, P ∉ S → x P ∈ P.LocalUnitGroup}
  one_mem' := fun _P _ ↦ one_mem _
  mul_mem' hx hy P hP := mul_mem (hx P hP) (hy P hP)
  inv_mem' hx P hP := inv_mem (hx P hP)

theorem mem_completedIntegralIdeleSubgroup_iff
    (S : Finset (GlobalPlace k F))
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedIntegralIdeleSubgroup S ↔
      ∀ P, P ∉ S → x P ∈ P.LocalUnitGroup :=
  Iff.rfl

/-- Allowing more exceptional places weakens the integrality condition. -/
theorem completedIntegralIdeleSubgroup_mono
    {S T : Finset (GlobalPlace k F)} (hST : S ⊆ T) :
    completedIntegralIdeleSubgroup (k := k) (F := F) S ≤
      completedIntegralIdeleSubgroup (k := k) (F := F) T := by
  intro x hx P hPT
  exact hx P fun hPS ↦ hPT (hST hPS)

/-- An idele is integral away from `S` exactly when all of its nonintegral
places lie in `S`. -/
theorem mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset
    (S : Finset (GlobalPlace k F))
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedIntegralIdeleSubgroup S ↔
      ideleNonintegralPlaces x ⊆ S := by
  classical
  rw [mem_completedIntegralIdeleSubgroup_iff]
  constructor
  · intro hx P hP
    by_contra hPS
    exact (mem_ideleNonintegralPlaces_iff x P).mp hP (hx P hPS)
  · intro hx P hPS
    by_contra hPunit
    have hP : P ∈ ideleNonintegralPlaces x :=
      (mem_ideleNonintegralPlaces_iff x P).mpr hPunit
    exact hPS (hx hP)

/-- The subgroup of ideles integral at every place. -/
abbrev completedEverywhereIntegralIdeleSubgroup :
    Subgroup (CompletedGlobalIdele (k := k) (F := F)) :=
  completedIntegralIdeleSubgroup (k := k) (F := F) ∅

/-- Everywhere integrality is equivalent to having no nonintegral places. -/
theorem mem_completedEverywhereIntegralIdeleSubgroup_iff
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedEverywhereIntegralIdeleSubgroup ↔
      ideleNonintegralPlaces x = ∅ := by
  rw [show x ∈ completedEverywhereIntegralIdeleSubgroup ↔
      ideleNonintegralPlaces x ⊆ ∅ from
    mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset ∅ x]
  exact Finset.subset_empty

/-- Requiring integrality away from a finite set defines an open idele
subgroup. -/
theorem isOpen_completedIntegralIdeleSubgroup
    (S : Finset (GlobalPlace k F)) :
    IsOpen (completedIntegralIdeleSubgroup (k := k) (F := F) S :
      Set (CompletedGlobalIdele (k := k) (F := F))) := by
  exact RestrictedProduct.isOpen_forall_imp_mem
    (fun P ↦ isOpen_localUnitGroup P)

/-- In particular, the everywhere-integral idele subgroup is open. -/
theorem isOpen_completedEverywhereIntegralIdeleSubgroup :
    IsOpen (completedEverywhereIntegralIdeleSubgroup (k := k) (F := F) :
      Set (CompletedGlobalIdele (k := k) (F := F))) :=
  isOpen_completedIntegralIdeleSubgroup ∅

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
