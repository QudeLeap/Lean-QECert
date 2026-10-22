import QEC.Distillation.MultiplicativeQuditProtocol.Phase
import QEC.Distillation.Core.TransversalGate
/-!
# Coordinatewise physical CCZ for Ngu24

This compile-free #725 layer composes the concrete tagged local CCZ transports
over every within-copy coordinate and records their exact disjoint triple
supports.  It stops before any code encoding or logical-action statement.
-/

noncomputable section

namespace QEC.Distillation

open Semantics
open scoped BigOperators

universe u

variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- Canonically enumerate the finite within-copy sites. -/
noncomputable def taggedCczSiteEquivFin (ι : Type u) [Fintype ι] :
    Fin (Fintype.card ι) ≃ ι :=
  (Fintype.equivFin ι).symm

/-- One coordinate support is literally the three tags above one site. -/
theorem coordinateSupport_eq_taggedTriple [Fintype ι] [DecidableEq ι]
    (site : ι) :
    coordinateSupport site =
      {(ThreeCopyTag.first, site), (ThreeCopyTag.second, site),
        (ThreeCopyTag.third, site)} := by
  ext coordinate
  rcases coordinate with ⟨tag, coordinateSite⟩
  cases tag <;> simp [coordinateSupport]

omit [Fintype F] in
/-- The tagged local phase depends only on its declared three-coordinate support. -/
theorem taggedCczAmplitude_eq_of_agree_on_coordinateSupport
    [Fintype ι] [DecidableEq ι] (site : ι)
    (label label' : TaggedThreeCopyRegisterLabel F ι)
    (h : ∀ coordinate ∈ coordinateSupport site,
      label coordinate = label' coordinate) :
    taggedCczAmplitude site label = taggedCczAmplitude site label' := by
  simp only [taggedCczAmplitude_eq_local]
  rw [h (ThreeCopyTag.first, site)
        (taggedCoordinate_mem_coordinateSupport ThreeCopyTag.first site)]
  rw [h (ThreeCopyTag.second, site)
        (taggedCoordinate_mem_coordinateSupport ThreeCopyTag.second site)]
  rw [h (ThreeCopyTag.third, site)
        (taggedCoordinate_mem_coordinateSupport ThreeCopyTag.third site)]

/-- Tagged local CCZ transports commute because both are concrete diagonal maps. -/
theorem taggedCczTransport_commute [Fintype ι] [DecidableEq ι]
    (first second : ι) (psi : TaggedThreeCopyRegister F ι) :
    taggedCczTransport first (taggedCczTransport second psi) =
      taggedCczTransport second (taggedCczTransport first psi) := by
  ext label
  simp only [taggedCczTransport_apply]
  ring

/-- The physical coordinatewise product in the canonical finite-site order. -/
noncomputable def taggedCczPhysicalTransport [Fintype ι] [DecidableEq ι] :
    UnitaryTransport (TaggedThreeCopyRegister F ι) (TaggedThreeCopyRegister F ι) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card ι) =>
    taggedCczTransport (taggedCczSiteEquivFin ι j)

private theorem composeTaggedCczTransports_apply [Fintype ι] [DecidableEq ι]
    (sites : List ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    UnitaryTransport.composeList (sites.map taggedCczTransport) psi label =
      (sites.map fun site => taggedCczAmplitude site label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons site sites ih =>
      change UnitaryTransport.composeList (sites.map taggedCczTransport)
          (taggedCczTransport site psi) label = _
      rw [ih]
      simp only [taggedCczTransport_apply, List.map_cons, List.prod_cons]
      ring

/-- The physical product acts by the product of its concrete local phases. -/
theorem taggedCczPhysicalTransport_apply [Fintype ι] [DecidableEq ι]
    (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczPhysicalTransport psi label =
      (∏ site : ι, taggedCczAmplitude site label) * psi label := by
  rw [taggedCczPhysicalTransport, UnitaryTransport.composeFamily]
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card ι) =>
        taggedCczTransport (taggedCczSiteEquivFin ι j)) =
        (List.ofFn (taggedCczSiteEquivFin ι)).map (taggedCczTransport (F := F)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, composeTaggedCczTransports_apply]
  rw [List.map_ofFn, Fin.prod_ofFn]
  congr 1
  exact Fintype.prod_equiv (taggedCczSiteEquivFin ι) _ _ (fun _ => rfl)

/-- The physical product has the coordinatewise phase action on every tagged basis ket. -/
theorem taggedCczPhysicalTransport_apply_basis [Fintype ι] [DecidableEq ι]
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczPhysicalTransport
        (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label) =
      (∏ site : ι, taggedCczAmplitude site label) •
        EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F ι) Complex label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [taggedCczPhysicalTransport_apply, EuclideanSpace.basisFun_apply]
  · simp [taggedCczPhysicalTransport_apply, EuclideanSpace.basisFun_apply, htarget]

/-- The only permitted local factor is the concrete CCZ on one exact tagged triple. -/
inductive TaggedCczLocalGate [Fintype ι] [DecidableEq ι] :
    Finset (TaggedThreeCopyCoordinate ι) → Type u
  | at (site : ι) : TaggedCczLocalGate (coordinateSupport site)

/-- The concrete support-indexed model for tagged local CCZ factors. -/
noncomputable def taggedCczPhysicalGateModel [Fintype ι] [DecidableEq ι] :
    FinitePhysicalGateModel (TaggedThreeCopyCoordinate ι)
      (TaggedThreeCopyRegister F ι) where
  LocalGate := TaggedCczLocalGate
  realize gate := match gate with
    | .at site => taggedCczTransport site

/-- The physical coordinatewise transport factors over pairwise-disjoint tagged triples. -/
noncomputable def taggedCczPhysicalFactorization [Fintype ι] [DecidableEq ι] :
    PhysicalGateFactorization (taggedCczPhysicalGateModel (F := F) (ι := ι))
      (taggedCczPhysicalTransport (F := F) (ι := ι)) where
  factorCount := Fintype.card ι
  support j := coordinateSupport (taggedCczSiteEquivFin ι j)
  factor j := .at (taggedCczSiteEquivFin ι j)
  pairwise_disjoint := by
    intro i j hij
    exact coordinateSupport_disjoint
      ((taggedCczSiteEquivFin ι).injective.ne hij)
  realizes := rfl

end QEC.Distillation
