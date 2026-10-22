import QEC.Distillation.MultiplicativeQuditProtocol.BinaryTriples
import QEC.Distillation.MultiplicativeQuditProtocol.CubicPhase

/-!
# The literal product of binary CCZ gates on inverse-permuted triples

Each factor is the sign-diagonal CCZ on the three vertices prescribed by
[Ngu24, Eq. (mfe-transversal)]. Only the actual selected MFE coordinates
occur in the finite product. Their previously proved disjoint supports are
the supports of these very operators.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding Semantics
open scoped BigOperators

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The binary cubic monomial on the three actual inverse-permuted vertices. -/
def binaryTripleExponent (x : J × Fin 512)
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) : ZMod 2 :=
  label (binaryTripleVertex J x .first) * label (binaryTripleVertex J x .second) *
    label (binaryTripleVertex J x .third)

def binaryTripleAmplitude (x : J × Fin 512)
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) : Complex :=
  PauliSymplectic.binaryPhaseScalar (binaryTripleExponent x label)

private theorem binarySign_square (p : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar p * PauliSymplectic.binaryPhaseScalar p = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hp : p + p = 0 := by fin_cases p <;> decide
  rw [hp, PauliSymplectic.binaryPhaseScalar_zero]

/-- The actual local CCZ, not a supplied action on a chosen code carrier. -/
def binaryTripleCCZ (x : J × Fin 512) :
    UnitaryTransport (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
      (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512)) where
  toLinearEquiv := KT19PrimeQuditCSS.diagonalLinearEquiv
    (binaryTripleAmplitude x) (binaryTripleAmplitude x)
    (fun _ => binarySign_square _) (fun _ => binarySign_square _)
  map_inner := KT19PrimeQuditCSS.diagonalOperator_map_inner _ (fun label => by
    change PauliSymplectic.binaryPhaseScalar _ *
      star (PauliSymplectic.binaryPhaseScalar _) = 1
    rw [PauliSymplectic.binaryPhaseScalar_star]
    exact binarySign_square _)

@[simp] theorem binaryTripleCCZ_apply (x : J × Fin 512)
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryTripleCCZ x psi label = binaryTripleAmplitude x label * psi label := rfl

omit [Fintype J] [DecidableEq J] in
/-- The local phase depends only on the three coordinates in its declared support. -/
theorem binaryTripleAmplitude_eq_of_agree_on_support (x : J × Fin 512)
    (a b : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512))
    (h : ∀ v ∈ binaryTripleSupport J x, a v = b v) :
    binaryTripleAmplitude x a = binaryTripleAmplitude x b := by
  have hm (tag : ThreeCopyTag) : binaryTripleVertex J x tag ∈ binaryTripleSupport J x :=
    Finset.mem_map.mpr ⟨tag, Finset.mem_univ _, rfl⟩
  unfold binaryTripleAmplitude binaryTripleExponent
  rw [h _ (hm .first), h _ (hm .second), h _ (hm .third)]

/-- Canonical finite enumeration of the actual selected first-block vertices. -/
def binarySelectedSiteEquivFin (J : Type) [Fintype J] :
    Fin (Fintype.card {x // x ∈ binarySelectedSites J}) ≃ {x // x ∈ binarySelectedSites J} :=
  taggedCczSiteEquivFin _

/-- The physical gate is literally the finite composition of the selected CCZs. -/
def binaryPhysicalCCZ :
    UnitaryTransport (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
      (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512)) :=
  UnitaryTransport.composeFamily fun j =>
    binaryTripleCCZ (binarySelectedSiteEquivFin J j).val

private theorem composeBinaryTriples_apply (sites : List (J × Fin 512))
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    UnitaryTransport.composeList (sites.map binaryTripleCCZ) psi label =
      (sites.map fun x => binaryTripleAmplitude x label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons x xs ih =>
    change UnitaryTransport.composeList (xs.map binaryTripleCCZ)
      (binaryTripleCCZ x psi) label = _
    rw [ih]
    simp only [binaryTripleCCZ_apply, List.map_cons, List.prod_cons]
    ring

/-- The total binary cubic exponent, with no unselected coordinates added. -/
def binarySelectedExponent
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) : ZMod 2 :=
  ∑ x ∈ binarySelectedSites J, binaryTripleExponent x label

theorem binaryPhysicalCCZ_apply
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryPhysicalCCZ psi label =
      PauliSymplectic.binaryPhaseScalar (binarySelectedExponent label) * psi label := by
  unfold binaryPhysicalCCZ UnitaryTransport.composeFamily
  have hlist : List.ofFn (fun j => binaryTripleCCZ (binarySelectedSiteEquivFin J j).val) =
      (List.ofFn (fun j => (binarySelectedSiteEquivFin J j).val)).map binaryTripleCCZ := by
    rw [List.map_ofFn]
    rfl
  rw [hlist, composeBinaryTriples_apply, List.map_ofFn, Fin.prod_ofFn]
  congr 1
  rw [binarySelectedExponent, PauliSymplectic.binaryPhaseScalar_sum]
  calc
    _ = ∏ x : {x // x ∈ binarySelectedSites J}, binaryTripleAmplitude x.val label :=
      Fintype.prod_equiv (binarySelectedSiteEquivFin J) _ _ (fun _ => rfl)
    _ = ∏ x ∈ binarySelectedSites J, PauliSymplectic.binaryPhaseScalar
        (binaryTripleExponent x label) := by
      exact (Finset.prod_subtype (binarySelectedSites J) (fun _ => Iff.rfl)
        (fun x => binaryTripleAmplitude x label)).symm

theorem binaryPhysicalCCZ_apply_basis
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryPhysicalCCZ (registerBasisKet label) =
      PauliSymplectic.binaryPhaseScalar (binarySelectedExponent label) • registerBasisKet label := by
  ext target
  by_cases h : target = label
  · subst target
    simp [binaryPhysicalCCZ_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [binaryPhysicalCCZ_apply, registerBasisKet, EuclideanSpace.basisFun_apply, h]

/-- The permitted local factor is precisely the CCZ on this inverse-permuted triple. -/
inductive BinaryTripleLocalGate : Finset (TaggedThreeCopyCoordinate (J × Fin 512)) → Type
  | at (x : J × Fin 512) : BinaryTripleLocalGate (binaryTripleSupport J x)

def binaryPhysicalGateModel :
    FinitePhysicalGateModel (TaggedThreeCopyCoordinate (J × Fin 512))
      (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512)) where
  LocalGate := BinaryTripleLocalGate
  realize gate := match gate with
    | .at x => binaryTripleCCZ x

/-- The actual finite product has exactly the already certified disjoint triple supports. -/
def binaryPhysicalFactorization : PhysicalGateFactorization
    (binaryPhysicalGateModel (J := J)) binaryPhysicalCCZ where
  factorCount := Fintype.card {x // x ∈ binarySelectedSites J}
  support j := binaryTripleSupport J (binarySelectedSiteEquivFin J j).val
  factor j := .at (binarySelectedSiteEquivFin J j).val
  pairwise_disjoint := by
    intro a b hab
    apply binaryTripleSupport_disjoint
    intro heq
    exact hab ((binarySelectedSiteEquivFin J).injective (Subtype.ext heq))
  realizes := rfl

end QEC.Distillation.Ngu24Binary
