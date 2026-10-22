import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The differential module sheaf of a scheme

A coefficient morphism into global functions determines the pointwise Kähler
presheaf. Its module sheafification carries a universal derivation: every actual
coefficient-relative derivation into a module sheaf factors uniquely through it.
This supplies the genuine sheaf used by the original normalization in the PK22 proof.
The affine comparison is proved separately in `AffineDifferentials`.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (X : Scheme.{u}) (k : CommRingCat.{u})

/-- Literal global constants restricted to each open of the actual scheme. -/
def schemeConstantPresheafMap (c : k ⟶ Γ(X, ⊤)) :
    (Functor.const X.Opensᵒᵖ).obj k ⟶ X.presheaf where
  app U := c ≫ X.presheaf.map (homOfLE le_top).op
  naturality {U V} f := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← X.presheaf.map_comp]
    congr 1

/-- The actual pointwise Kähler presheaf, before sheafification. -/
def schemeDifferentialPresheaf (c : k ⟶ Γ(X, ⊤)) : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (schemeConstantPresheafMap X k c)

/-- The associated genuine O_X module sheaf. -/
def schemeDifferentialSheaf (c : k ⟶ Γ(X, ⊤)) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (schemeDifferentialPresheaf X k c)

/-- The pointwise universal derivation identifies module maps and actual derivations. -/
def schemeDifferentialPresheafHomEquiv (c : k ⟶ Γ(X, ⊤))
    (M : X.PresheafOfModules) :
    (schemeDifferentialPresheaf X k c ⟶ M) ≃
      M.Derivation' (schemeConstantPresheafMap X k c) where
  toFun f := (PresheafOfModules.DifferentialsConstruction.derivation'
    (schemeConstantPresheafMap X k c)).postcomp f
  invFun d := (PresheafOfModules.DifferentialsConstruction.isUniversal'
    (schemeConstantPresheafMap X k c)).desc d
  left_inv f := by
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantPresheafMap X k c)).postcomp_injective
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantPresheafMap X k c)).fac _
  right_inv d := by
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantPresheafMap X k c)).fac d

/-- Maps from the actual differential sheaf are exactly derivations into a module sheaf. -/
def schemeDifferentialSheafHomEquiv (c : k ⟶ Γ(X, ⊤))
    (M : X.Modules) :
    (schemeDifferentialSheaf X k c ⟶ M) ≃
      ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
        (schemeConstantPresheafMap X k c) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (schemeDifferentialPresheafHomEquiv X k c
      ((Scheme.Modules.toPresheafOfModules X).obj M))

/-- Every actual derivation into a sheaf has a unique sheaf-module factorization. -/
lemma schemeDifferentialSheaf_existsUnique (c : k ⟶ Γ(X, ⊤))
    (M : X.Modules)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap X k c)) :
    ∃! f : schemeDifferentialSheaf X k c ⟶ M,
      schemeDifferentialSheafHomEquiv X k c M f = d := by
  refine ⟨(schemeDifferentialSheafHomEquiv X k c M).symm d, ?_, ?_⟩
  · exact (schemeDifferentialSheafHomEquiv X k c M).apply_symm_apply d
  · intro f hf
    apply (schemeDifferentialSheafHomEquiv X k c M).injective
    rw [hf, Equiv.apply_symm_apply]
end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (X : Scheme.{u}) (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "Omega" => schemeDifferentialSheaf X k c
local notation "constants" => schemeConstantPresheafMap X k c

def schemeDifferentialSheafDerivation :
    ((Scheme.Modules.toPresheafOfModules X).obj Omega).Derivation' constants :=
  schemeDifferentialSheafHomEquiv X k c Omega (𝟙 Omega)

lemma schemeDifferentialSheafDerivation_postcomp (M : X.Modules) (f : Omega ⟶ M) :
    (schemeDifferentialSheafDerivation X k c).postcomp
      ((Scheme.Modules.toPresheafOfModules X).map f) =
    schemeDifferentialSheafHomEquiv X k c M f := by
  ext U a
  rfl

lemma schemeDifferentialSheafDerivation_existsUnique (M : X.Modules)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation' constants) :
    ∃! f : Omega ⟶ M,
      (schemeDifferentialSheafDerivation X k c).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map f) = d := by
  simpa only [schemeDifferentialSheafDerivation_postcomp] using
    schemeDifferentialSheaf_existsUnique X k c M d
end
end QEC.Coding.AlgebraicGeometry
