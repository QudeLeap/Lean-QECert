import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic

/-!
# Kähler differentials under a coefficient-compatible ring isomorphism

The actual pointwise Kähler map induced by a ring isomorphism is bijective.
Both inverse laws follow from universal generator extensionality and the
proved inverse ring maps, with scalar restriction accounted for explicitly.
-/
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory
noncomputable section
universe u
variable {k B B' : CommRingCat.{u}} (phi : k ⟶ B) (psi : k ⟶ B')
  (e : B ≅ B') (h : phi ≫ e.hom = psi)

include h in
lemma kaehlerRingIso_inverse_square : psi ≫ e.inv = phi := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

def kaehlerRingIso_forward : CommRingCat.KaehlerDifferential phi ⟶
    (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential psi) :=
  CommRingCat.KaehlerDifferential.map (g := 𝟙 k) (g' := e.hom)
    ((Category.id_comp psi).trans h.symm)

def kaehlerRingIso_backward : CommRingCat.KaehlerDifferential psi ⟶
    (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential phi) :=
  CommRingCat.KaehlerDifferential.map (g := 𝟙 k) (g' := e.inv)
    ((Category.id_comp phi).trans (kaehlerRingIso_inverse_square phi psi e h).symm)

lemma kaehlerRingIso_hom_inv_ring : RingHom.id B = e.inv.hom.comp e.hom.hom := by
  ext b
  exact (congrArg (fun t => t b) e.hom_inv_id).symm

lemma kaehlerRingIso_inv_hom_ring : RingHom.id B' = e.hom.hom.comp e.inv.hom := by
  ext b
  exact (congrArg (fun t => t b) e.inv_hom_id).symm

lemma kaehlerRingIso_left_inverse : Function.LeftInverse
    (kaehlerRingIso_backward phi psi e h) (kaehlerRingIso_forward phi psi e h) := by
  let alpha := kaehlerRingIso_forward phi psi e h ≫
    (ModuleCat.restrictScalars e.hom.hom).map (kaehlerRingIso_backward phi psi e h) ≫
    (ModuleCat.restrictScalarsComp'App e.hom.hom e.inv.hom (RingHom.id B)
      (kaehlerRingIso_hom_inv_ring e) (CommRingCat.KaehlerDifferential phi)).inv ≫
    (ModuleCat.restrictScalarsId B).hom.app (CommRingCat.KaehlerDifferential phi)
  have heq : alpha = 𝟙 (CommRingCat.KaehlerDifferential phi) := by
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    change kaehlerRingIso_backward phi psi e h
      (kaehlerRingIso_forward phi psi e h (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d b
    simp only [kaehlerRingIso_forward, kaehlerRingIso_backward,
      CommRingCat.KaehlerDifferential.map_d]
    have hb : e.inv (e.hom b) = b := congrArg (fun t : B ⟶ B => t b) e.hom_inv_id
    exact congrArg (CommRingCat.KaehlerDifferential.d (f := phi)) hb
  intro x
  exact congrArg (fun t => t x) heq

lemma kaehlerRingIso_right_inverse : Function.RightInverse
    (kaehlerRingIso_backward phi psi e h) (kaehlerRingIso_forward phi psi e h) := by
  let alpha := kaehlerRingIso_backward phi psi e h ≫
    (ModuleCat.restrictScalars e.inv.hom).map (kaehlerRingIso_forward phi psi e h) ≫
    (ModuleCat.restrictScalarsComp'App e.inv.hom e.hom.hom (RingHom.id B')
      (kaehlerRingIso_inv_hom_ring e) (CommRingCat.KaehlerDifferential psi)).inv ≫
    (ModuleCat.restrictScalarsId B').hom.app (CommRingCat.KaehlerDifferential psi)
  have heq : alpha = 𝟙 (CommRingCat.KaehlerDifferential psi) := by
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    change kaehlerRingIso_forward phi psi e h
      (kaehlerRingIso_backward phi psi e h (CommRingCat.KaehlerDifferential.d b)) =
        CommRingCat.KaehlerDifferential.d b
    simp only [kaehlerRingIso_forward, kaehlerRingIso_backward,
      CommRingCat.KaehlerDifferential.map_d]
    have hb : e.hom (e.inv b) = b := congrArg (fun t : B' ⟶ B' => t b) e.inv_hom_id
    exact congrArg (CommRingCat.KaehlerDifferential.d (f := psi)) hb
  intro x
  exact congrArg (fun t => t x) heq

lemma kaehlerRingIso_forward_bijective : Function.Bijective
    (kaehlerRingIso_forward phi psi e h) :=
  ⟨(kaehlerRingIso_left_inverse phi psi e h).injective,
    (kaehlerRingIso_right_inverse phi psi e h).surjective⟩
end
end QEC.Coding.AlgebraicGeometry
