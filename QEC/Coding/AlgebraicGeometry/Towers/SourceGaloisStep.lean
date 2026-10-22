import QEC.Coding.AlgebraicGeometry.Towers.SourceStep

import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois translations of one source-facing Garcia--Stichtenoth step

The source coordinate satisfies `y^16 + y = x^16 / (x^15 + 1)`.  Translation
of `y` by any element of the concrete sixteen-element Artin--Schreier kernel
preserves this equation.  This file realizes those translations through the
reciprocal-root presentation of `SourceStepField`, proves that they are
distinct involutive automorphisms, and hence proves the actual step Galois.

No place splitting, ramification composition, divisor, genus, or asymptotic
conclusion is packaged here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem sourceTranslation_rhs_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepRhs x ≠ 0 := by
  intro hzero
  have horder := sourceStepRhs_order P x hx
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder

private theorem sourceTranslation_kernel_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (algebraMap F256 (SourceStepField P x hx) (c : F256)) ^ 16 +
        algebraMap F256 (SourceStepField P x hx) (c : F256) = 0 := by
  have hc : (c : F256) ^ 16 + (c : F256) = 0 := by
    have hc' : f256ArtinSchreier (c : F256) = 0 :=
      LinearMap.mem_ker.mp c.property
    simpa only [f256ArtinSchreier_apply] using hc'
  simpa only [map_add, map_pow, map_zero] using
    congrArg (algebraMap F256 (SourceStepField P x hx)) hc

private theorem sourceTranslatedCoordinate_equation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceStepCoordinate P x hx +
          algebraMap F256 (SourceStepField P x hx) (c : F256)) ^ 16 +
        (sourceStepCoordinate P x hx +
          algebraMap F256 (SourceStepField P x hx) (c : F256)) =
      sourceStepEmbedding P x hx (sourceStepRhs x) := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  have hstep := sourceStepCoordinate_equation P x hx
  have hkernel := sourceTranslation_kernel_equation P x hx c
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
  linear_combination hstep + hkernel

private theorem sourceTranslatedCoordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepCoordinate P x hx +
        algebraMap F256 (SourceStepField P x hx) (c : F256) ≠ 0 := by
  intro hzero
  have hequation := sourceTranslatedCoordinate_equation P x hx c
  rw [hzero] at hequation
  simp only [zero_pow (by norm_num : (16 : ℕ) ≠ 0), zero_add] at hequation
  apply (sourceStepEmbedding P x hx).injective.ne
    (sourceTranslation_rhs_ne_zero P x hx)
  simp only [map_zero]
  exact hequation.symm

private noncomputable def sourceTranslatedReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) : SourceStepField P x hx :=
  (sourceStepCoordinate P x hx +
    algebraMap F256 (SourceStepField P x hx) (c : F256))⁻¹

private theorem sourceStepPolynomial_eq_translation_explicit
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepPolynomial P x hx =
      X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 +
        C (sourceStepRhs x)⁻¹ := by
  simp [sourceStepPolynomial, sourceStepReciprocalPolynomial,
    sourceStepUniformizer, coe_reciprocalUniformizer]

private theorem sourceTranslatedReciprocalRoot_isRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    eval₂ (Algebra.ofId K (SourceStepField P x hx))
      (sourceTranslatedReciprocalRoot P x hx c)
      (sourceStepPolynomial P x hx) = 0 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  let a := sourceStepEmbedding P x hx (sourceStepRhs x)
  let y := sourceStepCoordinate P x hx +
    algebraMap F256 (SourceStepField P x hx) (c : F256)
  have ha : a ≠ 0 := by
    have hport := (sourceStepEmbedding P x hx).injective.ne
      (sourceTranslation_rhs_ne_zero P x hx)
    simp only [a, map_zero] at hport ⊢
    exact hport
  have hy : y ≠ 0 := sourceTranslatedCoordinate_ne_zero P x hx c
  have hyAS : y ^ 16 + y = a :=
    sourceTranslatedCoordinate_equation P x hx c
  have htwo : (2 : SourceStepField P x hx) = 0 :=
    CharP.cast_eq_zero (SourceStepField P x hx) 2
  have hexplicit :
      y⁻¹ ^ 16 + a⁻¹ * y⁻¹ ^ 15 + a⁻¹ = 0 := by
    field_simp [ha, hy]
    linear_combination hyAS + a * htwo
  have hpoly := sourceStepPolynomial_eq_translation_explicit P x hx
  calc
    eval₂ (Algebra.ofId K (SourceStepField P x hx))
        (sourceTranslatedReciprocalRoot P x hx c)
        (sourceStepPolynomial P x hx) =
        eval₂ (Algebra.ofId K (SourceStepField P x hx))
          (sourceTranslatedReciprocalRoot P x hx c)
          (X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 +
            C (sourceStepRhs x)⁻¹) :=
      congrArg
        (eval₂ (Algebra.ofId K (SourceStepField P x hx))
          (sourceTranslatedReciprocalRoot P x hx c)) hpoly
    _ = 0 := by
      rw [eval₂_add, eval₂_add, eval₂_X_pow,
        eval₂_mul, eval₂_C, eval₂_X_pow]
      simp only [sourceTranslatedReciprocalRoot, a, y,
        sourceStepEmbedding, map_inv₀] at hexplicit ⊢
      exact hexplicit

private noncomputable def sourceStepTranslationHom
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    SourceStepField P x hx →ₐ[K] SourceStepField P x hx :=
  AdjoinRoot.liftAlgHom (sourceStepPolynomial P x hx)
    (Algebra.ofId K (SourceStepField P x hx))
    (sourceTranslatedReciprocalRoot P x hx c)
    (sourceTranslatedReciprocalRoot_isRoot P x hx c)

@[simp]
private theorem sourceStepTranslationHom_apply_root
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c (sourceStepReciprocalRoot P x hx) =
      sourceTranslatedReciprocalRoot P x hx c := by
  simp only [sourceStepTranslationHom, sourceStepReciprocalRoot,
    AdjoinRoot.liftAlgHom_root]

private theorem sourceStepTranslationHom_fixes_constant
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c
        (algebraMap F256 (SourceStepField P x hx) (c : F256)) =
      algebraMap F256 (SourceStepField P x hx) (c : F256) := by
  rw [IsScalarTower.algebraMap_apply F256 K (SourceStepField P x hx)]
  exact (sourceStepTranslationHom P x hx c).commutes _

private theorem sourceStepTranslationHom_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c (sourceStepCoordinate P x hx) =
      sourceStepCoordinate P x hx +
        algebraMap F256 (SourceStepField P x hx) (c : F256) := by
  rw [sourceStepCoordinate, map_inv₀,
    sourceStepTranslationHom_apply_root]
  simp only [sourceTranslatedReciprocalRoot,
    inv_inv, sourceStepCoordinate]

private theorem sourceStepTranslationHom_apply_translatedReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslationHom P x hx c
        (sourceTranslatedReciprocalRoot P x hx c) =
      sourceStepReciprocalRoot P x hx := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP (SourceStepField P x hx) 2 :=
    charP_of_injective_algebraMap
      (algebraMap K (SourceStepField P x hx)).injective 2
  have hw : sourceStepReciprocalRoot P x hx ≠ 0 :=
    sourceStepReciprocalRoot_ne_zero P x hx
  rw [sourceTranslatedReciprocalRoot, map_inv₀, map_add,
    sourceStepTranslationHom_apply_coordinate,
    sourceStepTranslationHom_fixes_constant,
    add_assoc, CharTwo.add_self_eq_zero, add_zero,
    sourceStepCoordinate]
  exact inv_inv _

private theorem sourceStepTranslationHom_comp_self
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceStepTranslationHom P x hx c).comp
        (sourceStepTranslationHom P x hx c) =
      AlgHom.id K (SourceStepField P x hx) := by
  apply AdjoinRoot.algHom_ext
  change sourceStepTranslationHom P x hx c
      (sourceStepTranslationHom P x hx c
        (sourceStepReciprocalRoot P x hx)) =
    sourceStepReciprocalRoot P x hx
  rw [sourceStepTranslationHom_apply_root,
    sourceStepTranslationHom_apply_translatedReciprocalRoot]

/-- Translation of the source coordinate by one element of the concrete
sixteen-element Artin--Schreier kernel. -/
noncomputable def sourceStepTranslation
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx :=
  AlgEquiv.ofAlgHom (sourceStepTranslationHom P x hx c)
    (sourceStepTranslationHom P x hx c)
    (sourceStepTranslationHom_comp_self P x hx c)
    (sourceStepTranslationHom_comp_self P x hx c)

/-- The translation has the intended action on the literal source
coordinate. -/
theorem sourceStepTranslation_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceStepTranslation P x hx c (sourceStepCoordinate P x hx) =
      sourceStepCoordinate P x hx +
        algebraMap F256 (SourceStepField P x hx) (c : F256) :=
  sourceStepTranslationHom_apply_coordinate P x hx c

/-- Every source-coordinate translation is involutive in characteristic
two. -/
theorem sourceStepTranslation_involutive
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier)
    (y : SourceStepField P x hx) :
    sourceStepTranslation P x hx c (sourceStepTranslation P x hx c y) = y := by
  have hcomp := congrArg
    (fun f : SourceStepField P x hx →ₐ[K] SourceStepField P x hx => f y)
    (sourceStepTranslationHom_comp_self P x hx c)
  exact hcomp

/-- Distinct kernel constants induce distinct source-step translations. -/
theorem sourceStepTranslation_injective
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Function.Injective (sourceStepTranslation P x hx) := by
  intro c d hcd
  have hcoordinate := congrArg
    (fun e : SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx =>
      e (sourceStepCoordinate P x hx)) hcd
  change sourceStepTranslation P x hx c (sourceStepCoordinate P x hx) =
    sourceStepTranslation P x hx d (sourceStepCoordinate P x hx) at hcoordinate
  rw [sourceStepTranslation_apply_coordinate,
    sourceStepTranslation_apply_coordinate] at hcoordinate
  have hconstants :
      algebraMap F256 (SourceStepField P x hx) (c : F256) =
        algebraMap F256 (SourceStepField P x hx) (d : F256) :=
    add_left_cancel hcoordinate
  apply Subtype.ext
  exact (algebraMap F256 (SourceStepField P x hx)).injective hconstants

/-- One source recursion step has exactly sixteen lower-field algebra
automorphisms. -/
theorem sourceStepField_algEquiv_card
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Nat.card (SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx) = 16 := by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx) ≤
          Module.finrank K (SourceStepField P x hx) := AlgEquiv.card_le
      _ = 16 := sourceStep_finrank P x hx
  · calc
      16 = Nat.card (LinearMap.ker f256ArtinSchreier) := by
        rw [Nat.card_eq_fintype_card, f256ArtinSchreier_ker_card]
      _ ≤ Nat.card
          (SourceStepField P x hx ≃ₐ[K] SourceStepField P x hx) :=
        Nat.card_le_card_of_injective (sourceStepTranslation P x hx)
          (sourceStepTranslation_injective P x hx)

/-- The concrete degree-sixteen source recursion step is Galois over its
preceding field. -/
noncomputable instance sourceStepField_isGalois
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsGalois K (SourceStepField P x hx) := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [sourceStepField_algEquiv_card, sourceStep_finrank]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
