import QEC.Coding.AlgebraicGeometry.Towers.QuadraticRefinement

/-!
# A literal source root and its quadratic refinement

Any root of the source recursion over a rational-coordinate base generates
the existing degree-sixteen source-step model. Its degree is proved from
the model, not assumed. This reuses the source-step Eisenstein polynomial;
there is no second degree-sixteen field or different construction.
-/

open Polynomial IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K E : Type*} [_root_.Field K] [_root_.Field E]
  [Algebra F256 K] [Algebra K E]

private noncomputable def sourceStepLiteralAdjoinHom
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    SourceStepField P x hx →ₐ[K] K⟮y⟯ := by
  let z : K⟮y⟯ := AdjoinSimple.gen K y
  have hz : z ^ 16 + z = algebraMap K K⟮y⟯ (sourceStepRhs x) := by
    apply Subtype.ext
    exact hy
  have ha0 : sourceStepRhs x ≠ 0 := by
    intro h
    have ho := sourceStepRhs_order P x hx
    simp [h, GlobalPlace.order] at ho
  have haL : algebraMap K K⟮y⟯ (sourceStepRhs x) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K K⟮y⟯).injective.ne ha0
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
    exact haL hz.symm
  have hroot : eval₂ (Algebra.ofId K K⟮y⟯) z⁻¹
      (sourceStepPolynomial P x hx) = 0 := by
    have hc : ((Algebra.ofId K K⟮y⟯ : K →+* K⟮y⟯).comp
        (algebraMap P.valuationRing K)) (sourceStepUniformizer P x hx) =
        (algebraMap K K⟮y⟯ (sourceStepRhs x))⁻¹ := by
      change algebraMap K K⟮y⟯ ((sourceStepUniformizer P x hx : P.valuationRing) : K) = _
      rw [coe_sourceStepUniformizer, map_inv₀]
    rw [sourceStepPolynomial, Polynomial.eval₂_map]
    simp only [sourceStepReciprocalPolynomial, eval₂_add,
      eval₂_X_pow, eval₂_mul, eval₂_C]
    rw [hc]
    change z⁻¹ ^ 16 + (algebraMap K K⟮y⟯ (sourceStepRhs x))⁻¹ * z⁻¹ ^ 15 +
      (algebraMap K K⟮y⟯ (sourceStepRhs x))⁻¹ = 0
    letI : CharP F256 2 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
    letI : CharP K 2 :=
      charP_of_injective_algebraMap (algebraMap F256 K).injective 2
    letI : CharP K⟮y⟯ 2 :=
      charP_of_injective_algebraMap (algebraMap K K⟮y⟯).injective 2
    field_simp [hz0, haL]
    rw [← hz]
    calc
      z ^ 16 + z + z + z ^ 16 = (z ^ 16 + z ^ 16) + (z + z) := by ac_rfl
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
    all_goals simp
  exact AdjoinRoot.liftAlgHom _ (Algebra.ofId K K⟮y⟯) z⁻¹ hroot

private theorem sourceStepLiteralAdjoinHom_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    sourceStepLiteralAdjoinHom P x hx y hy (sourceStepCoordinate P x hx) =
      AdjoinSimple.gen K y := by
  simp only [sourceStepLiteralAdjoinHom, sourceStepCoordinate,
    sourceStepReciprocalRoot, map_inv₀, AdjoinRoot.liftAlgHom_root, inv_inv]

private theorem sourceStepLiteralAdjoinHom_surjective
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    Function.Surjective (sourceStepLiteralAdjoinHom P x hx y hy) := by
  let f := sourceStepLiteralAdjoinHom P x hx y hy
  rintro ⟨z, hz⟩
  induction hz using IntermediateField.adjoin_induction with
  | mem v hv =>
      have h : v = y := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨sourceStepCoordinate P x hx,
        sourceStepLiteralAdjoinHom_apply_coordinate P x hx y hy⟩
  | algebraMap v =>
      refine ⟨algebraMap K (SourceStepField P x hx) v, ?_⟩
      exact f.commutes v
  | add v w _ _ hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      refine ⟨v' + w', ?_⟩
      rw [map_add, hv', hw']
      rfl
  | inv v _ hv =>
      obtain ⟨v', hv'⟩ := hv
      refine ⟨v'⁻¹, ?_⟩
      rw [map_inv₀, hv']
      rfl
  | mul v w _ _ hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      refine ⟨v' * w', ?_⟩
      rw [map_mul, hv', hw']
      rfl

/-- The existing source-step model is the actual root-generated subfield. -/
noncomputable def sourceStepLiteralAdjoinEquiv
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    SourceStepField P x hx ≃ₐ[K] K⟮y⟯ :=
  AlgEquiv.ofBijective (sourceStepLiteralAdjoinHom P x hx y hy)
    ⟨(sourceStepLiteralAdjoinHom P x hx y hy).injective,
      sourceStepLiteralAdjoinHom_surjective P x hx y hy⟩

/-- The degree of the literal basic projection is derived, not an input. -/
theorem sourceStepLiteral_adjoin_finrank
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    Module.finrank K K⟮y⟯ = 16 := by
  rw [← (sourceStepLiteralAdjoinEquiv P x hx y hy).toLinearEquiv.finrank_eq]
  exact sourceStep_finrank P x hx

/-- Four successive quadratic source steps refine this actual projection. -/
noncomputable def sourceStepLiteralQuadraticRefinementEquiv
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    QuadraticArtinSchreierTowerField P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 ≃ₐ[K] K⟮y⟯ :=
  (sourceStepQuadraticRefinementEquiv P x hx).symm.trans
    (sourceStepLiteralAdjoinEquiv P x hx y hy)

theorem sourceStepLiteralQuadraticRefinementEquiv_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    sourceStepLiteralQuadraticRefinementEquiv P x hx y hy
        (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
          (sourceStepRhs_order P x hx) 4) = AdjoinSimple.gen K y := by
  rw [sourceStepLiteralQuadraticRefinementEquiv, AlgEquiv.trans_apply,
    ← sourceStepQuadraticRefinementEquiv_apply_coordinate P x hx,
    AlgEquiv.symm_apply_apply]
  exact sourceStepLiteralAdjoinHom_apply_coordinate P x hx y hy

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
