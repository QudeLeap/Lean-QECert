import QEC.Coding.AlgebraicGeometry.Towers.QuadraticTower
import QEC.Coding.AlgebraicGeometry.Towers.SourceStep

/-!
# Identifying the four quadratic stages with one source step

The four recursively constructed quadratic Artin--Schreier coordinates are
combined symbolically in characteristic two.  The terminal coordinate is
proved to satisfy `Y^16 + Y = a`.  For the actual Garcia--Stichtenoth source
right-hand side this gives a root of the existing reciprocal degree-sixteen
polynomial, hence an algebra equivalence between the source-step field and the
four-stage refinement.

The equivalence and its action on the distinguished coordinate are derived;
neither is stored as input.  No compositum, normal-closure, divisor, genus, or
asymptotic conclusion is made here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

universe u

variable {K : Type u} [Field K] [Algebra F256 K]

/-- Four quadratic Artin--Schreier equations compose to the literal
degree-sixteen equation. -/
theorem quadraticArtinSchreierTower_four_equation
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierTowerCoordinate P a ha 4 ^ 16 +
        quadraticArtinSchreierTowerCoordinate P a ha 4 =
      algebraMap K (QuadraticArtinSchreierTowerField P a ha 4) a := by
  let F₀ := QuadraticArtinSchreierTowerField P a ha 0
  let F₁ := QuadraticArtinSchreierTowerField P a ha 1
  let F₂ := QuadraticArtinSchreierTowerField P a ha 2
  let F₃ := QuadraticArtinSchreierTowerField P a ha 3
  let F₄ := QuadraticArtinSchreierTowerField P a ha 4
  let e₀ : F₀ →ₐ[F256] F₁ :=
    quadraticArtinSchreierTowerEmbedding P a ha 0
  let e₁ : F₁ →ₐ[F256] F₂ :=
    quadraticArtinSchreierTowerEmbedding P a ha 1
  let e₂ : F₂ →ₐ[F256] F₃ :=
    quadraticArtinSchreierTowerEmbedding P a ha 2
  let e₃ : F₃ →ₐ[F256] F₄ :=
    quadraticArtinSchreierTowerEmbedding P a ha 3
  let y₀ : F₀ := quadraticArtinSchreierTowerCoordinate P a ha 0
  let y₁ : F₁ := quadraticArtinSchreierTowerCoordinate P a ha 1
  let y₂ : F₂ := quadraticArtinSchreierTowerCoordinate P a ha 2
  let y₃ : F₃ := quadraticArtinSchreierTowerCoordinate P a ha 3
  let y₄ : F₄ := quadraticArtinSchreierTowerCoordinate P a ha 4
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP F₄ 2 :=
    charP_of_injective_algebraMap (algebraMap F256 F₄).injective 2
  have htwo : (2 : F₄) = 0 := CharP.cast_eq_zero F₄ 2
  have h₃ : y₄ ^ 2 + y₄ = e₃ y₃ := by
    simpa only [F₃, F₄, e₃, y₃, y₄] using
      quadraticArtinSchreierTower_equation P a ha 3
  have h₂raw := congrArg e₃
    (quadraticArtinSchreierTower_equation P a ha 2)
  have h₂ : (e₃ y₃) ^ 2 + e₃ y₃ = e₃ (e₂ y₂) := by
    simpa only [map_add, map_pow, F₂, F₃, F₄, e₂, e₃, y₂, y₃]
      using h₂raw
  have h₁raw := congrArg e₂
    (quadraticArtinSchreierTower_equation P a ha 1)
  have h₁raw' := congrArg e₃ h₁raw
  have h₁ :
      (e₃ (e₂ y₂)) ^ 2 + e₃ (e₂ y₂) =
        e₃ (e₂ (e₁ y₁)) := by
    simpa only [map_add, map_pow, F₁, F₂, F₃, F₄,
      e₁, e₂, e₃, y₁, y₂] using h₁raw'
  have h₀raw := congrArg e₁
    (quadraticArtinSchreierTower_equation P a ha 0)
  have h₀raw' := congrArg e₂ h₀raw
  have h₀raw'' := congrArg e₃ h₀raw'
  have h₀ :
      (e₃ (e₂ (e₁ y₁))) ^ 2 + e₃ (e₂ (e₁ y₁)) =
        e₃ (e₂ (e₁ (e₀ y₀))) := by
    simpa only [map_add, map_pow, F₀, F₁, F₂, F₃, F₄,
      e₀, e₁, e₂, e₃, y₀, y₁] using h₀raw''
  have h₂' : y₄ ^ 4 + y₄ = e₃ (e₂ y₂) := by
    rw [← h₃] at h₂
    linear_combination h₂ - (y₄ ^ 3 + y₄ ^ 2) * htwo
  have h₁' :
      y₄ ^ 8 + y₄ ^ 4 + y₄ ^ 2 + y₄ =
        e₃ (e₂ (e₁ y₁)) := by
    rw [← h₂'] at h₁
    linear_combination h₁ - y₄ ^ 5 * htwo
  have h₀' : y₄ ^ 16 + y₄ = e₃ (e₂ (e₁ (e₀ y₀))) := by
    rw [← h₁'] at h₀
    linear_combination h₀ -
      (y₄ ^ 12 + y₄ ^ 10 + y₄ ^ 9 + y₄ ^ 8 +
        y₄ ^ 6 + y₄ ^ 5 + y₄ ^ 4 + y₄ ^ 3 + y₄ ^ 2) * htwo
  change y₄ ^ 16 + y₄ = algebraMap K F₄ a
  rw [h₀']
  rfl

private theorem quadraticArtinSchreierTower_four_coordinate_ne_zero
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierTowerCoordinate P a ha 4 ≠ 0 := by
  intro hzero
  have horder := quadraticArtinSchreierTowerCoordinate_order P a ha 4
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder

private theorem reciprocal_artinSchreier_equation
    {L : Type*} [Field L] [CharP L 2] (a y : L)
    (ha : a ≠ 0) (hy : y ≠ 0) (hyAS : y ^ 16 + y = a) :
    y⁻¹ ^ 16 + a⁻¹ * y⁻¹ ^ 15 + a⁻¹ = 0 := by
  have htwo : (2 : L) = 0 := CharP.cast_eq_zero L 2
  field_simp [ha, hy]
  linear_combination hyAS + a * htwo

private theorem sourceStepPolynomial_aeval_quadraticTowerReciprocal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval
        (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
          (sourceStepRhs_order P x hx) 4)⁻¹
        (sourceStepPolynomial P x hx) = 0 := by
  let a := sourceStepRhs x
  let ha : P.order a = -1 := sourceStepRhs_order P x hx
  let T := QuadraticArtinSchreierTowerField P a ha 4
  let y : T := quadraticArtinSchreierTowerCoordinate P a ha 4
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP T 2 :=
    charP_of_injective_algebraMap (algebraMap K T).injective 2
  have ha_ne : a ≠ 0 := by
    intro hzero
    have horder := ha
    rw [hzero] at horder
    simp [GlobalPlace.order] at horder
  let aT : T := algebraMap K T a
  have haT : aT ≠ 0 := by
    simpa only [aT, map_zero] using (algebraMap K T).injective.ne ha_ne
  have hy : y ≠ 0 := by
    simpa only [a, ha, T, y] using
      quadraticArtinSchreierTower_four_coordinate_ne_zero P a ha
  have hyAS : y ^ 16 + y = aT := by
    simpa only [T, y, aT] using
      quadraticArtinSchreierTower_four_equation P a ha
  have hexplicit :
      y⁻¹ ^ 16 + aT⁻¹ * y⁻¹ ^ 15 + aT⁻¹ = 0 := by
    exact reciprocal_artinSchreier_equation aT y haT hy hyAS
  have hpoly : sourceStepPolynomial P x hx =
      X ^ 16 + C a⁻¹ * X ^ 15 + C a⁻¹ := by
    simp [sourceStepPolynomial, sourceStepReciprocalPolynomial,
      sourceStepUniformizer, coe_reciprocalUniformizer, a]
  rw [Polynomial.aeval_def]
  calc
    eval₂ (Algebra.ofId K T) y⁻¹ (sourceStepPolynomial P x hx) =
        eval₂ (Algebra.ofId K T) y⁻¹
          (X ^ 16 + C a⁻¹ * X ^ 15 + C a⁻¹) :=
      congrArg (eval₂ (Algebra.ofId K T) y⁻¹) hpoly
    _ = 0 := by
      rw [eval₂_add, eval₂_add, eval₂_X_pow,
        eval₂_mul, eval₂_C, eval₂_X_pow]
      simp only [aT, map_inv₀] at hexplicit ⊢
      exact hexplicit

private noncomputable def sourceStepToQuadraticRefinementHom
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepField P x hx →ₐ[K]
      QuadraticArtinSchreierTowerField P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 :=
  AdjoinRoot.liftAlgHom (sourceStepPolynomial P x hx)
    (Algebra.ofId K
      (QuadraticArtinSchreierTowerField P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4))
    (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
      (sourceStepRhs_order P x hx) 4)⁻¹
    (sourceStepPolynomial_aeval_quadraticTowerReciprocal P x hx)

@[simp]
private theorem sourceStepToQuadraticRefinementHom_apply_root
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepToQuadraticRefinementHom P x hx
        (sourceStepReciprocalRoot P x hx) =
      (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4)⁻¹ := by
  dsimp only [sourceStepToQuadraticRefinementHom, sourceStepReciprocalRoot]
  erw [AdjoinRoot.liftAlgHom_root]

/-- The actual degree-sixteen source step is the four-stage quadratic
Artin--Schreier refinement. -/
noncomputable def sourceStepQuadraticRefinementEquiv
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepField P x hx ≃ₐ[K]
      QuadraticArtinSchreierTowerField P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 := by
  let f := sourceStepToQuadraticRefinementHom P x hx
  have hdim : Module.finrank K (SourceStepField P x hx) =
      Module.finrank K
        (QuadraticArtinSchreierTowerField P (sourceStepRhs x)
          (sourceStepRhs_order P x hx) 4) := by
    rw [sourceStep_finrank, quadraticArtinSchreierTower_finrank]
    norm_num
  letI : FiniteDimensional K
      (QuadraticArtinSchreierTowerField P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4) :=
    quadraticArtinSchreierTowerFieldFiniteDimensional P (sourceStepRhs x)
      (sourceStepRhs_order P x hx) 4
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp
      (show Function.Injective f.toLinearMap from f.injective)
  exact AlgEquiv.ofBijective f ⟨f.injective, hsurj⟩

@[simp]
private theorem sourceStepQuadraticRefinementEquiv_apply
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (z : SourceStepField P x hx) :
    sourceStepQuadraticRefinementEquiv P x hx z =
      sourceStepToQuadraticRefinementHom P x hx z := by
  dsimp only [sourceStepQuadraticRefinementEquiv]
  erw [AlgEquiv.ofBijective_apply]

/-- The field equivalence sends the source coordinate to the terminal
quadratic-refinement coordinate. -/
theorem sourceStepQuadraticRefinementEquiv_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepQuadraticRefinementEquiv P x hx
        (sourceStepCoordinate P x hx) =
      quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 := by
  rw [sourceStepCoordinate, map_inv₀]
  rw [sourceStepQuadraticRefinementEquiv_apply,
    sourceStepToQuadraticRefinementHom_apply_root, inv_inv]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
