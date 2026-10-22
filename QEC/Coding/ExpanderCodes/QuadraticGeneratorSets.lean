import QEC.Coding.ExpanderCodes.QuadraticTorus

/-!
# Constant-torus arithmetic generator sets

These are the constant-field torus orbits of the two explicit quaternion
generators [DEL21, Section 6.2]. Inverse closure and total nonconjugacy are
derived from the coordinates, rather than stored as construction inputs.
-/

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

open scoped QuadraticAlgebra

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K]

/-- The constant quadratic generator is a unit by its explicit inverse. -/
def quadraticAlphaUnit (epsilon : F) (hEpsilon : epsilon ≠ 0) :
    (QuadraticAlgebra F epsilon 0)ˣ where
  val := ⟨0, 1⟩
  inv := ⟨0, epsilon⁻¹⟩
  val_inv := by ext <;> simp [hEpsilon]
  inv_val := by ext <;> simp [hEpsilon]

theorem projectiveAlpha_mem_constantTorus (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) :
    projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) ∈
      constantTorus f epsilon y := by
  refine ⟨quadraticAlphaUnit epsilon hEpsilon, ?_⟩
  apply congrArg (QuotientGroup.mk' _)
  apply Units.ext
  ext <;> simp [quadraticAlphaUnit, coefficientEmbedding, alpha]

/-- Central quaternion units have no non-scalar coordinates in odd characteristic. -/
theorem val_eq_scalar_of_mem_center (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (Model epsilon y)ˣ) (ha : a ∈ Subgroup.center (Model epsilon y)ˣ) :
    (a : Model epsilon y) = (((a : Model epsilon y).re : K) : Model epsilon y) := by
  have hAlpha := Subgroup.mem_center_iff.mp ha (alphaUnit epsilon y hEpsilon)
  have hZ := Subgroup.mem_center_iff.mp ha (skewUnit epsilon y hOne)
  have hI := congrArg (fun b : (Model epsilon y)ˣ => (b : Model epsilon y).imK) hZ
  have hJ := congrArg (fun b : (Model epsilon y)ˣ => (b : Model epsilon y).imK) hAlpha
  have hK := congrArg (fun b : (Model epsilon y)ˣ => (b : Model epsilon y).imJ) hAlpha
  simp [skewUnit, z] at hI
  simp [alpha] at hJ hK
  have hDoubleI : (2 : K) * (a : Model epsilon y).imI = 0 := by
    linear_combination -hI
  have hDoubleJ : (2 : K) * (a : Model epsilon y).imJ = 0 := by
    linear_combination hJ
  have hDoubleK : (2 : K) * epsilon * (a : Model epsilon y).imK = 0 := by
    linear_combination hK
  have hImagI := (mul_eq_zero.mp hDoubleI).resolve_left hTwo
  have hImagJ := (mul_eq_zero.mp hDoubleJ).resolve_left hTwo
  have hImagK := (mul_eq_zero.mp hDoubleK).resolve_left (mul_ne_zero hTwo hEpsilon)
  ext <;> simp [hImagI, hImagJ, hImagK]

/-- A constant torus element stabilizing the first generator is projectively
trivial. This proves freeness of the orbit rather than assuming its size. -/
theorem constantProjectiveMap_eq_one_of_commutes_base
    (f : F →+* K) (epsilon : F) (y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ)
    (hCommute : constantProjectiveMap f epsilon y a * projectiveBase (f epsilon) y hY hOne =
      projectiveBase (f epsilon) y hY hOne * constantProjectiveMap f epsilon y a) :
    constantProjectiveMap f epsilon y a = 1 := by
  let image := Units.map (coefficientEmbedding f epsilon y).toMonoidHom a
  let b := baseUnit (f epsilon) y hY hOne
  let c := (image * b) / (b * image)
  have hCenter : c ∈ Subgroup.center (Model (f epsilon) y)ˣ := by
    apply QuotientGroup.eq_iff_div_mem.mp
    simpa [constantProjectiveMap, projectiveBase, image, b, QuotientGroup.mk_mul]
      using hCommute
  have hScalar := val_eq_scalar_of_mem_center (f epsilon) y ((map_ne_zero f).mpr hEpsilon)
    hOne hTwo c hCenter
  have hProduct : image * b = c * (b * image) := by simp [c]
  have hValue := congrArg (fun u : (Model (f epsilon) y)ˣ => (u : Model (f epsilon) y))
    hProduct
  simp only [Units.val_mul] at hValue
  rw [hScalar] at hValue
  have hRe := congrArg QuaternionAlgebra.re hValue
  have hImI := congrArg QuaternionAlgebra.imI hValue
  simp [image, b, coefficientEmbedding, base] at hRe hImI
  have hScale : (c : Model (f epsilon) y).re = 1 := by
    by_cases hReal : f (a : QuadraticAlgebra F epsilon 0).re = 0
    · have hImag : f (a : QuadraticAlgebra F epsilon 0).im ≠ 0 := by
        intro hImag
        have hRealF : (a : QuadraticAlgebra F epsilon 0).re = 0 :=
          f.injective (by simpa using hReal)
        have hImagF : (a : QuadraticAlgebra F epsilon 0).im = 0 :=
          f.injective (by simpa using hImag)
        have hInverse := congrArg QuadraticAlgebra.re a.val_inv
        have hZeroOne : (0 : F) = 1 := by
          simpa only [QuadraticAlgebra.re_mul, hRealF, hImagF, zero_mul, mul_zero,
            add_zero, QuadraticAlgebra.re_one] using hInverse
        exact zero_ne_one hZeroOne
      apply mul_right_cancel₀ hImag
      simpa using hImI.symm
    · apply mul_right_cancel₀ hReal
      simpa using hRe.symm
  have hK := congrArg QuaternionAlgebra.imK hValue
  simp [image, b, coefficientEmbedding, base, hScale] at hK
  field_simp at hK
  have hDouble : (2 : K) * f (a : QuadraticAlgebra F epsilon 0).im = 0 := by
    linear_combination -hK
  apply (constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo a).mpr
  exact f.injective (by simpa using (mul_eq_zero.mp hDouble).resolve_left hTwo)

theorem constantTorus_conjugate_base_injective (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Function.Injective (fun t : constantTorus f epsilon y =>
      (t : ProjectiveGroup (f epsilon) y) * projectiveBase (f epsilon) y hY hOne *
        (t : ProjectiveGroup (f epsilon) y)⁻¹) := by
  intro t u hEqual
  have hCommute := congrArg (fun x => (u : ProjectiveGroup (f epsilon) y)⁻¹ * x *
    (t : ProjectiveGroup (f epsilon) y)) hEqual
  simp [mul_assoc] at hCommute
  have hMember : (u : ProjectiveGroup (f epsilon) y)⁻¹ * t ∈ constantTorus f epsilon y :=
    (constantTorus f epsilon y).mul_mem
      ((constantTorus f epsilon y).inv_mem u.property) t.property
  obtain ⟨a, ha⟩ := hMember
  have hIdentity := constantProjectiveMap_eq_one_of_commutes_base f epsilon y hEpsilon
    hY hOne hTwo a (by simpa [ha, mul_assoc] using hCommute)
  rw [ha] at hIdentity
  apply Subtype.ext
  exact (inv_mul_eq_one.mp hIdentity).symm

/-- The constant-torus first generator orbit has the asserted `q + 1` elements. -/
theorem card_constant_conjugacySet (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Nat.card (conjugacySet (constantTorus f epsilon y)
      (projectiveBase (f epsilon) y hY hOne)) = Fintype.card F + 1 := by
  unfold conjugacySet
  rw [← Nat.card_congr (Equiv.ofInjective _
    (constantTorus_conjugate_base_injective f epsilon y hEpsilon hY hOne hTwo))]
  exact card_constantTorus f epsilon y hNonSquare hOne hTwo

theorem projectivePrime_eq_alpha_mul_base (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectivePrime epsilon y hEpsilon hY hOne =
      projectiveAlpha epsilon y hEpsilon * projectiveBase epsilon y hY hOne :=
  (QuotientGroup.mk' _).map_mul _ _

/-- Every constant torus element commutes with the quadratic unit. -/
theorem constantTorus_commutes_alpha (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (t : constantTorus f epsilon y) :
    (t : ProjectiveGroup (f epsilon) y) *
        projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) * t := by
  obtain ⟨a, ha⟩ := t.property
  rw [← ha]
  have hUnits : Units.map (coefficientEmbedding f epsilon y).toMonoidHom a *
        alphaUnit (f epsilon) y ((map_ne_zero f).mpr hEpsilon) =
      alphaUnit (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
        Units.map (coefficientEmbedding f epsilon y).toMonoidHom a := by
    apply Units.ext
    ext <;> simp [coefficientEmbedding, alpha]
  have hProjective := congrArg (QuotientGroup.mk' (Subgroup.center (Model (f epsilon) y)ˣ)) hUnits
  simpa [constantProjectiveMap, projectiveAlpha, QuotientGroup.mk_mul] using hProjective

theorem constantTorus_conjugate_prime (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (t : constantTorus f epsilon y) :
    (t : ProjectiveGroup (f epsilon) y) *
        projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹ =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
        ((t : ProjectiveGroup (f epsilon) y) * projectiveBase (f epsilon) y hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹) := by
  rw [projectivePrime_eq_alpha_mul_base]
  calc
    _ = ((t : ProjectiveGroup (f epsilon) y) *
        projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon)) *
          projectiveBase (f epsilon) y hY hOne * (t : ProjectiveGroup (f epsilon) y)⁻¹ := by
      simp [mul_assoc]
    _ = _ := by
      rw [constantTorus_commutes_alpha f epsilon y hEpsilon t]
      simp [mul_assoc]

theorem constantTorus_conjugate_prime_injective (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Function.Injective (fun t : constantTorus f epsilon y =>
      (t : ProjectiveGroup (f epsilon) y) *
        projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹) := by
  intro t u hEqual
  dsimp only at hEqual
  rw [constantTorus_conjugate_prime f epsilon y hEpsilon hY hOne t,
    constantTorus_conjugate_prime f epsilon y hEpsilon hY hOne u] at hEqual
  exact constantTorus_conjugate_base_injective f epsilon y hEpsilon hY hOne hTwo
    (mul_left_cancel hEqual)

/-- The second constant-torus orbit also has exactly `q + 1` elements. -/
theorem card_constant_prime_conjugacySet (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Nat.card (conjugacySet (constantTorus f epsilon y)
      (projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne)) =
        Fintype.card F + 1 := by
  unfold conjugacySet
  rw [← Nat.card_congr (Equiv.ofInjective _
    (constantTorus_conjugate_prime_injective f epsilon y hEpsilon hY hOne hTwo))]
  exact card_constantTorus f epsilon y hNonSquare hOne hTwo

def constantLeftSet (f : F →+* K) (epsilon : F) (y : K)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Set (ProjectiveGroup (f epsilon) y) :=
  conjugacySet (constantTorus f epsilon y) (projectiveBase (f epsilon) y hY hOne)

def constantRightSet (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Set (ProjectiveGroup (f epsilon) y) :=
  conjugacySet (constantTorus f epsilon y)
    (projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne)

theorem constantLeftSet_inv_mem (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    {g : ProjectiveGroup (f epsilon) y} (hg : g ∈ constantLeftSet f epsilon y hY hOne) :
    g⁻¹ ∈ constantLeftSet f epsilon y hY hOne :=
  inv_mem_conjugacySet _ _ _ (projectiveAlpha_mem_constantTorus f epsilon y hEpsilon)
    (projectiveAlpha_conjugate_base (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne) hg

theorem constantRightSet_inv_mem (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    {g : ProjectiveGroup (f epsilon) y}
    (hg : g ∈ constantRightSet f epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ constantRightSet f epsilon y hEpsilon hY hOne :=
  inv_mem_conjugacySet_of_sq_one _ _
    (projectivePrime_sq (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne) hg

theorem constantSets_total_nonconjugacy (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) {a b : ProjectiveGroup (f epsilon) y}
    (ha : a ∈ constantLeftSet f epsilon y hY hOne)
    (hb : b ∈ constantRightSet f epsilon y hEpsilon hY hOne)
    (g : ProjectiveGroup (f epsilon) y) : a * g ≠ g * b :=
  conjugacySet_total_nonconjugacy _ _ _ _
    (projectiveBase_sq_ne_one (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne hTwo)
    (projectivePrime_sq (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne) ha hb g

end QEC.Coding.ExpanderCodes.QuaternionGenerators
