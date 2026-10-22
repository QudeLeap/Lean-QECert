import QEC.Coding.ExpanderCodes.QuadraticGeneratorSets

/-!
# A specialization-independent quadratic torus index

The scalar kernel of the constant quadratic unit group is independent of
the coefficient field and the specialization parameter. Thus the two
generator orbits in [DEL21, Section 6.2] admit a single index type across
all finite-field specializations. This is the quantifier bridge needed to
reuse one local-code sample, not an assumption of a spectral family.
-/

noncomputable section

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

open scoped QuadraticAlgebra

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K]

/-- At the harmless torus-only specialization `y = 0`, the kernel consists
of constant scalars. The definition itself does not depend on a larger field. -/
def scalarKernel (epsilon : F) : Subgroup (QuadraticAlgebra F epsilon 0)ˣ :=
  (constantProjectiveMap (RingHom.id F) epsilon 0).ker

abbrev TorusIndex (epsilon : F) :=
  (QuadraticAlgebra F epsilon 0)ˣ ⧸ scalarKernel epsilon

theorem scalarKernel_eq (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    scalarKernel epsilon = (constantProjectiveMap f epsilon y).ker := by
  ext a
  change constantProjectiveMap (RingHom.id F) epsilon 0 a = 1 ↔
    constantProjectiveMap f epsilon y a = 1
  rw [constantProjectiveMap_eq_one_iff (RingHom.id F) epsilon 0 (by simp) hTwoF,
    constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo]

/-- The same projective constant torus indexes every good specialization. -/
def torusIndexEquiv (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    TorusIndex epsilon ≃* constantTorus f epsilon y :=
  (QuotientGroup.quotientMulEquivOfEq
    (scalarKernel_eq f epsilon y hTwoF hOne hTwo)).trans
      (QuotientGroup.quotientKerEquivRange (constantProjectiveMap f epsilon y))

/-- The actual projective image of the specialization-independent index. -/
def torusIndexMap (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    TorusIndex epsilon →* ProjectiveGroup (f epsilon) y :=
  (constantTorus f epsilon y).subtype.comp
    (torusIndexEquiv f epsilon y hTwoF hOne hTwo).toMonoidHom

@[simp] theorem torusIndexMap_mk (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ) :
    torusIndexMap f epsilon y hTwoF hOne hTwo (QuotientGroup.mk a) =
      constantProjectiveMap f epsilon y a := rfl

theorem torusIndexMap_injective (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (torusIndexMap f epsilon y hTwoF hOne hTwo) :=
  Subtype.val_injective.comp (torusIndexEquiv f epsilon y hTwoF hOne hTwo).injective

instance finiteTorusIndex (epsilon : F) [Finite F] : Finite (TorusIndex epsilon) := by
  letI : Finite (QuadraticAlgebra F epsilon 0) :=
    Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd epsilon 0).symm
  infer_instance

instance fintypeTorusIndex (epsilon : F) [Fintype F] : Fintype (TorusIndex epsilon) :=
  Fintype.ofFinite _

theorem torusIndex_card (epsilon : F) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hTwoF : (2 : F) ≠ 0) :
    Fintype.card (TorusIndex epsilon) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (torusIndexEquiv (RingHom.id F) epsilon 0 hTwoF (by simp) hTwoF).toEquiv]
  exact card_constantTorus (RingHom.id F) epsilon 0 hNonSquare (by simp) hTwoF

def torusIndexAlpha (epsilon : F) (hEpsilon : epsilon ≠ 0) : TorusIndex epsilon :=
  QuotientGroup.mk (quadraticAlphaUnit epsilon hEpsilon)

theorem torusIndexAlpha_sq (epsilon : F) (hEpsilon : epsilon ≠ 0)
    (hTwoF : (2 : F) ≠ 0) : torusIndexAlpha epsilon hEpsilon ^ 2 = 1 := by
  change (QuotientGroup.mk (quadraticAlphaUnit epsilon hEpsilon) : TorusIndex epsilon) ^ 2 = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  change constantProjectiveMap (RingHom.id F) epsilon 0
    (quadraticAlphaUnit epsilon hEpsilon ^ 2) = 1
  apply (constantProjectiveMap_eq_one_iff (RingHom.id F) epsilon 0 (by simp) hTwoF _).mpr
  simp [quadraticAlphaUnit, pow_two]

theorem torusIndexMap_alpha (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    torusIndexMap f epsilon y hTwoF hOne hTwo (torusIndexAlpha epsilon hEpsilon) =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) := by
  rw [torusIndexAlpha, torusIndexMap_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Units.ext
  ext <;> simp [constantProjectiveMap, coefficientEmbedding, quadraticAlphaUnit, alpha]

/-- The first orbit, now with an index independent of the coefficient field. -/
def indexedLeft (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) : ProjectiveGroup (f epsilon) y :=
  torusIndexMap f epsilon y hTwoF hOne hTwo t * projectiveBase (f epsilon) y hY hOne *
    (torusIndexMap f epsilon y hTwoF hOne hTwo t)⁻¹

/-- The second orbit uses the same specialization-independent index. -/
def indexedRight (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    ProjectiveGroup (f epsilon) y :=
  torusIndexMap f epsilon y hTwoF hOne hTwo t *
      projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
    (torusIndexMap f epsilon y hTwoF hOne hTwo t)⁻¹

theorem indexedLeft_injective (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (indexedLeft f epsilon y hTwoF hY hOne hTwo) :=
  (constantTorus_conjugate_base_injective f epsilon y hEpsilon hY hOne hTwo).comp
    (torusIndexEquiv f epsilon y hTwoF hOne hTwo).injective

theorem indexedRight_injective (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo) :=
  (constantTorus_conjugate_prime_injective f epsilon y hEpsilon hY hOne hTwo).comp
    (torusIndexEquiv f epsilon y hTwoF hOne hTwo).injective

/-- The inverse permutation is fixed before choosing any specialization. -/
def indexedLeftInverse (epsilon : F) (hEpsilon : epsilon ≠ 0) :
    Equiv.Perm (TorusIndex epsilon) := Equiv.mulRight (torusIndexAlpha epsilon hEpsilon)

theorem indexedLeft_inverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    indexedLeft f epsilon y hTwoF hY hOne hTwo (indexedLeftInverse epsilon hEpsilon t) =
      (indexedLeft f epsilon y hTwoF hY hOne hTwo t)⁻¹ := by
  change indexedLeft f epsilon y hTwoF hY hOne hTwo (t * torusIndexAlpha epsilon hEpsilon) = _
  simp only [indexedLeft, map_mul, torusIndexMap_alpha, mul_inv_rev]
  have hConjugate := projectiveAlpha_conjugate_base (f epsilon) y
    ((map_ne_zero f).mpr hEpsilon) hY hOne
  calc
    _ = torusIndexMap f epsilon y hTwoF hOne hTwo t *
        (projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
          projectiveBase (f epsilon) y hY hOne *
          (projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon))⁻¹) *
        (torusIndexMap f epsilon y hTwoF hOne hTwo t)⁻¹ := by simp only [mul_assoc]
    _ = _ := by rw [hConjugate]; simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem indexedRight_inverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t =
      (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t)⁻¹ := by
  have hSquare : indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t ^ 2 = 1 := by
    rw [indexedRight, conj_pow, projectivePrime_sq]
    simp
  exact (inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hSquare)).symm

theorem indexed_total_nonconjugacy (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a b : TorusIndex epsilon) (g : ProjectiveGroup (f epsilon) y) :
    indexedLeft f epsilon y hTwoF hY hOne hTwo a * g ≠
      g * indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo b :=
  conjugates_total_nonconjugacy (f epsilon) y ((map_ne_zero f).mpr hEpsilon)
    hY hOne hTwo _ _ g

end QEC.Coding.ExpanderCodes.QuaternionGenerators
