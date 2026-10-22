import QEC.Coding.AlgebraicGeometry.Towers.RegularQuadraticStep
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Local models for a literal quadratic Artin--Schreier generator

The equation and the actual field degree identify the simple-pole model.
In the regular case, generation of the field additionally rules out a root
already in the base field. No different or ramification formula is assumed.
-/

open Polynomial IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private local instance : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2

variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]

/-- The simple-pole model maps to the literal quadratic extension by sending
its reciprocal root to the inverse of the given Artin--Schreier root. -/
noncomputable def quadraticSimplePoleLiteralEquiv
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1)
    (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) :
    QuadraticArtinSchreierField P a ha ≃ₐ[K] L := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  have ha0 : a ≠ 0 := by
    intro h
    simp [h, GlobalPlace.order] at ha
  have haL : algebraMap K L a ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne ha0
  have hy0 : y ≠ 0 := by
    intro h
    simp [h] at hy
    exact haL hy.symm
  have hroot : eval₂ (Algebra.ofId K L) y⁻¹
      (quadraticArtinSchreierPolynomial P a ha) = 0 := by
    have hp : quadraticArtinSchreierPolynomial P a ha =
        X ^ 2 + C a⁻¹ * X + C a⁻¹ := by
      simp [quadraticArtinSchreierPolynomial,
        quadraticArtinSchreierReciprocalPolynomial, coe_reciprocalUniformizer]
    rw [hp]
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_inv₀]
    change y⁻¹ ^ 2 + (algebraMap K L a)⁻¹ * y⁻¹ +
      (algebraMap K L a)⁻¹ = 0
    field_simp [hy0, haL]
    rw [← hy]
    calc
      y ^ 2 + y + y + y ^ 2 = (y ^ 2 + y ^ 2) + (y + y) := by ac_rfl
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
    all_goals simp
  let f : QuadraticArtinSchreierField P a ha →ₐ[K] L :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K L) y⁻¹ hroot
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  have hdim : Module.finrank K (QuadraticArtinSchreierField P a ha) =
      Module.finrank K L := by rw [quadraticArtinSchreier_finrank, hdegree]
  exact AlgEquiv.ofBijective f ⟨f.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp f.injective⟩

/-- A literal generator of a quadratic field has the irreducible regular
Artin--Schreier polynomial, whenever its parameter is integral. -/
theorem quadraticRegularLiteralPolynomial_irreducible
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (y : L) (hy : y ^ 2 + y = algebraMap K L (b : K))
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤) :
    Irreducible (regularQuadraticArtinSchreierPolynomial P b) := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  let p := regularQuadraticArtinSchreierPolynomial P b
  have hroot : aeval y p = 0 := by
    simp only [p, regularQuadraticArtinSchreierPolynomial,
      regularQuadraticArtinSchreierIntegralPolynomial, Polynomial.map_add,
      Polynomial.map_pow, map_X, map_C, map_add, map_pow, aeval_X, aeval_C]
    change y ^ 2 + y + algebraMap K L (b : K) = 0
    rw [hy, CharTwo.add_self_eq_zero]
  have hi : IsIntegral K y :=
    ⟨p, regularQuadraticArtinSchreierPolynomial_monic P b, hroot⟩
  have hdeg : (minpoly K y).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hi, hgen]
    exact (IntermediateField.topEquiv.toLinearEquiv.finrank_eq).trans hdegree
  have hmin : p = minpoly K y :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hi) (regularQuadraticArtinSchreierPolynomial_monic P b)
      (minpoly.dvd K y hroot) (by
        simp only [p, regularQuadraticArtinSchreierPolynomial_natDegree, hdeg, le_refl])
  change Irreducible p
  rw [hmin]
  exact minpoly.irreducible hi

/-- The regular integral-root model is the actual generated quadratic field. -/
noncomputable def quadraticRegularLiteralEquiv
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (y : L) (hy : y ^ 2 + y = algebraMap K L (b : K))
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤) :
    RegularQuadraticArtinSchreierField P b
      (quadraticRegularLiteralPolynomial_irreducible P b y hy hdegree hgen) ≃ₐ[K] L := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  let hirr := quadraticRegularLiteralPolynomial_irreducible P b y hy hdegree hgen
  let S := RegularQuadraticArtinSchreierField P b hirr
  let f : S →ₐ[K] L := by
    apply AdjoinRoot.liftAlgHom _ (Algebra.ofId K L) y
    change eval₂ (Algebra.ofId K L) y
      (regularQuadraticArtinSchreierPolynomial P b) = 0
    simp only [regularQuadraticArtinSchreierPolynomial,
      regularQuadraticArtinSchreierIntegralPolynomial, Polynomial.map_add,
      Polynomial.map_pow, map_X, map_C, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    change y ^ 2 + y + algebraMap K L (b : K) = 0
    rw [hy, CharTwo.add_self_eq_zero]
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  have hdim : Module.finrank K S = Module.finrank K L := by
    rw [regularQuadraticArtinSchreier_finrank, hdegree]
  exact AlgEquiv.ofBijective f ⟨f.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp f.injective⟩

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
