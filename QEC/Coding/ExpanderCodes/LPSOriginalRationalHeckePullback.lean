import QEC.Coding.ExpanderCodes.LPSOriginalRationalLevelInclusion

/-!
# LPSOriginalRationalHeckePullback

Construct the second actual original rational Hecke pullback, using the same
holomorphic ring, its genuine fraction field and the existing Q(j,j_N).
Forward positive-determinant pullback is a genuine equivalence. The actual
Fricke matrix exchanges j and j_N; at product level Np it sends j_N to j_p.
Finite rational polynomial evaluation and fraction localization identify the
existing generated rational field with the subfield closure of j and j_N.
Fricke therefore preserves that exact field at every positive level.

Actual dilation sends j to j_p and j_N to j_Np. Its embedded image equals the
product-level Fricke image of the source field. The previously proved first
inclusion supplies membership in Q(j,j_Np), and genuine field-degree transport
proves image-relative degree p+1 for a coprime prime. The restricted map,
injectivity, literal generator formulas and fieldRange are all constructed.
Fricke moves j: no algebra homomorphism over the fixed embedded Q(j) is claimed.
No 4-divides-p assumption or supplied map/image/degree is used.

This derived internal original-family API follows pinned PK22 main.tex ex:Xpq
(484–486) and the audited original modular-curve route. Exact public th:qLDPC
(231–238), node pk-good-qldpc, remains unchanged and unproved. Arithmetic good
reduction, geometric Hecke/Frobenius/Weil, full-level/every-representation LPS
spectra and the arbitrary-finite-field/every-rate explicit qLDPC family remain
subsequent mathematics. No new public theorem/source claim is introduced.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Actual forward positive-determinant pullback, with genuine inverse action. -/
def lpsOriginalPositiveHolomorphicPullback (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) :
    LPSOriginalHolomorphicRing ≃ₐ[ℂ] LPSOriginalHolomorphicRing where
  toFun f := ⟨fun τ => f.val (g • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul hg)⟩
  invFun f := ⟨fun τ => f.val (g⁻¹ • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul (by
      simpa only [map_inv, Units.val_inv_eq_inv_val] using inv_pos.mpr hg))⟩
  left_inv f := by apply Subtype.ext; funext τ; simp only [smul_inv_smul]
  right_inv f := by apply Subtype.ext; funext τ; simp only [inv_smul_smul]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def lpsOriginalPositiveFractionPullback (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) :
    LPSOriginalHolomorphicFractionField ≃+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.ringEquivOfRingEquiv
    (lpsOriginalPositiveHolomorphicPullback g hg).toRingEquiv

lemma lpsOriginalPositiveFractionPullback_localization
    (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (f : LPSOriginalHolomorphicRing) :
    lpsOriginalPositiveFractionPullback g hg
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f) =
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalPositiveHolomorphicPullback g hg f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ f

def lpsOriginalFrickeMatrix (N : ℕ) (hN : 0 < N) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * lpsE2AffineMatrix N hN 0

lemma lpsOriginalFrickeMatrix_det (N : ℕ) (hN : 0 < N) :
    (lpsOriginalFrickeMatrix N hN).det.val = (N : ℝ) := by
  calc
    (lpsOriginalFrickeMatrix N hN).det.val =
        (lpsE2AffineMatrix N hN 0).det.val := by simp [lpsOriginalFrickeMatrix]
    _ = (N : ℝ) := lpsE2AffineMatrix_det N hN 0

lemma lpsOriginalFrickeMatrix_pos (N : ℕ) (hN : 0 < N) :
    0 < (lpsOriginalFrickeMatrix N hN).det.val := by
  rw [lpsOriginalFrickeMatrix_det]
  exact_mod_cast hN

lemma lpsOriginalPositiveHolomorphicPullback_fricke_j
    (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveHolomorphicPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) lpsOriginalJHolomorphic =
        lpsOriginalJNHolomorphic N hN := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant
    ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * lpsE2AffineMatrix N hN 0) • τ) =
      lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • τ)
  rw [mul_smul]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨ModularGroup.S, rfl⟩ _

/-- Actual complex value of the Fricke action on the original upper half plane. -/
lemma lpsOriginalFrickeMatrix_action (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    ((lpsOriginalFrickeMatrix N hN • τ : ℍ) : ℂ) =
      (-((N : ℂ) * (τ : ℂ)))⁻¹ := by
  rw [lpsOriginalFrickeMatrix, mul_smul]
  change ((ModularGroup.S • (lpsE2AffineMatrix N hN 0 • τ) : ℍ) : ℂ) = _
  rw [UpperHalfPlane.modular_S_smul]
  simp only [lpsOriginalJDilated_coe]

/-- Dilation after Fricke is the actual S action, not an assumed relation on j. -/
lemma lpsOriginalDilation_fricke (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    lpsE2AffineMatrix N hN 0 • (lpsOriginalFrickeMatrix N hN • τ) =
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • τ := by
  apply UpperHalfPlane.ext
  rw [lpsOriginalJDilated_coe, lpsOriginalFrickeMatrix_action]
  change (N : ℂ) * (-((N : ℂ) * (τ : ℂ)))⁻¹ = ((ModularGroup.S • τ : ℍ) : ℂ)
  rw [UpperHalfPlane.modular_S_smul]
  change (N : ℂ) * (-((N : ℂ) * (τ : ℂ)))⁻¹ = (-(τ : ℂ))⁻¹
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Fricke swaps the literal original second generator with j. -/
lemma lpsOriginalPositiveHolomorphicPullback_fricke_jN
    (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveHolomorphicPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) (lpsOriginalJNHolomorphic N hN) =
        lpsOriginalJHolomorphic := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 •
      (lpsOriginalFrickeMatrix N hN • τ)) = lpsOriginalJInvariant τ
  rw [lpsOriginalDilation_fricke]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨ModularGroup.S, rfl⟩ _

/-- At level Np the original N-dilation followed by Fricke is S after p-dilation. -/
lemma lpsOriginalDilation_fricke_product (N p : ℕ) (hN : 0 < N) (hp : 0 < p)
    (τ : ℍ) :
    lpsE2AffineMatrix N hN 0 •
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp) • τ) =
    Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • (lpsE2AffineMatrix p hp 0 • τ) := by
  apply UpperHalfPlane.ext
  rw [lpsOriginalJDilated_coe, lpsOriginalFrickeMatrix_action]
  change (N : ℂ) * (-(((N*p : ℕ) : ℂ) * (τ : ℂ)))⁻¹ =
    ((ModularGroup.S • (lpsE2AffineMatrix p hp 0 • τ) : ℍ) : ℂ)
  rw [UpperHalfPlane.modular_S_smul]
  simp only [lpsOriginalJDilated_coe, Nat.cast_mul]
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The actual product-level Fricke sends j_N to j_p. -/
lemma lpsOriginalPositiveHolomorphicPullback_fricke_product_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalPositiveHolomorphicPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalJNHolomorphic N hN) = lpsOriginalJNHolomorphic p hp := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 •
    (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp) • τ)) =
      lpsOriginalJInvariant (lpsE2AffineMatrix p hp 0 • τ)
  rw [lpsOriginalDilation_fricke_product]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨ModularGroup.S, rfl⟩ _

/-- The literal original j in the actual holomorphic fraction field. -/
def lpsOriginalJInFractionField : LPSOriginalHolomorphicFractionField :=
  algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField lpsOriginalJHolomorphic

lemma lpsOriginalPositiveFractionPullback_fricke_j (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) lpsOriginalJInFractionField =
        lpsOriginalJNInFractionField N hN := by
  rw [lpsOriginalJInFractionField, lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_fricke_j]
  rfl

lemma lpsOriginalPositiveFractionPullback_fricke_jN (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) (lpsOriginalJNInFractionField N hN) =
        lpsOriginalJInFractionField := by
  rw [lpsOriginalJNInFractionField, lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_fricke_jN]
  rfl

lemma lpsOriginalPositiveFractionPullback_fricke_product_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalPositiveFractionPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalJNInFractionField N hN) = lpsOriginalJNInFractionField p hp := by
  rw [lpsOriginalJNInFractionField, lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_fricke_product_jN]
  rfl

/-- Rational polynomial evaluation is literally evaluation at j in the ambient fraction field. -/
lemma lpsOriginalJHolomorphicEvalQ_localization (P : Polynomial ℚ) :
    algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (lpsOriginalJHolomorphicEvalQ P) =
        P.eval₂ (algebraMap ℚ LPSOriginalHolomorphicFractionField) lpsOriginalJInFractionField := by
  have he : (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
      lpsOriginalJHolomorphicEvalQ =
        Polynomial.eval₂RingHom (algebraMap ℚ LPSOriginalHolomorphicFractionField)
          lpsOriginalJInFractionField := by
    apply Polynomial.ringHom_ext
    · intro q
      simp [lpsOriginalJHolomorphicEvalQ, lpsOriginalJHolomorphicEval,
        Polynomial.aeval_def]
      exact map_ratCast ((algebraMap LPSOriginalHolomorphicRing
        LPSOriginalHolomorphicFractionField).comp
          (algebraMap ℂ LPSOriginalHolomorphicRing)) q
    · simp [lpsOriginalJHolomorphicEvalQ, lpsOriginalJHolomorphicEval,
        Polynomial.aeval_def, lpsOriginalJInFractionField]
  exact RingHom.congr_fun he P

/-- Every subfield containing literal j contains the actual embedded rational function field Q(j). -/
lemma lpsOriginalJFractionEmbeddingQ_mem (S : Subfield LPSOriginalHolomorphicFractionField)
    (hj : lpsOriginalJInFractionField ∈ S) (a : FractionRing (Polynomial ℚ)) :
    lpsOriginalJFractionEmbeddingQ a ∈ S := by
  have hm (P : Polynomial ℚ) :
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalQ P) ∈ S := by
    rw [lpsOriginalJHolomorphicEvalQ_localization]
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [Polynomial.eval₂_add]; exact S.add_mem hP hQ
    | monomial n q =>
      rw [Polynomial.eval₂_monomial]
      exact S.mul_mem (by simpa only [eq_ratCast] using
        (SubfieldClass.ratCast_mem S q)) (S.pow_mem hj n)
  obtain ⟨A, B, _, hAB⟩ := IsFractionRing.div_surjective (Polynomial ℚ) a
  rw [←hAB, map_div₀, lpsOriginalJFractionEmbeddingQ_polynomial,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  exact S.div_mem (hm A) (hm B)

/-- The actual existing Q(j,j_N) intermediate field is the literal subfield closure of its two generators. -/
lemma lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield =
      Subfield.closure {lpsOriginalJInFractionField, lpsOriginalJNInFractionField N hN} := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply le_antisymm
  · intro x hx
    change x ∈ IntermediateField.adjoin (FractionRing (Polynomial ℚ))
      {lpsOriginalJNInFractionField N hN} at hx
    let S := Subfield.closure {lpsOriginalJInFractionField, lpsOriginalJNInFractionField N hN}
    have hj : lpsOriginalJInFractionField ∈ S := Subfield.subset_closure (by simp)
    refine IntermediateField.adjoin_induction (FractionRing (Polynomial ℚ))
      (fun y hy => ?_) (fun a => ?_)
      (fun y z _ _ hy hz => S.add_mem hy hz)
      (fun y _ hy => S.inv_mem hy)
      (fun y z _ _ hy hz => S.mul_mem hy hz) hx
    · have he := Set.mem_singleton_iff.mp hy
      subst y
      exact Subfield.subset_closure (by simp)
    · exact lpsOriginalJFractionEmbeddingQ_mem S hj a
  · apply Subfield.closure_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      have he : lpsOriginalJInFractionField = lpsOriginalJFractionEmbeddingQ
          (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X) := by
        rw [lpsOriginalJFractionEmbeddingQ_polynomial, lpsOriginalJHolomorphicEvalQ_localization]
        simp
      rw [he]
      exact IntermediateField.algebraMap_mem _ _
    · have he := Set.mem_singleton_iff.mp hx
      subst x
      exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)

/-- Actual Fricke pullback preserves the actual rational generated field at every positive level. -/
lemma lpsOriginalGeneratedFunctionFieldQ_fricke_map (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
        (lpsOriginalFrickeMatrix_pos N hN)).toRingHom =
          (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  simp only [lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure, RingHom.map_field_closure,
    Set.image_insert_eq, Set.image_singleton, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, lpsOriginalPositiveFractionPullback_fricke_j,
    lpsOriginalPositiveFractionPullback_fricke_jN, Set.pair_comm]

/-- Actual composition of positive integer dilations on the upper half plane. -/
lemma lpsOriginalDilation_product (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (τ : ℍ) :
    lpsE2AffineMatrix N hN 0 • (lpsE2AffineMatrix p hp 0 • τ) =
      lpsE2AffineMatrix (N*p) (Nat.mul_pos hN hp) 0 • τ := by
  apply UpperHalfPlane.ext
  simp only [lpsOriginalJDilated_coe, Nat.cast_mul, mul_assoc]

/-- Actual dilation pullback on the ambient holomorphic fraction field. -/
def lpsOriginalDilationFractionPullback (p : ℕ) (hp : 0 < p) :
    LPSOriginalHolomorphicFractionField ≃+* LPSOriginalHolomorphicFractionField :=
  lpsOriginalPositiveFractionPullback (lpsE2AffineMatrix p hp 0)
    (by rw [lpsE2AffineMatrix_det]; exact_mod_cast hp)

lemma lpsOriginalDilationFractionPullback_j (p : ℕ) (hp : 0 < p) :
    lpsOriginalDilationFractionPullback p hp lpsOriginalJInFractionField =
      lpsOriginalJNInFractionField p hp := by
  rw [lpsOriginalDilationFractionPullback, lpsOriginalJInFractionField,
    lpsOriginalPositiveFractionPullback_localization]
  rfl

lemma lpsOriginalPositiveHolomorphicPullback_dilation_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalPositiveHolomorphicPullback (lpsE2AffineMatrix p hp 0)
      (by rw [lpsE2AffineMatrix_det]; exact_mod_cast hp)
      (lpsOriginalJNHolomorphic N hN) =
        lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp) := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 •
    (lpsE2AffineMatrix p hp 0 • τ)) =
      lpsOriginalJInvariant (lpsE2AffineMatrix (N*p) (Nat.mul_pos hN hp) 0 • τ)
  rw [lpsOriginalDilation_product]

lemma lpsOriginalDilationFractionPullback_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalDilationFractionPullback p hp (lpsOriginalJNInFractionField N hN) =
      lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp) := by
  rw [lpsOriginalDilationFractionPullback, lpsOriginalJNInFractionField,
    lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_dilation_jN]
  rfl

/-- The genuine two embedded images agree: dilation equals product-level Fricke on the source generated field. -/
lemma lpsOriginalGeneratedFunctionFieldQ_dilation_image_eq_fricke
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p hp).toRingHom =
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalPositiveFractionPullback
        (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
        (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  simp only [lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure,
    RingHom.map_field_closure, Set.image_insert_eq, Set.image_singleton,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    lpsOriginalDilationFractionPullback_j, lpsOriginalDilationFractionPullback_jN,
    lpsOriginalPositiveFractionPullback_fricke_j,
    lpsOriginalPositiveFractionPullback_fricke_product_jN N p hN hp, Set.pair_comm]

/-- Actual dilation image lies in the same original product-level rational field. -/
lemma lpsOriginalGeneratedFunctionFieldQ_dilation_image_le
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p hp).toRingHom ≤
        (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
    (lpsOriginalDilationFractionPullback p hp).toRingHom ≤
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield
  rw [lpsOriginalGeneratedFunctionFieldQ_dilation_image_eq_fricke]
  have hle := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.mp hy
  have hm := Subfield.map_mem_map
    (lpsOriginalPositiveFractionPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))).toRingHom
    (s := (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield)
    (x := x)
  rw [lpsOriginalGeneratedFunctionFieldQ_fricke_map] at hm
  exact hm.mpr (hle hx)

/-- The second actual Hecke pullback has relative degree p+1, measured in its literal embedded image. -/
lemma lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p (Fact.out : p.Prime).pos).toRingHom).relfinrank
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalGeneratedFunctionFieldQ_dilation_image_eq_fricke]
  have h := Subfield.relfinrank_map_map
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield
    (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield
    (lpsOriginalPositiveFractionPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))).toRingHom
  rw [lpsOriginalGeneratedFunctionFieldQ_fricke_map] at h
  exact h.trans (lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN)

/-- The second original rational Hecke map is the actual dilation restricted to the proved generated fields. -/
def lpsOriginalRationalHeckePullback (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →+*
      lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact
    { toFun := fun x => ⟨lpsOriginalDilationFractionPullback p hp x,
        lpsOriginalGeneratedFunctionFieldQ_dilation_image_le N p hN hp h4N
          (Subfield.mem_map.mpr ⟨x, x.property, rfl⟩)⟩
      map_one' := Subtype.ext (map_one (lpsOriginalDilationFractionPullback p hp))
      map_mul' := fun x y => Subtype.ext (map_mul (lpsOriginalDilationFractionPullback p hp)
        (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField))
      map_zero' := Subtype.ext (map_zero (lpsOriginalDilationFractionPullback p hp))
      map_add' := fun x y => Subtype.ext (map_add (lpsOriginalDilationFractionPullback p hp)
        (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField)) }

lemma lpsOriginalRationalHeckePullback_coe (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ x : lpsOriginalGeneratedFunctionFieldQ N hN,
      ((lpsOriginalRationalHeckePullback N p hN hp h4N x :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) = lpsOriginalDilationFractionPullback p hp x := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro x
  rfl

lemma lpsOriginalRationalHeckePullback_injective (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    Function.Injective (lpsOriginalRationalHeckePullback N p hN hp h4N) :=
  (lpsOriginalRationalHeckePullback N p hN hp h4N).injective

/-- Literal original j belongs to the existing rational field generated by j and j_N. -/
lemma lpsOriginalJInFractionField_mem_generatedQ (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalJInFractionField ∈ lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change lpsOriginalJInFractionField ∈ (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield
  rw [lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure]
  exact Subfield.subset_closure (by simp)

/-- The restricted second Hecke map really sends the first generator j to j_p. -/
lemma lpsOriginalRationalHeckePullback_j (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalHeckePullback N p hN hp h4N
      ⟨lpsOriginalJInFractionField, lpsOriginalJInFractionField_mem_generatedQ N hN⟩ :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) = lpsOriginalJNInFractionField p hp := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalHeckePullback_coe]
  exact lpsOriginalDilationFractionPullback_j p hp

/-- The restricted second Hecke map really sends the second generator j_N to j_Np. -/
lemma lpsOriginalRationalHeckePullback_jN (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalHeckePullback N p hN hp h4N
      ⟨lpsOriginalJNInFractionField N hN,
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) =
            lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalHeckePullback_coe]
  exact lpsOriginalDilationFractionPullback_jN N p hN hp

/-- The actual restricted Hecke map has exactly the proved ambient dilation image. -/
lemma lpsOriginalRationalHeckePullback_fieldRange (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield.subtype.comp
      (lpsOriginalRationalHeckePullback N p hN hp h4N)).fieldRange =
        (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
          (lpsOriginalDilationFractionPullback p hp).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  ext y
  change (∃ x : lpsOriginalGeneratedFunctionFieldQ N hN,
    lpsOriginalDilationFractionPullback p hp (x : LPSOriginalHolomorphicFractionField) = y) ↔
      ∃ x ∈ (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield,
        lpsOriginalDilationFractionPullback p hp x = y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x.property, hx⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨⟨x, hx⟩, he⟩

/-- The second genuine original rational Hecke map has image-relative degree p+1. -/
lemma lpsOriginalPrimeRationalHeckePullback_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (((lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield.subtype.comp
      (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N)).fieldRange).relfinrank
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalHeckePullback_fieldRange]
  exact lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN

end
end QEC.Coding.TannerLiftedProduct
