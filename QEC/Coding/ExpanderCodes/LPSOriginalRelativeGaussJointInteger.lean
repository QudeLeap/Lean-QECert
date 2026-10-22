import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussJointFiber
import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The actual Gauss integer tensor correspondence

The actual first and second projection images jointly generate the literal
relative Gauss normalization: coefficients generate the lower order and the
second projection supplies the native adjoining root. Its tensor presentation
over the canonical integer scalar actions is therefore surjective and induces
an actual affine spectrum closed immersion, with both entire projection diagrams.
The actual monic Hecke polynomial supplies a basis with p+1 vectors for the
first action. The proved Fricke ring equivalences and whole coefficient diagram
transfer freeness and rank to the distinct second action. Both actual spectrum
projections are finite and flat.

These are derived internal prerequisites motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486). These rings are the actual generic Gauss orders; this is
not yet a global smooth proper modular curve or a global correspondence cycle.
Global models, good reduction, Weil bounds, principal-level spectrum and the
exact explicit arbitrary-finite-field qLDPC family remain separate obligations.
Parent issue449 remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

lemma lpsOriginalAdjoinRoot_subring_eq_top
    {R : Type*} [CommRing R] (f : Polynomial R) (S : Subring (AdjoinRoot f))
    (hcoeff : ∀ r : R, AdjoinRoot.of f r ∈ S) (hroot : AdjoinRoot.root f ∈ S) : S = ⊤ := by
  have hP (P : Polynomial R) : Polynomial.aeval (AdjoinRoot.root f) P ∈ S := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simpa only [map_add] using S.add_mem hP hQ
    | monomial n r => simpa using S.mul_mem (hcoeff r) (S.pow_mem hroot n)
  apply top_unique
  intro x _hx
  induction x using AdjoinRoot.induction_on with
  | ih P => simpa only [AdjoinRoot.aeval_eq] using hP P

lemma lpsOriginalRelativeGaussNormalization_jointClosure_eq_top
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Subring.closure (Set.range (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ∪
      Set.range (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN)) = ⊤ := by
  let e := lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
  let S := Subring.closure
    (Set.range (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ∪
      Set.range (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))
  have hT : S.comap e.toRingHom = ⊤ := by
    apply lpsOriginalAdjoinRoot_subring_eq_top (lpsOriginalRelativeGaussHeckePolynomial N hN p)
    · intro r
      exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · change lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN ∈ S
      rw [← lpsOriginalRelativeGaussNormalizationSecondOrderMap_root]
      exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  apply top_unique
  intro x _hx
  have h : e.symm x ∈ S.comap e.toRingHom := by rw [hT]; trivial
  change e (e.symm x) ∈ S at h
  simpa using h

def lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    (LPSOriginalGaussAffineOrder N hN p ⊗[ℤ] LPSOriginalGaussAffineOrder N hN p) →ₐ[ℤ] LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  exact Algebra.TensorProduct.lift
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).toIntAlgHom
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).toIntAlgHom
    (fun _ _ => Commute.all _ _)

lemma lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    Function.Surjective (lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN) := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  exact lpsOriginalJointTensorMap_surjective_of_jointClosure
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).toIntAlgHom
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).toIntAlgHom
    (lpsOriginalRelativeGaussNormalization_jointClosure_eq_top N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_tmul
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (u v : LPSOriginalGaussAffineOrder N hN p) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN (u ⊗ₜ[ℤ] v) =
      lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN u *
        lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN v := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  rfl

lemma lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_comp_first
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    (lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)) =
        lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  apply RingHom.ext
  intro u
  change (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN u) *
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN 1) = _
  rw [map_one, mul_one]

lemma lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_comp_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    (lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom =
        lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  apply RingHom.ext
  intro v
  change (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN 1) *
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN v) = _
  rw [map_one, one_mul]

lemma lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_isClosedImmersion
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap N p hNp h4N hN hpN).toRingHom)) := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  apply AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
  exact lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap_surjective N p hNp h4N hN hpN

lemma lpsOriginalFreeOfRingEquivs
    {A₁ B₁ A₂ B₂ : Type*} [CommSemiring A₁] [CommSemiring B₁]
    [CommSemiring A₂] [CommSemiring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap A₁ B₁))
    [Module.Free A₁ B₁] : Module.Free A₂ B₂ := by
  let : RingHomInvPair e₁.toRingHom e₁.symm.toRingHom := RingHomInvPair.of_ringEquiv e₁
  let : RingHomInvPair e₁.symm.toRingHom e₁.toRingHom := RingHomInvPair.of_ringEquiv_symm e₁
  let e : B₁ ≃ₛₗ[e₁.toRingHom] B₂ :=
    { e₂.toAddEquiv with
      map_smul' := by
        intro r x
        change e₂ (r • x) = e₁ r • e₂ x
        simp only [Algebra.smul_def, map_mul]
        exact congrArg (fun y => y * e₂ x) (RingHom.congr_fun he r).symm }
  exact Module.Free.of_equiv (σ' := e₁.symm.toRingHom) e

lemma lpsOriginalRelativeGaussHeckePolynomial_natDegree
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (lpsOriginalRelativeGaussHeckePolynomial N hN p).natDegree = p + 1 := by
  let := lpsOriginalGaussAffineOrder_domain N hN p
  rw [lpsOriginalRelativeGaussHeckePolynomial,
    (lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).natDegree_map,
    lpsOriginalPrimeIntegerPolynomial_degree]

def lpsOriginalRelativeGaussNormalizationFirstBasis
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    Module.Basis (Fin (p+1)) (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  exact ((AdjoinRoot.powerBasis' (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p)).basis.map
    (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN).toLinearEquiv).reindex
    (finCongr (lpsOriginalRelativeGaussHeckePolynomial_natDegree N hN p))

lemma lpsOriginalRelativeGaussNormalization_firstFree
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    Module.Free (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  exact Module.Free.of_basis (lpsOriginalRelativeGaussNormalizationFirstBasis N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalization_secondFree
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    Module.Free (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let h := lpsOriginalRelativeGaussNormalization_firstFree N p hNp h4N hN hpN
  refine @lpsOriginalFreeOfRingEquivs R C R C _ _ _ _
    (lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN) (lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN)
    (lpsOriginalGaussFrickeRingEquiv N hN p hpN)
    (lpsOriginalRelativeGaussNormalizationFrickeRingEquiv N p hNp h4N hN hpN) ?_ h
  exact (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN).symm

lemma lpsOriginalRelativeGaussNormalization_firstFinrank
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    Module.finrank (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) = p+1 := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalGaussAffineOrder_domain N hN p
  simpa using Module.finrank_eq_card_basis (lpsOriginalRelativeGaussNormalizationFirstBasis N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalization_secondFinrank
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    Module.finrank (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) = p+1 := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  have h := @Algebra.finrank_eq_of_equiv_equiv R C _ _
    (lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN) R C _ _ (lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN)
    (lpsOriginalGaussFrickeRingEquiv N hN p hpN)
    (lpsOriginalRelativeGaussNormalizationFrickeRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN).symm
  exact h.symm.trans (lpsOriginalRelativeGaussNormalization_firstFinrank N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalization_firstFlat
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).Flat := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_firstFree N p hNp h4N hN hpN
  change Module.Flat (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)
  infer_instance

lemma lpsOriginalRelativeGaussNormalization_firstSpecFinite
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))) := by
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_firstFinite N p hNp h4N hN hpN
  change Module.Finite (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)
  infer_instance

lemma lpsOriginalRelativeGaussNormalization_firstSpecFlat
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))) := by
  apply AlgebraicGeometry.Flat.SpecMap_iff.mpr
  exact lpsOriginalRelativeGaussNormalization_firstFlat N p hNp h4N hN hpN

lemma lpsOriginalRelativeGaussNormalization_secondFlat
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).Flat := by
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_secondFree N p hNp h4N hN hpN
  change Module.Flat (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)
  infer_instance

lemma lpsOriginalRelativeGaussNormalization_secondSpecFinite
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))) := by
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_secondFinite N p hNp h4N hN hpN
  change Module.Finite (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)
  infer_instance

lemma lpsOriginalRelativeGaussNormalization_secondSpecFlat
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))) := by
  apply AlgebraicGeometry.Flat.SpecMap_iff.mpr
  exact lpsOriginalRelativeGaussNormalization_secondFlat N p hNp h4N hN hpN

end
end QEC.Coding.TannerLiftedProduct
