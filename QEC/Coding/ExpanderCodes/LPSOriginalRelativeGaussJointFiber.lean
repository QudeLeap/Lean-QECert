import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual Gauss fiber as a closed Frobenius correspondence

The proved native residue coordinate is not a second Frobenius power of itself.
Use it to separate the two Frobenius images by the product idempotents and prove
that the actual first and second fiber maps jointly generate the literal fiber
ring. Derive canonical prime-field linearity, construct the joint tensor map
and prove its surjectivity. Prove its entire diagram with both Frobenius graph
maps, its pure-tensor formula and the intersection formula for its kernel.
The actual affine spectrum map is therefore a closed immersion.

These derived internal prerequisites are motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486). This is the actual generic Gauss normalization fiber,
not a global correspondence cycle or a smooth proper curve. Global cycles,
good reduction, Weil bounds, principal-level spectrum and the exact explicit
arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449
remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

lemma lpsOriginalFrobeniusPair_subring_eq_top
    {K : Type*} [Field K] (p : ℕ) (S : Subring (K × K))
    (hfirst : ∀ a : K, (a, a^p) ∈ S)
    (hsecond : ∀ a : K, (a^p, a) ∈ S)
    (u : K) (hu : (u^p)^p ≠ u) : S = ⊤ := by
  let d := u - (u^p)^p
  have hd : d ≠ 0 := sub_ne_zero.mpr hu.symm
  have h10 : ((1 : K), (0 : K)) ∈ S := by
    have h := S.mul_mem (hfirst d⁻¹) (S.sub_mem (hfirst u) (hsecond (u^p)))
    have he : (d⁻¹, (d⁻¹)^p) * ((u, u^p) - ((u^p)^p, u^p)) =
        ((1 : K), (0 : K)) := by
      apply Prod.ext
      · change d⁻¹ * (u - (u^p)^p) = 1
        exact inv_mul_cancel₀ hd
      · simp
    exact he ▸ h
  have h01 : ((0 : K), (1 : K)) ∈ S := by
    have h := S.sub_mem S.one_mem h10
    have he : (1 : K × K) - ((1 : K), (0 : K)) = ((0 : K), (1 : K)) := by
      ext <;> simp
    exact he ▸ h
  apply top_unique
  intro x _hx
  have h := S.add_mem (S.mul_mem (hfirst x.1) h10) (S.mul_mem (hsecond x.2) h01)
  have he : (x.1, x.1^p) * ((1 : K), (0 : K)) +
      (x.2^p, x.2) * ((0 : K), (1 : K)) = x := by
    ext <;> simp
  exact he ▸ h

lemma lpsOriginalGaussFrobeniusPair_closure_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    Subring.closure (Set.range ((RingHom.id (LPSOriginalGaussAffineOrder N hN p ⧸ q)).prod
      (frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p)) ∪
      Set.range ((frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p).prod
        (RingHom.id (LPSOriginalGaussAffineOrder N hN p ⧸ q)))) = ⊤ := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  apply lpsOriginalFrobeniusPair_subring_eq_top p _
    (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩))
    (lpsOriginalGaussMaximalResidueJN N hN p q)
  exact lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q
    ((lpsOriginalGaussMaximalResidueJN N hN p q)^p)

lemma lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Subring.closure
      (Set.range (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) ∪
        Set.range (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q)) = ⊤ := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  let S := Subring.closure
    (Set.range (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) ∪
      Set.range (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q))
  have hT : S.comap e.symm.toRingHom = ⊤ := by
    refine lpsOriginalFrobeniusPair_subring_eq_top p _ ?_ ?_
      (lpsOriginalGaussMaximalResidueJN N hN p q) ?_
    · intro a
      change e.symm (a, a^p) ∈ S
      have h := RingHom.congr_fun
        (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
          N p hNp h4N hN hpN q) a
      change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q a) =
        (a, a^p) at h
      rw [← h, e.symm_apply_apply]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · intro a
      change e.symm (a^p, a) ∈ S
      have h := RingHom.congr_fun
        (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
          N p hNp h4N hN hpN q) a
      change e (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q a) =
        (a^p, a) at h
      rw [← h, e.symm_apply_apply]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
    · exact lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q
        ((lpsOriginalGaussMaximalResidueJN N hN p q)^p)
  apply top_unique
  intro x _hx
  have h : e x ∈ S.comap e.symm.toRingHom := by rw [hT]; trivial
  change e.symm (e x) ∈ S at h
  simpa using h

def lpsOriginalPrimeFieldAlgHomOfRingHom
    (p : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    [Algebra (ZMod p) R] [Algebra (ZMod p) S] (f : R →+* S) : R →ₐ[ZMod p] S :=
  { f with
    commutes' := by
      intro r
      exact RingHom.congr_fun
        (Subsingleton.elim (f.comp (algebraMap (ZMod p) R)) (algebraMap (ZMod p) S)) r }

lemma lpsOriginalJointTensorMap_surjective_of_jointClosure
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Subring.closure (Set.range f ∪ Set.range g) = ⊤) :
    Function.Surjective (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)) := by
  let t := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  apply (RingHom.range_eq_top (f := t.toRingHom)).mp
  apply top_unique
  rw [← h]
  apply Subring.closure_le.mpr
  rintro x (hx | hx)
  · obtain ⟨a, rfl⟩ := hx
    exact ⟨a ⊗ₜ[R] (1 : B), by simp [t]⟩
  · obtain ⟨b, rfl⟩ := hx
    exact ⟨(1 : A) ⊗ₜ[R] b, by simp [t]⟩

def lpsOriginalRelativeGaussNormalizationFiberJointTensorMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    (K ⊗[ZMod p] K) →ₐ[ZMod p] F := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  exact Algebra.TensorProduct.lift (R := ZMod p) (S := ZMod p) (A := K) (B := K) (C := F)
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (R := K) (S := F)
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q))
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (R := K) (S := F)
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q))
    (fun _ _ => Commute.all _ _)

lemma lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  exact lpsOriginalJointTensorMap_surjective_of_jointClosure (R := ZMod p) (A := K) (B := K) (C := F) _ _
    (lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top N p hNp h4N hN hpN q)

def lpsOriginalFrobeniusFirstTensorGraphMap
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] : (K ⊗[ZMod p] K) →ₐ[ZMod p] K :=
  Algebra.TensorProduct.lift (AlgHom.id (ZMod p) K)
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (frobenius K p)) (fun _ _ => Commute.all _ _)

def lpsOriginalFrobeniusSecondTensorGraphMap
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] : (K ⊗[ZMod p] K) →ₐ[ZMod p] K :=
  Algebra.TensorProduct.lift
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (frobenius K p))
    (AlgHom.id (ZMod p) K) (fun _ _ => Commute.all _ _)

lemma lpsOriginalFrobeniusFirstTensorGraphMap_tmul
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a b : K) :
    lpsOriginalFrobeniusFirstTensorGraphMap p K (a ⊗ₜ[ZMod p] b) = a * b^p := by
  rfl

lemma lpsOriginalFrobeniusSecondTensorGraphMap_tmul
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a b : K) :
    lpsOriginalFrobeniusSecondTensorGraphMap p K (a ⊗ₜ[ZMod p] b) = a^p * b := by
  rfl

lemma lpsOriginalRingHom_prod_ker
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) :
    RingHom.ker (f.prod g) = RingHom.ker f ⊓ RingHom.ker g := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_inf, RingHom.prod_apply, Prod.mk_eq_zero]

lemma lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_generatedDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom =
        (lpsOriginalFrobeniusFirstTensorGraphMap p K).toRingHom.prod
          (lpsOriginalFrobeniusSecondTensorGraphMap p K).toRingHom := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro a
    change e ((lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q a) *
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q 1)) =
        (a * 1^p, a^p * 1)
    have h := RingHom.congr_fun
      (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first N p hNp h4N hN hpN q) a
    change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q a) =
      (a, a^p) at h
    simpa only [map_one, mul_one, one_pow] using h
  · apply RingHom.ext
    intro b
    change e ((lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q 1) *
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q b)) =
        (1 * b^p, 1^p * b)
    have h := RingHom.congr_fun
      (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second N p hNp h4N hN hpN q) b
    change e (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q b) =
      (b^p, b) at h
    simpa only [map_one, one_mul, one_pow] using h

lemma lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_tmul
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (a b : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q
        (a ⊗ₜ[ZMod p] b)) = (a * b^p, a^p * b) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  have h := RingHom.congr_fun
    (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_generatedDiagram N p hNp h4N hN hpN q)
    (a ⊗ₜ[ZMod p] b)
  exact h

lemma lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_ker
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    RingHom.ker (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom =
      RingHom.ker (lpsOriginalFrobeniusFirstTensorGraphMap p K).toRingHom ⊓
        RingHom.ker (lpsOriginalFrobeniusSecondTensorGraphMap p K).toRingHom := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  rw [← RingHom.ker_comp_of_injective (f := e.toRingHom)
    (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom e.injective,
    lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_generatedDiagram]
  exact lpsOriginalRingHom_prod_ker _ _

lemma lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_isClosedImmersion
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom)) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  apply AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
  exact lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_surjective N p hNp h4N hN hpN q

end
end QEC.Coding.TannerLiftedProduct
