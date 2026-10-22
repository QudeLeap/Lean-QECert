import QEC.Coding.AlgebraicGeometry.Differentials.KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import QEC.Coding.AlgebraicGeometry.Places.ValuationCentres

/-!
# Actual affine Kahler images from localization

Construct genuine affine differential preimages using localized Kahler numerators and denominators, an actual maximal ideal over the denominator ideal, and height-one valuation-ring transport preserving literal field values.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
This proves actual affine preimages; overlap compatibility, torsion/smoothness,
global differential/sheaf/GAGA comparison, good reduction, Hecke/Frobenius/Weil
and the exact public quantum-family theorem remain further proof obligations.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section

section module
variable (A W : Type*) [CommRing A] [AddCommGroup W] [Module A W]
/-- Denominators outside every maximal ideal force actual submodule membership via the ideal of clearing scalars. -/
lemma submodule_mem_of_forall_maximal_clear (U : Submodule A W) (omega : W)
    (h : ∀ (P : Ideal A) [P.IsMaximal], ∃ s : A, s ∉ P ∧ s • omega ∈ U) :
    omega ∈ U := by
  classical
  let I : Ideal A := U.comap (LinearMap.toSpanSingleton A W omega)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P,hP,hIP⟩ := I.exists_le_maximal hne
    let : P.IsMaximal := hP
    obtain ⟨s,hs,hu⟩ := h P
    apply hs
    apply hIP
    change s • omega ∈ U
    exact hu
  simpa only [I,Submodule.mem_comap,LinearMap.toSpanSingleton_apply,one_smul] using
    (I.eq_top_iff_one.mp hI)
end module

section localization
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
/-- A genuine localized differential preimage supplies a denominator and numerator in the actual affine field image. -/
lemma kaehler_field_map_range_localization_clear (S : Submonoid A) [IsLocalization S B]
    (omega : KaehlerDifferential R K)
    (h : omega ∈ (KaehlerDifferential.map R R B K).range) :
    ∃ s : S, s.val • omega ∈ (KaehlerDifferential.map R R A K).range := by
  rcases h with ⟨eta,rfl⟩
  obtain ⟨⟨tau,s⟩,he⟩ := IsLocalizedModule.surj S (KaehlerDifferential.map R R A B) eta
  change s.val • eta = KaehlerDifferential.map R R A B tau at he
  refine ⟨s,tau,?_⟩
  calc
    KaehlerDifferential.map R R A K tau =
        KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B tau) :=
      kaehler_field_map_comp R A B K tau
    _ = KaehlerDifferential.map R R B K (s.val • eta) := congrArg _ he.symm
    _ = s.val • KaehlerDifferential.map R R B K eta :=
      ((KaehlerDifferential.map R R B K).restrictScalars A).map_smul s.val eta
end localization

section allMaximal
variable (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K]
variable (B : ∀ (P : Ideal A) [P.IsMaximal], Type*)
variable [∀ (P : Ideal A) [P.IsMaximal], CommRing (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsLocalization.AtPrime (B P) P]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra R (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], Algebra (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower R (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], IsScalarTower A (B P) K]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R A (B P)]
variable [∀ (P : Ideal A) [P.IsMaximal], SMulCommClass R (B P) K]
/-- The actual affine differential image equals membership in the actual images from every maximal localization. -/
lemma kaehler_field_map_range_iff_allMaximal
    (omega : KaehlerDifferential R K) :
    omega ∈ (KaehlerDifferential.map R R A K).range ↔
      ∀ (P : Ideal A) [P.IsMaximal], omega ∈ (KaehlerDifferential.map R R (B P) K).range := by
  constructor
  · rintro ⟨tau,rfl⟩ P hP
    exact ⟨KaehlerDifferential.map R R A (B P) tau,
      (kaehler_field_map_comp R A (B P) K tau).symm⟩
  · intro h
    apply submodule_mem_of_forall_maximal_clear A (KaehlerDifferential R K)
      (KaehlerDifferential.map R R A K).range omega
    intro P hP
    obtain ⟨s,hs⟩ := kaehler_field_map_range_localization_clear R A (B P) K
      P.primeCompl omega (h P)
    exact ⟨s.val,s.property,hs⟩
end allMaximal

end
end QEC.Coding.AlgebraicGeometry


namespace QEC.Coding.AlgebraicGeometry
noncomputable section

/-- Equal valuation subrings of one field are ring equivalent while retaining literal ambient values. -/
def kaehlerValuationSubringEquiv {K : Type*} [Field K]
    (S T : ValuationSubring K) (h : S = T) : S ≃+* T where
  toFun x := ⟨x.val, by rw [← h]; exact x.property⟩
  invFun x := ⟨x.val, by rw [h]; exact x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]

/-- Transport canonical height-one localization to the same actual valuation ring and clear a genuine differential denominator. -/
lemma kaehler_field_map_range_heightOne_clear
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) (omega : KaehlerDifferential R K)
    (h : omega ∈ (KaehlerDifferential.map R R T K).range) :
    ∃ s : A, s ∉ H.asIdeal ∧ s • omega ∈ (KaehlerDifferential.map R R A K).range := by
  let S := H.valuationSubringAtPrime K
  let e : S ≃+* T := kaehlerValuationSubringEquiv S T heq
  let : Algebra A T := (e.toRingHom.comp (algebraMap A S)).toAlgebra
  let : IsLocalization H.asIdeal.primeCompl T :=
    (IsLocalization.isLocalization_iff_of_ringEquiv H.asIdeal.primeCompl e).mp inferInstance
  let : IsScalarTower A T K := .of_algebraMap_eq fun a => by
    rw [hT]
    exact IsScalarTower.algebraMap_apply A S K a
  let : IsScalarTower R A T := .of_algebraMap_eq fun r => by
    apply Subtype.val_injective
    change (algebraMap R T r).val = (e (algebraMap A S (algebraMap R A r))).val
    calc
      _ = algebraMap T K (algebraMap R T r) := (hT _).symm
      _ = algebraMap R K r := (IsScalarTower.algebraMap_apply R T K r).symm
      _ = algebraMap A K (algebraMap R A r) := IsScalarTower.algebraMap_apply R A K r
      _ = _ := IsScalarTower.algebraMap_apply A S K _
  let : SMulCommClass R A T :=
    { smul_comm := fun r a t => by simp only [Algebra.smul_def]; ring }
  obtain ⟨s,hs⟩ := kaehler_field_map_range_localization_clear R A T K
    H.asIdeal.primeCompl omega h
  exact ⟨s.val,s.property,hs⟩

/-- An actual affine differential preimage maps into the same-field valuation ring at its genuine height-one centre. -/
lemma kaehler_field_map_range_le_heightOne
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) (omega : KaehlerDifferential R K)
    (h : omega ∈ (KaehlerDifferential.map R R A K).range) :
    omega ∈ (KaehlerDifferential.map R R T K).range := by
  let S := H.valuationSubringAtPrime K
  let e : S ≃+* T := kaehlerValuationSubringEquiv S T heq
  let : Algebra A T := (e.toRingHom.comp (algebraMap A S)).toAlgebra
  let : IsScalarTower A T K := .of_algebraMap_eq fun a => by
    rw [hT]
    exact IsScalarTower.algebraMap_apply A S K a
  let : IsScalarTower R A T := .of_algebraMap_eq fun r => by
    apply Subtype.val_injective
    change (algebraMap R T r).val = (e (algebraMap A S (algebraMap R A r))).val
    calc
      _ = algebraMap T K (algebraMap R T r) := (hT _).symm
      _ = algebraMap R K r := (IsScalarTower.algebraMap_apply R T K r).symm
      _ = algebraMap A K (algebraMap R A r) := IsScalarTower.algebraMap_apply R A K r
      _ = _ := IsScalarTower.algebraMap_apply A S K _
  let : SMulCommClass R A T :=
    { smul_comm := fun r a t => by simp only [Algebra.smul_def]; ring }
  rcases h with ⟨tau,rfl⟩
  exact ⟨KaehlerDifferential.map R R A T tau,
    (kaehler_field_map_comp R A T K tau).symm⟩
end
end
end QEC.Coding.AlgebraicGeometry
