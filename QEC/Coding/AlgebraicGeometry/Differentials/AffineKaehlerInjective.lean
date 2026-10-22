import QEC.Coding.AlgebraicGeometry.Differentials.AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Affine differential kernel clearing and localization

Transport compatible actual height-one localizations, derive essential finite type, clear genuine differential kernel elements, and transport injection through real Kahler localization. Actual original consumers prove every local or affine injection premise.

Derived internal PK22 ex:Xpq machinery, pinned main.tex484–486, for parent #449.
This proves actual differential injection and compatible affine preimages.
Genuine global differential sheaf/gluing/GAGA, good reduction, Hecke/Frobenius/Weil
and the exact arbitrary-finite-field public quantum family remain outstanding.
No public node changes status.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [IsDedekindDomain A] [IsFractionRing A K] [Algebra.EssFiniteType R A]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K]
/-- Transport actual height-one localization and compatible literal scalar maps to derive essential finite type of the same-field valuation ring. -/
lemma heightOne_valuation_essFiniteType
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) :
    Algebra.EssFiniteType R T := by
  let S := H.valuationSubringAtPrime K
  let e : S ≃+* T := kaehlerValuationSubringEquiv S T heq
  let : Algebra A T := (e.toRingHom.comp (algebraMap A S)).toAlgebra
  let : IsLocalization H.asIdeal.primeCompl T :=
    (IsLocalization.isLocalization_iff_of_ringEquiv H.asIdeal.primeCompl e).mp inferInstance
  let : IsScalarTower R A T := .of_algebraMap_eq fun r => by
    apply Subtype.val_injective
    change (algebraMap R T r).val = (e (algebraMap A S (algebraMap R A r))).val
    calc
      _ = algebraMap T K (algebraMap R T r) := (hT _).symm
      _ = algebraMap R K r := (IsScalarTower.algebraMap_apply R T K r).symm
      _ = algebraMap A K (algebraMap R A r) := IsScalarTower.algebraMap_apply R A K r
      _ = _ := IsScalarTower.algebraMap_apply A S K _
  let : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T H.asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp R A T
end
end QEC.Coding.AlgebraicGeometry


namespace QEC.Coding.AlgebraicGeometry
noncomputable section
section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]

/-- A proved local differential injection clears an affine kernel element by a scalar outside its actual height-one centre. -/
lemma kaehler_field_map_zero_heightOne_clear
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val)
    (hTin : Function.Injective (KaehlerDifferential.map R R T K))
    (tau : KaehlerDifferential R A)
    (hzero : KaehlerDifferential.map R R A K tau = 0) :
    ∃ s : A, s ∉ H.asIdeal ∧ s • tau = 0 := by
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
  have ht : KaehlerDifferential.map R R A T tau = 0 := by
    apply hTin
    rw [map_zero, ← kaehler_field_map_comp R A T K]
    exact hzero
  obtain ⟨s,hs⟩ := (IsLocalizedModule.eq_zero_iff H.asIdeal.primeCompl
    (KaehlerDifferential.map R R A T)).mp ht
  change s.val • tau = 0 at hs
  exact ⟨s.val,s.property,hs⟩
end
end
end QEC.Coding.AlgebraicGeometry


namespace QEC.Coding.AlgebraicGeometry
noncomputable section
section localization
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]
/-- Actual Kahler localization and its inverted denominators transport a proved affine differential injection to the localized ring. -/
lemma kaehler_field_map_injective_localization
    (S : Submonoid A) [IsLocalization S B]
    (hA : Function.Injective (KaehlerDifferential.map R R A K)) :
    Function.Injective (KaehlerDifferential.map R R B K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro eta heta
  obtain ⟨⟨tau,s⟩,he⟩ := IsLocalizedModule.surj S (KaehlerDifferential.map R R A B) eta
  change s.val • eta = KaehlerDifferential.map R R A B tau at he
  have htau : KaehlerDifferential.map R R A K tau = 0 := by
    calc
      _ = KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B tau) :=
        kaehler_field_map_comp R A B K tau
      _ = KaehlerDifferential.map R R B K (s.val • eta) := congrArg _ he.symm
      _ = s.val • KaehlerDifferential.map R R B K eta :=
        ((KaehlerDifferential.map R R B K).restrictScalars A).map_smul s.val eta
      _ = 0 := by rw [heta,smul_zero]
  have htau0 : tau = 0 := hA (htau.trans (map_zero _).symm)
  rw [htau0,map_zero] at he
  have hu := IsLocalization.map_units B s
  exact hu.smul_eq_zero.mp (by rw [IsScalarTower.algebraMap_smul B]; exact he)
end localization
end
end QEC.Coding.AlgebraicGeometry
