import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Differents under simultaneous localization

The local Artin--Schreier calculations used by the Garcia--Stichtenoth
normal-closure construction take place after localizing at one lower prime.
The upper ring must be localized by the image of that lower prime complement;
localizing at a single chosen upper prime need not be finite over the lower
DVR.  This file supplies the trace-dual basis calculation for the correct
simultaneous localization.

It introduces no tower, ramification, genus, divisor, or asymptotic
conclusion.
-/

open Module
open scoped nonZeroDivisors

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private theorem traceDual_one_span_eq_of_isLocalization
    (R S Rm Sm K L : Type*)
    [CommRing R] [CommRing S] [CommRing Rm] [CommRing Sm]
    [IsDomain R] [IsDomain S] [IsDomain Rm] [IsDomain Sm]
    [Field K] [Field L]
    [Algebra R S] [Algebra R Rm] [Algebra S Sm]
    [Algebra R Sm] [Algebra Rm Sm]
    [IsScalarTower R S Sm] [IsScalarTower R Rm Sm]
    [Algebra R K] [Algebra Rm K]
    [Algebra S L] [Algebra Sm L] [Algebra K L]
    [Algebra R L] [Algebra Rm L]
    [IsScalarTower R K L] [IsScalarTower Rm K L]
    [IsScalarTower R S L] [IsScalarTower Rm Sm L]
    [IsScalarTower S Sm L] [IsScalarTower R Sm L]
    [IsFractionRing R K] [IsFractionRing Rm K]
    [IsFractionRing S L] [IsFractionRing Sm L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Free R S] [Module.Finite R S]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    Submodule.span Sm
        (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      Submodule.traceDual Rm K (1 : Submodule Sm L) := by
  classical
  let b := Module.Free.chooseBasis R S
  let bK := b.localizationLocalization K R⁰ L
  let bm := b.localizationLocalization Rm M Sm
  let bmK := bm.localizationLocalization K Rm⁰ L
  letI : Finite (Module.Free.ChooseBasisIndex R S) :=
    Module.Finite.finite_basis b
  have hbK : bmK = bK := by
    apply DFunLike.coe_injective
    funext i
    simp only [bmK, bm, bK, Basis.localizationLocalization_apply]
    rw [IsScalarTower.algebraMap_apply S Sm L]
  have hb :
      (1 : Submodule S L).restrictScalars R =
        Submodule.span R (Set.range bK) := by
    rw [b.localizationLocalization_span K R⁰ L]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_one,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hbm :
      (1 : Submodule Sm L).restrictScalars Rm =
        Submodule.span Rm (Set.range bmK) := by
    rw [bm.localizationLocalization_span K Rm⁰ L]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_one,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hdual := Submodule.traceDual_span_of_basis R
    (1 : Submodule S L) bK hb
  have hdual_m := Submodule.traceDual_span_of_basis Rm
    (1 : Submodule Sm L) bmK hbm
  rw [show (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      ((Submodule.traceDual R K (1 : Submodule S L)).restrictScalars R : Set L) by
        rfl,
    hdual, Submodule.span_span_of_tower, ← hbK,
    ← Submodule.span_span_of_tower (R := Rm) (S := Sm), ← hdual_m]
  exact Submodule.span_eq _

private theorem dual_one_extendedHom_eq_of_isLocalization
    (R S Rm Sm K L : Type*)
    [CommRing R] [CommRing S] [CommRing Rm] [CommRing Sm]
    [IsDomain R] [IsDomain S] [IsDomain Rm] [IsDomain Sm]
    [Field K] [Field L]
    [Algebra R S] [Algebra R Rm] [Algebra S Sm]
    [Algebra R Sm] [Algebra Rm Sm]
    [IsScalarTower R S Sm] [IsScalarTower R Rm Sm]
    [Algebra R K] [Algebra Rm K]
    [Algebra S L] [Algebra Sm L] [Algebra K L]
    [Algebra R L] [Algebra Rm L]
    [IsScalarTower R K L] [IsScalarTower Rm K L]
    [IsScalarTower R S L] [IsScalarTower Rm Sm L]
    [IsScalarTower S Sm L] [IsScalarTower R Sm L]
    [IsFractionRing R K] [IsFractionRing Rm K]
    [IsFractionRing S L] [IsFractionRing Sm L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Free R S] [Module.Finite R S]
    [Module.IsTorsionFree S Sm]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rm]
    [IsIntegralClosure S R L] [IsIntegralClosure Sm Rm L]
    [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)).extendedHom L Sm =
      FractionalIdeal.dual Rm K (1 : FractionalIdeal Sm⁰ L) := by
  classical
  let hf : S⁰ ≤ Submonoid.comap (algebraMap S Sm) Sm⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective S Sm)
  have hmap :
      IsLocalization.map L (algebraMap S Sm) hf = RingHom.id L := by
    apply IsLocalization.ringHom_ext S⁰
    ext x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [IsLocalization.map_eq]
    exact (IsScalarTower.algebraMap_apply S Sm L x).symm
  have hdual_set :
      (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) : Set L) =
        (Submodule.traceDual R K (1 : Submodule S L) : Set L) := by
    change
      ((FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) :
          Submodule S L) : Set L) = _
    rw [FractionalIdeal.coe_dual_one]
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (FractionalIdeal.extended L hf
        (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) :
      Submodule Sm L) =
      (FractionalIdeal.dual Rm K (1 : FractionalIdeal Sm⁰ L) :
        Submodule Sm L)
  rw [FractionalIdeal.coe_extended_eq_span, hmap, hdual_set,
    FractionalIdeal.coe_dual_one]
  simpa only [RingHom.id_apply, Set.image_id'] using
    traceDual_one_span_eq_of_isLocalization R S Rm Sm K L M

/-- Localization preserves the multiplicity of an ideal at a maximal ideal
which is disjoint from the localization monoid.  The proof contracts every
localized power of the maximal ideal; its positive powers are primary, so no
other prime factor of the ideal can affect the comparison. -/
theorem multiplicity_map_eq_of_isLocalization
    (S Sm : Type*) [CommRing S] [CommRing Sm]
    [IsDomain S] [IsDomain Sm]
    [Algebra S Sm] [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid S) [IsLocalization M Sm]
    (Q I : Ideal S) [Q.IsMaximal]
    (hQ : Disjoint (M : Set S) (Q : Set S)) :
    multiplicity (Ideal.map (algebraMap S Sm) Q)
        (Ideal.map (algebraMap S Sm) I) =
      multiplicity Q I := by
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  cases n with
  | zero => simp
  | succ n =>
      have hQprimary : (Q ^ (n + 1)).IsPrimary := by
        apply Ideal.isPrimary_of_isMaximal_radical
        rw [Ideal.radical_pow Q (Nat.succ_ne_zero n),
          (inferInstance : Q.IsPrime).radical]
        exact inferInstance
      have hQdisjoint :
          Disjoint (M : Set S) ((Q ^ (n + 1) : Ideal S) : Set S) :=
        hQ.mono_right (Ideal.pow_le_self (I := Q) (Nat.succ_ne_zero n))
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, ← Ideal.map_pow]
      constructor
      · intro h
        calc
          I ≤ (Ideal.map (algebraMap S Sm) I).under S := Ideal.le_comap_map
          _ ≤ (Ideal.map (algebraMap S Sm) (Q ^ (n + 1))).under S :=
            Ideal.comap_mono h
          _ = Q ^ (n + 1) :=
            IsLocalization.under_map_of_isPrimary_disjoint M Sm hQprimary hQdisjoint
      · exact Ideal.map_mono

/-- Simultaneous localization carries the global different ideal to the
different ideal of the localized finite extension.  The common fraction
fields make explicit that both pairs describe the same field extension. -/
theorem differentIdeal_map_eq_of_isLocalization
    (R S Rm Sm K L : Type*)
    [CommRing R] [CommRing S] [CommRing Rm] [CommRing Sm]
    [IsDomain R] [IsDomain S] [IsDomain Rm] [IsDomain Sm]
    [Field K] [Field L]
    [Algebra R S] [Algebra R Rm] [Algebra S Sm]
    [Algebra R Sm] [Algebra Rm Sm]
    [IsScalarTower R S Sm] [IsScalarTower R Rm Sm]
    [Algebra R K] [Algebra Rm K]
    [Algebra S L] [Algebra Sm L] [Algebra K L]
    [Algebra R L] [Algebra Rm L]
    [IsScalarTower R K L] [IsScalarTower Rm K L]
    [IsScalarTower R S L] [IsScalarTower Rm Sm L]
    [IsScalarTower S Sm L] [IsScalarTower R Sm L]
    [IsFractionRing R K] [IsFractionRing Rm K]
    [IsFractionRing S L] [IsFractionRing Sm L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Free R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree Rm Sm]
    [Module.IsTorsionFree S Sm]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rm]
    [IsIntegralClosure S R L] [IsIntegralClosure Sm Rm L]
    [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L] :
    Ideal.map (algebraMap S Sm) (differentIdeal R S) =
      differentIdeal Rm Sm := by
  rw [← FractionalIdeal.coeIdeal_inj (K := L),
    ← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := L) L Sm,
    coeIdeal_differentIdeal R K L S,
    coeIdeal_differentIdeal Rm K L Sm, map_inv₀,
    dual_one_extendedHom_eq_of_isLocalization R S Rm Sm K L M]

/-- At every upper maximal ideal which remains after simultaneous
localization, the local different has exactly the multiplicity of the global
different. -/
theorem differentIdeal_multiplicity_eq_of_isLocalization
    (R S Rm Sm K L : Type*)
    [CommRing R] [CommRing S] [CommRing Rm] [CommRing Sm]
    [IsDomain R] [IsDomain S] [IsDomain Rm] [IsDomain Sm]
    [Field K] [Field L]
    [Algebra R S] [Algebra R Rm] [Algebra S Sm]
    [Algebra R Sm] [Algebra Rm Sm]
    [IsScalarTower R S Sm] [IsScalarTower R Rm Sm]
    [Algebra R K] [Algebra Rm K]
    [Algebra S L] [Algebra Sm L] [Algebra K L]
    [Algebra R L] [Algebra Rm L]
    [IsScalarTower R K L] [IsScalarTower Rm K L]
    [IsScalarTower R S L] [IsScalarTower Rm Sm L]
    [IsScalarTower S Sm L] [IsScalarTower R Sm L]
    [IsFractionRing R K] [IsFractionRing Rm K]
    [IsFractionRing S L] [IsFractionRing Sm L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Free R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree Rm Sm]
    [Module.IsTorsionFree S Sm]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rm]
    [IsIntegralClosure S R L] [IsIntegralClosure Sm Rm L]
    [IsDedekindDomain S] [IsDedekindDomain Sm]
    (M : Submonoid R)
    [IsLocalization M Rm]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sm]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [IsLocalization (Algebra.algebraMapSubmonoid Sm Rm⁰) L]
    (Q : Ideal S) [Q.IsMaximal]
    (hQ : Disjoint (Algebra.algebraMapSubmonoid S M : Set S) (Q : Set S)) :
    multiplicity (Ideal.map (algebraMap S Sm) Q) (differentIdeal Rm Sm) =
      multiplicity Q (differentIdeal R S) := by
  rw [← differentIdeal_map_eq_of_isLocalization R S Rm Sm K L M]
  exact multiplicity_map_eq_of_isLocalization S Sm
    (Algebra.algebraMapSubmonoid S M) Q (differentIdeal R S) hQ

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
