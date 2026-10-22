import Mathlib.RingTheory.Trace.Quotient
import QEC.Coding.AlgebraicGeometry.Trace.DedekindQuotientTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Reduction of the direct integral trace

For the direct integral closure of `k[X]` in a finite separable function
field, this module reduces the actual integral trace modulo a height-one base
prime and splits it over the finite prime factors upstairs.  It is the
integral-coefficient algebraic bridge toward trace--residue compatibility.

It also transports the quotient formula to the actual ideal residue fields.
It does not yet identify those fields with valuation-place residue fields,
treat semilocal denominators, or state a global residue theorem, duality
theorem, genus formula, or Riemann--Roch theorem.
-/

namespace Ideal

open scoped nonZeroDivisors
open UniqueFactorizationMonoid

attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

namespace Factors

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {S : Type v} [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable [Module.IsTorsionFree R S] [Module.Finite R S]

/-- Reduction of the actual direct integral trace at a height-one polynomial
prime is the finite ramification-weighted sum of the upper quotient traces.
The equality combines Mathlib's integral-trace reduction theorem with the
proved Dedekind quotient-factor trace decomposition. -/
theorem integralTrace_mod_eq_sum_ramificationIdx_mul
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Ideal.Quotient.mk p (Algebra.intTrace R S x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : R ⧸ p) *
          Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
            (Ideal.Quotient.mk (P : Ideal S) x) := by
  calc
    Ideal.Quotient.mk p (Algebra.intTrace R S x) =
        Algebra.trace (R ⧸ p) (S ⧸ map (algebraMap R S) p)
          (Ideal.Quotient.mk _ x) :=
      by rw [Algebra.trace_quotient_eq_of_isDedekindDomain]
    _ = _ := trace_quotient_map_eq_sum_ramificationIdx_mul p hp x

/-- The canonical equivalence from an ideal quotient by a maximal ideal to
its residue field. -/
noncomputable def quotientResidueEquiv
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsMaximal] :
    (A ⧸ I) ≃+* I.ResidueField :=
  RingEquiv.ofBijective (algebraMap (A ⧸ I) I.ResidueField)
    I.bijective_algebraMap_quotient_residueField

@[simp]
theorem quotientResidueEquiv_mk
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsMaximal] (x : A) :
    quotientResidueEquiv I (Ideal.Quotient.mk I x) =
      algebraMap A I.ResidueField x := by
  rw [quotientResidueEquiv, RingEquiv.ofBijective_apply,
    Ideal.algebraMap_quotient_residueField_mk]

/-- The residue-field trace of an integral element at one actual prime factor
above `p`.  Its scalar algebra is the canonical localization map supplied by
the factor's proved lies-over relation. -/
noncomputable def factorResidueTrace
    (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    p.ResidueField := by
  letI : (P : Ideal S).IsMaximal :=
    (Factors.isPrime p P).isMaximal (Factors.ne_bot p P)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime (P : Ideal S)) :=
    Localization.AtPrime.algebraOfLiesOver p (P : Ideal S)
  exact Algebra.trace p.ResidueField (P : Ideal S).ResidueField
    (algebraMap S (P : Ideal S).ResidueField x)

omit [IsDedekindDomain R] [Module.IsTorsionFree R S] [Module.Finite R S] in
/-- Transporting multiplication trace on an upper ideal quotient to the base
residue field gives the corresponding factor residue trace. -/
theorem quotientTrace_to_factorResidueTrace
    (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    quotientResidueEquiv p
        (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (Ideal.Quotient.mk (P : Ideal S) x)) =
      factorResidueTrace p P x := by
  letI : (P : Ideal S).IsMaximal :=
    (Factors.isPrime p P).isMaximal (Factors.ne_bot p P)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime (P : Ideal S)) :=
    Localization.AtPrime.algebraOfLiesOver p (P : Ideal S)
  let ep : (R ⧸ p) ≃+* p.ResidueField := quotientResidueEquiv p
  let eP : (S ⧸ (P : Ideal S)) ≃+* (P : Ideal S).ResidueField :=
    quotientResidueEquiv (P : Ideal S)
  have he : RingHom.comp
      (algebraMap p.ResidueField (P : Ideal S).ResidueField) ep =
        RingHom.comp eP (algebraMap (R ⧸ p) (S ⧸ (P : Ideal S))) := by
    ext r
    simp only [RingHom.comp_apply,
      Ideal.Quotient.algebraMap_quotient_of_ramificationIdx_neZero]
    have hep : ep (Ideal.Quotient.mk p r) =
        algebraMap R p.ResidueField r := by
      simpa only [ep] using quotientResidueEquiv_mk p r
    have heP : eP (Ideal.Quotient.mk (P : Ideal S) (algebraMap R S r)) =
        algebraMap S (P : Ideal S).ResidueField (algebraMap R S r) := by
      simpa only [eP] using quotientResidueEquiv_mk (P : Ideal S) (algebraMap R S r)
    change algebraMap p.ResidueField (P : Ideal S).ResidueField
        (ep (Ideal.Quotient.mk p r)) =
      eP (Ideal.Quotient.mk (P : Ideal S) (algebraMap R S r))
    rw [hep, heP, ← IsScalarTower.algebraMap_apply R p.ResidueField,
      ← IsScalarTower.algebraMap_apply R S]
  have htrace := Algebra.trace_eq_of_equiv_equiv ep eP he
    (Ideal.Quotient.mk (P : Ideal S) x)
  calc
    quotientResidueEquiv p
        (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (Ideal.Quotient.mk (P : Ideal S) x)) =
        Algebra.trace p.ResidueField (P : Ideal S).ResidueField
          (eP (Ideal.Quotient.mk (P : Ideal S) x)) := by
      change ep (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
        (Ideal.Quotient.mk (P : Ideal S) x)) = _
      rw [htrace, ep.apply_symm_apply]
    _ = factorResidueTrace p P x := by
      rw [factorResidueTrace]
      exact congrArg (Algebra.trace p.ResidueField (P : Ideal S).ResidueField)
        (quotientResidueEquiv_mk (P : Ideal S) x)

/-- Reduction of an integral trace in the actual base residue field is the
finite ramification-weighted sum of the actual upper residue-field traces.
This transports the quotient-factor identity through the canonical quotient
to residue-field equivalences; it does not enumerate either residue field. -/
theorem integralTrace_residue_eq_sum_ramificationIdx_mul
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    algebraMap R p.ResidueField (Algebra.intTrace R S x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : p.ResidueField) *
          factorResidueTrace p P x := by
  have h := congrArg (quotientResidueEquiv p)
    (integralTrace_mod_eq_sum_ramificationIdx_mul p hp x)
  simpa only [quotientResidueEquiv_mk, map_sum, map_mul, map_natCast,
    quotientTrace_to_factorResidueTrace] using h

end Factors
end Ideal
