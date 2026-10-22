/-
Rational-place and residue-evaluation slice.

For every `GlobalPlace`, finiteness of the constant field makes the valuation
trivial on constants.  This gives an actual ring map from the constant field
into the valuation ring and, by reduction, into its residue field.  A
`RationalPlace` is deliberately additional data: an equivalence of that
specific residue-constant map with the constant field.  It is not inferred
for arbitrary global places and it is not supplied for rational infinity here.

Residue degree is only defined after an explicit finite-dimensionality witness
for the residue field with its canonical constant-field algebra structure.
No general residue finiteness, rationality, infinity extension, or evaluation
surjectivity theorem is claimed in this file.
-/

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace

namespace QEC.Coding.AlgebraicGeometry

namespace GlobalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- The finite constant field maps into the valuation ring of every global
place.  This is a codomain restriction of the supplied constant-field map,
not a newly assumed algebra structure. -/
def constantsToValuationRing (P : GlobalPlace k F) :
    k →+* valuationRing P :=
  (algebraMap k F).codRestrict (valuationRing P) fun a =>
    (mem_valuationRing_iff P _).mpr
      (FiniteField.valuation_algebraMap_le_one P.valuation a)

@[simp]
theorem coe_constantsToValuationRing (P : GlobalPlace k F) (a : k) :
    ((constantsToValuationRing P a : valuationRing P) : F) = algebraMap k F a :=
  rfl

/-- Reduction of constants through the valuation ring.  This is the canonical
constant-field map used below to state rationality of a place. -/
noncomputable def constantsToResidue (P : GlobalPlace k F) : k →+* residueField P :=
  (residue P).comp (constantsToValuationRing P)

/-- The canonical `k`-algebra structure on a residue field, formed from its
actual constant-reduction map.  It is a definition rather than a global
instance, so unrelated algebra structures cannot be selected silently. -/
@[reducible]
noncomputable def residueAlgebra (P : GlobalPlace k F) : Algebra k (residueField P) :=
  (constantsToResidue P).toAlgebra

/-- The separately supplied condition needed before speaking of a numerical
residue degree.  It does not assert that all global places have finite residue
field degree. -/
def HasFiniteResidueDegree (P : GlobalPlace k F) : Prop := by
  letI : Algebra k (residueField P) := residueAlgebra P
  exact FiniteDimensional k (residueField P)

/-- The residue degree of a place, defined only relative to a proof that its
canonical residue-field algebra is finite-dimensional. -/
noncomputable def residueDegreeOfFinite (P : GlobalPlace k F)
    (_hfinite : HasFiniteResidueDegree P) : ℕ := by
  letI : Algebra k (residueField P) := residueAlgebra P
  letI : FiniteDimensional k (residueField P) := _hfinite
  exact Module.finrank k (residueField P)

end GlobalPlace

/-- A rational global place has residue field exactly the constant field,
through the actual constant-reduction map.  The compatibility field prevents a
bare isomorphism of fields from being mistaken for a `k`-rational place. -/
structure RationalPlace (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F] where
  place : GlobalPlace k F
  constantsEquiv : k ≃+* GlobalPlace.residueField place
  constantsEquiv_apply (a : k) :
    constantsEquiv a = GlobalPlace.constantsToResidue place a

namespace RationalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- The genuine residue evaluation at a rational place, with codomain
identified with the constant field.  Its domain remains the valuation ring;
there is no total evaluation map on functions with poles. -/
noncomputable def evaluate (Q : RationalPlace k F) :
    GlobalPlace.valuationRing Q.place →+* k :=
  Q.constantsEquiv.symm.toRingHom.comp (GlobalPlace.residue Q.place)

/-- Evaluation of a function together with an explicit proof that it is
regular at the rational place. -/
noncomputable def evaluateRegular (Q : RationalPlace k F) (f : F)
    (hf : GlobalPlace.RegularAt Q.place f) : k :=
  Q.evaluate ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩

/-- The kernel of rational-place evaluation is exactly the maximal ideal of
the valuation ring. -/
theorem evaluate_eq_zero_iff (Q : RationalPlace k F)
    (x : GlobalPlace.valuationRing Q.place) :
    Q.evaluate x = 0 ↔ x ∈ IsLocalRing.maximalIdeal (GlobalPlace.valuationRing Q.place) := by
  change Q.constantsEquiv.symm (GlobalPlace.residue Q.place x) = 0 ↔ _
  rw [Q.constantsEquiv.symm.map_eq_zero_iff,
    GlobalPlace.residue_eq_zero_iff]

/-- The regular-function version of the kernel characterization. -/
theorem evaluateRegular_eq_zero_iff (Q : RationalPlace k F) (f : F)
    (hf : GlobalPlace.RegularAt Q.place f) :
    Q.evaluateRegular f hf = 0 ↔
      (⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩ :
        GlobalPlace.valuationRing Q.place) ∈
        IsLocalRing.maximalIdeal (GlobalPlace.valuationRing Q.place) := by
  exact Q.evaluate_eq_zero_iff _

/-- Every constant is regular at every rational place. -/
theorem constants_regular (Q : RationalPlace k F) (a : k) :
    GlobalPlace.RegularAt Q.place (algebraMap k F a) :=
  (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
    (FiniteField.valuation_algebraMap_le_one Q.place.valuation a)

/-- Rational-place evaluation fixes constants. -/
theorem evaluate_constants (Q : RationalPlace k F) (a : k) :
    Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) = a := by
  change Q.constantsEquiv.symm (GlobalPlace.constantsToResidue Q.place a) = a
  rw [← Q.constantsEquiv_apply a, Q.constantsEquiv.symm_apply_apply]

/-- The regular-function evaluation formulation of constant preservation. -/
theorem evaluateRegular_algebraMap (Q : RationalPlace k F) (a : k) :
    Q.evaluateRegular (algebraMap k F a) (Q.constants_regular a) = a := by
  change Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) = a
  exact Q.evaluate_constants a

/-- The canonical constant-reduction map is bijective at a rational place. -/
theorem constantsToResidue_bijective (Q : RationalPlace k F) :
    Function.Bijective (GlobalPlace.constantsToResidue Q.place) := by
  constructor
  · intro a b hab
    apply Q.constantsEquiv.injective
    simpa only [Q.constantsEquiv_apply] using hab
  · intro x
    obtain ⟨a, ha⟩ := Q.constantsEquiv.surjective x
    refine ⟨a, ?_⟩
    rw [← Q.constantsEquiv_apply a]
    exact ha

/-- Rationality supplies the finite-dimensionality witness required for the
residue degree; it is derived from the chosen compatible equivalence rather
than stored as an independent field. -/
theorem hasFiniteResidueDegree (Q : RationalPlace k F) :
    GlobalPlace.HasFiniteResidueDegree Q.place := by
  letI : Algebra k (GlobalPlace.residueField Q.place) :=
    GlobalPlace.residueAlgebra Q.place
  change FiniteDimensional k (GlobalPlace.residueField Q.place)
  apply FiniteDimensional.of_surjective
    (Algebra.linearMap k (GlobalPlace.residueField Q.place))
  intro x
  obtain ⟨a, ha⟩ := Q.constantsEquiv.surjective x
  refine ⟨a, ?_⟩
  change GlobalPlace.constantsToResidue Q.place a = x
  rw [← Q.constantsEquiv_apply a]
  exact ha

/-- A rational place has residue degree one.  The degree is the conditional
`finrank` construction above, so this theorem does not introduce a general
finiteness assumption on residue fields. -/
theorem residueDegree_eq_one (Q : RationalPlace k F) :
    GlobalPlace.residueDegreeOfFinite Q.place Q.hasFiniteResidueDegree = 1 := by
  unfold GlobalPlace.residueDegreeOfFinite
  letI : Algebra k (GlobalPlace.residueField Q.place) :=
    GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional k (GlobalPlace.residueField Q.place) :=
    Q.hasFiniteResidueDegree
  apply Module.finrank_of_bijective_algebraMap
  simpa only [GlobalPlace.residueAlgebra, RingHom.algebraMap_toAlgebra] using
    Q.constantsToResidue_bijective

end RationalPlace

end QEC.Coding.AlgebraicGeometry
