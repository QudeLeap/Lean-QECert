import QEC.Coding.AlgebraicGeometry.Places.FullConstantField
import QEC.Coding.AlgebraicGeometry.Places.RationalPlace
import Mathlib.FieldTheory.Finite.Valuation

/-!
# An actual rational place forces the finite full constant field

Any finite algebraic constant extension evaluates injectively into the
residue field of the rational place, so has the same finite cardinality.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

theorem isFullConstantField_of_rationalPlace
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (Q : RationalPlace k F) : IsFullConstantField k F := by
  refine ⟨fun x hx => ?_⟩
  let E : IntermediateField k F := IntermediateField.adjoin k {x}
  letI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  letI : Finite E := Module.finite_of_finite k
  let integralInclusion : E →+* Q.place.valuationRing :=
    (algebraMap E F).codRestrict Q.place.valuationRing fun y =>
      (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
        (FiniteField.valuation_algebraMap_le_one Q.place.valuation y)
  let evaluateAdjoin : E →+* k := Q.evaluate.comp integralInclusion
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype E := Fintype.ofFinite E
  have hEk : Fintype.card E ≤ Fintype.card k :=
    Fintype.card_le_of_injective evaluateAdjoin evaluateAdjoin.injective
  have hkE : Fintype.card k ≤ Fintype.card E :=
    Fintype.card_le_of_injective (algebraMap k E) (algebraMap k E).injective
  have hcard : Fintype.card k = Fintype.card E := Nat.le_antisymm hkE hEk
  have hsurjective : Function.Surjective (algebraMap k E) :=
    ((Fintype.bijective_iff_injective_and_card (algebraMap k E)).mpr
      ⟨(algebraMap k E).injective, hcard⟩).2
  have hxmem : x ∈ E := IntermediateField.subset_adjoin k ({x} : Set F) (by simp)
  obtain ⟨c, hc⟩ := hsurjective ⟨x, hxmem⟩
  refine ⟨c, ?_⟩
  have hc' := congrArg (fun y : E => (y : F)) hc
  simpa [E] using hc'.symm

end

end QEC.Coding.AlgebraicGeometry
