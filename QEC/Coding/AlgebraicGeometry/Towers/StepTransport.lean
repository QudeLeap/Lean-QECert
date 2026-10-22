import QEC.Coding.AlgebraicGeometry.Towers.Step

/-!
# Transport between identical Garcia--Stichtenoth step fields

The reciprocal polynomial defining one recursion step depends on a place only
through the proof that the fixed coordinate has a simple pole there.  This
file proves that the resulting polynomials are equal and constructs the
canonical equivalence between their adjoining fields.  This lets later local
ramification calculations be transported into the actual recursive field;
no ramification or genus conclusion is asserted here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem stepPolynomial_eq_explicit_transport
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepPolynomial P x hx =
      X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹ := by
  simp [stepPolynomial, reciprocalPolynomial, coe_reciprocalUniformizer]
  rw [← map_pow, inv_pow]

/-- The defining step polynomial is independent of which simple-pole place
supplies its valuation proof. -/
theorem stepPolynomial_eq_of_place
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    stepPolynomial P x hP = stepPolynomial Q x hQ := by
  rw [stepPolynomial_eq_explicit_transport,
    stepPolynomial_eq_explicit_transport]

/-- The canonical equivalence between two presentations of the same explicit
degree-sixteen step field. -/
noncomputable def stepFieldEquiv
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    StepField P x hP ≃ₐ[K] StepField Q x hQ :=
  AdjoinRoot.algEquivOfEq K
    (stepPolynomial P x hP) (stepPolynomial Q x hQ)
    (stepPolynomial_eq_of_place P Q x hP hQ)

@[simp]
theorem stepFieldEquiv_stepFieldEmbedding
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) (y : K) :
    stepFieldEquiv P Q x hP hQ (stepFieldEmbedding P x hP y) =
      stepFieldEmbedding Q x hQ y := by
  have hport := (stepFieldEquiv P Q x hP hQ).commutes y
  simp only [stepFieldEmbedding] at hport ⊢
  exact hport

@[simp]
theorem stepFieldEquiv_stepReciprocalRoot
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    stepFieldEquiv P Q x hP hQ (stepReciprocalRoot P x hP) =
      stepReciprocalRoot Q x hQ := by
  exact AdjoinRoot.algEquivOfEq_root
    (stepPolynomial P x hP) (stepPolynomial Q x hQ)
    (stepPolynomial_eq_of_place P Q x hP hQ)

@[simp]
theorem stepFieldEquiv_stepAuxiliaryCoordinate
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    stepFieldEquiv P Q x hP hQ (stepAuxiliaryCoordinate P x hP) =
      stepAuxiliaryCoordinate Q x hQ := by
  rw [stepAuxiliaryCoordinate, map_div₀,
    stepFieldEquiv_stepFieldEmbedding,
    stepFieldEquiv_stepReciprocalRoot]
  rfl

@[simp]
theorem stepFieldEquiv_stepDistinguishedCoordinate
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    stepFieldEquiv P Q x hP hQ (stepDistinguishedCoordinate P x hP) =
      stepDistinguishedCoordinate Q x hQ := by
  rw [stepDistinguishedCoordinate_eq_inv,
    map_inv₀, stepFieldEquiv_stepReciprocalRoot,
    stepDistinguishedCoordinate_eq_inv]

end


end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
