import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Polynomial maximal points and finite prime separation

Every maximal ideal of Complex[X] is exactly polynomial evaluation zero at
a complex number. An actual integral quotient and complex algebraic closure
produce that number; maximality identifies the principal X-C(a) ideal.
Finite prime avoidance supplies an element of a maximal ideal outside a
finite collection of prime ideals, without assuming a chosen separator.
These two algebraic lemmas are used in original zero-chart point coverage.
-/

namespace QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
noncomputable section

lemma complexPolynomialMaximal_exists_eval (M : Ideal (Polynomial ℂ))
    [M.IsMaximal] : ∃ a : ℂ, ∀ p : Polynomial ℂ, p ∈ M ↔ p.eval a = 0 := by
  let φ : ℂ →+* Polynomial ℂ ⧸ M := (Ideal.Quotient.mk M).comp Polynomial.C
  have hφ : φ.IsIntegral := Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing M
  obtain ⟨a, ha⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral φ hφ).2
    (Ideal.Quotient.mk M Polynomial.X)
  have hx : Polynomial.X - Polynomial.C a ∈ M := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr ha.symm
  let L : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X - Polynomial.C a}
  have hL : L.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible
    (Polynomial.irreducible_X_sub_C a)
  have hLM : L ≤ M := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have heq : L = M := hL.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hLM
  refine ⟨a, fun p => ?_⟩
  rw [←heq,Ideal.mem_span_singleton,Polynomial.dvd_iff_isRoot]
  rfl

end
end QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints

namespace QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
noncomputable section

lemma finitePrimeAvoidance {R : Type*} [CommRing R] [Nontrivial R]
    (M : Ideal R) [M.IsMaximal] (S : Set (Ideal R)) (hS : S.Finite)
    (hprime : ∀ I ∈ S, I.IsPrime) (houtside : M ∉ S) :
    ∃ g ∈ M, ∀ I ∈ S, g ∉ I := by
  have hn : ¬((M : Set R) ⊆ ⋃ I ∈ S, (I : Set R)) := by
    intro hs
    apply houtside
    exact (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite hS ⊥ ⊥
      (fun I hI _ _ => hprime I hI) bot_ne_top bot_ne_top).mp hs
  obtain ⟨g,hg,hgu⟩ := Set.not_subset.mp hn
  refine ⟨g,hg,fun I hI hgi => hgu ?_⟩
  exact Set.mem_iUnion.mpr ⟨I,Set.mem_iUnion.mpr ⟨hI,hgi⟩⟩

end
end QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
