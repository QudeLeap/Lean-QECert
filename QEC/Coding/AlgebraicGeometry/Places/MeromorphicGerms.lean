import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Punctured meromorphic and analytic germs

The local order valuation, integral-element bounds, and analytic evaluation
are constructed from actual representatives. These lemmas are consumed by
the original normalization's point construction.
-/

namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

/-- Actual meromorphic representatives modulo punctured germ equality at x. -/
def meromorphicGermSubring (x : ℂ) : Subring (Germ (𝓝[≠] x) ℂ) where
  carrier := {A | ∃ f : ℂ → ℂ, MeromorphicAt f x ∧ A = (f : Germ (𝓝[≠] x) ℂ)}
  zero_mem' := ⟨0, MeromorphicAt.const 0 x, rfl⟩
  one_mem' := ⟨1, MeromorphicAt.const 1 x, rfl⟩
  add_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g,hf.add hg,rfl⟩
  neg_mem' := by
    rintro A ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩

abbrev MeromorphicGermRing (x : ℂ) := ↥(meromorphicGermSubring x)

def germOrder (x : ℂ) (A : Germ (𝓝[≠] x) ℂ) : WithTop ℤ :=
  Germ.liftOn A (fun f => meromorphicOrderAt f x)
    (fun _ _ h => meromorphicOrderAt_congr h)

lemma germOrder_coe (x : ℂ) (f : ℂ → ℂ) :
    germOrder x (f : Germ (𝓝[≠] x) ℂ) = meromorphicOrderAt f x := rfl

def meromorphicOrderValuation (x : ℂ) : AddValuation (MeromorphicGermRing x) (WithTop ℤ) :=
  AddValuation.of (fun A => germOrder x A.val)
    (by change meromorphicOrderAt (0 : ℂ → ℂ) x = ⊤; simp)
    (by change meromorphicOrderAt (1 : ℂ → ℂ) x = 0; simp)
    (by
      intro A B
      obtain ⟨f,hf,he⟩ := A.property
      obtain ⟨g,hg,hgerm⟩ := B.property
      change min (germOrder x A.val) (germOrder x B.val) ≤ germOrder x (A.val+B.val)
      rw [he,hgerm]
      exact meromorphicOrderAt_add hf hg)
    (by
      intro A B
      obtain ⟨f,hf,he⟩ := A.property
      obtain ⟨g,hg,hgerm⟩ := B.property
      change germOrder x (A.val*B.val) = germOrder x A.val + germOrder x B.val
      rw [he,hgerm]
      exact meromorphicOrderAt_mul hf hg)

lemma meromorphicOrderValuation_rep (x : ℂ) (f : ℂ → ℂ) (hf : MeromorphicAt f x) :
    meromorphicOrderValuation x ⟨(f : Germ (𝓝[≠] x) ℂ),f,hf,rfl⟩ =
      meromorphicOrderAt f x := rfl

lemma meromorphicOrderValuation_eq_top_iff (x : ℂ) (A : MeromorphicGermRing x) :
    meromorphicOrderValuation x A = ⊤ ↔ A = 0 := by
  obtain ⟨f,hf,he⟩ := A.property
  change germOrder x A.val = ⊤ ↔ A = 0
  rw [he, germOrder_coe, meromorphicOrderAt_eq_top_iff]
  constructor
  · intro h
    apply Subtype.ext
    rw [he]
    exact Filter.Germ.coe_eq.mpr h
  · intro h
    have hv : (f : Germ (𝓝[≠] x) ℂ) = 0 := by
      rw [← he]
      exact congrArg Subtype.val h
    exact Filter.Germ.coe_eq.mp hv

lemma nonnegativeOrder_iff_analytic_extension (x : ℂ) (f : ℂ → ℂ)
    (hf : MeromorphicAt f x) :
    0 ≤ meromorphicOrderValuation x ⟨(f : Germ (𝓝[≠] x) ℂ),f,hf,rfl⟩ ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ f =ᶠ[𝓝[≠] x] g :=
  hf.meromorphicOrderAt_nonneg_iff

/-- Integral elements over coefficients in a valuation ring have no pole. -/
lemma valuation_le_one_of_integral_map
    {R A Γ : Type*} [CommRing R] [CommRing A] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation A Γ) (f : R →+* A) (hf : ∀ r, v (f r) ≤ 1)
    {a : A} (ha : f.IsIntegralElem a) : v a ≤ 1 := by
  let g : R →+* v.integer := f.codRestrict v.integer hf
  have h : (v.integer.subtype.comp g).IsIntegralElem a := ha
  have hi : IsIntegral v.integer a := h.of_comp
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hi

/-- Nonnegative additive valuation rings contain every integral element over them. -/
lemma nonnegative_of_integral_map
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : R →+* A)
    (hf : ∀ r, 0 ≤ v (f r)) {a : A} (ha : f.IsIntegralElem a) :
    0 ≤ v a := by
  exact valuation_le_one_of_integral_map (AddValuation.toValuation v) f hf ha

/-- The coefficient ring and chosen coordinate generate only nonnegative-order polynomials. -/
lemma nonnegative_polynomial_eval
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : R →+* A)
    (hf : ∀ r, 0 ≤ v (f r)) (a : A) (ha : 0 ≤ v a) (p : Polynomial R) :
    0 ≤ v (p.eval₂ f a) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add]
      exact v.map_le_add hp hq
  | monomial n c =>
      rw [Polynomial.eval₂_monomial, v.map_mul, v.map_pow]
      exact add_nonneg (hf c) (nsmul_nonneg ha n)

lemma additiveValuation_nonnegative_or_inverse
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (a : K) :
    0 ≤ v a ∨ 0 ≤ v a⁻¹ := by
  rw [v.map_inv]
  induction v a using WithTop.recTopCoe with
  | top => exact Or.inl le_top
  | coe n =>
      rcases le_total 0 n with hn | hn
      · left; exact_mod_cast hn
      · right
        rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
        exact_mod_cast (neg_nonneg.mpr hn)

lemma nonnegative_laurent_map
    {R A : Type*} [CommRing R] [CommRing A]
    (v : AddValuation A (WithTop ℤ)) (f : LaurentPolynomial R →+* A)
    (hc : ∀ c, 0 ≤ v (f (LaurentPolynomial.C c)))
    (h1 : 0 ≤ v (f (LaurentPolynomial.T 1)))
    (hinv : 0 ≤ v (f (LaurentPolynomial.T (-1)))) (p : LaurentPolynomial R) :
    0 ≤ v (f p) := by
  refine LaurentPolynomial.induction_on p hc ?_ ?_ ?_
  · intro p q hp hq
    rw [map_add]
    exact v.map_le_add hp hq
  · intro n c hn
    have he : LaurentPolynomial.C c * LaurentPolynomial.T ((n : ℤ)+1) =
        (LaurentPolynomial.C c * LaurentPolynomial.T (n : ℤ)) * LaurentPolynomial.T 1 := by
      rw [mul_assoc, ← LaurentPolynomial.T_add]
    rw [he, map_mul, v.map_mul]
    exact add_nonneg hn h1
  · intro n c hn
    have he : LaurentPolynomial.C c * LaurentPolynomial.T (-(n : ℤ)-1) =
        (LaurentPolynomial.C c * LaurentPolynomial.T (-(n : ℤ))) *
          LaurentPolynomial.T (-1) := by
      rw [mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]
    rw [he, map_mul, v.map_mul]
    exact add_nonneg hn hinv

end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
