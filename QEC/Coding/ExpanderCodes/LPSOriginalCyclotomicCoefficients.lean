import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic

/-!
# Cyclotomic coefficients for original cusp expansions

The actual cyclotomic quotient embeds faithfully into the complex numbers and
reduces to the prime field by sending its distinguished root to one. The inverse
root and prime-power identities are proved in this same coefficient ring.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

abbrev lpsOriginalCyclotomicCoefficientRing (p : ℕ) : Type :=
  AdjoinRoot (Polynomial.cyclotomic p ℤ)

def lpsOriginalCyclotomicComplexRoot (p : ℕ) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I/p)

lemma lpsOriginalCyclotomicComplexRoot_primitive (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (lpsOriginalCyclotomicComplexRoot p) p :=
  Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero

lemma lpsOriginalCyclotomicComplexRoot_annihilates (p : ℕ) [Fact p.Prime] :
    (Polynomial.cyclotomic p ℤ).eval₂ (Int.castRingHom ℂ)
      (lpsOriginalCyclotomicComplexRoot p)=0 := by
  have h := (lpsOriginalCyclotomicComplexRoot_primitive p).isRoot_cyclotomic
    (Fact.out : p.Prime).pos
  rw [Polynomial.eval₂_eq_eval_map,Polynomial.map_cyclotomic_int]
  exact h

def lpsOriginalCyclotomicComplexEmbedding (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicCoefficientRing p →+* ℂ :=
  AdjoinRoot.lift (Int.castRingHom ℂ) (lpsOriginalCyclotomicComplexRoot p)
    (lpsOriginalCyclotomicComplexRoot_annihilates p)

lemma lpsOriginalCyclotomicComplexEmbedding_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalCyclotomicComplexEmbedding p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih P =>
    rw [lpsOriginalCyclotomicComplexEmbedding,AdjoinRoot.lift_mk] at hx
    have h := minpoly.isIntegrallyClosed_dvd
      ((lpsOriginalCyclotomicComplexRoot_primitive p).isIntegral (Fact.out : p.Prime).pos) hx
    rw [← Polynomial.cyclotomic_eq_minpoly
      (lpsOriginalCyclotomicComplexRoot_primitive p) (Fact.out : p.Prime).pos] at h
    exact AdjoinRoot.mk_eq_zero.mpr h

lemma lpsOriginalCyclotomic_mod_root (p : ℕ) [Fact p.Prime] :
    (Polynomial.cyclotomic p ℤ).eval₂ (Int.castRingHom (ZMod p)) 1=0 := by
  rw [Polynomial.eval₂_eq_eval_map,Polynomial.map_cyclotomic_int,
    Polynomial.cyclotomic_prime]
  simp

def lpsOriginalCyclotomicReduction (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicCoefficientRing p →+* ZMod p :=
  AdjoinRoot.lift (Int.castRingHom (ZMod p)) 1 (lpsOriginalCyclotomic_mod_root p)

lemma lpsOriginalCyclotomicReduction_root (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicReduction p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))=1 :=
  AdjoinRoot.lift_root _

lemma lpsOriginalCyclotomicReduction_root_pow (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCyclotomicReduction p
      ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)=1 := by
  rw [map_pow,lpsOriginalCyclotomicReduction_root,one_pow]

lemma lpsOriginalCyclotomicComplexEmbedding_root (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicComplexEmbedding p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))=
      lpsOriginalCyclotomicComplexRoot p :=
  AdjoinRoot.lift_root _

lemma lpsOriginalCyclotomicRoot_pow (p : ℕ) [Fact p.Prime] :
    (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^p=1 := by
  apply lpsOriginalCyclotomicComplexEmbedding_injective p
  rw [map_pow,map_one,lpsOriginalCyclotomicComplexEmbedding_root]
  exact (lpsOriginalCyclotomicComplexRoot_primitive p).pow_eq_one

lemma lpsOriginalCyclotomicRoot_inverse (p : ℕ) [Fact p.Prime] :
    AdjoinRoot.root (Polynomial.cyclotomic p ℤ)*
      (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^(p-1)=1 := by
  rw [←pow_succ',Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    lpsOriginalCyclotomicRoot_pow]

lemma lpsOriginalCyclotomicComplexEmbedding_root_inverse (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicComplexEmbedding p ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^(p-1))=
      (lpsOriginalCyclotomicComplexRoot p)⁻¹ := by
  have h:=congrArg (lpsOriginalCyclotomicComplexEmbedding p) (lpsOriginalCyclotomicRoot_inverse p)
  rw [map_mul,map_one,lpsOriginalCyclotomicComplexEmbedding_root] at h
  exact eq_inv_of_mul_eq_one_right h

end
end QEC.Coding.TannerLiftedProduct
