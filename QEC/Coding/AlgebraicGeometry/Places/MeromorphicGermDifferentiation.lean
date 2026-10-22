import QEC.Coding.AlgebraicGeometry.Places.AnalyticGermEvaluation
import Mathlib.RingTheory.Derivation.Basic

/-!
# Differentiation of punctured meromorphic germs

Literal complex constants and actual derivatives of representatives give
a genuine complex derivation. Punctured germ equality makes the derivative
independent of the chosen representative. Analytic germs stay analytic,
and a nonzero finite integer order decreases by one under differentiation.
-/

namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

/-- Embed literal complex constant functions into punctured meromorphic germs. -/
def germComplexConstants (x : ℂ) : ℂ →+* MeromorphicGermRing x where
  toFun c := ⟨((fun _ : ℂ => c) : Germ (𝓝[≠] x) ℂ),
    (fun _ : ℂ => c),MeromorphicAt.const c x,rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Differentiate a genuine meromorphic representative and take its punctured germ. -/
def germDerivative (x : ℂ) (A : MeromorphicGermRing x) : MeromorphicGermRing x :=
  ⟨(deriv A.property.choose : Germ (𝓝[≠] x) ℂ),deriv A.property.choose,
    A.property.choose_spec.1.deriv,rfl⟩

/-- Differentiation agrees with every meromorphic representative of the same punctured germ. -/
lemma germDerivative_value (x : ℂ) (A : MeromorphicGermRing x)
    (f : ℂ → ℂ) (_hf : MeromorphicAt f x) (he : A.val = (f : Germ (𝓝[≠] x) ℂ)) :
    (germDerivative x A).val = (deriv f : Germ (𝓝[≠] x) ℂ) := by
  apply Germ.coe_eq.mpr
  exact (Germ.coe_eq.mp (A.property.choose_spec.2.symm.trans he)).nhdsNE_deriv

/-- Representative-independent punctured germ differentiation is additive. -/
lemma germDerivative_add (x : ℂ) (A B : MeromorphicGermRing x) :
    germDerivative x (A+B) = germDerivative x A + germDerivative x B := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A+B).val = (f+g : Germ (𝓝[≠] x) ℂ) := by
    change A.val+B.val = _
    rw [he,he']
  apply Subtype.ext
  change (germDerivative x (A+B)).val = (germDerivative x A).val + (germDerivative x B).val
  rw [germDerivative_value x (A+B) (f+g) (hf.add hg) hab,
    germDerivative_value x A f hf he,germDerivative_value x B g hg he']
  apply Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hz hz'
  exact deriv_add hz.differentiableAt hz'.differentiableAt

/-- Actual germ differentiation satisfies the Leibniz rule. -/
lemma germDerivative_mul (x : ℂ) (A B : MeromorphicGermRing x) :
    germDerivative x (A*B) = A*germDerivative x B + B*germDerivative x A := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A*B).val = (f*g : Germ (𝓝[≠] x) ℂ) := by
    change A.val*B.val = _
    rw [he,he']
  apply Subtype.ext
  change (germDerivative x (A*B)).val = A.val*(germDerivative x B).val + B.val*(germDerivative x A).val
  rw [germDerivative_value x (A*B) (f*g) (hf.mul hg) hab,
    germDerivative_value x A f hf he,germDerivative_value x B g hg he',he,he']
  apply Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hz hz'
  simpa only [Pi.mul_apply,Pi.add_apply,mul_comm,add_comm] using
    deriv_mul hz.differentiableAt hz'.differentiableAt

/-- The differentiated germ of every literal complex constant is zero. -/
lemma germDerivative_constant (x : ℂ) (c : ℂ) :
    germDerivative x (germComplexConstants x c) = 0 := by
  apply Subtype.ext
  rw [germDerivative_value x _ (fun _ : ℂ => c) (MeromorphicAt.const c x) rfl]
  apply Germ.coe_eq.mpr
  filter_upwards with z
  simp only [deriv_const]

section ComplexDerivation
variable (x : ℂ)
local instance : Algebra ℂ (MeromorphicGermRing x) := (germComplexConstants x).toAlgebra

/-- The genuine complex-linear derivation on punctured meromorphic germs. -/
def germCoefficientDerivation : Derivation ℂ (MeromorphicGermRing x) (MeromorphicGermRing x) := by
  let D : MeromorphicGermRing x →ₗ[ℂ] MeromorphicGermRing x :=
    { toFun := germDerivative x
      map_add' := germDerivative_add x
      map_smul' := by
        intro c A
        change germDerivative x (germComplexConstants x c * A) =
          germComplexConstants x c * germDerivative x A
        rw [germDerivative_mul,germDerivative_constant,mul_zero,add_zero] }
  exact Derivation.mk' D (germDerivative_mul x)

end ComplexDerivation

/-- Differentiating a germ with an analytic representative preserves nonnegative order. -/
lemma germDerivative_nonnegative (x : ℂ) (A : MeromorphicGermRing x)
    (hA : 0 ≤ meromorphicOrderValuation x A) :
    0 ≤ meromorphicOrderValuation x (germDerivative x A) := by
  obtain ⟨g,hg,he⟩ := (meromorphicGerm_noPole_iff_analytic x A).mp hA
  apply (meromorphicGerm_noPole_iff_analytic x (germDerivative x A)).mpr
  exact ⟨deriv g,hg.deriv,germDerivative_value x A g hg.meromorphicAt he⟩

/-- A nonzero finite integer order decreases by one under actual complex differentiation. -/
lemma germDerivative_order (x : ℂ) (A : MeromorphicGermRing x) (m : ℤ)
    (hm : m ≠ 0) (hA : meromorphicOrderValuation x A = (m : WithTop ℤ)) :
    meromorphicOrderValuation x (germDerivative x A) = ((m-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨f,hf,he⟩ := A.property
  change germOrder x (germDerivative x A).val = _
  rw [germDerivative_value x A f hf he,germOrder_coe]
  apply meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hm)
  change germOrder x A.val = _ at hA
  rwa [he,germOrder_coe] at hA

end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
