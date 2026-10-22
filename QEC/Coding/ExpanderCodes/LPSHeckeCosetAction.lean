import QEC.Coding.ExpanderCodes.LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The genuine finite Hecke coset action

True original right factors and uniqueness prove composition. Inverse actors give a left Gamma0 action, with both genuine intersection stabilizers and transitivity. The quotient is not assumed normal.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

/-- A genuine integral factor determines the originally selected representative index uniquely. -/
lemma lpsHeckeRightIndex_of_factor (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (i j : Option (Fin p)) (δ : SL(2,ℤ))
    (he : lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j) :
    lpsHeckeRightIndex N p hNp γ hγ i=j := by
  obtain ⟨ε,_hε,hε⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
  apply lpsHeckeUpperMatrix_index_unique p _ j ((ε⁻¹*δ:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)
  calc
    lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i)=
        ((ε⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*
          ((ε:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i)) := by
      rw [←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one,Matrix.one_mul]
    _ = _ := by
      rw [←hε,he,←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul]

/-- The originally selected right index is unchanged by the identity matrix. -/
lemma lpsHeckeRightIndex_one (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp 1 (CongruenceSubgroup.Gamma0 N).one_mem i=i := by
  apply lpsHeckeRightIndex_of_factor N p hNp 1 (CongruenceSubgroup.Gamma0 N).one_mem i i 1
  simp

/-- Actual integral factor multiplication proves the contravariant right-index composition law. -/
lemma lpsHeckeRightIndex_mul (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ δ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (γ*δ) ((CongruenceSubgroup.Gamma0 N).mul_mem hγ hδ) i =
      lpsHeckeRightIndex N p hNp δ hδ (lpsHeckeRightIndex N p hNp γ hγ i) := by
  obtain ⟨a,_ha,hea⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
  obtain ⟨b,_hb,heb⟩ := lpsHeckeRightIndex_spec N p hNp δ hδ
    (lpsHeckeRightIndex N p hNp γ hγ i)
  apply lpsHeckeRightIndex_of_factor N p hNp (γ*δ)
    ((CongruenceSubgroup.Gamma0 N).mul_mem hγ hδ) i _ (a*b)
  rw [Matrix.SpecialLinearGroup.coe_mul,←Matrix.mul_assoc,hea,Matrix.mul_assoc,heb,
    ←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul]

/-- The inverse right-index actor is a genuine left Gamma0 action on the original Hecke representatives. -/
@[instance_reducible]
noncomputable def lpsHeckeIndexAction (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    MulAction (CongruenceSubgroup.Gamma0 N) (Option (Fin p)) where
  smul γ i := lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) i
  one_smul i := by
    change lpsHeckeRightIndex N p hNp (1:SL(2,ℤ))⁻¹ _ i=i
    simpa only [inv_one] using lpsHeckeRightIndex_one N p hNp i
  mul_smul γ δ i := by
    change lpsHeckeRightIndex N p hNp ((γ:SL(2,ℤ))*(δ:SL(2,ℤ)))⁻¹ _ i =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹ _
        (lpsHeckeRightIndex N p hNp (δ:SL(2,ℤ))⁻¹ _ i)
    simpa only [mul_inv_rev] using lpsHeckeRightIndex_mul N p hNp
      (δ:SL(2,ℤ))⁻¹ (γ:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem δ.property)
      ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) i

/-- The infinity index is fixed exactly by original Gamma0(Np). -/
lemma lpsHeckeRightIndex_none_iff (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    lpsHeckeRightIndex N p hNp γ hγ none=none ↔ γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by
  constructor
  · intro hi
    obtain ⟨δ,hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ none
    rw [hi] at he
    exact lpsHeckeIntersection_of_conjugate N p γ δ hδ
      (lpsHeckeRightFactorGL ℝ p none none γ δ he)
  · intro hγ'
    obtain ⟨δ,_hδ,he⟩ := lpsHeckeIntersection_conjugateMatrix N p γ hγ'
    exact lpsHeckeRightIndex_of_factor N p hNp γ hγ none none δ he

/-- The genuine finite-action infinity stabilizer is the actual relative Gamma0(Np) subgroup. -/
lemma lpsHeckeIndex_stabilizer_none (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) (none:Option (Fin p)) =
      (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N) := by
  let := lpsHeckeIndexAction N p hNp
  ext γ
  change lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹ _ none=none ↔
    (γ:SL(2,ℤ)) ∈ CongruenceSubgroup.Gamma0 (N*p)
  rw [lpsHeckeRightIndex_none_iff]
  exact inv_mem_iff

/-- Every original representative index occurs in the actual infinity orbit. -/
lemma lpsHeckeIndex_orbit_none (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.orbit (CongruenceSubgroup.Gamma0 N) (none:Option (Fin p))=Set.univ := by
  let := lpsHeckeIndexAction N p hNp
  apply Set.eq_univ_of_forall
  intro i
  obtain ⟨δ,γ,_hδ,hγ,he⟩ := lpsHeckeUpperMatrix_doubleCoset N p hNp i
  have hf : lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p i := by
    rw [he,←Matrix.mul_assoc,←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.one_mul]
  refine ⟨⟨γ⁻¹,(CongruenceSubgroup.Gamma0 N).inv_mem hγ⟩,?_⟩
  change lpsHeckeRightIndex N p hNp (γ⁻¹)⁻¹ _ none=i
  simpa only [inv_inv] using lpsHeckeRightIndex_of_factor N p hNp γ hγ none i δ⁻¹ hf

/-- The zero finite index is fixed exactly by the genuine second intersection. -/
lemma lpsHeckeRightIndex_some_zero_iff (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    lpsHeckeRightIndex N p hNp γ hγ (some ⟨0,(Fact.out:p.Prime).pos⟩)=
        some ⟨0,(Fact.out:p.Prime).pos⟩ ↔
      γ ∈ lpsHeckeConjugateIntersection N p := by
  constructor
  · intro hi
    obtain ⟨δ,_hδ,he⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ _
    rw [hi] at he
    exact lpsHeckeConjugateIntersection_of_factor N p γ δ hγ
      (lpsHeckeRightFactorGL ℝ p _ _ γ δ he)
  · intro hγ'
    obtain ⟨δ,_hδ,he⟩ := lpsHeckeConjugateIntersection_factorMatrix N p γ hγ'
    exact lpsHeckeRightIndex_of_factor N p hNp γ hγ _ _ δ he

/-- The finite-action zero stabilizer is the actual second intersection inside original Gamma0(N). -/
lemma lpsHeckeIndex_stabilizer_some_zero (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N)
      (some ⟨0,(Fact.out:p.Prime).pos⟩:Option (Fin p)) =
      (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N) := by
  let := lpsHeckeIndexAction N p hNp
  ext γ
  change lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹ _ _ = _ ↔
    (γ:SL(2,ℤ)) ∈ lpsHeckeConjugateIntersection N p
  rw [lpsHeckeRightIndex_some_zero_iff]
  exact inv_mem_iff

/-- The genuine inverse-actor action is transitive from every original Hecke index. -/
lemma lpsHeckeIndex_orbit (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.orbit (CongruenceSubgroup.Gamma0 N) i=Set.univ := by
  let := lpsHeckeIndexAction N p hNp
  have hall (j : Option (Fin p)) : j ∈ MulAction.orbit (CongruenceSubgroup.Gamma0 N) none := by
    rw [lpsHeckeIndex_orbit_none]
    trivial
  obtain ⟨γ,hγ⟩ := hall i
  apply Set.eq_univ_of_forall
  intro j
  obtain ⟨δ,hδ⟩ := hall j
  refine ⟨δ*γ⁻¹,?_⟩
  change (δ*γ⁻¹) • i=j
  change γ • none=i at hγ
  change δ • none=j at hδ
  rw [mul_smul,←hγ,inv_smul_smul,hδ]

end
end QEC.Coding.TannerLiftedProduct
