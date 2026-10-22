import QEC.Coding.ExpanderCodes.LPSHeckeCosetAction
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Actual p+1 Hecke cosets

The genuine action and proved stabilizers give both nonnormal left-coset bijections, exact representative evaluation and exact relative indices. Their inverse representatives support the subsequent domain covers; adjugates are not permuted through the same left list.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

/-- The actual nonnormal relative Gamma0(Np) left cosets biject with all p+1 original indices. -/
noncomputable def lpsHeckeIntersectionCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    CongruenceSubgroup.Gamma0 N ⧸
      (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
        Option (Fin p) := by
  let := lpsHeckeIndexAction N p hNp
  exact (Subgroup.quotientEquivOfEq (lpsHeckeIndex_stabilizer_none N p hNp).symm).trans
    (((MulAction.orbitEquivQuotientStabilizer (CongruenceSubgroup.Gamma0 N)
      (none:Option (Fin p))).symm).trans
      ((Equiv.setCongr (lpsHeckeIndex_orbit_none N p hNp)).trans (Equiv.Set.univ (Option (Fin p)))))

/-- The exact original relative Gamma0(Np) index is p+1. -/
lemma lpsHeckeIntersection_index (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    ((CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)).index=p+1 := by
  change Nat.card (CongruenceSubgroup.Gamma0 N ⧸
    (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N))=p+1
  rw [Nat.card_congr (lpsHeckeIntersectionCosetEquiv N p hNp),Nat.card_eq_fintype_card]
  simp

/-- The actual left-coset equivalence evaluates by the inverse right-index actor. -/
lemma lpsHeckeIntersectionCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsHeckeIntersectionCosetEquiv N p hNp (QuotientGroup.mk γ) =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) none := by
  rfl

/-- The actual second-intersection left cosets biject with all p+1 original Hecke indices. -/
noncomputable def lpsHeckeConjugateCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    CongruenceSubgroup.Gamma0 N ⧸
      (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
        Option (Fin p) := by
  letI := lpsHeckeIndexAction N p hNp
  exact (Subgroup.quotientEquivOfEq (lpsHeckeIndex_stabilizer_some_zero N p hNp).symm).trans
    (((MulAction.orbitEquivQuotientStabilizer (CongruenceSubgroup.Gamma0 N)
      (some ⟨0,(Fact.out:p.Prime).pos⟩:Option (Fin p))).symm).trans
      ((Equiv.setCongr (lpsHeckeIndex_orbit N p hNp _)).trans (Equiv.Set.univ (Option (Fin p)))))

/-- The second true left-coset equivalence evaluates by the inverse actor at the zero finite index. -/
lemma lpsHeckeConjugateCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsHeckeConjugateCosetEquiv N p hNp (QuotientGroup.mk γ) =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property)
        (some ⟨0,(Fact.out:p.Prime).pos⟩) := by
  rfl

/-- The exact relative index of the actual second intersection is p+1. -/
lemma lpsHeckeConjugateIntersection_index (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    ((lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N)).index=p+1 := by
  change Nat.card (CongruenceSubgroup.Gamma0 N ⧸
    (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N))=p+1
  rw [Nat.card_congr (lpsHeckeConjugateCosetEquiv N p hNp),Nat.card_eq_fintype_card]
  simp

end
end QEC.Coding.TannerLiftedProduct
