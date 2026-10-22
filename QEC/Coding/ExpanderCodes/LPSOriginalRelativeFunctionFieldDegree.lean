/-
Relative degrees of the original modular function fields along actual levels.

For N dividing M and 4 dividing N, the proved pullback of the whole original
meromorphic field supplies the inclusion of the same C(j,j_N) into C(j,j_M).
The exact absolute degrees and subgroup-index tower formula then give its
relative degree. The original filled level map has this many points in every
fibre over an interior point; at a coprime prime extension the degree is p+1.

These are derived internal APIs for the original analytic modular-curve route.
The PK22 main.tex passages th:qLDPC (lines 231-238) and ex:Xpq (lines 484-486)
retain their registered scope; this module asserts no new public realization.
-/

import QEC.Coding.ExpanderCodes.LPSOriginalFullFieldLevelPullback
import QEC.Coding.ExpanderCodes.LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane
noncomputable section
/-- The relative degree of the same original generated fields equals the actual integral congruence-subgroup relative index. -/
lemma lpsOriginalGeneratedFunctionField_relfinrank_eq
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalGeneratedFunctionField_finiteDimensional N hposN
  let GN : Subgroup (GL (Fin 2) ℝ) :=
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let GM : Subgroup (GL (Fin 2) ℝ) :=
    (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))
  have hle : GM ≤ GN := Subgroup.map_mono (lpsGamma0_level_le N M hNM)
  have htop : GN ≤ 𝒮ℒ := (CongruenceSubgroup.Gamma0 N).map_le_range _
  have hG := Subgroup.relIndex_mul_relIndex GM GN 𝒮ℒ hle htop
  have hidx : GM.relIndex GN =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
    change ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
      ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) = _
    exact Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective
  rw [hidx] at hG
  have hF := IntermediateField.finrank_bot_mul_relfinrank
    (lpsOriginalGeneratedFunctionField_level_le N M hNM hN hposN hposM)
  rw [lpsOriginalGeneratedFunctionField_finrank_eq N hposN,
    lpsOriginalGeneratedFunctionField_finrank_eq M hposM] at hF
  change GN.relIndex 𝒮ℒ *
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) = GM.relIndex 𝒮ℒ at hF
  have hp : 0 < Module.finrank (FractionRing (Polynomial ℂ))
      (lpsOriginalGeneratedFunctionField N hposN) :=
    (Module.finrank_pos_iff_of_free (FractionRing (Polynomial ℂ))
      (lpsOriginalGeneratedFunctionField N hposN)).mpr inferInstance
  rw [lpsOriginalGeneratedFunctionField_finrank_eq N hposN] at hp
  change 0 < GN.relIndex 𝒮ℒ at hp
  apply Nat.eq_of_mul_eq_mul_left hp
  exact hF.trans (by simpa only [Nat.mul_comm] using hG.symm)

/-- The same original relative degree equals every full filled fibre cardinality over an interior point. -/
lemma lpsOriginalGeneratedFunctionField_relfinrank_filledFibre
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) =
      Nat.card {x : LPSOriginalFilledCurve M |
        lpsOriginalFilledForgetLevel N M hNM x = Sum.inl y} := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [lpsOriginalGeneratedFunctionField_relfinrank_eq N M hNM hN hposN hposM]
  exact (lpsOriginalInteriorForgetLevel_fibre_card N M hNM hN y).symm.trans
    (Nat.card_congr (lpsOriginalFilledInteriorFibreEquiv N M hNM y))

/-- The same original coprime-prime function-field extension has degree p+1. -/
lemma lpsOriginalPrimeGeneratedFunctionField_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (hposN : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField (N*p)
        (Nat.mul_pos hposN (Fact.out : p.Prime).pos)) = p+1 := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  rw [lpsOriginalGeneratedFunctionField_relfinrank_eq N (N*p)
    (dvd_mul_right N p) hN hposN (Nat.mul_pos hposN (Fact.out : p.Prime).pos)]
  exact lpsHeckeIntersection_index N p hNp
end
end QEC.Coding.TannerLiftedProduct
