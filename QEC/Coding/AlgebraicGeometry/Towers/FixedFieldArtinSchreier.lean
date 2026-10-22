import QEC.Coding.FiniteFieldMultiplication.Field

import Mathlib.FieldTheory.Finite.Trace

/-!
# The concrete `F256/F16` Artin--Schreier fibre

This file isolates the finite-field algebra used by the split paths in the
Garcia--Stichtenoth tower.  The subfield and every fibre are constructed from
finite-field maps; no tower, place-count, genus, or divisor conclusion is
stored as data here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- A concrete field with sixteen elements, used as the relative constant subfield. -/
abbrev F16 : Type := GaloisField 2 4

noncomputable instance f16Fintype : Fintype F16 := Fintype.ofFinite F16

theorem f16_card : Fintype.card F16 = 16 := by
  rw [Fintype.card_eq_nat_card]
  simpa using (GaloisField.card 2 4 (by norm_num : (4 : ℕ) ≠ 0))

private theorem f16_finrank : Module.finrank (ZMod 2) F16 = 4 := by
  exact GaloisField.finrank 2 (by norm_num : (4 : ℕ) ≠ 0)

/-- A fixed `ZMod 2`-algebra embedding of `F16` into the concrete `F256`. -/
noncomputable def f16Embedding : F16 →ₐ[ZMod 2] F256 :=
  Classical.choice
    (FiniteField.nonempty_algHom_of_finrank_dvd
      (F := ZMod 2) (K := F16) (L := F256) (by
        rw [f16_finrank, f256_finrank]
        norm_num))

noncomputable instance f256F16Algebra : Algebra F16 F256 :=
  f16Embedding.toRingHom.toAlgebra

noncomputable instance f256F16ScalarTower : IsScalarTower (ZMod 2) F16 F256 :=
  IsScalarTower.of_algebraMap_eq fun c => (f16Embedding.commutes c).symm

/-- The concrete extension `F256/F16` has degree two. -/
theorem f256_finrank_over_f16 : Module.finrank F16 F256 = 2 := by
  have h := Module.finrank_mul_finrank (ZMod 2) F16 F256
  rw [f16_finrank, f256_finrank] at h
  omega

/-- The relative Artin--Schreier map `y ↦ y^16 + y` on `F256`. -/
noncomputable def f256ArtinSchreier : F256 →ₗ[F16] F256 :=
  (FiniteField.frobeniusAlgHom F16 F256).toLinearMap + LinearMap.id

@[simp] theorem f256ArtinSchreier_apply (x : F256) :
    f256ArtinSchreier x = x ^ 16 + x := by
  change x ^ Fintype.card F16 + x = x ^ 16 + x
  rw [f16_card]

private theorem algebraMap_trace_eq_f256ArtinSchreier (x : F256) :
    algebraMap F16 F256 (Algebra.trace F16 F256 x) = f256ArtinSchreier x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  simp only [f256_finrank_over_f16, Nat.card_eq_fintype_card, f16_card]
  norm_num [Finset.sum_range_succ, f256ArtinSchreier_apply, add_comm]

private theorem f256ArtinSchreier_ker_eq_trace_ker :
    LinearMap.ker f256ArtinSchreier = LinearMap.ker (Algebra.trace F16 F256) := by
  ext x
  simp only [LinearMap.mem_ker]
  rw [← algebraMap_trace_eq_f256ArtinSchreier]
  simp

noncomputable instance f256ArtinSchreierKernelFintype :
    Fintype (LinearMap.ker f256ArtinSchreier) := Fintype.ofFinite _

/-- The additive kernel has relative dimension one. -/
theorem f256ArtinSchreier_ker_finrank :
    Module.finrank F16 (LinearMap.ker f256ArtinSchreier) = 1 := by
  rw [f256ArtinSchreier_ker_eq_trace_ker]
  have hrange : LinearMap.range (Algebra.trace F16 F256) = ⊤ :=
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective F16 F256)
  have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace F16 F256)
  rw [hrange] at h
  simp only [finrank_top, Module.finrank_self, f256_finrank_over_f16] at h
  omega

/-- The additive kernel contains exactly sixteen constants. -/
theorem f256ArtinSchreier_ker_card :
    Fintype.card (LinearMap.ker f256ArtinSchreier) = 16 := by
  rw [Module.card_eq_pow_finrank (K := F16), f16_card,
    f256ArtinSchreier_ker_finrank]
  norm_num

/-- One actual Artin--Schreier preimage of the relative norm of `x`. -/
noncomputable def f256ArtinSchreierRoot (x : F256) : F256 :=
  Classical.choose
    (Algebra.trace_surjective F16 F256 (Algebra.norm F16 x))

private theorem f256ArtinSchreierRoot_trace (x : F256) :
    Algebra.trace F16 F256 (f256ArtinSchreierRoot x) = Algebra.norm F16 x :=
  Classical.choose_spec
    (Algebra.trace_surjective F16 F256 (Algebra.norm F16 x))

/-- The chosen preimage solves the source equation `y^16 + y = x^17`. -/
theorem f256ArtinSchreierRoot_spec (x : F256) :
    f256ArtinSchreier (f256ArtinSchreierRoot x) = x ^ 17 := by
  calc
    f256ArtinSchreier (f256ArtinSchreierRoot x) =
        algebraMap F16 F256 (Algebra.trace F16 F256 (f256ArtinSchreierRoot x)) :=
      (algebraMap_trace_eq_f256ArtinSchreier _).symm
    _ = algebraMap F16 F256 (Algebra.norm F16 x) := by
      rw [f256ArtinSchreierRoot_trace]
    _ = x ^ 17 := by
      rw [FiniteField.algebraMap_norm_eq_pow]
      norm_num [Nat.card_eq_fintype_card, f16_card, f256_card]

/-- The literal finite fibre used for one split-path step. -/
noncomputable def f256ArtinSchreierRoots (x : F256) : Finset F256 :=
  Finset.univ.filter fun y => f256ArtinSchreier y = x ^ 17

theorem mem_f256ArtinSchreierRoots (x y : F256) :
    y ∈ f256ArtinSchreierRoots x ↔ y ^ 16 + y = x ^ 17 := by
  simp [f256ArtinSchreierRoots, f256ArtinSchreier_apply]

private noncomputable def f256ArtinSchreierKernelEquivRoots (x : F256) :
    LinearMap.ker f256ArtinSchreier ≃ ↥(f256ArtinSchreierRoots x) where
  toFun y := ⟨f256ArtinSchreierRoot x + y, by
    simp only [f256ArtinSchreierRoots, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [map_add, f256ArtinSchreierRoot_spec, y.property, add_zero]⟩
  invFun y := ⟨y - f256ArtinSchreierRoot x, by
    change f256ArtinSchreier (y - f256ArtinSchreierRoot x) = 0
    rw [map_sub, f256ArtinSchreierRoot_spec]
    have hy : f256ArtinSchreier (y : F256) = x ^ 17 := by
      simpa only [f256ArtinSchreierRoots, Finset.mem_filter, Finset.mem_univ, true_and]
        using y.property
    rw [hy, sub_self]⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- Every split-path Artin--Schreier fibre has exactly sixteen elements. -/
theorem f256ArtinSchreierRoots_card (x : F256) :
    (f256ArtinSchreierRoots x).card = 16 := by
  calc
    (f256ArtinSchreierRoots x).card =
        Fintype.card ↥(f256ArtinSchreierRoots x) := (Fintype.card_coe _).symm
    _ = Fintype.card (LinearMap.ker f256ArtinSchreier) :=
      Fintype.card_congr (f256ArtinSchreierKernelEquivRoots x).symm
    _ = 16 := f256ArtinSchreier_ker_card

end


end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
