import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.CompactGroup
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingStabilizer
import QEC.Coding.HighDimensionalExpander.Hecke.CartanDecomposition

/-!
# Unique normal forms in the integral projective cyclic group

This module upgrades the finite normal-form parametrization to a bijection.
Equality of two projective normal forms forces equality of their Frobenius
conjugation actions, hence equality of their canonical cyclic exponents; the
remaining constant kernel is proved to be exactly `F_qˣ`.  It follows that
the projective unit group of the integral cyclic order has the exact source
cardinality from LSV05b Proposition 3.5.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

theorem quotientMk_eq_of_globalConstantPGL_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : globalConstantPGLHom P r u = globalConstantPGLHom P r v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by
  change Matrix.ProjGenLinGroup.mk
      (Units.map (constantMatrixEmbedding P r).toMonoidHom u) =
    Matrix.ProjGenLinGroup.mk
      (Units.map (constantMatrixEmbedding P r).toMonoidHom v) at h
  obtain ⟨a, ha⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq h
  have hmat := congrArg Units.val ha
  let i0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  let i1 : Fin r.matrixRank := ⟨1, Rank.two_le_matrixRank r⟩
  change constantMatrix P r u =
      Matrix.scalar (Fin r.matrixRank) (a : SplittingFunctionField P r) *
        constantMatrix P r v at hmat
  rw [constantMatrix, constantMatrix, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal] at hmat
  have h0 := congrFun (congrFun hmat i0) i0
  have h1 := congrFun (congrFun hmat i1) i1
  simp [i0, i1] at h0 h1
  have h0' : algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r) (u : ConstantExtension P r) =
        (a : SplittingFunctionField P r) *
          algebraMap (ConstantExtension P r)
            (SplittingFunctionField P r) (v : ConstantExtension P r) := by
    exact h0
  have h1' : algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r)
        ((constantFrobenius P r).symm (u : ConstantExtension P r)) =
      (a : SplittingFunctionField P r) *
        algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
          ((constantFrobenius P r).symm (v : ConstantExtension P r)) := by
    exact h1
  have hv0 : algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r) (v : ConstantExtension P r) ≠ 0 := by simp
  have hv1 : algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r)
        ((constantFrobenius P r).symm (v : ConstantExtension P r)) ≠ 0 := by simp
  have hcross :
      algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
          (u : ConstantExtension P r) *
        algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
          ((constantFrobenius P r).symm (v : ConstantExtension P r)) =
      algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
          (v : ConstantExtension P r) *
        algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
          ((constantFrobenius P r).symm (u : ConstantExtension P r)) := by
    calc
      _ = (a : SplittingFunctionField P r) *
          algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
            (v : ConstantExtension P r) *
          algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
            ((constantFrobenius P r).symm (v : ConstantExtension P r)) := by
              rw [h0']
      _ = algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
          (v : ConstantExtension P r) *
        ((a : SplittingFunctionField P r) *
          algebraMap (ConstantExtension P r) (SplittingFunctionField P r)
            ((constantFrobenius P r).symm (v : ConstantExtension P r))) := by ring
      _ = _ := by rw [← h1']
  have hcrossConst :
      (u : ConstantExtension P r) *
          (constantFrobenius P r).symm (v : ConstantExtension P r) =
        (v : ConstantExtension P r) *
          (constantFrobenius P r).symm (u : ConstantExtension P r) := by
    apply (algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r)).injective
    simpa only [map_mul] using hcross
  have hsu : (constantFrobenius P r).symm
      (u : ConstantExtension P r) ≠ 0 := by simp
  have hsv : (constantFrobenius P r).symm
      (v : ConstantExtension P r) ≠ 0 := by simp
  have hfixedSymm :
      (constantFrobenius P r).symm
          ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
        (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have hdiv :
        (constantFrobenius P r).symm (u : ConstantExtension P r) /
            (constantFrobenius P r).symm (v : ConstantExtension P r) =
          (u : ConstantExtension P r) / (v : ConstantExtension P r) := by
      apply (div_eq_div_iff hsv (Units.ne_zero v)).mpr
      simpa [mul_comm] using hcrossConst.symm
    simpa [map_mul, map_inv, div_eq_mul_inv] using hdiv
  have hfixed :
      constantFrobenius P r
          ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
        (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have hf := congrArg (constantFrobenius P r) hfixedSymm
    simpa using hf.symm
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_constantFrobenius_eq P r _ hfixed
  have hc0 : c ≠ 0 := by
    intro hcZero
    rw [hcZero, map_zero] at hc
    exact (mul_ne_zero (Units.ne_zero u) (inv_ne_zero (Units.ne_zero v))) hc.symm
  apply QuotientGroup.eq_iff_div_mem.mpr
  change u / v ∈ baseScalarUnits P r
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simpa [baseScalarUnitHom, div_eq_mul_inv] using hc

theorem globalNormalForm_conj_constant
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (c : ConstantExtension P r) :
    ((Units.map (constantMatrixEmbedding P r).toMonoidHom u *
        cyclicGenerator P r ^ j :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) : Matrix _ _ _) *
      constantMatrix P r c *
      (((Units.map (constantMatrixEmbedding P r).toMonoidHom u *
          cyclicGenerator P r ^ j)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) =
      constantMatrix P r (Multiplicative.ofAdd (j : ℤ) • c) := by
  have hz := globalCyclic_zpow_conj_constant P r (j : ℤ) c
  have hz' :
      ((cyclicGenerator P r ^ j :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) *
        constantMatrix P r c *
        (((cyclicGenerator P r ^ j)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) =
      constantMatrix P r (Multiplicative.ofAdd (j : ℤ) • c) := by
    simpa only [zpow_natCast] using hz
  let U := Units.map (constantMatrixEmbedding P r).toMonoidHom u
  let Z := cyclicGenerator P r ^ j
  change ((U * Z : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r)) : Matrix _ _ _) *
      constantMatrix P r c *
      (((U * Z)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) : Matrix _ _ _) = _
  simp only [mul_inv_rev, Units.val_mul]
  calc
    ((U : Matrix _ _ _) * (Z : Matrix _ _ _)) * constantMatrix P r c *
          (((Z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) *
          ((U⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _)) =
        (U : Matrix _ _ _) *
          ((Z : Matrix _ _ _) * constantMatrix P r c *
            ((Z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _)) *
          ((U⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) := by group
    _ = (U : Matrix _ _ _) *
          constantMatrix P r (Multiplicative.ofAdd (j : ℤ) • c) *
          ((U⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) := by rw [hz']
    _ = constantMatrix P r (Multiplicative.ofAdd (j : ℤ) • c) := by
      change constantMatrix P r u *
          constantMatrix P r (Multiplicative.ofAdd (j : ℤ) • c) *
          constantMatrix P r (u⁻¹ : (ConstantExtension P r)ˣ) = _
      rw [← constantMatrixEmbedding_apply,
        ← constantMatrixEmbedding_apply, ← constantMatrixEmbedding_apply,
        ← map_mul, ← map_mul]
      apply congrArg (constantMatrixEmbedding P r)
      calc
        (u : ConstantExtension P r) * (Multiplicative.ofAdd (j : ℤ) • c) *
            (u⁻¹ : (ConstantExtension P r)ˣ) =
          ((u : ConstantExtension P r) * (u⁻¹ : (ConstantExtension P r)ˣ)) *
            (Multiplicative.ofAdd (j : ℤ) • c) := by ring
        _ = Multiplicative.ofAdd (j : ℤ) • c := by rw [Units.mul_inv, one_mul]

set_option maxHeartbeats 800000 in
theorem globalNormalForm_exponent_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ) (j k : ℕ)
    (hj : j < r.matrixRank) (hk : k < r.matrixRank)
    (h : globalConstantPGLHom P r u *
          globalCyclicGeneratorPGL P r ^ j =
        globalConstantPGLHom P r v *
          globalCyclicGeneratorPGL P r ^ k) :
    j = k := by
  change Matrix.ProjGenLinGroup.mk
      (Units.map (constantMatrixEmbedding P r).toMonoidHom u *
        cyclicGenerator P r ^ j) =
    Matrix.ProjGenLinGroup.mk
      (Units.map (constantMatrixEmbedding P r).toMonoidHom v *
        cyclicGenerator P r ^ k) at h
  obtain ⟨a, ha⟩ :=
    SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq h
  have hconj (c : ConstantExtension P r) :
      constantMatrix P r (Multiplicative.ofAdd (j : ℤ) • c) =
        constantMatrix P r (Multiplicative.ofAdd (k : ℤ) • c) := by
    rw [← globalNormalForm_conj_constant P r u j c,
      ← globalNormalForm_conj_constant P r v k c]
    have hmat := congrArg Units.val ha
    let A := Units.map (constantMatrixEmbedding P r).toMonoidHom u *
      cyclicGenerator P r ^ j
    let B := Units.map (constantMatrixEmbedding P r).toMonoidHom v *
      cyclicGenerator P r ^ k
    let S := Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) a
    change ((A : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) : Matrix _ _ _) *
        constantMatrix P r c *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) =
      ((B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (SplittingFunctionField P r)) : Matrix _ _ _) *
        constantMatrix P r c *
        ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _)
    have hAB : A = S * B := ha
    rw [hAB]
    have hScomm (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :
        (S : Matrix _ _ _) * M = M * (S : Matrix _ _ _) := by
      dsimp [S]
      exact Matrix.scalar_comm _ (fun b => Commute.all _ b) M
    have hScancel (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) :
        (S : Matrix _ _ _) * M *
            ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _) = M := by
      rw [hScomm]
      simp only [mul_assoc]
      rw [← Units.val_mul]
      simp
    calc
      (((S * B : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) : Matrix _ _ _) *
          constantMatrix P r c *
          (((S * B)⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _)) =
        (S : Matrix _ _ _) *
          ((B : Matrix _ _ _) * constantMatrix P r c *
            ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (SplittingFunctionField P r)) : Matrix _ _ _)) *
          ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) := by
              simp only [mul_inv_rev, Units.val_mul]
              group
      _ = (B : Matrix _ _ _) * constantMatrix P r c *
          ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (SplittingFunctionField P r)) : Matrix _ _ _) := by
              let M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                  (SplittingFunctionField P r) :=
                (B : Matrix _ _ _) * constantMatrix P r c *
                  ((B⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                    (SplittingFunctionField P r)) : Matrix _ _ _)
              calc
                _ = (S : Matrix _ _ _) * M *
                    ((S⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
                      (SplittingFunctionField P r)) : Matrix _ _ _) := by
                        dsimp [M]
                _ = M := hScancel M
                _ = _ := by
                  dsimp [M]
  have hfrob : constantFrobenius P r ^ j = constantFrobenius P r ^ k := by
    apply AlgEquiv.ext
    intro c
    have hc := constantMatrixEmbedding_injective P r (hconj c)
    change (((constantFrobenius P r).toRingEquiv ^ (j : ℤ)) c) =
      (((constantFrobenius P r).toRingEquiv ^ (k : ℤ)) c) at hc
    rw [zpow_natCast, zpow_natCast] at hc
    have haction (n : ℕ) (x : ConstantExtension P r) :
        ((constantFrobenius P r).toRingEquiv ^ n) x =
          (constantFrobenius P r ^ n) x := by
      induction n with
      | zero => simp
      | succ n ih => simp [pow_succ]
    exact (haction j c).symm.trans (hc.trans (haction k c))
  by_cases hkj : k ≤ j
  · have hpow : constantFrobenius P r ^ (j - k) = 1 := by
      apply mul_right_cancel (b := constantFrobenius P r ^ k)
      rw [← pow_add, Nat.sub_add_cancel hkj, hfrob, one_mul]
    have hdiffLt : j - k < r.matrixRank :=
      lt_of_le_of_lt (Nat.sub_le j k) hj
    have hzero := eq_zero_of_constantFrobenius_pow_eq_one
      P r (j - k) hdiffLt hpow
    omega
  · have hjk : j ≤ k := Nat.le_of_not_ge hkj
    have hpow : constantFrobenius P r ^ (k - j) = 1 := by
      apply mul_right_cancel (b := constantFrobenius P r ^ j)
      rw [← pow_add, Nat.sub_add_cancel hjk, hfrob.symm, one_mul]
    have hdiffLt : k - j < r.matrixRank :=
      lt_of_le_of_lt (Nat.sub_le k j) hk
    have hzero := eq_zero_of_constantFrobenius_pow_eq_one
      P r (k - j) hdiffLt hpow
    omega

theorem globalNormalForm_source_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ) (j k : ℕ)
    (hj : j < r.matrixRank) (hk : k < r.matrixRank)
    (h : globalConstantPGLHom P r u *
          globalCyclicGeneratorPGL P r ^ j =
        globalConstantPGLHom P r v *
          globalCyclicGeneratorPGL P r ^ k) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
        QuotientGroup.mk v ∧ j = k := by
  have hjk := globalNormalForm_exponent_eq P r u v j k hj hk h
  subst k
  have hconstant : globalConstantPGLHom P r u =
      globalConstantPGLHom P r v := by
    apply mul_right_cancel (b := globalCyclicGeneratorPGL P r ^ j)
    exact h
  exact ⟨quotientMk_eq_of_globalConstantPGL_eq P r u v hconstant, rfl⟩

theorem globalConstantPGLHom_baseScalar
    (P : BasePrime) (r : Rank) (a : (BaseField P)ˣ) :
    globalConstantPGLHom P r
      (Units.map
        (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a) = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (Units.map (constantMatrixEmbedding P r).toMonoidHom
        (Units.map
          (algebraMap (BaseField P)
            (ConstantExtension P r)).toMonoidHom a)) = 1
  let aSplit : (SplittingFunctionField P r)ˣ :=
    Units.map (algebraMap (ConstantExtension P r)
      (SplittingFunctionField P r)).toMonoidHom
        (Units.map
          (algebraMap (BaseField P)
            (ConstantExtension P r)).toMonoidHom a)
  have hgl : Units.map (constantMatrixEmbedding P r).toMonoidHom
        (Units.map
          (algebraMap (BaseField P)
            (ConstantExtension P r)).toMonoidHom a) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) aSplit := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst j
      simp [constantMatrixEmbedding, constantMatrix, aSplit]
    · simp [constantMatrixEmbedding, constantMatrix, aSplit, hij]
  rw [hgl]
  exact Matrix.ProjGenLinGroup.mk_scalar _

theorem globalConstantPGL_eq_of_quotientMk_eq
    (P : BasePrime) (r : Rank)
    (u v : (ConstantExtension P r)ˣ)
    (h : (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v) :
    globalConstantPGLHom P r u = globalConstantPGLHom P r v := by
  have hdiv : u / v ∈ baseScalarUnits P r :=
    QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨a, ha⟩ := hdiv
  apply div_eq_one.mp
  rw [← map_div]
  rw [← ha]
  simpa [baseScalarUnitHom] using globalConstantPGLHom_baseScalar P r a

noncomputable def globalIntegralProjectiveNormalForm
    (P : BasePrime) (r : Rank) :
    ConstantProjectiveClass P r × Fin r.matrixRank →
      GlobalIntegralCompactCyclicSubgroup P r :=
  fun x => ⟨globalConstantPGLHom P r
      (constantClassRepresentative P r x.1) *
        globalCyclicGeneratorPGL P r ^ (x.2 : ℕ), by
    exact (GlobalIntegralCompactCyclicSubgroup P r).mul_mem
      (Subgroup.subset_closure
        (Set.mem_union_left _
          (Set.mem_range_self (constantClassRepresentative P r x.1))))
      ((GlobalIntegralCompactCyclicSubgroup P r).pow_mem
        (Subgroup.subset_closure
          (Set.mem_union_right _ (Set.mem_singleton _))) x.2)⟩

theorem globalIntegralProjectiveNormalForm_bijective
    (P : BasePrime) (r : Rank) :
    Function.Bijective (globalIntegralProjectiveNormalForm P r) := by
  constructor
  · rintro ⟨x, j⟩ ⟨y, k⟩ hxy
    have hval := congrArg Subtype.val hxy
    obtain ⟨hconst, hexp⟩ := globalNormalForm_source_eq P r
      (constantClassRepresentative P r x)
      (constantClassRepresentative P r y) j k j.isLt k.isLt hval
    apply Prod.ext
    · simpa [constantClassRepresentative] using hconst
    · exact Fin.ext hexp
  · rintro ⟨g, hg⟩
    obtain ⟨c, j, hj, hform⟩ :=
      exists_constant_mul_cyclic_pow_of_mem_globalIntegralCompact P r g hg
    let x : ConstantProjectiveClass P r := QuotientGroup.mk c
    let jf : Fin r.matrixRank := ⟨j, hj⟩
    refine ⟨(x, jf), ?_⟩
    apply Subtype.ext
    change globalConstantPGLHom P r (constantClassRepresentative P r x) *
        globalCyclicGeneratorPGL P r ^ j = g
    rw [globalConstantPGL_eq_of_quotientMk_eq P r
      (constantClassRepresentative P r x) c]
    · exact hform.symm
    · simp [x, constantClassRepresentative]

noncomputable def globalIntegralProjectiveNormalFormEquiv
    (P : BasePrime) (r : Rank) :
    ConstantProjectiveClass P r × Fin r.matrixRank ≃
      GlobalIntegralCompactCyclicSubgroup P r :=
  Equiv.ofBijective (globalIntegralProjectiveNormalForm P r)
    (globalIntegralProjectiveNormalForm_bijective P r)

theorem natCard_globalIntegralCompactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    Nat.card (GlobalIntegralCompactCyclicSubgroup P r) =
      r.matrixRank * ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by
  rw [Nat.card_congr (globalIntegralProjectiveNormalFormEquiv P r).symm,
    Nat.card_prod, Nat.card_fin, natCard_constantProjectiveClass]
  exact Nat.mul_comm _ _

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
