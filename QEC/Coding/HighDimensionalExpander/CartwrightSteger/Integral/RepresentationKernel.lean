import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingSkewRepresentation

/-!
# Agreement of the global and building integral projective kernels

The global split representation and the building-place representation of the
same integral skew Laurent unit group have exactly the same projective kernel.
No presentation relations are assumed: the result follows from the proved
unique normal forms on both sides.  The first isomorphism theorem therefore
upgrades the global/local compact correspondence to a genuine group
isomorphism.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

private theorem global_normal_data_of_eq_one
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ)
    (h : globalConstantPGLHom P r c *
        globalCyclicGeneratorPGL P r ^ n = 1) :
    (QuotientGroup.mk c : ConstantProjectiveClass P r) =
        QuotientGroup.mk 1 ∧
      n % (r.matrixRank : ℤ) = 0 := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank :=
    (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  have hmj : m = (j : ℤ) := (Int.toNat_of_nonneg hmNonneg).symm
  have hreduce : globalCyclicGeneratorPGL P r ^ n =
      globalCyclicGeneratorPGL P r ^ j := by
    calc
      _ = globalCyclicGeneratorPGL P r ^ m :=
        zpow_eq_zpow_emod' n (globalCyclicGeneratorPGL_pow_matrixRank P r)
      _ = globalCyclicGeneratorPGL P r ^ (j : ℤ) := by rw [hmj]
      _ = _ := zpow_natCast _ j
  have hcanonical :
      globalConstantPGLHom P r c * globalCyclicGeneratorPGL P r ^ j =
        globalConstantPGLHom P r 1 * globalCyclicGeneratorPGL P r ^ 0 := by
    rw [← hreduce, h]
    simp
  obtain ⟨hc, hj0⟩ := globalNormalForm_source_eq P r c 1 j 0
    hj (by exact hdNat) hcanonical
  refine ⟨hc, ?_⟩
  change m = 0
  rw [hmj, hj0]
  rfl

private theorem building_normal_data_of_eq_one
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ)
    (h : buildingConstantPGLHom P r c *
        buildingCyclicGeneratorPGL P r ^ n = 1) :
    (QuotientGroup.mk c : ConstantProjectiveClass P r) =
        QuotientGroup.mk 1 ∧
      n % (r.matrixRank : ℤ) = 0 := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank :=
    (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  have hmj : m = (j : ℤ) := (Int.toNat_of_nonneg hmNonneg).symm
  have hreduce : buildingCyclicGeneratorPGL P r ^ n =
      buildingCyclicGeneratorPGL P r ^ j := by
    calc
      _ = buildingCyclicGeneratorPGL P r ^ m :=
        zpow_eq_zpow_emod' n (buildingCyclicGeneratorPGL_pow_matrixRank P r)
      _ = buildingCyclicGeneratorPGL P r ^ (j : ℤ) := by rw [hmj]
      _ = _ := zpow_natCast _ j
  have hcanonical :
      buildingConstantPGLHom P r c * buildingCyclicGeneratorPGL P r ^ j =
        buildingConstantPGLHom P r 1 * buildingCyclicGeneratorPGL P r ^ 0 := by
    rw [← hreduce, h]
    simp
  obtain ⟨hc, hj0⟩ := buildingNormalForm_source_eq P r c 1 j 0
    hj (by exact hdNat) hcanonical
  refine ⟨hc, ?_⟩
  change m = 0
  rw [hmj, hj0]
  rfl

theorem global_monomial_eq_one_iff_building_monomial_eq_one
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    globalConstantPGLHom P r c * globalCyclicGeneratorPGL P r ^ n = 1 ↔
      buildingConstantPGLHom P r c * buildingCyclicGeneratorPGL P r ^ n = 1 := by
  constructor
  · intro h
    obtain ⟨hc, hn⟩ := global_normal_data_of_eq_one P r c n h
    have hcyclic : buildingCyclicGeneratorPGL P r ^ n = 1 := by
      calc
        _ = buildingCyclicGeneratorPGL P r ^
            (n % (r.matrixRank : ℤ)) :=
          zpow_eq_zpow_emod' n
            (buildingCyclicGeneratorPGL_pow_matrixRank P r)
        _ = 1 := by rw [hn]; simp
    rw [hcyclic, mul_one]
    rw [buildingConstantPGL_eq_of_quotientMk_eq P r c 1 hc]
    exact map_one (buildingConstantPGLHom P r)
  · intro h
    obtain ⟨hc, hn⟩ := building_normal_data_of_eq_one P r c n h
    have hcyclic : globalCyclicGeneratorPGL P r ^ n = 1 := by
      calc
        _ = globalCyclicGeneratorPGL P r ^
            (n % (r.matrixRank : ℤ)) :=
          zpow_eq_zpow_emod' n
            (globalCyclicGeneratorPGL_pow_matrixRank P r)
        _ = 1 := by rw [hn]; simp
    rw [hcyclic, mul_one]
    rw [globalConstantPGL_eq_of_quotientMk_eq P r c 1 hc]
    exact map_one (globalConstantPGLHom P r)

theorem integralProjectiveRepresentation_ker_eq
    (P : BasePrime) (r : Rank) :
    (globalIntegralUnitPGLHom P r).ker =
      (buildingIntegralUnitPGLHom P r).ker := by
  ext u
  simp only [MonoidHom.mem_ker]
  obtain ⟨c, n, hu⟩ := exists_constant_zpow_of_skewLaurent_unit P r u
  have huUnit : u = skewLaurentMonomialUnit P r c n := by
    apply Units.ext
    exact hu
  rw [huUnit, globalIntegralUnitPGLHom_monomial,
    buildingIntegralUnitPGLHom_monomial]
  exact global_monomial_eq_one_iff_building_monomial_eq_one P r c n

noncomputable def globalIntegralCompactMulEquivBuildingCompact
    (P : BasePrime) (r : Rank) :
    GlobalIntegralCompactCyclicSubgroup P r ≃*
      BuildingCompactCyclicSubgroup P r := by
  rw [← range_globalIntegralUnitPGLHom P r,
    ← range_buildingIntegralUnitPGLHom P r]
  exact (QuotientGroup.quotientKerEquivRange
      (globalIntegralUnitPGLHom P r)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (integralProjectiveRepresentation_ker_eq P r)).trans
        (QuotientGroup.quotientKerEquivRange
          (buildingIntegralUnitPGLHom P r)))

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
