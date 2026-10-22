import QEC.Coding.HighDimensionalExpander.Spectrum.FiniteSpectrum

/-!
# Cartwright--Steger prefix / spherical-Hecke compatibility

This file proves that, in matrix ranks three and four, the length-`k`
prefixes of genuine rank-length Cartwright--Steger relations enumerate every
fundamental Bruhat--Tits color-`k` neighbor exactly once.  The difficult
rank-four middle color is derived from Cartan support bounds and inversion;
it is not inferred from determinant color alone.  Consequently the #768
construction-indexed finite operator equals the actual fundamental-neighbor
Hecke operator, with congruence-collision multiplicity preserved.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups Pointwise
open QEC.Coding.HighDimensionalExpander.SphericalHecke

noncomputable local instance buildingVertexDecidableEq
    (P : BasePrime) (r : Rank) :
    DecidableEq (CartwrightStegerBuildingVertex P r) :=
  Classical.decEq _

private theorem dominant_mem_fundamental_mul_of_common_member
    (P : BasePrime) (w : ProjectiveDominantCoweight 3)
    (x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hxw : x ∈ projectiveDominantDoubleCoset (BaseField P) w)
    (hxprod : x ∈ fundamentalDoubleCoset (BaseField P) 4 1 *
      fundamentalDoubleCoset (BaseField P) 4 1) :
    dominantCoweight (BaseField P) w.toDominant ∈
      projectiveDominantDoubleCoset (BaseField P)
          (fundamentalProjectiveDominantCoweight 3 1 (by omega)) *
        projectiveDominantDoubleCoset (BaseField P)
          (fundamentalProjectiveDominantCoweight 3 1 (by omega)) := by
  rw [projectiveDominantDoubleCoset_fundamental]
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset, Set.mem_mul] at hxw
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hxw
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  rw [Set.mem_mul] at hxprod ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := hxprod
  refine ⟨left⁻¹ * a,
    left_mul_mem_fundamentalDoubleCoset (BaseField P) 4 1
      ((maximalCompact (BaseField P) 4).inv_mem hleft) ha,
    b * right⁻¹,
    right_mul_mem_fundamentalDoubleCoset (BaseField P) 4 1
      ((maximalCompact (BaseField P) 4).inv_mem hright) hb, ?_⟩
  calc
    left⁻¹ * a * (b * right⁻¹) = left⁻¹ * (a * b) * right⁻¹ := by group
    _ = left⁻¹ * x * right⁻¹ := by rw [hab]
    _ = left⁻¹ * (middle * right) * right⁻¹ := by rw [← hfactor]
    _ = left⁻¹ * (left * dominantCoweight (BaseField P) w.toDominant) *
        right * right⁻¹ := by simp only [← hmiddleFactor, mul_assoc]
    _ = dominantCoweight (BaseField P) w.toDominant := by group

private theorem lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
    (P : BasePrime) (r : Rank)
    (x : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hx : x ∈ maximalCompact (BaseField P) r.matrixRank) :
    lsvProjectiveDetOrderColor P r x = 1 := by
  rw [mem_maximalCompact_iff] at hx
  obtain ⟨A, rfl⟩ := hx
  change lsvProjectiveDetOrderColor P r
      (Matrix.ProjGenLinGroup.mk
        (integralGeneralLinearToLocal (BaseField P) r.matrixRank A)) = 1
  rw [lsvProjectiveDetOrderColor_mk]
  change Multiplicative.ofAdd
      (localUnitOrder (Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal (BaseField P) r.matrixRank A)) :
        ZMod r.matrixRank) = 1
  rw [integralGeneralLinear_det_localUnitOrder_eq_zero]
  simp

private theorem lsvProjectiveDetOrderColor_of_mem_rankFour_one
    (P : BasePrime)
    (x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hx : x ∈ fundamentalDoubleCoset (BaseField P) 4 1) :
    lsvProjectiveDetOrderColor P .four x =
      Multiplicative.ofAdd (1 : ZMod 4) := by
  rw [fundamentalDoubleCoset, Set.mem_mul] at hx
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hx
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  rw [← hfactor, ← hmiddleFactor]
  have hmapOuter := (lsvProjectiveDetOrderColor P .four).map_mul
    (left * fundamentalCoweight (BaseField P) 4 1) right
  have hmapInner := (lsvProjectiveDetOrderColor P .four).map_mul
    left (fundamentalCoweight (BaseField P) 4 1)
  calc
    lsvProjectiveDetOrderColor P .four
        (left * fundamentalCoweight (BaseField P) 4 1 * right) =
        lsvProjectiveDetOrderColor P .four
            (left * fundamentalCoweight (BaseField P) 4 1) *
          lsvProjectiveDetOrderColor P .four right := hmapOuter
    _ = (lsvProjectiveDetOrderColor P .four left *
          lsvProjectiveDetOrderColor P .four
            (fundamentalCoweight (BaseField P) 4 1)) *
        lsvProjectiveDetOrderColor P .four right :=
      congrArg (fun z => z * lsvProjectiveDetOrderColor P .four right) hmapInner
    _ = lsvProjectiveDetOrderColor P .four
        (fundamentalCoweight (BaseField P) 4 1) := by
      rw [lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four left hleft,
        lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four right hright, one_mul, mul_one]
    _ = Multiplicative.ofAdd (1 : ZMod Rank.four.matrixRank) := by
      change lsvProjectiveDetOrderColor P .four
          (Matrix.ProjGenLinGroup.mk
            (fundamentalDiagonal (BaseField P) 4 1)) = _
      erw [lsvProjectiveDetOrderColor_mk]
      change Multiplicative.ofAdd
          (localUnitOrder (Matrix.GeneralLinearGroup.det
            (fundamentalDiagonal (BaseField P) 4 1)) : ZMod 4) = _
      rw [show fundamentalDiagonal (BaseField P) 4 1 =
          dominantGeneralLinear (BaseField P)
            (fundamentalDominantCoweight 4 1) by
        symm
        exact dominantGeneralLinear_fundamental (BaseField P) 4 1]
      rw [dominantGeneralLinear_det_localUnitOrder]
      norm_num [fundamentalDominantCoweight, Fin.sum_univ_succ]
      rfl

private theorem lsvProjectiveDetOrderColor_of_mem_projectiveDominantDoubleCoset
    (P : BasePrime) (w : ProjectiveDominantCoweight 3)
    (x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hx : x ∈ projectiveDominantDoubleCoset (BaseField P) w) :
    lsvProjectiveDetOrderColor P .four x =
      Multiplicative.ofAdd
        ((∑ i, w.toDominant.exponent i : Nat) : ZMod 4) := by
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset, Set.mem_mul] at hx
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hx
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  rw [← hfactor, ← hmiddleFactor]
  have hmapOuter := (lsvProjectiveDetOrderColor P .four).map_mul
    (left * dominantCoweight (BaseField P) w.toDominant) right
  have hmapInner := (lsvProjectiveDetOrderColor P .four).map_mul
    left (dominantCoweight (BaseField P) w.toDominant)
  calc
    lsvProjectiveDetOrderColor P .four
        (left * dominantCoweight (BaseField P) w.toDominant * right) =
        lsvProjectiveDetOrderColor P .four
            (left * dominantCoweight (BaseField P) w.toDominant) *
          lsvProjectiveDetOrderColor P .four right := hmapOuter
    _ = (lsvProjectiveDetOrderColor P .four left *
          lsvProjectiveDetOrderColor P .four
            (dominantCoweight (BaseField P) w.toDominant)) *
        lsvProjectiveDetOrderColor P .four right :=
      congrArg (fun z => z * lsvProjectiveDetOrderColor P .four right) hmapInner
    _ = lsvProjectiveDetOrderColor P .four
        (dominantCoweight (BaseField P) w.toDominant) := by
      rw [lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four left hleft,
        lsvProjectiveDetOrderColor_eq_one_of_mem_maximalCompact
          P .four right hright, one_mul, mul_one]
    _ = Multiplicative.ofAdd
        ((∑ i, w.toDominant.exponent i : Nat) : ZMod Rank.four.matrixRank) := by
      change lsvProjectiveDetOrderColor P .four
          (Matrix.ProjGenLinGroup.mk
            (dominantGeneralLinear (BaseField P) w.toDominant)) = _
      rw [lsvProjectiveDetOrderColor_mk]
      change Multiplicative.ofAdd
          (localUnitOrder (Matrix.GeneralLinearGroup.det
            (dominantGeneralLinear (BaseField P) w.toDominant)) :
            ZMod 4) = _
      rw [dominantGeneralLinear_det_localUnitOrder]
      rfl

private def rankFourDoubleFirstWeight : ProjectiveDominantCoweight 3 where
  toDominant :=
    { exponent := ![2, 0, 0, 0]
      antitone_exponent := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all }
  last_exponent_eq_zero := rfl

private def rankFourDoubleFirstInverseWeight : ProjectiveDominantCoweight 3 where
  toDominant :=
    { exponent := ![2, 2, 2, 0]
      antitone_exponent := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all }
  last_exponent_eq_zero := rfl

private theorem rankFour_weight_sum_two_cases
    (w : ProjectiveDominantCoweight 3)
    (hsum : ∑ i, w.toDominant.exponent i = 2) :
    w = fundamentalProjectiveDominantCoweight 3 2 (by omega) ∨
      w = rankFourDoubleFirstWeight := by
  have hlast : w.toDominant.exponent (3 : Fin 4) = 0 := by
    simpa using w.last_exponent_eq_zero
  have h01 := w.toDominant.antitone_exponent
    (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := w.toDominant.antitone_exponent
    (show (1 : Fin 4) ≤ 2 by decide)
  simp [Fin.sum_univ_succ, hlast] at hsum
  by_cases hfirst : w.toDominant.exponent (0 : Fin 4) = 1
  · left
    apply ProjectiveDominantCoweight.ext
    funext i
    fin_cases i <;>
      simp [fundamentalProjectiveDominantCoweight,
        fundamentalDominantCoweight, hfirst, hlast] <;> omega
  · right
    apply ProjectiveDominantCoweight.ext
    funext i
    fin_cases i <;>
      simp [rankFourDoubleFirstWeight, hlast] <;> omega

private theorem rankFourDoubleFirstWeight_inv
    (P : BasePrime) :
    (projectiveDominantDoubleCoset (BaseField P)
      rankFourDoubleFirstWeight)⁻¹ =
      projectiveDominantDoubleCoset (BaseField P)
        rankFourDoubleFirstInverseWeight := by
  rw [projectiveDominantDoubleCoset, projectiveDominantDoubleCoset]
  apply subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact (BaseField P) 4)
    (permutationCoweight_mem_maximalCompact (BaseField P) Fin.revPerm)
  have hscalar :
      Matrix.GeneralLinearGroup.scalar (Fin 4)
          (uniformizerUnit (BaseField P) ^ 2) *
        (dominantGeneralLinear (BaseField P)
          rankFourDoubleFirstWeight.toDominant)⁻¹ =
      permutationGeneralLinear (BuildingLocalField P) Fin.revPerm *
        dominantGeneralLinear (BaseField P)
          rankFourDoubleFirstInverseWeight.toDominant *
        (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm)⁻¹ := by
    change _ = permutationGeneralLinear (BuildingLocalField P) Fin.revPerm *
      diagonalGeneralLinear (BuildingLocalField P) 4
        (fun i => uniformizerUnit (BaseField P) ^
          rankFourDoubleFirstInverseWeight.toDominant.exponent i) *
      (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm)⁻¹
    rw [permutationGeneralLinear_conj_diagonal]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rankFourDoubleFirstWeight, rankFourDoubleFirstInverseWeight,
        dominantGeneralLinear, diagonalGeneralLinear_inv,
        diagonalGeneralLinear_apply, Matrix.mul_apply, pow_two]
  have hmk := congrArg Matrix.ProjGenLinGroup.mk hscalar
  change
    Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.scalar (Fin 4)
          (uniformizerUnit (BaseField P) ^ 2)) *
          (dominantCoweight (BaseField P)
            rankFourDoubleFirstWeight.toDominant)⁻¹ =
      Matrix.ProjGenLinGroup.mk
          (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm) *
        dominantCoweight (BaseField P)
          rankFourDoubleFirstInverseWeight.toDominant *
        (Matrix.ProjGenLinGroup.mk
          (permutationGeneralLinear (BuildingLocalField P) Fin.revPerm))⁻¹ at hmk
  simp [Matrix.ProjGenLinGroup.mk_scalar] at hmk ⊢
  exact hmk

theorem rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation
    (P : BasePrime)
    (a b c d : BuildingCartwrightStegerLattice P .four)
    (ha : a.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hb : b.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hc : c.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hd : d.1 ∈ fundamentalDoubleCoset (BaseField P) 4 1)
    (hprod : ((a * b) * c) * d = 1) :
    (a * b).1 ∈ fundamentalDoubleCoset (BaseField P) 4 2 := by
  let x : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P) := (a * b).1
  have hxprod : x ∈ fundamentalDoubleCoset (BaseField P) 4 1 *
      fundamentalDoubleCoset (BaseField P) 4 1 := by
    rw [Set.mem_mul]
    exact ⟨a.1, ha, b.1, hb, rfl⟩
  obtain ⟨w, hxw⟩ := exists_mem_projectiveDominantDoubleCoset
    (BaseField P) x
  have hdiagprod := dominant_mem_fundamental_mul_of_common_member P w x hxw hxprod
  let f1 := fundamentalProjectiveDominantCoweight 3 1 (by omega)
  have hsumInt := projectiveDominant_exponent_sum_le_of_mem_cartanDoubleCoset_mul
    (BaseField P) w f1 f1 hdiagprod
  have hsumLe : (∑ i, w.toDominant.exponent i) ≤ 2 := by
    exact_mod_cast hsumInt
  have hxcolor : lsvProjectiveDetOrderColor P .four x =
      Multiplicative.ofAdd (2 : ZMod 4) := by
    change lsvBuildingLatticeColor P .four (a * b) = _
    rw [map_mul]
    change lsvBuildingLatticeColor P .four a *
      lsvBuildingLatticeColor P .four b = _
    have haColor := lsvProjectiveDetOrderColor_of_mem_rankFour_one P a.1 ha
    have hbColor := lsvProjectiveDetOrderColor_of_mem_rankFour_one P b.1 hb
    change lsvProjectiveDetOrderColor P .four a.1 *
      lsvProjectiveDetOrderColor P .four b.1 = _
    rw [haColor, hbColor]
    apply Multiplicative.toAdd.injective
    change (1 : ZMod 4) + 1 = 2
    norm_num
  have hwcolor :=
    lsvProjectiveDetOrderColor_of_mem_projectiveDominantDoubleCoset
      P w x hxw
  have hsumZMod :
      (((∑ i, w.toDominant.exponent i : Nat) : ZMod 4)) = 2 := by
    apply Multiplicative.ofAdd.injective
    exact hwcolor.symm.trans hxcolor
  have hsum : ∑ i, w.toDominant.exponent i = 2 := by
    let s := ∑ i, w.toDominant.exponent i
    have hs : s ≤ 2 := by simpa [s] using hsumLe
    change (s : ZMod 4) = 2 at hsumZMod
    change s = 2
    interval_cases hsval : s
    · exfalso
      exact (by decide : (0 : ZMod 4) ≠ 2) hsumZMod
    · exfalso
      exact (by decide : (1 : ZMod 4) ≠ 2) hsumZMod
    · rfl
  rcases rankFour_weight_sum_two_cases w hsum with hw | hw
  · rw [hw, projectiveDominantDoubleCoset_fundamental] at hxw
    exact hxw
  · subst w
    exfalso
    have hxinvBad : x⁻¹ ∈ projectiveDominantDoubleCoset (BaseField P)
        rankFourDoubleFirstInverseWeight := by
      have hinvset : x⁻¹ ∈
          (projectiveDominantDoubleCoset (BaseField P)
            rankFourDoubleFirstWeight)⁻¹ := by
        exact Set.inv_mem_inv.mpr hxw
      rw [rankFourDoubleFirstWeight_inv P] at hinvset
      exact hinvset
    have hxinvProd : x⁻¹ ∈ fundamentalDoubleCoset (BaseField P) 4 1 *
        fundamentalDoubleCoset (BaseField P) 4 1 := by
      have hxcd : x⁻¹ = c.1 * d.1 := by
        change ((a * b).1)⁻¹ = (c * d).1
        have hprodGrouped : (a * b) * (c * d) = 1 := by
          simpa only [mul_assoc] using hprod
        have hprod'' := congrArg Subtype.val hprodGrouped
        exact inv_eq_of_mul_eq_one_right hprod''
      rw [hxcd]
      erw [Set.mem_mul]
      exact ⟨c.1, hc, d.1, hd, rfl⟩
    have hdiagInvProd := dominant_mem_fundamental_mul_of_common_member
      P rankFourDoubleFirstInverseWeight x⁻¹ hxinvBad hxinvProd
    have hbadBound := projectiveDominant_exponent_sum_le_of_mem_cartanDoubleCoset_mul
      (BaseField P) rankFourDoubleFirstInverseWeight f1 f1 hdiagInvProd
    norm_num [rankFourDoubleFirstInverseWeight, f1,
      fundamentalProjectiveDominantCoweight, fundamentalDominantCoweight,
      Fin.sum_univ_succ] at hbadBound

private theorem list_ofFn_rankThree_local
    {A : Type*} (u : Fin 3 → A) :
    List.ofFn u = [u 0, u 1, u 2] := by
  apply List.ext_get
  · simp
  · intro n hna hnb
    change n < 3 at hna
    interval_cases n <;> simp

private theorem list_ofFn_rankFour_local
    {A : Type*} (u : Fin 4 → A) :
    List.ofFn u = [u 0, u 1, u 2, u 3] := by
  apply List.ext_get
  · simp
  · intro n hna hnb
    change n < 4 at hna
    interval_cases n <;> simp

private theorem buildingGeneratorWordProduct_rankThree_local
    (P : BasePrime) (u : Fin 3 → ConstantProjectiveClass P .three) :
    buildingGeneratorWordProduct P .three (List.ofFn u) =
      (buildingLatticeGenerator P .three (u 0) *
        buildingLatticeGenerator P .three (u 1)) *
          buildingLatticeGenerator P .three (u 2) := by
  rw [list_ofFn_rankThree_local u]
  simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

private theorem buildingGeneratorWordProduct_rankFour_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorWordProduct P .four (List.ofFn u) =
      ((buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1)) *
          buildingLatticeGenerator P .four (u 2)) *
            buildingLatticeGenerator P .four (u 3) := by
  rw [list_ofFn_rankFour_local u]
  simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]

private theorem buildingGeneratorPrefixProduct_rankThree_one_local
    (P : BasePrime) (u : Fin 3 → ConstantProjectiveClass P .three) :
    buildingGeneratorPrefixProduct P .three 1 u =
      buildingLatticeGenerator P .three (u 0) := by
  have htake : (List.ofFn u).take 1 = [u 0] := by
    rw [list_ofFn_rankThree_local u]
    rfl
  change buildingGeneratorWordProduct P .three ((List.ofFn u).take 1) = _
  calc
    buildingGeneratorWordProduct P .three ((List.ofFn u).take 1) =
        buildingGeneratorWordProduct P .three [u 0] :=
      congrArg (buildingGeneratorWordProduct P .three) htake
    _ = buildingLatticeGenerator P .three (u 0) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]

private theorem buildingGeneratorPrefixProduct_rankThree_two_local
    (P : BasePrime) (u : Fin 3 → ConstantProjectiveClass P .three) :
    buildingGeneratorPrefixProduct P .three 2 u =
      buildingLatticeGenerator P .three (u 0) *
        buildingLatticeGenerator P .three (u 1) := by
  have htake : (List.ofFn u).take 2 = [u 0, u 1] := by
    rw [list_ofFn_rankThree_local u]
    rfl
  change buildingGeneratorWordProduct P .three ((List.ofFn u).take 2) = _
  calc
    buildingGeneratorWordProduct P .three ((List.ofFn u).take 2) =
        buildingGeneratorWordProduct P .three [u 0, u 1] :=
      congrArg (buildingGeneratorWordProduct P .three) htake
    _ = buildingLatticeGenerator P .three (u 0) *
        buildingLatticeGenerator P .three (u 1) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]

private theorem buildingGeneratorPrefixProduct_rankFour_one_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorPrefixProduct P .four 1 u =
      buildingLatticeGenerator P .four (u 0) := by
  have htake : (List.ofFn u).take 1 = [u 0] := by
    rw [list_ofFn_rankFour_local u]
    rfl
  change buildingGeneratorWordProduct P .four ((List.ofFn u).take 1) = _
  calc
    buildingGeneratorWordProduct P .four ((List.ofFn u).take 1) =
        buildingGeneratorWordProduct P .four [u 0] :=
      congrArg (buildingGeneratorWordProduct P .four) htake
    _ = buildingLatticeGenerator P .four (u 0) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]

private theorem buildingGeneratorPrefixProduct_rankFour_two_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorPrefixProduct P .four 2 u =
      buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1) := by
  have htake : (List.ofFn u).take 2 = [u 0, u 1] := by
    rw [list_ofFn_rankFour_local u]
    rfl
  change buildingGeneratorWordProduct P .four ((List.ofFn u).take 2) = _
  calc
    buildingGeneratorWordProduct P .four ((List.ofFn u).take 2) =
        buildingGeneratorWordProduct P .four [u 0, u 1] :=
      congrArg (buildingGeneratorWordProduct P .four) htake
    _ = buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]

private theorem buildingGeneratorPrefixProduct_rankFour_three_local
    (P : BasePrime) (u : Fin 4 → ConstantProjectiveClass P .four) :
    buildingGeneratorPrefixProduct P .four 3 u =
      (buildingLatticeGenerator P .four (u 0) *
        buildingLatticeGenerator P .four (u 1)) *
          buildingLatticeGenerator P .four (u 2) := by
  have htake : (List.ofFn u).take 3 = [u 0, u 1, u 2] := by
    rw [list_ofFn_rankFour_local u]
    rfl
  change buildingGeneratorWordProduct P .four ((List.ofFn u).take 3) = _
  calc
    buildingGeneratorWordProduct P .four ((List.ofFn u).take 3) =
        buildingGeneratorWordProduct P .four [u 0, u 1, u 2] :=
      congrArg (buildingGeneratorWordProduct P .four) htake
    _ = (buildingLatticeGenerator P .four (u 0) *
          buildingLatticeGenerator P .four (u 1)) *
        buildingLatticeGenerator P .four (u 2) := by
      simp only [buildingGeneratorWordProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, mul_assoc]

private theorem mem_buildingRelationTupleFinset_iff
    (P : BasePrime) (r : Rank)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    u ∈ buildingRelationTupleFinset P r ↔
      buildingGeneratorWordProduct P r (List.ofFn u) = 1 := by
  classical
  constructor
  · intro hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu
    exact hu.2
  · intro hrel
    rw [buildingRelationTupleFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hrel⟩

theorem buildingGeneratorPrefixProduct_mem_fundamentalDoubleCoset
    (P : BasePrime) (r : Rank)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r)
    {color : Nat} (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    (buildingGeneratorPrefixProduct P r color u).1 ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by
  classical
  have hrel : buildingGeneratorWordProduct P r (List.ofFn u) = 1 := by
    have hu' := hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu'
    exact hu'.2
  cases r with
  | three =>
      change Fin 3 → ConstantProjectiveClass P .three at u
      simp only [Rank.matrixRank] at hcolor ⊢
      simp only [Finset.mem_Icc] at hcolor
      have hcases : color = 1 ∨ color = 2 := by omega
      rcases hcases with rfl | rfl
      · rw [buildingGeneratorPrefixProduct_rankThree_one_local P u]
        exact buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
          P .three (u 0)
      · have hrel' :
            (buildingLatticeGenerator P .three (u 0) *
              buildingLatticeGenerator P .three (u 1)) *
                buildingLatticeGenerator P .three (u 2) = 1 := by
            exact (buildingGeneratorWordProduct_rankThree_local P u).symm.trans hrel
        have hprefix :
            buildingLatticeGenerator P .three (u 0) *
                buildingLatticeGenerator P .three (u 1) =
              (buildingLatticeGenerator P .three (u 2))⁻¹ := by
          calc
            buildingLatticeGenerator P .three (u 0) *
                buildingLatticeGenerator P .three (u 1) =
              ((buildingLatticeGenerator P .three (u 0) *
                buildingLatticeGenerator P .three (u 1)) *
                  buildingLatticeGenerator P .three (u 2)) *
                (buildingLatticeGenerator P .three (u 2))⁻¹ := by group
            _ = (buildingLatticeGenerator P .three (u 2))⁻¹ := by
              rw [hrel', one_mul]
        rw [buildingGeneratorPrefixProduct_rankThree_two_local P u]
        rw [hprefix]
        have hinv :
            (buildingLatticeGenerator P .three (u 2)).1⁻¹ ∈
              (fundamentalDoubleCoset (BaseField P) 3 1)⁻¹ :=
          Set.inv_mem_inv.mpr
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .three (u 2))
        rw [fundamentalDoubleCoset_rankThree_one_inv] at hinv
        exact hinv
  | four =>
      change Fin 4 → ConstantProjectiveClass P .four at u
      simp only [Rank.matrixRank] at hcolor ⊢
      simp only [Finset.mem_Icc] at hcolor
      have hcases : color = 1 ∨ color = 2 ∨ color = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · rw [buildingGeneratorPrefixProduct_rankFour_one_local P u]
        exact buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
          P .four (u 0)
      · have hrel' :
            ((buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2)) *
                  buildingLatticeGenerator P .four (u 3) = 1 := by
            exact (buildingGeneratorWordProduct_rankFour_local P u).symm.trans hrel
        rw [buildingGeneratorPrefixProduct_rankFour_two_local P u]
        exact rankFour_twoStep_mem_fundamentalDoubleCoset_two_of_relation P
            (buildingLatticeGenerator P .four (u 0))
            (buildingLatticeGenerator P .four (u 1))
            (buildingLatticeGenerator P .four (u 2))
            (buildingLatticeGenerator P .four (u 3))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 0))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 1))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 2))
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 3)) hrel'
      · have hrel' :
            ((buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2)) *
                  buildingLatticeGenerator P .four (u 3) = 1 := by
            exact (buildingGeneratorWordProduct_rankFour_local P u).symm.trans hrel
        have hprefix :
            (buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2) =
              (buildingLatticeGenerator P .four (u 3))⁻¹ := by
          calc
            (buildingLatticeGenerator P .four (u 0) *
              buildingLatticeGenerator P .four (u 1)) *
                buildingLatticeGenerator P .four (u 2) =
              (((buildingLatticeGenerator P .four (u 0) *
                buildingLatticeGenerator P .four (u 1)) *
                  buildingLatticeGenerator P .four (u 2)) *
                    buildingLatticeGenerator P .four (u 3)) *
                (buildingLatticeGenerator P .four (u 3))⁻¹ := by group
            _ = (buildingLatticeGenerator P .four (u 3))⁻¹ := by
              rw [hrel', one_mul]
        rw [buildingGeneratorPrefixProduct_rankFour_three_local P u]
        rw [hprefix]
        have hinv :
            (buildingLatticeGenerator P .four (u 3)).1⁻¹ ∈
              (fundamentalDoubleCoset (BaseField P) 4 1)⁻¹ :=
          Set.inv_mem_inv.mpr
            (buildingCartwrightStegerGenerator_mem_fundamentalDoubleCoset
              P .four (u 3))
        rw [fundamentalDoubleCoset_rankFour_one_inv] at hinv
        exact hinv

theorem exists_buildingRelation_prefix_maps_fundamentalNeighbor
    (P : BasePrime) (r : Rank) (color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1))
    (q : CartwrightStegerBuildingVertex P r)
    (hq : q ∈ fundamentalNeighborCosets
      (BaseField P) r.matrixRank color) :
    ∃ u ∈ buildingRelationTupleFinset P r,
      buildingLatticeVertexMap P r
        (buildingGeneratorPrefixProduct P r color u) = q := by
  classical
  cases r with
  | three =>
      simp only [Rank.matrixRank] at hcolor hq ⊢
      simp only [Finset.mem_Icc] at hcolor
      have hcases : color = 1 ∨ color = 2 := by omega
      rcases hcases with rfl | rfl
      · obtain ⟨u0, u1, u2, hrel, hmem1, hmem2, htarget⟩ :=
          exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
            P (0 : Fin 2) q hq
        let u : Fin Rank.three.matrixRank →
            ConstantProjectiveClass P .three := ![u0, u1, u2]
        refine ⟨u, ?_, ?_⟩
        · apply (mem_buildingRelationTupleFinset_iff P .three u).mpr
          exact (buildingGeneratorWordProduct_rankThree_local P u).trans (by
            simpa [u] using hrel)
        · rw [buildingGeneratorPrefixProduct_rankThree_one_local P u]
          simpa [u] using htarget
      · obtain ⟨u0, u1, u2, hrel, hmem1, hmem2, htarget⟩ :=
          exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
            P (1 : Fin 2) q hq
        let u : Fin Rank.three.matrixRank →
            ConstantProjectiveClass P .three := ![u0, u1, u2]
        refine ⟨u, ?_, ?_⟩
        · apply (mem_buildingRelationTupleFinset_iff P .three u).mpr
          exact (buildingGeneratorWordProduct_rankThree_local P u).trans (by
            simpa [u] using hrel)
        · rw [buildingGeneratorPrefixProduct_rankThree_two_local P u]
          simpa [u] using htarget
  | four =>
      simp only [Rank.matrixRank] at hcolor hq ⊢
      simp only [Finset.mem_Icc] at hcolor
      have hcases : color = 1 ∨ color = 2 ∨ color = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · obtain ⟨u0, u1, u2, u3, hrel, hmem1, hmem2, hmem3, htarget⟩ :=
          exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
            P (0 : Fin 3) q hq
        let u : Fin Rank.four.matrixRank →
            ConstantProjectiveClass P .four := ![u0, u1, u2, u3]
        refine ⟨u, ?_, ?_⟩
        · apply (mem_buildingRelationTupleFinset_iff P .four u).mpr
          exact (buildingGeneratorWordProduct_rankFour_local P u).trans (by
            simpa [u] using hrel)
        · rw [buildingGeneratorPrefixProduct_rankFour_one_local P u]
          simpa [u] using htarget
      · obtain ⟨u0, u1, u2, u3, hrel, hmem1, hmem2, hmem3, htarget⟩ :=
          exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
            P (1 : Fin 3) q hq
        let u : Fin Rank.four.matrixRank →
            ConstantProjectiveClass P .four := ![u0, u1, u2, u3]
        refine ⟨u, ?_, ?_⟩
        · apply (mem_buildingRelationTupleFinset_iff P .four u).mpr
          exact (buildingGeneratorWordProduct_rankFour_local P u).trans (by
            simpa [u] using hrel)
        · rw [buildingGeneratorPrefixProduct_rankFour_two_local P u]
          simpa [u] using htarget
      · obtain ⟨u0, u1, u2, u3, hrel, hmem1, hmem2, hmem3, htarget⟩ :=
          exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
            P (2 : Fin 3) q hq
        let u : Fin Rank.four.matrixRank →
            ConstantProjectiveClass P .four := ![u0, u1, u2, u3]
        refine ⟨u, ?_, ?_⟩
        · apply (mem_buildingRelationTupleFinset_iff P .four u).mpr
          exact (buildingGeneratorWordProduct_rankFour_local P u).trans (by
            simpa [u] using hrel)
        · rw [buildingGeneratorPrefixProduct_rankFour_three_local P u]
          simpa [u] using htarget

theorem image_buildingColorGeneratorFinset_vertexMap
    (P : BasePrime) (r : Rank) (color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    (buildingColorGeneratorFinset P r color).image
        (buildingLatticeVertexMap P r) =
      fundamentalNeighborCosets (BaseField P) r.matrixRank color := by
  classical
  ext q
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [buildingColorGeneratorFinset, Finset.mem_image] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [mem_fundamentalNeighborCosets]
    exact ⟨(buildingGeneratorPrefixProduct P r color u).1,
      buildingGeneratorPrefixProduct_mem_fundamentalDoubleCoset
        P r hu hcolor, rfl⟩
  · intro hq
    obtain ⟨u, hu, hprefix⟩ :=
      exists_buildingRelation_prefix_maps_fundamentalNeighbor
        P r color hcolor q hq
    exact ⟨buildingGeneratorPrefixProduct P r color u,
      Finset.mem_image.mpr ⟨u, hu, rfl⟩, hprefix⟩

/-- The source-prefix presentation and the actual fundamental-neighbor
presentation are equal without collapsing multiplicity: the building lattice
orbit map is injective by simple transitivity. -/
theorem lsvConstructionColorOperator_eq_lsvColorHeckeOperator
    (P : BasePrime) (r : Rank) (level color : Nat)
    (hcolor : color ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    lsvConstructionColorOperator P r level color =
      lsvColorHeckeOperator P r level color := by
  classical
  apply LinearMap.ext
  intro f
  funext x
  rw [lsvColorHeckeOperator_apply]
  change (∑ s ∈ buildingColorGeneratorFinset P r color,
      f (x * buildingLatticeFiniteReduction P r level s)) =
    ∑ q ∈ fundamentalNeighborCosets (BaseField P) r.matrixRank color,
      f (x * buildingLatticeFiniteReduction P r level
        ((lsvBuildingLatticeVertexEquiv P r).symm q))
  rw [← image_buildingColorGeneratorFinset_vertexMap P r color hcolor]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [show (lsvBuildingLatticeVertexEquiv P r).symm
        (buildingLatticeVertexMap P r s) = s by
      exact (lsvBuildingLatticeVertexEquiv P r).symm_apply_apply s]
  · intro a ha b hb hab
    exact buildingLatticeVertexMap_injective P r hab

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
