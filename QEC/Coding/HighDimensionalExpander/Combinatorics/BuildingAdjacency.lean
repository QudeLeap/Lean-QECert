import QEC.Coding.HighDimensionalExpander.Hecke.SphericalHeckeGenerators
import QEC.Coding.HighDimensionalExpander.Combinatorics.FiniteGrassmannian
import QEC.Coding.HighDimensionalExpander.Combinatorics.LocalLinkReduction

/-!
# Colored adjacency on the affine-building vertex set

Vertices are the actual right-coset space `PGL_d(F) / PGL_d(O)`.  The
colored relation is defined by the fundamental Cartan double cosets and is
proved independent of representatives.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.SphericalHecke

open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction

universe u

/-- Vertices of the affine building in the homogeneous-space model. -/
abbrev BuildingVertex (k : Type u) [Field k] [Finite k] (d : ℕ) :=
  HeckeGroup k d ⧸ maximalCompact k d

noncomputable instance buildingVertexDiscreteTopology
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    DiscreteTopology (BuildingVertex k d) :=
  QuotientGroup.discreteTopology_iff.mpr (maximalCompact_isOpen k d)

/-- The color-`r` adjacency relation, stated using representatives but on the
actual quotient vertex type. -/
def ColoredBuildingAdjacent
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x y : BuildingVertex k d) : Prop :=
  ∃ gx gy : HeckeGroup k d,
    QuotientGroup.mk gx = x ∧ QuotientGroup.mk gy = y ∧
      gx⁻¹ * gy ∈ fundamentalDoubleCoset k d r

theorem coloredBuildingAdjacent_mk_iff
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (gx gy : HeckeGroup k d) :
    ColoredBuildingAdjacent k d r (QuotientGroup.mk gx) (QuotientGroup.mk gy) ↔
      gx⁻¹ * gy ∈ fundamentalDoubleCoset k d r := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have hka : a⁻¹ * gx ∈ maximalCompact k d := QuotientGroup.eq.mp ha
    have hkb : b⁻¹ * gy ∈ maximalCompact k d := QuotientGroup.eq.mp hb
    have hleft := left_mul_mem_fundamentalDoubleCoset k d r
      ((maximalCompact k d).inv_mem hka) hab
    have hboth := right_mul_mem_fundamentalDoubleCoset k d r hkb hleft
    simpa [mul_assoc] using hboth
  · intro h
    exact ⟨gx, gy, rfl, rfl, h⟩

/-- Colored building adjacency is invariant under the natural left action
of the local projective linear group. -/
theorem coloredBuildingAdjacent_smul_iff
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (g : HeckeGroup k d) (x y : BuildingVertex k d) :
    ColoredBuildingAdjacent k d r (g • x) (g • y) ↔
      ColoredBuildingAdjacent k d r x y := by
  induction x using QuotientGroup.induction_on with
  | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b =>
          rw [MulAction.Quotient.smul_mk,
            MulAction.Quotient.smul_mk,
            coloredBuildingAdjacent_mk_iff,
            coloredBuildingAdjacent_mk_iff]
          simp [smul_eq_mul, mul_assoc]

/-- The zeroth coordinate uniformizer is the distinguished color-one Cartan
representative. -/
theorem coordinateUniformizerCoweight_zero_eq_fundamental
    (k : Type u) [Field k] {d : ℕ} (hd : 0 < d) :
    coordinateUniformizerCoweight k d ⟨0, hd⟩ =
      fundamentalCoweight k d 1 := by
  apply congrArg Matrix.ProjGenLinGroup.mk
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [coordinateUniformizerGeneralLinear, fundamentalDiagonal,
    diagonalGeneralLinear_apply, diagonalGeneralLinear_apply]
  by_cases hab : a = b
  · subst b
    simp [coordinateUniformizerUnits, fundamentalDiagonalUnits,
      Fin.ext_iff]
  · simp [hab]

/-- Every one-coordinate uniformizer represents a color-one Cartan step. -/
theorem coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) (i : Fin d) :
    coordinateUniformizerCoweight k d i ∈
      fundamentalDoubleCoset k d 1 := by
  let i0 : Fin d := ⟨0, hd⟩
  have hbase : coordinateUniformizerCoweight k d i0 =
      fundamentalCoweight k d 1 := by
    exact coordinateUniformizerCoweight_zero_eq_fundamental k hd
  let p := permutationCoweight k (Equiv.swap i0 i)
  have hp : p ∈ maximalCompact k d :=
    permutationCoweight_mem_maximalCompact k _
  have hfund : coordinateUniformizerCoweight k d i0 ∈
      fundamentalDoubleCoset k d 1 := by
    rw [hbase]
    exact fundamentalCoweight_mem_doubleCoset k d 1
  have hleft := left_mul_mem_fundamentalDoubleCoset k d 1 hp hfund
  have hright := right_mul_mem_fundamentalDoubleCoset k d 1
    ((maximalCompact k d).inv_mem hp) hleft
  simpa [p, coordinateUniformizerCoweight_conj] using hright

/-- Reachability by directed color-one building steps. -/
abbrev ColorOneReachable
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (x y : BuildingVertex k d) : Prop :=
  Relation.ReflTransGen (ColoredBuildingAdjacent k d 1) x y

/-- Left translation preserves color-one reachability. -/
theorem colorOneReachable_smul
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) {x y : BuildingVertex k d}
    (hxy : ColorOneReachable k d x y) :
    ColorOneReachable k d (g • x) (g • y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact ih.tail
        ((coloredBuildingAdjacent_smul_iff k d 1 g _ _).2 hbc)

/-- A finite product of one-coordinate uniformizers is reachable from the
base vertex using color-one steps only. -/
theorem coordinateUniformizerProduct_colorOneReachable
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d)
    (coordinates : List (Fin d)) :
    ColorOneReachable k d (QuotientGroup.mk 1)
      (QuotientGroup.mk
        ((coordinates.map (coordinateUniformizerCoweight k d)).prod)) := by
  induction coordinates with
  | nil =>
      simpa using (Relation.ReflTransGen.refl :
        ColorOneReachable k d (QuotientGroup.mk 1) (QuotientGroup.mk 1))
  | cons i coordinates ih =>
      have hstep : ColoredBuildingAdjacent k d 1
          (QuotientGroup.mk 1)
          (QuotientGroup.mk (coordinateUniformizerCoweight k d i)) := by
        rw [coloredBuildingAdjacent_mk_iff]
        simpa using
          coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
            k hd i
      have htail := colorOneReachable_smul k d
        (coordinateUniformizerCoweight k d i) ih
      have htail' : ColorOneReachable k d
          (QuotientGroup.mk (coordinateUniformizerCoweight k d i))
          (QuotientGroup.mk
            (coordinateUniformizerCoweight k d i *
              (coordinates.map
                (coordinateUniformizerCoweight k d)).prod)) := by
        simpa [MulAction.Quotient.smul_mk, smul_eq_mul] using htail
      exact (Relation.ReflTransGen.single hstep).trans (by
        simpa using htail')

theorem coordinateUniformizerCoweight_rankThree_zero_one
    (k : Type u) [Field k] :
    coordinateUniformizerCoweight k 3 0 *
        coordinateUniformizerCoweight k 3 1 =
      fundamentalCoweight k 3 2 := by
  apply congrArg Matrix.ProjGenLinGroup.mk
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateUniformizerGeneralLinear, coordinateUniformizerUnits,
      fundamentalDiagonal,
      fundamentalDiagonalUnits, diagonalGeneralLinear_apply,
      Matrix.mul_apply]

theorem coordinateUniformizerCoweight_rankFour_zero_one
    (k : Type u) [Field k] :
    coordinateUniformizerCoweight k 4 0 *
        coordinateUniformizerCoweight k 4 1 =
      fundamentalCoweight k 4 2 := by
  apply congrArg Matrix.ProjGenLinGroup.mk
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateUniformizerGeneralLinear, coordinateUniformizerUnits,
      fundamentalDiagonal,
      fundamentalDiagonalUnits, diagonalGeneralLinear_apply,
      Matrix.mul_apply]

theorem coordinateUniformizerCoweight_rankFour_zero_one_two
    (k : Type u) [Field k] :
    coordinateUniformizerCoweight k 4 0 *
          coordinateUniformizerCoweight k 4 1 *
        coordinateUniformizerCoweight k 4 2 =
      fundamentalCoweight k 4 3 := by
  apply congrArg Matrix.ProjGenLinGroup.mk
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateUniformizerGeneralLinear, coordinateUniformizerUnits,
      fundamentalDiagonal,
      fundamentalDiagonalUnits, diagonalGeneralLinear_apply,
      Matrix.mul_apply]

/-- Every fundamental rank-three Cartan vertex is reachable using only
color-one steps. -/
theorem fundamentalCoweight_rankThree_colorOneReachable
    (k : Type u) [Field k] [Finite k] (color : Fin 2) :
    ColorOneReachable k 3 (QuotientGroup.mk 1)
      (QuotientGroup.mk
        (fundamentalCoweight k 3 (color.val + 1))) := by
  fin_cases color
  · change ColorOneReachable k 3 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 3 1))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 3) (by omega) ([0] : List (Fin 3))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    have hzero : coordinateUniformizerCoweight k 3 (0 : Fin 3) =
        fundamentalCoweight k 3 1 :=
      coordinateUniformizerCoweight_zero_eq_fundamental k (by decide)
    rw [hzero] at h
    exact h
  · change ColorOneReachable k 3 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 3 2))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 3) (by omega) ([0, 1] : List (Fin 3))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    simpa [coordinateUniformizerCoweight_rankThree_zero_one] using h

/-- Every fundamental rank-four Cartan vertex is reachable using only
color-one steps. -/
theorem fundamentalCoweight_rankFour_colorOneReachable
    (k : Type u) [Field k] [Finite k] (color : Fin 3) :
    ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk
        (fundamentalCoweight k 4 (color.val + 1))) := by
  fin_cases color
  · change ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 4 1))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 4) (by omega) ([0] : List (Fin 4))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    have hzero : coordinateUniformizerCoweight k 4 (0 : Fin 4) =
        fundamentalCoweight k 4 1 :=
      coordinateUniformizerCoweight_zero_eq_fundamental k (by decide)
    rw [hzero] at h
    exact h
  · change ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 4 2))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 4) (by omega) ([0, 1] : List (Fin 4))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    simpa [coordinateUniformizerCoweight_rankFour_zero_one] using h
  · change ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (fundamentalCoweight k 4 3))
    have h := coordinateUniformizerProduct_colorOneReachable
      k (d := 4) (by omega) ([0, 1, 2] : List (Fin 4))
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h
    rw [← mul_assoc,
      coordinateUniformizerCoweight_rankFour_zero_one_two] at h
    exact h

/-- Every normalized dominant rank-three Cartan vertex is reachable using
color-one steps. -/
theorem projectiveDominantCoweight_rankThree_colorOneReachable
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 2) :
    ColorOneReachable k 3 (QuotientGroup.mk 1)
      (QuotientGroup.mk (dominantCoweight k weight.toDominant)) := by
  refine Nat.strong_induction_on
    (p := fun n => ∀ w : ProjectiveDominantCoweight 2,
      projectiveDominantExponentSum w = n →
        ColorOneReachable k 3 (QuotientGroup.mk 1)
          (QuotientGroup.mk (dominantCoweight k w.toDominant)))
    (projectiveDominantExponentSum weight) ?_ weight rfl
  intro n ih w hw
  by_cases hzero : w = projectiveDominantCoweightZero 2
  · subst w
    simpa using (Relation.ReflTransGen.refl :
      ColorOneReachable k 3 (QuotientGroup.mk 1) (QuotientGroup.mk 1))
  · obtain ⟨previous, color, hdecomp⟩ :=
      exists_rankThree_projective_predecessor w hzero
    let fundamental := fundamentalProjectiveDominantCoweight
      2 (color.val + 1) (by omega)
    have hfundPos : 0 < projectiveDominantExponentSum fundamental := by
      have hterm : 0 < fundamental.toDominant.exponent (0 : Fin 3) := by
        fin_cases color <;>
          simp [fundamental, fundamentalProjectiveDominantCoweight,
            fundamentalDominantCoweight]
      have hle : fundamental.toDominant.exponent (0 : Fin 3) ≤
          projectiveDominantExponentSum fundamental := by
        exact Finset.single_le_sum
          (fun i _ => Nat.zero_le (fundamental.toDominant.exponent i))
          (Finset.mem_univ (0 : Fin 3))
      exact hterm.trans_le hle
    have hpreviousLt : projectiveDominantExponentSum previous < n := by
      rw [← hw, hdecomp, projectiveDominantExponentSum_add]
      exact Nat.lt_add_of_pos_right hfundPos
    have hprevious := ih _ hpreviousLt previous rfl
    have hfund := fundamentalCoweight_rankThree_colorOneReachable k color
    have htranslated := colorOneReachable_smul k 3
      (dominantCoweight k previous.toDominant) hfund
    have htranslated' : ColorOneReachable k 3
        (QuotientGroup.mk (dominantCoweight k previous.toDominant))
        (QuotientGroup.mk
          (dominantCoweight k previous.toDominant *
            dominantCoweight k fundamental.toDominant)) := by
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, fundamental,
        fundamentalProjectiveDominantCoweight,
        dominantCoweight_fundamental] using htranslated
    have htotal := hprevious.trans htranslated'
    simpa [hdecomp, fundamental,
      dominantCoweight_projectiveDominantCoweightAdd] using htotal

/-- Every normalized dominant rank-four Cartan vertex is reachable using
color-one steps. -/
theorem projectiveDominantCoweight_rankFour_colorOneReachable
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 3) :
    ColorOneReachable k 4 (QuotientGroup.mk 1)
      (QuotientGroup.mk (dominantCoweight k weight.toDominant)) := by
  refine Nat.strong_induction_on
    (p := fun n => ∀ w : ProjectiveDominantCoweight 3,
      projectiveDominantExponentSum w = n →
        ColorOneReachable k 4 (QuotientGroup.mk 1)
          (QuotientGroup.mk (dominantCoweight k w.toDominant)))
    (projectiveDominantExponentSum weight) ?_ weight rfl
  intro n ih w hw
  by_cases hzero : w = projectiveDominantCoweightZero 3
  · subst w
    simpa using (Relation.ReflTransGen.refl :
      ColorOneReachable k 4 (QuotientGroup.mk 1) (QuotientGroup.mk 1))
  · obtain ⟨previous, color, hdecomp⟩ :=
      exists_rankFour_projective_predecessor w hzero
    let fundamental := fundamentalProjectiveDominantCoweight
      3 (color.val + 1) (by omega)
    have hfundPos : 0 < projectiveDominantExponentSum fundamental := by
      have hterm : 0 < fundamental.toDominant.exponent (0 : Fin 4) := by
        fin_cases color <;>
          simp [fundamental, fundamentalProjectiveDominantCoweight,
            fundamentalDominantCoweight]
      have hle : fundamental.toDominant.exponent (0 : Fin 4) ≤
          projectiveDominantExponentSum fundamental := by
        exact Finset.single_le_sum
          (fun i _ => Nat.zero_le (fundamental.toDominant.exponent i))
          (Finset.mem_univ (0 : Fin 4))
      exact hterm.trans_le hle
    have hpreviousLt : projectiveDominantExponentSum previous < n := by
      rw [← hw, hdecomp, projectiveDominantExponentSum_add]
      exact Nat.lt_add_of_pos_right hfundPos
    have hprevious := ih _ hpreviousLt previous rfl
    have hfund := fundamentalCoweight_rankFour_colorOneReachable k color
    have htranslated := colorOneReachable_smul k 4
      (dominantCoweight k previous.toDominant) hfund
    have htranslated' : ColorOneReachable k 4
        (QuotientGroup.mk (dominantCoweight k previous.toDominant))
        (QuotientGroup.mk
          (dominantCoweight k previous.toDominant *
            dominantCoweight k fundamental.toDominant)) := by
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, fundamental,
        fundamentalProjectiveDominantCoweight,
        dominantCoweight_fundamental] using htranslated
    have htotal := hprevious.trans htranslated'
    simpa [hdecomp, fundamental,
      dominantCoweight_projectiveDominantCoweightAdd] using htotal

/-- If all normalized dominant Cartan vertices are color-one reachable, then
the full building is color-one reachable. -/
theorem colorOneReachable_of_projectiveDominant
    (k : Type u) [Field k] [Finite k] (n : ℕ)
    (hdominant : ∀ weight : ProjectiveDominantCoweight n,
      ColorOneReachable k (n + 1) (QuotientGroup.mk 1)
        (QuotientGroup.mk (dominantCoweight k weight.toDominant)))
    (q : BuildingVertex k (n + 1)) :
    ColorOneReachable k (n + 1) (QuotientGroup.mk 1) q := by
  obtain ⟨weight, hq⟩ :=
    exists_mem_projectiveDominantDoubleCoset k q.out
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset,
    Set.mem_mul] at hq
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hq
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  have hpath := hdominant weight
  have htranslated := colorOneReachable_smul k (n + 1) left hpath
  have hleftBase : left •
      (QuotientGroup.mk 1 : BuildingVertex k (n + 1)) =
        QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk]
    apply QuotientGroup.eq.mpr
    simpa using (maximalCompact k (n + 1)).inv_mem hleft
  have hmiddlePath : ColorOneReachable k (n + 1)
      (QuotientGroup.mk 1)
      (QuotientGroup.mk
        (left * dominantCoweight k weight.toDominant)) := by
    simpa [hleftBase, MulAction.Quotient.smul_mk, smul_eq_mul]
      using htranslated
  have hrightCoset :
      QuotientGroup.mk
          ((left * dominantCoweight k weight.toDominant) * right) =
        (QuotientGroup.mk
          (left * dominantCoweight k weight.toDominant) :
            BuildingVertex k (n + 1)) := by
    apply QuotientGroup.eq.mpr
    simpa [mul_assoc] using (maximalCompact k (n + 1)).inv_mem hright
  have hqOut :
      (QuotientGroup.mk q.out : BuildingVertex k (n + 1)) = q :=
    q.out_eq'
  rw [← hqOut, ← hfactor, ← hmiddleFactor, hrightCoset]
  exact hmiddlePath

/-- The rank-three affine building is connected by directed color-one
steps. -/
theorem rankThree_colorOneReachable
    (k : Type u) [Field k] [Finite k] (q : BuildingVertex k 3) :
    ColorOneReachable k 3 (QuotientGroup.mk 1) q := by
  exact colorOneReachable_of_projectiveDominant k 2
    (projectiveDominantCoweight_rankThree_colorOneReachable k) q

/-- The rank-four affine building is connected by directed color-one
steps. -/
theorem rankFour_colorOneReachable
    (k : Type u) [Field k] [Finite k] (q : BuildingVertex k 4) :
    ColorOneReachable k 4 (QuotientGroup.mk 1) q := by
  exact colorOneReachable_of_projectiveDominant k 3
    (projectiveDominantCoweight_rankFour_colorOneReachable k) q

/-- The fundamental Hecke function is exactly the indicator of the colored
building adjacency relation. -/
theorem fundamentalHeckeFunction_ne_zero_iff_adjacent
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (gx gy : HeckeGroup k d) :
    fundamentalHeckeFunction k d r (gx⁻¹ * gy) ≠ 0 ↔
      ColoredBuildingAdjacent k d r
        (QuotientGroup.mk gx) (QuotientGroup.mk gy) := by
  rw [coloredBuildingAdjacent_mk_iff]
  by_cases h : gx⁻¹ * gy ∈ fundamentalDoubleCoset k d r
  · simp [fundamentalHeckeFunction_apply, h]
  · simp [fundamentalHeckeFunction_apply, h]

/-- The finite set of right `K`-cosets occurring in a fundamental Cartan
double coset. -/
def fundamentalNeighborCosetSet
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    Set (BuildingVertex k d) :=
  QuotientGroup.mk '' fundamentalDoubleCoset k d r

theorem fundamentalNeighborCosetSet_finite
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    (fundamentalNeighborCosetSet k d r).Finite := by
  apply IsCompact.finite_of_discrete
  exact (fundamentalDoubleCoset_isCompact k d r).image
    QuotientGroup.continuous_mk

/-- The actual finite neighbor-coset set used to define the colored degree. -/
noncomputable def fundamentalNeighborCosets
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    Finset (BuildingVertex k d) :=
  (fundamentalNeighborCosetSet_finite k d r).toFinset

@[simp]
theorem mem_fundamentalNeighborCosets
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    x ∈ fundamentalNeighborCosets k d r ↔
      x ∈ fundamentalNeighborCosetSet k d r := by
  simp [fundamentalNeighborCosets]

/-- At the base vertex, membership in the finite projected double coset is
exactly the colored adjacency relation. -/
theorem mem_fundamentalNeighborCosetSet_iff_adjacent_base
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    x ∈ fundamentalNeighborCosetSet k d r ↔
      ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) x := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
      rw [coloredBuildingAdjacent_mk_iff]
      simp only [inv_one, one_mul]
      constructor
      · rintro ⟨t, ht, htg⟩
        have hright : t⁻¹ * g ∈ maximalCompact k d :=
          QuotientGroup.eq.mp htg
        have hmem := right_mul_mem_fundamentalDoubleCoset k d r hright ht
        simpa [mul_assoc] using hmem
      · intro hg
        exact ⟨g, hg, rfl⟩

/-- Left translation identifies the colored neighbor sets at any two
vertices in the same local-group orbit. -/
noncomputable def coloredNeighborSmuEquiv
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (g : HeckeGroup k d) (x : BuildingVertex k d) :
    {q // ColoredBuildingAdjacent k d r x q} ≃
      {q // ColoredBuildingAdjacent k d r (g • x) q} where
  toFun q := ⟨g • q.1,
    (coloredBuildingAdjacent_smul_iff k d r g x q.1).2 q.2⟩
  invFun q := ⟨g⁻¹ • q.1, by
    have h := (coloredBuildingAdjacent_smul_iff
      k d r g⁻¹ (g • x) q.1).2 q.2
    simpa using h⟩
  left_inv q := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp

/-- The finite fundamental-neighbor subtype is exactly the color-`r`
neighbor subtype at the base vertex. -/
noncomputable def fundamentalNeighborAdjacentBaseEquiv
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    {q // q ∈ fundamentalNeighborCosets k d r} ≃
      {q // ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) q} where
  toFun q := ⟨q.1,
    (mem_fundamentalNeighborCosetSet_iff_adjacent_base k d r q.1).1
      ((mem_fundamentalNeighborCosets k d r q.1).1 q.2)⟩
  invFun q := ⟨q.1,
    (mem_fundamentalNeighborCosets k d r q.1).2
      ((mem_fundamentalNeighborCosetSet_iff_adjacent_base k d r q.1).2
        q.2)⟩
  left_inv q := by rfl
  right_inv q := by rfl

/-- The unnormalized color-`r` degree is the cardinality of the constructed
finite right-coset set. -/
def coloredAdjacencyDegree
    (k : Type u) [Field k] [Finite k] (d r : ℕ) : ℕ :=
  (fundamentalNeighborCosets k d r).card

theorem coloredAdjacencyDegree_eq_ncard_neighbors
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    coloredAdjacencyDegree k d r =
      {x : BuildingVertex k d |
        ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) x}.ncard := by
  rw [coloredAdjacencyDegree, fundamentalNeighborCosets,
    ← Set.ncard_eq_toFinset_card (fundamentalNeighborCosetSet k d r)
      (fundamentalNeighborCosetSet_finite k d r)]
  apply congrArg Set.ncard
  ext x
  exact mem_fundamentalNeighborCosetSet_iff_adjacent_base k d r x

theorem quotientFiber_eq_preimage_left_mul
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q} =
      (fun x ↦ q.out⁻¹ * x) ⁻¹' (maximalCompact k d : Set (HeckeGroup k d)) := by
  ext x
  change QuotientGroup.mk x = q ↔ q.out⁻¹ * x ∈ maximalCompact k d
  constructor
  · intro hx
    apply QuotientGroup.eq.mp
    exact q.out_eq'.trans hx.symm
  · intro hx
    have hmk : QuotientGroup.mk q.out = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    exact hmk.symm.trans q.out_eq'

theorem normalizedLocalHaarMeasure_quotientFiber
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    normalizedLocalHaarMeasure k d
        ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}) = 1 := by
  rw [quotientFiber_eq_preimage_left_mul,
    MeasureTheory.measure_preimage_mul,
    normalizedLocalHaarMeasure_maximalCompact]

theorem fundamentalDoubleCoset_eq_biUnion_quotientFiber
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    fundamentalDoubleCoset k d r =
      ⋃ q ∈ fundamentalNeighborCosets k d r,
        (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_iUnion.2
    refine ⟨QuotientGroup.mk x, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact (mem_fundamentalNeighborCosets k d r _).2 ⟨x, hx, rfl⟩
    · rfl
  · intro hx
    obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hq, hxq⟩ := Set.mem_iUnion.1 hx
    have hqImage := (mem_fundamentalNeighborCosets k d r q).1 hq
    obtain ⟨t, ht, htq⟩ := hqImage
    have htx : t⁻¹ * x ∈ maximalCompact k d := by
      apply QuotientGroup.eq.mp
      exact htq.trans hxq.symm
    have hmem := right_mul_mem_fundamentalDoubleCoset k d r htx ht
    simpa [mul_assoc] using hmem

/-- Exact analytic normalization: the Haar volume of a fundamental double
coset is the cardinality of its finite right-`K` quotient, hence the actual
colored adjacency degree. -/
theorem normalizedLocalHaarMeasure_fundamentalDoubleCoset
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    normalizedLocalHaarMeasure k d (fundamentalDoubleCoset k d r) =
      coloredAdjacencyDegree k d r := by
  rw [fundamentalDoubleCoset_eq_biUnion_quotientFiber]
  rw [MeasureTheory.measure_biUnion_finset]
  · simp [normalizedLocalHaarMeasure_quotientFiber,
      coloredAdjacencyDegree]
  · intro a ha b hb hab
    change Disjoint
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {a})
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {b})
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  · intro q hq
    rw [quotientFiber_eq_preimage_left_mul]
    exact (maximalCompact_isOpen k d).measurableSet.preimage
      (measurable_const_mul q.out⁻¹)

/-! ### Integral representatives for the finite link -/

/-- The right `K`-coset represented by `g a_r`, for an integral matrix
`g ∈ GL_d(k[[X]])`. -/
def integralFundamentalNeighbor
    (k : Type*) [Field k] [Finite k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) : BuildingVertex k d :=
  QuotientGroup.mk
    (powerSeriesProjectiveMap k d g * fundamentalCoweight k d r)

theorem integralFundamentalNeighbor_mem
    (k : Type*) [Field k] [Finite k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    integralFundamentalNeighbor k d r g ∈
      fundamentalNeighborCosets k d r := by
  rw [mem_fundamentalNeighborCosets]
  refine ⟨powerSeriesProjectiveMap k d g * fundamentalCoweight k d r, ?_, rfl⟩
  rw [fundamentalDoubleCoset, Set.mem_mul]
  refine ⟨powerSeriesProjectiveMap k d g * fundamentalCoweight k d r, ?_,
    1, (maximalCompact k d).one_mem, mul_one _⟩
  rw [Set.mem_mul]
  exact ⟨powerSeriesProjectiveMap k d g,
    mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact g,
    fundamentalCoweight k d r, Set.mem_singleton _, rfl⟩

/-- Every right coset in a fundamental double coset has an integral
representative of the form `g a_r`. -/
theorem integralFundamentalNeighbor_surjective
    (k : Type*) [Field k] [Finite k] (d r : ℕ) :
    Function.Surjective (fun g : GL (Fin d) (IntegerRing k) ↦
      (⟨integralFundamentalNeighbor k d r g,
        integralFundamentalNeighbor_mem k d r g⟩ :
        {q // q ∈ fundamentalNeighborCosets k d r})) := by
  rintro ⟨q, hq⟩
  rw [mem_fundamentalNeighborCosets] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  rw [fundamentalDoubleCoset, Set.mem_mul] at ht
  obtain ⟨y, hy, z, hz, rfl⟩ := ht
  rw [Set.mem_mul] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  simp only [Set.mem_singleton_iff] at hb
  subst b
  rw [maximalCompact_eq_range_powerSeriesProjectiveMap] at ha
  obtain ⟨g, rfl⟩ := ha
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply QuotientGroup.eq.mpr
  simpa [integralFundamentalNeighbor, mul_assoc] using hz

/-- Equality of integral fundamental neighbors is projective maximal-compact
membership of the relative fundamental conjugate. -/
theorem integralFundamentalNeighbor_eq_iff_projective
    (k : Type*) [Field k] [Finite k] (d r : ℕ)
    (g h : GL (Fin d) (IntegerRing k)) :
    integralFundamentalNeighbor k d r g =
        integralFundamentalNeighbor k d r h ↔
      Matrix.ProjGenLinGroup.mk
          (fundamentalIntegralConjugate k d r (g⁻¹ * h)) ∈
        maximalCompact k d := by
  change QuotientGroup.mk
      (powerSeriesProjectiveMap k d g * fundamentalCoweight k d r) =
      QuotientGroup.mk
        (powerSeriesProjectiveMap k d h * fundamentalCoweight k d r) ↔ _
  rw [QuotientGroup.eq]
  change (powerSeriesProjectiveMap k d g * fundamentalCoweight k d r)⁻¹ *
      (powerSeriesProjectiveMap k d h * fundamentalCoweight k d r) ∈
        maximalCompact k d ↔ _
  simp [fundamentalIntegralConjugate, fundamentalCoweight,
    powerSeriesProjectiveMap, map_mul, map_inv]
  group

/-- The actual fundamental-neighbor map and the residue-plane map have
exactly the same fibers. -/
theorem integralFundamentalNeighbor_eq_iff_residuePlane
    (k : Type*) [Field k] [Finite k] (d r : ℕ) (hd : 0 < d) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    integralFundamentalNeighbor k d r g =
        integralFundamentalNeighbor k d r h ↔
      residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h := by
  rw [integralFundamentalNeighbor_eq_iff_projective]
  rw [projective_mk_mem_maximalCompact_iff_integral k d hd
    (fundamentalIntegralConjugate k d r (g⁻¹ * h))
    (fundamentalIntegralConjugate_det_localUnitOrder_eq_zero k d r (g⁻¹ * h))]
  exact (residueFundamentalPlane_eq_iff_integralConjugate k d r hr g h).symm

/-- Two surjections with identical fibers induce an equivalence of their
codomains. -/
noncomputable def equivOfSurjectiveOfEqFibers
    {α β γ : Type*} (f : α → β) (g : α → γ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfiber : ∀ x y, f x = f y ↔ g x = g y) : β ≃ γ where
  toFun b := g (Classical.choose (hf b))
  invFun c := f (Classical.choose (hg c))
  left_inv b := by
    calc
      f (Classical.choose (hg (g (Classical.choose (hf b))))) =
          f (Classical.choose (hf b)) := (hfiber _ _).mpr
            (Classical.choose_spec (hg (g (Classical.choose (hf b)))))
      _ = b := Classical.choose_spec (hf b)
  right_inv c := by
    calc
      g (Classical.choose (hf (f (Classical.choose (hg c))))) =
          g (Classical.choose (hg c)) := (hfiber _ _).mp
            (Classical.choose_spec (hf (f (Classical.choose (hg c)))))
      _ = c := Classical.choose_spec (hg c)

/-- The finite right-coset link of a fundamental Cartan type is the actual
finite residue-field Grassmannian, not merely a set of the same size. -/
noncomputable def fundamentalNeighborGrassmannianEquiv
    (k : Type*) [Field k] [Finite k] (d r : ℕ) (hd : 0 < d) (hr : r ≤ d) :
    {q // q ∈ fundamentalNeighborCosets k d r} ≃
      QEC.Coding.HighDimensionalExpander.FiniteGeometry.FiniteGrassmannian
        k (Fin d → k) r :=
  equivOfSurjectiveOfEqFibers
    (fun g : GL (Fin d) (IntegerRing k) =>
      (⟨integralFundamentalNeighbor k d r g,
        integralFundamentalNeighbor_mem k d r g⟩ :
        {q // q ∈ fundamentalNeighborCosets k d r}))
    (residueFundamentalPlane k d r hr)
    (integralFundamentalNeighbor_surjective k d r)
    (residueFundamentalPlane_surjective k d r hr)
    (fun g h => by
      rw [Subtype.ext_iff]
      exact integralFundamentalNeighbor_eq_iff_residuePlane k d r hd hr g h)

/-- Consequently, the actual colored adjacency degree is the cardinality of
the finite Grassmannian. -/
theorem coloredAdjacencyDegree_eq_natCard_finiteGrassmannian
    (k : Type*) [Field k] [Finite k] (d r : ℕ) (hd : 0 < d) (hr : r ≤ d) :
    coloredAdjacencyDegree k d r =
      Nat.card
        (QEC.Coding.HighDimensionalExpander.FiniteGeometry.FiniteGrassmannian
          k (Fin d → k) r) := by
  rw [coloredAdjacencyDegree, fundamentalNeighborCosets,
    ← Set.ncard_eq_toFinset_card (fundamentalNeighborCosetSet k d r)
      (fundamentalNeighborCosetSet_finite k d r)]
  simpa using
    (Nat.card_congr (fundamentalNeighborGrassmannianEquiv k d r hd hr))

theorem coloredAdjacencyDegree_rankThree_one
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 3 1 = Nat.card k ^ 2 + Nat.card k + 1 := by
  letI := Fintype.ofFinite k
  rw [coloredAdjacencyDegree_eq_natCard_finiteGrassmannian k 3 1 (by omega) (by omega)]
  simpa [Nat.card_eq_fintype_card] using
    QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankOneSubspaces_finThree k

theorem coloredAdjacencyDegree_rankThree_two
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 3 2 = Nat.card k ^ 2 + Nat.card k + 1 := by
  letI := Fintype.ofFinite k
  rw [coloredAdjacencyDegree_eq_natCard_finiteGrassmannian k 3 2 (by omega) (by omega)]
  simpa [Nat.card_eq_fintype_card] using
    QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankTwoSubspaces_finThree k

theorem coloredAdjacencyDegree_rankFour_one
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 4 1 =
      Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 := by
  letI := Fintype.ofFinite k
  rw [coloredAdjacencyDegree_eq_natCard_finiteGrassmannian k 4 1 (by omega) (by omega)]
  simpa [Nat.card_eq_fintype_card] using
    QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankOneSubspaces_finFour k

theorem coloredAdjacencyDegree_rankFour_two
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 4 2 =
      (Nat.card k ^ 2 + 1) * (Nat.card k ^ 2 + Nat.card k + 1) := by
  letI := Fintype.ofFinite k
  rw [coloredAdjacencyDegree_eq_natCard_finiteGrassmannian k 4 2 (by omega) (by omega)]
  simpa [Nat.card_eq_fintype_card] using
    QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankTwoSubspaces_finFour k

theorem coloredAdjacencyDegree_rankFour_three
    (k : Type*) [Field k] [Finite k] :
    coloredAdjacencyDegree k 4 3 =
      Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 := by
  letI := Fintype.ofFinite k
  rw [coloredAdjacencyDegree_eq_natCard_finiteGrassmannian k 4 3 (by omega) (by omega)]
  simpa [Nat.card_eq_fintype_card] using
    QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_rankThreeSubspaces_finFour k

theorem normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankThree_one
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 3 (fundamentalDoubleCoset k 3 1) =
      (Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankThree_one]

theorem normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankThree_two
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 3 (fundamentalDoubleCoset k 3 2) =
      (Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankThree_two]

theorem normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_one
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 1) =
      (Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankFour_one]

theorem normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_two
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 2) =
      ((Nat.card k ^ 2 + 1) * (Nat.card k ^ 2 + Nat.card k + 1) : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankFour_two]

theorem normalizedLocalHaarMeasure_fundamentalDoubleCoset_rankFour_three
    (k : Type*) [Field k] [Finite k] :
    normalizedLocalHaarMeasure k 4 (fundamentalDoubleCoset k 4 3) =
      (Nat.card k ^ 3 + Nat.card k ^ 2 + Nat.card k + 1 : ℕ) := by
  rw [normalizedLocalHaarMeasure_fundamentalDoubleCoset,
    coloredAdjacencyDegree_rankFour_three]

/-- The two colored relations for the two-dimensional (`PGL_3`) building. -/
def RankThreeAdjacent
    (k : Type u) [Field k] [Finite k] (color : RankThreeColor)
    (x y : BuildingVertex k 3) : Prop :=
  ColoredBuildingAdjacent k 3 (color.val + 1) x y

/-- The three colored relations for the three-dimensional (`PGL_4`) building. -/
def RankFourAdjacent
    (k : Type u) [Field k] [Finite k] (color : RankFourColor)
    (x y : BuildingVertex k 4) : Prop :=
  ColoredBuildingAdjacent k 4 (color.val + 1) x y

theorem rankThreeHecke_ne_zero_iff_adjacent
    (k : Type u) [Field k] [Finite k] (color : RankThreeColor)
    (gx gy : HeckeGroup k 3) :
    fundamentalHeckeFunction k 3 (color.val + 1) (gx⁻¹ * gy) ≠ 0 ↔
      RankThreeAdjacent k color (QuotientGroup.mk gx) (QuotientGroup.mk gy) :=
  fundamentalHeckeFunction_ne_zero_iff_adjacent k 3 (color.val + 1) gx gy

theorem rankFourHecke_ne_zero_iff_adjacent
    (k : Type u) [Field k] [Finite k] (color : RankFourColor)
    (gx gy : HeckeGroup k 4) :
    fundamentalHeckeFunction k 4 (color.val + 1) (gx⁻¹ * gy) ≠ 0 ↔
      RankFourAdjacent k color (QuotientGroup.mk gx) (QuotientGroup.mk gy) :=
  fundamentalHeckeFunction_ne_zero_iff_adjacent k 4 (color.val + 1) gx gy

end QEC.Coding.HighDimensionalExpander.SphericalHecke
