import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.Relations

/-!
# Completion of Cartwright--Steger apartment relations

Every fundamental rank-three or rank-four Bruhat--Tits neighbor is placed in
a translated coordinate apartment chamber.  Simple transitivity uniquely
lifts the chamber's color-one edges to Cartwright--Steger generators.  The
resulting rank-length word is a genuine relation, every proper prefix lies in
the prescribed fundamental double coset, and the selected prefix reaches the
original neighbor.  This is the exhaustive all-color bridge needed by the
finite LSV Hecke presentation.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

open QEC.Coding.HighDimensionalExpander.SphericalHecke

private theorem exists_compact_mul_fundamentalCoweight_mk_eq_of_mem_neighbor
    (P : BasePrime) (r : Rank) (color : Nat)
    (q : CartwrightStegerBuildingVertex P r)
    (hq : q ∈ fundamentalNeighborCosets
      (BaseField P) r.matrixRank color) :
    ∃ left : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P),
      left ∈ maximalCompact (BaseField P) r.matrixRank ∧
      QuotientGroup.mk
          (left * fundamentalCoweight (BaseField P) r.matrixRank color) = q := by
  rw [mem_fundamentalNeighborCosets] at hq
  obtain ⟨x, hx, hxq⟩ := hq
  rw [fundamentalDoubleCoset, Set.mem_mul] at hx
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hx
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  refine ⟨left, hleft, ?_⟩
  have hrightCoset :
      QuotientGroup.mk ((left *
          fundamentalCoweight (BaseField P) r.matrixRank color) * right) =
        (QuotientGroup.mk (left *
          fundamentalCoweight (BaseField P) r.matrixRank color) :
          CartwrightStegerBuildingVertex P r) := by
    apply QuotientGroup.eq.mpr
    simpa [mul_assoc] using
      (maximalCompact (BaseField P) r.matrixRank).inv_mem hright
  rw [← hxq, ← hfactor, ← hmiddleFactor, hrightCoset]

theorem buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq
    (P : BasePrime) (r : Rank) (color : Nat)
    (g : BuildingCartwrightStegerLattice P r)
    (hg : buildingLatticeVertexMap P r g =
      QuotientGroup.mk
        (fundamentalCoweight (BaseField P) r.matrixRank color)) :
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by
  have hcompact :
      (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))⁻¹ *
          fundamentalCoweight (BaseField P) r.matrixRank color ∈
        maximalCompact (BaseField P) r.matrixRank := by
    exact QuotientGroup.eq.mp hg
  have hmem := right_mul_mem_fundamentalDoubleCoset
    (BaseField P) r.matrixRank color
    ((maximalCompact (BaseField P) r.matrixRank).inv_mem hcompact)
    (fundamentalCoweight_mem_doubleCoset
      (BaseField P) r.matrixRank color)
  simpa [mul_assoc] using hmem

theorem buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
    (P : BasePrime) (r : Rank) (color : Nat)
    (g : BuildingCartwrightStegerLattice P r)
    (left : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) r.matrixRank)
    (hg : buildingLatticeVertexMap P r g =
      QuotientGroup.mk
        (left * fundamentalCoweight (BaseField P) r.matrixRank color)) :
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by
  let x := left * fundamentalCoweight (BaseField P) r.matrixRank color
  have hx : x ∈ fundamentalDoubleCoset
      (BaseField P) r.matrixRank color :=
    left_mul_mem_fundamentalDoubleCoset
      (BaseField P) r.matrixRank color hleft
      (fundamentalCoweight_mem_doubleCoset
        (BaseField P) r.matrixRank color)
  have hcompact :
      (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))⁻¹ *
          x ∈ maximalCompact (BaseField P) r.matrixRank := by
    exact QuotientGroup.eq.mp hg
  have hmem := right_mul_mem_fundamentalDoubleCoset
    (BaseField P) r.matrixRank color
    ((maximalCompact (BaseField P) r.matrixRank).inv_mem hcompact) hx
  simpa [x, mul_assoc] using hmem

private noncomputable def translatedRankThreeVertex1
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk (left *
    coordinateUniformizerCoweight (BaseField P) 3 0)

private noncomputable def translatedRankThreeVertex2
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .three :=
  QuotientGroup.mk ((left *
    coordinateUniformizerCoweight (BaseField P) 3 0) *
      coordinateUniformizerCoweight (BaseField P) 3 1)

private theorem translatedRankThreeAdjacent01
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 3) :
    ColoredBuildingAdjacent (BaseField P) 3 1
      (QuotientGroup.mk 1) (translatedRankThreeVertex1 P left) := by
  rw [translatedRankThreeVertex1]
  change ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk 1)
    (QuotientGroup.mk (left *
      coordinateUniformizerCoweight (BaseField P) 3 0))
  rw [coloredBuildingAdjacent_mk_iff]
  simp only [inv_one, one_mul]
  change left * coordinateUniformizerCoweight (BaseField P) 3 0 ∈
    fundamentalDoubleCoset (BaseField P) 3 1
  exact left_mul_mem_fundamentalDoubleCoset (BaseField P) 3 1 hleft
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) 0)

private theorem translatedRankThreeAdjacent12
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P)) :
    ColoredBuildingAdjacent (BaseField P) 3 1
      (translatedRankThreeVertex1 P left)
      (translatedRankThreeVertex2 P left) := by
  rw [translatedRankThreeVertex1, translatedRankThreeVertex2]
  change ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk (left *
      coordinateUniformizerCoweight (BaseField P) 3 0))
    (QuotientGroup.mk ((left *
      coordinateUniformizerCoweight (BaseField P) 3 0) *
        coordinateUniformizerCoweight (BaseField P) 3 1))
  rw [coloredBuildingAdjacent_mk_iff]
  change (left * coordinateUniformizerCoweight (BaseField P) 3 0)⁻¹ *
      ((left * coordinateUniformizerCoweight (BaseField P) 3 0) *
        coordinateUniformizerCoweight (BaseField P) 3 1) ∈
    fundamentalDoubleCoset (BaseField P) 3 1
  simpa [mul_assoc] using
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) (1 : Fin 3))

private theorem translatedRankThreeAdjacent20
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 3) :
    ColoredBuildingAdjacent (BaseField P) 3 1
      (translatedRankThreeVertex2 P left) (QuotientGroup.mk 1) := by
  let c0 := coordinateUniformizerCoweight (BaseField P) 3 (0 : Fin 3)
  let c1 := coordinateUniformizerCoweight (BaseField P) 3 (1 : Fin 3)
  let c2 := coordinateUniformizerCoweight (BaseField P) 3 (2 : Fin 3)
  have hstep : ColoredBuildingAdjacent (BaseField P) 3 1
      (QuotientGroup.mk ((left * c0) * c1))
      (QuotientGroup.mk (((left * c0) * c1) * c2)) := by
    rw [coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using
      (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
        (BaseField P) (by omega) (2 : Fin 3))
  have hcycle : c0 * c1 * c2 = 1 := by
    have h := prod_coordinateUniformizerCoweight (BaseField P) 3
    norm_num [List.finRange] at h
    simpa [c0, c1, c2, mul_assoc] using h
  have hend :
      (QuotientGroup.mk (((left * c0) * c1) * c2) :
          CartwrightStegerBuildingVertex P .three) = QuotientGroup.mk 1 := by
    rw [show ((left * c0) * c1) * c2 = left * (c0 * c1 * c2) by group,
      hcycle, mul_one]
    apply QuotientGroup.eq.mpr
    rw [mul_one]
    exact (maximalCompact (BaseField P) 3).inv_mem hleft
  rw [translatedRankThreeVertex2]
  change ColoredBuildingAdjacent (BaseField P) 3 1
    (QuotientGroup.mk ((left * c0) * c1)) (QuotientGroup.mk 1)
  exact hend ▸ hstep

private theorem exists_translated_rankThree_apartment_relation
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 3) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 3) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 ∧
      buildingLatticeVertexMap P .three
          (buildingLatticeGenerator P .three u0) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 3 1) ∧
      buildingLatticeVertexMap P .three
          (buildingLatticeGenerator P .three u0 *
            buildingLatticeGenerator P .three u1) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 3 2) := by
  let v1 := translatedRankThreeVertex1 P left
  let v2 := translatedRankThreeVertex2 P left
  let u0 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three 1 v1 (by
      rw [buildingLatticeVertexMap_one]
      exact translatedRankThreeAdjacent01 P left hleft))
  have hu0 : buildingLatticeVertexMap P .three
      (1 * buildingLatticeGenerator P .three u0) = v1 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .three 1 v1 (by
        rw [buildingLatticeVertexMap_one]
        exact translatedRankThreeAdjacent01 P left hleft))).1
  let u1 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three (1 * buildingLatticeGenerator P .three u0) v2 (by
      rw [hu0]
      exact translatedRankThreeAdjacent12 P left))
  have hu01 : buildingLatticeVertexMap P .three
      ((1 * buildingLatticeGenerator P .three u0) *
        buildingLatticeGenerator P .three u1) = v2 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .three (1 * buildingLatticeGenerator P .three u0) v2 (by
        rw [hu0]
        exact translatedRankThreeAdjacent12 P left))).1
  let u2 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .three ((1 * buildingLatticeGenerator P .three u0) *
      buildingLatticeGenerator P .three u1) (QuotientGroup.mk 1) (by
        rw [hu01]
        exact translatedRankThreeAdjacent20 P left hleft))
  have hu012 : buildingLatticeVertexMap P .three
      (((1 * buildingLatticeGenerator P .three u0) *
        buildingLatticeGenerator P .three u1) *
          buildingLatticeGenerator P .three u2) = QuotientGroup.mk 1 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .three ((1 * buildingLatticeGenerator P .three u0) *
        buildingLatticeGenerator P .three u1) (QuotientGroup.mk 1) (by
          rw [hu01]
          exact translatedRankThreeAdjacent20 P left hleft))).1
  refine ⟨u0, u1, u2, ?_, ?_, ?_⟩
  · apply buildingLatticeVertexMap_injective P .three
    simp only [one_mul] at hu012
    exact hu012
  · rw [one_mul] at hu0
    dsimp [v1, translatedRankThreeVertex1] at hu0
    have hc0 : coordinateUniformizerCoweight (BaseField P) 3 (0 : Fin 3) =
        fundamentalCoweight (BaseField P) 3 1 := by
      exact coordinateUniformizerCoweight_zero_eq_fundamental
        (BaseField P) (d := 3) (by omega)
    rw [hc0] at hu0
    exact hu0
  · rw [one_mul] at hu01
    dsimp [v2, translatedRankThreeVertex2] at hu01
    rw [mul_assoc, coordinateUniformizerCoweight_rankThree_zero_one] at hu01
    exact hu01

theorem exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
    (P : BasePrime) (color : Fin 2)
    (q : CartwrightStegerBuildingVertex P .three)
    (hq : q ∈ fundamentalNeighborCosets (BaseField P) 3 (color.val + 1)) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 ∧
      (buildingLatticeGenerator P .three u0).1 ∈
        fundamentalDoubleCoset (BaseField P) 3 1 ∧
      (buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1).1 ∈
        fundamentalDoubleCoset (BaseField P) 3 2 ∧
      buildingLatticeVertexMap P .three
        (if color = 0 then buildingLatticeGenerator P .three u0
          else buildingLatticeGenerator P .three u0 *
            buildingLatticeGenerator P .three u1) = q := by
  obtain ⟨left, hleft, hqleft⟩ :=
    exists_compact_mul_fundamentalCoweight_mk_eq_of_mem_neighbor
      P .three (color.val + 1) q hq
  obtain ⟨u0, u1, u2, hrel, hprefix1, hprefix2⟩ :=
    exists_translated_rankThree_apartment_relation P left hleft
  have hmem1 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .three 1 (buildingLatticeGenerator P .three u0) left hleft hprefix1
  have hmem2 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .three 2 (buildingLatticeGenerator P .three u0 *
        buildingLatticeGenerator P .three u1) left hleft hprefix2
  refine ⟨u0, u1, u2, hrel, hmem1, hmem2, ?_⟩
  fin_cases color
  · simpa using hprefix1.trans hqleft
  · simpa using hprefix2.trans hqleft

private noncomputable def translatedRankFourVertex1
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk (left *
    coordinateUniformizerCoweight (BaseField P) 4 0)

private noncomputable def translatedRankFourVertex2
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk ((left *
    coordinateUniformizerCoweight (BaseField P) 4 0) *
      coordinateUniformizerCoweight (BaseField P) 4 1)

private noncomputable def translatedRankFourVertex3
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    CartwrightStegerBuildingVertex P .four :=
  QuotientGroup.mk (((left *
    coordinateUniformizerCoweight (BaseField P) 4 0) *
      coordinateUniformizerCoweight (BaseField P) 4 1) *
        coordinateUniformizerCoweight (BaseField P) 4 2)

private theorem translatedRankFourAdjacent01
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 4) :
    ColoredBuildingAdjacent (BaseField P) 4 1
      (QuotientGroup.mk 1) (translatedRankFourVertex1 P left) := by
  rw [translatedRankFourVertex1]
  change ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk 1)
    (QuotientGroup.mk (left *
      coordinateUniformizerCoweight (BaseField P) 4 0))
  rw [coloredBuildingAdjacent_mk_iff]
  simp only [inv_one, one_mul]
  exact left_mul_mem_fundamentalDoubleCoset (BaseField P) 4 1 hleft
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) 0)

private theorem translatedRankFourAdjacent12
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    ColoredBuildingAdjacent (BaseField P) 4 1
      (translatedRankFourVertex1 P left)
      (translatedRankFourVertex2 P left) := by
  rw [translatedRankFourVertex1, translatedRankFourVertex2]
  change ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk (left *
      coordinateUniformizerCoweight (BaseField P) 4 0))
    (QuotientGroup.mk ((left *
      coordinateUniformizerCoweight (BaseField P) 4 0) *
        coordinateUniformizerCoweight (BaseField P) 4 1))
  rw [coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) (1 : Fin 4))

private theorem translatedRankFourAdjacent23
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P)) :
    ColoredBuildingAdjacent (BaseField P) 4 1
      (translatedRankFourVertex2 P left)
      (translatedRankFourVertex3 P left) := by
  rw [translatedRankFourVertex2, translatedRankFourVertex3]
  change ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk ((left *
      coordinateUniformizerCoweight (BaseField P) 4 0) *
        coordinateUniformizerCoweight (BaseField P) 4 1))
    (QuotientGroup.mk (((left *
      coordinateUniformizerCoweight (BaseField P) 4 0) *
        coordinateUniformizerCoweight (BaseField P) 4 1) *
          coordinateUniformizerCoweight (BaseField P) 4 2))
  rw [coloredBuildingAdjacent_mk_iff]
  simpa [mul_assoc] using
    (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
      (BaseField P) (by omega) (2 : Fin 4))

private theorem translatedRankFourAdjacent30
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 4) :
    ColoredBuildingAdjacent (BaseField P) 4 1
      (translatedRankFourVertex3 P left) (QuotientGroup.mk 1) := by
  let c0 := coordinateUniformizerCoweight (BaseField P) 4 (0 : Fin 4)
  let c1 := coordinateUniformizerCoweight (BaseField P) 4 (1 : Fin 4)
  let c2 := coordinateUniformizerCoweight (BaseField P) 4 (2 : Fin 4)
  let c3 := coordinateUniformizerCoweight (BaseField P) 4 (3 : Fin 4)
  have hstep : ColoredBuildingAdjacent (BaseField P) 4 1
      (QuotientGroup.mk (((left * c0) * c1) * c2))
      (QuotientGroup.mk ((((left * c0) * c1) * c2) * c3)) := by
    rw [coloredBuildingAdjacent_mk_iff]
    simpa [mul_assoc] using
      (coordinateUniformizerCoweight_mem_fundamentalDoubleCoset_one
        (BaseField P) (by omega) (3 : Fin 4))
  have hcycle : ((c0 * c1) * c2) * c3 = 1 := by
    have h := prod_coordinateUniformizerCoweight (BaseField P) 4
    norm_num [List.finRange] at h
    simpa [c0, c1, c2, c3, mul_assoc] using h
  have hend :
      (QuotientGroup.mk ((((left * c0) * c1) * c2) * c3) :
          CartwrightStegerBuildingVertex P .four) = QuotientGroup.mk 1 := by
    rw [show (((left * c0) * c1) * c2) * c3 =
      left * (((c0 * c1) * c2) * c3) by group, hcycle, mul_one]
    apply QuotientGroup.eq.mpr
    rw [mul_one]
    exact (maximalCompact (BaseField P) 4).inv_mem hleft
  rw [translatedRankFourVertex3]
  change ColoredBuildingAdjacent (BaseField P) 4 1
    (QuotientGroup.mk (((left * c0) * c1) * c2)) (QuotientGroup.mk 1)
  exact hend ▸ hstep

private theorem exists_translated_rankFour_apartment_relation
    (P : BasePrime)
    (left : Matrix.ProjGenLinGroup (Fin 4) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) 4) :
    ∃ u0 u1 u2 u3 : ConstantProjectiveClass P .four,
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2) *
              buildingLatticeGenerator P .four u3 = 1 ∧
      buildingLatticeVertexMap P .four
          (buildingLatticeGenerator P .four u0) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 4 1) ∧
      buildingLatticeVertexMap P .four
          (buildingLatticeGenerator P .four u0 *
            buildingLatticeGenerator P .four u1) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 4 2) ∧
      buildingLatticeVertexMap P .four
          ((buildingLatticeGenerator P .four u0 *
            buildingLatticeGenerator P .four u1) *
              buildingLatticeGenerator P .four u2) =
        QuotientGroup.mk (left * fundamentalCoweight (BaseField P) 4 3) := by
  let v1 := translatedRankFourVertex1 P left
  let v2 := translatedRankFourVertex2 P left
  let v3 := translatedRankFourVertex3 P left
  let u0 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .four 1 v1 (by
      rw [buildingLatticeVertexMap_one]
      exact translatedRankFourAdjacent01 P left hleft))
  have hu0 : buildingLatticeVertexMap P .four
      (1 * buildingLatticeGenerator P .four u0) = v1 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .four 1 v1 (by
        rw [buildingLatticeVertexMap_one]
        exact translatedRankFourAdjacent01 P left hleft))).1
  let u1 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .four (1 * buildingLatticeGenerator P .four u0) v2 (by
      rw [hu0]
      exact translatedRankFourAdjacent12 P left))
  have hu01 : buildingLatticeVertexMap P .four
      ((1 * buildingLatticeGenerator P .four u0) *
        buildingLatticeGenerator P .four u1) = v2 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .four (1 * buildingLatticeGenerator P .four u0) v2 (by
        rw [hu0]
        exact translatedRankFourAdjacent12 P left))).1
  let u2 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .four ((1 * buildingLatticeGenerator P .four u0) *
      buildingLatticeGenerator P .four u1) v3 (by
        rw [hu01]
        exact translatedRankFourAdjacent23 P left))
  have hu012 : buildingLatticeVertexMap P .four
      (((1 * buildingLatticeGenerator P .four u0) *
        buildingLatticeGenerator P .four u1) *
          buildingLatticeGenerator P .four u2) = v3 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .four ((1 * buildingLatticeGenerator P .four u0) *
        buildingLatticeGenerator P .four u1) v3 (by
          rw [hu01]
          exact translatedRankFourAdjacent23 P left))).1
  let u3 := Classical.choose (existsUnique_generator_mul_eq_coloredNeighbor
    P .four (((1 * buildingLatticeGenerator P .four u0) *
      buildingLatticeGenerator P .four u1) *
        buildingLatticeGenerator P .four u2) (QuotientGroup.mk 1) (by
          rw [hu012]
          exact translatedRankFourAdjacent30 P left hleft))
  have hu0123 : buildingLatticeVertexMap P .four
      ((((1 * buildingLatticeGenerator P .four u0) *
        buildingLatticeGenerator P .four u1) *
          buildingLatticeGenerator P .four u2) *
            buildingLatticeGenerator P .four u3) = QuotientGroup.mk 1 :=
    (Classical.choose_spec (existsUnique_generator_mul_eq_coloredNeighbor
      P .four (((1 * buildingLatticeGenerator P .four u0) *
        buildingLatticeGenerator P .four u1) *
          buildingLatticeGenerator P .four u2) (QuotientGroup.mk 1) (by
            rw [hu012]
            exact translatedRankFourAdjacent30 P left hleft))).1
  refine ⟨u0, u1, u2, u3, ?_, ?_, ?_, ?_⟩
  · apply buildingLatticeVertexMap_injective P .four
    simp only [one_mul] at hu0123
    exact hu0123
  · rw [one_mul] at hu0
    dsimp [v1, translatedRankFourVertex1] at hu0
    have hc0 : coordinateUniformizerCoweight (BaseField P) 4 (0 : Fin 4) =
        fundamentalCoweight (BaseField P) 4 1 := by
      exact coordinateUniformizerCoweight_zero_eq_fundamental
        (BaseField P) (d := 4) (by omega)
    rw [hc0] at hu0
    exact hu0
  · rw [one_mul] at hu01
    dsimp [v2, translatedRankFourVertex2] at hu01
    rw [mul_assoc, coordinateUniformizerCoweight_rankFour_zero_one] at hu01
    exact hu01
  · rw [one_mul] at hu012
    dsimp [v3, translatedRankFourVertex3] at hu012
    rw [show ((left * coordinateUniformizerCoweight (BaseField P) 4 0) *
        coordinateUniformizerCoweight (BaseField P) 4 1) *
        coordinateUniformizerCoweight (BaseField P) 4 2 =
      left * ((coordinateUniformizerCoweight (BaseField P) 4 0 *
        coordinateUniformizerCoweight (BaseField P) 4 1) *
        coordinateUniformizerCoweight (BaseField P) 4 2) by group,
      coordinateUniformizerCoweight_rankFour_zero_one_two] at hu012
    exact hu012

theorem exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
    (P : BasePrime) (color : Fin 3)
    (q : CartwrightStegerBuildingVertex P .four)
    (hq : q ∈ fundamentalNeighborCosets (BaseField P) 4 (color.val + 1)) :
    ∃ u0 u1 u2 u3 : ConstantProjectiveClass P .four,
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2) *
              buildingLatticeGenerator P .four u3 = 1 ∧
      (buildingLatticeGenerator P .four u0).1 ∈
        fundamentalDoubleCoset (BaseField P) 4 1 ∧
      (buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1).1 ∈
        fundamentalDoubleCoset (BaseField P) 4 2 ∧
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2).1 ∈
        fundamentalDoubleCoset (BaseField P) 4 3 ∧
      buildingLatticeVertexMap P .four
        (match color.val with
        | 0 => buildingLatticeGenerator P .four u0
        | 1 => buildingLatticeGenerator P .four u0 *
            buildingLatticeGenerator P .four u1
        | _ => (buildingLatticeGenerator P .four u0 *
            buildingLatticeGenerator P .four u1) *
              buildingLatticeGenerator P .four u2) = q := by
  obtain ⟨left, hleft, hqleft⟩ :=
    exists_compact_mul_fundamentalCoweight_mk_eq_of_mem_neighbor
      P .four (color.val + 1) q hq
  obtain ⟨u0, u1, u2, u3, hrel, hprefix1, hprefix2, hprefix3⟩ :=
    exists_translated_rankFour_apartment_relation P left hleft
  have hmem1 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .four 1 (buildingLatticeGenerator P .four u0) left hleft hprefix1
  have hmem2 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .four 2 (buildingLatticeGenerator P .four u0 *
        buildingLatticeGenerator P .four u1) left hleft hprefix2
  have hmem3 :=
    buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
      P .four 3 ((buildingLatticeGenerator P .four u0 *
        buildingLatticeGenerator P .four u1) *
          buildingLatticeGenerator P .four u2) left hleft hprefix3
  refine ⟨u0, u1, u2, u3, hrel, hmem1, hmem2, hmem3, ?_⟩
  fin_cases color
  · simpa using hprefix1.trans hqleft
  · simpa using hprefix2.trans hqleft
  · simpa using hprefix3.trans hqleft

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
