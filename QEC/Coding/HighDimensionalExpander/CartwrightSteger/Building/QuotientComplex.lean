import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.PrasadSpecialization
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.Reduction
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.ApartmentCompletion
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingQuotient
import QEC.Coding.HighDimensionalExpander.Combinatorics.CayleyClique
import QEC.Coding.HighDimensionalExpander.Combinatorics.SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Finite Cartwright--Steger quotient complexes

This file turns the construction-owned finite Cartwright--Steger image and
its explicit generator family into actual finite Cayley clique complexes.
The rank-three and rank-four values are then fed directly to the simplicial
binary-chain construction.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open Finset

private theorem faceVertices_injective
    {V : Type*} {K : AbstractSimplicialComplex V} {p : Nat} :
    Function.Injective
      (SimplicialChain.Face.vertices :
        SimplicialChain.Face K p → Finset V) := by
  intro σ τ h
  cases σ
  cases τ
  simp_all

/-- The actual finite Cartwright--Steger image, used as the vertex group of
the quotient Cayley complex. -/
noncomputable def IndexFiniteGroup (P : BasePrime) (r : Rank) (level : Nat) :=
  IndexCartwrightStegerImage P r level

noncomputable instance residuePGLFinite
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finite (PGL P r level) :=
  Finite.of_surjective
    (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) → PGL P r level)
    Matrix.ProjGenLinGroup.mk_surjective

noncomputable instance indexFiniteGroupFinite
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finite (IndexFiniteGroup P r level) := by
  dsimp [IndexFiniteGroup]
  infer_instance

noncomputable instance indexFiniteGroupFintype
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype (IndexFiniteGroup P r level) :=
  Fintype.ofFinite _

noncomputable instance indexFiniteGroupDecidableEq
    (P : BasePrime) (r : Rank) (level : Nat) :
    DecidableEq (IndexFiniteGroup P r level) :=
  Classical.decEq _

/-- The genuine building-lattice reduction with its codomain exposed through
the finite vertex-group name used by the quotient complex. -/
noncomputable def buildingLatticeFiniteReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r →* IndexFiniteGroup P r level :=
  buildingLatticeReduction P r level

@[simp] theorem buildingLatticeFiniteReduction_apply
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : BuildingCartwrightStegerLattice P r) :
    buildingLatticeFiniteReduction P r level g =
      buildingLatticeReduction P r level g :=
  rfl

/-- The Cayley vertex group is the actual quotient of the constructed
integral lattice by its selected principal congruence subgroup. -/
noncomputable def lsvCongruenceVertexEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    OrderSplitCartwrightStegerLattice P r ⧸
        OrderSplitCartwrightStegerCongruenceSubgroup P r level ≃
      IndexFiniteGroup P r level :=
  (orderSplitLatticeQuotientEquiv P r level).toEquiv

/-- The same finite vertex group as the genuine quotient of the simply
transitive building lattice.  This is the construction-level
quotient/building identification, independent of the split-coordinate
presentation above. -/
noncomputable def lsvBuildingCongruenceVertexEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    BuildingCartwrightStegerLattice P r ⧸
        BuildingCartwrightStegerCongruenceSubgroup P r level ≃
      IndexFiniteGroup P r level :=
  (buildingLatticeQuotientEquiv P r level).toEquiv

/-- Every explicit conjugate, bundled as an element of the generated finite
image. -/
noncomputable def bundledIndexGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    IndexFiniteGroup P r level :=
  ⟨indexCartwrightStegerClassGenerator P r level u,
    indexCartwrightStegerGenerator_mem_image P r level u⟩

/-- The color-one generator set is computed from the source projective
constant classes `F_(q^d)^× / F_q^×`; it is not supplied by a caller. -/
noncomputable def indexGeneratorFinset
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finset (IndexFiniteGroup P r level) :=
  Finset.univ.image (bundledIndexGenerator P r level)

theorem bundledIndexGenerator_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (bundledIndexGenerator P r level) := by
  intro u v huv
  apply indexCartwrightStegerClassGenerator_injective P r level
  exact congrArg (fun g : IndexFiniteGroup P r level =>
    (g : PGL P r level)) huv

theorem bundledIndexGenerator_ne_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    bundledIndexGenerator P r level u ≠ 1 := by
  intro hu
  apply indexCartwrightStegerClassGenerator_ne_one P r level u
  exact congrArg (fun g : IndexFiniteGroup P r level =>
    (g : PGL P r level)) hu

/-- In rank four the selected determinant color has exact order four at
every hierarchy level.  The residue degree is a multiple of four and the
base prime is odd, so the residue-field unit-group order is divisible by
four. -/
theorem rankFour_indexRatioClass_orderOf
    (P : BasePrime) (level : Nat) :
    orderOf
        (QuotientGroup.mk (indexRatioUnit P .four level) :
          ResiduePowerClass P .four level) = 4 := by
  rw [indexRatioUnit_orderOf]
  change (Fintype.card (ResidueField P .four level) - 1).gcd 4 = 4
  rw [← Nat.card_eq_fintype_card, natCard_residueField]
  apply Nat.gcd_eq_right
  have hodd : Odd P.q := P.prime.odd_of_ne_two
    (ne_of_gt (lt_of_lt_of_le (by norm_num) P.five_le))
  obtain ⟨k, hk⟩ := hodd
  have hfour : 4 ∣ P.q ^ 2 - 1 := by
    refine ⟨k * (k + 1), ?_⟩
    rw [hk]
    have hcalc :
        (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  have htwo : 2 ∣ Rank.four.residueExponent level := by
    refine ⟨2 * (3 + level), ?_⟩
    simp [Rank.residueExponent]
    ring
  exact hfour.trans (Nat.pow_sub_one_dvd_pow_sub_one P.q htwo)

/-- A two-step rank-four prefix cannot collapse in the finite quotient: its
determinant color is the square of an element of exact order four. -/
theorem rankFour_bundledIndexGenerator_mul_ne_one
    (P : BasePrime) (level : Nat)
    (u v : ConstantProjectiveClass P .four) :
    bundledIndexGenerator P .four level u *
        bundledIndexGenerator P .four level v ≠ 1 := by
  intro hmul
  have hdet := congrArg
    (fun g : IndexFiniteGroup P .four level =>
      residueProjectiveDetClass P .four level
        (g : PGL P .four level)) hmul
  have hsq :
      (QuotientGroup.mk (indexRatioUnit P .four level) :
        ResiduePowerClass P .four level) ^ 2 = 1 := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_one,
      bundledIndexGenerator, map_mul,
      residueProjectiveDetClass_indexCartwrightStegerClassGenerator,
      map_one, pow_two] using hdet
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [rankFour_indexRatioClass_orderOf] at hdvd
  omega

/-- The finite generating set has exactly the source projective-line size;
no repetitions are hidden by the selected representatives. -/
theorem card_indexGeneratorFinset
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGeneratorFinset P r level).card =
      Fintype.card (ConstantProjectiveClass P r) := by
  rw [indexGeneratorFinset,
    Finset.card_image_of_injective _
      (bundledIndexGenerator_injective P r level),
    Finset.card_univ]

theorem card_indexGeneratorFinset_le
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGeneratorFinset P r level).card ≤
      Fintype.card (ConstantProjectiveClass P r) := by
  exact (card_indexGeneratorFinset P r level).le

/-- A level-independent upper bound on the number of directed generators.
It depends only on the base prime and the Cartwright--Steger rank. -/
noncomputable def indexGeneratorBound (P : BasePrime) (r : Rank) : Nat :=
  Fintype.card (ConstantProjectiveClass P r)

@[simp] theorem coe_bundledIndexGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    ((bundledIndexGenerator P r level u :
        IndexFiniteGroup P r level) : PGL P r level) =
      indexCartwrightStegerClassGenerator P r level u :=
  rfl

/-- Exact source-size equation for the hierarchy's projective generator
index. -/
theorem indexGeneratorBound_mul_baseScalar
    (P : BasePrime) (r : Rank) :
    indexGeneratorBound P r * (P.q - 1) =
      P.q ^ r.matrixRank - 1 := by
  simpa [indexGeneratorBound, Nat.card_eq_fintype_card] using
    natCard_constantProjectiveClass_mul_baseScalar P r

/-- Product of a finite word in the color-one Cartwright--Steger
generators. -/
noncomputable def indexGeneratorWordProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    IndexFiniteGroup P r level :=
  (word.map (bundledIndexGenerator P r level)).prod

private theorem coe_indexGeneratorWordProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    ((indexGeneratorWordProduct P r level word : IndexFiniteGroup P r level) :
        PGL P r level) =
      (word.map (indexCartwrightStegerClassGenerator P r level)).prod := by
  induction word with
  | nil => rfl
  | cons u word ih =>
      simp only [indexGeneratorWordProduct, List.map_cons, List.prod_cons,
        Subgroup.coe_mul, coe_bundledIndexGenerator]
      simpa [indexGeneratorWordProduct] using congrArg
        (fun g => indexCartwrightStegerClassGenerator P r level u * g) ih

private theorem indexGeneratorWordProduct_eq_one_of_classProduct_eq_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (h : (word.map
      (indexCartwrightStegerClassGenerator P r level)).prod = 1) :
    indexGeneratorWordProduct P r level word = 1 := by
  apply Subtype.ext
  rw [coe_indexGeneratorWordProduct]
  exact h

/-- Every relation in the genuine building lattice remains a relation after
passing to the selected finite congruence image. -/
private theorem indexGeneratorWordProduct_eq_one_of_building_relation
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (hbuilding : (word.map (buildingLatticeGenerator P r)).prod = 1) :
    indexGeneratorWordProduct P r level word = 1 := by
  apply indexGeneratorWordProduct_eq_one_of_classProduct_eq_one
  exact indexClassGenerator_wordProduct_eq_one_of_building_relation
    P r level word hbuilding

/-- Product of a rank-length tuple of color-one generators. -/
noncomputable def indexGeneratorTupleProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    IndexFiniteGroup P r level :=
  indexGeneratorWordProduct P r level (List.ofFn u)

/-- Product of the first `k` entries of a rank-length generator tuple. -/
noncomputable def indexGeneratorPrefixProduct
    (P : BasePrime) (r : Rank) (level k : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    IndexFiniteGroup P r level :=
  indexGeneratorWordProduct P r level ((List.ofFn u).take k)

private def rankZeroIndex (r : Rank) : Fin r.matrixRank :=
  ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩

@[simp] theorem indexGeneratorPrefixProduct_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    indexGeneratorPrefixProduct P r level 1 u =
      bundledIndexGenerator P r level (u (rankZeroIndex r)) := by
  have hlen : 0 < (List.ofFn u).length := by
    rw [List.length_ofFn]
    exact (rankZeroIndex r).isLt
  have htake := List.take_one_drop_eq_of_lt_length
    (l := List.ofFn u) (n := 0) hlen
  have hget :
      (List.ofFn u).get ⟨0, hlen⟩ = u (rankZeroIndex r) := by
    rw [List.get_ofFn]
    apply congrArg u
    apply Fin.ext
    rfl
  rw [List.drop_zero, hget] at htake
  rw [indexGeneratorPrefixProduct, htake]
  simp [indexGeneratorWordProduct]

/-- Product of a finite word in the genuine Cartwright--Steger building
lattice.  Relation data are fixed before passing to any congruence quotient. -/
noncomputable def buildingGeneratorWordProduct
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r)) :
    BuildingCartwrightStegerLattice P r :=
  (word.map (buildingLatticeGenerator P r)).prod

/-- Product of the first `k` entries of a rank-length tuple in the genuine
Cartwright--Steger building lattice.  This is the level-independent source
of the finite colored generators. -/
noncomputable def buildingGeneratorPrefixProduct
    (P : BasePrime) (r : Rank) (k : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    BuildingCartwrightStegerLattice P r :=
  buildingGeneratorWordProduct P r ((List.ofFn u).take k)

/-- Congruence reduction commutes with products of the construction-owned
building generators. -/
@[simp] theorem buildingLatticeReduction_wordProduct
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r)) :
    buildingLatticeReduction P r level
        (buildingGeneratorWordProduct P r word) =
      indexGeneratorWordProduct P r level word := by
  induction word with
  | nil =>
      change buildingLatticeReduction P r level 1 = 1
      exact map_one (buildingLatticeReduction P r level)
  | cons u word ih =>
      change buildingLatticeReduction P r level
          (buildingLatticeGenerator P r u *
            buildingGeneratorWordProduct P r word) =
        bundledIndexGenerator P r level u *
          indexGeneratorWordProduct P r level word
      rw [map_mul, buildingLatticeReduction_generator, ih]
      rfl

/-- Congruence reduction sends each building prefix product to the matching
finite prefix product. -/
@[simp] theorem buildingLatticeReduction_prefixProduct
    (P : BasePrime) (r : Rank) (level k : Nat)
    (u : Fin r.matrixRank → ConstantProjectiveClass P r) :
    buildingLatticeReduction P r level
        (buildingGeneratorPrefixProduct P r k u) =
      indexGeneratorPrefixProduct P r level k u := by
  exact buildingLatticeReduction_wordProduct P r level ((List.ofFn u).take k)

/-- The construction-owned rank-length building relations.  In particular,
this finset does not acquire spurious short relations at special congruence
levels. -/
noncomputable def buildingRelationTupleFinset
    (P : BasePrime) (r : Rank) :
    Finset (Fin r.matrixRank → ConstantProjectiveClass P r) := by
  classical
  exact Finset.univ.filter fun u =>
    buildingGeneratorWordProduct P r (List.ofFn u) = 1

/-- Color `k` in the genuine building lattice: the length-`k` prefixes of
the fixed construction-owned apartment relations. -/
noncomputable def buildingColorGeneratorFinset
    (P : BasePrime) (r : Rank) (k : Nat) :
    Finset (BuildingCartwrightStegerLattice P r) := by
  classical
  exact (buildingRelationTupleFinset P r).image
    (buildingGeneratorPrefixProduct P r k)

private noncomputable def relationTupleOfWord
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r))
    (hlen : r.matrixRank = word.length) :
    Fin r.matrixRank → ConstantProjectiveClass P r :=
  fun i => word.get ⟨i, by rw [← hlen]; exact i.isLt⟩

private theorem ofFn_relationTupleOfWord
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r))
    (hlen : r.matrixRank = word.length) :
    List.ofFn (relationTupleOfWord P r word hlen) = word := by
  apply List.ext_get
  · simp [hlen]
  · intro n hn₁ hn₂
    rw [List.get_ofFn]
    apply congrArg word.get
    apply Fin.ext
    rfl

private theorem buildingGeneratorWordProduct_rotate_eq_one
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r))
    (hword : buildingGeneratorWordProduct P r word = 1)
    (n : Nat) :
    buildingGeneratorWordProduct P r (word.rotate n) = 1 := by
  change ((word.rotate n).map
    (buildingLatticeGenerator P r)).prod = 1
  rw [List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one hword n

private theorem buildingRelationTupleFinset_nonempty_of_buildingWord
    (P : BasePrime) (r : Rank)
    (word : List (ConstantProjectiveClass P r))
    (hlen : r.matrixRank = word.length)
    (hbuilding : (word.map (buildingLatticeGenerator P r)).prod = 1) :
    (buildingRelationTupleFinset P r).Nonempty := by
  classical
  let u := relationTupleOfWord P r word hlen
  have htuple : buildingGeneratorWordProduct P r (List.ofFn u) = 1 := by
    have hu : List.ofFn u = word := by
      exact ofFn_relationTupleOfWord P r word hlen
    rw [hu]
    exact hbuilding
  refine ⟨u, ?_⟩
  rw [buildingRelationTupleFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, htuple⟩

set_option maxHeartbeats 1000000 in
/-- The construction-owned relation set is genuinely nonempty.  Its witness
is the rank-three or rank-four apartment loop, transported through the actual
arithmetic order and congruence reduction. -/
theorem buildingRelationTupleFinset_nonempty
    (P : BasePrime) (r : Rank) :
    (buildingRelationTupleFinset P r).Nonempty := by
  cases r with
  | three =>
      obtain ⟨u0, u1, u2, hbuilding⟩ :=
        exists_rankThree_buildingGenerator_relation P
      apply buildingRelationTupleFinset_nonempty_of_buildingWord
        P .three [u0, u1, u2] rfl
      simpa only [List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, mul_assoc] using hbuilding
  | four =>
      obtain ⟨u0, u1, u2, u3, hbuilding⟩ :=
        exists_rankFour_buildingGenerator_relation P
      apply buildingRelationTupleFinset_nonempty_of_buildingWord
        P .four [u0, u1, u2, u3] rfl
      simpa only [List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, mul_assoc] using hbuilding

/-- A genuine building relation remains a rank-length relation in every
selected congruence image.  The converse is deliberately not used: a finite
quotient can contain additional short words equal to one. -/
theorem indexGeneratorTupleProduct_eq_one_of_mem_buildingRelationTupleFinset
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    indexGeneratorTupleProduct P r level u = 1 := by
  classical
  rw [buildingRelationTupleFinset, Finset.mem_filter] at hu
  exact indexGeneratorWordProduct_eq_one_of_building_relation
    P r level (List.ofFn u) hu.2

/-- Color `k` consists of the length-`k` prefixes of full
Cartwright--Steger relations, exactly as in the LSV construction. -/
noncomputable def indexColorGeneratorFinset
    (P : BasePrime) (r : Rank) (level k : Nat) :
    Finset (IndexFiniteGroup P r level) := by
  classical
  exact (buildingRelationTupleFinset P r).image
    (indexGeneratorPrefixProduct P r level k)

/-- A finite color is exactly the congruence image of the corresponding
level-independent building color.  Thus the finite complex has neither
omitted building colors nor congruence-only extra colors. -/
theorem image_buildingColorGeneratorFinset_reduction
    (P : BasePrime) (r : Rank) (level k : Nat) :
    (buildingColorGeneratorFinset P r k).image
        (buildingLatticeFiniteReduction P r level) =
      indexColorGeneratorFinset P r level k := by
  classical
  ext g
  simp only [buildingColorGeneratorFinset, indexColorGeneratorFinset,
    Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu,
      (buildingLatticeReduction_prefixProduct P r level k u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨buildingGeneratorPrefixProduct P r k u,
      ⟨u, hu, rfl⟩, ?_⟩
    exact buildingLatticeReduction_prefixProduct P r level k u

/-- Membership in a finite color has a witness in the fixed global building
relation system.  Hence congruence-only short relations cannot create new
colored generators or faces. -/
theorem mem_indexColorGeneratorFinset_iff_exists_buildingRelation
    (P : BasePrime) (r : Rank) (level k : Nat)
    (g : IndexFiniteGroup P r level) :
    g ∈ indexColorGeneratorFinset P r level k ↔
      ∃ u ∈ buildingRelationTupleFinset P r,
        indexGeneratorPrefixProduct P r level k u = g := by
  classical
  rw [indexColorGeneratorFinset, Finset.mem_image]

/-- Every prefix color has an actual generator, since it is the image of the
nonempty construction-owned apartment-relation set. -/
theorem indexColorGeneratorFinset_nonempty
    (P : BasePrime) (r : Rank) (level k : Nat) :
    (indexColorGeneratorFinset P r level k).Nonempty := by
  obtain ⟨u, hu⟩ := buildingRelationTupleFinset_nonempty P r
  refine ⟨indexGeneratorPrefixProduct P r level k u, ?_⟩
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

private theorem indexGeneratorWordTake_mem_color_of_relation
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (hlen : r.matrixRank = word.length)
    (hword : buildingGeneratorWordProduct P r word = 1)
    (k : Nat) :
    indexGeneratorWordProduct P r level (word.take k) ∈
      indexColorGeneratorFinset P r level k := by
  classical
  let u := relationTupleOfWord P r word hlen
  have huList : List.ofFn u = word :=
    ofFn_relationTupleOfWord P r word hlen
  have huRelation : u ∈ buildingRelationTupleFinset P r := by
    rw [buildingRelationTupleFinset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change buildingGeneratorWordProduct P r (List.ofFn u) = 1
    rw [huList]
    exact hword
  rw [indexColorGeneratorFinset]
  refine Finset.mem_image.mpr ⟨u, huRelation, ?_⟩
  change indexGeneratorPrefixProduct P r level k u =
    indexGeneratorWordProduct P r level (word.take k)
  rw [indexGeneratorPrefixProduct, huList]

/-- Every cyclic segment of a construction-owned relation appears in its
corresponding color.  Rotation is justified by the relation product itself,
not postulated as extra combinatorial input. -/
theorem indexGeneratorRotatedPrefix_mem_color
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r)
    (n k : Nat) :
    indexGeneratorWordProduct P r level
        (((List.ofFn u).rotate n).take k) ∈
      indexColorGeneratorFinset P r level k := by
  classical
  have hword : buildingGeneratorWordProduct P r (List.ofFn u) = 1 := by
    have hu' := hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu'
    exact hu'.2
  apply indexGeneratorWordTake_mem_color_of_relation P r level
    ((List.ofFn u).rotate n)
  · rw [List.length_rotate, List.length_ofFn]
  · exact buildingGeneratorWordProduct_rotate_eq_one
      P r (List.ofFn u) hword n

/-- The first entry of every full relation occurs as an actual color-one
generator. -/
theorem bundledIndexGenerator_mem_colorOne
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    bundledIndexGenerator P r level (u (rankZeroIndex r)) ∈
      indexColorGeneratorFinset P r level 1 := by
  rw [indexColorGeneratorFinset]
  exact Finset.mem_image.mpr
    ⟨u, hu, indexGeneratorPrefixProduct_one P r level u⟩

/-- All nonzero building colors.  In rank four this explicitly includes the
middle color `S₂`, which is not recovered by merely symmetrizing `S₁`. -/
noncomputable def indexColoredGeneratorFinset
    (P : BasePrime) (r : Rank) (level : Nat) :
    Finset (IndexFiniteGroup P r level) := by
  classical
  exact (Finset.Icc 1 (r.matrixRank - 1)).biUnion
    (indexColorGeneratorFinset P r level)

/-- All nonzero colors in the genuine building lattice, fixed independently
of the chosen congruence level. -/
noncomputable def buildingColoredGeneratorFinset
    (P : BasePrime) (r : Rank) :
    Finset (BuildingCartwrightStegerLattice P r) := by
  classical
  exact (Finset.Icc 1 (r.matrixRank - 1)).biUnion
    (buildingColorGeneratorFinset P r)

/-- The complete finite colored generator set is exactly the congruence
image of the complete building colored generator set. -/
theorem image_buildingColoredGeneratorFinset_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (buildingColoredGeneratorFinset P r).image
        (buildingLatticeFiniteReduction P r level) =
      indexColoredGeneratorFinset P r level := by
  classical
  rw [buildingColoredGeneratorFinset, indexColoredGeneratorFinset,
    Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro k hk
  exact image_buildingColorGeneratorFinset_reduction P r level k

/-- The building lattice acts on a finite congruence quotient by right
multiplication with the inverse of its reduction.  The inverse makes this a
left action and matches the undirected right Cayley-graph convention. -/
noncomputable instance buildingLatticeFiniteMulAction
    (P : BasePrime) (r : Rank) (level : Nat) :
    MulAction (BuildingCartwrightStegerLattice P r)
      (IndexFiniteGroup P r level) where
  smul g x := x * (buildingLatticeFiniteReduction P r level g)⁻¹
  one_smul x := by
    change x * (buildingLatticeFiniteReduction P r level 1)⁻¹ = x
    rw [map_one, inv_one, mul_one]
  mul_smul g h x := by
    change x * (buildingLatticeFiniteReduction P r level (g * h))⁻¹ =
      (x * (buildingLatticeFiniteReduction P r level h)⁻¹) *
        (buildingLatticeFiniteReduction P r level g)⁻¹
    rw [map_mul, mul_inv_rev, mul_assoc]

@[simp] theorem buildingLatticeFinite_smul
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : BuildingCartwrightStegerLattice P r)
    (x : IndexFiniteGroup P r level) :
    g • x = x * (buildingLatticeFiniteReduction P r level g)⁻¹ :=
  rfl

/-- The Schreier graph of the genuine building-lattice action is exactly
the finite colored Cayley graph.  This identifies all finite edges with the
congruence quotient of the fixed building adjacency relation. -/
theorem buildingSchreierGraph_eq_indexCayleyGraph
    (P : BasePrime) (r : Rank) (level : Nat) :
    CayleyClique.schreierGraph
        (X := IndexFiniteGroup P r level)
        (buildingColoredGeneratorFinset P r :
          Set (BuildingCartwrightStegerLattice P r)) =
      SimpleGraph.mulCayley
        (indexColoredGeneratorFinset P r level :
          Set (IndexFiniteGroup P r level)) := by
  classical
  apply SimpleGraph.ext
  funext x y
  apply propext
  rw [CayleyClique.schreierGraph_adj, SimpleGraph.mulCayley_adj]
  rw [← image_buildingColoredGeneratorFinset_reduction P r level]
  simp only [Finset.coe_image, Set.mem_image]
  constructor
  · rintro (⟨hxy, g, hg, hgy⟩ | ⟨hxy, g, hg, hgy⟩)
    · refine ⟨hxy, Or.inr ?_⟩
      refine ⟨g, hg, ?_⟩
      apply inv_injective
      calc
        (buildingLatticeFiniteReduction P r level g)⁻¹ = x⁻¹ * y := by
          exact eq_inv_mul_iff_mul_eq.mpr hgy
        _ = (y⁻¹ * x)⁻¹ := by simp
    · refine ⟨hxy, Or.inl ?_⟩
      refine ⟨g, hg, ?_⟩
      apply inv_injective
      calc
        (buildingLatticeFiniteReduction P r level g)⁻¹ = y⁻¹ * x := by
          exact eq_inv_mul_iff_mul_eq.mpr hgy
        _ = (x⁻¹ * y)⁻¹ := by simp
  · rintro ⟨hxy, h | h⟩
    · obtain ⟨g, hg, hred⟩ := h
      right
      refine ⟨hxy, g, hg, ?_⟩
      rw [buildingLatticeFinite_smul, hred]
      simp
    · obtain ⟨g, hg, hred⟩ := h
      left
      refine ⟨hxy, g, hg, ?_⟩
      rw [buildingLatticeFinite_smul, hred]
      simp

theorem indexColorGeneratorFinset_subset_colored
    (P : BasePrime) (r : Rank) (level k : Nat)
    (hk : k ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    indexColorGeneratorFinset P r level k ⊆
      indexColoredGeneratorFinset P r level := by
  intro g hg
  rw [indexColoredGeneratorFinset, Finset.mem_biUnion]
  exact ⟨k, hk, hg⟩

/-- The complete colored generating set is nonempty for both supported
ranks; in particular the quotient Cayley complex is not generated from an
empty relation family. -/
theorem indexColoredGeneratorFinset_nonempty
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexColoredGeneratorFinset P r level).Nonempty := by
  have hcolor : 1 ∈ Finset.Icc 1 (r.matrixRank - 1) := by
    cases r <;> decide
  obtain ⟨g, hg⟩ := indexColorGeneratorFinset_nonempty P r level 1
  refine ⟨g, ?_⟩
  rw [indexColoredGeneratorFinset, Finset.mem_biUnion]
  exact ⟨1, hcolor, hg⟩

/-- Every construction-owned full relation supplies a nonidentity member of
the complete colored generating set. -/
theorem bundledIndexGenerator_mem_colored
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    bundledIndexGenerator P r level (u (rankZeroIndex r)) ∈
      indexColoredGeneratorFinset P r level := by
  have hcolor : 1 ∈ Finset.Icc 1 (r.matrixRank - 1) := by
    cases r <;> decide
  rw [indexColoredGeneratorFinset, Finset.mem_biUnion]
  exact ⟨1, hcolor, bundledIndexGenerator_mem_colorOne P r level hu⟩

theorem card_buildingRelationTupleFinset_le
    (P : BasePrime) (r : Rank) :
    (buildingRelationTupleFinset P r).card ≤
      indexGeneratorBound P r ^ r.matrixRank := by
  classical
  calc
    (buildingRelationTupleFinset P r).card ≤
        (Finset.univ : Finset
          (Fin r.matrixRank → ConstantProjectiveClass P r)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = indexGeneratorBound P r ^ r.matrixRank := by
      simp [indexGeneratorBound]

theorem card_indexColorGeneratorFinset_le
    (P : BasePrime) (r : Rank) (level k : Nat) :
    (indexColorGeneratorFinset P r level k).card ≤
      indexGeneratorBound P r ^ r.matrixRank := by
  exact (Finset.card_image_le.trans
    (card_buildingRelationTupleFinset_le P r))

/-- A level-independent bound for the complete colored generating set. -/
noncomputable def indexColoredGeneratorBound
    (P : BasePrime) (r : Rank) : Nat :=
  r.matrixRank * indexGeneratorBound P r ^ r.matrixRank

theorem card_indexColoredGeneratorFinset_le
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexColoredGeneratorFinset P r level).card ≤
      indexColoredGeneratorBound P r := by
  let colors := Finset.Icc 1 (r.matrixRank - 1)
  have hcolors : colors.card ≤ r.matrixRank := by
    cases r <;> native_decide
  calc
    (indexColoredGeneratorFinset P r level).card ≤
        colors.card * indexGeneratorBound P r ^ r.matrixRank := by
      exact Finset.card_biUnion_le_card_mul colors
        (indexColorGeneratorFinset P r level)
        (indexGeneratorBound P r ^ r.matrixRank)
        (fun k _ => card_indexColorGeneratorFinset_le P r level k)
    _ ≤ r.matrixRank * indexGeneratorBound P r ^ r.matrixRank :=
      Nat.mul_le_mul_right _ hcolors
    _ = indexColoredGeneratorBound P r := rfl

/-- The finite Cayley clique complex at one hierarchy level. -/
noncomputable def lsvQuotientComplex
    (P : BasePrime) (r : Rank) (level : Nat) :=
  CayleyClique.cayleyCliqueComplex (indexColoredGeneratorFinset P r level :
    Set (IndexFiniteGroup P r level))

/-- The level-independent Cayley clique complex of the simply transitive
Cartwright--Steger building lattice, using the same construction-owned
colored apartment prefixes as every finite quotient. -/
noncomputable def cartwrightStegerBuildingCliqueComplex
    (P : BasePrime) (r : Rank) :=
  CayleyClique.cayleyCliqueComplex (buildingColoredGeneratorFinset P r :
    Set (BuildingCartwrightStegerLattice P r))

/-- The finite LSV clique complex is exactly the Schreier clique complex of
the congruence action of the genuine building lattice.  Consequently the
identification covers every clique face, not only vertices or generators. -/
theorem lsvQuotientComplex_eq_buildingSchreierCliqueComplex
    (P : BasePrime) (r : Rank) (level : Nat) :
    lsvQuotientComplex P r level =
      CayleyClique.schreierCliqueComplex
        (X := IndexFiniteGroup P r level)
        (buildingColoredGeneratorFinset P r :
          Set (BuildingCartwrightStegerLattice P r)) := by
  unfold lsvQuotientComplex CayleyClique.cayleyCliqueComplex
    CayleyClique.schreierCliqueComplex
  rw [buildingSchreierGraph_eq_indexCayleyGraph P r level]

/-- The rank-three / two-dimensional member of the hierarchy. -/
noncomputable def lsvTwoDimensionalQuotient
    (P : BasePrime) (level : Nat) :=
  lsvQuotientComplex P .three level

/-- The rank-four / three-dimensional member of the hierarchy. -/
noncomputable def lsvThreeDimensionalQuotient
    (P : BasePrime) (level : Nat) :=
  lsvQuotientComplex P .four level

private theorem exists_cayleyFace_containing
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (S : Finset Γ) (p : Nat)
    (σ : SimplicialChain.Face
      (CayleyClique.cayleyCliqueComplex (S : Set Γ)) p)
    (x : Γ) :
    ∃ τ : SimplicialChain.Face
        (CayleyClique.cayleyCliqueComplex (S : Set Γ)) p,
      x ∈ τ.vertices := by
  classical
  have hnonempty : σ.vertices.Nonempty :=
    ((CayleyClique.mem_cayleyCliqueComplex_iff
      (S : Set Γ) σ.vertices).mp σ.mem_complex).1
  obtain ⟨v, hv⟩ := hnonempty
  let a : Γ := x * v⁻¹
  let vertices := σ.vertices.map (Equiv.mulLeft a).toEmbedding
  have hvertices :
      vertices ∈ CayleyClique.cayleyCliqueComplex (S : Set Γ) := by
    exact (CayleyClique.leftMul_mem_cayleyCliqueComplex_iff
      (S : Set Γ) a σ.vertices).mpr σ.mem_complex
  have hcard : vertices.card = p := by
    change (σ.vertices.map (Equiv.mulLeft a).toEmbedding).card = p
    rw [Finset.card_map, σ.card_vertices]
  let τ : SimplicialChain.Face
      (CayleyClique.cayleyCliqueComplex (S : Set Γ)) p :=
    ⟨vertices, hvertices, hcard⟩
  refine ⟨τ, ?_⟩
  change x ∈ σ.vertices.map (Equiv.mulLeft a).toEmbedding
  rw [Finset.mem_map]
  refine ⟨v, hv, ?_⟩
  simp [a]

private def rankThreeIndexZero : Fin Rank.three.matrixRank :=
  ⟨0, by decide⟩

private def rankThreeIndexOne : Fin Rank.three.matrixRank :=
  ⟨1, by decide⟩

private def rankThreeIndexTwo : Fin Rank.three.matrixRank :=
  ⟨2, by decide⟩

private theorem list_ofFn_rankThree
    {A : Type*} (u : Fin Rank.three.matrixRank → A) :
    List.ofFn u =
      [u rankThreeIndexZero, u rankThreeIndexOne, u rankThreeIndexTwo] := by
  change List.ofFn (fun i : Fin 3 => u i) = _
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

private theorem rankThree_rotate_zero_take_one
    {A : Type*} (u : Fin Rank.three.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 1 = [u rankThreeIndexZero] := by
  rw [list_ofFn_rankThree]
  rfl

private theorem rankThree_rotate_one_take_one
    {A : Type*} (u : Fin Rank.three.matrixRank → A) :
    ((List.ofFn u).rotate 1).take 1 = [u rankThreeIndexOne] := by
  rw [list_ofFn_rankThree]
  rfl

private theorem rankThree_rotate_zero_take_two
    {A : Type*} (u : Fin Rank.three.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 2 =
      [u rankThreeIndexZero, u rankThreeIndexOne] := by
  rw [list_ofFn_rankThree]
  rfl

/-- The rank-three quotient contains an actual triangular chamber obtained
from the three cyclically colored prefixes of a proved relation. -/
theorem lsvTwoDimensionalQuotient_triangleFaces_nonempty
    (P : BasePrime) (level : Nat) :
    Nonempty
      (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by
  classical
  obtain ⟨u, hu⟩ := buildingRelationTupleFinset_nonempty P .three
  let a : IndexFiniteGroup P .three level :=
    bundledIndexGenerator P .three level (u rankThreeIndexZero)
  let b : IndexFiniteGroup P .three level :=
    bundledIndexGenerator P .three level (u rankThreeIndexOne)
  let c : IndexFiniteGroup P .three level :=
    bundledIndexGenerator P .three level (u rankThreeIndexTwo)
  let ab : IndexFiniteGroup P .three level := a * b
  have hrelation : ab * c = 1 := by
    have hu' := hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu'
    have huProduct := indexGeneratorWordProduct_eq_one_of_building_relation
      P .three level (List.ofFn u) hu'.2
    rw [list_ofFn_rankThree] at huProduct
    change (a * b) * c = 1
    change a * (b * (c * 1)) = 1 at huProduct
    simpa only [mul_one, mul_assoc] using huProduct
  have ha_ne : a ≠ 1 :=
    bundledIndexGenerator_ne_one P .three level (u rankThreeIndexZero)
  have hb_ne : b ≠ 1 :=
    bundledIndexGenerator_ne_one P .three level (u rankThreeIndexOne)
  have hc_ne : c ≠ 1 :=
    bundledIndexGenerator_ne_one P .three level (u rankThreeIndexTwo)
  have hab_ne : ab ≠ 1 := by
    intro hab
    apply hc_ne
    rw [hab, one_mul] at hrelation
    exact hrelation
  have haColor : a ∈ indexColorGeneratorFinset P .three level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .three level hu 0 1
    rw [rankThree_rotate_zero_take_one] at h
    simpa [indexGeneratorWordProduct, a] using h
  have hbColor : b ∈ indexColorGeneratorFinset P .three level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .three level hu 1 1
    rw [rankThree_rotate_one_take_one] at h
    simpa [indexGeneratorWordProduct, b] using h
  have habColor : ab ∈ indexColorGeneratorFinset P .three level 2 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .three level hu 0 2
    rw [rankThree_rotate_zero_take_two] at h
    simpa [indexGeneratorWordProduct, a, b, ab] using h
  have h1 : 1 ∈ Finset.Icc 1 (Rank.three.matrixRank - 1) := by decide
  have h2 : 2 ∈ Finset.Icc 1 (Rank.three.matrixRank - 1) := by decide
  have haMem := indexColorGeneratorFinset_subset_colored
    P .three level 1 h1 haColor
  have hbMem := indexColorGeneratorFinset_subset_colored
    P .three level 1 h1 hbColor
  have habMem := indexColorGeneratorFinset_subset_colored
    P .three level 2 h2 habColor
  let G := SimpleGraph.mulCayley
    (indexColoredGeneratorFinset P .three level :
      Set (IndexFiniteGroup P .three level))
  have hadj_one_a : G.Adj 1 a := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨ha_ne.symm, Or.inl (by simpa using haMem)⟩
  have hadj_one_ab : G.Adj 1 ab := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨hab_ne.symm, Or.inl (by simpa using habMem)⟩
  have ha_ab_ne : a ≠ ab := by
    exact ((mul_ne_left : a * b ≠ a ↔ b ≠ 1).mpr hb_ne).symm
  have hadj_a_ab : G.Adj a ab := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨ha_ab_ne, Or.inl ?_⟩
    change a⁻¹ * (a * b) ∈
      (indexColoredGeneratorFinset P .three level :
        Set (IndexFiniteGroup P .three level))
    rw [inv_mul_cancel_left]
    exact hbMem
  refine ⟨⟨{1, a, ab}, ?_, ?_⟩⟩
  · change {1, a, ab} ∈ CayleyClique.cayleyCliqueComplex
      (indexColoredGeneratorFinset P .three level :
        Set (IndexFiniteGroup P .three level))
    exact CayleyClique.triple_mem_cliqueComplex G
      hadj_one_a hadj_one_ab hadj_a_ab
  · exact Finset.card_eq_three.mpr
      ⟨1, a, ab, ha_ne.symm, hab_ne.symm, ha_ab_ne, rfl⟩

/-- Every vertex of the rank-three quotient lies in a triangular chamber,
by translating the construction-owned chamber with the Cayley action. -/
theorem exists_triangleFace_containing_vertex
    (P : BasePrime) (level : Nat)
    (x : IndexFiniteGroup P .three level) :
    ∃ σ : SimplicialChain.Face
        (lsvTwoDimensionalQuotient P level) 3,
      x ∈ σ.vertices := by
  let σ := Classical.choice
    (lsvTwoDimensionalQuotient_triangleFaces_nonempty P level)
  exact exists_cayleyFace_containing
    (indexColoredGeneratorFinset P .three level) 3 σ x

private def rankFourIndexZero : Fin Rank.four.matrixRank :=
  ⟨0, by decide⟩

private def rankFourIndexOne : Fin Rank.four.matrixRank :=
  ⟨1, by decide⟩

private def rankFourIndexTwo : Fin Rank.four.matrixRank :=
  ⟨2, by decide⟩

private def rankFourIndexThree : Fin Rank.four.matrixRank :=
  ⟨3, by decide⟩

private theorem list_ofFn_rankFour
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    List.ofFn u = [u rankFourIndexZero, u rankFourIndexOne,
      u rankFourIndexTwo, u rankFourIndexThree] := by
  change List.ofFn (fun i : Fin 4 => u i) = _
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

private theorem rankFour_rotate_zero_take_one
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 1 = [u rankFourIndexZero] := by
  rw [list_ofFn_rankFour]
  rfl

private theorem rankFour_rotate_one_take_one
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 1).take 1 = [u rankFourIndexOne] := by
  rw [list_ofFn_rankFour]
  rfl

private theorem rankFour_rotate_two_take_one
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 2).take 1 = [u rankFourIndexTwo] := by
  rw [list_ofFn_rankFour]
  rfl

private theorem rankFour_rotate_zero_take_two
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 2 =
      [u rankFourIndexZero, u rankFourIndexOne] := by
  rw [list_ofFn_rankFour]
  rfl

private theorem rankFour_rotate_one_take_two
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 1).take 2 =
      [u rankFourIndexOne, u rankFourIndexTwo] := by
  rw [list_ofFn_rankFour]
  rfl

private theorem rankFour_rotate_zero_take_three
    {A : Type*} (u : Fin Rank.four.matrixRank → A) :
    ((List.ofFn u).rotate 0).take 3 =
      [u rankFourIndexZero, u rankFourIndexOne, u rankFourIndexTwo] := by
  rw [list_ofFn_rankFour]
  rfl

/-- The rank-four quotient contains an actual tetrahedral chamber.  Its
middle-color edges remain nondegenerate because the selected determinant
color has exact order four. -/
theorem lsvThreeDimensionalQuotient_tetrahedronFaces_nonempty
    (P : BasePrime) (level : Nat) :
    Nonempty
      (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) := by
  classical
  obtain ⟨u, hu⟩ := buildingRelationTupleFinset_nonempty P .four
  let a : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexZero)
  let b : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexOne)
  let c : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexTwo)
  let d : IndexFiniteGroup P .four level :=
    bundledIndexGenerator P .four level (u rankFourIndexThree)
  let ab : IndexFiniteGroup P .four level := a * b
  let bc : IndexFiniteGroup P .four level := b * c
  let abc : IndexFiniteGroup P .four level := ab * c
  have hrelation : abc * d = 1 := by
    have hu' := hu
    rw [buildingRelationTupleFinset, Finset.mem_filter] at hu'
    have huProduct := indexGeneratorWordProduct_eq_one_of_building_relation
      P .four level (List.ofFn u) hu'.2
    rw [list_ofFn_rankFour] at huProduct
    change ((a * b) * c) * d = 1
    change a * (b * (c * (d * 1))) = 1 at huProduct
    simpa only [mul_one, mul_assoc] using huProduct
  have ha_ne : a ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexZero)
  have hb_ne : b ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexOne)
  have hc_ne : c ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexTwo)
  have hd_ne : d ≠ 1 :=
    bundledIndexGenerator_ne_one P .four level (u rankFourIndexThree)
  have hab_ne : ab ≠ 1 := by
    exact rankFour_bundledIndexGenerator_mul_ne_one P level
      (u rankFourIndexZero) (u rankFourIndexOne)
  have hbc_ne : bc ≠ 1 := by
    exact rankFour_bundledIndexGenerator_mul_ne_one P level
      (u rankFourIndexOne) (u rankFourIndexTwo)
  have habc_ne : abc ≠ 1 := by
    intro habc
    apply hd_ne
    rw [habc, one_mul] at hrelation
    exact hrelation
  have haColor : a ∈ indexColorGeneratorFinset P .four level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 0 1
    rw [rankFour_rotate_zero_take_one] at h
    simpa [indexGeneratorWordProduct, a] using h
  have hbColor : b ∈ indexColorGeneratorFinset P .four level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 1 1
    rw [rankFour_rotate_one_take_one] at h
    simpa [indexGeneratorWordProduct, b] using h
  have hcColor : c ∈ indexColorGeneratorFinset P .four level 1 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 2 1
    rw [rankFour_rotate_two_take_one] at h
    simpa [indexGeneratorWordProduct, c] using h
  have habColor : ab ∈ indexColorGeneratorFinset P .four level 2 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 0 2
    rw [rankFour_rotate_zero_take_two] at h
    simpa [indexGeneratorWordProduct, a, b, ab] using h
  have hbcColor : bc ∈ indexColorGeneratorFinset P .four level 2 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 1 2
    rw [rankFour_rotate_one_take_two] at h
    simpa [indexGeneratorWordProduct, b, c, bc] using h
  have habcColor : abc ∈ indexColorGeneratorFinset P .four level 3 := by
    have h := indexGeneratorRotatedPrefix_mem_color P .four level hu 0 3
    rw [rankFour_rotate_zero_take_three] at h
    simpa [indexGeneratorWordProduct, a, b, c, ab, abc, mul_assoc] using h
  have h1 : 1 ∈ Finset.Icc 1 (Rank.four.matrixRank - 1) := by decide
  have h2 : 2 ∈ Finset.Icc 1 (Rank.four.matrixRank - 1) := by decide
  have h3 : 3 ∈ Finset.Icc 1 (Rank.four.matrixRank - 1) := by decide
  have haMem := indexColorGeneratorFinset_subset_colored
    P .four level 1 h1 haColor
  have hbMem := indexColorGeneratorFinset_subset_colored
    P .four level 1 h1 hbColor
  have hcMem := indexColorGeneratorFinset_subset_colored
    P .four level 1 h1 hcColor
  have habMem := indexColorGeneratorFinset_subset_colored
    P .four level 2 h2 habColor
  have hbcMem := indexColorGeneratorFinset_subset_colored
    P .four level 2 h2 hbcColor
  have habcMem := indexColorGeneratorFinset_subset_colored
    P .four level 3 h3 habcColor
  let G := SimpleGraph.mulCayley
    (indexColoredGeneratorFinset P .four level :
      Set (IndexFiniteGroup P .four level))
  have hadj_one_a : G.Adj 1 a := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨ha_ne.symm, Or.inl (by simpa using haMem)⟩
  have hadj_one_ab : G.Adj 1 ab := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨hab_ne.symm, Or.inl (by simpa using habMem)⟩
  have hadj_one_abc : G.Adj 1 abc := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨habc_ne.symm, Or.inl (by simpa using habcMem)⟩
  have ha_ab_ne : a ≠ ab :=
    ((mul_ne_left : a * b ≠ a ↔ b ≠ 1).mpr hb_ne).symm
  have ha_abc_ne : a ≠ abc := by
    have hmul : a * bc ≠ a :=
      (mul_ne_left : a * bc ≠ a ↔ bc ≠ 1).mpr hbc_ne
    have heq : abc = a * bc := by simp [abc, ab, bc, mul_assoc]
    rw [heq]
    exact hmul.symm
  have hab_abc_ne : ab ≠ abc :=
    ((mul_ne_left : ab * c ≠ ab ↔ c ≠ 1).mpr hc_ne).symm
  have hadj_a_ab : G.Adj a ab := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨ha_ab_ne, Or.inl ?_⟩
    change a⁻¹ * (a * b) ∈
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    rw [inv_mul_cancel_left]
    exact hbMem
  have hadj_a_abc : G.Adj a abc := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨ha_abc_ne, Or.inl ?_⟩
    change a⁻¹ * ((a * b) * c) ∈
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    rw [← mul_assoc, inv_mul_cancel_left]
    exact hbcMem
  have hadj_ab_abc : G.Adj ab abc := by
    rw [SimpleGraph.mulCayley_adj]
    refine ⟨hab_abc_ne, Or.inl ?_⟩
    change ab⁻¹ * (ab * c) ∈
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    rw [inv_mul_cancel_left]
    exact hcMem
  refine ⟨⟨{1, a, ab, abc}, ?_, ?_⟩⟩
  · change {1, a, ab, abc} ∈ CayleyClique.cayleyCliqueComplex
      (indexColoredGeneratorFinset P .four level :
        Set (IndexFiniteGroup P .four level))
    exact CayleyClique.quadruple_mem_cliqueComplex G
      hadj_one_a hadj_one_ab hadj_one_abc
      hadj_a_ab hadj_a_abc hadj_ab_abc
  · exact Finset.card_eq_four.mpr
      ⟨1, a, ab, abc, ha_ne.symm, hab_ne.symm, habc_ne.symm,
        ha_ab_ne, ha_abc_ne, hab_abc_ne, rfl⟩

/-- Every vertex of the rank-four quotient lies in a tetrahedral chamber,
again by the genuine Cayley left action. -/
theorem exists_tetrahedronFace_containing_vertex
    (P : BasePrime) (level : Nat)
    (x : IndexFiniteGroup P .four level) :
    ∃ σ : SimplicialChain.Face
        (lsvThreeDimensionalQuotient P level) 4,
      x ∈ σ.vertices := by
  let σ := Classical.choice
    (lsvThreeDimensionalQuotient_tetrahedronFaces_nonempty P level)
  exact exists_cayleyFace_containing
    (indexColoredGeneratorFinset P .four level) 4 σ x

/-- Each selected finite quotient contains a genuine edge.  The witness is
the identity together with the first vertex step of a constructed apartment
relation; nondegeneracy follows from the finite generator theorem, not from
an assumed quotient-injectivity radius. -/
theorem lsvQuotientComplex_edgeFaces_nonempty
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nonempty (SimplicialChain.Face (lsvQuotientComplex P r level) 2) := by
  classical
  obtain ⟨u, hu⟩ := buildingRelationTupleFinset_nonempty P r
  let g : IndexFiniteGroup P r level :=
    bundledIndexGenerator P r level (u (rankZeroIndex r))
  have hg_ne : g ≠ 1 := by
    exact bundledIndexGenerator_ne_one P r level (u (rankZeroIndex r))
  have hg_mem : g ∈ indexColoredGeneratorFinset P r level := by
    exact bundledIndexGenerator_mem_colored P r level hu
  have hadj :
      (SimpleGraph.mulCayley
        (indexColoredGeneratorFinset P r level :
          Set (IndexFiniteGroup P r level))).Adj 1 g := by
    rw [SimpleGraph.mulCayley_adj]
    exact ⟨hg_ne.symm, Or.inl (by simpa using hg_mem)⟩
  refine ⟨⟨{1, g}, ?_, ?_⟩⟩
  · change {1, g} ∈ CayleyClique.cayleyCliqueComplex
      (indexColoredGeneratorFinset P r level :
        Set (IndexFiniteGroup P r level))
    rw [CayleyClique.mem_cayleyCliqueComplex_iff]
    refine ⟨by simp, ?_⟩
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (SimpleGraph.isClique_pair.mpr (fun _ => hadj))
  · exact Finset.card_pair hg_ne.symm

theorem rankThree_complexDimension : Rank.three.complexDimension = 2 := rfl

theorem rankFour_complexDimension : Rank.four.complexDimension = 3 := rfl

section VertexFaces

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)

/-- The unique vertex of a one-vertex simplicial face. -/
private noncomputable def faceVertex
    (σ : SimplicialChain.Face K 1) : V :=
  Classical.choose (Finset.card_eq_one.mp σ.card_vertices)

omit [Fintype V] [DecidableEq V] in
private theorem faceVertex_spec
    (σ : SimplicialChain.Face K 1) :
    σ.vertices = {faceVertex K σ} :=
  Classical.choose_spec (Finset.card_eq_one.mp σ.card_vertices)

/-- One-vertex faces are exactly the vertices of the underlying complex. -/
noncomputable def vertexFaceEquiv :
    SimplicialChain.Face K 1 ≃ V where
  toFun := faceVertex K
  invFun x := ⟨{x}, K.singleton_mem x, Finset.card_singleton x⟩
  left_inv σ := by
    apply faceVertices_injective
    simpa using (faceVertex_spec K σ).symm
  right_inv x := by
    have h := faceVertex_spec K
      (⟨{x}, K.singleton_mem x, Finset.card_singleton x⟩ :
        SimplicialChain.Face K 1)
    simpa using h.symm

omit [DecidableEq V] in
theorem card_vertexFaces :
    Fintype.card (SimplicialChain.Face K 1) = Fintype.card V :=
  Fintype.card_congr (vertexFaceEquiv K)

variable {K}

private noncomputable def chosenFaceContaining
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices)
    (x : V) : SimplicialChain.Face K p :=
  Classical.choose (hcover x)

omit [Fintype V] [DecidableEq V] in
private theorem mem_chosenFaceContaining
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices)
    (x : V) :
    x ∈ (chosenFaceContaining p hcover x).vertices :=
  Classical.choose_spec (hcover x)

private noncomputable def vertexToFacePosition
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices) :
    V → (Σ σ : SimplicialChain.Face K p, σ.vertices) :=
  fun x => ⟨chosenFaceContaining p hcover x,
    ⟨x, mem_chosenFaceContaining p hcover x⟩⟩

private theorem vertexToFacePosition_injective
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices) :
    Function.Injective (vertexToFacePosition p hcover) := by
  intro x y hxy
  exact congrArg (fun z => z.2.1) hxy

/-- If every vertex lies in a `p`-vertex face, double counting chosen vertex
incidences bounds the vertex count by `p` times the number of such faces. -/
theorem card_vertices_le_faceSize_mul_card_faces
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices) :
    Fintype.card V ≤
      p * Fintype.card (SimplicialChain.Face K p) := by
  have hle := Fintype.card_le_of_injective
    (vertexToFacePosition p hcover)
    (vertexToFacePosition_injective p hcover)
  rw [Fintype.card_sigma] at hle
  calc
    Fintype.card V ≤
        ∑ σ : SimplicialChain.Face K p,
          Fintype.card σ.vertices := hle
    _ = ∑ _σ : SimplicialChain.Face K p, p := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Fintype.card_coe, σ.card_vertices]
    _ = p * Fintype.card (SimplicialChain.Face K p) := by
      simp [Nat.mul_comm]

end VertexFaces

/-- Exact zero-dimensional face count of each finite LSV quotient. -/
theorem card_lsvQuotientComplex_vertexFaces
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) 1) =
      Fintype.card (IndexFiniteGroup P r level) :=
  card_vertexFaces (lsvQuotientComplex P r level)

/-- Exact zero-face count in terms of the genuine lattice congruence
quotient, rather than only its finite image presentation. -/
theorem card_lsvQuotientComplex_vertexFaces_eq_congruenceQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) 1) =
      Nat.card
        (OrderSplitCartwrightStegerLattice P r ⧸
          OrderSplitCartwrightStegerCongruenceSubgroup P r level) := by
  rw [card_lsvQuotientComplex_vertexFaces]
  simpa only [Nat.card_eq_fintype_card] using
    (Nat.card_congr (lsvCongruenceVertexEquiv P r level)).symm

/-- Exact zero-face count in terms of the congruence quotient of the
simply transitive building lattice itself. -/
theorem card_lsvQuotientComplex_vertexFaces_eq_buildingQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) 1) =
      Nat.card
        (BuildingCartwrightStegerLattice P r ⧸
          BuildingCartwrightStegerCongruenceSubgroup P r level) := by
  rw [card_lsvQuotientComplex_vertexFaces]
  simpa only [Nat.card_eq_fintype_card] using
    (Nat.card_congr (lsvBuildingCongruenceVertexEquiv P r level)).symm

/-- The rank-three triangle count controls the full vertex count. -/
theorem card_rankThree_vertices_le_three_mul_triangleFaces
    (P : BasePrime) (level : Nat) :
    Fintype.card (IndexFiniteGroup P .three level) ≤
      3 * Fintype.card
        (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by
  exact card_vertices_le_faceSize_mul_card_faces 3
    (exists_triangleFace_containing_vertex P level)

/-- The rank-four tetrahedron count controls the full vertex count. -/
theorem card_rankFour_vertices_le_four_mul_tetrahedronFaces
    (P : BasePrime) (level : Nat) :
    Fintype.card (IndexFiniteGroup P .four level) ≤
      4 * Fintype.card
        (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) := by
  exact card_vertices_le_faceSize_mul_card_faces 4
    (exists_tetrahedronFace_containing_vertex P level)

section CayleyFaceIncidence

universe u

variable {Γ : Type u} [Group Γ] [Fintype Γ] [DecidableEq Γ]

/-- Left translation identifies the `p`-vertex faces through any Cayley
vertex with the `p`-vertex faces through the identity.  This is the local
homogeneity input for the exact face-incidence count below. -/
private noncomputable def cayleyIncidentFaceEquiv
    (S : Set Γ) (p : Nat) (x : Γ) :
    {σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p //
      x ∈ σ.vertices} ≃
    {σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p //
      1 ∈ σ.vertices} where
  toFun σ := ⟨{
    vertices := σ.1.vertices.map (Equiv.mulLeft x⁻¹).toEmbedding
    mem_complex :=
      (CayleyClique.leftMul_mem_cayleyCliqueComplex_iff
        S x⁻¹ σ.1.vertices).2 σ.1.mem_complex
    card_vertices := by
      rw [Finset.card_map, σ.1.card_vertices] }, by
        simpa using σ.2⟩
  invFun σ := ⟨{
    vertices := σ.1.vertices.map (Equiv.mulLeft x).toEmbedding
    mem_complex :=
      (CayleyClique.leftMul_mem_cayleyCliqueComplex_iff
        S x σ.1.vertices).2 σ.1.mem_complex
    card_vertices := by
      rw [Finset.card_map, σ.1.card_vertices] }, by
        simpa using σ.2⟩
  left_inv σ := by
    apply Subtype.ext
    apply faceVertices_injective
    ext y
    simp
  right_inv σ := by
    apply Subtype.ext
    apply faceVertices_injective
    ext y
    simp

/-- Reindex the set of all face--vertex incidences by putting the vertex
first. -/
private def faceVertexIncidenceEquiv
    (S : Set Γ) (p : Nat) :
    (Σ σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p,
      σ.vertices) ≃
    (Σ x : Γ,
      {σ : SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p //
        x ∈ σ.vertices}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact face-incidence formula for a finite Cayley clique complex.  The
rightmost factor is computed at the identity, and left translation proves
that the same number of faces is incident to every vertex. -/
theorem cayley_face_incidence_formula
    (S : Set Γ) (p : Nat) :
    p * Fintype.card
        (SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p) =
      Fintype.card Γ *
        Fintype.card
          {σ : SimplicialChain.Face
              (CayleyClique.cayleyCliqueComplex S) p //
            1 ∈ σ.vertices} := by
  classical
  have hincidence := Fintype.card_congr (faceVertexIncidenceEquiv S p)
  rw [Fintype.card_sigma, Fintype.card_sigma] at hincidence
  calc
    p * Fintype.card
        (SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p) =
        ∑ _σ : SimplicialChain.Face
            (CayleyClique.cayleyCliqueComplex S) p, p := by
          simp [Nat.mul_comm]
    _ = ∑ σ : SimplicialChain.Face
            (CayleyClique.cayleyCliqueComplex S) p,
          Fintype.card σ.vertices := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Fintype.card_coe, σ.card_vertices]
    _ = ∑ x : Γ,
          Fintype.card
            {σ : SimplicialChain.Face
                (CayleyClique.cayleyCliqueComplex S) p //
              x ∈ σ.vertices} := hincidence
    _ = ∑ _x : Γ,
          Fintype.card
            {σ : SimplicialChain.Face
                (CayleyClique.cayleyCliqueComplex S) p //
              1 ∈ σ.vertices} := by
          apply Finset.sum_congr rfl
          intro x _
          exact Fintype.card_congr (cayleyIncidentFaceEquiv S p x)
    _ = Fintype.card Γ *
          Fintype.card
            {σ : SimplicialChain.Face
                (CayleyClique.cayleyCliqueComplex S) p //
              1 ∈ σ.vertices} := by simp

end CayleyFaceIncidence

/-- Exact face-incidence formula for every selected finite LSV quotient,
with the global vertex factor written as the genuine lattice congruence
quotient.  This covers every face degree, not only the top-dimensional
chambers. -/
theorem card_lsvQuotientComplex_faces_incidence_formula
    (P : BasePrime) (r : Rank) (level p : Nat) :
    p * Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) p) =
      Nat.card
          (OrderSplitCartwrightStegerLattice P r ⧸
            OrderSplitCartwrightStegerCongruenceSubgroup P r level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvQuotientComplex P r level) p //
            1 ∈ σ.vertices} := by
  rw [natCard_orderSplitLatticeQuotient P r level]
  change p * Fintype.card
      (SimplicialChain.Face
        (CayleyClique.cayleyCliqueComplex
          (indexColoredGeneratorFinset P r level :
            Set (IndexFiniteGroup P r level))) p) =
    Nat.card (IndexFiniteGroup P r level) *
      Fintype.card
        {σ : SimplicialChain.Face
            (CayleyClique.cayleyCliqueComplex
              (indexColoredGeneratorFinset P r level :
                Set (IndexFiniteGroup P r level))) p //
          1 ∈ σ.vertices}
  rw [Nat.card_eq_fintype_card]
  exact cayley_face_incidence_formula
    (indexColoredGeneratorFinset P r level :
      Set (IndexFiniteGroup P r level)) p

/-- Exact rank-three top-face formula, derived from the actual finite
Cartwright--Steger Cayley complex. -/
theorem rankThree_triangle_face_incidence_formula
    (P : BasePrime) (level : Nat) :
    3 * Fintype.card
        (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) =
      Fintype.card (IndexFiniteGroup P .three level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvTwoDimensionalQuotient P level) 3 //
            1 ∈ σ.vertices} := by
  exact cayley_face_incidence_formula
    (indexColoredGeneratorFinset P .three level :
      Set (IndexFiniteGroup P .three level)) 3

/-- Exact rank-four top-face formula, derived from the actual finite
Cartwright--Steger Cayley complex. -/
theorem rankFour_tetrahedron_face_incidence_formula
    (P : BasePrime) (level : Nat) :
    4 * Fintype.card
        (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) =
      Fintype.card (IndexFiniteGroup P .four level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvThreeDimensionalQuotient P level) 4 //
            1 ∈ σ.vertices} := by
  exact cayley_face_incidence_formula
    (indexColoredGeneratorFinset P .four level :
      Set (IndexFiniteGroup P .four level)) 4

section CofaceBounds

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : AbstractSimplicialComplex V} {p : Nat}

private theorem coface_exists_addedVertex
    (σ : SimplicialChain.Face K p)
    (τ : {τ : SimplicialChain.Face K (p + 1) //
      τ ∈ SimplicialChain.cofaces K p σ}) :
    ∃ x ∉ σ.vertices, insert x σ.vertices = τ.1.vertices := by
  apply Finset.exists_eq_insert_iff.mpr
  constructor
  · have hss : σ.vertices ⊂ τ.1.vertices := by
      have hmem := τ.2
      change τ.1 ∈ Finset.univ.filter
        (fun υ : SimplicialChain.Face K (p + 1) =>
          σ.vertices ⊂ υ.vertices) at hmem
      exact (Finset.mem_filter.mp hmem).2
    exact hss.1
  · rw [σ.card_vertices, τ.1.card_vertices]

/-- The unique vertex added by a codimension-one coface. -/
private noncomputable def cofaceAddedVertex
    (σ : SimplicialChain.Face K p)
    (τ : {τ : SimplicialChain.Face K (p + 1) //
      τ ∈ SimplicialChain.cofaces K p σ}) : V :=
  Classical.choose (coface_exists_addedVertex σ τ)

private theorem cofaceAddedVertex_notMem
    (σ : SimplicialChain.Face K p)
    (τ : {τ : SimplicialChain.Face K (p + 1) //
      τ ∈ SimplicialChain.cofaces K p σ}) :
    cofaceAddedVertex σ τ ∉ σ.vertices :=
  (Classical.choose_spec (coface_exists_addedVertex σ τ)).1

private theorem insert_cofaceAddedVertex
    (σ : SimplicialChain.Face K p)
    (τ : {τ : SimplicialChain.Face K (p + 1) //
      τ ∈ SimplicialChain.cofaces K p σ}) :
    insert (cofaceAddedVertex σ τ) σ.vertices = τ.1.vertices :=
  (Classical.choose_spec (coface_exists_addedVertex σ τ)).2

/-- Codimension-one cofaces inject into the vertices which extend a face.
This bridge derives the coface count from the actual simplicial complex; it
does not accept a locality table as data. -/
theorem card_cofaces_le_extensionVertices
    (σ : SimplicialChain.Face K p) :
    (SimplicialChain.cofaces K p σ).card ≤
      (CayleyClique.extensionVertices K σ.vertices).card := by
  classical
  let added :
      {τ : SimplicialChain.Face K (p + 1) //
        τ ∈ SimplicialChain.cofaces K p σ} →
        {x : V // x ∈ CayleyClique.extensionVertices K σ.vertices} :=
    fun τ => ⟨cofaceAddedVertex σ τ,
      (CayleyClique.mem_extensionVertices_iff K σ.vertices _).mpr
        ⟨cofaceAddedVertex_notMem σ τ, by
          rw [insert_cofaceAddedVertex σ τ]
          exact τ.1.mem_complex⟩⟩
  have hInjective : Function.Injective added := by
    intro τ υ h
    apply Subtype.ext
    have hVertices : τ.1.vertices = υ.1.vertices := by
      rw [← insert_cofaceAddedVertex σ τ,
        ← insert_cofaceAddedVertex σ υ]
      exact congrArg (fun x => insert x σ.vertices)
        (congrArg Subtype.val h)
    exact faceVertices_injective hVertices
  simpa only [Fintype.card_coe] using
    (Finset.card_le_card_of_injective hInjective)

end CofaceBounds

/-- Every codimension-one coface count is bounded uniformly in the hierarchy
level.  The bound is computed from the constant extension field, not supplied
as an assumption. -/
theorem card_lsvQuotientComplex_cofaces_le
    (P : BasePrime) (r : Rank) (level p : Nat)
    (σ : SimplicialChain.Face (lsvQuotientComplex P r level) p) :
    (SimplicialChain.cofaces (lsvQuotientComplex P r level) p σ).card ≤
      2 * indexColoredGeneratorBound P r := by
  let S := indexColoredGeneratorFinset P r level
  have hNonempty : σ.vertices.Nonempty := by
    exact ((CayleyClique.mem_cayleyCliqueComplex_iff
      (S : Set (IndexFiniteGroup P r level)) σ.vertices).mp
        (by simpa [lsvQuotientComplex, S] using σ.mem_complex)).1
  obtain ⟨x, hx⟩ := hNonempty
  calc
    (SimplicialChain.cofaces (lsvQuotientComplex P r level) p σ).card ≤
        (CayleyClique.extensionVertices
          (lsvQuotientComplex P r level) σ.vertices).card :=
      card_cofaces_le_extensionVertices σ
    _ ≤ 2 * S.card := by
      simpa [lsvQuotientComplex, S] using
        (CayleyClique.card_cayley_extensionVertices_le S σ.vertices hx)
    _ ≤ 2 * indexColoredGeneratorBound P r := by
      exact Nat.mul_le_mul_left 2 (by
        simpa [S] using
          card_indexColoredGeneratorFinset_le P r level)

/-- Binary simplicial chain complex extracted from an actual finite LSV
Cayley clique complex. -/
noncomputable def lsvBinaryChainAt
    (P : BasePrime) (r : Rank) (level p : Nat) :=
  SimplicialChain.chainComplexAt (lsvQuotientComplex P r level) p

noncomputable def lsvTwoDimensionalBinaryChain
    (P : BasePrime) (level : Nat) :=
  SimplicialChain.chainComplexAt (lsvTwoDimensionalQuotient P level) 1

noncomputable def lsvThreeDimensionalBinaryChain
    (P : BasePrime) (level : Nat) :=
  SimplicialChain.chainComplexAt (lsvThreeDimensionalQuotient P level) 1

/-- The binary chain complex has a locality bound independent of the quotient
level.  Only `P`, `r`, and the selected chain degree occur in the bound. -/
theorem lsvBinaryChain_boundedLocality
    (P : BasePrime) (r : Rank) (level p : Nat) (hp : 1 ≤ p) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (lsvBinaryChainAt P r level p)).localityProfile
      (max (max (2 * indexColoredGeneratorBound P r) (p + 2))
        (p + 1 + 2 * indexColoredGeneratorBound P r)) := by
  apply SimplicialChain.boundedLocality_of_coface_bounds
    (lsvQuotientComplex P r level) p
      (2 * indexColoredGeneratorBound P r) hp
  · exact fun σ => card_lsvQuotientComplex_cofaces_le P r level p σ
  · exact fun τ => card_lsvQuotientComplex_cofaces_le P r level (p + 1) τ

theorem lsvBinaryChain_stabilizer_isSourceValidBinary
    (P : BasePrime) (r : Rank) (level p : Nat) :
    ((lsvBinaryChainAt P r level p).binaryCSSCode).stabilizer.IsSourceValidBinary :=
  SimplicialChain.binaryCSSCode_stabilizer_isSourceValidBinary
    (lsvQuotientComplex P r level) p

/-! ## Conditional hierarchy growth from Prasad strong approximation -/

/-- Under the sole construction-specialized Prasad density premise, the
zero-dimensional face counts of the actual finite LSV quotient complexes are
unbounded. -/
theorem lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvQuotientComplex P r level) 1) := by
  obtain ⟨level, hlevel⟩ :=
    indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
      P r hPrasad bound
  refine ⟨level, ?_⟩
  rw [card_lsvQuotientComplex_vertexFaces]
  rw [← Nat.card_eq_fintype_card]
  exact hlevel

/-- The rank-three / two-dimensional LSV quotient hierarchy has unbounded
vertex count under exactly the Prasad density premise. -/
theorem
    lsvTwoDimensionalQuotient_vertexFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .three))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 1) := by
  exact lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
    P .three hPrasad bound

/-- The rank-four / three-dimensional LSV quotient hierarchy has unbounded
vertex count under exactly the Prasad density premise. -/
theorem
    lsvThreeDimensionalQuotient_vertexFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .four))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 1) := by
  exact lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
    P .four hPrasad bound

/-- The triangle counts of the actual two-dimensional LSV quotient hierarchy
are unbounded under exactly the Prasad density premise.  The conclusion is
derived from the constructed vertex hierarchy and the proved triangle-cover
incidence bound. -/
theorem
    lsvTwoDimensionalQuotient_triangleFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .three))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by
  obtain ⟨level, hlevel⟩ :=
    indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
      P .three hPrasad (3 * bound)
  have hvertices :
      3 * bound < Fintype.card (IndexFiniteGroup P .three level) := by
    rw [← Nat.card_eq_fintype_card]
    exact hlevel
  have hcover := card_rankThree_vertices_le_three_mul_triangleFaces P level
  refine ⟨level, ?_⟩
  omega

/-- The tetrahedron counts of the actual three-dimensional LSV quotient
hierarchy are unbounded under exactly the Prasad density premise.  The
conclusion is derived from the constructed vertex hierarchy and the proved
tetrahedron-cover incidence bound. -/
theorem
    lsvThreeDimensionalQuotient_tetrahedronFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .four))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) := by
  obtain ⟨level, hlevel⟩ :=
    indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
      P .four hPrasad (4 * bound)
  have hvertices :
      4 * bound < Fintype.card (IndexFiniteGroup P .four level) := by
    rw [← Nat.card_eq_fintype_card]
    exact hlevel
  have hcover := card_rankFour_vertices_le_four_mul_tetrahedronFaces P level
  refine ⟨level, ?_⟩
  omega

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
