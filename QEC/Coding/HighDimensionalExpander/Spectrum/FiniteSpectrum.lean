import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.QuotientComplex
import QEC.Coding.HighDimensionalExpander.Spectrum.UniversalBuildingSpectrum

/-!
# Finite Hecke spectrum and determinant-sector candidate for LSV

This file defines the actual colored quotient Hecke operators by pulling the
universal fundamental-neighbour finsets back through #768's proved simple
transitivity equivalence and then applying congruence reduction.  It compares
their simultaneous spectrum with the actual joint approximate spectrum on the
universal affine building.  No Satake classification is used.

For compatibility with #768's clique-complex presentation, the file also
retains a construction-prefix operator.  The downstream
`LSVPrefixHeckeCompatibility` module proves, for every nonzero color, that
this prefix presentation agrees with the actual Hecke operator below.

The finite determinant-character subspace is constructed from characters of
the concrete residue quotient.  Under #768's concrete `PSL` containment, this
file proves the exact building-place color quotient, bidirectional character
descent, and literal `ζ^(d/t) = 1` criterion.  Identifying the resulting
one-dimensional functions with the trivial constituents in Proposition 1.5's
actual quotient representation remains part of the #770/#769 handoff; no
caller supplies a list of trivial eigenpackets.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

/-! ## Building-place color and finite determinant color -/

/-- Determinant valuation modulo the matrix rank on the general linear
group.  The multiplicative wrapper records that multiplication of matrices
adds determinant valuations. -/
noncomputable def lsvGeneralLinearDetOrderColor
    (P : BasePrime) (r : Rank) :
    GL (Fin r.matrixRank) (BuildingLocalField P) →*
      Multiplicative (ZMod r.matrixRank) where
  toFun A := Multiplicative.ofAdd
    (SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det A) : ZMod r.matrixRank)
  map_one' := by simp [SphericalHecke.localUnitOrder]
  map_mul' := by
    intro A B
    simp [map_mul, SphericalHecke.localUnitOrder_mul]

/-- Scalar matrices change the determinant valuation by a multiple of the
matrix rank, so determinant color descends to `PGL`. -/
theorem generalLinearCenter_le_lsvGeneralLinearDetOrderColor_ker
    (P : BasePrime) (r : Rank) :
    Subgroup.center (GL (Fin r.matrixRank) (BuildingLocalField P)) ≤
      (lsvGeneralLinearDetOrderColor P r).ker := by
  intro A hA
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
  obtain ⟨c, rfl⟩ := hA
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd
      (SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) c)) :
        ZMod r.matrixRank) = Multiplicative.ofAdd 0
  simp [Matrix.GeneralLinearGroup.det_scalar,
    SphericalHecke.localUnitOrder_pow]

/-- The genuine building-place determinant-valuation color on `PGL_d`. -/
noncomputable def lsvProjectiveDetOrderColor
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) →*
      Multiplicative (ZMod r.matrixRank) :=
  QuotientGroup.lift
    (Subgroup.center (GL (Fin r.matrixRank) (BuildingLocalField P)))
    (lsvGeneralLinearDetOrderColor P r)
    (generalLinearCenter_le_lsvGeneralLinearDetOrderColor_ker P r)

@[simp]
theorem lsvProjectiveDetOrderColor_mk
    (P : BasePrime) (r : Rank)
    (A : GL (Fin r.matrixRank) (BuildingLocalField P)) :
    lsvProjectiveDetOrderColor P r (Matrix.ProjGenLinGroup.mk A) =
      lsvGeneralLinearDetOrderColor P r A := by
  exact QuotientGroup.lift_mk _ _ A

/-- Building-place determinant color restricted to the actual simply
transitive Cartwright--Steger lattice. -/
noncomputable def lsvBuildingLatticeColor
    (P : BasePrime) (r : Rank) :
    BuildingCartwrightStegerLattice P r →*
      Multiplicative (ZMod r.matrixRank) :=
  (lsvProjectiveDetOrderColor P r).comp
    (BuildingCartwrightStegerLattice P r).subtype

/-- Every Cartwright--Steger generator has building color one. -/
@[simp]
theorem lsvBuildingLatticeColor_generator
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    lsvBuildingLatticeColor P r (buildingLatticeGenerator P r u) =
      Multiplicative.ofAdd (1 : ZMod r.matrixRank) := by
  change lsvProjectiveDetOrderColor P r
      (Matrix.ProjGenLinGroup.mk
        (buildingCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u))) = _
  rw [lsvProjectiveDetOrderColor_mk]
  change Multiplicative.ofAdd
      (SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (buildingCartwrightStegerGeneratorGL P r
            (constantClassRepresentative P r u))) :
        ZMod r.matrixRank) = _
  rw [buildingCartwrightStegerGeneratorGL_det_localUnitOrder]
  norm_num

/-- The lattice realizes every building-place color. -/
theorem lsvBuildingLatticeColor_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (lsvBuildingLatticeColor P r) := by
  letI : NeZero r.matrixRank :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega)
      (Rank.two_le_matrixRank r))⟩
  intro z
  let u : ConstantProjectiveClass P r := QuotientGroup.mk 1
  refine ⟨buildingLatticeGenerator P r u ^
      (Multiplicative.toAdd z).val, ?_⟩
  rw [map_pow, lsvBuildingLatticeColor_generator]
  apply Multiplicative.toAdd.injective
  simpa using (ZMod.natCast_zmod_val (Multiplicative.toAdd z)).symm

/-- The canonical quotient from building color `Z/dZ` to the finite residue
determinant class.  It sends color one to the selected ratio class, whose
order is `t = gcd(|L^×|, d)`.  Thus this map retains the distinction between
`d` and `t` required by LSV05a's `ζ^(d/t) = 1` condition. -/
noncomputable def lsvBuildingColorToResidueDetClass
    (P : BasePrime) (r : Rank) (level : Nat) :
    Multiplicative (ZMod r.matrixRank) →*
      ResiduePowerClass P r level := by
  let c : ResiduePowerClass P r level :=
    QuotientGroup.mk (indexRatioUnit P r level)
  have hdvd : orderOf c ∣ r.matrixRank := by
    rw [show orderOf c =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank from
        indexRatioUnit_orderOf P r level]
    exact Nat.gcd_dvd_right _ _
  have hpow : c ^ r.matrixRank = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hdvd
  let f : ℤ →+ Additive (ResiduePowerClass P r level) :=
    { toFun := fun n ↦ Additive.ofMul (c ^ n)
      map_zero' := by simp
      map_add' := by
        intro m n
        apply Additive.toMul.injective
        exact zpow_add c m n }
  have hf : f (r.matrixRank : ℤ) = 0 := by
    apply Additive.toMul.injective
    change c ^ (r.matrixRank : ℤ) = 1
    simpa using hpow
  let fmod : ZMod r.matrixRank →+
      Additive (ResiduePowerClass P r level) :=
    ZMod.lift r.matrixRank ⟨f, hf⟩
  exact
    { toFun := fun z ↦ Additive.toMul (fmod (Multiplicative.toAdd z))
      map_one' := by simp [fmod]
      map_mul' := by
        intro x y
        change Additive.toMul
            (fmod (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
        rw [map_add]
        rfl }

@[simp]
theorem lsvBuildingColorToResidueDetClass_one
    (P : BasePrime) (r : Rank) (level : Nat) :
    lsvBuildingColorToResidueDetClass P r level
        (Multiplicative.ofAdd (1 : ZMod r.matrixRank)) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  unfold lsvBuildingColorToResidueDetClass
  dsimp
  have hone : (1 : ZMod r.matrixRank) =
      ((1 : ℤ) : ZMod r.matrixRank) := by norm_num
  rw [hone, ZMod.lift_coe]
  simp

/-- Exact compatibility of building-place color and finite residue
determinant color on the entire constructed lattice.  The proof uses the
actual closure by Cartwright--Steger generators; it is not an assumed
commuting square. -/
theorem lsvBuildingColor_reduction_compatibility
    (P : BasePrime) (r : Rank) (level : Nat) :
    (lsvBuildingColorToResidueDetClass P r level).comp
        (lsvBuildingLatticeColor P r) =
      (indexImageDetClassHom P r level).comp
        (buildingLatticeReduction P r level) := by
  apply MonoidHom.ext
  intro g
  change lsvBuildingColorToResidueDetClass P r level
      (lsvBuildingLatticeColor P r g) =
    indexImageDetClassHom P r level
      (buildingLatticeReduction P r level g)
  rcases g with ⟨g, hg⟩
  refine Subgroup.closure_induction (p := fun x hx ↦
      lsvBuildingColorToResidueDetClass P r level
          (lsvBuildingLatticeColor P r ⟨x, hx⟩) =
        indexImageDetClassHom P r level
          (buildingLatticeReduction P r level ⟨x, hx⟩)) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨u, rfl⟩
    rw [show (⟨buildingCartwrightStegerGenerator P r u,
        Subgroup.subset_closure (Set.mem_range_self u)⟩ :
          BuildingCartwrightStegerLattice P r) =
        buildingLatticeGenerator P r u from rfl]
    rw [lsvBuildingLatticeColor_generator,
      lsvBuildingColorToResidueDetClass_one,
      buildingLatticeReduction_generator]
    simpa [indexImageDetClassHom] using
      (residueProjectiveDetClass_indexCartwrightStegerClassGenerator
        P r level u).symm
  · change lsvBuildingColorToResidueDetClass P r level
        (lsvBuildingLatticeColor P r
          (1 : BuildingCartwrightStegerLattice P r)) =
      indexImageDetClassHom P r level
        (buildingLatticeReduction P r level 1)
    simp
  · intro x y hx hy hxeq hyeq
    rw [show (⟨x * y, Subgroup.mul_mem _ hx hy⟩ :
        BuildingCartwrightStegerLattice P r) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl]
    simp only [map_mul, hxeq, hyeq]
  · intro x hx hxeq
    rw [show (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ :
        BuildingCartwrightStegerLattice P r) = (⟨x, hx⟩ :
          BuildingCartwrightStegerLattice P r)⁻¹ from rfl]
    simp only [map_inv, hxeq]

/-- The building-to-residue color quotient is onto for every selected level.
This follows from the actual finite reduction and its determinant-class
surjectivity, together with the proved compatibility square. -/
theorem lsvBuildingColorToResidueDetClass_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (lsvBuildingColorToResidueDetClass P r level) := by
  intro y
  obtain ⟨x, hx⟩ := indexImageDetClassHom_surjective P r level y
  obtain ⟨g, hg⟩ := buildingLatticeReduction_surjective P r level x
  refine ⟨lsvBuildingLatticeColor P r g, ?_⟩
  have hcompat := congrArg (fun h ↦ h g)
    (lsvBuildingColor_reduction_compatibility P r level)
  simpa [hg, hx] using hcompat

/-- The selected principal congruence subgroup has building color in the
kernel of the finite color quotient.  The reverse inclusion is proved below
under the concrete finite `PSL` containment. -/
theorem buildingCongruence_color_mem_residueKernel
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : BuildingCartwrightStegerCongruenceSubgroup P r level) :
    lsvBuildingLatticeColor P r g.1 ∈
      (lsvBuildingColorToResidueDetClass P r level).ker := by
  rw [MonoidHom.mem_ker]
  have hcompat := congrArg (fun h ↦ h g.1)
    (lsvBuildingColor_reduction_compatibility P r level)
  change lsvBuildingColorToResidueDetClass P r level
      (lsvBuildingLatticeColor P r g.1) =
    indexImageDetClassHom P r level
      (buildingLatticeReduction P r level g.1) at hcompat
  have hg : buildingLatticeReduction P r level g.1 = 1 := g.2
  rw [hg] at hcompat
  simpa using hcompat

/-- Under the concrete finite `PSL` containment, every determinant-zero
finite image element lifts to a lattice element of building color zero.
Perfectness of the already constructed finite `PSL` supplies the reverse
lifting: commutators lift through the surjective congruence reduction and
every commutator has zero color. -/
theorem lsvColorZeroReduction_surjective_of_PSL_le
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    ∀ x : IndexCartwrightStegerColorZero P r level,
      ∃ g : (lsvBuildingLatticeColor P r).ker,
        buildingLatticeReduction P r level g.1 = x.1 := by
  let L := BuildingCartwrightStegerLattice P r
  let F := IndexCartwrightStegerImage P r level
  let K := IndexCartwrightStegerColorZero P r level
  let color := lsvBuildingLatticeColor P r
  let reduction := buildingLatticeReduction P r level
  have hcommL : commutator L ≤ color.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hrange : reduction.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (buildingLatticeReduction_surjective P r level)
  have hmapped : (commutator L).map reduction = commutator F := by
    rw [map_commutator_eq, hrange]
    rfl
  have hcommF : commutator F ≤ color.ker.map reduction := by
    rw [← hmapped]
    exact Subgroup.map_mono hcommL
  let e := indexCartwrightStegerColorZeroEquivPSLOfLe P r level hPSL
  letI : Group.IsPerfect (PSL P r level) :=
    ⟨PSL_commutator_eq_top P r level⟩
  letI : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective
  intro x
  have hxcommK : x ∈ commutator K := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top x
  have hxmap : (x : F) ∈ (commutator K).map K.subtype :=
    ⟨x, hxcommK, rfl⟩
  rw [K.map_subtype_commutator] at hxmap
  have hxcommF : (x : F) ∈ commutator F :=
    (Subgroup.commutator_mono le_top le_top) hxmap
  obtain ⟨g, hg, hgreduction⟩ := hcommF hxcommF
  exact ⟨⟨g, hg⟩, hgreduction⟩

/-- The image of the principal congruence subgroup in building color. -/
noncomputable def lsvCongruenceBuildingColorImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (Multiplicative (ZMod r.matrixRank)) :=
  (BuildingCartwrightStegerCongruenceSubgroup P r level).map
    (lsvBuildingLatticeColor P r)

/-- Exact bidirectional building-color descent under the concrete `PSL`
containment: the colors realized by the congruence subgroup are precisely the
kernel of the quotient from `Z/dZ` to the finite residue determinant class.
This is the group-level content behind LSV05a's `ζ^(d/t) = 1` condition. -/
theorem lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    lsvCongruenceBuildingColorImage P r level =
      (lsvBuildingColorToResidueDetClass P r level).ker := by
  apply le_antisymm
  · rintro z ⟨g, hg, rfl⟩
    exact buildingCongruence_color_mem_residueKernel P r level ⟨g, hg⟩
  · intro z hz
    obtain ⟨g, hgcolor⟩ := lsvBuildingLatticeColor_surjective P r z
    have hcompat := congrArg (fun h ↦ h g)
      (lsvBuildingColor_reduction_compatibility P r level)
    change lsvBuildingColorToResidueDetClass P r level
        (lsvBuildingLatticeColor P r g) =
      indexImageDetClassHom P r level
        (buildingLatticeReduction P r level g) at hcompat
    have hdetzero : indexImageDetClassHom P r level
        (buildingLatticeReduction P r level g) = 1 := by
      rw [← hcompat, hgcolor]
      exact hz
    let x : IndexCartwrightStegerColorZero P r level :=
      ⟨buildingLatticeReduction P r level g, hdetzero⟩
    obtain ⟨h, hh⟩ :=
      lsvColorZeroReduction_surjective_of_PSL_le P r level hPSL x
    let gamma : BuildingCartwrightStegerLattice P r := g * h.1⁻¹
    have hgammaReduction : buildingLatticeReduction P r level gamma = 1 := by
      dsimp [gamma]
      rw [map_mul, map_inv, hh]
      simp [x]
    have hgammaColor : lsvBuildingLatticeColor P r gamma = z := by
      dsimp [gamma]
      rw [map_mul, map_inv, hgcolor]
      have hhcolor : lsvBuildingLatticeColor P r h.1 = 1 := h.2
      rw [hhcolor]
      simp
    exact ⟨gamma, hgammaReduction, hgammaColor⟩

/-- A building-color character is trivial on the concrete congruence
subgroup exactly when it kills the subgroup's actual color image. -/
def IsLSVBuildingColorCharacterTrivialOnCongruence
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) : Prop :=
  lsvCongruenceBuildingColorImage P r level ≤ character.ker

theorem isLSVBuildingColorCharacterTrivialOnCongruence_iff_pointwise
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      ∀ g : BuildingCartwrightStegerCongruenceSubgroup P r level,
        character (lsvBuildingLatticeColor P r g.1) = 1 := by
  constructor
  · intro h g
    rw [← MonoidHom.mem_ker]
    exact h ⟨g.1, g.2, rfl⟩
  · intro h z hz
    obtain ⟨g, hg, rfl⟩ := hz
    rw [MonoidHom.mem_ker]
    exact h ⟨g, hg⟩

/-- Exact bidirectional character descent.  Under the concrete `PSL`
containment, the one-dimensional building-color characters well defined on
the congruence quotient are precisely the pullbacks of characters of the
finite residue determinant-class quotient. -/
theorem isLSVBuildingColorCharacterTrivialOnCongruence_iff_factors
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      ∃ finiteCharacter : ResiduePowerClass P r level →* ℂ,
        finiteCharacter.comp
            (lsvBuildingColorToResidueDetClass P r level) = character := by
  let colorQuotient := lsvBuildingColorToResidueDetClass P r level
  have hsurj : Function.Surjective colorQuotient :=
    lsvBuildingColorToResidueDetClass_surjective P r level
  have himage : lsvCongruenceBuildingColorImage P r level =
      colorQuotient.ker :=
    lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
      P r level hPSL
  constructor
  · intro htrivial
    have hker : colorQuotient.ker ≤ character.ker := by
      rw [← himage]
      exact htrivial
    have hkerUnits : colorQuotient.ker ≤ character.toHomUnits.ker := by
      simpa only [MonoidHom.ker_toHomUnits] using hker
    let finiteUnitCharacter : ResiduePowerClass P r level →* ℂˣ :=
      MonoidHom.liftOfSurjective colorQuotient hsurj
        ⟨character.toHomUnits, hkerUnits⟩
    have hfiniteUnitCharacter :
        finiteUnitCharacter.comp colorQuotient = character.toHomUnits :=
      MonoidHom.liftOfRightInverse_comp ..
    let finiteCharacter : ResiduePowerClass P r level →* ℂ :=
      (Units.coeHom ℂ).comp finiteUnitCharacter
    refine ⟨finiteCharacter, ?_⟩
    apply MonoidHom.ext
    intro z
    change ((finiteUnitCharacter (colorQuotient z) : ℂ)) = character z
    have hz := DFunLike.congr_fun hfiniteUnitCharacter z
    exact congrArg Units.val hz
  · rintro ⟨finiteCharacter, hfactor⟩
    change finiteCharacter.comp colorQuotient = character at hfactor
    rw [IsLSVBuildingColorCharacterTrivialOnCongruence, himage]
    intro z hz
    rw [MonoidHom.mem_ker]
    rw [← hfactor]
    change finiteCharacter (colorQuotient z) = 1
    rw [show colorQuotient z = 1 from hz]
    simp

/-- Evaluation of the building-to-residue color quotient on a natural color.
The selected ratio class is the image of color one. -/
theorem lsvBuildingColorToResidueDetClass_natCast
    (P : BasePrime) (r : Rank) (level n : Nat) :
    lsvBuildingColorToResidueDetClass P r level
        (Multiplicative.ofAdd (n : ZMod r.matrixRank)) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) ^ n := by
  rw [show Multiplicative.ofAdd (n : ZMod r.matrixRank) =
      Multiplicative.ofAdd (1 : ZMod r.matrixRank) ^ n by
    apply Multiplicative.toAdd.injective
    simp]
  rw [map_pow, lsvBuildingColorToResidueDetClass_one]

/-- Evaluation of a building-color character on a natural color. -/
theorem lsvBuildingColorCharacter_natCast
    (r : Rank) (character : Multiplicative (ZMod r.matrixRank) →* ℂ)
    (n : Nat) :
    character (Multiplicative.ofAdd (n : ZMod r.matrixRank)) =
      character (Multiplicative.ofAdd (1 : ZMod r.matrixRank)) ^ n := by
  rw [show Multiplicative.ofAdd (n : ZMod r.matrixRank) =
      Multiplicative.ofAdd (1 : ZMod r.matrixRank) ^ n by
    apply Multiplicative.toAdd.injective
    simp]
  rw [map_pow]

/-- Exact order formula for the LSV notation.  If `t` is the cardinality of
the congruence subgroup's image in building color, then
`d = t * |ResiduePowerClass|`. -/
theorem lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    r.matrixRank =
      Nat.card (lsvCongruenceBuildingColorImage P r level) *
        orderOf
          (QuotientGroup.mk (indexRatioUnit P r level) :
            ResiduePowerClass P r level) := by
  let colorQuotient := lsvBuildingColorToResidueDetClass P r level
  have hsurj : Function.Surjective colorQuotient :=
    lsvBuildingColorToResidueDetClass_surjective P r level
  have himage : lsvCongruenceBuildingColorImage P r level =
      colorQuotient.ker :=
    lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
      P r level hPSL
  calc
    r.matrixRank = Nat.card (Multiplicative (ZMod r.matrixRank)) := by
      rw [Nat.card_congr Multiplicative.toAdd]
      exact (Nat.card_zmod r.matrixRank).symm
    _ = Nat.card
          (Multiplicative (ZMod r.matrixRank) ⧸ colorQuotient.ker) *
        Nat.card colorQuotient.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup colorQuotient.ker
    _ = Nat.card (ResiduePowerClass P r level) *
        Nat.card (lsvCongruenceBuildingColorImage P r level) := by
      rw [Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective
          colorQuotient hsurj).toEquiv,
        himage]
    _ = Nat.card (lsvCongruenceBuildingColorImage P r level) *
        orderOf
          (QuotientGroup.mk (indexRatioUnit P r level) :
            ResiduePowerClass P r level) := by
      rw [indexRatioUnit_orderOf,
        IndexSelection.natCard_powerClass]
      simp only [Fintype.card_fin]
      exact Nat.mul_comm _ _

/-- In the source's notation, the order of the surviving finite determinant
color quotient is literally `d / t`. -/
theorem lsvResidueDetClassOrder_eq_matrixRank_div_congruenceColorOrder
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    r.matrixRank /
        Nat.card (lsvCongruenceBuildingColorImage P r level) =
      orderOf
        (QuotientGroup.mk (indexRatioUnit P r level) :
          ResiduePowerClass P r level) := by
  letI : NeZero r.matrixRank :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega)
      (Rank.two_le_matrixRank r))⟩
  letI : Finite (lsvCongruenceBuildingColorImage P r level) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let t := Nat.card (lsvCongruenceBuildingColorImage P r level)
  let quotientOrder := orderOf
    (QuotientGroup.mk (indexRatioUnit P r level) :
      ResiduePowerClass P r level)
  have hcard : r.matrixRank = t * quotientOrder :=
    lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
      P r level hPSL
  calc
    r.matrixRank / t = (t * quotientOrder) / t :=
      congrArg (fun n ↦ n / t) hcard
    _ = quotientOrder := Nat.mul_div_cancel_left _ Nat.card_pos

/-- Literal LSV05a descent criterion.  Write `t` for the order of the color
image of the congruence subgroup.  The finite residue determinant class has
order `d / t`; hence the displayed exponent is exactly the paper's
`d/t`.  The proof is bidirectional and uses the exact color-image/kernel
identity above, not an unrestricted `ζ^d = 1` condition. -/
theorem isLSVBuildingColorCharacterTrivialOnCongruence_iff_zeta_pow
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      character (Multiplicative.ofAdd (1 : ZMod r.matrixRank)) ^
          orderOf
            (QuotientGroup.mk (indexRatioUnit P r level) :
              ResiduePowerClass P r level) = 1 := by
  letI : NeZero r.matrixRank :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega)
      (Rank.two_le_matrixRank r))⟩
  let colorQuotient := lsvBuildingColorToResidueDetClass P r level
  let c : ResiduePowerClass P r level :=
    QuotientGroup.mk (indexRatioUnit P r level)
  have himage : lsvCongruenceBuildingColorImage P r level =
      colorQuotient.ker :=
    lsvCongruenceBuildingColorImage_eq_residueKernel_of_PSL_le
      P r level hPSL
  constructor
  · intro htrivial
    have hker : colorQuotient.ker ≤ character.ker := by
      rw [← himage]
      exact htrivial
    let z := Multiplicative.ofAdd
      ((orderOf c : Nat) : ZMod r.matrixRank)
    have hz : z ∈ colorQuotient.ker := by
      rw [MonoidHom.mem_ker]
      change lsvBuildingColorToResidueDetClass P r level z = 1
      rw [show z = Multiplicative.ofAdd
          ((orderOf c : Nat) : ZMod r.matrixRank) from rfl,
        lsvBuildingColorToResidueDetClass_natCast]
      exact pow_orderOf_eq_one c
    have hchar : character z = 1 := MonoidHom.mem_ker.mp (hker hz)
    rw [show z = Multiplicative.ofAdd
        ((orderOf c : Nat) : ZMod r.matrixRank) from rfl,
      lsvBuildingColorCharacter_natCast] at hchar
    exact hchar
  · intro hpow
    rw [IsLSVBuildingColorCharacterTrivialOnCongruence, himage]
    intro z hz
    rw [MonoidHom.mem_ker]
    let n := (Multiplicative.toAdd z).val
    have hzrepr : z = Multiplicative.ofAdd
        (n : ZMod r.matrixRank) := by
      apply Multiplicative.toAdd.injective
      dsimp [n]
      symm
      exact ZMod.natCast_zmod_val (Multiplicative.toAdd z)
    have hcpow : c ^ n = 1 := by
      have hzmap : colorQuotient z = 1 := hz
      rw [hzrepr] at hzmap
      rw [show colorQuotient =
          lsvBuildingColorToResidueDetClass P r level from rfl,
        lsvBuildingColorToResidueDetClass_natCast] at hzmap
      exact hzmap
    obtain ⟨m, hm⟩ := orderOf_dvd_of_pow_eq_one hcpow
    rw [hzrepr, lsvBuildingColorCharacter_natCast, hm, pow_mul, hpow,
      one_pow]

/-- Counting `L²` functions on the actual finite quotient vertex group. -/
abbrev LSVFiniteL2 (P : BasePrime) (r : Rank) (level : Nat) :=
  IndexFiniteGroup P r level → ℂ

/-- #768's simple transitivity as an equivalence between the constructed
lattice and all universal-building vertices. -/
noncomputable def lsvBuildingLatticeVertexEquiv
    (P : BasePrime) (r : Rank) :
    BuildingCartwrightStegerLattice P r ≃
      CartwrightStegerBuildingVertex P r :=
  Equiv.ofBijective (buildingLatticeVertexMap P r)
    (buildingLatticeVertexMap_bijective P r)

/-- The actual color-`k` Hecke operator on the finite congruence quotient.
Every universal fundamental neighbour is pulled back to its unique lattice
element and then reduced.  Summing before reduction preserves multiplicity
when distinct neighbours collide in the finite quotient. -/
def lsvColorHeckeOperator
    (P : BasePrime) (r : Rank) (level k : Nat) :
    LSVFiniteL2 P r level →ₗ[ℂ] LSVFiniteL2 P r level := by
  classical
  exact
    { toFun := fun f x ↦
        ∑ q ∈ SphericalHecke.fundamentalNeighborCosets
            (BaseField P) r.matrixRank k,
          f (x * buildingLatticeFiniteReduction P r level
            ((lsvBuildingLatticeVertexEquiv P r).symm q))
      map_add' := by
        intro f g
        funext x
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum] }

@[simp]
theorem lsvColorHeckeOperator_apply
    (P : BasePrime) (r : Rank) (level k : Nat)
    (f : LSVFiniteL2 P r level) (x : IndexFiniteGroup P r level) :
    lsvColorHeckeOperator P r level k f x =
      ∑ q ∈ SphericalHecke.fundamentalNeighborCosets
          (BaseField P) r.matrixRank k,
        f (x * buildingLatticeFiniteReduction P r level
          ((lsvBuildingLatticeVertexEquiv P r).symm q)) := by
  rfl

/-- The constant vector has the actual universal-building colored degree as
its eigenvalue.  This fixes the unnormalized Hecke multiplicity convention. -/
theorem lsvColorHeckeOperator_const
    (P : BasePrime) (r : Rank) (level k : Nat) (c : ℂ) :
    lsvColorHeckeOperator P r level k (fun _ ↦ c) =
      (SphericalHecke.coloredAdjacencyDegree
        (BaseField P) r.matrixRank k : ℂ) • (fun _ ↦ c) := by
  funext x
  simp [SphericalHecke.coloredAdjacencyDegree]

/-- The construction-indexed color-`k` operator on the finite vertex group.
It sums over the source building-color finset and reduces each term only
inside the summand.  In particular, distinct building neighbours that collide
in a congruence quotient retain their Hecke multiplicity. -/
def lsvConstructionColorOperator
    (P : BasePrime) (r : Rank) (level k : Nat) :
    LSVFiniteL2 P r level →ₗ[ℂ] LSVFiniteL2 P r level := by
  classical
  exact
    { toFun := fun f x ↦
        ∑ s ∈ buildingColorGeneratorFinset P r k,
          f (x * buildingLatticeFiniteReduction P r level s)
      map_add' := by
        intro f g
        funext x
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum] }

/-- A simultaneous eigenpair for every nonzero building color. -/
def IsLSVJointEigenpair
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ)
    (vector : LSVFiniteL2 P r level) : Prop :=
  vector ≠ 0 ∧ ∀ color : Fin (r.matrixRank - 1),
    lsvColorHeckeOperator P r level (color.val + 1) vector =
      eigenvalue color • vector

/-- The actual finite quotient Hecke joint spectrum is built from concrete
common eigenvectors; no spectrum list is supplied by a caller. -/
def lsvJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  {eigenvalue | ∃ vector,
    IsLSVJointEigenpair P r level eigenvalue vector}

/-- Pull a complex character of #768's concrete finite determinant-class
quotient back to the actual finite quotient vertices. -/
def lsvColorCharacterVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : ResiduePowerClass P r level →* ℂ) :
    LSVFiniteL2 P r level :=
  fun x ↦ character (indexImageDetClassHom P r level x)

/-- The finite determinant-character subspace of the selected quotient.
The preceding theorems prove that these are exactly the building-color
characters descending through the congruence subgroup under concrete `PSL`
containment.  The final Proposition 1.5 adapter must still identify their
one-dimensional representation-theoretic realizations with its trivial
constituents.  The span formulation handles multiplicity among equal packets
without silently deleting a nontrivial eigenvector that shares an eigenvalue. -/
def lsvFiniteDetCharacterSubspace
    (P : BasePrime) (r : Rank) (level : Nat) :
    Submodule ℂ (LSVFiniteL2 P r level) :=
  Submodule.span ℂ
    (Set.range (lsvColorCharacterVector P r level))

/-- Whether a concrete finite-quotient vector belongs to the finite
determinant-character sector. -/
def IsLSVFiniteDetCharacterVector
    (P : BasePrime) (r : Rank) (level : Nat)
    (vector : LSVFiniteL2 P r level) : Prop :=
  vector ∈ lsvFiniteDetCharacterSubspace P r level

/-- Actual Hecke packets with a finite determinant-character
eigenvector. -/
def lsvFiniteDetCharacterJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  {eigenvalue | ∃ vector,
    IsLSVJointEigenpair P r level eigenvalue vector ∧
      IsLSVFiniteDetCharacterVector P r level vector}

/-- Actual Hecke packets with a witnessing eigenvector outside the
finite determinant-character candidate.  The vector-level definition, rather
than packet-set subtraction, preserves mixed multiplicity. -/
def lsvFiniteDetCandidateNontrivialJointSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set (Fin (r.matrixRank - 1) → ℂ) :=
  {eigenvalue | ∃ vector,
    IsLSVJointEigenpair P r level eigenvalue vector ∧
      ¬ IsLSVFiniteDetCharacterVector P r level vector}

/-- The actual universal-building simultaneous spectrum in the supported
matrix ranks. -/
def lsvUniversalBuildingJointSpectrum
    (P : BasePrime) :
    (r : Rank) → Set (Fin (r.matrixRank - 1) → ℂ)
  | .three => RankThreeBuildingJointApproximateSpectrum (BaseField P)
  | .four => RankFourBuildingJointApproximateSpectrum (BaseField P)

/-- The finite-determinant-sector containment candidate.  It may be promoted
to LSV's Ramanujan predicate only after #770 identifies the descended
one-dimensional characters with Proposition 1.5's actual quotient-`L²`
trivial constituents and the actual Hecke presentation is related to #768's
clique-complex color presentation. -/
def IsLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum
    (P : BasePrime) (r : Rank) (level : Nat) : Prop :=
  lsvFiniteDetCandidateNontrivialJointSpectrum P r level ⊆
    lsvUniversalBuildingJointSpectrum P r

theorem mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ) :
    eigenvalue ∈ lsvFiniteDetCandidateNontrivialJointSpectrum P r level ↔
      ∃ vector,
        IsLSVJointEigenpair P r level eigenvalue vector ∧
          ¬ IsLSVFiniteDetCharacterVector P r level vector := by
  rfl

/-- Quantifier-level form of the finite-determinant-sector containment
candidate. -/
theorem isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum P r level ↔
      ∀ eigenvalue vector,
        IsLSVJointEigenpair P r level eigenvalue vector →
        ¬ IsLSVFiniteDetCharacterVector P r level vector →
        eigenvalue ∈ lsvUniversalBuildingJointSpectrum P r := by
  constructor
  · intro h eigenvalue vector heigen hnontrivial
    exact h ⟨vector, heigen, hnontrivial⟩
  · rintro h eigenvalue ⟨vector, heigen, hnontrivial⟩
    exact h eigenvalue vector heigen hnontrivial

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
