import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Norm.NormOneCompatibility

/-!
# Intrinsic strong-approximation interface for Cartwright--Steger

The completion and finite reduction maps are transported from the checked
split-coordinate presentation to all intrinsic norm-one units of the actual
arithmetic order.  The proved group equivalence makes density and
surjectivity literally equivalent, so no selected-subgroup premise remains.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped PowerSeries.WithPiTopology

local instance intrinsicResidueFieldDiscreteTopologicalSpace
    (P : BasePrime) (r : Rank) (level : Nat) :
    TopologicalSpace (ResidueField P r level) := ⊥

local instance intrinsicResidueFieldDiscreteTopology
    (P : BasePrime) (r : Rank) (level : Nat) :
    DiscreteTopology (ResidueField P r level) := ⟨rfl⟩

/-- Completion of every intrinsic base-field norm-one arithmetic-order unit
at the selected congruence place. -/
noncomputable def baseNormOneOrderUnitsToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerBaseNormOneOrderUnits P r →*
      IndexCompletedNormOneInnerForm P r level :=
  (orderNormOneInnerFormToCompleted P r level).comp
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm.toMonoidHom

/-- Finite projective reduction on all intrinsic norm-one units of the
actual arithmetic order. -/
noncomputable def baseNormOneOrderUnitsReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    CartwrightStegerBaseNormOneOrderUnits P r →* PSL P r level :=
  (orderNormOneInnerFormReduction P r level).comp
    (orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm.toMonoidHom

theorem baseNormOneOrderUnitsReduction_factor_completed
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerBaseNormOneOrderUnits P r) :
    baseNormOneOrderUnitsReduction P r level u =
      specialLinearToPSL P r level
        (indexCompletedNormOneReduction P r level
          (baseNormOneOrderUnitsToCompleted P r level u)) := by
  exact orderNormOneInnerFormReduction_factor_completed P r level
    ((orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm u)

/-- Passing from split coordinates to all actual norm-one order units does
not change the completed image. -/
theorem range_baseNormOneOrderUnitsToCompleted
    (P : BasePrime) (r : Rank) (level : Nat) :
    Set.range (baseNormOneOrderUnitsToCompleted P r level) =
      Set.range (orderNormOneInnerFormToCompleted P r level) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm u,
      rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨orderNormOneInnerFormEquivBaseNormOneOrderUnits P r s, ?_⟩
    simp [baseNormOneOrderUnitsToCompleted]

theorem denseRange_baseNormOneOrderUnitsToCompleted_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    DenseRange (baseNormOneOrderUnitsToCompleted P r level) ↔
      DenseRange (orderNormOneInnerFormToCompleted P r level) := by
  change Dense (Set.range (baseNormOneOrderUnitsToCompleted P r level)) ↔
    Dense (Set.range (orderNormOneInnerFormToCompleted P r level))
  rw [range_baseNormOneOrderUnitsToCompleted]

/-- Finite surjectivity for intrinsic norm-one order units is exactly the
construction-owned split-coordinate strong-approximation endpoint. -/
theorem baseNormOneOrderUnitsReduction_surjective_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) ↔
      Function.Surjective (orderNormOneInnerFormReduction P r level) := by
  constructor
  · intro h y
    obtain ⟨u, hu⟩ := h y
    exact ⟨(orderNormOneInnerFormEquivBaseNormOneOrderUnits P r).symm u, hu⟩
  · intro h y
    obtain ⟨s, hs⟩ := h y
    refine ⟨orderNormOneInnerFormEquivBaseNormOneOrderUnits P r s, ?_⟩
    simpa [baseNormOneOrderUnitsReduction] using hs

/-! ## Exact finite strong-approximation endpoint

The following equivalences prevent two tempting but invalid shortcuts.  The
ordinary split `SL` lifting theorem is not enough, and neither is the proved
nontriviality of the norm-one image.  For the actual Cartwright--Steger order,
finite norm-one surjectivity is *exactly* the missing containment of the full
finite `PSL` in the construction's genuine finite image.
-/

/-- Surjectivity of the genuine norm-one reduction is equivalent to placing
the full finite `PSL` inside the reduction image of all actual inner-form
integral points. -/
theorem orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexInnerFormImage P r level := by
  constructor
  · intro hsurj y hy
    let yPSL : PSL P r level := ⟨y, hy⟩
    obtain ⟨s, hs⟩ := hsurj yPSL
    have hprojective :
        orderNormOneInnerFormReductionToPGL P r level s = y := by
      exact congrArg Subtype.val hs
    have hyNorm : y ∈ IndexInnerFormNormOnePGLImage P r level := by
      rw [IndexInnerFormNormOnePGLImage_eq_orderNormOne_range]
      exact ⟨s, hprojective⟩
    exact IndexInnerFormNormOnePGLImage_le_innerFormImage P r level
      hyNorm
  · exact orderNormOneInnerFormReduction_surjective_of_PSL_le_innerFormImage
      P r level

/-- The full-inner-form formulation is literally the explicit finite ambient
formulation, by the proved lattice-times-stabilizer decomposition. -/
theorem orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerAmbient P r level := by
  rw [orderNormOneInnerFormReduction_surjective_iff_PSL_le_innerFormImage,
    IndexInnerFormImage_eq_IndexCartwrightStegerAmbient]

/-- The actual Cartwright--Steger image is contained in its explicit ambient
group. -/
theorem IndexCartwrightStegerImage_le_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ≤
      IndexCartwrightStegerAmbient P r level := by
  rw [IndexCartwrightStegerAmbient,
    IndexCartwrightStegerUnitImage_eq_image]
  exact le_sup_right

/-- Exact construction-level endpoint: genuine norm-one reduction is onto if
and only if the finite Cartwright--Steger image contains the selected `PSL`.
This packages no density or surjectivity certificate; both sides are concrete
properties of objects already constructed from the cyclic algebra and order. -/
theorem orderNormOneInnerFormReduction_surjective_iff_PSL_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (orderNormOneInnerFormReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  constructor
  · intro hsurj
    exact PSL_le_IndexCartwrightStegerImage_of_le_ambient P r level
      ((orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
        P r level).mp hsurj)
  · intro hPSL
    apply (orderNormOneInnerFormReduction_surjective_iff_PSL_le_ambient
      P r level).mpr
    exact hPSL.trans (IndexCartwrightStegerImage_le_ambient P r level)

/-- The intrinsic base-field norm-one order units have surjective finite
reduction exactly when the explicit finite Cartwright--Steger image contains
the full selected `PSL`. -/
theorem baseNormOneOrderUnitsReduction_surjective_iff_PSL_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (baseNormOneOrderUnitsReduction P r level) ↔
      PSL P r level ≤ IndexCartwrightStegerImage P r level := by
  rw [baseNormOneOrderUnitsReduction_surjective_iff,
    orderNormOneInnerFormReduction_surjective_iff_PSL_le_image]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
