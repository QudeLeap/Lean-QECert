import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Order.SplitCoordinates

/-!
# Compatibility of the Cartwright--Steger norm-one groups

The global and building-place determinant kernels introduced during the
construction are both the scalar extensions of one reduced norm over the
base function field.  This file identifies the three subgroups exactly.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- The intrinsic global norm-one subgroup, defined over the base function
field rather than in either matrix splitting. -/
noncomputable def CyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) : Subgroup ((CyclicAlgebra P r)ˣ) :=
  (cyclicAlgebraReducedNorm P r).ker

theorem cyclicAlgebraSplitNormOne_eq_normOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraSplitNormOne P r = CyclicAlgebraNormOne P r := by
  apply SetLike.ext
  intro u
  change cyclicAlgebraSplitReducedNorm P r u = 1 ↔
    cyclicAlgebraReducedNorm P r u = 1
  constructor
  · intro hu
    apply Units.map_injective (functionFieldEmbedding P r).injective
    calc
      Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) =
        cyclicAlgebraSplitReducedNorm P r u :=
          cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r u
      _ = 1 := hu
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 := (map_one _).symm
  · intro hu
    calc
      cyclicAlgebraSplitReducedNorm P r u =
        Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) :=
            (cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r u).symm
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 :=
        congrArg (Units.map (functionFieldEmbedding P r).toMonoidHom) hu
      _ = 1 := map_one _

theorem cyclicAlgebraBuildingNormOne_eq_normOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraBuildingNormOne P r = CyclicAlgebraNormOne P r := by
  apply SetLike.ext
  intro u
  change cyclicAlgebraBuildingReducedNorm P r u = 1 ↔
    cyclicAlgebraReducedNorm P r u = 1
  constructor
  · intro hu
    apply Units.map_injective (functionFieldToBuildingLocalField P).injective
    calc
      Units.map (functionFieldToBuildingLocalField P).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) =
        cyclicAlgebraBuildingReducedNorm P r u :=
          cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm P r u
      _ = 1 := hu
      _ = Units.map (functionFieldToBuildingLocalField P).toMonoidHom 1 :=
        (map_one _).symm
  · intro hu
    calc
      cyclicAlgebraBuildingReducedNorm P r u =
        Units.map (functionFieldToBuildingLocalField P).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) :=
            (cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm P r u).symm
      _ = Units.map (functionFieldToBuildingLocalField P).toMonoidHom 1 :=
        congrArg (Units.map
          (functionFieldToBuildingLocalField P).toMonoidHom) hu
      _ = 1 := map_one _

/-- The two construction-era concrete kernels are the same subgroup, as a
consequence rather than an assumption. -/
theorem cyclicAlgebraSplitNormOne_eq_buildingNormOne
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraSplitNormOne P r = CyclicAlgebraBuildingNormOne P r := by
  rw [cyclicAlgebraSplitNormOne_eq_normOne,
    cyclicAlgebraBuildingNormOne_eq_normOne]

/-- Reduced norm on the actual arithmetic-order units, valued in the base
function field. -/
noncomputable def cartwrightStegerOrderBaseReducedNorm
    (P : BasePrime) (r : Rank) :
    (CartwrightStegerOrder P r)ˣ →* (FunctionField P)ˣ :=
  (cyclicAlgebraReducedNorm P r).comp (orderUnitToCyclicUnit P r)

/-- Intrinsic norm-one units of the construction-owned arithmetic order. -/
noncomputable def CartwrightStegerBaseNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    Subgroup ((CartwrightStegerOrder P r)ˣ) :=
  (cartwrightStegerOrderBaseReducedNorm P r).ker

theorem cartwrightStegerNormOneOrderUnits_eq_baseNormOne
    (P : BasePrime) (r : Rank) :
    CartwrightStegerNormOneOrderUnits P r =
      CartwrightStegerBaseNormOneOrderUnits P r := by
  apply SetLike.ext
  intro u
  change cartwrightStegerOrderReducedNorm P r u = 1 ↔
    cartwrightStegerOrderBaseReducedNorm P r u = 1
  change cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) = 1 ↔
    cyclicAlgebraReducedNorm P r (orderUnitToCyclicUnit P r u) = 1
  constructor
  · intro hu
    apply Units.map_injective (functionFieldEmbedding P r).injective
    calc
      Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r (orderUnitToCyclicUnit P r u)) =
        cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) :=
          cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r _
      _ = 1 := hu
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 :=
        (map_one _).symm
  · intro hu
    calc
      cyclicAlgebraSplitReducedNorm P r (orderUnitToCyclicUnit P r u) =
        Units.map (functionFieldEmbedding P r).toMonoidHom
          (cyclicAlgebraReducedNorm P r (orderUnitToCyclicUnit P r u)) :=
            (cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm P r _).symm
      _ = Units.map (functionFieldEmbedding P r).toMonoidHom 1 :=
        congrArg (Units.map (functionFieldEmbedding P r).toMonoidHom) hu
      _ = 1 := map_one _

/-- The split-coordinate integral model maps to the intrinsic base-field
norm-one order units. -/
noncomputable def orderNormOneInnerFormToBaseNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →*
      CartwrightStegerBaseNormOneOrderUnits P r where
  toFun s := ⟨orderNormOneInnerFormToOrderUnits P r s, by
    rw [← cartwrightStegerNormOneOrderUnits_eq_baseNormOne]
    exact orderNormOneInnerFormToOrderUnits_mem_normOne P r s⟩
  map_one' := Subtype.ext (map_one (orderNormOneInnerFormToOrderUnits P r))
  map_mul' s t := Subtype.ext
    (map_mul (orderNormOneInnerFormToOrderUnits P r) s t)

theorem orderNormOneInnerFormToBaseNormOneOrderUnits_injective
    (P : BasePrime) (r : Rank) :
    Function.Injective (orderNormOneInnerFormToBaseNormOneOrderUnits P r) := by
  intro s t hst
  apply orderNormOneInnerFormToOrderUnits_injective P r
  exact congrArg Subtype.val hst

/-- Every intrinsic norm-one unit of the actual arithmetic order has
descended special-linear coordinates. -/
theorem orderNormOneInnerFormToBaseNormOneOrderUnits_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective
      (orderNormOneInnerFormToBaseNormOneOrderUnits P r) := by
  intro u
  obtain ⟨g, hg⟩ := orderInnerFormToOrderUnits_surjective P r u
  have huOld : (u : (CartwrightStegerOrder P r)ˣ) ∈
      CartwrightStegerNormOneOrderUnits P r := by
    rw [cartwrightStegerNormOneOrderUnits_eq_baseNormOne]
    exact u.property
  have huDet : Matrix.GeneralLinearGroup.det
      (orderUnitToGlobalGL P r (u : (CartwrightStegerOrder P r)ˣ)) = 1 :=
    huOld
  have hgMap : Units.map
      (constantArithmeticToSplittingFunctionField P r).toMonoidHom
        (Matrix.GeneralLinearGroup.det
          (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ConstantArithmeticRing P r))) = 1 := by
    calc
      _ = Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map
            (constantArithmeticToSplittingFunctionField P r)
            (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ConstantArithmeticRing P r))) :=
        (Matrix.GeneralLinearGroup.map_det
          (constantArithmeticToSplittingFunctionField P r) _).symm
      _ = Matrix.GeneralLinearGroup.det
          (orderUnitToGlobalGL P r
            (orderInnerFormToOrderUnits P r g)) := by
        apply congrArg Matrix.GeneralLinearGroup.det
        rw [orderUnitToGlobalGL_orderInnerFormToOrderUnits]
        apply Units.ext
        rfl
      _ = Matrix.GeneralLinearGroup.det
          (orderUnitToGlobalGL P r
            (u : (CartwrightStegerOrder P r)ˣ)) := by rw [hg]
      _ = 1 := huDet
  have hgDet : Matrix.GeneralLinearGroup.det
      (g : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) = 1 := by
    apply Units.map_injective
      (constantArithmeticToSplittingFunctionField_injective P r)
    simpa using hgMap
  let gn : OrderInnerFormNormOne P r := ⟨g, hgDet⟩
  let s : OrderNormOneInnerForm P r :=
    (orderNormOneInnerFormEquivFullNormOne P r).symm gn
  refine ⟨s, ?_⟩
  apply Subtype.ext
  rw [← hg]
  apply Units.ext
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.toGL
      ((s : OrderNormOneInnerForm P r) :
        Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ConstantArithmeticRing P r))) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r) =
    (((g : OrderInnerFormUnits P r) :
      Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ConstantArithmeticRing P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r)).map
          (constantArithmeticToSplittingFunctionField P r)
  congr 1

/-- The split-coordinate norm-one integral model and the intrinsic
base-field norm-one units of the actual order are the same group. -/
noncomputable def orderNormOneInnerFormEquivBaseNormOneOrderUnits
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r ≃*
      CartwrightStegerBaseNormOneOrderUnits P r :=
  MulEquiv.ofBijective
    (orderNormOneInnerFormToBaseNormOneOrderUnits P r)
    ⟨orderNormOneInnerFormToBaseNormOneOrderUnits_injective P r,
      orderNormOneInnerFormToBaseNormOneOrderUnits_surjective P r⟩

/-- The split-coordinate model maps directly to the intrinsic global
norm-one subgroup of the cyclic division algebra. -/
noncomputable def orderNormOneInnerFormToCyclicAlgebraNormOne
    (P : BasePrime) (r : Rank) :
    OrderNormOneInnerForm P r →* CyclicAlgebraNormOne P r where
  toFun s := ⟨orderUnitToCyclicUnit P r
      (orderNormOneInnerFormToOrderUnits P r s), by
    change cyclicAlgebraReducedNorm P r
      (orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s)) = 1
    have hs : (orderUnitToCyclicUnit P r
        (orderNormOneInnerFormToOrderUnits P r s)) ∈
        CyclicAlgebraSplitNormOne P r :=
      (orderNormOneInnerFormToCyclicAlgebraSplitNormOne P r s).property
    rw [cyclicAlgebraSplitNormOne_eq_normOne] at hs
    exact hs⟩
  map_one' := Subtype.ext <| by simp
  map_mul' s t := Subtype.ext <| by simp

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
