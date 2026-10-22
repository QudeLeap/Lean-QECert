import QEC.Coding.AlgebraicGeometry.Towers.QuadraticStepDifferent

/-!
# The iterated quadratic Artin--Schreier refinement

Starting from a normalized simple pole `a`, this file recursively applies the
actual quadratic step `y² + y = a`.  Every successor has degree two, its
distinguished coordinate is again a normalized simple pole, and its local
different exponent is two.

This file supplies the composable four-stage tower used to refine one
degree-sixteen source step.  It does not yet identify the terminal field with
the source-step field or make a normal-closure, genus, divisor, or asymptotic
claim.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

universe u

variable {K : Type u} [Field K] [Algebra F256 K]

private structure QuadraticArtinSchreierTowerLevelData
    (K : Type u) [Field K] [Algebra F256 K] where
  carrier : Type u
  [field : _root_.Field carrier]
  [constantAlgebra : Algebra F256 carrier]
  [baseAlgebra : Algebra K carrier]
  [constantTower : IsScalarTower F256 K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  [separable : Algebra.IsSeparable K carrier]
  place : GlobalPlace F256 carrier
  coordinate : carrier
  coordinate_order : place.order coordinate = -1

@[reducible] private noncomputable def quadraticArtinSchreierTowerBaseData
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierTowerLevelData K where
  carrier := K
  field := inferInstance
  constantAlgebra := inferInstance
  baseAlgebra := inferInstance
  constantTower := inferInstance
  finiteDimensional := inferInstance
  separable := inferInstance
  place := P
  coordinate := a
  coordinate_order := ha

@[reducible] private noncomputable def quadraticArtinSchreierTowerSuccessorData
    (data : QuadraticArtinSchreierTowerLevelData K) :
    QuadraticArtinSchreierTowerLevelData K := by
  letI : _root_.Field data.carrier := data.field
  letI : Algebra F256 data.carrier := data.constantAlgebra
  letI : Algebra K data.carrier := data.baseAlgebra
  letI : IsScalarTower F256 K data.carrier := data.constantTower
  letI : FiniteDimensional K data.carrier := data.finiteDimensional
  letI : Algebra.IsSeparable K data.carrier := data.separable
  let L := QuadraticArtinSchreierField
    data.place data.coordinate data.coordinate_order
  letI : FiniteDimensional K L :=
    FiniteDimensional.trans K data.carrier L
  letI : Algebra.IsSeparable K L :=
    Algebra.IsSeparable.trans K data.carrier L
  exact
    { carrier := L
      field := inferInstance
      constantAlgebra := inferInstance
      baseAlgebra := inferInstance
      constantTower := inferInstance
      finiteDimensional := inferInstance
      separable := inferInstance
      place := quadraticArtinSchreierAbovePlace
        data.place data.coordinate data.coordinate_order
      coordinate := quadraticArtinSchreierCoordinate
        data.place data.coordinate data.coordinate_order
      coordinate_order :=
        quadraticArtinSchreierAbovePlace_order_coordinate
          data.place data.coordinate data.coordinate_order }

@[reducible] private noncomputable def quadraticArtinSchreierTowerLevelData
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    ℕ → QuadraticArtinSchreierTowerLevelData K
  | 0 => quadraticArtinSchreierTowerBaseData P a ha
  | i + 1 => quadraticArtinSchreierTowerSuccessorData
      (quadraticArtinSchreierTowerLevelData P a ha i)

/-- The actual field at level `i` of the quadratic refinement. -/
abbrev QuadraticArtinSchreierTowerField
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) : Type u :=
  (quadraticArtinSchreierTowerLevelData P a ha i).carrier

noncomputable instance quadraticArtinSchreierTowerFieldField
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    _root_.Field (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).field

noncomputable instance quadraticArtinSchreierTowerFieldConstantAlgebra
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Algebra F256 (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).constantAlgebra

noncomputable instance quadraticArtinSchreierTowerFieldBaseAlgebra
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Algebra K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).baseAlgebra

noncomputable instance quadraticArtinSchreierTowerFieldConstantTower
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    IsScalarTower F256 K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).constantTower

noncomputable instance quadraticArtinSchreierTowerFieldFiniteDimensional
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    FiniteDimensional K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).finiteDimensional

noncomputable instance quadraticArtinSchreierTowerFieldSeparable
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Algebra.IsSeparable K (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).separable

/-- The recursively chosen normalized place. -/
noncomputable def quadraticArtinSchreierTowerPlace
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    GlobalPlace F256 (QuadraticArtinSchreierTowerField P a ha i) :=
  (quadraticArtinSchreierTowerLevelData P a ha i).place

/-- The recursively chosen Artin--Schreier coordinate. -/
noncomputable def quadraticArtinSchreierTowerCoordinate
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    QuadraticArtinSchreierTowerField P a ha i :=
  (quadraticArtinSchreierTowerLevelData P a ha i).coordinate

theorem quadraticArtinSchreierTowerCoordinate_order
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    (quadraticArtinSchreierTowerPlace P a ha i).order
      (quadraticArtinSchreierTowerCoordinate P a ha i) = -1 :=
  (quadraticArtinSchreierTowerLevelData P a ha i).coordinate_order

/-- The literal embedding of one quadratic level into the next. -/
noncomputable def quadraticArtinSchreierTowerEmbedding
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    QuadraticArtinSchreierTowerField P a ha i →ₐ[F256]
      QuadraticArtinSchreierTowerField P a ha (i + 1) :=
  quadraticArtinSchreierEmbedding
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)

/-- Every successor in the refinement has degree two. -/
theorem quadraticArtinSchreierTowerStep_finrank
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Module.finrank
      (QuadraticArtinSchreierTowerField P a ha i)
      (QuadraticArtinSchreierTowerField P a ha (i + 1)) = 2 :=
  quadraticArtinSchreier_finrank
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)

/-- Level `i` has degree `2^i` over the starting field. -/
theorem quadraticArtinSchreierTower_finrank
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Module.finrank K (QuadraticArtinSchreierTowerField P a ha i) = 2 ^ i := by
  induction i with
  | zero =>
      change Module.finrank K K = 1
      simp
  | succ i ih =>
      letI : IsScalarTower K
          (QuadraticArtinSchreierTowerField P a ha i)
          (QuadraticArtinSchreierTowerField P a ha (i + 1)) :=
        IsScalarTower.of_algebraMap_eq' rfl
      calc
        Module.finrank K (QuadraticArtinSchreierTowerField P a ha (i + 1)) =
            Module.finrank K (QuadraticArtinSchreierTowerField P a ha i) *
              Module.finrank (QuadraticArtinSchreierTowerField P a ha i)
                (QuadraticArtinSchreierTowerField P a ha (i + 1)) :=
          (Module.finrank_mul_finrank K
            (QuadraticArtinSchreierTowerField P a ha i)
            (QuadraticArtinSchreierTowerField P a ha (i + 1))).symm
        _ = 2 ^ i * 2 := by
          rw [ih, quadraticArtinSchreierTowerStep_finrank]
        _ = 2 ^ (i + 1) := by rw [pow_succ]

/-- The literal quadratic equation at every successor. -/
theorem quadraticArtinSchreierTower_equation
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    quadraticArtinSchreierTowerCoordinate P a ha (i + 1) ^ 2 +
        quadraticArtinSchreierTowerCoordinate P a ha (i + 1) =
      quadraticArtinSchreierTowerEmbedding P a ha i
        (quadraticArtinSchreierTowerCoordinate P a ha i) :=
  quadraticArtinSchreierCoordinate_equation
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)

/-- Every actual local successor has different exponent two. -/
theorem quadraticArtinSchreierTowerStepDifferent_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    multiplicity
        (quadraticArtinSchreierUpperIdeal
          (quadraticArtinSchreierTowerPlace P a ha i)
          (quadraticArtinSchreierTowerCoordinate P a ha i)
          (quadraticArtinSchreierTowerCoordinate_order P a ha i))
        (differentIdeal
          (quadraticArtinSchreierTowerPlace P a ha i).valuationRing
          (QuadraticArtinSchreierIntegralClosure
            (quadraticArtinSchreierTowerPlace P a ha i)
            (quadraticArtinSchreierTowerCoordinate P a ha i)
            (quadraticArtinSchreierTowerCoordinate_order P a ha i))) = 2 :=
  quadraticArtinSchreierDifferentIdeal_multiplicity
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
