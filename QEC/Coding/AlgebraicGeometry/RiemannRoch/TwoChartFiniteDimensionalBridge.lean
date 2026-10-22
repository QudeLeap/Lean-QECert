import Mathlib
import QEC.Coding.AlgebraicGeometry.RiemannRoch.DirectChartCommonDenominator
import QEC.Coding.AlgebraicGeometry.Places.InverseAffinePlace
import QEC.Coding.AlgebraicGeometry.RiemannRoch.InverseChartDenominatorTransport
import QEC.Coding.AlgebraicGeometry.RiemannRoch.LaurentFiniteWindow

namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge

open scoped LaurentPolynomial Polynomial RatFunc

variable {k F ι : Type*}

/-- The direct Laurent realization, now as a `k`-linear map. -/
noncomputable def directLaurentLinear (k : Type*) [Field k] :
    LaurentPolynomial k →ₗ[k] RatFunc k where
  toFun := InverseChartDenominatorTransport.directLaurentToRatFunc k
  map_add' := map_add _
  map_smul' := by
    intro c z
    rw [LaurentPolynomial.smul_eq_C_mul]
    rw [map_mul]
    simp [InverseChartDenominatorTransport.directLaurentToRatFunc,
      InverseChartDenominatorTransport.ratFuncXUnit, Algebra.smul_def]

/-- A finite Laurent window, viewed in the direct rational coordinate. -/
noncomputable def directLaurentWindow (k : Type*) [Field k]
    (lower upper : ℤ) : Submodule k (RatFunc k) :=
  LinearMap.range <|
    (directLaurentLinear k).comp
      (LaurentFiniteWindow.laurentWindow k lower upper).subtype

theorem directLaurentWindow_finiteDimensional (k : Type*) [Field k]
    (lower upper : ℤ) :
    FiniteDimensional k (directLaurentWindow k lower upper) := by
  let := LaurentFiniteWindow.laurentWindow_finiteDimensional k lower upper
  exact LinearMap.finiteDimensional_range _

/-- Finitely many basis coordinates in one direct Laurent window. -/
noncomputable def directLaurentWindowCoordinates (k : Type*) [Field k]
    (ι : Type*) (lower upper : ℤ) : Submodule k (ι →₀ RatFunc k) :=
  LinearMap.range <|
    Finsupp.mapRange.linearMap
      (directLaurentWindow k lower upper).subtype

theorem directLaurentWindowCoordinates_finiteDimensional
    (k : Type*) [Field k] [Fintype ι] (lower upper : ℤ) :
    FiniteDimensional k (directLaurentWindowCoordinates k ι lower upper) := by
  let := directLaurentWindow_finiteDimensional k lower upper
  exact LinearMap.finiteDimensional_range _

/-- Scale a genuine rational-function basis coordinate by the direct and
inverse chart denominators, but retain the direct rational coordinate. -/
noncomputable def twoChartScaledCoordinateMap
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) :
    F →ₗ[k] (ι →₀ RatFunc k) where
  toFun := fun x =>
    (algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d)) • b.repr x
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro c x
    ext j
    have hj := congrArg (fun q : ι →₀ RatFunc k => q j)
      ((b.repr.restrictScalars k).map_smul c x)
    simp only [LinearEquiv.restrictScalars_apply, Finsupp.smul_apply,
      Algebra.smul_def] at hj ⊢
    rw [hj]
    ac_rfl

theorem twoChartScaledCoordinateMap_apply
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F) (j : ι) :
    twoChartScaledCoordinateMap b a d x j =
      (algebraMap (Polynomial k) (RatFunc k) a *
        InverseAffinePlace.rationalInvolution k
          (algebraMap (Polynomial k) (RatFunc k) d)) *
        b.repr x j := rfl

/-- The Laurent localization maps injectively into the rational-function
field.  The target map is identified by localization ring-map extensionality
on `k[X]`; its source is `LaurentPolynomial.isLocalization`, its target is
the fraction-field localization, and the only submonoid inclusion sends each
power of `X` to a nonzero polynomial. -/
theorem directLaurentToRatFunc_injective (k : Type*) [Field k] :
    Function.Injective
      (InverseChartDenominatorTransport.directLaurentToRatFunc k) := by
  let M : Submonoid k[X] := Submonoid.powers Polynomial.X
  let N : Submonoid k[X] := nonZeroDivisors k[X]
  have hMN : M ≤ Submonoid.comap (RingHom.id k[X]) N := by
    rintro f ⟨n, rfl⟩
    simp [N]
  let f : LaurentPolynomial k →+* RatFunc k :=
    IsLocalization.map (T := N) (RatFunc k) (RingHom.id k[X]) hMN
  have hf : Function.Injective f :=
    IsLocalization.map_injective_of_injective'
      (R := Polynomial k) (S := Polynomial k) (f := RingHom.id (Polynomial k))
      (Rₘ := LaurentPolynomial k) M (RatFunc k) (N := N) hMN (by simp [N])
      Function.injective_id
  have hmap :
      InverseChartDenominatorTransport.directLaurentToRatFunc k = f := by
    apply IsLocalization.ringHom_ext M
    apply Polynomial.ringHom_ext
    · intro c
      simp [f, InverseChartDenominatorTransport.directLaurentToRatFunc,
        InverseChartDenominatorTransport.ratFuncXUnit]
    · simp [f,
        InverseChartDenominatorTransport.directLaurentToRatFunc,
        InverseChartDenominatorTransport.ratFuncXUnit]
  rw [hmap]
  exact hf

/-- Direct Laurent coordinates of direct polynomials are the ordinary
polynomial image in the rational-function field. -/
theorem directLaurent_directCoordinate
    (k : Type*) [Field k] (p : Polynomial k) :
    InverseChartDenominatorTransport.directLaurentToRatFunc k
      (LaurentFiniteWindow.directCoordinate k p) =
      algebraMap (Polynomial k) (RatFunc k) p := by
  simp only [LaurentFiniteWindow.directCoordinate_apply,
    InverseChartDenominatorTransport.directLaurentToRatFunc,
    LaurentPolynomial.eval₂_toLaurent]
  rw [← Polynomial.aeval_def]
  exact RatFunc.aeval_X_left_eq_algebraMap p

/-- The coordinate of an inverse-polynomial scalar multiplication, stated in
the saved direct basis.  The `change` line unfolds the transported polynomial
map; it is the only point where the two scalar-tower records meet. -/
theorem direct_repr_inverse_polynomial_smul
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [_π : Algebra (Polynomial k) F]
    [_τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (d : Polynomial k) (x : F) (j : ι) :
    let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
    let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
    let oldRepr := oldBasis.repr
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    oldRepr (d • x) j =
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j := by
  dsimp only
  let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
  let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
  let oldRepr := oldBasis.repr
  let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  change oldRepr
      ((@Algebra.algebraMap (RatFunc k) F _ _ ρ)
        (InverseAffinePlace.rationalInvolution k
          (algebraMap (Polynomial k) (RatFunc k) d)) * x) j =
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j
  let r := InverseAffinePlace.rationalInvolution k
    (algebraMap (Polynomial k) (RatFunc k) d)
  let hOld := ρ.smul_def' r x
  calc
    oldRepr ((@Algebra.algebraMap (RatFunc k) F _ _ ρ) r * x) j =
        oldRepr (@SMul.smul (RatFunc k) F oldModule.toSMul r x) j := by
      apply congrArg (fun z : F => oldRepr z j)
      exact hOld.symm
    _ = (r • oldRepr x) j :=
      congrArg (fun c : ι →₀ RatFunc k => c j) (oldRepr.map_smul r x)
    _ = r * oldRepr x j := by
      simp [Finsupp.smul_apply]

/-- A direct-coordinate equality and an inverse-coordinate equality place the
same scaled coordinate in the fixed Laurent exponent window. -/
theorem scaled_coordinate_mem_directLaurentWindow
    [Field k] [Field F] [Algebra k F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F) (j : ι)
    (hdirect : ∃ p : Polynomial k,
      b.repr (a • x) j = algebraMap (Polynomial k) (RatFunc k) p)
    (hinverse :
      let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∃ q : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr (d • x) j) =
          InverseChartDenominatorTransport.directLaurentToRatFunc k
            (InverseChartDenominatorTransport.inverseLaurentCoordinate k q)) :
    twoChartScaledCoordinateMap b a d x j ∈
      directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by
  rcases hdirect with ⟨p, hp⟩
  have hp' : algebraMap (Polynomial k) (RatFunc k) a * b.repr x j =
      algebraMap (Polynomial k) (RatFunc k) p := by
    rw [← _root_.QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.repr_smul_polynomial
      b a x j]
    exact hp
  let oldRepr := b.repr
  obtain ⟨q, hq'⟩ : ∃ q : Polynomial k,
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j =
        InverseChartDenominatorTransport.directLaurentToRatFunc k
          (InverseChartDenominatorTransport.inverseLaurentCoordinate k q) := by
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    rcases hinverse with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j =
          oldRepr (d • x) j :=
        (direct_repr_inverse_polynomial_smul
          (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b d x j).symm
      _ = InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr (d • x) j) := by
        symm
        exact InverseChartDenominatorTransport.inverseBasis_coordinate_to_direct
          (ρ := ρ) (π := π) (τ := τ) (φ := φ) (s := s) b (d • x) j
      _ = _ := hq
  let w : LaurentPolynomial k :=
    LaurentFiniteWindow.directCoordinate k p *
      InverseChartDenominatorTransport.inverseLaurentCoordinate k d
  have hwImage :
      InverseChartDenominatorTransport.directLaurentToRatFunc k w =
        twoChartScaledCoordinateMap b a d x j := by
    calc
      InverseChartDenominatorTransport.directLaurentToRatFunc k w =
          algebraMap (Polynomial k) (RatFunc k) p *
            InverseAffinePlace.rationalInvolution k
              (algebraMap (Polynomial k) (RatFunc k) d) := by
        simp [w, map_mul,
          InverseChartDenominatorTransport.directLaurent_inverseLaurentCoordinate_eq_rationalInvolution,
          directLaurent_directCoordinate]
      _ = _ := by
        rw [twoChartScaledCoordinateMap_apply]
        rw [← hp']
        ac_rfl
  have hwOther : w =
      LaurentFiniteWindow.directCoordinate k a *
        InverseChartDenominatorTransport.inverseLaurentCoordinate k q := by
    apply directLaurentToRatFunc_injective k
    calc
      InverseChartDenominatorTransport.directLaurentToRatFunc k w =
          twoChartScaledCoordinateMap b a d x j := hwImage
      _ = algebraMap (Polynomial k) (RatFunc k) a *
          InverseChartDenominatorTransport.directLaurentToRatFunc k
            (InverseChartDenominatorTransport.inverseLaurentCoordinate k q) := by
        rw [twoChartScaledCoordinateMap_apply, mul_assoc, hq']
      _ = InverseChartDenominatorTransport.directLaurentToRatFunc k
          (LaurentFiniteWindow.directCoordinate k a *
            InverseChartDenominatorTransport.inverseLaurentCoordinate k q) := by
        rw [map_mul, directLaurent_directCoordinate]
  have hw : w ∈ LaurentFiniteWindow.laurentWindow k
      (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by
    change w.coeff.support ⊆ Finset.Icc (-(d.natDegree : ℤ)) (a.natDegree : ℤ)
    intro n hn
    have hlower : n ∈ Finset.Icc (-(d.natDegree : ℤ)) (p.natDegree : ℤ) := by
      apply LaurentFiniteWindow.direct_mul_inverse_support_subset k p d
      simpa only [w, InverseChartDenominatorTransport.inverseLaurentCoordinate,
        LaurentFiniteWindow.inverseCoordinate] using hn
    have hupper : n ∈ Finset.Icc (-(q.natDegree : ℤ)) (a.natDegree : ℤ) := by
      apply LaurentFiniteWindow.direct_mul_inverse_support_subset k a q
      simpa only [hwOther, InverseChartDenominatorTransport.inverseLaurentCoordinate,
        LaurentFiniteWindow.inverseCoordinate] using hn
    rw [Finset.mem_Icc] at hlower hupper ⊢
    exact ⟨hlower.1, hupper.2⟩
  exact ⟨⟨w, hw⟩, hwImage⟩

/-- Coordinatewise membership lifts to the finite direct-Laurent coordinate
space.  Finiteness of `ι` turns the pointwise subtype family into a Finsupp. -/
theorem scaled_coordinates_mem_windowCoordinates
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [Fintype ι]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F)
    (hcoordinate : ∀ j : ι,
      twoChartScaledCoordinateMap b a d x j ∈
        directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ)) :
    twoChartScaledCoordinateMap b a d x ∈
      directLaurentWindowCoordinates k ι (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by
  classical
  let lift : ι →₀ directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ) :=
    (Finsupp.linearEquivFunOnFinite k
      (directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ)) ι).symm
      (fun j => ⟨twoChartScaledCoordinateMap b a d x j, hcoordinate j⟩)
  refine ⟨lift, ?_⟩
  ext j
  simp [lift, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]

/-- The scaled coordinate map is injective when both actual polynomial
denominators are nonzero. -/
theorem twoChartScaledCoordinateMap_injective
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) {a d : Polynomial k} (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Injective (twoChartScaledCoordinateMap b a d) := by
  have haK : algebraMap (Polynomial k) (RatFunc k) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr ha
  have hdK : algebraMap (Polynomial k) (RatFunc k) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hd
  have hc : algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) ≠ 0 :=
    mul_ne_zero haK
      ((map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hdK)
  intro x y hxy
  apply b.repr.injective
  ext j
  have hj := congrArg (fun c : ι →₀ RatFunc k => c j) hxy
  change (algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d)) * b.repr x j =
    (algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d)) * b.repr y j at hj
  exact mul_left_cancel₀ hc hj

/-- The bounded two-chart finite-dimensional bridge.  `L` is an actual
`k`-submodule (the later all-place valuation-bounded submodule is supplied
here only after its chart membership theorem is built).  The two inclusion
certificates target actual finite polynomial submodules, respectively under
the direct and the fully transported inverse action. -/
theorem finiteDimensional_of_twoChart_denominator_certificates
    [Field k] [Field F] [Algebra k F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F)
    (L : Submodule k F) (Λdirect : Submodule (Polynomial k) F)
    [Module.Finite (Polynomial k) Λdirect]
    (hdirectContains : ∀ x : L, (x : F) ∈ Λdirect)
    (hinverseContains :
      let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∃ Λinverse : Submodule (Polynomial k) F,
        Module.Finite (Polynomial k) Λinverse ∧
        ∀ x : L, (x : F) ∈ Λinverse) :
    FiniteDimensional k L := by
  obtain ⟨a, ha, hdirect⟩ :=
    _root_.QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
      (b := b) Λdirect
  let S : Polynomial k → F →ₗ[k] (ι →₀ RatFunc k) :=
    fun d => twoChartScaledCoordinateMap b a d
  have hSinjective : ∀ d : Polynomial k, d ≠ 0 → Function.Injective (S d) := by
    intro d hd
    simpa [S] using twoChartScaledCoordinateMap_injective b ha hd
  obtain ⟨d, hd, hinverseL⟩ : ∃ d : Polynomial k, d ≠ 0 ∧
      (let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∀ x : L, ∀ j : ι, ∃ q : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr
              (d • (x : F)) j) =
            InverseChartDenominatorTransport.directLaurentToRatFunc k
              (InverseChartDenominatorTransport.inverseLaurentCoordinate k q)) := by
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    rcases hinverseContains with ⟨Λinverse, hfiniteInverse, hcontainsInverse⟩
    let : Module.Finite (Polynomial k) Λinverse := hfiniteInverse
    obtain ⟨d, hd, hinverse⟩ :=
      InverseChartDenominatorTransport.exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
          (ρ := ρ) (π := π) (τ := τ) (φ := φ) (s := s) (b := b) Λinverse hfiniteInverse
    refine ⟨d, hd, ?_⟩
    dsimp only
    intro x j
    exact hinverse ⟨x, hcontainsInverse x⟩ j
  let W := directLaurentWindowCoordinates k ι
    (-(d.natDegree : ℤ)) (a.natDegree : ℤ)
  have hS : ∀ x : L, S d x ∈ W := by
    intro x
    change twoChartScaledCoordinateMap b a d x ∈ W
    apply scaled_coordinates_mem_windowCoordinates
    intro j
    apply scaled_coordinate_mem_directLaurentWindow b a d (x : F) j
    · rcases hdirect ⟨x, hdirectContains x⟩ j with ⟨p, hp⟩
      exact ⟨p, hp.symm⟩
    · exact hinverseL x j
  let SL : L →ₗ[k] W :=
    ((S d).comp L.subtype).codRestrict W hS
  have hSL : Function.Injective SL := by
    intro x y hxy
    apply Subtype.ext
    apply hSinjective d hd
    exact congrArg Subtype.val hxy
  let : FiniteDimensional k W :=
    directLaurentWindowCoordinates_finiteDimensional (ι := ι) k
      (-(d.natDegree : ℤ)) (a.natDegree : ℤ)
  exact FiniteDimensional.of_injective (V₂ := W) SL hSL

end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
