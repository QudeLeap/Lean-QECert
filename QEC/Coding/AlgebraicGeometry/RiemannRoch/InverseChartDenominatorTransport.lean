import Mathlib.Algebra.Polynomial.Laurent
import QEC.Coding.AlgebraicGeometry.RiemannRoch.DirectChartCommonDenominator
import QEC.Coding.AlgebraicGeometry.Places.InverseAffinePlace

namespace QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport

open scoped LaurentPolynomial Polynomial RatFunc

variable {k F ι : Type*}

/-- The actual unit selected by the nonzero rational coordinate. -/
noncomputable def ratFuncXUnit (k : Type*) [Field k] : (RatFunc k)ˣ :=
  Units.mk0 RatFunc.X RatFunc.X_ne_zero

/-- Evaluate a Laurent polynomial in the direct rational coordinate. -/
noncomputable def directLaurentToRatFunc (k : Type*) [Field k] :
    LaurentPolynomial k →+* RatFunc k :=
  LaurentPolynomial.eval₂ (algebraMap k (RatFunc k)) (ratFuncXUnit k)

/-- The inverse polynomial coordinate is the actual Laurent inversion after
the installed polynomial-to-Laurent map. -/
noncomputable def inverseLaurentCoordinate (k : Type*) [Field k] :
    k[X] →ₐ[k] LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toAlgHom.comp Polynomial.toLaurentAlg

/-- The direct rational realization of the inverse Laurent coordinate. -/
noncomputable def inverseLaurentToRatFunc (k : Type*) [Field k] :
    k[X] →+* RatFunc k :=
  (directLaurentToRatFunc k).comp (inverseLaurentCoordinate k).toRingHom

/-- The rational involution, restricted along the ordinary polynomial chart. -/
noncomputable def rationalInvolutionOnPolynomial (k : Type*) [Field k] :
    k[X] →+* RatFunc k :=
  (InverseAffinePlace.rationalInvolution k).toRingHom.comp
    (algebraMap k[X] (RatFunc k))

/-- The two concrete rational maps agree.  The proof is deliberately by
polynomial-ring extensionality: constants use the algebra-map laws, while the
single generator uses `rationalInvolution_X`, `invert_T`, and `eval₂_T`. -/
theorem inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial
    (k : Type*) [Field k] :
    inverseLaurentToRatFunc k = rationalInvolutionOnPolynomial k := by
  apply Polynomial.ringHom_ext
  · intro c
    simpa [inverseLaurentToRatFunc, rationalInvolutionOnPolynomial,
      directLaurentToRatFunc, inverseLaurentCoordinate, ratFuncXUnit]
      using ((InverseAffinePlace.rationalInvolution k).commutes c).symm
  · simpa [inverseLaurentToRatFunc, rationalInvolutionOnPolynomial,
      directLaurentToRatFunc, inverseLaurentCoordinate, ratFuncXUnit]
      using (InverseAffinePlace.rationalInvolution_X k).symm

/-- Pointwise form of the constructed Laurent/rational bridge. -/
theorem directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
    (k : Type*) [Field k] (p : k[X]) :
    directLaurentToRatFunc k (inverseLaurentCoordinate k p) =
      InverseAffinePlace.rationalInvolution k (algebraMap k[X] (RatFunc k) p) := by
  change inverseLaurentToRatFunc k p = rationalInvolutionOnPolynomial k p
  rw [inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial]

/-- Change coefficients from the outer direct rational action to the inverse
transported action.  The vectors stay the given vectors; only their coordinate
scalars are transported by the constructed rational involution. -/
noncomputable def inverseBasis
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [_π : Algebra (Polynomial k) F]
    [_τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) :
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    Module.Basis ι (RatFunc k) F := by
  let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
  let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
  let transportedAlg : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (RatFunc k) F := transportedAlg
  let newModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _
    transportedAlg
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower (k := k) (F := F)
      (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  exact @Module.Basis.mapCoeffs ι (RatFunc k) F _ _ oldModule oldBasis
    (RatFunc k) _ newModule (InverseAffinePlace.rationalInvolution k).toRingEquiv.symm (by
      intro c x
      let hNew := transportedAlg.smul_def' ((InverseAffinePlace.rationalInvolution k).symm c) x
      let hOld := ρ.smul_def' c x
      change @SMul.smul (RatFunc k) F newModule.toSMul
          ((InverseAffinePlace.rationalInvolution k).symm c) x =
        @SMul.smul (RatFunc k) F oldModule.toSMul c x
      calc
        @SMul.smul (RatFunc k) F newModule.toSMul
            ((InverseAffinePlace.rationalInvolution k).symm c) x =
            (@Algebra.algebraMap (RatFunc k) F _ _ transportedAlg)
              ((InverseAffinePlace.rationalInvolution k).symm c) * x :=
          hNew
        _ = (@Algebra.algebraMap (RatFunc k) F _ _ ρ) c * x := by
          apply congrArg (fun z : F => z * x)
          change InverseAffinePlace.transportedRationalMap
              (k := k) (F := F) (oldRationalAlgebra := ρ)
              ((InverseAffinePlace.rationalInvolution k).symm c) =
            (@Algebra.algebraMap (RatFunc k) F _ _ ρ) c
          simp [InverseAffinePlace.transportedRationalMap]
        _ = @SMul.smul (RatFunc k) F oldModule.toSMul c x :=
          hOld.symm)

/-- Inverse-basis coordinates, transported back by the actual involution, are
the original direct coordinates.  This unfolds `Basis.mapCoeffs` and its
`Finsupp.mapRange.linearEquiv` coordinate transport. -/
theorem inverseBasis_coordinate_to_direct
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) :
    let oldRepr := b.repr
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    ∀ x : F, ∀ j : ι,
      InverseAffinePlace.rationalInvolution k
        ((inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr x j) =
        oldRepr x j := by
  dsimp only
  let oldRepr := b.repr
  let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower (k := k) (F := F)
      (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  intro x j
  simp [inverseBasis, Module.Basis.mapCoeffs, Finsupp.mapRange_apply]
  change InverseAffinePlace.rationalInvolution k
      ((InverseAffinePlace.rationalInvolution k).symm (oldRepr x j)) =
    oldRepr x j
  exact (InverseAffinePlace.rationalInvolution k).apply_symm_apply _

/-- Transport the already constructed direct common-denominator result through
the exact inverse chart.  It stops at inverse Laurent-coordinate containment;
no intersection or finite-dimensional conclusion is used here. -/
theorem exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F) :
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    ∀ (L : Submodule (Polynomial k) F), Module.Finite (Polynomial k) L →
      ∃ a : Polynomial k, a ≠ 0 ∧ ∀ x : L, ∀ j : ι, ∃ p : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr
            (a • (x : F)) j) =
          directLaurentToRatFunc k (inverseLaurentCoordinate k p) := by
  let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower (k := k) (F := F)
      (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  dsimp only
  intro L hfinite
  let : Module.Finite (Polynomial k) L := hfinite
  obtain ⟨a, ha, hcoordinates⟩ :=
    QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
      (b := inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b) L
  refine ⟨a, ha, ?_⟩
  intro x j
  rcases hcoordinates x j with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [← hp]
  exact
    (directLaurent_inverseLaurentCoordinate_eq_rationalInvolution k p).symm

end QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
