import QEC.Coding.HighDimensionalExpander.Combinatorics.BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Spherical adjacency operators on the universal affine building

This file realizes every fundamental colored adjacency as an actual bounded
operator on the Hilbert space of square-summable functions on building
vertices.  The construction is by a finite sum of left-regular translations,
so boundedness follows before any spectral classification is invoked.
-/

noncomputable section

namespace QEC.Coding.HighDimensionalExpander.SphericalHecke

open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory

universe u v

/-! ### Haar reduction to the finite building-neighbour sum

These two lemmas are the only analytic bridge used below from the former
`SphericalHeckeEigenvalue` module.  Keeping them here avoids restoring the
principal-series classification chain merely to construct the universal
building operators. -/

/-- A quotient fiber is an actual compact right coset of the maximal compact
subgroup. -/
theorem quotientFiber_isCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (q : BuildingVertex k d) :
    IsCompact
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}) := by
  rw [quotientFiber_eq_preimage_left_mul]
  have heq :
      (fun x : HeckeGroup k d => q.out⁻¹ * x) ⁻¹'
          (maximalCompact k d : Set (HeckeGroup k d)) =
        (fun y : HeckeGroup k d => q.out * y) ''
          (maximalCompact k d : Set (HeckeGroup k d)) := by
    ext x
    constructor
    · intro hx
      refine ⟨q.out⁻¹ * x, hx, ?_⟩
      group
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  exact (maximalCompact_isCompact k d).image
    (continuous_const.mul continuous_id)

/-- Haar integration over a fundamental double coset is exactly the finite
sum over the construction-owned neighbouring right cosets. -/
theorem setIntegral_fundamentalDoubleCoset_eq_sum_neighbors
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (F : HeckeGroup k d → ℂ) (hF : Continuous F)
    (hK : ∀ g q : HeckeGroup k d, q ∈ maximalCompact k d →
      F (g * q) = F g) :
    ∫ x in fundamentalDoubleCoset k d r, F x
        ∂normalizedLocalHaarMeasure k d =
      ∑ q ∈ fundamentalNeighborCosets k d r, F q.out := by
  rw [fundamentalDoubleCoset_eq_biUnion_quotientFiber]
  rw [integral_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro q hq
    let μ := normalizedLocalHaarMeasure k d
    let fiber : Set (HeckeGroup k d) :=
      (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}
    have hfiber : MeasurableSet fiber := by
      dsimp only [fiber]
      rw [quotientFiber_eq_preimage_left_mul]
      exact (maximalCompact_isOpen k d).measurableSet.preimage
        (measurable_const_mul q.out⁻¹)
    have hpointwise :
        (fun x => fiber.indicator F (q.out * x)) =
          (fun x => (maximalCompact k d : Set (HeckeGroup k d)).indicator
            (fun _ => F q.out) x) := by
      funext x
      have hmem : q.out * x ∈ fiber ↔ x ∈ maximalCompact k d := by
        dsimp only [fiber]
        rw [quotientFiber_eq_preimage_left_mul]
        simp
      by_cases hx : x ∈ maximalCompact k d
      · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx,
          hK q.out x hx]
      · rw [Set.indicator_of_notMem (not_congr hmem |>.mpr hx),
          Set.indicator_of_notMem hx]
    calc
      ∫ x in fiber, F x ∂μ = ∫ x, fiber.indicator F x ∂μ := by
        rw [integral_indicator hfiber]
      _ = ∫ x, fiber.indicator F (q.out * x) ∂μ :=
        (integral_mul_left_eq_self (fiber.indicator F) q.out).symm
      _ = ∫ x, (maximalCompact k d : Set (HeckeGroup k d)).indicator
          (fun _ => F q.out) x ∂μ := by rw [hpointwise]
      _ = ∫ x in (maximalCompact k d : Set (HeckeGroup k d)),
          F q.out ∂μ := by
        rw [integral_indicator (maximalCompact_isOpen k d).measurableSet]
      _ = F q.out := by
        rw [setIntegral_const]
        change (normalizedLocalHaarMeasure k d).real
            (maximalCompact k d : Set (HeckeGroup k d)) • F q.out = F q.out
        rw [Measure.real, normalizedLocalHaarMeasure_maximalCompact,
          ENNReal.toReal_one, one_smul]
  · intro q hq
    rw [quotientFiber_eq_preimage_left_mul]
    exact (maximalCompact_isOpen k d).measurableSet.preimage
      (measurable_const_mul q.out⁻¹)
  · intro a ha b hb hab
    change Disjoint
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {a})
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {b})
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  · intro q hq
    exact hF.continuousOn.integrableOn_compact
      (quotientFiber_isCompact k d q)

/-- Reindexing square-summable complex functions along an equivalence is a
linear isometry. -/
noncomputable def l2ReindexLinearIsometry {α : Type u} {β : Type v}
    (e : α ≃ β) :
    lp (fun _ : α ↦ ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : β ↦ ℂ) 2 where
  toFun f := ⟨fun b ↦ f (e.symm b), by
    show Memℓp (fun b ↦ f (e.symm b)) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  map_add' f g := by
    apply lp.ext
    funext b
    rfl
  map_smul' c f := by
    apply lp.ext
    funext b
    rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun a ↦ ‖f a‖ ^ ((2 : ℝ≥0∞).toReal))

@[simp]
theorem l2ReindexLinearIsometry_apply {α : Type u} {β : Type v}
    (e : α ≃ β) (f : lp (fun _ : α ↦ ℂ) 2) (b : β) :
    l2ReindexLinearIsometry e f b = f (e.symm b) :=
  rfl

/-- The Hilbert space of square-summable complex functions on the vertices of
the universal affine building. -/
abbrev BuildingL2 (k : Type u) [Field k] [Finite k] (d : ℕ) :=
  lp (fun _ : BuildingVertex k d ↦ ℂ) 2

/-- The left-regular action of the local projective linear group on building
`ℓ²`: `(L_g f)(x) = f(g⁻¹ • x)`. -/
noncomputable def buildingL2Translation
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) :
    BuildingL2 k d →ₗᵢ[ℂ] BuildingL2 k d :=
  l2ReindexLinearIsometry (MulAction.toPerm g)

@[simp]
theorem buildingL2Translation_apply
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) (f : BuildingL2 k d)
    (x : BuildingVertex k d) :
    buildingL2Translation k d g f x = f (g⁻¹ • x) := by
  rfl

/-- The chosen representative of a building vertex carries the base vertex
back to that vertex. -/
@[simp]
theorem buildingVertex_out_smul_base
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (x : BuildingVertex k d) :
    x.out • (QuotientGroup.mk 1 : BuildingVertex k d) = x := by
  rw [MulAction.Quotient.smul_mk]
  change QuotientGroup.mk (x.out * 1) = x
  simpa only [mul_one] using x.out_eq'

/-- The constructed finite fundamental right-cosets enumerate exactly the
color-`r` neighbors of every building vertex. -/
noncomputable def fundamentalNeighborAdjacentEquiv
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    {q // q ∈ fundamentalNeighborCosets k d r} ≃
      {y // ColoredBuildingAdjacent k d r x y} where
  toFun q := ⟨x.out • q.1, by
    have hbase := (fundamentalNeighborAdjacentBaseEquiv k d r q).2
    have hsmul := (coloredBuildingAdjacent_smul_iff k d r x.out
      (QuotientGroup.mk 1 : BuildingVertex k d) q.1).2 hbase
    simpa only [buildingVertex_out_smul_base] using hsmul⟩
  invFun y := ⟨x.out⁻¹ • y.1, by
    have hsmul := (coloredBuildingAdjacent_smul_iff k d r x.out⁻¹
      x y.1).2 y.2
    have hbase : x.out⁻¹ • x =
        (QuotientGroup.mk 1 : BuildingVertex k d) := by
      calc
        x.out⁻¹ • x = x.out⁻¹ •
            (x.out • (QuotientGroup.mk 1 : BuildingVertex k d)) := by
          exact congrArg (fun z : BuildingVertex k d ↦ x.out⁻¹ • z)
            (buildingVertex_out_smul_base k d x).symm
        _ = QuotientGroup.mk 1 :=
          inv_smul_smul x.out (QuotientGroup.mk 1 : BuildingVertex k d)
    have hadj : ColoredBuildingAdjacent k d r
        (QuotientGroup.mk 1) (x.out⁻¹ • y.1) := by
      exact hbase ▸ hsmul
    exact (fundamentalNeighborAdjacentBaseEquiv k d r).symm
      ⟨x.out⁻¹ • y.1, hadj⟩ |>.2⟩
  left_inv q := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- Every colored neighbor fiber is finite, by the explicit transported
fundamental-coset enumeration. -/
noncomputable instance coloredBuildingNeighborFintype
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    Fintype {y // ColoredBuildingAdjacent k d r x y} :=
  Fintype.ofEquiv {q // q ∈ fundamentalNeighborCosets k d r}
    (fundamentalNeighborAdjacentEquiv k d r x)

/-- Every vertex has exactly the constructed color-`r` degree. -/
theorem card_coloredBuildingNeighbors
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    Fintype.card {y // ColoredBuildingAdjacent k d r x y} =
      coloredAdjacencyDegree k d r := by
  rw [← Fintype.card_congr (fundamentalNeighborAdjacentEquiv k d r x)]
  simp [coloredAdjacencyDegree]

/-- Reversing a colored edge changes its color according to inversion of the
corresponding fundamental double coset. -/
theorem coloredBuildingAdjacent_reverse_iff_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (x y : BuildingVertex k d) :
    ColoredBuildingAdjacent k d r x y ↔
      ColoredBuildingAdjacent k d s y x := by
  constructor
  · rintro ⟨gx, gy, rfl, rfl, hxy⟩
    refine ⟨gy, gx, rfl, rfl, ?_⟩
    have hinv : (gx⁻¹ * gy)⁻¹ ∈
        (fundamentalDoubleCoset k d r)⁻¹ := by
      simpa
    rw [hset] at hinv
    simpa using hinv
  · rintro ⟨gy, gx, rfl, rfl, hyx⟩
    refine ⟨gx, gy, rfl, rfl, ?_⟩
    have hinv : (gy⁻¹ * gx)⁻¹ ∈
        (fundamentalDoubleCoset k d s)⁻¹ := by
      simpa
    have hsetInv : (fundamentalDoubleCoset k d s)⁻¹ =
        fundamentalDoubleCoset k d r := by
      rw [← hset]
      simp
    rw [hsetInv] at hinv
    simpa using hinv

/-- The raw graph-theoretic color adjacency sum.  Its index is the actual
neighbor relation, so no representative or inverse convention is hidden in
the definition. -/
noncomputable def buildingColoredNeighborSum
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingVertex k d → ℂ) (x : BuildingVertex k d) : ℂ :=
  ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y

/-- Directed color-`r` edges, retaining both their source and target. -/
abbrev ColoredBuildingEdge
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :=
  Σ x : BuildingVertex k d,
    {y // ColoredBuildingAdjacent k d r x y}

/-- Edge reversal is an equivalence when inversion exchanges the two Cartan
double cosets. -/
noncomputable def coloredBuildingEdgeReverseEquiv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    ColoredBuildingEdge k d r ≃ ColoredBuildingEdge k d s where
  toFun e := ⟨e.2.1, ⟨e.1,
    (coloredBuildingAdjacent_reverse_iff_of_inv
      k d r s hset e.1 e.2.1).1 e.2.2⟩⟩
  invFun e := ⟨e.2.1, ⟨e.1,
    (coloredBuildingAdjacent_reverse_iff_of_inv
      k d r s hset e.2.1 e.1).2 e.2.2⟩⟩
  left_inv e := by
    rcases e with ⟨x, ⟨y, hy⟩⟩
    rfl
  right_inv e := by
    rcases e with ⟨x, ⟨y, hy⟩⟩
    rfl

/-- Square norms pulled back from the source are summable over a finite-degree
colored edge space. -/
theorem summable_norm_sq_coloredBuildingEdge_source
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦ ‖f e.1‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ sq_nonneg _)]
  constructor
  · intro x
    exact Summable.of_finite
  · have hf : Summable (fun x : BuildingVertex k d ↦ ‖f x‖ ^ 2) := by
      simpa using (lp.memℓp f).summable (by norm_num)
    have hfun : (fun x : BuildingVertex k d ↦
        ∑' _y : {y // ColoredBuildingAdjacent k d r x y}, ‖f x‖ ^ 2) =
        fun x ↦ (coloredAdjacencyDegree k d r : ℝ) * ‖f x‖ ^ 2 := by
      funext x
      rw [tsum_fintype]
      simp [card_coloredBuildingNeighbors]
    rw [hfun]
    exact hf.mul_left _

/-- Counting a source-weight once for every outgoing edge gives the colored
degree times the vertex `ℓ²` norm. -/
theorem tsum_norm_sq_coloredBuildingEdge_source
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingL2 k d) :
    (∑' e : ColoredBuildingEdge k d r, ‖f e.1‖ ^ 2) =
      (coloredAdjacencyDegree k d r : ℝ) * ‖f‖ ^ 2 := by
  rw [(summable_norm_sq_coloredBuildingEdge_source k d r f).tsum_sigma]
  simp_rw [tsum_fintype]
  have hinner : (fun x : BuildingVertex k d ↦
      ∑ _y : {y // ColoredBuildingAdjacent k d r x y}, ‖f x‖ ^ 2) =
      fun x ↦ (coloredAdjacencyDegree k d r : ℝ) * ‖f x‖ ^ 2 := by
    funext x
    simp [card_coloredBuildingNeighbors]
  rw [hinner, tsum_mul_left]
  congr 1
  simpa using (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f).symm

/-- Square norms pulled back from the target are summable as soon as the
reverse color is a fundamental Cartan color. -/
theorem summable_norm_sq_coloredBuildingEdge_target_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦ ‖f e.2.1‖ ^ 2) := by
  let e := coloredBuildingEdgeReverseEquiv k d r s hset
  have hs := summable_norm_sq_coloredBuildingEdge_source k d s f
  exact (e.summable_iff.mpr hs).congr (fun _ => rfl)

/-- Counting a target-weight over color `r` is counting a source-weight over
the reverse color `s`. -/
theorem tsum_norm_sq_coloredBuildingEdge_target_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    (∑' e : ColoredBuildingEdge k d r, ‖f e.2.1‖ ^ 2) =
      (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 := by
  let e := coloredBuildingEdgeReverseEquiv k d r s hset
  calc
    (∑' a : ColoredBuildingEdge k d r, ‖f a.2.1‖ ^ 2) =
        ∑' b : ColoredBuildingEdge k d s, ‖f b.1‖ ^ 2 := by
      simpa [e, coloredBuildingEdgeReverseEquiv] using
        (e.tsum_eq (fun b : ColoredBuildingEdge k d s ↦ ‖f b.1‖ ^ 2))
    _ = (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 :=
      tsum_norm_sq_coloredBuildingEdge_source k d s f

/-- Pointwise Cauchy--Schwarz for the actual finite neighbor sum. -/
theorem norm_buildingColoredNeighborSum_sq_le
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingVertex k d → ℂ) (x : BuildingVertex k d) :
    ‖buildingColoredNeighborSum k d r f x‖ ^ 2 ≤
      (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
  calc
    ‖buildingColoredNeighborSum k d r f x‖ ^ 2 ≤
        (∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (Fintype.card {y // ColoredBuildingAdjacent k d r x y} : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun y : {y // ColoredBuildingAdjacent k d r x y} ↦ ‖f y‖))
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
      rw [card_coloredBuildingNeighbors]

/-- The actual graph-neighbor sum of an `ℓ²` vector is again square summable.
The proof double-counts directed edges using the reverse Cartan color. -/
theorem buildingColoredNeighborSum_memLp_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    Memℓp (buildingColoredNeighborSum k d r f) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hedge :=
    summable_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f
  have houter : Summable (fun x : BuildingVertex k d ↦
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) := by
    have hsigma := (summable_sigma_of_nonneg
      (f := fun e : ColoredBuildingEdge k d r ↦ ‖f e.2.1‖ ^ 2)
      (fun _ ↦ sq_nonneg _)).mp hedge
    simpa only [tsum_fintype] using hsigma.2
  have hmajor : Summable (fun x : BuildingVertex k d ↦
      (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) :=
    houter.mul_left _
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    hmajor.of_nonneg_of_le
    (fun x ↦ sq_nonneg _)
    (fun x ↦ norm_buildingColoredNeighborSum_sq_le k d r f x)

/-- The graph-theoretic color adjacency linear map on universal-building
`ℓ²`, constructed without choosing neighbor representatives. -/
noncomputable def buildingColoredAdjacencyLinearMapOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    BuildingL2 k d →ₗ[ℂ] BuildingL2 k d where
  toFun f := ⟨buildingColoredNeighborSum k d r f,
    buildingColoredNeighborSum_memLp_of_inv k d r s hset f⟩
  map_add' f g := by
    apply lp.ext
    funext x
    change (∑ y : {y // ColoredBuildingAdjacent k d r x y},
      (f y + g y)) =
        (∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y) +
          ∑ y : {y // ColoredBuildingAdjacent k d r x y}, g y
    exact Finset.sum_add_distrib
  map_smul' c f := by
    apply lp.ext
    funext x
    change (∑ y : {y // ColoredBuildingAdjacent k d r x y},
      c * f y) = c * ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y
    rw [Finset.mul_sum]

@[simp]
theorem buildingColoredAdjacencyLinearMapOfInv_apply_apply
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) (x : BuildingVertex k d) :
    buildingColoredAdjacencyLinearMapOfInv k d r s hset f x =
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y :=
  rfl

/-- The global `ℓ²` estimate obtained from pointwise Cauchy--Schwarz and
reverse-edge double counting. -/
theorem norm_buildingColoredAdjacencyLinearMapOfInv_sq_le
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    ‖buildingColoredAdjacencyLinearMapOfInv k d r s hset f‖ ^ 2 ≤
      (coloredAdjacencyDegree k d r : ℝ) *
        (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 := by
  let A := buildingColoredAdjacencyLinearMapOfInv k d r s hset
  have hout : Summable (fun x : BuildingVertex k d ↦ ‖A f x‖ ^ 2) := by
    simpa using (lp.memℓp (A f)).summable (by norm_num)
  have hedge :=
    summable_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f
  have houter : Summable (fun x : BuildingVertex k d ↦
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) := by
    have hsigma := (summable_sigma_of_nonneg
      (f := fun e : ColoredBuildingEdge k d r ↦ ‖f e.2.1‖ ^ 2)
      (fun _ ↦ sq_nonneg _)).mp hedge
    simpa only [tsum_fintype] using hsigma.2
  have hmajor : Summable (fun x : BuildingVertex k d ↦
      (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) :=
    houter.mul_left _
  calc
    ‖A f‖ ^ 2 = ∑' x : BuildingVertex k d, ‖A f x‖ ^ 2 := by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (A f)
    _ ≤ ∑' x : BuildingVertex k d,
        (coloredAdjacencyDegree k d r : ℝ) *
          ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
      exact hout.tsum_le_tsum
        (fun x ↦ norm_buildingColoredNeighborSum_sq_le k d r f x) hmajor
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        ∑' e : ColoredBuildingEdge k d r, ‖f e.2.1‖ ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact (hedge.tsum_sigma.trans (tsum_congr fun x ↦ by
        rw [tsum_fintype])).symm
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        ((coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2) := by
      rw [tsum_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f]
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 := by ring

/-- Consequently the graph adjacency linear map has operator bound
`sqrt(deg r * deg s)`. -/
theorem norm_buildingColoredAdjacencyLinearMapOfInv_le
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    ‖buildingColoredAdjacencyLinearMapOfInv k d r s hset f‖ ≤
      Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
        coloredAdjacencyDegree k d s) * ‖f‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)), mul_pow,
    Real.sq_sqrt (mul_nonneg (by positivity) (by positivity))]
  exact norm_buildingColoredAdjacencyLinearMapOfInv_sq_le
    k d r s hset f

/-- The bounded graph-theoretic color adjacency operator on universal-building
`ℓ²`. -/
noncomputable def buildingColoredAdjacencyOperatorOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    BuildingL2 k d →L[ℂ] BuildingL2 k d :=
  (buildingColoredAdjacencyLinearMapOfInv k d r s hset).mkContinuous
    (Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
      coloredAdjacencyDegree k d s))
    (norm_buildingColoredAdjacencyLinearMapOfInv_le k d r s hset)

@[simp]
theorem buildingColoredAdjacencyOperatorOfInv_apply_apply
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) (x : BuildingVertex k d) :
    buildingColoredAdjacencyOperatorOfInv k d r s hset f x =
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y :=
  rfl

/-- Operator-norm form of the reverse-degree bound. -/
theorem norm_buildingColoredAdjacencyOperatorOfInv_le
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    ‖buildingColoredAdjacencyOperatorOfInv k d r s hset‖ ≤
      Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
        coloredAdjacencyDegree k d s) := by
  exact (buildingColoredAdjacencyLinearMapOfInv k d r s hset).mkContinuous_norm_le
    (Real.sqrt_nonneg _)
    (norm_buildingColoredAdjacencyLinearMapOfInv_le k d r s hset)

/-! ### The five actual rank-three/rank-four color operators -/

noncomputable def rankThreeBuildingAdjacencyOne
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 3 →L[ℂ] BuildingL2 k 3 :=
  buildingColoredAdjacencyOperatorOfInv k 3 1 2
    (fundamentalDoubleCoset_rankThree_one_inv k)

noncomputable def rankThreeBuildingAdjacencyTwo
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 3 →L[ℂ] BuildingL2 k 3 :=
  buildingColoredAdjacencyOperatorOfInv k 3 2 1
    (fundamentalDoubleCoset_rankThree_two_inv k)

noncomputable def rankFourBuildingAdjacencyOne
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 4 →L[ℂ] BuildingL2 k 4 :=
  buildingColoredAdjacencyOperatorOfInv k 4 1 3
    (fundamentalDoubleCoset_rankFour_one_inv k)

noncomputable def rankFourBuildingAdjacencyTwo
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 4 →L[ℂ] BuildingL2 k 4 :=
  buildingColoredAdjacencyOperatorOfInv k 4 2 2
    (fundamentalDoubleCoset_rankFour_two_inv k)

noncomputable def rankFourBuildingAdjacencyThree
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 4 →L[ℂ] BuildingL2 k 4 :=
  buildingColoredAdjacencyOperatorOfInv k 4 3 1
    (fundamentalDoubleCoset_rankFour_three_inv k)

@[simp]
theorem rankThreeBuildingAdjacencyOne_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 3) (x : BuildingVertex k 3) :
    rankThreeBuildingAdjacencyOne k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 3 1 x y}, f y :=
  rfl

@[simp]
theorem rankThreeBuildingAdjacencyTwo_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 3) (x : BuildingVertex k 3) :
    rankThreeBuildingAdjacencyTwo k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 3 2 x y}, f y :=
  rfl

@[simp]
theorem rankFourBuildingAdjacencyOne_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 4) (x : BuildingVertex k 4) :
    rankFourBuildingAdjacencyOne k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 4 1 x y}, f y :=
  rfl

@[simp]
theorem rankFourBuildingAdjacencyTwo_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 4) (x : BuildingVertex k 4) :
    rankFourBuildingAdjacencyTwo k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 4 2 x y}, f y :=
  rfl

@[simp]
theorem rankFourBuildingAdjacencyThree_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 4) (x : BuildingVertex k 4) :
    rankFourBuildingAdjacencyThree k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 4 3 x y}, f y :=
  rfl

theorem norm_rankThreeBuildingAdjacencyOne_le_degree
    (k : Type u) [Field k] [Finite k] :
    ‖rankThreeBuildingAdjacencyOne k‖ ≤
      coloredAdjacencyDegree k 3 1 := by
  calc
    ‖rankThreeBuildingAdjacencyOne k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 3 1 : ℝ) *
          coloredAdjacencyDegree k 3 2) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 3 1 2
        (fundamentalDoubleCoset_rankThree_one_inv k)
    _ = coloredAdjacencyDegree k 3 1 := by
      rw [coloredAdjacencyDegree_rankThree_one,
        coloredAdjacencyDegree_rankThree_two]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

theorem norm_rankThreeBuildingAdjacencyTwo_le_degree
    (k : Type u) [Field k] [Finite k] :
    ‖rankThreeBuildingAdjacencyTwo k‖ ≤
      coloredAdjacencyDegree k 3 2 := by
  calc
    ‖rankThreeBuildingAdjacencyTwo k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 3 2 : ℝ) *
          coloredAdjacencyDegree k 3 1) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 3 2 1
        (fundamentalDoubleCoset_rankThree_two_inv k)
    _ = coloredAdjacencyDegree k 3 2 := by
      rw [coloredAdjacencyDegree_rankThree_one,
        coloredAdjacencyDegree_rankThree_two]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

theorem norm_rankFourBuildingAdjacencyOne_le_degree
    (k : Type u) [Field k] [Finite k] :
    ‖rankFourBuildingAdjacencyOne k‖ ≤
      coloredAdjacencyDegree k 4 1 := by
  calc
    ‖rankFourBuildingAdjacencyOne k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 4 1 : ℝ) *
          coloredAdjacencyDegree k 4 3) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 4 1 3
        (fundamentalDoubleCoset_rankFour_one_inv k)
    _ = coloredAdjacencyDegree k 4 1 := by
      rw [coloredAdjacencyDegree_rankFour_one,
        coloredAdjacencyDegree_rankFour_three]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

theorem norm_rankFourBuildingAdjacencyTwo_le_degree
    (k : Type u) [Field k] [Finite k] :
    ‖rankFourBuildingAdjacencyTwo k‖ ≤
      coloredAdjacencyDegree k 4 2 := by
  calc
    ‖rankFourBuildingAdjacencyTwo k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 4 2 : ℝ) *
          coloredAdjacencyDegree k 4 2) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 4 2 2
        (fundamentalDoubleCoset_rankFour_two_inv k)
    _ = coloredAdjacencyDegree k 4 2 := by
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

theorem norm_rankFourBuildingAdjacencyThree_le_degree
    (k : Type u) [Field k] [Finite k] :
    ‖rankFourBuildingAdjacencyThree k‖ ≤
      coloredAdjacencyDegree k 4 3 := by
  calc
    ‖rankFourBuildingAdjacencyThree k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 4 3 : ℝ) *
          coloredAdjacencyDegree k 4 1) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 4 3 1
        (fundamentalDoubleCoset_rankFour_three_inv k)
    _ = coloredAdjacencyDegree k 4 3 := by
      rw [coloredAdjacencyDegree_rankFour_one,
        coloredAdjacencyDegree_rankFour_three]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-! ### Adjoint color convention -/

/-- Pull an `ℓ²` vertex function back to the source of every color-`r` edge. -/
noncomputable def coloredBuildingEdgeSourceL2
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingL2 k d) :
  lp (fun _ : ColoredBuildingEdge k d r ↦ ℂ) 2 :=
  ⟨fun e ↦ f e.1, by
    show Memℓp (fun e : ColoredBuildingEdge k d r ↦ f e.1) 2
    rw [memℓp_gen_iff (by norm_num)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_norm_sq_coloredBuildingEdge_source k d r f⟩

/-- Pull an `ℓ²` vertex function back to the target of every color-`r` edge. -/
noncomputable def coloredBuildingEdgeTargetL2OfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
  lp (fun _ : ColoredBuildingEdge k d r ↦ ℂ) 2 :=
  ⟨fun e ↦ f e.2.1, by
    show Memℓp (fun e : ColoredBuildingEdge k d r ↦ f e.2.1) 2
    rw [memℓp_gen_iff (by norm_num)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f⟩

/-- The edgewise matrix-coefficient series is absolutely summable. -/
theorem summable_inner_coloredBuildingEdge_target_source_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f g : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦
      inner ℂ (f e.2.1) (g e.1)) := by
  exact lp.summable_inner
      (coloredBuildingEdgeTargetL2OfInv k d r s hset f)
      (coloredBuildingEdgeSourceL2 k d r g)

/-- Reversing the Cartan color gives the Hilbert-space adjoint relation for
the actual graph adjacency operators. -/
theorem inner_buildingColoredAdjacencyOperatorOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d r)
    (f g : BuildingL2 k d) :
    inner ℂ (buildingColoredAdjacencyOperatorOfInv k d r s hset f) g =
      inner ℂ f (buildingColoredAdjacencyOperatorOfInv k d s r hsset g) := by
  let er := coloredBuildingEdgeReverseEquiv k d r s hset
  have hr := summable_inner_coloredBuildingEdge_target_source_of_inv
    k d r s hset f g
  have hs := summable_inner_coloredBuildingEdge_target_source_of_inv
    k d s r hsset g f
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp_rw [buildingColoredAdjacencyOperatorOfInv_apply_apply,
    sum_inner, inner_sum]
  calc
    (∑' x : BuildingVertex k d,
        ∑ y : {y // ColoredBuildingAdjacent k d r x y},
          inner ℂ (f y) (g x)) =
        ∑' e : ColoredBuildingEdge k d r,
          inner ℂ (f e.2.1) (g e.1) := by
      exact (hr.tsum_sigma.trans (tsum_congr fun x ↦ by
        rw [tsum_fintype])).symm
    _ = ∑' e : ColoredBuildingEdge k d s,
          inner ℂ (f e.1) (g e.2.1) := by
      simpa [er, coloredBuildingEdgeReverseEquiv] using
        (er.tsum_eq (fun e : ColoredBuildingEdge k d s ↦
          inner ℂ (f e.1) (g e.2.1)))
    _ = ∑' x : BuildingVertex k d,
        ∑ y : {y // ColoredBuildingAdjacent k d s x y},
          inner ℂ (f x) (g y) := by
      have hs' : Summable (fun e : ColoredBuildingEdge k d s ↦
          inner ℂ (f e.1) (g e.2.1)) := by
        simpa only [inner_conj_symm] using
          (Complex.summable_conj.mpr hs)
      exact hs'.tsum_sigma.trans (tsum_congr fun x ↦ by
        rw [tsum_fintype])

/-- The Hilbert adjoint is exactly the operator for the reverse Cartan color. -/
theorem adjoint_buildingColoredAdjacencyOperatorOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d r) :
    (buildingColoredAdjacencyOperatorOfInv k d r s hset)† =
      buildingColoredAdjacencyOperatorOfInv k d s r hsset := by
  rw [← eq_comm]
  exact (ContinuousLinearMap.eq_adjoint_iff
    (buildingColoredAdjacencyOperatorOfInv k d s r hsset)
    (buildingColoredAdjacencyOperatorOfInv k d r s hset)).2
      (fun f g ↦ inner_buildingColoredAdjacencyOperatorOfInv
        k d s r hsset hset f g)

@[simp]
theorem adjoint_rankThreeBuildingAdjacencyOne
    (k : Type u) [Field k] [Finite k] :
    (rankThreeBuildingAdjacencyOne k)† =
      rankThreeBuildingAdjacencyTwo k :=
  adjoint_buildingColoredAdjacencyOperatorOfInv k 3 1 2
    (fundamentalDoubleCoset_rankThree_one_inv k)
    (fundamentalDoubleCoset_rankThree_two_inv k)

@[simp]
theorem adjoint_rankThreeBuildingAdjacencyTwo
    (k : Type u) [Field k] [Finite k] :
    (rankThreeBuildingAdjacencyTwo k)† =
      rankThreeBuildingAdjacencyOne k :=
  adjoint_buildingColoredAdjacencyOperatorOfInv k 3 2 1
    (fundamentalDoubleCoset_rankThree_two_inv k)
    (fundamentalDoubleCoset_rankThree_one_inv k)

@[simp]
theorem adjoint_rankFourBuildingAdjacencyOne
    (k : Type u) [Field k] [Finite k] :
    (rankFourBuildingAdjacencyOne k)† =
      rankFourBuildingAdjacencyThree k :=
  adjoint_buildingColoredAdjacencyOperatorOfInv k 4 1 3
    (fundamentalDoubleCoset_rankFour_one_inv k)
    (fundamentalDoubleCoset_rankFour_three_inv k)

@[simp]
theorem adjoint_rankFourBuildingAdjacencyTwo
    (k : Type u) [Field k] [Finite k] :
    (rankFourBuildingAdjacencyTwo k)† =
      rankFourBuildingAdjacencyTwo k :=
  adjoint_buildingColoredAdjacencyOperatorOfInv k 4 2 2
    (fundamentalDoubleCoset_rankFour_two_inv k)
    (fundamentalDoubleCoset_rankFour_two_inv k)

@[simp]
theorem adjoint_rankFourBuildingAdjacencyThree
    (k : Type u) [Field k] [Finite k] :
    (rankFourBuildingAdjacencyThree k)† =
      rankFourBuildingAdjacencyOne k :=
  adjoint_buildingColoredAdjacencyOperatorOfInv k 4 3 1
    (fundamentalDoubleCoset_rankFour_three_inv k)
    (fundamentalDoubleCoset_rankFour_one_inv k)

theorem rankFourBuildingAdjacencyTwo_isSelfAdjoint
    (k : Type u) [Field k] [Finite k] :
    IsSelfAdjoint (rankFourBuildingAdjacencyTwo k) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact adjoint_rankFourBuildingAdjacencyTwo k

/-! ### Commutativity from the actual spherical Hecke convolution -/

/-- Haar convolution of two fundamental characteristic functions is the
finite right-coset sum that counts the corresponding two-step building
paths. -/
theorem convolution_fundamentalHeckeFunction_apply_eq_sum
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (a : HeckeGroup k d) :
    (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) a =
      ∑ q ∈ fundamentalNeighborCosets k d r,
        fundamentalHeckeFunction k d s (q.out⁻¹ * a) := by
  rw [show (fundamentalHeckeFunction k d r *
      fundamentalHeckeFunction k d s) a =
      ∫ t in fundamentalDoubleCoset k d r,
        fundamentalHeckeFunction k d s (t⁻¹ * a)
          ∂normalizedLocalHaarMeasure k d by
    exact coloredAdjacency_apply k d r
      (fundamentalHeckeFunction k d s) a]
  exact setIntegral_fundamentalDoubleCoset_eq_sum_neighbors k d r
    (fun t ↦ fundamentalHeckeFunction k d s (t⁻¹ * a))
    ((fundamentalHeckeFunction k d s).continuous.comp
      (continuous_inv.mul continuous_const))
    (by
      intro g q hq
      change fundamentalHeckeFunction k d s ((g * q)⁻¹ * a) =
        fundamentalHeckeFunction k d s (g⁻¹ * a)
      rw [mul_inv_rev, mul_assoc]
      exact (fundamentalHeckeFunction k d s).left_invariant q⁻¹
        ((maximalCompact k d).inv_mem hq) (g⁻¹ * a))

/-- The two finite fundamental-coset kernels commute pointwise, with all Haar
volumes already evaluated to one on the right-coset fibers. -/
theorem sum_fundamentalHeckeFunction_comm
    (k : Type u) [Field k] [Finite k] (n r s : ℕ)
    (a : HeckeGroup k (n + 1)) :
    (∑ q ∈ fundamentalNeighborCosets k (n + 1) r,
        fundamentalHeckeFunction k (n + 1) s (q.out⁻¹ * a)) =
      ∑ q ∈ fundamentalNeighborCosets k (n + 1) s,
        fundamentalHeckeFunction k (n + 1) r (q.out⁻¹ * a) := by
  rw [← convolution_fundamentalHeckeFunction_apply_eq_sum,
    ← convolution_fundamentalHeckeFunction_apply_eq_sum,
    mul_comm]

@[simp]
theorem fundamentalNeighborAdjacentEquiv_apply_val
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d)
    (q : {q // q ∈ fundamentalNeighborCosets k d r}) :
    (fundamentalNeighborAdjacentEquiv k d r x q).1 = x.out • q.1 := by
  simp [fundamentalNeighborAdjacentEquiv]

/-- Reindex the actual neighbor sum at `x` by the construction-owned
fundamental right-cosets transported from the base vertex. -/
theorem sum_coloredBuildingNeighbors_eq_sum_fundamental
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) (F : BuildingVertex k d → ℂ) :
    (∑ y : {y // ColoredBuildingAdjacent k d r x y}, F y) =
      ∑ q : {q // q ∈ fundamentalNeighborCosets k d r},
        F (x.out • q.1) := by
  let e := fundamentalNeighborAdjacentEquiv k d r x
  simpa [e] using
    (e.sum_comp (fun y : {y // ColoredBuildingAdjacent k d r x y} ↦ F y.1)).symm

/-- The unit delta vector at a building vertex. -/
noncomputable def buildingVertexDelta
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (z : BuildingVertex k d) : BuildingL2 k d := by
  classical
  exact lp.single 2 z (1 : ℂ)

/-- On an adjacent delta vertex, a color adjacency operator has value one. -/
theorem buildingColoredAdjacencyOperatorOfInv_single_apply_of_adjacent
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (z x : BuildingVertex k d)
    (hxz : ColoredBuildingAdjacent k d r x z) :
    buildingColoredAdjacencyOperatorOfInv k d r s hset
        (buildingVertexDelta k d z) x = 1 := by
  classical
  rw [buildingColoredAdjacencyOperatorOfInv_apply_apply]
  let z' : {y // ColoredBuildingAdjacent k d r x y} := ⟨z, hxz⟩
  rw [Fintype.sum_eq_single z' (fun y hy ↦ by
      have hne : y.1 ≠ z := fun hval ↦ hy (Subtype.ext hval)
      exact lp.single_apply_ne (E := fun _ : BuildingVertex k d ↦ ℂ)
        2 z (1 : ℂ) hne)]
  exact lp.single_apply_self (E := fun _ : BuildingVertex k d ↦ ℂ)
    2 z (1 : ℂ)

/-- On a nonadjacent delta vertex, a color adjacency operator has value
zero. -/
theorem buildingColoredAdjacencyOperatorOfInv_single_apply_of_not_adjacent
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (z x : BuildingVertex k d)
    (hxz : ¬ ColoredBuildingAdjacent k d r x z) :
    buildingColoredAdjacencyOperatorOfInv k d r s hset
        (buildingVertexDelta k d z) x = 0 := by
  classical
  rw [buildingColoredAdjacencyOperatorOfInv_apply_apply]
  apply Fintype.sum_eq_zero
  intro y
  have hne : y.1 ≠ z := fun hy ↦ hxz (by simpa [hy] using y.2)
  exact lp.single_apply_ne (E := fun _ : BuildingVertex k d ↦ ℂ)
    2 z (1 : ℂ) hne

/-- In the transported fundamental-neighbor coordinates, adjacency to `z`
is membership of the exact relative element in the second Cartan double
coset. -/
theorem coloredBuildingAdjacent_smul_fundamental_iff
    (k : Type u) [Field k] [Finite k] (d s : ℕ)
    (x z : BuildingVertex k d)
    (q : BuildingVertex k d) :
    ColoredBuildingAdjacent k d s (x.out • q) z ↔
      q.out⁻¹ * x.out⁻¹ * z.out ∈ fundamentalDoubleCoset k d s := by
  have hxq : x.out • q =
      QuotientGroup.mk (x.out * q.out) := by
    calc
      x.out • q = x.out • QuotientGroup.mk (q.out) :=
        congrArg (fun w : BuildingVertex k d ↦ x.out • w) q.out_eq'.symm
      _ = QuotientGroup.mk (x.out * q.out) := by
        rw [MulAction.Quotient.smul_mk]
        rfl
  have hmk := coloredBuildingAdjacent_mk_iff k d s
    (x.out * q.out) z.out
  have hzOut : (QuotientGroup.mk z.out : BuildingVertex k d) = z :=
    z.out_eq'
  rw [← hxq, hzOut] at hmk
  simpa only [mul_inv_rev, mul_assoc] using hmk

/-- A second-color adjacency applied to a delta, at a transported
first-color neighbor, is exactly the second fundamental Hecke indicator. -/
theorem buildingColoredAdjacencyOperatorOfInv_single_transported_apply
    (k : Type u) [Field k] [Finite k] (d r s t : ℕ)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d t)
    (x z : BuildingVertex k d)
    (q : {q // q ∈ fundamentalNeighborCosets k d r}) :
    buildingColoredAdjacencyOperatorOfInv k d s t hsset
        (buildingVertexDelta k d z) (x.out • q.1) =
      fundamentalHeckeFunction k d s
        (q.1.out⁻¹ * x.out⁻¹ * z.out) := by
  by_cases hAdj : ColoredBuildingAdjacent k d s (x.out • q.1) z
  · rw [buildingColoredAdjacencyOperatorOfInv_single_apply_of_adjacent
      k d s t hsset z (x.out • q.1) hAdj]
    have hmem := (coloredBuildingAdjacent_smul_fundamental_iff
      k d s x z q.1).1 hAdj
    simp [fundamentalHeckeFunction_apply, hmem]
  · rw [buildingColoredAdjacencyOperatorOfInv_single_apply_of_not_adjacent
      k d s t hsset z (x.out • q.1) hAdj]
    have hmem : q.1.out⁻¹ * x.out⁻¹ * z.out ∉
        fundamentalDoubleCoset k d s := fun h ↦ hAdj
      ((coloredBuildingAdjacent_smul_fundamental_iff k d s x z q.1).2 h)
    simp [fundamentalHeckeFunction_apply, hmem]

/-- Composition of two graph adjacency operators on a vertex delta is the
actual Haar convolution coefficient at the corresponding relative group
element. -/
theorem buildingColoredAdjacencyOperatorOfInv_comp_single_apply
    (k : Type u) [Field k] [Finite k] (d r r' s s' : ℕ)
    (hrset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d r')
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d s')
    (z x : BuildingVertex k d) :
    (buildingColoredAdjacencyOperatorOfInv k d r r' hrset ∘L
        buildingColoredAdjacencyOperatorOfInv k d s s' hsset)
        (buildingVertexDelta k d z) x =
      (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) (x.out⁻¹ * z.out) := by
  rw [ContinuousLinearMap.comp_apply,
    buildingColoredAdjacencyOperatorOfInv_apply_apply]
  rw [sum_coloredBuildingNeighbors_eq_sum_fundamental]
  simp_rw [buildingColoredAdjacencyOperatorOfInv_single_transported_apply
    k d r s s' hsset x z]
  calc
    (∑ q : {q // q ∈ fundamentalNeighborCosets k d r},
        fundamentalHeckeFunction k d s
          (q.1.out⁻¹ * x.out⁻¹ * z.out)) =
        ∑ q ∈ fundamentalNeighborCosets k d r,
          fundamentalHeckeFunction k d s
            (q.out⁻¹ * (x.out⁻¹ * z.out)) := by
      rw [show (∑ q ∈ fundamentalNeighborCosets k d r,
          fundamentalHeckeFunction k d s
            (q.out⁻¹ * (x.out⁻¹ * z.out))) =
          ∑ q : {q // q ∈ fundamentalNeighborCosets k d r},
            fundamentalHeckeFunction k d s
              (q.1.out⁻¹ * (x.out⁻¹ * z.out)) by
        rw [← Finset.sum_attach, Finset.attach_eq_univ]]
      apply Fintype.sum_congr
      intro q
      rw [mul_assoc]
    _ = (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) (x.out⁻¹ * z.out) :=
      (convolution_fundamentalHeckeFunction_apply_eq_sum
        k d r s (x.out⁻¹ * z.out)).symm

/-- All bounded color adjacency operators commute in positive rank, because
their matrix coefficients on the dense vertex-delta span are the coefficients
of the commutative spherical Hecke convolution. -/
theorem buildingColoredAdjacencyOperatorOfInv_comm
    (k : Type u) [Field k] [Finite k] (n r r' s s' : ℕ)
    (hrset : (fundamentalDoubleCoset k (n + 1) r)⁻¹ =
      fundamentalDoubleCoset k (n + 1) r')
    (hsset : (fundamentalDoubleCoset k (n + 1) s)⁻¹ =
      fundamentalDoubleCoset k (n + 1) s') :
    buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset ∘L
        buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset =
      buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset ∘L
        buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset := by
  classical
  let Ar := buildingColoredAdjacencyOperatorOfInv k (n + 1) r r' hrset
  let As := buildingColoredAdjacencyOperatorOfInv k (n + 1) s s' hsset
  apply lp.ext_continuousLinearMap (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ)
    (p := (2 : ℝ≥0∞)) (by norm_num)
  intro z
  apply ContinuousLinearMap.ext
  intro c
  apply lp.ext
  funext x
  have hsingle : lp.single (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ)
      2 z c = c • buildingVertexDelta k (n + 1) z := by
    simpa [buildingVertexDelta] using
      (lp.single_smul (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ)
        2 z c (1 : ℂ))
  change ((Ar ∘L As)
      (lp.single (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ) 2 z c)) x =
    ((As ∘L Ar)
      (lp.single (E := fun _ : BuildingVertex k (n + 1) ↦ ℂ) 2 z c)) x
  rw [hsingle]
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply]
  congr 1
  rw [buildingColoredAdjacencyOperatorOfInv_comp_single_apply
      k (n + 1) r r' s s' hrset hsset z x,
    buildingColoredAdjacencyOperatorOfInv_comp_single_apply
      k (n + 1) s s' r r' hsset hrset z x,
    mul_comm]

/-! ### Rank-three and rank-four commuting normal families -/

/-- The two rank-three color adjacency operators commute. -/
theorem rankThreeBuildingAdjacencyOne_comm_two
    (k : Type u) [Field k] [Finite k] :
    rankThreeBuildingAdjacencyOne k ∘L rankThreeBuildingAdjacencyTwo k =
      rankThreeBuildingAdjacencyTwo k ∘L rankThreeBuildingAdjacencyOne k := by
  simpa [rankThreeBuildingAdjacencyOne, rankThreeBuildingAdjacencyTwo] using
    (buildingColoredAdjacencyOperatorOfInv_comm k 2 1 2 2 1
      (fundamentalDoubleCoset_rankThree_one_inv k)
      (fundamentalDoubleCoset_rankThree_two_inv k))

/-- The first and second rank-four color adjacency operators commute. -/
theorem rankFourBuildingAdjacencyOne_comm_two
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyOne k ∘L rankFourBuildingAdjacencyTwo k =
      rankFourBuildingAdjacencyTwo k ∘L rankFourBuildingAdjacencyOne k := by
  simpa [rankFourBuildingAdjacencyOne, rankFourBuildingAdjacencyTwo] using
    (buildingColoredAdjacencyOperatorOfInv_comm k 3 1 3 2 2
      (fundamentalDoubleCoset_rankFour_one_inv k)
      (fundamentalDoubleCoset_rankFour_two_inv k))

/-- The first and third rank-four color adjacency operators commute. -/
theorem rankFourBuildingAdjacencyOne_comm_three
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyOne k ∘L rankFourBuildingAdjacencyThree k =
      rankFourBuildingAdjacencyThree k ∘L rankFourBuildingAdjacencyOne k := by
  simpa [rankFourBuildingAdjacencyOne, rankFourBuildingAdjacencyThree] using
    (buildingColoredAdjacencyOperatorOfInv_comm k 3 1 3 3 1
      (fundamentalDoubleCoset_rankFour_one_inv k)
      (fundamentalDoubleCoset_rankFour_three_inv k))

/-- The second and third rank-four color adjacency operators commute. -/
theorem rankFourBuildingAdjacencyTwo_comm_three
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyTwo k ∘L rankFourBuildingAdjacencyThree k =
      rankFourBuildingAdjacencyThree k ∘L rankFourBuildingAdjacencyTwo k := by
  simpa [rankFourBuildingAdjacencyTwo, rankFourBuildingAdjacencyThree] using
    (buildingColoredAdjacencyOperatorOfInv_comm k 3 2 2 3 1
      (fundamentalDoubleCoset_rankFour_two_inv k)
      (fundamentalDoubleCoset_rankFour_three_inv k))

/-- The first rank-three color adjacency operator is normal. -/
theorem rankThreeBuildingAdjacencyOne_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankThreeBuildingAdjacencyOne k) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint,
    adjoint_rankThreeBuildingAdjacencyOne]
  exact (rankThreeBuildingAdjacencyOne_comm_two k).symm

/-- The second rank-three color adjacency operator is normal. -/
theorem rankThreeBuildingAdjacencyTwo_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankThreeBuildingAdjacencyTwo k) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint,
    adjoint_rankThreeBuildingAdjacencyTwo]
  exact rankThreeBuildingAdjacencyOne_comm_two k

/-- The first rank-four color adjacency operator is normal. -/
theorem rankFourBuildingAdjacencyOne_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankFourBuildingAdjacencyOne k) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint,
    adjoint_rankFourBuildingAdjacencyOne]
  exact (rankFourBuildingAdjacencyOne_comm_three k).symm

/-- The middle rank-four color adjacency operator is normal. -/
theorem rankFourBuildingAdjacencyTwo_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankFourBuildingAdjacencyTwo k) :=
  (rankFourBuildingAdjacencyTwo_isSelfAdjoint k).isStarNormal

/-- The third rank-four color adjacency operator is normal. -/
theorem rankFourBuildingAdjacencyThree_isStarNormal
    (k : Type u) [Field k] [Finite k] :
    IsStarNormal (rankFourBuildingAdjacencyThree k) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint,
    adjoint_rankFourBuildingAdjacencyThree]
  exact rankFourBuildingAdjacencyOne_comm_three k

/-! ### Actual finite color families and approximate joint spectrum -/

/-- The complete two-color adjacency family of the universal rank-three
building. -/
noncomputable def rankThreeBuildingAdjacencyFamily
    (k : Type u) [Field k] [Finite k] :
    Fin 2 → (BuildingL2 k 3 →L[ℂ] BuildingL2 k 3) :=
  ![rankThreeBuildingAdjacencyOne k, rankThreeBuildingAdjacencyTwo k]

/-- The complete three-color adjacency family of the universal rank-four
building. -/
noncomputable def rankFourBuildingAdjacencyFamily
    (k : Type u) [Field k] [Finite k] :
    Fin 3 → (BuildingL2 k 4 →L[ℂ] BuildingL2 k 4) :=
  ![rankFourBuildingAdjacencyOne k, rankFourBuildingAdjacencyTwo k,
    rankFourBuildingAdjacencyThree k]

@[simp]
theorem rankThreeBuildingAdjacencyFamily_zero
    (k : Type u) [Field k] [Finite k] :
    rankThreeBuildingAdjacencyFamily k 0 =
      rankThreeBuildingAdjacencyOne k :=
  rfl

@[simp]
theorem rankThreeBuildingAdjacencyFamily_one
    (k : Type u) [Field k] [Finite k] :
    rankThreeBuildingAdjacencyFamily k 1 =
      rankThreeBuildingAdjacencyTwo k :=
  rfl

@[simp]
theorem rankFourBuildingAdjacencyFamily_zero
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyFamily k 0 =
      rankFourBuildingAdjacencyOne k :=
  rfl

@[simp]
theorem rankFourBuildingAdjacencyFamily_one
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyFamily k 1 =
      rankFourBuildingAdjacencyTwo k :=
  rfl

@[simp]
theorem rankFourBuildingAdjacencyFamily_two
    (k : Type u) [Field k] [Finite k] :
    rankFourBuildingAdjacencyFamily k 2 =
      rankFourBuildingAdjacencyThree k :=
  rfl

/-- The rank-three color family commutes pairwise. -/
theorem rankThreeBuildingAdjacencyFamily_comm
    (k : Type u) [Field k] [Finite k] (i j : Fin 2) :
    rankThreeBuildingAdjacencyFamily k i ∘L
        rankThreeBuildingAdjacencyFamily k j =
      rankThreeBuildingAdjacencyFamily k j ∘L
        rankThreeBuildingAdjacencyFamily k i := by
  fin_cases i <;> fin_cases j <;>
    simp [rankThreeBuildingAdjacencyFamily,
      rankThreeBuildingAdjacencyOne_comm_two]

/-- The rank-four color family commutes pairwise. -/
theorem rankFourBuildingAdjacencyFamily_comm
    (k : Type u) [Field k] [Finite k] (i j : Fin 3) :
    rankFourBuildingAdjacencyFamily k i ∘L
        rankFourBuildingAdjacencyFamily k j =
      rankFourBuildingAdjacencyFamily k j ∘L
        rankFourBuildingAdjacencyFamily k i := by
  fin_cases i <;> fin_cases j <;>
    simp [rankFourBuildingAdjacencyFamily,
      rankFourBuildingAdjacencyOne_comm_two,
      rankFourBuildingAdjacencyOne_comm_three,
      rankFourBuildingAdjacencyTwo_comm_three]

/-- Every member of the rank-three color family is normal. -/
theorem rankThreeBuildingAdjacencyFamily_isStarNormal
    (k : Type u) [Field k] [Finite k] (i : Fin 2) :
    IsStarNormal (rankThreeBuildingAdjacencyFamily k i) := by
  fin_cases i
  · exact rankThreeBuildingAdjacencyOne_isStarNormal k
  · exact rankThreeBuildingAdjacencyTwo_isStarNormal k

/-- Every member of the rank-four color family is normal. -/
theorem rankFourBuildingAdjacencyFamily_isStarNormal
    (k : Type u) [Field k] [Finite k] (i : Fin 3) :
    IsStarNormal (rankFourBuildingAdjacencyFamily k i) := by
  fin_cases i
  · exact rankFourBuildingAdjacencyOne_isStarNormal k
  · exact rankFourBuildingAdjacencyTwo_isStarNormal k
  · exact rankFourBuildingAdjacencyThree_isStarNormal k

/-- Approximate joint eigenpackets of a finite family of bounded operators.
This is an analytic definition: it requires unit vectors with arbitrarily
small simultaneous residuals and contains no caller-supplied spectrum. -/
def jointApproximatePointSpectrum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) : Set (ι → ℂ) :=
  {a | ∀ ε : ℝ, 0 < ε → ∃ v : E, ‖v‖ = 1 ∧
    ∀ i, ‖A i v - a i • v‖ < ε}

/-- The actual rank-three approximate joint spectrum. -/
abbrev RankThreeBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] : Set (Fin 2 → ℂ) :=
  jointApproximatePointSpectrum (rankThreeBuildingAdjacencyFamily k)

/-- The actual rank-four approximate joint spectrum. -/
abbrev RankFourBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] : Set (Fin 3 → ℂ) :=
  jointApproximatePointSpectrum (rankFourBuildingAdjacencyFamily k)

/-- A common unit eigenvector gives an approximate joint eigenpacket. -/
theorem mem_jointApproximatePointSpectrum_of_eigenvector
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ) (v : E)
    (hv : ‖v‖ = 1) (heigen : ∀ i, A i v = a i • v) :
    a ∈ jointApproximatePointSpectrum A := by
  intro ε hε
  refine ⟨v, hv, ?_⟩
  intro i
  rw [heigen i, sub_self, norm_zero]
  exact hε

/-- For a finite operator family, the approximate joint spectrum is closed.
The proof uses one simultaneous coordinate neighborhood and retains the same
unit vector while moving the candidate eigenpacket to its limit. -/
theorem isClosed_jointApproximatePointSpectrum
    {ι E : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) :
    IsClosed (jointApproximatePointSpectrum A) := by
  rw [← closure_subset_iff_isClosed]
  intro a ha ε hε
  let U : Set (ι → ℂ) :=
    {b | ∀ i, ‖b i - a i‖ < ε / 2}
  have hhalf : 0 < ε / 2 := half_pos hε
  have hUopen : IsOpen U := by
    dsimp only [U]
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (((continuous_apply i).sub continuous_const).norm)
      continuous_const
  have haU : a ∈ U := by
    intro i
    simpa using hhalf
  obtain ⟨b, hbU, hbSpec⟩ :=
    (mem_closure_iff_nhds.1 ha U (hUopen.mem_nhds haU))
  obtain ⟨v, hv, hvres⟩ := hbSpec (ε / 2) hhalf
  refine ⟨v, hv, ?_⟩
  intro i
  calc
    ‖A i v - a i • v‖ =
        ‖(A i v - b i • v) + (b i - a i) • v‖ := by
      congr 1
      simp only [sub_smul]
      abel
    _ ≤ ‖A i v - b i • v‖ + ‖(b i - a i) • v‖ :=
      norm_add_le _ _
    _ = ‖A i v - b i • v‖ + ‖b i - a i‖ := by
      rw [norm_smul, hv, mul_one]
    _ < ε / 2 + ε / 2 := add_lt_add (hvres i) (hbU i)
    _ = ε := by ring

/-- Every coordinate of an approximate joint eigenpacket is bounded by the
operator norm of the corresponding color. -/
theorem norm_apply_le_of_mem_jointApproximatePointSpectrum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ)
    (ha : a ∈ jointApproximatePointSpectrum A) (i : ι) :
    ‖a i‖ ≤ ‖A i‖ := by
  by_contra hle
  have hlt : ‖A i‖ < ‖a i‖ := lt_of_not_ge hle
  have hdiff : 0 < ‖a i‖ - ‖A i‖ := sub_pos.mpr hlt
  obtain ⟨v, hv, hres⟩ := ha (‖a i‖ - ‖A i‖) hdiff
  have hAv : ‖A i v‖ ≤ ‖A i‖ := by
    simpa [hv] using (A i).le_opNorm v
  have hcontra : ‖a i‖ < ‖a i‖ := by
    calc
      ‖a i‖ = ‖a i • v‖ := by rw [norm_smul, hv, mul_one]
      _ = ‖(a i • v - A i v) + A i v‖ := by
        congr 1
        abel
      _ ≤ ‖a i • v - A i v‖ + ‖A i v‖ := norm_add_le _ _
      _ = ‖A i v - a i • v‖ + ‖A i v‖ := by
        rw [← norm_neg (A i v - a i • v)]
        congr 2
        abel
      _ < (‖a i‖ - ‖A i‖) + ‖A i‖ :=
        add_lt_add_of_lt_of_le (hres i) hAv
      _ = ‖a i‖ := sub_add_cancel _ _
  exact (lt_irrefl _ hcontra)

/-- Every coordinate of a simultaneous approximate eigenpacket lies in the
ordinary Banach-algebra spectrum of the corresponding bounded operator. -/
theorem apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) (a : ι → ℂ)
    (ha : a ∈ jointApproximatePointSpectrum A) (i : ι) :
    a i ∈ spectrum ℂ (A i) := by
  by_contra hspec
  have hunit : IsUnit
      (algebraMap ℂ (E →L[ℂ] E) (a i) - A i) :=
    spectrum.notMem_iff.mp hspec
  obtain ⟨u, hu⟩ := hunit
  let C : ℝ := ‖((↑u⁻¹) : E →L[ℂ] E)‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  obtain ⟨v, hv, hres⟩ := ha C⁻¹ (inv_pos.mpr hC)
  have huApply : ((u : E →L[ℂ] E) v) =
      a i • v - A i v := by
    rw [hu]
    simp [Algebra.algebraMap_eq_smul_one]
  have hresU : ‖(u : E →L[ℂ] E) v‖ < C⁻¹ := by
    rw [huApply, norm_sub_rev]
    exact hres i
  have hvInv : v = ((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)
      ((u : E →L[ℂ] E) v) := by
    have hmul := congrArg
      (fun T : E →L[ℂ] E ↦ T v)
      u.inv_mul
    calc
      v = (1 : E →L[ℂ] E) v := by simp
      _ = ((((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E) *
          (u : E →L[ℂ] E)) v) := hmul.symm
      _ = ((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E)
          ((u : E →L[ℂ] E) v) := rfl
  have hnormInv :=
    (((u⁻¹ : (E →L[ℂ] E)ˣ) : E →L[ℂ] E).le_opNorm
      ((u : E →L[ℂ] E) v))
  have hprodLt :
      ‖((↑u⁻¹) : E →L[ℂ] E)‖ *
          ‖(u : E →L[ℂ] E) v‖ < 1 := by
    calc
      ‖((↑u⁻¹) : E →L[ℂ] E)‖ *
          ‖(u : E →L[ℂ] E) v‖ ≤
          C * ‖(u : E →L[ℂ] E) v‖ := by
        apply mul_le_mul_of_nonneg_right
        · dsimp only [C]
          linarith
        · exact norm_nonneg _
      _ < C * C⁻¹ := mul_lt_mul_of_pos_left hresU hC
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have : ‖v‖ < 1 := by
    rw [hvInv]
    exact hnormInv.trans_lt hprodLt
  rw [hv] at this
  exact (lt_irrefl 1 this)

/-- A finite-family approximate joint spectrum is bounded by the sum of the
individual operator norms. -/
theorem isBounded_jointApproximatePointSpectrum
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) :
    Bornology.IsBounded (jointApproximatePointSpectrum A) := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : ι → ℂ)).2
  refine ⟨∑ i : ι, ‖A i‖, ?_⟩
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
  intro i
  exact (norm_apply_le_of_mem_jointApproximatePointSpectrum A a ha i).trans
    (Finset.single_le_sum (fun j _ ↦ norm_nonneg (A j))
      (Finset.mem_univ i))

/-- For a finite family, the approximate joint spectrum is compact. -/
theorem isCompact_jointApproximatePointSpectrum
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) :
    IsCompact (jointApproximatePointSpectrum A) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_jointApproximatePointSpectrum A)
    (isBounded_jointApproximatePointSpectrum A)

theorem isClosed_rankThreeBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsClosed (RankThreeBuildingJointApproximateSpectrum k) :=
  isClosed_jointApproximatePointSpectrum
    (rankThreeBuildingAdjacencyFamily k)

theorem isCompact_rankThreeBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsCompact (RankThreeBuildingJointApproximateSpectrum k) :=
  isCompact_jointApproximatePointSpectrum
    (rankThreeBuildingAdjacencyFamily k)

/-- Every rank-three joint approximate eigenpacket projects to the ordinary
operator spectrum in both actual colors. -/
theorem rankThree_jointApproximate_apply_mem_spectrum
    (k : Type u) [Field k] [Finite k]
    (a : Fin 2 → ℂ) (ha : a ∈ RankThreeBuildingJointApproximateSpectrum k)
    (color : Fin 2) :
    a color ∈ spectrum ℂ (rankThreeBuildingAdjacencyFamily k color) :=
  apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
    (rankThreeBuildingAdjacencyFamily k) a ha color

theorem isClosed_rankFourBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsClosed (RankFourBuildingJointApproximateSpectrum k) :=
  isClosed_jointApproximatePointSpectrum
    (rankFourBuildingAdjacencyFamily k)

theorem isCompact_rankFourBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] :
    IsCompact (RankFourBuildingJointApproximateSpectrum k) :=
  isCompact_jointApproximatePointSpectrum
    (rankFourBuildingAdjacencyFamily k)

/-- Every rank-four joint approximate eigenpacket projects to the ordinary
operator spectrum in all three actual colors. -/
theorem rankFour_jointApproximate_apply_mem_spectrum
    (k : Type u) [Field k] [Finite k]
    (a : Fin 3 → ℂ) (ha : a ∈ RankFourBuildingJointApproximateSpectrum k)
    (color : Fin 3) :
    a color ∈ spectrum ℂ (rankFourBuildingAdjacencyFamily k color) :=
  apply_mem_spectrum_of_mem_jointApproximatePointSpectrum
    (rankFourBuildingAdjacencyFamily k) a ha color

end QEC.Coding.HighDimensionalExpander.SphericalHecke
