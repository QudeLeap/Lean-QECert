import QEC.Coding.ExpanderCodes.SmallSetExpansionSpectrum
import QEC.Coding.ExpanderCodes.TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic

/-!
# Spectral form of a labelled finite Cayley graph

This module unfolds the weighted adjacency operator of a labelled Cayley
multigraph as the sum of right translations.  Parallel labels are retained,
which is essential for the quaternion-shell construction.
-/

namespace QEC.Coding.TannerLiftedProduct

universe v

variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

/-- The unnormalized complex right-translation sum attached to a labelled
generator family. -/
noncomputable def cayleyRightTranslationSum
    (label : W → G) (f : G → ℂ) (g : G) : ℂ :=
  ∑ a, f (g * label a)

/-- The right regular representation in the multiplication convention used
by `rightCayleyGraph`. -/
def cayleyRightRegularRepresentation : Representation ℂ G (G → ℂ) where
  toFun s :=
    { toFun := fun f g => f (g * s)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f g
    simp
  map_mul' s t := by
    ext f g
    simp [mul_assoc]

@[simp] theorem cayleyRightRegularRepresentation_apply
    (s g : G) (f : G → ℂ) :
    cayleyRightRegularRepresentation s f g = f (g * s) := rfl

/-- The group-algebra element which records the labelled generator family,
with multiplicity. -/
noncomputable def cayleyGeneratorSum
    (label : W → G) : MonoidAlgebra ℂ G :=
  ∑ a, MonoidAlgebra.single (label a) 1

/-- The sum of all group elements in the complex group algebra. -/
noncomputable def cayleyGroupSum : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g 1

/-- The rank-one projection from the right regular representation onto its
constant subspace. -/
noncomputable def cayleyConstantProjection : Module.End ℂ (G → ℂ) :=
  ((Fintype.card G : ℂ)⁻¹) •
    cayleyRightRegularRepresentation.asAlgebraHom cayleyGroupSum

/-- The labelled generator sum after removing its action on the trivial
representation. -/
noncomputable def cayleyCenteredGeneratorSum
    (label : W → G) : MonoidAlgebra ℂ G :=
  cayleyGeneratorSum label -
    (((Fintype.card W : ℂ) / (Fintype.card G : ℂ)) • cayleyGroupSum)

/-- Acting by the generator sum in the right regular representation is the
unnormalized Cayley adjacency operator. -/
theorem cayleyGeneratorSum_action
    (label : W → G) (f : G → ℂ) (g : G) :
    (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyGeneratorSum label) f) g =
      cayleyRightTranslationSum label f g := by
  classical
  simp [cayleyGeneratorSum, cayleyRightTranslationSum]

/-- The full group sum acts in the right regular representation by the
constant function whose value is the sum of the input coordinates. -/
theorem cayleyGroupSum_action (f : G → ℂ) (g : G) :
    (cayleyRightRegularRepresentation.asAlgebraHom cayleyGroupSum f) g =
      ∑ h, f h := by
  classical
  simp only [cayleyGroupSum, map_sum, Representation.asAlgebraHom_single,
    LinearMap.sum_apply, one_smul]
  rw [Finset.sum_apply]
  exact (Equiv.sum_comp (Equiv.mulLeft g) f)

@[simp] theorem cayleyConstantProjection_apply
    (f : G → ℂ) (g : G) :
    cayleyConstantProjection f g =
      (Fintype.card G : ℂ)⁻¹ * ∑ h, f h := by
  simp [cayleyConstantProjection, cayleyGroupSum_action]

/-- The averaging operator onto constants is idempotent. -/
theorem cayleyConstantProjection_mul_self :
    cayleyConstantProjection (G := G) * cayleyConstantProjection =
      cayleyConstantProjection := by
  classical
  apply LinearMap.ext
  intro f
  funext g
  simp [Finset.sum_const, Fintype.card_ne_zero]

/-- A labelled Cayley adjacency operator acts on constants by the number of
labels. -/
theorem cayleyGeneratorSum_action_mul_constantProjection
    (label : W → G) :
    cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum label) * cayleyConstantProjection =
      (Fintype.card W : ℂ) • cayleyConstantProjection := by
  classical
  apply LinearMap.ext
  intro f
  funext g
  simp [cayleyGeneratorSum_action, cayleyRightTranslationSum,
    Finset.sum_const]

/-- Averaging after labelled Cayley adjacency also multiplies by the number
of labels. -/
theorem cayleyConstantProjection_mul_generatorSum_action
    (label : W → G) :
    cayleyConstantProjection *
          cayleyRightRegularRepresentation.asAlgebraHom
            (cayleyGeneratorSum label) =
      (Fintype.card W : ℂ) • cayleyConstantProjection := by
  classical
  apply LinearMap.ext
  intro f
  funext g
  change cayleyConstantProjection
      (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyGeneratorSum label) f) g =
    (Fintype.card W : ℂ) * cayleyConstantProjection f g
  rw [cayleyConstantProjection_apply]
  simp only [cayleyGeneratorSum_action, cayleyRightTranslationSum,
    cayleyConstantProjection_apply]
  rw [Finset.sum_comm]
  have hsum (a : W) : ∑ x : G, f (x * label a) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.mulRight (label a)) f
  simp_rw [hsum]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  ring

/-- The trace of a right translation is the size of the group for the
identity translation and zero otherwise. -/
theorem trace_cayleyRightRegularRepresentation (s : G) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation (G := G) s) =
      if s = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G)]
  simp only [Matrix.trace]
  by_cases hs : s = 1
  · subst s
    simp
  · simp only [if_neg hs]
    apply Finset.sum_eq_zero
    intro i _hi
    have his : i ≠ i * s := by
      intro h
      apply hs
      have hiEq : (1 : G) = s := by
        simpa [mul_assoc] using congrArg (fun x => i⁻¹ * x) h
      exact hiEq.symm
    simp [his]

/-- In the finite right regular representation, the trace of a group-algebra
element is the group order times its identity coefficient.  This is the
generic trace/count bridge used by the LPS Hecke calculation. -/
theorem trace_cayleyRightRegularRepresentation_asAlgebraHom
    (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom a) =
      (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      change LinearMap.trace ℂ (G → ℂ)
          (cayleyRightRegularRepresentation.asAlgebraHom
            (MonoidAlgebra.single g 1)) =
        (Fintype.card G : ℂ) * (MonoidAlgebra.single g 1).coeff 1
      rw [Representation.asAlgebraHom_single,
        one_smul, trace_cayleyRightRegularRepresentation]
      by_cases hg1 : g = 1
      · subst g
        simp
      · simp [hg1]
  | add a b iha ihb =>
      simp [map_add, iha, ihb, mul_add]
  | smul c a ih =>
      simp [map_smul, ih]
      ring

/-- The averaging projection onto constants has trace one. -/
@[simp] theorem trace_cayleyConstantProjection :
    LinearMap.trace ℂ (G → ℂ) (cayleyConstantProjection (G := G)) = 1 := by
  rw [cayleyConstantProjection, map_smul]
  change (Fintype.card G : ℂ)⁻¹ *
    LinearMap.trace ℂ (G → ℂ)
      (cayleyRightRegularRepresentation.asAlgebraHom cayleyGroupSum) = 1
  rw [trace_cayleyRightRegularRepresentation_asAlgebraHom]
  simp [cayleyGroupSum, Fintype.card_ne_zero]

/-- Acting by the centered generator sum is adjacency with the constant mode
subtracted. -/
theorem cayleyCenteredGeneratorSum_action
    (label : W → G) (f : G → ℂ) (g : G) :
    (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum label) f) g =
      cayleyRightTranslationSum label f g -
        ((Fintype.card W : ℂ) / (Fintype.card G : ℂ)) * ∑ h, f h := by
  classical
  simp [cayleyCenteredGeneratorSum, cayleyGeneratorSum_action,
    cayleyGroupSum_action]

/-- The centered right-regular adjacency is ordinary adjacency minus the
degree times the rank-one constant projection. -/
theorem cayleyCenteredGeneratorSum_action_eq_sub_projection
    (label : W → G) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum label) =
      cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum label) -
        (Fintype.card W : ℂ) • cayleyConstantProjection := by
  classical
  apply LinearMap.ext
  intro f
  funext g
  rw [cayleyCenteredGeneratorSum_action]
  simp [cayleyGeneratorSum_action, cayleyConstantProjection_apply]
  ring

/-- Centered Cayley adjacency annihilates the constant projection on the
right. -/
theorem cayleyCenteredGeneratorSum_action_mul_constantProjection
    (label : W → G) :
    cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyCenteredGeneratorSum label) * cayleyConstantProjection =
      0 := by
  rw [cayleyCenteredGeneratorSum_action_eq_sub_projection,
    sub_mul, cayleyGeneratorSum_action_mul_constantProjection,
    smul_mul_assoc, cayleyConstantProjection_mul_self]
  simp

/-- Centered Cayley adjacency annihilates the constant projection on the
left. -/
theorem cayleyConstantProjection_mul_centeredGeneratorSum_action
    (label : W → G) :
    cayleyConstantProjection *
          cayleyRightRegularRepresentation.asAlgebraHom
            (cayleyCenteredGeneratorSum label) =
      0 := by
  rw [cayleyCenteredGeneratorSum_action_eq_sub_projection,
    mul_sub, cayleyConstantProjection_mul_generatorSum_action,
    mul_smul_comm, cayleyConstantProjection_mul_self]
  simp

/-- The weighted adjacency operator of the labelled right Cayley multigraph
is exactly its right-translation sum, including label multiplicities. -/
theorem complexWeightedNeighborSum_rightCayleyGraph
    (label : W → G) (f : G → ℂ) (g : G) :
    SmallSetExpansion.complexWeightedNeighborSum
        (rightCayleyGraph label) f g =
      cayleyRightTranslationSum label f g := by
  classical
  unfold SmallSetExpansion.complexWeightedNeighborSum rightCayleyGraph
    cayleyRightTranslationSum
  calc
    (∑ h, ((Finset.univ.filter fun a : W => g * label a = h).card : ℂ) *
        f h) =
        ∑ h, ∑ a ∈ Finset.univ.filter (fun a : W => g * label a = h),
          f h := by
      apply Finset.sum_congr rfl
      intro h _hh
      simp
    _ = ∑ h, ∑ a ∈ Finset.univ.filter (fun a : W => g * label a = h),
          f (g * label a) := by
      apply Finset.sum_congr rfl
      intro h _hh
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, f (g * label a) :=
      Finset.sum_fiberwise (Finset.univ : Finset W)
        (fun a => g * label a) (fun a => f (g * label a))

/-- The centered Euclidean adjacency operator of a labelled Cayley graph is
exactly the right-regular action of the centered generator-sum element. -/
theorem centeredAdjacencyEuclidean_rightCayleyGraph_apply
    (label : W → G) (f : EuclideanSpace ℂ G) (g : G) :
    SmallSetExpansion.centeredAdjacencyEuclidean
        (rightCayleyGraph label) (Fintype.card W) f g =
      (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum label) (fun h => f h)) g := by
  classical
  rw [cayleyCenteredGeneratorSum_action]
  simp [SmallSetExpansion.centeredAdjacencyEuclidean,
    complexWeightedNeighborSum_rightCayleyGraph,
    SmallSetExpansion.inner_constantEuclideanVector]

/-- Canonical linear identification of ordinary finite functions with their
`L²` Euclidean-space presentation. -/
noncomputable def cayleyEuclideanLinearEquiv :
    (G → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ G :=
  (WithLp.linearEquiv 2 ℂ (G → ℂ)).symm

/-- Centered Euclidean Cayley adjacency is conjugate to the centered
right-regular operator on the ordinary function space. -/
theorem centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj
    (label : W → G) :
    SmallSetExpansion.centeredAdjacencyEuclidean
        (rightCayleyGraph label) (Fintype.card W) =
      (cayleyEuclideanLinearEquiv (G := G)).conj
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyCenteredGeneratorSum label)) := by
  apply LinearMap.ext
  intro f
  apply WithLp.ofLp_injective 2
  funext g
  rw [centeredAdjacencyEuclidean_rightCayleyGraph_apply]
  rfl

/-- Direct right-regular-action formulation of the complex mean-zero
operator bound on a labelled Cayley multigraph. -/
theorem hasMeanZeroComplexOperatorBound_rightCayleyGraph_iff
    (label : W → G) (spectral : ℝ) :
    SmallSetExpansion.HasMeanZeroComplexOperatorBound
        (rightCayleyGraph label) spectral ↔
      ∀ f : G → ℂ,
        (∑ g, f g) = 0 →
          (∑ g, ‖cayleyRightTranslationSum label f g‖ ^ 2) ≤
            spectral ^ 2 * ∑ g, ‖f g‖ ^ 2 := by
  simp only [SmallSetExpansion.HasMeanZeroComplexOperatorBound,
    complexWeightedNeighborSum_rightCayleyGraph]

end QEC.Coding.TannerLiftedProduct
