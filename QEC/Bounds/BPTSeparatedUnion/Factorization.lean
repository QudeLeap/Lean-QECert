import QEC.Bounds.BPTSeparatedUnion.Transport.Support
import QEC.Bounds.GeometricLocalityTradeoff.Entropy
noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v
namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem abcFactorization_eq_left_factorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    BPTEntropy.QuditSubsystem.abcFactorization A B hAB =
      composeUnitaryTransport A.registerFactorization
        (unitaryLTensor A.selectedSystem
          (BPTEntropy.QuditSubsystem.complementABCFactorization A B hAB)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  dsimp [composeUnitaryTransport]
  rw [BPTEntropy.QuditSubsystem.abcFactorization_apply_basis A B hAB labels]
  rw [A.registerFactorization_apply_basis labels]
  rw [unitaryLTensor_apply_tmul]
  rw [BPTEntropy.QuditSubsystem.complementABCFactorization_apply_basis A B hAB]
  rw [BPTEntropy.QuditSubsystem.splitComplementABCLabel_splitLabel]
  rfl

/--
After the explicit `A`/`B` swap, the same three-coordinate factorization is
obtained by first splitting off `B` and then splitting its complement into
`A tensor C`.
-/
theorem bacFactorization_eq_right_factorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
    composeUnitaryTransport
        (BPTEntropy.QuditSubsystem.abcFactorization A B hAB)
        (BPTEntropy.abcToBac A.selectedSystem B.selectedSystem C.complementSystem) =
      composeUnitaryTransport B.registerFactorization
        (unitaryLTensor B.selectedSystem
          (BPTEntropy.QuditSubsystem.complementBACFactorization A B hAB)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  dsimp [composeUnitaryTransport]
  rw [BPTEntropy.QuditSubsystem.abcFactorization_apply_basis A B hAB labels]
  simp only [BPTEntropy.abcToBac_apply_tmul]
  rw [B.registerFactorization_apply_basis labels]
  rw [unitaryLTensor_apply_tmul]
  rw [BPTEntropy.QuditSubsystem.complementBACFactorization_apply_basis A B hAB]
  rw [BPTEntropy.QuditSubsystem.splitComplementBACLabel_splitLabel]
  rfl

/-- In `A tensor (B tensor C)` coordinates, an `A`-local operator is literal left action. -/
theorem abcFactorization_conj_extend_left
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (Aoperator : Semantics.Operator (M.regionSubsystem left).selectedSystem) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    (BPTEntropy.QuditSubsystem.abcFactorization A B hAB).conjOperator
      (A.extendLocalToRegister Aoperator) =
      TensorProduct.map Aoperator
        (1 : Semantics.Operator
          (Semantics.CompositeSystem B.selectedSystem
            (BPTEntropy.QuditSubsystem.unionSubsystem A B).complementSystem)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  rw [M.abcFactorization_eq_left_factorization left right hdisjoint]
  rw [composeUnitaryTransport_conjOperator]
  rw [registerFactorization_conj_extendLocalToRegister]
  exact unitaryLTensor_conj_tensorMap_right
    A.selectedSystem (BPTEntropy.QuditSubsystem.complementABCFactorization A B hAB) Aoperator

/-- The `A`/`B` swap sends a right-factor local action to literal left action. -/
theorem abcToBac_conj_right_local
    {A B C : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (Boperator : Semantics.Operator B) :
    (BPTEntropy.abcToBac A B C).conjOperator
      (TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map Boperator (1 : Semantics.Operator C))) =
      TensorProduct.map Boperator
        (TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator C)) := by
  let U := BPTEntropy.abcToBac A B C
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul b rest =>
      induction rest using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
          have hsymm : U.symm (b ⊗ₜ[Complex] (a ⊗ₜ[Complex] c)) =
              a ⊗ₜ[Complex] (b ⊗ₜ[Complex] c) := by
            apply U.toLinearEquiv.injective
            simpa [U, Semantics.UnitaryTransport.symm_toLinearEquiv] using
              (BPTEntropy.abcToBac_apply_tmul A B C a b c).symm
          change U
              ((TensorProduct.map (1 : Semantics.Operator A)
                (TensorProduct.map Boperator (1 : Semantics.Operator C)))
                (U.symm (b ⊗ₜ[Complex] (a ⊗ₜ[Complex] c)))) = _
          rw [hsymm]
          simp only [TensorProduct.map_tmul, Module.End.one_apply]
          exact BPTEntropy.abcToBac_apply_tmul A B C a (Boperator b) c
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.tmul_add, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add x y hx hy => simp [map_add, hx, hy]

/-- In `A tensor (B tensor C)` coordinates, a `B`-local operator is literal middle action. -/
theorem abcFactorization_conj_extend_right
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (Boperator : Semantics.Operator (M.regionSubsystem right).selectedSystem) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
    (BPTEntropy.QuditSubsystem.abcFactorization A B hAB).conjOperator
      (B.extendLocalToRegister Boperator) =
      TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
        (TensorProduct.map Boperator (1 : Semantics.Operator C.complementSystem)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  let Uabc := BPTEntropy.QuditSubsystem.abcFactorization A B hAB
  let Uswap := BPTEntropy.abcToBac A.selectedSystem B.selectedSystem C.complementSystem
  let Ubac := composeUnitaryTransport Uabc Uswap
  have hbac : Ubac.conjOperator (B.extendLocalToRegister Boperator) =
      TensorProduct.map Boperator
        (TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (1 : Semantics.Operator C.complementSystem)) := by
    rw [show Ubac = composeUnitaryTransport B.registerFactorization
      (unitaryLTensor B.selectedSystem
        (BPTEntropy.QuditSubsystem.complementBACFactorization A B hAB)) by
      simpa [Ubac, Uabc, Uswap] using
        (M.bacFactorization_eq_right_factorization left right hdisjoint)]
    rw [composeUnitaryTransport_conjOperator]
    rw [registerFactorization_conj_extendLocalToRegister]
    rw [unitaryLTensor_conj_tensorMap_right]
    rw [TensorProduct.map_one]
  have hswap : Uswap.conjOperator
      (TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
        (TensorProduct.map Boperator (1 : Semantics.Operator C.complementSystem))) =
      TensorProduct.map Boperator
        (TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (1 : Semantics.Operator C.complementSystem)) :=
    abcToBac_conj_right_local Boperator
  calc
    Uabc.conjOperator (B.extendLocalToRegister Boperator) =
        Uswap.symm.conjOperator
          (Uswap.conjOperator (Uabc.conjOperator (B.extendLocalToRegister Boperator))) :=
      (Uswap.symm_conjOperator_conjOperator _).symm
    _ = Uswap.symm.conjOperator (Ubac.conjOperator (B.extendLocalToRegister Boperator)) := by
      rw [composeUnitaryTransport_conjOperator]
    _ = Uswap.symm.conjOperator
        (TensorProduct.map Boperator
          (TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
            (1 : Semantics.Operator C.complementSystem))) := by rw [hbac]
    _ = Uswap.symm.conjOperator
        (Uswap.conjOperator
          (TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
            (TensorProduct.map Boperator (1 : Semantics.Operator C.complementSystem)))) := by
      rw [hswap]
    _ = TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
        (TensorProduct.map Boperator (1 : Semantics.Operator C.complementSystem)) :=
      Uswap.symm_conjOperator_conjOperator _

/-- Split the selected labels of `left union right` into the two disjoint regions. -/
def splitUnionSelectedLabel
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions ×
      Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions :=
  (fun site => labels ⟨site, Finset.mem_union_left right site.property⟩,
    fun site => labels ⟨site, Finset.mem_union_right left site.property⟩)

/-- Recombine two disjoint selected labels into a label on their union. -/
def recombineUnionSelectedLabel
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (labels : Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions ×
      Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions) :
    Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions :=
  fun site => if hleft : (site : L.Site) ∈ left then
    labels.1 ⟨site, hleft⟩
  else
    labels.2 ⟨site, (Finset.mem_union.mp site.property).resolve_left hleft⟩

/-- The selected union is concretely equivalent to the product of the two disjoint regions. -/
def unionSelectedLabelFactorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions ≃
      Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions ×
        Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions where
  toFun := M.splitUnionSelectedLabel left right
  invFun := M.recombineUnionSelectedLabel left right
  left_inv := by
    intro labels
    funext site
    by_cases hleft : (site : L.Site) ∈ left
    · simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hleft]
    · simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hleft]
  right_inv := by
    rintro ⟨leftLabels, rightLabels⟩
    apply Prod.ext
    · funext site
      have hleft : (site : L.Site) ∈ left := site.property
      simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hleft]
    · funext site
      have hnotleft : (site : L.Site) ∉ left := by
        intro hleft
        exact (Finset.disjoint_left.mp hdisjoint) hleft site.property
      simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hnotleft]

/-- The unitary coordinate factorization of the concrete selected union. -/
noncomputable def unionSelectedFactorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    Semantics.UnitaryTransport (M.regionSubsystem (left ∪ right)).selectedSystem
      (Semantics.CompositeSystem (M.regionSubsystem left).selectedSystem
        (M.regionSubsystem right).selectedSystem) := by
  let sourceBasis := EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions) Complex
  let leftBasis := EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions) Complex
  let rightBasis := EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions) Complex
  let targetBasis := leftBasis.tensorProduct rightBasis
  let U := sourceBasis.equiv targetBasis (M.unionSelectedLabelFactorization left right hdisjoint)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- Basis action of the selected-union factorization. -/
theorem unionSelectedFactorization_apply_basis
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    M.unionSelectedFactorization left right hdisjoint
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
          Complex labels) =
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions) Complex
        (M.splitUnionSelectedLabel left right labels).1) ⊗ₜ[Complex]
      (EuclideanSpace.basisFun
        (Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions) Complex
        (M.splitUnionSelectedLabel left right labels).2) := by
  dsimp [unionSelectedFactorization]
  rw [OrthonormalBasis.equiv_apply_basis]
  rw [OrthonormalBasis.tensorProduct_apply']
  simp [unionSelectedLabelFactorization]

/--
The global `A tensor (B tensor C)` coordinates are the union split followed by
the explicit selected-union factorization and reassociation.
-/
theorem abcFactorization_eq_union_factorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let U := M.regionSubsystem (left ∪ right)
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
    BPTEntropy.QuditSubsystem.abcFactorization A B hAB =
      composeUnitaryTransport U.registerFactorization
        (composeUnitaryTransport
          (unitaryRTensor (M.unionSelectedFactorization left right hdisjoint) C.complementSystem)
          (tensorAssociatorUnitary A.selectedSystem B.selectedSystem C.complementSystem)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let U := M.regionSubsystem (left ∪ right)
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  dsimp [composeUnitaryTransport]
  rw [BPTEntropy.QuditSubsystem.abcFactorization_apply_basis A B hAB labels]
  rw [U.registerFactorization_apply_basis labels]
  change _ =
    tensorAssociatorUnitary A.selectedSystem B.selectedSystem C.complementSystem
      (((M.unionSelectedFactorization left right hdisjoint)
        (EuclideanSpace.basisFun (Semantics.Qudit.Label U.selectedDimensions) Complex
          (U.splitLabel labels).1)) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Semantics.Qudit.Label U.complementDimensions) Complex
          (U.splitLabel labels).2))
  rw [M.unionSelectedFactorization_apply_basis left right hdisjoint]
  erw [tensorAssociatorUnitary_apply_tmul]
  rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "abcFactorization_conj_extend_union_rankOne"

set_option maxHeartbeats 4000000 in
/--
In the common `A tensor (B tensor C)` coordinates, a rank-one matrix unit on
the concrete selected union is the product of the corresponding rank-one
matrix units on the two separated selected regions.
-/
theorem abcFactorization_conj_extend_union_rankOne
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (labels labels' : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let R := M.regionSubsystem (left ∪ right)
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
    let leftLabels := (M.splitUnionSelectedLabel left right labels).1
    let rightLabels := (M.splitUnionSelectedLabel left right labels).2
    let leftLabels' := (M.splitUnionSelectedLabel left right labels').1
    let rightLabels' := (M.splitUnionSelectedLabel left right labels').2
    (BPTEntropy.QuditSubsystem.abcFactorization A B hAB).conjOperator
      (R.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
            Complex labels')).toLinearMap) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels')).toLinearMap
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
              Complex rightLabels)
            (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
              Complex rightLabels')).toLinearMap
          (1 : Semantics.Operator C.complementSystem)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let R := M.regionSubsystem (left ∪ right)
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  have htransport :
      (unitaryRTensor (M.unionSelectedFactorization left right hdisjoint)
        (BPTEntropy.QuditSubsystem.unionSubsystem
          (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem).conjOperator
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun
              (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
              Complex labels)
            (EuclideanSpace.basisFun
              (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
              Complex labels')).toLinearMap
          (1 : Semantics.Operator
            (BPTEntropy.QuditSubsystem.unionSubsystem
              (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem)) =
        TensorProduct.map
          ((M.unionSelectedFactorization left right hdisjoint).conjOperator
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun
                (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
                Complex labels)
              (EuclideanSpace.basisFun
                (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
                Complex labels')).toLinearMap)
          (1 : Semantics.Operator
            (BPTEntropy.QuditSubsystem.unionSubsystem
              (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem) := by
    exact unitaryRTensor_conj_tensorMap_left
      (M.unionSelectedFactorization left right hdisjoint)
        (BPTEntropy.QuditSubsystem.unionSubsystem
          (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem _
  rw [M.abcFactorization_eq_union_factorization left right hdisjoint]
  erw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [registerFactorization_conj_extendLocalToRegister]
  refine (congrArg
    (tensorAssociatorUnitary A.selectedSystem B.selectedSystem C.complementSystem).conjOperator
    htransport).trans ?_
  rw [Semantics.QuditSubsystem.conjOperator_rankOne]
  rw [M.unionSelectedFactorization_apply_basis left right hdisjoint labels,
    M.unionSelectedFactorization_apply_basis left right hdisjoint labels']
  rw [← Semantics.DensityOperator.tensorMap_rankOne]
  exact tensorAssociatorUnitary_conj_tensorMap _ _ _

/--
The preceding coordinate identity reflects back to the physical register as a
product of one local matrix unit on each separated region.
-/
theorem extend_union_rankOne_eq_product
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (labels labels' : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let R := M.regionSubsystem (left ∪ right)
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let leftLabels := (M.splitUnionSelectedLabel left right labels).1
    let rightLabels := (M.splitUnionSelectedLabel left right labels).2
    let leftLabels' := (M.splitUnionSelectedLabel left right labels').1
    let rightLabels' := (M.splitUnionSelectedLabel left right labels').2
    R.extendLocalToRegister
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
        (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
          Complex labels')).toLinearMap =
      A.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels')).toLinearMap *
      B.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
            Complex rightLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
            Complex rightLabels')).toLinearMap := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let R := M.regionSubsystem (left ∪ right)
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  let U := BPTEntropy.QuditSubsystem.abcFactorization A B (by
    simpa [A, B] using hdisjoint)
  let leftUnit := (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels).1)
    (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels').1)).toLinearMap
  let rightUnit := (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels).2)
    (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels').2)).toLinearMap
  let unionUnit := (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
    (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
      Complex labels')).toLinearMap
  let target : Semantics.Operator
      (Semantics.CompositeSystem A.selectedSystem
        (Semantics.CompositeSystem B.selectedSystem C.complementSystem)) :=
    TensorProduct.map leftUnit
      (TensorProduct.map rightUnit (1 : Semantics.Operator C.complementSystem))
  have hunion : U.conjOperator (R.extendLocalToRegister unionUnit) = target := by
    simpa [U, target, unionUnit, leftUnit, rightUnit] using
      M.abcFactorization_conj_extend_union_rankOne left right hdisjoint labels labels'
  have hproduct : U.conjOperator
      (A.extendLocalToRegister leftUnit * B.extendLocalToRegister rightUnit) = target := by
    rw [Semantics.UnitaryTransport.conjOperator_mul]
    rw [M.abcFactorization_conj_extend_left left right hdisjoint]
    rw [M.abcFactorization_conj_extend_right left right hdisjoint]
    change
      TensorProduct.map leftUnit
        (1 : Semantics.Operator (Semantics.CompositeSystem B.selectedSystem C.complementSystem)) *
        TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (TensorProduct.map rightUnit (1 : Semantics.Operator C.complementSystem)) = target
    rw [show (1 : Semantics.Operator (Semantics.CompositeSystem B.selectedSystem
      C.complementSystem)) = TensorProduct.map
        (1 : Semantics.Operator B.selectedSystem)
        (1 : Semantics.Operator C.complementSystem) by
      symm
      exact TensorProduct.map_one]
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    simp [target]
  calc
    R.extendLocalToRegister unionUnit = U.symm.conjOperator
        (U.conjOperator (R.extendLocalToRegister unionUnit)) :=
      (U.symm_conjOperator_conjOperator _).symm
    _ = U.symm.conjOperator target := by rw [hunion]
    _ = U.symm.conjOperator
        (U.conjOperator (A.extendLocalToRegister leftUnit *
          B.extendLocalToRegister rightUnit)) := by rw [hproduct]
    _ = A.extendLocalToRegister leftUnit * B.extendLocalToRegister rightUnit :=
      U.symm_conjOperator_conjOperator _

/--
Scalar compression for all products of separated local operators extends to
all local operators on their concrete union by finite matrix-unit expansion.
-/
theorem allLocalScalarCompression_union_of_product
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (hproduct : ∀ (A : Semantics.Operator (M.regionSubsystem left).selectedSystem)
      (B : Semantics.Operator (M.regionSubsystem right).selectedSystem),
      Semantics.QuditSubsystem.ScalarCompression M.codeSpace
        ((M.regionSubsystem left).extendLocalToRegister A *
          (M.regionSubsystem right).extendLocalToRegister B)) :
    Semantics.QuditSubsystem.AllLocalScalarCompression M.codeSpace
      (M.regionSubsystem (left ∪ right)) := by
  let R := M.regionSubsystem (left ∪ right)
  let basis := EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex
  apply Semantics.QuditSubsystem.allLocalScalarCompression_of_rankOne_basis basis
  intro labels labels'
  rw [M.extend_union_rankOne_eq_product left right hdisjoint labels labels']
  exact hproduct _ _

/-- Reassociation commutes with an operator on its final tensor factor. -/
theorem tensorAssociator_right_intertwines
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J] (R : Semantics.Operator J) :
    (TensorProduct.map (1 : Semantics.Operator H)
      (TensorProduct.map (1 : Semantics.Operator K) R)).comp
        (tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap =
      (tensorAssociatorUnitary H K J).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map
          (1 : Semantics.Operator (Semantics.CompositeSystem H K)) R) := by
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => rfl
  | tmul hk j =>
      induction hk using TensorProduct.induction_on with
      | zero => rfl
      | tmul h k => rfl
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond

end BPTCommutingProjectorModel
end Bounds
end QEC
