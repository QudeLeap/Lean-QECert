import QEC.Coding.ExpanderCodes.LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Coordinates for a free finite group action

This file isolates the noncomputable choice of one representative in every
orbit.  Unlike a bare cardinality argument, `freeOrbitEquiv` also records the
group coordinate and proves how that coordinate changes under the action.
That compatibility is the bridge needed to turn an equivariant Tanner map
into a group-algebra matrix.
-/

noncomputable section

namespace QEC.Coding.BalancedProduct.FreeOrbitCoordinates

universe u v

variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

/-- The orbit index type of the action. -/
abbrev OrbitIndex := Quotient (MulAction.orbitRel G X)

/-- The orbit containing a point. -/
def orbitOf (x : X) : OrbitIndex G X := Quotient.mk'' x

/-- A fixed representative of an orbit. -/
def orbitRep (o : OrbitIndex G X) : X := Quotient.out o

theorem exists_smul_orbitRep_eq (x : X) :
    ∃ g : G, g • orbitRep G X (orbitOf G X x) = x := by
  have hout :
      Quotient.mk'' (orbitRep G X (orbitOf G X x)) = orbitOf G X x :=
    Quotient.out_eq' _
  have hrel :
      MulAction.orbitRel G X (orbitRep G X (orbitOf G X x)) x :=
    Quotient.eq''.mp hout
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  rcases hrel with ⟨g, hg⟩
  exact ⟨g⁻¹, by simpa using (congrArg (fun y => g⁻¹ • y) hg).symm⟩

/-- The unique group element carrying the chosen representative to `x`. -/
def groupCoordinate [IsCancelSMul G X] (x : X) : G :=
  Classical.choose (exists_smul_orbitRep_eq G X x)

@[simp]
theorem groupCoordinate_smul_orbitRep [IsCancelSMul G X] (x : X) :
    groupCoordinate G X x • orbitRep G X (orbitOf G X x) = x :=
  Classical.choose_spec (exists_smul_orbitRep_eq G X x)

@[simp]
theorem orbitOf_smul (g : G) (x : X) :
    orbitOf G X (g • x) = orbitOf G X x := by
  apply Quotient.sound
  exact (MulAction.orbitRel_apply).2 (MulAction.mem_orbit x g)

@[simp]
theorem groupCoordinate_smul [IsCancelSMul G X] (g : G) (x : X) :
    groupCoordinate G X (g • x) = g * groupCoordinate G X x := by
  apply IsCancelSMul.right_cancel _ _ (orbitRep G X (orbitOf G X x))
  rw [mul_smul]
  rw [groupCoordinate_smul_orbitRep]
  simpa using groupCoordinate_smul_orbitRep G X (g • x)

/-- A free action is not merely equicardinal with orbit representatives times
the group: this equivalence uses the action coordinate itself. -/
def freeOrbitEquiv [IsCancelSMul G X] :
    X ≃ OrbitIndex G X × G where
  toFun x := (orbitOf G X x, groupCoordinate G X x)
  invFun og := og.2 • orbitRep G X og.1
  left_inv x := groupCoordinate_smul_orbitRep G X x
  right_inv og := by
    rcases og with ⟨o, g⟩
    apply Prod.ext
    · change orbitOf G X (g • orbitRep G X o) = o
      rw [orbitOf_smul]
      exact Quotient.out_eq' o
    · change groupCoordinate G X (g • orbitRep G X o) = g
      rw [groupCoordinate_smul]
      have hcoord : groupCoordinate G X (orbitRep G X o) = 1 := by
        apply IsCancelSMul.right_cancel _ _ (orbitRep G X o)
        have hs := groupCoordinate_smul_orbitRep G X (orbitRep G X o)
        have horbit : orbitOf G X (orbitRep G X o) = o := Quotient.out_eq' o
        rw [horbit] at hs
        simpa using hs
      simp [hcoord]

@[simp]
theorem freeOrbitEquiv_apply [IsCancelSMul G X] (x : X) :
    freeOrbitEquiv G X x = (orbitOf G X x, groupCoordinate G X x) := rfl

@[simp]
theorem freeOrbitEquiv_symm_apply [IsCancelSMul G X]
    (o : OrbitIndex G X) (g : G) :
    (freeOrbitEquiv G X).symm (o, g) = g • orbitRep G X o := rfl

section MatrixCompression

variable {F : Type*} [Semiring F]
variable {R : Type*} {C : Type*}
variable [MulAction G R] [MulAction G C]
variable [IsCancelSMul G R] [IsCancelSMul G C]
variable [Fintype G]

/-- Compress a simultaneously equivariant matrix along its free group
orbits.  The coefficient at `h` compares `h` times the chosen row
representative with the chosen column representative. -/
def groupAlgebraMatrix
    (P : Matrix R C F) :
    Matrix (OrbitIndex G R) (OrbitIndex G C) (MonoidAlgebra F G) :=
  fun ro co => MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun h =>
    P (h • orbitRep G R ro) (orbitRep G C co))

@[simp]
theorem groupAlgebraMatrix_apply
    (P : Matrix R C F) (ro : OrbitIndex G R) (co : OrbitIndex G C) (h : G) :
    (groupAlgebraMatrix G P ro co).coeff h =
      P (h • orbitRep G R ro) (orbitRep G C co) := rfl

/-- The compressed matrix recovers the original matrix in free-orbit
coordinates.  This is the exact relative-coordinate convention used by
`LiftedProduct.rightRegularMatrix`. -/
theorem rightRegularMatrix_groupAlgebraMatrix
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (ro : OrbitIndex G R) (co : OrbitIndex G C) (go gi : G) :
    QEC.Coding.LiftedProduct.rightRegularMatrix
        (groupAlgebraMatrix G P ro co) go gi =
      P ((freeOrbitEquiv G R).symm (ro, go))
        ((freeOrbitEquiv G C).symm (co, gi)) := by
  change P ((gi⁻¹ * go) • orbitRep G R ro) (orbitRep G C co) =
    P (go • orbitRep G R ro) (gi • orbitRep G C co)
  have h := hP gi⁻¹ (go • orbitRep G R ro) (gi • orbitRep G C co)
  simpa [smul_smul] using h

/-- Matrix-vector multiplication by the right-regular expansion is exactly
matrix-vector multiplication by the original equivariant matrix after
reindexing the column coordinates. -/
theorem sum_rightRegularMatrix_groupAlgebraMatrix
    [Fintype C] [Fintype (OrbitIndex G C)]
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (z : C → F)
    (ro : OrbitIndex G R) (go : G) :
    (∑ co : OrbitIndex G C, ∑ gi : G,
      QEC.Coding.LiftedProduct.rightRegularMatrix
          (groupAlgebraMatrix G P ro co) go gi *
        z ((freeOrbitEquiv G C).symm (co, gi))) =
      ∑ c : C,
        P ((freeOrbitEquiv G R).symm (ro, go)) c * z c := by
  calc
    _ = ∑ p : OrbitIndex G C × G,
        QEC.Coding.LiftedProduct.rightRegularMatrix
            (groupAlgebraMatrix G P ro p.1) go p.2 *
          z ((freeOrbitEquiv G C).symm p) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (freeOrbitEquiv G C).symm
      intro p
      rcases p with ⟨co, gi⟩
      rw [rightRegularMatrix_groupAlgebraMatrix G P hP]

/-- The analogous matrix-vector identity for the star-transpose. -/
theorem sum_rightRegularMatrix_starTranspose_groupAlgebraMatrix
    [Fintype R] [Fintype (OrbitIndex G R)]
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (y : R → F)
    (co : OrbitIndex G C) (go : G) :
    (∑ ro : OrbitIndex G R, ∑ gi : G,
      QEC.Coding.LiftedProduct.rightRegularMatrix
          (QEC.Coding.LiftedProduct.starTranspose
            (groupAlgebraMatrix G P) co ro) go gi *
        y ((freeOrbitEquiv G R).symm (ro, gi))) =
      ∑ r : R,
        P r ((freeOrbitEquiv G C).symm (co, go)) * y r := by
  calc
    _ = ∑ p : OrbitIndex G R × G,
        QEC.Coding.LiftedProduct.rightRegularMatrix
            (QEC.Coding.LiftedProduct.starTranspose
              (groupAlgebraMatrix G P) co p.1) go p.2 *
          y ((freeOrbitEquiv G R).symm p) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (freeOrbitEquiv G R).symm
      intro p
      rcases p with ⟨ro, gi⟩
      rw [show QEC.Coding.LiftedProduct.rightRegularMatrix
          (QEC.Coding.LiftedProduct.starTranspose
            (groupAlgebraMatrix G P) co ro) go gi =
          QEC.Coding.LiftedProduct.rightRegularMatrix
            (groupAlgebraMatrix G P ro co) gi go by
        exact congrFun (congrFun
          (QEC.Coding.LiftedProduct.rightRegularMatrix_starTranspose_entry
            (groupAlgebraMatrix G P) ro co) go) gi]
      rw [rightRegularMatrix_groupAlgebraMatrix G P hP]

end MatrixCompression

end QEC.Coding.BalancedProduct.FreeOrbitCoordinates
