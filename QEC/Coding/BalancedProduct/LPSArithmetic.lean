import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The upper-unipotent subgroup used in the BE20 LPS quotient

Breuckmann--Eberhardt use the image in `PGL(2, q)` of the matrices

`[1 x; 0 1]`, `x \in 𝔽_q`.

This file constructs that image from Mathlib's actual general linear group and
proves the elementary facts needed before the LPS generator calculation: the
projective map is still injective, its image has the expected cardinality, and
right translation on the ambient projective group is free.  No expansion,
spectral, quotient-condition, or code-parameter conclusion is included as
data.
-/

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSArithmetic

open Matrix

variable {R : Type*} [CommRing R]

/-- The upper-unipotent additive character, projected to `PGL(2, R)`. -/
def upperUnipotentPGL : AddChar R PGL(2, R) :=
  Matrix.ProjGenLinGroup.mk.compAddChar
    (Matrix.GeneralLinearGroup.upperRightHom (R := R))

@[simp]
theorem upperUnipotentPGL_apply (x : R) :
    upperUnipotentPGL x =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.upperRightHom x) :=
  rfl

@[simp]
theorem upperUnipotentPGL_zero : upperUnipotentPGL (0 : R) = 1 :=
  AddChar.map_zero_eq_one _

@[simp]
theorem upperUnipotentPGL_add (x y : R) :
    upperUnipotentPGL (x + y) =
      upperUnipotentPGL x * upperUnipotentPGL y :=
  AddChar.map_add_eq_mul _ _ _

/-- No two distinct upper-unipotent matrices become equal after quotienting by
scalar matrices.  The diagonal entries force the scalar to be one, after
which the upper-right entry recovers the parameter. -/
theorem upperUnipotentPGL_injective :
    Function.Injective (upperUnipotentPGL (R := R)) := by
  intro x y hxy
  have hzero : upperUnipotentPGL (x - y) = 1 := by
    rw [sub_eq_add_neg, upperUnipotentPGL_add]
    rw [AddChar.map_neg_eq_inv, hxy, mul_inv_cancel]
  rw [upperUnipotentPGL_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzero
  rcases hzero with ⟨u, hu⟩
  have h01 := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 1) hu
  exact sub_eq_zero.mp (by
    simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using h01.symm)

/-- The concrete upper-unipotent subgroup of `PGL(2, R)`. -/
def upperUnipotentSubgroup : Subgroup PGL(2, R) :=
  AddSubgroup.toSubgroup
    ((upperUnipotentPGL (R := R)).toAddMonoidHom.range)

@[simp]
theorem mem_upperUnipotentSubgroup_iff (g : PGL(2, R)) :
    g ∈ upperUnipotentSubgroup (R := R) ↔
      ∃ x : R, upperUnipotentPGL x = g := by
  rfl

theorem upperUnipotentPGL_mem (x : R) :
    upperUnipotentPGL x ∈ upperUnipotentSubgroup (R := R) := by
  exact ⟨x, rfl⟩

/-- The parameterization of the upper-unipotent subgroup. -/
noncomputable def upperUnipotentEquiv :
    R ≃ upperUnipotentSubgroup (R := R) where
  toFun x := ⟨upperUnipotentPGL x, upperUnipotentPGL_mem x⟩
  invFun g := Classical.choose (mem_upperUnipotentSubgroup_iff g |>.mp g.property)
  left_inv x := by
    have hx := Classical.choose_spec
      (mem_upperUnipotentSubgroup_iff (upperUnipotentPGL x) |>.mp
        (upperUnipotentPGL_mem x))
    apply upperUnipotentPGL_injective
    exact hx
  right_inv g := by
    apply Subtype.ext
    exact Classical.choose_spec
      (mem_upperUnipotentSubgroup_iff (g : PGL(2, R)) |>.mp g.property)

noncomputable instance upperUnipotentSubgroupFintype [Fintype R] :
    Fintype (upperUnipotentSubgroup (R := R)) :=
  Fintype.ofEquiv R (upperUnipotentEquiv (R := R))

/-- The upper-unipotent subgroup has exactly as many elements as the base
ring.  In the BE20 specialization `R = ZMod q`, this is the asserted order
`q`. -/
theorem card_upperUnipotentSubgroup [Fintype R] :
    Fintype.card (upperUnipotentSubgroup (R := R)) = Fintype.card R := by
  exact (Fintype.card_congr (upperUnipotentEquiv (R := R))).symm

theorem card_upperUnipotentSubgroup_zmod (q : ℕ) [NeZero q] :
    Fintype.card (upperUnipotentSubgroup (R := ZMod q)) = q := by
  rw [card_upperUnipotentSubgroup, ZMod.card]

/-- Right multiplication by a subgroup element fixes an ambient PGL vertex
only for the identity.  This is the vertex-freeness used by the balanced
product; edge-freeness additionally requires the LPS quotient condition and
is deliberately not asserted here. -/
theorem right_mul_eq_self_iff
    (g : PGL(2, R)) (h : upperUnipotentSubgroup (R := R)) :
    g * (h : PGL(2, R)) = g ↔ h = 1 := by
  constructor
  · intro hfix
    apply Subtype.ext
    have heq : g * (h : PGL(2, R)) = g * 1 := by simpa using hfix
    exact mul_left_cancel heq
  · rintro rfl
    simp

section DeterminantSquareClass

/-- Equality in `PGL(2, R)` preserves whether the determinant of a lift is a
square.  This is the rank-two reason the determinant square class descends to
the projective quotient: changing a lift multiplies its determinant by the
square of a scalar unit. -/
theorem det_isSquare_iff_of_projective_eq
    {A B : GL (Fin 2) R}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    IsSquare A.det ↔ IsSquare B.det := by
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) R)) A =
      QuotientGroup.mk' (Subgroup.center (GL (Fin 2) R)) B at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hAz⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rcases hz with ⟨u, rfl⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hAz
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at hdet
  constructor
  · intro hA
    rw [← hdet]
    exact hA.mul (IsSquare.sq u)
  · intro hB
    have hBinv : IsSquare (B.det * (u⁻¹ ^ 2)) :=
      hB.mul (IsSquare.sq u⁻¹)
    convert hBinv using 1
    calc
      A.det = A.det * (u ^ 2 * u⁻¹ ^ 2) := by simp
      _ = (A.det * u ^ 2) * u⁻¹ ^ 2 := by ac_rfl
      _ = B.det * u⁻¹ ^ 2 := by rw [hdet]

/-- The determinant square class of a projective matrix, expressed without
choosing or storing a distinguished lift. -/
def ProjectiveDetIsSquare (g : PGL(2, R)) : Prop :=
  ∃ A : GL (Fin 2) R,
    Matrix.ProjGenLinGroup.mk A = g ∧ IsSquare A.det

theorem projectiveDetIsSquare_mk_iff (A : GL (Fin 2) R) :
    ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) ↔ IsSquare A.det := by
  constructor
  · rintro ⟨B, hBA, hB⟩
    exact (det_isSquare_iff_of_projective_eq hBA).mp hB
  · intro hA
    exact ⟨A, rfl, hA⟩

theorem not_projectiveDetIsSquare_mk_of_val
    (A : GL (Fin 2) R)
    (hA : ¬ IsSquare (A.det : R)) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  rw [projectiveDetIsSquare_mk_iff]
  rintro ⟨u, hu⟩
  apply hA
  exact ⟨(u : R), congrArg Units.val hu⟩

/-- A lift whose determinant is a quadratic residue has square projective
determinant.  This is the elementary determinant-class step used by the
`PSL(2,q)` branch of the LPS construction. -/
theorem projectiveDetIsSquare_mk_of_det
    {p q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (p : ZMod q))
    (hpq : (p : ZMod q) ≠ 0)
    (hq : legendreSym q p = 1) :
    ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  rw [projectiveDetIsSquare_mk_iff]
  rcases (legendreSym.eq_one_iff' (p := q) (a := p) hpq).mp hq with ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hpq
    simpa [hzero] using hx
  let u : (ZMod q)ˣ := Units.mk0 x hx0
  refine ⟨u, Units.ext ?_⟩
  simpa [u, hdet] using hx

/-- A lift whose determinant is a quadratic nonresidue has nonsquare
projective determinant. -/
theorem not_projectiveDetIsSquare_mk_of_det
    {p q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (p : ZMod q))
    (hq : legendreSym q p = -1) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  apply not_projectiveDetIsSquare_mk_of_val A
  rw [hdet]
  exact (legendreSym.eq_neg_one_iff' (p := q) (a := p)).mp hq

/-- In rank two, the image of `PSL(2,R)` inside `PGL(2,R)` is exactly the
square-determinant class.  The forward direction rescales a square-determinant
lift to determinant one; the reverse direction uses the determinant-one
representative of a projective special-linear element. -/
theorem projectiveDetIsSquare_iff_mem_range_toPGL
    (g : PGL(2, R)) :
    ProjectiveDetIsSquare g ↔
      g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := R)).range := by
  constructor
  · rintro ⟨A, hAg, ⟨k, hk⟩⟩
    let r : Rˣ := k⁻¹
    have hr : r ^ 2 * A.det = 1 := by
      rw [hk]
      simp [r, pow_two]
    have hrMatrix : Matrix.det (r.1 • A.1) = 1 := by
      simpa [Matrix.det_smul] using congrArg Units.val hr
    let X : SL(2, R) := ⟨r.1 • A.1, hrMatrix⟩
    refine ⟨(QuotientGroup.mk X : PSL(2, R)), ?_⟩
    change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (QuotientGroup.mk X : PSL(2, R)) = g
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
    calc
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL X) =
          Matrix.ProjGenLinGroup.mk A := by
        rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
        refine ⟨r⁻¹, ?_⟩
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [X, r, Matrix.SpecialLinearGroup.toGL, Matrix.mul_apply,
            mul_comm, mul_assoc]
      _ = g := hAg
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H X =>
        rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
          projectiveDetIsSquare_mk_iff]
        simp

/-- The exact determinant calculation needed for the BE20 choice `p = 401`:
an LPS lift with determinant `401` has nonsquare projective determinant at
every admissible prime `q`. -/
theorem not_projectiveDetIsSquare_mk_of_det_401
    {q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (401 : ZMod q))
    (hq : legendreSym q 401 = -1) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  exact not_projectiveDetIsSquare_mk_of_det A hdet hq

theorem projectiveDetIsSquare_upperUnipotent (x : R) :
    ProjectiveDetIsSquare (upperUnipotentPGL x) := by
  rw [upperUnipotentPGL_apply, projectiveDetIsSquare_mk_iff]
  have hdet :
      (Matrix.GeneralLinearGroup.upperRightHom x).det = (1 : Rˣ) := by
    ext
    simp [Matrix.GeneralLinearGroup.det,
      Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.det_fin_two_of]
  rw [hdet]
  exact IsSquare.one

theorem projectiveDetIsSquare_conj_iff
    (g h : PGL(2, R)) :
    ProjectiveDetIsSquare (g * h * g⁻¹) ↔ ProjectiveDetIsSquare h := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk G =>
      induction h using Matrix.ProjGenLinGroup.induction_on with
      | mk H =>
          simp only [← map_mul, ← map_inv]
          rw [projectiveDetIsSquare_mk_iff, projectiveDetIsSquare_mk_iff]
          simp

/-- A projective element of nonsquare determinant cannot be conjugate to an
upper-unipotent element.  Once the LPS generators are shown to have determinant
class `401`, this is exactly the BE20 quotient-condition argument. -/
theorem ne_conj_upperUnipotent_of_not_detSquare
    {s : PGL(2, R)}
    (hs : ¬ ProjectiveDetIsSquare s)
    (g : PGL(2, R)) (x : R) :
    s ≠ g * upperUnipotentPGL x * g⁻¹ := by
  intro heq
  apply hs
  rw [heq, projectiveDetIsSquare_conj_iff]
  exact projectiveDetIsSquare_upperUnipotent x

end DeterminantSquareClass

end QEC.Coding.BalancedProduct.LPSArithmetic
