import QEC.Coding.ExpanderCodes.LPSResiduePrime
import QEC.Coding.ExpanderCodes.LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic

/-!
# Variable-prime LPS quaternion matrices

This file formalizes the algebraic part of the `PSL(2,q)` generator
construction uniformly in the degree prime `p`.  An integral quaternion of
norm `p` gives a matrix of determinant `p`; at a residue prime from
`LPSResiduePrime p`, that projective matrix lies in the image of `PSL(2,q)`.

The finite normalized quaternion shell and Jacobi's `p+1` representation
count are deliberately not assumed here.  They are the remaining enumeration
layer, separate from the matrix and projective-group algebra proved below.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic

variable {p : ℕ}

/-- Integral quaternion coordinates used by the LPS construction. -/
structure LPSQuaternion where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

@[ext] theorem LPSQuaternion.ext {t u : LPSQuaternion}
    (ha : t.a = u.a) (hb : t.b = u.b)
    (hc : t.c = u.c) (hd : t.d = u.d) : t = u := by
  cases t
  cases u
  simp_all

/-- The integral reduced norm `a²+b²+c²+d²`. -/
def LPSQuaternion.norm (t : LPSQuaternion) : ℤ :=
  t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2

/-- Quaternion conjugation. -/
def LPSQuaternion.conj (t : LPSQuaternion) : LPSQuaternion where
  a := t.a
  b := -t.b
  c := -t.c
  d := -t.d

@[simp] theorem LPSQuaternion.conj_a (t : LPSQuaternion) :
    t.conj.a = t.a := rfl

@[simp] theorem LPSQuaternion.conj_b (t : LPSQuaternion) :
    t.conj.b = -t.b := rfl

@[simp] theorem LPSQuaternion.conj_c (t : LPSQuaternion) :
    t.conj.c = -t.c := rfl

@[simp] theorem LPSQuaternion.conj_d (t : LPSQuaternion) :
    t.conj.d = -t.d := rfl

@[simp] theorem LPSQuaternion.conj_conj (t : LPSQuaternion) :
    t.conj.conj = t := by
  cases t
  simp [LPSQuaternion.conj]

@[simp] theorem LPSQuaternion.norm_conj (t : LPSQuaternion) :
    t.conj.norm = t.norm := by
  simp [LPSQuaternion.norm]

/-- Computed finite-field coordinates satisfying `x²+y²+1=0`. -/
def lpsResidueX (q : ℕ) [Fact q.Prime] : ZMod q :=
  lpsEffectiveResidueX q

def lpsResidueY (q : ℕ) [Fact q.Prime] : ZMod q :=
  lpsEffectiveResidueY q

theorem lpsResidueX_sq_add_lpsResidueY_sq_add_one
    (q : ℕ) [Fact q.Prime] :
    lpsResidueX q ^ 2 + lpsResidueY q ^ 2 + 1 = 0 :=
  lpsEffectiveResidueX_sq_add_lpsEffectiveResidueY_sq_add_one q

/-- The LPS matrix attached to an integral quaternion, reduced modulo `q`. -/
def lpsQuaternionMatrix
    (q : ℕ) [Fact q.Prime]
    (t : LPSQuaternion) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  let a : ZMod q := t.a
  let b : ZMod q := t.b
  let c : ZMod q := t.c
  let d : ZMod q := t.d
  let x := lpsResidueX q
  let y := lpsResidueY q
  !![a + b * x + d * y, -b * y + c + d * x;
     -b * y - c + d * x, a - b * x - d * y]

theorem lpsQuaternionMatrix_conj
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    lpsQuaternionMatrix q t.conj = (lpsQuaternionMatrix q t).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsQuaternionMatrix, Matrix.adjugate_fin_two] <;> ring

/-- The exact determinant identity, before specializing the norm to `p`. -/
theorem det_lpsQuaternionMatrix
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    (lpsQuaternionMatrix q t).det = (t.norm : ZMod q) := by
  have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one q
  simp only [lpsQuaternionMatrix, LPSQuaternion.norm,
    Matrix.det_fin_two_of]
  push_cast
  linear_combination
    -((t.b : ZMod q) ^ 2 + (t.d : ZMod q) ^ 2) * hroot

theorem lpsQuaternionMatrix_mul_conj
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    lpsQuaternionMatrix q t * lpsQuaternionMatrix q t.conj =
      (t.norm : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  rw [lpsQuaternionMatrix_conj, Matrix.mul_adjugate,
    det_lpsQuaternionMatrix]

/-- The invertible LPS matrix attached to a norm-`p` quaternion at a residue
prime `q`.  Invertibility follows from `q ∤ p`, already proved by the
arithmetic schedule. -/
noncomputable def lpsQuaternionGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    GL (Fin 2) (ZMod a.q) :=
  Matrix.GeneralLinearGroup.mk'' (lpsQuaternionMatrix a.q t) <| by
    rw [det_lpsQuaternionMatrix, ht]
    apply isUnit_iff_ne_zero.mpr
    simpa using a.degree_nonzero

theorem lpsQuaternionGL_det
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    ((lpsQuaternionGL a t ht).det : ZMod a.q) = (p : ZMod a.q) := by
  change (lpsQuaternionMatrix a.q t).det = (p : ZMod a.q)
  rw [det_lpsQuaternionMatrix, ht]
  norm_cast

/-- The projective generator before choosing its unique `PSL` preimage. -/
noncomputable def lpsQuaternionPGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : PGL(2, ZMod a.q) :=
  Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t ht)

theorem projectiveDetIsSquare_lpsQuaternionPGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    ProjectiveDetIsSquare (lpsQuaternionPGL a t ht) := by
  exact projectiveDetIsSquare_mk_of_det
    (lpsQuaternionGL a t ht) (lpsQuaternionGL_det a t ht)
      a.degree_nonzero a.residue

theorem lpsQuaternionPGL_mem_range_toPGL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t ht ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod a.q)).range := by
  exact (projectiveDetIsSquare_iff_mem_range_toPGL _).mp
    (projectiveDetIsSquare_lpsQuaternionPGL a t ht)

/-- The actual `PSL(2,q)` generator selected from the proved image witness. -/
noncomputable def lpsQuaternionPSL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : PSL(2, ZMod a.q) :=
  Classical.choose (lpsQuaternionPGL_mem_range_toPGL a t ht)

theorem toPGL_lpsQuaternionPSL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsQuaternionPSL a t ht) = lpsQuaternionPGL a t ht :=
  Classical.choose_spec (lpsQuaternionPGL_mem_range_toPGL a t ht)

theorem lpsQuaternionPGL_conj_eq_inv
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t.conj (by simpa using ht) =
      (lpsQuaternionPGL a t ht)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  change Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t ht) *
      Matrix.ProjGenLinGroup.mk
        (lpsQuaternionGL a t.conj (by simpa using ht)) = 1
  rw [← map_mul]
  apply (Matrix.ProjGenLinGroup.mk_eq_one).mpr
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨(lpsQuaternionGL a t ht).det, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hnorm : (t.norm : ZMod a.q) = (p : ZMod a.q) := by
    rw [ht]
    norm_cast
  have hmatrix :
      Matrix.scalar (Fin 2) ((lpsQuaternionGL a t ht).det : ZMod a.q) =
        lpsQuaternionMatrix a.q t * lpsQuaternionMatrix a.q t.conj := by
    rw [lpsQuaternionGL_det a t ht]
    calc
      Matrix.scalar (Fin 2) (p : ZMod a.q) =
          (p : ZMod a.q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod a.q)) := by
        change Matrix.diagonal (fun _ : Fin 2 => (p : ZMod a.q)) =
          (p : ZMod a.q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod a.q))
        exact (Matrix.smul_one_eq_diagonal (p : ZMod a.q)).symm
      _ = (t.norm : ZMod a.q) •
          (1 : Matrix (Fin 2) (Fin 2) (ZMod a.q)) := by rw [hnorm]
      _ = lpsQuaternionMatrix a.q t *
          lpsQuaternionMatrix a.q t.conj :=
        (lpsQuaternionMatrix_mul_conj a.q t).symm
  exact congrFun (congrFun hmatrix i) j

/-- Quaternion conjugation gives inversion already in `PSL`, not merely
after embedding into `PGL`. -/
theorem lpsQuaternionPSL_conj_eq_inv
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPSL a t.conj (by simpa using ht) =
      (lpsQuaternionPSL a t ht)⁻¹ := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [map_inv, toPGL_lpsQuaternionPSL, toPGL_lpsQuaternionPSL]
  exact lpsQuaternionPGL_conj_eq_inv a t ht

end QEC.Coding.TannerLiftedProduct
