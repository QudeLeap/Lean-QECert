import QEC.Coding.ExpanderCodes.LPSQuaternionRing

/-!
# Multiplicative projective reduction of LPS quaternions

The LPS generator map is the norm-`p` slice of a larger multiplicative
construction.  Integral quaternions whose reduced norm is a unit modulo a
residue prime form a submonoid, and reduction gives a monoid homomorphism
from that submonoid to `PGL(2, ZMod q)`.  This is the algebraic input needed
to interpret the norm shells as Hecke correspondences rather than as an
unstructured list of graph generators.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- Integral quaternions whose reduced norm remains invertible modulo `q`. -/
noncomputable def lpsQuaternionAwaySubmonoid
    (q : ℕ) [Fact q.Prime] : Submonoid LPSQuaternion where
  carrier := {t | IsUnit (t.norm : ZMod q)}
  one_mem' := by simp
  mul_mem' {t u} ht hu := by
    simpa using ht.mul hu

@[simp] theorem mem_lpsQuaternionAwaySubmonoid_iff
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    t ∈ lpsQuaternionAwaySubmonoid q ↔
      IsUnit (t.norm : ZMod q) :=
  Iff.rfl

/-- Matrix reduction, now regarded as an invertible matrix on the
norm-away-from-`q` submonoid. -/
noncomputable def lpsQuaternionAwayGL
    (q : ℕ) [Fact q.Prime] :
    lpsQuaternionAwaySubmonoid q →* GL (Fin 2) (ZMod q) where
  toFun t := Matrix.GeneralLinearGroup.mk''
    (lpsQuaternionMatrix q t.1) <| by
      rw [det_lpsQuaternionMatrix]
      exact t.2
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun (map_one (lpsQuaternionMatrixRingHom q)) i) j
  map_mul' t u := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun
      (congrFun (map_mul (lpsQuaternionMatrixRingHom q) t.1 u.1) i) j

@[simp] theorem coe_lpsQuaternionAwayGL
    (q : ℕ) [Fact q.Prime]
    (t : lpsQuaternionAwaySubmonoid q) :
    (lpsQuaternionAwayGL q t : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      lpsQuaternionMatrix q t.1 :=
  rfl

/-- Projectivization of multiplicative quaternion reduction. -/
noncomputable def lpsQuaternionAwayPGL
    (q : ℕ) [Fact q.Prime] :
    lpsQuaternionAwaySubmonoid q →* PGL(2, ZMod q) :=
  Matrix.ProjGenLinGroup.mk.comp (lpsQuaternionAwayGL q)

@[simp] theorem lpsQuaternionAwayPGL_apply
    (q : ℕ) [Fact q.Prime]
    (t : lpsQuaternionAwaySubmonoid q) :
    lpsQuaternionAwayPGL q t =
      Matrix.ProjGenLinGroup.mk (lpsQuaternionAwayGL q t) :=
  rfl

/-- A norm-`p` quaternion belongs to the norm-away submonoid at every LPS
residue prime. -/
noncomputable def lpsQuaternionAwayElement
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionAwaySubmonoid a.q :=
  ⟨t, by
    apply isUnit_iff_ne_zero.mpr
    rw [ht]
    simpa only [Int.cast_natCast] using a.degree_nonzero⟩

/-- The original norm-`p` general-linear reduction is exactly the
restriction of the multiplicative norm-away construction. -/
theorem lpsQuaternionGL_eq_away
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionGL a t ht =
      lpsQuaternionAwayGL a.q (lpsQuaternionAwayElement a t ht) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- The original projective LPS generator is the norm-`p` slice of the
multiplicative projective reduction homomorphism. -/
theorem lpsQuaternionPGL_eq_away
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t ht =
      lpsQuaternionAwayPGL a.q (lpsQuaternionAwayElement a t ht) := by
  rw [lpsQuaternionPGL, lpsQuaternionAwayPGL_apply,
    lpsQuaternionGL_eq_away]

/-- Projective quaternion reduction is the identity exactly when the three
imaginary coordinates vanish modulo the residue prime.  This is the local
algebraic core of the identity-coefficient count in the LPS trace formula. -/
theorem lpsQuaternionAwayPGL_eq_one_iff
    (a : LPSResiduePrime p)
    (t : lpsQuaternionAwaySubmonoid a.q) :
    lpsQuaternionAwayPGL a.q t = 1 ↔
      (a.q : ℤ) ∣ t.1.b ∧
        (a.q : ℤ) ∣ t.1.c ∧
          (a.q : ℤ) ∣ t.1.d := by
  rw [lpsQuaternionAwayPGL_apply,
    Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨lambda, hlambda⟩
    have hval := congrArg Units.val hlambda
    have h00 := congrFun (congrFun hval (0 : Fin 2)) (0 : Fin 2)
    have h01 := congrFun (congrFun hval (0 : Fin 2)) (1 : Fin 2)
    have h10 := congrFun (congrFun hval (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hval (1 : Fin 2)) (1 : Fin 2)
    simp [Matrix.GeneralLinearGroup.scalar, lpsQuaternionAwayGL,
      lpsQuaternionMatrix] at h00 h01 h10 h11
    have h2 : (2 : ZMod a.q) ≠ 0 := by
      intro hz
      change ((2 : ℕ) : ZMod a.q) = 0 at hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      have hqle : a.q ≤ 2 := Nat.le_of_dvd (by omega) hz
      have hp := a.degreePrime.pos
      have hlarge := a.large
      omega
    have hc : (t.1.c : ZMod a.q) = 0 := by
      have hzero : (2 : ZMod a.q) * (t.1.c : ZMod a.q) = 0 := by
        linear_combination h10 - h01
      exact (mul_eq_zero.mp hzero).resolve_left h2
    have hu : (t.1.b : ZMod a.q) * lpsResidueX a.q +
        (t.1.d : ZMod a.q) * lpsResidueY a.q = 0 := by
      have hzero : (2 : ZMod a.q) *
          ((t.1.b : ZMod a.q) * lpsResidueX a.q +
            (t.1.d : ZMod a.q) * lpsResidueY a.q) = 0 := by
        linear_combination -h00 + h11
      exact (mul_eq_zero.mp hzero).resolve_left h2
    have hv : -(t.1.b : ZMod a.q) * lpsResidueY a.q +
        (t.1.d : ZMod a.q) * lpsResidueX a.q = 0 := by
      have hzero : (2 : ZMod a.q) *
          (-(t.1.b : ZMod a.q) * lpsResidueY a.q +
            (t.1.d : ZMod a.q) * lpsResidueX a.q) = 0 := by
        linear_combination -h01 - h10
      exact (mul_eq_zero.mp hzero).resolve_left h2
    have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one a.q
    have hb : (t.1.b : ZMod a.q) = 0 := by
      linear_combination
        -lpsResidueX a.q * hu + lpsResidueY a.q * hv +
          (t.1.b : ZMod a.q) * hroot
    have hd : (t.1.d : ZMod a.q) = 0 := by
      linear_combination
        -lpsResidueY a.q * hu - lpsResidueX a.q * hv +
          (t.1.d : ZMod a.q) * hroot
    exact ⟨
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.b a.q).mp hb,
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.c a.q).mp hc,
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.d a.q).mp hd⟩
  · rintro ⟨hbDiv, hcDiv, hdDiv⟩
    have hb : (t.1.b : ZMod a.q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.b a.q).mpr hbDiv
    have hc : (t.1.c : ZMod a.q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.c a.q).mpr hcDiv
    have hd : (t.1.d : ZMod a.q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.d a.q).mpr hdDiv
    have haSq : (t.1.a : ZMod a.q) ^ 2 = (t.1.norm : ZMod a.q) := by
      simp [LPSQuaternion.norm, hb, hc, hd]
    have ha : (t.1.a : ZMod a.q) ≠ 0 := by
      intro haZero
      have hnormZero : (t.1.norm : ZMod a.q) = 0 := by
        rw [← haSq, haZero]
        simp
      exact (isUnit_iff_ne_zero.mp t.2) hnormZero
    refine ⟨Units.mk0 (t.1.a : ZMod a.q) ha, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change Matrix.scalar (Fin 2) (t.1.a : ZMod a.q) i j =
      lpsQuaternionMatrix a.q t.1 i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix, hb, hc, hd] <;>
      rfl

end QEC.Coding.TannerLiftedProduct
