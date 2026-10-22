import QEC.Coding.ExpanderCodes.LPSQuaternion
import Mathlib.Data.Finset.Interval

/-!
# The finite normalized LPS quaternion shell

This file defines the actual finite shell whose elements label the
variable-prime LPS generators.  Membership is proved equivalent to the source
normalization: norm `p`, positive first coordinate, and odd first coordinate.
Quaternion conjugation preserves the shell and becomes inversion on the
resulting `PSL(2,q)` generator finset.

The remaining arithmetic enumeration theorem is intentionally visible: one
must still prove that this shell has cardinality `p+1` for prime
`p = 1 mod 4`.  No cardinality or spectral conclusion is stored as data.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- A product-coordinate equivalence used to enumerate integral quaternions
inside a finite box. -/
def lpsQuaternionEquivTuple :
    LPSQuaternion ≃ (((ℤ × ℤ) × ℤ) × ℤ) where
  toFun t := (((t.a, t.b), t.c), t.d)
  invFun x := ⟨x.1.1.1, x.1.1.2, x.1.2, x.2⟩
  left_inv t := by cases t; rfl
  right_inv x := by rcases x with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

/-- Integer coordinates large enough to contain every norm-`p` quaternion. -/
noncomputable def lpsQuaternionCoordinateRange (p : ℕ) : Finset ℤ :=
  Finset.Icc (-(p : ℤ)) (p : ℤ)

/-- The finite four-dimensional coordinate box `[-p,p]^4`. -/
noncomputable def lpsQuaternionBox (p : ℕ) : Finset LPSQuaternion :=
  let r := lpsQuaternionCoordinateRange p
  (((r.product r).product r).product r).map
    lpsQuaternionEquivTuple.symm.toEmbedding

theorem mem_lpsQuaternionBox_iff (p : ℕ) (t : LPSQuaternion) :
    t ∈ lpsQuaternionBox p ↔
      -(p : ℤ) ≤ t.a ∧ t.a ≤ p ∧
      -(p : ℤ) ≤ t.b ∧ t.b ≤ p ∧
      -(p : ℤ) ≤ t.c ∧ t.c ≤ p ∧
      -(p : ℤ) ≤ t.d ∧ t.d ≤ p := by
  simp [lpsQuaternionBox, lpsQuaternionCoordinateRange,
    lpsQuaternionEquivTuple, and_assoc]

/-- The source normalization for the `p+1` LPS quaternion representatives. -/
def LPSQuaternion.IsNormalizedAt (p : ℕ) (t : LPSQuaternion) : Prop :=
  t.norm = p ∧ 0 < t.a ∧ Odd t.a

noncomputable instance (p : ℕ) (t : LPSQuaternion) :
    Decidable (t.IsNormalizedAt p) :=
  Classical.propDecidable _

/-- The finite normalized shell used to label `S_{p,q}`. -/
noncomputable def lpsQuaternionShell (p : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionBox p).filter (LPSQuaternion.IsNormalizedAt p)

theorem coordinate_bounds_of_norm
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion)
    (ht : t.norm = p) :
    -(p : ℤ) ≤ t.a ∧ t.a ≤ p ∧
      -(p : ℤ) ≤ t.b ∧ t.b ≤ p ∧
      -(p : ℤ) ≤ t.c ∧ t.c ≤ p ∧
      -(p : ℤ) ≤ t.d ∧ t.d ≤ p := by
  have hnorm :
      t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = (p : ℤ) := ht
  have ha : t.a ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.b, sq_nonneg t.c, sq_nonneg t.d]
  have hb : t.b ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.c, sq_nonneg t.d]
  have hc : t.c ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.d]
  have hd : t.d ^ 2 ≤ (p : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.c]
  have hpz : (1 : ℤ) ≤ p := by exact_mod_cast hp
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a + p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a - p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b + p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b - p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c + p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c - p)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d + p)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d - p)]

theorem mem_lpsQuaternionShell_iff
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion) :
    t ∈ lpsQuaternionShell p ↔ t.IsNormalizedAt p := by
  rw [lpsQuaternionShell, Finset.mem_filter]
  exact and_iff_right_of_imp fun ht =>
    (mem_lpsQuaternionBox_iff p t).mpr
      (coordinate_bounds_of_norm hp t ht.1)

theorem norm_eq_of_mem_lpsQuaternionShell
    {p : ℕ} (hp : 0 < p) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.norm = p :=
  ((mem_lpsQuaternionShell_iff hp t).mp ht).1

theorem conj_mem_lpsQuaternionShell_iff
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion) :
    t.conj ∈ lpsQuaternionShell p ↔ t ∈ lpsQuaternionShell p := by
  rw [mem_lpsQuaternionShell_iff hp, mem_lpsQuaternionShell_iff hp]
  simp [LPSQuaternion.IsNormalizedAt]

private theorem int_eq_of_cast_eq_of_bounds
    {p q : ℕ} (hpq : 2 * p < q) {x y : ℤ}
    (hxlo : -(p : ℤ) ≤ x) (hxhi : x ≤ p)
    (hylo : -(p : ℤ) ≤ y) (hyhi : y ≤ p)
    (hcast : (x : ZMod q) = (y : ZMod q)) : x = y := by
  have hdiv : (q : ℤ) ∣ y - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).mp hcast
  have hpqz : (2 * p : ℤ) < q := by exact_mod_cast hpq
  have habs : |y - x| < (q : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
  omega

/-- Reduction modulo the residue prime is injective on the normalized shell
already at the matrix level.  The stored bound `q > 4p` is stronger than the
`q > 2p` needed to recover each integral coordinate. -/
theorem lpsQuaternion_eq_of_matrix_eq
    (a : LPSResiduePrime p) {t u : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p)
    (hu : u ∈ lpsQuaternionShell p)
    (hM : lpsQuaternionMatrix a.q t = lpsQuaternionMatrix a.q u) :
    t = u := by
  have h2 : (2 : ZMod a.q) ≠ 0 := by
    intro hz
    change ((2 : ℕ) : ZMod a.q) = 0 at hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have hqle : a.q ≤ 2 := Nat.le_of_dvd (by omega) hz
    have hp := a.degreePrime.pos
    have hlarge := a.large
    omega
  have h00 := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hM (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hM (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hM (1 : Fin 2)) (1 : Fin 2)
  simp [lpsQuaternionMatrix] at h00 h01 h10 h11
  have ha : (t.a : ZMod a.q) = (u.a : ZMod a.q) := by
    have hzero : (2 : ZMod a.q) *
        ((t.a : ZMod a.q) - (u.a : ZMod a.q)) = 0 := by
      linear_combination h00 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have hc : (t.c : ZMod a.q) = (u.c : ZMod a.q) := by
    have hzero : (2 : ZMod a.q) *
        ((t.c : ZMod a.q) - (u.c : ZMod a.q)) = 0 := by
      linear_combination h01 - h10
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have huEq :
      ((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueX a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueY a.q = 0 := by
    have hzero : (2 : ZMod a.q) *
        (((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueX a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueY a.q) = 0 := by
      linear_combination h00 - h11
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hvEq :
      -((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueY a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueX a.q = 0 := by
    have hzero : (2 : ZMod a.q) *
        (-((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueY a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueX a.q) = 0 := by
      linear_combination h01 + h10
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one a.q
  have hb : (t.b : ZMod a.q) = (u.b : ZMod a.q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsResidueX a.q * huEq + lpsResidueY a.q * hvEq +
        ((t.b : ZMod a.q) - (u.b : ZMod a.q)) * hroot
  have hd : (t.d : ZMod a.q) = (u.d : ZMod a.q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsResidueY a.q * huEq - lpsResidueX a.q * hvEq +
        ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * hroot
  have htBounds := (mem_lpsQuaternionBox_iff p t).mp
    ((Finset.mem_filter.mp ht).1)
  have huBounds := (mem_lpsQuaternionBox_iff p u).mp
    ((Finset.mem_filter.mp hu).1)
  have hpq : 2 * p < a.q := by
    have hp := a.degreePrime.pos
    have hlarge := a.large
    omega
  apply LPSQuaternion.ext
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.1 htBounds.2.1 huBounds.1 huBounds.2.1 ha
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.2.2.1 htBounds.2.2.2.1
      huBounds.2.2.1 huBounds.2.2.2.1 hb
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.2.2.2.2.1 htBounds.2.2.2.2.2.1
      huBounds.2.2.2.2.1 huBounds.2.2.2.2.2.1 hc
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.2.2.2.2.2.2.1 htBounds.2.2.2.2.2.2.2
      huBounds.2.2.2.2.2.2.1 huBounds.2.2.2.2.2.2.2 hd

private theorem shell_a_cast_ne_neg
    (a : LPSResiduePrime p) (t u : LPSQuaternion)
    (ht : t ∈ lpsQuaternionShell p)
    (hu : u ∈ lpsQuaternionShell p) :
    (t.a : ZMod a.q) ≠ -(u.a : ZMod a.q) := by
  intro ha
  have hsum : ((t.a + u.a : ℤ) : ZMod a.q) = 0 := by
    push_cast
    linear_combination ha
  have hdiv : (a.q : ℤ) ∣ t.a + u.a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (t.a + u.a) a.q).mp hsum
  have htNormalized := (mem_lpsQuaternionShell_iff
    a.degreePrime.pos t).mp ht
  have huNormalized := (mem_lpsQuaternionShell_iff
    a.degreePrime.pos u).mp hu
  have htBounds := (mem_lpsQuaternionBox_iff p t).mp
    ((Finset.mem_filter.mp ht).1)
  have huBounds := (mem_lpsQuaternionBox_iff p u).mp
    ((Finset.mem_filter.mp hu).1)
  have htPos : 0 < t.a := htNormalized.2.1
  have huPos : 0 < u.a := huNormalized.2.1
  have hnonneg : 0 ≤ t.a + u.a := by omega
  have hpq : (2 * p : ℤ) < a.q := by
    have hp := a.degreePrime.pos
    have hlarge := a.large
    exact_mod_cast (show 2 * p < a.q by omega)
  have hlt : t.a + u.a < (a.q : ℤ) :=
    calc
      t.a + u.a ≤ (p : ℤ) + p :=
        add_le_add htBounds.2.1 huBounds.2.1
      _ = (2 * p : ℤ) := by ring
      _ < (a.q : ℤ) := hpq
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hdiv
  omega

/-- Distinct normalized shell quaternions give distinct elements of
`PSL(2,q)`.  Equality in the projective quotient introduces a scalar; equal
determinants force that scalar to be `±1`, and positivity of the normalized
first coordinate excludes the negative case. -/
theorem lpsQuaternionPSL_injective (a : LPSResiduePrime p) :
    Function.Injective
      (fun t : {t // t ∈ lpsQuaternionShell p} =>
        lpsQuaternionPSL a t.1
          (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)) := by
  intro t u hPSL
  let htNorm := norm_eq_of_mem_lpsQuaternionShell
    a.degreePrime.pos t.2
  let huNorm := norm_eq_of_mem_lpsQuaternionShell
    a.degreePrime.pos u.2
  have hproj : lpsQuaternionPGL a t.1 htNorm =
      lpsQuaternionPGL a u.1 huNorm := by
    rw [← toPGL_lpsQuaternionPSL a t.1 htNorm,
      ← toPGL_lpsQuaternionPSL a u.1 huNorm]
    exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hPSL
  change Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t.1 htNorm) =
      Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a u.1 huNorm) at hproj
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod a.q)))
      (lpsQuaternionGL a t.1 htNorm) =
    QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod a.q)))
      (lpsQuaternionGL a u.1 huNorm) at hproj
  rw [QuotientGroup.mk'_eq_mk'] at hproj
  rcases hproj with ⟨z, hz, hmul⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rcases hz with ⟨lambda, rfl⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hmul
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at hdet
  have hdetEq :
      (lpsQuaternionGL a t.1 htNorm).det =
        (lpsQuaternionGL a u.1 huNorm).det := by
    apply Units.ext
    rw [lpsQuaternionGL_det a t.1 htNorm,
      lpsQuaternionGL_det a u.1 huNorm]
  have hlambdaSq : lambda ^ 2 = 1 := by
    apply mul_left_cancel
    calc
      (lpsQuaternionGL a t.1 htNorm).det * lambda ^ 2 =
          (lpsQuaternionGL a u.1 huNorm).det := hdet
      _ = (lpsQuaternionGL a t.1 htNorm).det := hdetEq.symm
      _ = (lpsQuaternionGL a t.1 htNorm).det * 1 := by simp
  have hlambdaValSq : (lambda : ZMod a.q) ^ 2 = 1 :=
    congrArg Units.val hlambdaSq
  rcases sq_eq_one_iff.mp hlambdaValSq with hlambdaVal | hlambdaVal
  · have hlambda : lambda = 1 := Units.ext hlambdaVal
    have hGL : lpsQuaternionGL a t.1 htNorm =
        lpsQuaternionGL a u.1 huNorm := by
      simpa [hlambda] using hmul
    apply Subtype.ext
    apply lpsQuaternion_eq_of_matrix_eq a t.2 u.2
    exact congrArg Units.val hGL
  · exfalso
    have hlambda : lambda = -1 := Units.ext hlambdaVal
    have hval := congrArg Units.val hmul
    have h00 := congrFun (congrFun hval (0 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hval (1 : Fin 2)) (1 : Fin 2)
    have h2 : (2 : ZMod a.q) ≠ 0 := by
      intro hz
      change ((2 : ℕ) : ZMod a.q) = 0 at hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      have hqle : a.q ≤ 2 := Nat.le_of_dvd (by omega) hz
      have hp := a.degreePrime.pos
      have hlarge := a.large
      omega
    have ha : (t.1.a : ZMod a.q) = -(u.1.a : ZMod a.q) := by
      simp [hlambda, lpsQuaternionGL, lpsQuaternionMatrix,
        Matrix.GeneralLinearGroup.scalar] at h00 h11
      apply eq_neg_iff_add_eq_zero.mpr
      have hzero : (2 : ZMod a.q) *
          ((t.1.a : ZMod a.q) + (u.1.a : ZMod a.q)) = 0 := by
        linear_combination -h00 - h11
      exact (mul_eq_zero.mp hzero).resolve_left h2
    exact shell_a_cast_ne_neg a t.1 u.1 t.2 u.2 ha

/-- The concrete finite `PSL(2,q)` generator set obtained from the normalized
quaternion shell. -/
noncomputable def lpsQuaternionGeneratorsPSL
    (a : LPSResiduePrime p) : Finset PSL(2, ZMod a.q) := by
  classical
  exact (lpsQuaternionShell p).attach.image fun t =>
    lpsQuaternionPSL a t.1
      (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)

theorem inv_mem_lpsQuaternionGeneratorsPSL_of_mem
    (a : LPSResiduePrime p) {g : PSL(2, ZMod a.q)}
    (hg : g ∈ lpsQuaternionGeneratorsPSL a) :
    g⁻¹ ∈ lpsQuaternionGeneratorsPSL a := by
  classical
  rw [lpsQuaternionGeneratorsPSL] at hg ⊢
  rcases Finset.mem_image.mp hg with ⟨t, ht, rfl⟩
  let tc : {u // u ∈ lpsQuaternionShell p} :=
    ⟨t.1.conj, (conj_mem_lpsQuaternionShell_iff
      a.degreePrime.pos t.1).mpr t.2⟩
  refine Finset.mem_image.mpr ⟨tc, Finset.mem_attach _ tc, ?_⟩
  simpa [tc] using lpsQuaternionPSL_conj_eq_inv a t.1
    (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)

/-- Projectivization loses no normalized generators.  The remaining exact
degree statement is therefore precisely the cardinality of the integral
quaternion shell. -/
theorem card_lpsQuaternionGeneratorsPSL
    (a : LPSResiduePrime p) :
    (lpsQuaternionGeneratorsPSL a).card =
      (lpsQuaternionShell p).card := by
  classical
  rw [lpsQuaternionGeneratorsPSL,
    Finset.card_image_of_injective _ (lpsQuaternionPSL_injective a),
    Finset.card_attach]

end QEC.Coding.TannerLiftedProduct
