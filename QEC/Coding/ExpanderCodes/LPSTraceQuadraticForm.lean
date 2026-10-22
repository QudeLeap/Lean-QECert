import QEC.Coding.ExpanderCodes.LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The quadratic form in the LPS trace calculation

The LPS trace proof converts a congruence count for integral quaternions into
representations by

`Q_q(a,b,c,d) = a² + (2q)²b² + (2q)²c² + (2q)²d²`.

This file defines that form, its finite representation shell, and the exact
coordinate-scaling map back to the ordinary quaternion norm.  Thus the later
theta-series layer can speak about a concrete finite coefficient rather than
an informal representation number.
-/

namespace QEC.Coding.TannerLiftedProduct

/-- The positive integral quadratic form used in the LPS trace formula. -/
def lpsTraceQuadraticForm (q : ℕ) (t : LPSQuaternion) : ℤ :=
  t.a ^ 2 + ((2 * q : ℕ) : ℤ) ^ 2 * t.b ^ 2 +
    ((2 * q : ℕ) : ℤ) ^ 2 * t.c ^ 2 +
      ((2 * q : ℕ) : ℤ) ^ 2 * t.d ^ 2

/-- Scale the three imaginary coordinates by `2q`. -/
def lpsTraceQuaternion (q : ℕ) (t : LPSQuaternion) : LPSQuaternion where
  a := t.a
  b := (2 * q : ℕ) * t.b
  c := (2 * q : ℕ) * t.c
  d := (2 * q : ℕ) * t.d

@[simp] theorem lpsTraceQuaternion_a (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).a = t.a := rfl

@[simp] theorem lpsTraceQuaternion_b (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).b = (2 * q : ℕ) * t.b := rfl

@[simp] theorem lpsTraceQuaternion_c (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).c = (2 * q : ℕ) * t.c := rfl

@[simp] theorem lpsTraceQuaternion_d (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).d = (2 * q : ℕ) * t.d := rfl

/-- The trace quadratic form is literally the reduced norm after scaling
the imaginary quaternion coordinates. -/
@[simp] theorem norm_lpsTraceQuaternion (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).norm = lpsTraceQuadraticForm q t := by
  simp [LPSQuaternion.norm, lpsTraceQuadraticForm]
  ring

/-- Scaling is injective as soon as `q` is positive. -/
theorem lpsTraceQuaternion_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (lpsTraceQuaternion q) := by
  intro t u h
  have hab := congrArg LPSQuaternion.a h
  have hbb := congrArg LPSQuaternion.b h
  have hcb := congrArg LPSQuaternion.c h
  have hdb := congrArg LPSQuaternion.d h
  simp only [lpsTraceQuaternion_a] at hab
  simp only [lpsTraceQuaternion_b] at hbb
  simp only [lpsTraceQuaternion_c] at hcb
  simp only [lpsTraceQuaternion_d] at hdb
  apply LPSQuaternion.ext hab
  · exact mul_left_cancel₀ (by positivity : ((2 * q : ℕ) : ℤ) ≠ 0) hbb
  · exact mul_left_cancel₀ (by positivity : ((2 * q : ℕ) : ℤ) ≠ 0) hcb
  · exact mul_left_cancel₀ (by positivity : ((2 * q : ℕ) : ℤ) ≠ 0) hdb

/-- The image of the scaling map consists exactly of quaternions whose
three imaginary coordinates are divisible by `2q`. -/
theorem exists_lpsTraceQuaternion_eq_iff (q : ℕ) (u : LPSQuaternion) :
    (∃ t, lpsTraceQuaternion q t = u) ↔
      ((2 * q : ℕ) : ℤ) ∣ u.b ∧
        ((2 * q : ℕ) : ℤ) ∣ u.c ∧
          ((2 * q : ℕ) : ℤ) ∣ u.d := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
    refine ⟨⟨u.a, b, c, d⟩, ?_⟩
    apply LPSQuaternion.ext <;> simp [hb, hc, hd]

/-- The finite set of integral representations of `n` by the LPS trace
quadratic form. -/
noncomputable def lpsTraceQuadraticShell (q n : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionBox n).filter fun t => lpsTraceQuadraticForm q t = n

private theorem coordinate_bounds_of_traceQuadraticForm
    {q n : ℕ} (hq : 0 < q) (t : LPSQuaternion)
    (ht : lpsTraceQuadraticForm q t = n) :
    -(n : ℤ) ≤ t.a ∧ t.a ≤ n ∧
      -(n : ℤ) ≤ t.b ∧ t.b ≤ n ∧
      -(n : ℤ) ≤ t.c ∧ t.c ≤ n ∧
      -(n : ℤ) ≤ t.d ∧ t.d ≤ n := by
  let scale : ℤ := (2 * q : ℕ)
  have hscale : 1 ≤ scale ^ 2 := by
    have hscaleOne : (1 : ℤ) ≤ scale := by
      dsimp [scale]
      exact_mod_cast (show 1 ≤ 2 * q by omega)
    nlinarith [sq_nonneg (scale - 1)]
  have hform :
      t.a ^ 2 + scale ^ 2 * t.b ^ 2 + scale ^ 2 * t.c ^ 2 +
          scale ^ 2 * t.d ^ 2 = (n : ℤ) := by
    simpa [lpsTraceQuadraticForm, scale] using ht
  have ha : t.a ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.b, sq_nonneg t.c, sq_nonneg t.d]
  have hbScale : t.b ^ 2 ≤ scale ^ 2 * t.b ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hscale (sq_nonneg t.b)
  have hb : t.b ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.c, sq_nonneg t.d]
  have hcScale : t.c ^ 2 ≤ scale ^ 2 * t.c ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hscale (sq_nonneg t.c)
  have hc : t.c ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.d]
  have hdScale : t.d ^ 2 ≤ scale ^ 2 * t.d ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hscale (sq_nonneg t.d)
  have hd : t.d ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.c]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a + n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a - n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b + n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b - n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c + n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c - n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d + n)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d - n)]

/-- Membership in the finite shell is exactly representation by `Q_q`; the
bounding box adds no mathematical condition. -/
theorem mem_lpsTraceQuadraticShell_iff
    {q n : ℕ} (hq : 0 < q) (t : LPSQuaternion) :
    t ∈ lpsTraceQuadraticShell q n ↔
      lpsTraceQuadraticForm q t = n := by
  rw [lpsTraceQuadraticShell, Finset.mem_filter]
  exact and_iff_right_of_imp fun ht =>
    (mem_lpsQuaternionBox_iff n t).mpr
      (coordinate_bounds_of_traceQuadraticForm hq t ht)

/-- The finite norm shell satisfying the congruence condition used in the
LPS orbit count. -/
noncomputable def lpsTraceCongruenceShell (q n : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionFullShell n).filter fun u =>
    ((2 * q : ℕ) : ℤ) ∣ u.b ∧
      ((2 * q : ℕ) : ℤ) ∣ u.c ∧
        ((2 * q : ℕ) : ℤ) ∣ u.d

theorem mem_lpsTraceCongruenceShell_iff
    {q n : ℕ} (hn : 0 < n) (u : LPSQuaternion) :
    u ∈ lpsTraceCongruenceShell q n ↔
      u.norm = n ∧
        ((2 * q : ℕ) : ℤ) ∣ u.b ∧
          ((2 * q : ℕ) : ℤ) ∣ u.c ∧
            ((2 * q : ℕ) : ℤ) ∣ u.d := by
  rw [lpsTraceCongruenceShell, Finset.mem_filter,
    mem_lpsQuaternionFullShell_iff hn]

/-- Scaling the three imaginary coordinates is an exact finite equivalence
between representations by `Q_q` and the quaternion congruence shell. -/
noncomputable def lpsTraceQuadraticShellEquivCongruenceShell
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    {t // t ∈ lpsTraceQuadraticShell q n} ≃
      {u // u ∈ lpsTraceCongruenceShell q n} :=
  Equiv.ofBijective
    (fun t => ⟨lpsTraceQuaternion q t.1,
      (mem_lpsTraceCongruenceShell_iff hn _).mpr ⟨by
        rw [norm_lpsTraceQuaternion]
        exact (mem_lpsTraceQuadraticShell_iff hq t.1).mp t.2,
      by simp⟩⟩) <| by
    constructor
    · intro t u h
      apply Subtype.ext
      apply lpsTraceQuaternion_injective hq
      exact congrArg Subtype.val h
    · intro u
      have hu := (mem_lpsTraceCongruenceShell_iff hn u.1).mp u.2
      obtain ⟨t, ht⟩ :=
        (exists_lpsTraceQuaternion_eq_iff q u.1).mpr hu.2
      refine ⟨⟨t, (mem_lpsTraceQuadraticShell_iff hq t).mpr ?_⟩, ?_⟩
      · rw [← norm_lpsTraceQuaternion, ht]
        exact hu.1
      · apply Subtype.ext
        exact ht

/-- The representation number of `Q_q` is exactly the finite quaternion
congruence count appearing in the LPS trace calculation. -/
theorem card_lpsTraceQuadraticShell_eq_congruenceShell
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (lpsTraceQuadraticShell q n).card =
      (lpsTraceCongruenceShell q n).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    (lpsTraceQuadraticShellEquivCongruenceShell hq hn)

/-- The theta series of the LPS trace quadratic form, defined by its finite
representation numbers. -/
noncomputable def lpsTraceThetaSeries (q : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun n => (lpsTraceQuadraticShell q n).card

@[simp] theorem coeff_lpsTraceThetaSeries (q n : ℕ) :
    PowerSeries.coeff n (lpsTraceThetaSeries q) =
      (lpsTraceQuadraticShell q n).card := by
  simp [lpsTraceThetaSeries]

/-- Positive coefficients of the theta series are exactly the quaternion
congruence counts in the finite LPS trace formula. -/
theorem coeff_lpsTraceThetaSeries_eq_congruenceShell
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    PowerSeries.coeff n (lpsTraceThetaSeries q) =
      (lpsTraceCongruenceShell q n).card := by
  rw [coeff_lpsTraceThetaSeries,
    card_lpsTraceQuadraticShell_eq_congruenceShell hq hn]

end QEC.Coding.TannerLiftedProduct
