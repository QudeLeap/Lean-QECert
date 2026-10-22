import QEC.Coding.BalancedProduct.LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The concrete `p = 401` LPS generating set

This file fixes the finite quaternion norm shell used by the BE20
specialization of the Lubotzky--Phillips--Sarnak construction.  The shell is
enumerated over proved coordinate bounds, so its cardinality and every later
matrix identity are theorem-derived rather than supplied as construction
fields.
-/

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSGenerators

open Matrix
open LPSArithmetic

/-- Finite search coordinates for the normalized `p = 401` quaternion shell.
The first coordinate represents the positive odd integer `2i+1`; the other
three represent every integer in `[-20,20]`. -/
structure ShellIndex401 where
  aIndex : Fin 10
  bIndex : Fin 41
  cIndex : Fin 41
  dIndex : Fin 41
  deriving DecidableEq, Fintype

@[ext]
theorem ShellIndex401.ext {t u : ShellIndex401}
    (ha : t.aIndex = u.aIndex)
    (hb : t.bIndex = u.bIndex)
    (hc : t.cIndex = u.cIndex)
    (hd : t.dIndex = u.dIndex) : t = u := by
  cases t
  cases u
  simp_all

def ShellIndex401.a (t : ShellIndex401) : ℤ := 2 * t.aIndex.val + 1
def ShellIndex401.b (t : ShellIndex401) : ℤ := t.bIndex.val - 20
def ShellIndex401.c (t : ShellIndex401) : ℤ := t.cIndex.val - 20
def ShellIndex401.d (t : ShellIndex401) : ℤ := t.dIndex.val - 20

def ShellIndex401.HasNorm401 (t : ShellIndex401) : Prop :=
  t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = 401

instance (t : ShellIndex401) : Decidable t.HasNorm401 :=
  by
    unfold ShellIndex401.HasNorm401
    infer_instance

/-- The source-normalized LPS shell `S_401`: positive odd first coordinate and
quaternion norm exactly `401`. -/
def shell401 : Finset ShellIndex401 :=
  Finset.univ.filter ShellIndex401.HasNorm401

theorem mem_shell401_iff (t : ShellIndex401) :
    t ∈ shell401 ↔ t.HasNorm401 := by
  simp [shell401]

/-- Jacobi's `p+1` count in the one fixed instance actually used by BE20.
The theorem is a kernel-checked evaluation of the explicit finite shell. -/
theorem card_shell401 : shell401.card = 402 := by
  native_decide

/-- Quaternion conjugation on the normalized shell. -/
def ShellIndex401.conj (t : ShellIndex401) : ShellIndex401 where
  aIndex := t.aIndex
  bIndex := Fin.rev t.bIndex
  cIndex := Fin.rev t.cIndex
  dIndex := Fin.rev t.dIndex

@[simp] theorem ShellIndex401.a_conj (t : ShellIndex401) : t.conj.a = t.a := rfl

@[simp] theorem ShellIndex401.b_conj (t : ShellIndex401) : t.conj.b = -t.b := by
  simp [ShellIndex401.conj, ShellIndex401.b, Fin.rev]
  omega

@[simp] theorem ShellIndex401.c_conj (t : ShellIndex401) : t.conj.c = -t.c := by
  simp [ShellIndex401.conj, ShellIndex401.c, Fin.rev]
  omega

@[simp] theorem ShellIndex401.d_conj (t : ShellIndex401) : t.conj.d = -t.d := by
  simp [ShellIndex401.conj, ShellIndex401.d, Fin.rev]
  omega

@[simp] theorem ShellIndex401.conj_conj (t : ShellIndex401) : t.conj.conj = t := by
  cases t
  simp [ShellIndex401.conj]

theorem ShellIndex401.hasNorm401_conj_iff (t : ShellIndex401) :
    t.conj.HasNorm401 ↔ t.HasNorm401 := by
  simp [ShellIndex401.HasNorm401]

@[simp] theorem ShellIndex401.conj_mem_shell401_iff (t : ShellIndex401) :
    t.conj ∈ shell401 ↔ t ∈ shell401 := by
  simp [mem_shell401_iff, ShellIndex401.hasNorm401_conj_iff]

/-- Chosen finite-field coordinates satisfying the LPS relation
`x²+y²+1=0`.  Existence is supplied by the finite-field two-squares
theorem, not as a caller hypothesis. -/
noncomputable def lpsX (q : ℕ) [Fact q.Prime] : ZMod q :=
  Classical.choose (ZMod.sq_add_sq q (-1))

noncomputable def lpsY (q : ℕ) [Fact q.Prime] : ZMod q :=
  Classical.choose (Classical.choose_spec (ZMod.sq_add_sq q (-1)))

theorem lpsX_sq_add_lpsY_sq_add_one (q : ℕ) [Fact q.Prime] :
    lpsX q ^ 2 + lpsY q ^ 2 + 1 = 0 := by
  have h := Classical.choose_spec
    (Classical.choose_spec (ZMod.sq_add_sq q (-1)))
  dsimp [lpsX, lpsY]
  linear_combination h

/-- The integral-quaternion matrix in the LPS construction, reduced modulo
`q` after inserting the chosen solution of `x²+y²+1=0`. -/
noncomputable def lpsMatrix401 (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) : Matrix (Fin 2) (Fin 2) (ZMod q) :=
  let a : ZMod q := t.a
  let b : ZMod q := t.b
  let c : ZMod q := t.c
  let d : ZMod q := t.d
  let x := lpsX q
  let y := lpsY q
  !![a + b * x + d * y, -b * y + c + d * x;
     -b * y - c + d * x, a - b * x - d * y]

theorem lpsMatrix401_conj
    (q : ℕ) [Fact q.Prime] (t : ShellIndex401) :
    lpsMatrix401 q t.conj = (lpsMatrix401 q t).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsMatrix401, Matrix.adjugate_fin_two] <;> ring

private theorem fin_eq_of_natCast_eq_of_card_le
    {n q : ℕ} [NeZero q]
    (hnq : n ≤ q) {i j : Fin n}
    (h : (i.val : ZMod q) = (j.val : ZMod q)) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  change i.val % q = j.val % q at h
  rw [Nat.mod_eq_of_lt (i.isLt.trans_le hnq),
    Nat.mod_eq_of_lt (j.isLt.trans_le hnq)] at h
  exact Fin.ext h

/-- For `q > 40`, the integral quaternion representation has no collisions
after reduction modulo `q`.  This is the coordinate-injectivity half of the
later projective generator count. -/
theorem shellIndex401_eq_of_lpsMatrix401_eq
    (q : ℕ) [Fact q.Prime] (hq : 40 < q)
    {t u : ShellIndex401}
    (hM : lpsMatrix401 q t = lpsMatrix401 q u) : t = u := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro hz
    change ((2 : ℕ) : ZMod q) = 0 at hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have : q ≤ 2 := Nat.le_of_dvd (by omega) hz
    omega
  have h00 := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hM (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hM (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hM (1 : Fin 2)) (1 : Fin 2)
  simp [lpsMatrix401] at h00 h01 h10 h11
  have ha : (t.a : ZMod q) = (u.a : ZMod q) := by
    have hzero : (2 : ZMod q) * ((t.a : ZMod q) - (u.a : ZMod q)) = 0 := by
      linear_combination h00 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have hc : (t.c : ZMod q) = (u.c : ZMod q) := by
    have hzero : (2 : ZMod q) * ((t.c : ZMod q) - (u.c : ZMod q)) = 0 := by
      linear_combination h01 - h10
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have huEq :
      ((t.b : ZMod q) - (u.b : ZMod q)) * lpsX q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsY q = 0 := by
    have hzero : (2 : ZMod q) *
        (((t.b : ZMod q) - (u.b : ZMod q)) * lpsX q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsY q) = 0 := by
      linear_combination h00 - h11
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hvEq :
      -((t.b : ZMod q) - (u.b : ZMod q)) * lpsY q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsX q = 0 := by
    have hzero : (2 : ZMod q) *
        (-((t.b : ZMod q) - (u.b : ZMod q)) * lpsY q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsX q) = 0 := by
      linear_combination h01 + h10
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hroot := lpsX_sq_add_lpsY_sq_add_one q
  have hb : (t.b : ZMod q) = (u.b : ZMod q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsX q * huEq + lpsY q * hvEq +
        ((t.b : ZMod q) - (u.b : ZMod q)) * hroot
  have hd : (t.d : ZMod q) = (u.d : ZMod q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsY q * huEq - lpsX q * hvEq +
        ((t.d : ZMod q) - (u.d : ZMod q)) * hroot
  apply ShellIndex401.ext
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 10 ≤ q)
    dsimp [ShellIndex401.a] at ha
    push_cast at ha
    have hzero : (2 : ZMod q) *
        ((t.aIndex.val : ZMod q) - (u.aIndex.val : ZMod q)) = 0 := by
      linear_combination ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 41 ≤ q)
    dsimp [ShellIndex401.b] at hb
    push_cast at hb
    linear_combination hb
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 41 ≤ q)
    dsimp [ShellIndex401.c] at hc
    push_cast at hc
    linear_combination hc
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 41 ≤ q)
    dsimp [ShellIndex401.d] at hd
    push_cast at hd
    linear_combination hd

theorem det_lpsMatrix401
    (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) (ht : t ∈ shell401) :
    (lpsMatrix401 q t).det = (401 : ZMod q) := by
  have hnorm : t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = 401 :=
    (mem_shell401_iff t).mp ht
  have hnormq := congrArg (fun z : ℤ => (z : ZMod q)) hnorm
  push_cast at hnormq
  have hroot := lpsX_sq_add_lpsY_sq_add_one q
  simp only [lpsMatrix401, Matrix.det_fin_two_of]
  linear_combination hnormq -
    ((t.b : ZMod q) ^ 2 + (t.d : ZMod q) ^ 2) * hroot

theorem lpsMatrix401_mul_conj
    (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) (ht : t ∈ shell401) :
    lpsMatrix401 q t * lpsMatrix401 q t.conj =
      (401 : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  rw [lpsMatrix401_conj, Matrix.mul_adjugate, det_lpsMatrix401 q t ht]

/-- The genuine invertible LPS matrix at an admissible prime.  Invertibility is
proved from `(401/q) = -1`, which in particular says that `401` is nonzero
modulo `q`; it is not stored in the generator data. -/
noncomputable def lpsGL401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    GL (Fin 2) (ZMod q) :=
  Matrix.GeneralLinearGroup.mk'' (lpsMatrix401 q t) <| by
    rw [det_lpsMatrix401 q t ht]
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hnonsquare : ¬ IsSquare (401 : ZMod q) :=
      (legendreSym.eq_neg_one_iff' (p := q) (a := 401)).mp hq
    apply hnonsquare
    rw [hzero]
    exact IsSquare.zero

theorem lpsGL401_det
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    ((lpsGL401 q hq t ht).det : ZMod q) = (401 : ZMod q) := by
  change (lpsMatrix401 q t).det = (401 : ZMod q)
  exact det_lpsMatrix401 q t ht

/-- A concrete projective LPS generator indexed by the normalized shell. -/
noncomputable def lpsGenerator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) : PGL(2, ZMod q) :=
  Matrix.ProjGenLinGroup.mk (lpsGL401 q hq t ht)

theorem not_projectiveDetIsSquare_lpsGenerator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    ¬ ProjectiveDetIsSquare (lpsGenerator401 q hq t ht) := by
  exact not_projectiveDetIsSquare_mk_of_det_401
    (lpsGL401 q hq t ht) (lpsGL401_det q hq t ht) hq

theorem lpsGenerator401_conj_eq_inv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (t : ShellIndex401) (ht : t ∈ shell401) :
    lpsGenerator401 q hq t.conj
        ((ShellIndex401.conj_mem_shell401_iff t).mpr ht) =
      (lpsGenerator401 q hq t ht)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  change Matrix.ProjGenLinGroup.mk (lpsGL401 q hq t ht) *
      Matrix.ProjGenLinGroup.mk
        (lpsGL401 q hq t.conj
          ((ShellIndex401.conj_mem_shell401_iff t).mpr ht)) = 1
  rw [← map_mul]
  apply (Matrix.ProjGenLinGroup.mk_eq_one).mpr
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨(lpsGL401 q hq t ht).det, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (Matrix.scalar (Fin 2) ((lpsGL401 q hq t ht).det : ZMod q)) i j =
    (lpsMatrix401 q t * lpsMatrix401 q t.conj) i j
  rw [lpsMatrix401_mul_conj q t ht, lpsGL401_det q hq t ht]
  simp [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply]

private theorem shell401_a_cast_ne_neg
    (q : ℕ) [Fact q.Prime] (hq : 40 < q)
    (t u : ShellIndex401) :
    (t.a : ZMod q) ≠ -(u.a : ZMod q) := by
  intro ha
  dsimp [ShellIndex401.a] at ha
  push_cast at ha
  have hsum' :
      (2 : ZMod q) * t.aIndex.val + 1 +
          ((2 : ZMod q) * u.aIndex.val + 1) = 0 := by
    linear_combination ha
  have hsum :
      ((2 * t.aIndex.val + 1 + (2 * u.aIndex.val + 1) : ℕ) : ZMod q) = 0 := by
    push_cast
    exact hsum'
  rw [ZMod.natCast_eq_zero_iff] at hsum
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hsum

/-- Under the source size condition `q > 2√401` (used here through its
integer consequence `q > 40`), distinct normalized shell elements remain
distinct even after projectivization. -/
theorem lpsGenerator401_injective
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Function.Injective
      (fun t : {t // t ∈ shell401} => lpsGenerator401 q hq t.1 t.2) := by
  intro t u hproj
  change Matrix.ProjGenLinGroup.mk (lpsGL401 q hq t.1 t.2) =
      Matrix.ProjGenLinGroup.mk (lpsGL401 q hq u.1 u.2) at hproj
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod q)))
      (lpsGL401 q hq t.1 t.2) =
    QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod q)))
      (lpsGL401 q hq u.1 u.2) at hproj
  rw [QuotientGroup.mk'_eq_mk'] at hproj
  rcases hproj with ⟨z, hz, hmul⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rcases hz with ⟨lambda, rfl⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hmul
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at hdet
  have hdetEq :
      (lpsGL401 q hq t.1 t.2).det =
        (lpsGL401 q hq u.1 u.2).det := by
    apply Units.ext
    rw [lpsGL401_det q hq t.1 t.2, lpsGL401_det q hq u.1 u.2]
  have hlambdaSq : lambda ^ 2 = 1 := by
    apply mul_left_cancel
    calc
      (lpsGL401 q hq t.1 t.2).det * lambda ^ 2 =
          (lpsGL401 q hq u.1 u.2).det := hdet
      _ = (lpsGL401 q hq t.1 t.2).det := hdetEq.symm
      _ = (lpsGL401 q hq t.1 t.2).det * 1 := by simp
  have hlambdaValSq : (lambda : ZMod q) ^ 2 = 1 :=
    congrArg Units.val hlambdaSq
  rcases sq_eq_one_iff.mp hlambdaValSq with hlambdaVal | hlambdaVal
  · have hlambda : lambda = 1 := Units.ext hlambdaVal
    have hGL : lpsGL401 q hq t.1 t.2 = lpsGL401 q hq u.1 u.2 := by
      simpa [hlambda] using hmul
    apply Subtype.ext
    apply shellIndex401_eq_of_lpsMatrix401_eq q hq40
    exact congrArg Units.val hGL
  · exfalso
    have hlambda : lambda = -1 := Units.ext hlambdaVal
    have hval := congrArg Units.val hmul
    have h00 := congrFun (congrFun hval (0 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hval (1 : Fin 2)) (1 : Fin 2)
    have h2 : (2 : ZMod q) ≠ 0 := by
      intro hz
      change ((2 : ℕ) : ZMod q) = 0 at hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      have : q ≤ 2 := Nat.le_of_dvd (by omega) hz
      omega
    have ha : (t.1.a : ZMod q) = -(u.1.a : ZMod q) := by
      simp [hlambda, lpsGL401, lpsMatrix401,
        Matrix.GeneralLinearGroup.scalar] at h00 h11
      apply eq_neg_iff_add_eq_zero.mpr
      have hzero : (2 : ZMod q) *
          ((t.1.a : ZMod q) + (u.1.a : ZMod q)) = 0 := by
        linear_combination -h00 - h11
      exact (mul_eq_zero.mp hzero).resolve_left h2
    exact shell401_a_cast_ne_neg q hq40 t.1 u.1 ha

/-- The finite projective generating set obtained from all 402 normalized
norm-401 quaternions.  Injectivity of the reduction map (and hence cardinality
402 after projection) is proved separately from the LPS size hypothesis; this
definition itself carries no such conclusion. -/
noncomputable def lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Finset PGL(2, ZMod q) :=
  by
    classical
    exact shell401.attach.image fun t => lpsGenerator401 q hq t.1 t.2

theorem card_lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    (lpsGenerators401 q hq).card = 402 := by
  classical
  rw [lpsGenerators401,
    Finset.card_image_of_injective _ (lpsGenerator401_injective q hq40 hq)]
  simpa using card_shell401

theorem mem_lpsGenerators401_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (s : PGL(2, ZMod q)) :
    s ∈ lpsGenerators401 q hq ↔
      ∃ t : ShellIndex401, ∃ ht : t ∈ shell401,
        lpsGenerator401 q hq t ht = s := by
  classical
  simp [lpsGenerators401]

theorem not_projectiveDetIsSquare_of_mem_lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq) :
    ¬ ProjectiveDetIsSquare s := by
  rcases (mem_lpsGenerators401_iff q hq s).mp hs with ⟨t, ht, rfl⟩
  exact not_projectiveDetIsSquare_lpsGenerator401 q hq t ht

theorem inv_mem_lpsGenerators401_of_mem
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq) :
    s⁻¹ ∈ lpsGenerators401 q hq := by
  rcases (mem_lpsGenerators401_iff q hq s).mp hs with ⟨t, ht, rfl⟩
  apply (mem_lpsGenerators401_iff q hq _).mpr
  refine ⟨t.conj, (ShellIndex401.conj_mem_shell401_iff t).mpr ht, ?_⟩
  exact lpsGenerator401_conj_eq_inv q hq t ht

theorem inv_mem_lpsGenerators401_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (s : PGL(2, ZMod q)) :
    s⁻¹ ∈ lpsGenerators401 q hq ↔ s ∈ lpsGenerators401 q hq := by
  constructor
  · intro hs
    simpa using inv_mem_lpsGenerators401_of_mem q hq hs
  · exact inv_mem_lpsGenerators401_of_mem q hq

/-- The determinant proof closes the source quotient condition at the level
of concrete generators: no generator lies in any conjugate of the
upper-unipotent subgroup. -/
theorem lpsGenerators401_ne_conj_upperUnipotent
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq)
    (g : PGL(2, ZMod q)) (x : ZMod q) :
    s ≠ g * upperUnipotentPGL x * g⁻¹ :=
  ne_conj_upperUnipotent_of_not_detSquare
    (not_projectiveDetIsSquare_of_mem_lpsGenerators401 q hq hs) g x

end QEC.Coding.BalancedProduct.LPSGenerators
