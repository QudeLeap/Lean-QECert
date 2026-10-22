import QEC.Coding.ExpanderCodes.LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Prime right factors of integral LPS quaternions

This file turns divisibility by a degree prime into two-dimensional linear
algebra over `ZMod p`.  It is the existence engine for the recursive LPS
quaternion normal form.
-/

namespace QEC.Coding.TannerLiftedProduct

open Matrix
open scoped LinearAlgebra.Projectivization

variable {p : ℕ}

/-- The finite-field LPS matrix vanishes exactly when all four integral
quaternion coordinates are divisible by the residue characteristic. -/
theorem lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) (t : LPSQuaternion) :
    lpsQuaternionMatrix p t = 0 ↔ t.CoordinatesDvd (p : ℤ) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    change ((2 : ℕ) : ZMod p) = 0 at hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by omega) hz
    have hpge : 2 ≤ p := hp.two_le
    interval_cases p <;> norm_num at hp4
  constructor
  · intro hM
    have h00 := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
    have h01 := congrFun (congrFun hM (0 : Fin 2)) (1 : Fin 2)
    have h10 := congrFun (congrFun hM (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hM (1 : Fin 2)) (1 : Fin 2)
    simp [lpsQuaternionMatrix] at h00 h01 h10 h11
    have ha : (t.a : ZMod p) = 0 := by
      have hz : (2 : ZMod p) * (t.a : ZMod p) = 0 := by
        linear_combination h00 + h11
      exact (mul_eq_zero.mp hz).resolve_left h2
    have hc : (t.c : ZMod p) = 0 := by
      have hz : (2 : ZMod p) * (t.c : ZMod p) = 0 := by
        linear_combination h01 - h10
      exact (mul_eq_zero.mp hz).resolve_left h2
    have hu : (t.b : ZMod p) * lpsResidueX p +
        (t.d : ZMod p) * lpsResidueY p = 0 := by
      linear_combination h00 - ha
    have hv : -(t.b : ZMod p) * lpsResidueY p +
        (t.d : ZMod p) * lpsResidueX p = 0 := by
      linear_combination h01 - hc
    have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one p
    have hxy : lpsResidueX p ^ 2 + lpsResidueY p ^ 2 =
        (-1 : ZMod p) := by
      linear_combination hroot
    have hb : (t.b : ZMod p) = 0 := by
      have hs : (t.b : ZMod p) *
          (lpsResidueX p ^ 2 + lpsResidueY p ^ 2) = 0 := by
        linear_combination lpsResidueX p * hu - lpsResidueY p * hv
      rw [hxy] at hs
      simpa using hs
    have hd : (t.d : ZMod p) = 0 := by
      have hs : (t.d : ZMod p) *
          (lpsResidueX p ^ 2 + lpsResidueY p ^ 2) = 0 := by
        linear_combination lpsResidueY p * hu + lpsResidueX p * hv
      rw [hxy] at hs
      simpa using hs
    simpa [LPSQuaternion.CoordinatesDvd,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd] using ⟨ha, hb, hc, hd⟩
  · intro hdiv
    rcases hdiv with ⟨ha, hb, hc, hd⟩
    have ha0 : (t.a : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ha
    have hb0 : (t.b : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb
    have hc0 : (t.c : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc
    have hd0 : (t.d : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix, ha0, hb0, hc0, hd0]

/-- A nonzero singular two-by-two LPS matrix has a one-dimensional kernel. -/
theorem finrank_ker_lpsQuaternionMatrix_eq_one
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    Module.finrank (ZMod p)
      (LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t))) = 1 := by
  let f := Matrix.toLin' (lpsQuaternionMatrix p t)
  have hM : lpsQuaternionMatrix p t ≠ 0 := by
    simpa [lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd hp hp4 t]
  have hf : f ≠ 0 := by
    intro hf0
    apply hM
    exact Matrix.toLin'.injective (by simpa [f] using hf0)
  have hdetM : (lpsQuaternionMatrix p t).det = 0 := by
    rw [det_lpsQuaternionMatrix]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hnorm
  have hkerBot : LinearMap.ker f ≠ ⊥ := by
    rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']
    exact hdetM
  have hkerTop : LinearMap.ker f ≠ ⊤ := by
    intro htop
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.ker f := by rw [htop]; trivial
    simpa using hv
  have hlo : 1 ≤ Module.finrank (ZMod p) (LinearMap.ker f) :=
    Submodule.one_le_finrank_iff.mpr hkerBot
  have hhi : Module.finrank (ZMod p) (LinearMap.ker f) < 2 := by
    simpa [f] using Submodule.finrank_lt hkerTop
  change Module.finrank (ZMod p) (LinearMap.ker f) = 1
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo

/-- The kernel line of a primitive integral quaternion whose norm is
divisible by `p`. -/
noncomputable def lpsQuaternionKernelPoint
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    ℙ (ZMod p) (Fin 2 → ZMod p) :=
  Projectivization.mk''
    (LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t)))
    (finrank_ker_lpsQuaternionMatrix_eq_one hp hp4 t hnorm hprimitive)

@[simp] theorem lpsQuaternionKernelPoint_submodule
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    (lpsQuaternionKernelPoint hp hp4 t hnorm hprimitive).submodule =
      LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t)) := by
  apply Projectivization.submodule_mk''

/-- Two singular two-by-two matrices with the same kernel annihilate after
multiplying the first by the adjugate of the second. -/
theorem matrix_mul_adjugate_eq_zero_of_ker_eq
    {K : Type*} [Field K] (B C : Matrix (Fin 2) (Fin 2) K)
    (hdetC : C.det = 0)
    (hker : LinearMap.ker (Matrix.toLin' B) =
      LinearMap.ker (Matrix.toLin' C)) :
    B * C.adjugate = 0 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  apply LinearMap.ext
  intro v
  have hCprod : C * C.adjugate = 0 := by
    rw [Matrix.mul_adjugate, hdetC]
    simp
  have hvC : Matrix.toLin' C (Matrix.toLin' C.adjugate v) = 0 := by
    have hv := congrArg (fun M => Matrix.toLin' M v) hCprod
    simpa [Matrix.toLin'_mul_apply] using hv
  have hmemC : Matrix.toLin' C.adjugate v ∈
      LinearMap.ker (Matrix.toLin' C) := hvC
  have hmemB : Matrix.toLin' C.adjugate v ∈
      LinearMap.ker (Matrix.toLin' B) := by
    rw [hker]
    exact hmemC
  simpa [LinearMap.comp_apply] using hmemB

/-- A prime-norm integral quaternion cannot have every coordinate divisible
by that prime. -/
theorem not_coordinatesDvd_of_norm_eq_prime
    (hp : p.Prime) (t : LPSQuaternion) (hnorm : t.norm = p) :
    ¬t.CoordinatesDvd (p : ℤ) := by
  intro hdiv
  let u := lpsQuaternionDiv (p : ℤ) t
  have hscale : lpsScaleQuaternion (p : ℤ) u = t :=
    lpsScaleQuaternion_div_eq hdiv
  have hnormScale := congrArg LPSQuaternion.norm hscale
  rw [norm_lpsScaleQuaternion, hnorm] at hnormScale
  have huNonneg : 0 ≤ u.norm := by
    simp only [LPSQuaternion.norm]
    positivity
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpNe : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcancel : (p : ℤ) * ((p : ℤ) * u.norm) = (p : ℤ) * 1 := by
    simpa [pow_two, mul_assoc] using hnormScale
  have hunit : (p : ℤ) * u.norm = 1 := mul_left_cancel₀ hpNe hcancel
  have hdvdInt : (p : ℤ) ∣ (1 : ℤ) := ⟨u.norm, hunit.symm⟩
  have hdvdNat : p ∣ 1 := by exact_mod_cast hdvdInt
  exact hp.ne_one (Nat.dvd_one.mp hdvdNat)

/-- The usual LPS parity statement for a normalized prime shell, without
packaging an auxiliary residue prime. -/
theorem hasLPSParity_of_mem_lpsQuaternionShell_prime
    (hp4 : p % 4 = 1) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.HasLPSParity := by
  have hpPos : 0 < p := by
    by_contra h
    interval_cases p <;> norm_num at hp4
  have hnorm := norm_eq_of_mem_lpsQuaternionShell hpPos ht
  have hnormalized := (mem_lpsQuaternionShell_iff hpPos t).mp ht
  rcases exactly_one_odd_coordinate hp4 t hnorm with
      hfirst | hsecond | hthird | hfourth
  · exact ⟨hnormalized.2.2,
      Int.not_odd_iff_even.mp hfirst.2.1,
      Int.not_odd_iff_even.mp hfirst.2.2.1,
      Int.not_odd_iff_even.mp hfirst.2.2.2⟩
  · exact (hsecond.1 hnormalized.2.2).elim
  · exact (hthird.1 hnormalized.2.2).elim
  · exact (hfourth.1 hnormalized.2.2).elim

theorem LPSQuaternion.HasLPSParity.conj
    {t : LPSQuaternion} (ht : t.HasLPSParity) : t.conj.HasLPSParity := by
  rcases ht with ⟨ha, hb, hc, hd⟩
  change Odd t.a ∧ Even (-t.b) ∧ Even (-t.c) ∧ Even (-t.d)
  exact ⟨ha, hb.neg, hc.neg, hd.neg⟩

/-- Exact division by an odd scalar preserves the LPS parity class. -/
theorem hasLPSParity_lpsQuaternionDiv
    (hpOdd : Odd (p : ℤ)) {t : LPSQuaternion}
    (hdiv : t.CoordinatesDvd (p : ℤ)) (ht : t.HasLPSParity) :
    (lpsQuaternionDiv (p : ℤ) t).HasLPSParity := by
  let u := lpsQuaternionDiv (p : ℤ) t
  have hscale : lpsScaleQuaternion (p : ℤ) u = t :=
    lpsScaleQuaternion_div_eq hdiv
  have haEq := congrArg LPSQuaternion.a hscale
  have hbEq := congrArg LPSQuaternion.b hscale
  have hcEq := congrArg LPSQuaternion.c hscale
  have hdEq := congrArg LPSQuaternion.d hscale
  simp [lpsScaleQuaternion] at haEq hbEq hcEq hdEq
  rcases ht with ⟨ha, hb, hc, hd⟩
  constructor
  · exact (Int.odd_mul.mp (haEq ▸ ha)).2
  constructor
  · exact Int.not_odd_iff_even.mp fun huOdd =>
      (Int.not_odd_iff_even.mpr hb) (hbEq ▸ hpOdd.mul huOdd)
  constructor
  · exact Int.not_odd_iff_even.mp fun huOdd =>
      (Int.not_odd_iff_even.mpr hc) (hcEq ▸ hpOdd.mul huOdd)
  · exact Int.not_odd_iff_even.mp fun huOdd =>
      (Int.not_odd_iff_even.mpr hd) (hdEq ▸ hpOdd.mul huOdd)

@[simp] theorem LPSQuaternion.neg_a (t : LPSQuaternion) :
    (-t).a = -t.a := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).re = _
  rw [map_neg]
  rfl

@[simp] theorem LPSQuaternion.neg_b (t : LPSQuaternion) :
    (-t).b = -t.b := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).imI = _
  rw [map_neg]
  rfl

@[simp] theorem LPSQuaternion.neg_c (t : LPSQuaternion) :
    (-t).c = -t.c := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).imJ = _
  rw [map_neg]
  rfl

@[simp] theorem LPSQuaternion.neg_d (t : LPSQuaternion) :
    (-t).d = -t.d := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).imK = _
  rw [map_neg]
  rfl

/-- The only norm-one integral quaternions in the LPS parity class are the
two central units. -/
theorem eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity
    (t : LPSQuaternion) (hnorm : t.norm = 1)
    (hparity : t.HasLPSParity) : t = 1 ∨ t = -1 := by
  rcases hparity with ⟨_, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
  have hnorm' : t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = 1 := hnorm
  have hbSq : t.b ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.c, sq_nonneg t.d]
  have hcSq : t.c ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.d]
  have hdSq : t.d ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.c]
  have hb0 : t.b = 0 := by
    have hlo : -1 ≤ t.b := by nlinarith [sq_nonneg (t.b + 1)]
    have hhi : t.b ≤ 1 := by nlinarith [sq_nonneg (t.b - 1)]
    omega
  have hc0 : t.c = 0 := by
    have hlo : -1 ≤ t.c := by nlinarith [sq_nonneg (t.c + 1)]
    have hhi : t.c ≤ 1 := by nlinarith [sq_nonneg (t.c - 1)]
    omega
  have hd0 : t.d = 0 := by
    have hlo : -1 ≤ t.d := by nlinarith [sq_nonneg (t.d + 1)]
    have hhi : t.d ≤ 1 := by nlinarith [sq_nonneg (t.d - 1)]
    omega
  have ha : t.a = 1 ∨ t.a = -1 := by
    apply sq_eq_one_iff.mp
    nlinarith
  rcases ha with ha | ha
  · left
    apply LPSQuaternion.ext <;> simp [ha, hb0, hc0, hd0]
  · right
    apply LPSQuaternion.ext <;> simp [ha, hb0, hc0, hd0]

/-- A normalized norm-`p` LPS quaternion determines its kernel point on the
projective line over `ZMod p`. -/
noncomputable def lpsPrimeQuaternionKernelPoint
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    LPSGeneratorIndex p → ℙ (ZMod p) (Fin 2 → ZMod p) := fun beta =>
  lpsQuaternionKernelPoint hp hp4 beta.1
    (by
      have hnorm := norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2
      exact ⟨1, by simpa [hnorm]⟩)
    (not_coordinatesDvd_of_norm_eq_prime hp beta.1
      (norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2))

/-- Distinct normalized prime quaternions have distinct kernel lines. -/
theorem lpsPrimeQuaternionKernelPoint_injective
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    Function.Injective (lpsPrimeQuaternionKernelPoint hp hp4) := by
  intro beta gamma hpoint
  have hbetaNorm : beta.1.norm = (p : ℤ) :=
    norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2
  have hgammaNorm : gamma.1.norm = (p : ℤ) :=
    norm_eq_of_mem_lpsQuaternionShell hp.pos gamma.2
  have hbetaPrimitive : ¬beta.1.CoordinatesDvd (p : ℤ) :=
    not_coordinatesDvd_of_norm_eq_prime hp beta.1 hbetaNorm
  have hgammaPrimitive : ¬gamma.1.CoordinatesDvd (p : ℤ) :=
    not_coordinatesDvd_of_norm_eq_prime hp gamma.1 hgammaNorm
  have hpDvdBetaNorm : (p : ℤ) ∣ beta.1.norm :=
    ⟨1, by simpa [hbetaNorm]⟩
  have hpDvdGammaNorm : (p : ℤ) ∣ gamma.1.norm :=
    ⟨1, by simpa [hgammaNorm]⟩
  have hker :
      LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p beta.1)) =
        LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p gamma.1)) := by
    have hsub := congrArg Projectivization.submodule hpoint
    simpa [lpsPrimeQuaternionKernelPoint,
      lpsQuaternionKernelPoint_submodule hp hp4 beta.1
        hpDvdBetaNorm hbetaPrimitive,
      lpsQuaternionKernelPoint_submodule hp hp4 gamma.1
        hpDvdGammaNorm hgammaPrimitive] using hsub
  have hgammaDet : (lpsQuaternionMatrix p gamma.1).det = 0 := by
    rw [det_lpsQuaternionMatrix, hgammaNorm]
    simp
  have hmatrixProd :
      lpsQuaternionMatrix p beta.1 *
        (lpsQuaternionMatrix p gamma.1).adjugate = 0 :=
    matrix_mul_adjugate_eq_zero_of_ker_eq _ _ hgammaDet hker
  have hquatMatrix : lpsQuaternionMatrix p (beta.1 * gamma.1.conj) = 0 := by
    rw [lpsQuaternionMatrix_mul, lpsQuaternionMatrix_conj]
    exact hmatrixProd
  have hdiv : (beta.1 * gamma.1.conj).CoordinatesDvd (p : ℤ) :=
    (lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd hp hp4 _).mp hquatMatrix
  let u := lpsQuaternionDiv (p : ℤ) (beta.1 * gamma.1.conj)
  have hfactor : u * gamma.1 = beta.1 :=
    lpsQuaternionDiv_mul_conj_mul_eq hp hgammaNorm hdiv
  have huNorm : u.norm = 1 := by
    simpa [u] using norm_lpsQuaternionDiv_mul_conj
      (n := 0) hp (by simpa using hbetaNorm) hgammaNorm hdiv
  have hpOddNat : Odd p := by
    have hdecomp := Nat.mod_add_div p 4
    refine ⟨2 * (p / 4), ?_⟩
    omega
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  have hbetaParity :=
    hasLPSParity_of_mem_lpsQuaternionShell_prime hp4 beta.2
  have hgammaParity :=
    hasLPSParity_of_mem_lpsQuaternionShell_prime hp4 gamma.2
  have huParity : u.HasLPSParity := by
    apply hasLPSParity_lpsQuaternionDiv hpOdd hdiv
    exact hbetaParity.mul hgammaParity.conj
  rcases eq_one_or_neg_one_of_norm_eq_one_of_hasLPSParity u huNorm huParity with
      hu | hu
  · apply Subtype.ext
    simpa [hu] using hfactor.symm
  · have hbetaPos :=
      ((mem_lpsQuaternionShell_iff hp.pos beta.1).mp beta.2).2.1
    have hgammaPos :=
      ((mem_lpsQuaternionShell_iff hp.pos gamma.1).mp gamma.2).2.1
    have ha := congrArg LPSQuaternion.a hfactor
    rw [hu] at ha
    simp at ha
    omega

/-- The projective line over `ZMod p` has `p+1` points. -/
theorem natCard_lpsProjectiveLine [Fact p.Prime] :
    Nat.card (ℙ (ZMod p) (Fin 2 → ZMod p)) = p + 1 := by
  have hfinrank : Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 := by
    simp
  simpa [ZMod.card] using
    (Projectivization.card_of_finrank_two
      (ZMod p) (Fin 2 → ZMod p) hfinrank)

/-- Every projective kernel line comes from a unique normalized norm-`p`
LPS quaternion. -/
theorem lpsPrimeQuaternionKernelPoint_surjective
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    Function.Surjective (lpsPrimeQuaternionKernelPoint hp hp4) := by
  classical
  letI : Fintype (ℙ (ZMod p) (Fin 2 → ZMod p)) := Fintype.ofFinite _
  have hcard :
      Fintype.card (LPSGeneratorIndex p) =
        Fintype.card (ℙ (ZMod p) (Fin 2 → ZMod p)) := by
    calc
      Fintype.card (LPSGeneratorIndex p) =
          (lpsQuaternionShell p).card := card_lpsGeneratorIndex
      _ = p + 1 := card_lpsQuaternionShell_eq_prime_add_one hp hp4
      _ = Nat.card (ℙ (ZMod p) (Fin 2 → ZMod p)) :=
        natCard_lpsProjectiveLine.symm
      _ = Fintype.card (ℙ (ZMod p) (Fin 2 → ZMod p)) := by
        simp
  exact ((Fintype.bijective_iff_injective_and_card
    (lpsPrimeQuaternionKernelPoint hp hp4)).2
      ⟨lpsPrimeQuaternionKernelPoint_injective hp hp4, hcard⟩).2

/-- Every primitive integral quaternion whose norm is divisible by `p` has
a normalized norm-`p` right factor.  The quotient is integral because the
product with the conjugate factor vanishes modulo `p`. -/
theorem exists_lpsPrimeRightFactor_of_not_coordinatesDvd
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    ∃ beta : LPSGeneratorIndex p,
      (t * beta.1.conj).CoordinatesDvd (p : ℤ) := by
  let target := lpsQuaternionKernelPoint hp hp4 t hnorm hprimitive
  obtain ⟨beta, hbetaPoint⟩ :=
    lpsPrimeQuaternionKernelPoint_surjective hp hp4 target
  have hbetaNorm : beta.1.norm = (p : ℤ) :=
    norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2
  have hbetaPrimitive : ¬beta.1.CoordinatesDvd (p : ℤ) :=
    not_coordinatesDvd_of_norm_eq_prime hp beta.1 hbetaNorm
  have hpDvdBetaNorm : (p : ℤ) ∣ beta.1.norm :=
    ⟨1, by simpa [hbetaNorm]⟩
  have hker :
      LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t)) =
        LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p beta.1)) := by
    have hsub := congrArg Projectivization.submodule hbetaPoint
    simpa [target, lpsPrimeQuaternionKernelPoint,
      lpsQuaternionKernelPoint_submodule hp hp4 t hnorm hprimitive,
      lpsQuaternionKernelPoint_submodule hp hp4 beta.1
        hpDvdBetaNorm hbetaPrimitive] using hsub.symm
  have hbetaDet : (lpsQuaternionMatrix p beta.1).det = 0 := by
    rw [det_lpsQuaternionMatrix, hbetaNorm]
    simp
  have hmatrixProd :
      lpsQuaternionMatrix p t *
        (lpsQuaternionMatrix p beta.1).adjugate = 0 :=
    matrix_mul_adjugate_eq_zero_of_ker_eq _ _ hbetaDet hker
  refine ⟨beta,
    (lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd hp hp4 _).mp ?_⟩
  rw [lpsQuaternionMatrix_mul, lpsQuaternionMatrix_conj]
  exact hmatrixProd

end QEC.Coding.TannerLiftedProduct
