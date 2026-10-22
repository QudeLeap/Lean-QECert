import QEC.Coding.ExpanderCodes.LPSOriginalDilatedModularFunction
import QEC.Coding.ExpanderCodes.LPSModularDilation


/-!
# Original level descent and exact cusp coordinate arithmetic

Genuine original Gamma0 subgroup inclusion descends the actual interior and
cusp orbit relations, yielding a surjective map on the same filled sets and
commutation with original j. The map is not here claimed continuous or analytic.
The already proved positive integral minimum widths and true period groups
supply their level divisors and integral ratio. Exact exponential algebra gives
the literal q-coordinate power formula, with no supplied width or descent law.

This internal closure supports the original LPS/Hecke route behind pinned PK22
main.tex ex:Xpq:484–486 and th:qLDPC:231–238. Arithmetic normalization transport,
whole-fibre smoothness, uniform good reduction, Hecke/Frobenius/Weil, the LPS
spectrum and the exact arbitrary-field quantum family remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

/-- Positive integral real-period factors give genuine natural divisibility. -/
lemma lpsOriginalCuspWidth_dvd_of_positive_zmultiple (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (z : ℤ) (hz : z • (a : ℝ) = (b : ℝ)) : a ∣ b := by
  have haz : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbz : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rw [zsmul_eq_mul] at hz
    nlinarith
  have hzint : 0 < z := by exact_mod_cast hzpos
  have he : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hzint)
  refine ⟨z.toNat, ?_⟩
  have hreal : (b : ℝ) = (a : ℝ) * (z.toNat : ℝ) := by
    rw [he, zsmul_eq_mul] at *
    nlinarith
  exact_mod_cast hreal

/-- Actual inclusion of the conjugated cusp groups follows from original level divisibility. -/
lemma lpsOriginalCuspGroup_level_le (N M : ℕ) (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspGroup M ρ ≤ lpsOriginalCuspGroup N ρ := by
  intro g hg
  rw [lpsOriginalCuspGroup, ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul] at hg ⊢
  exact (Subgroup.map_mono (lpsGamma0_level_le N M hNM)) hg

/-- The actual minimal original cusp width divides the original level. -/
lemma lpsOriginalCuspWidthNat_dvd_level (N : ℕ) [NeZero N] (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ ∣ N := by
  have hp := lpsOriginalCuspGroup_integerPeriod N ρ
  rw [lpsOriginalCuspGroup_periods_generated] at hp
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hp
  rw [lpsOriginalCuspWidthNat_cast] at hz
  exact lpsOriginalCuspWidth_dvd_of_positive_zmultiple _ _
    (lpsOriginalCuspWidthNat_positive N ρ) (Nat.pos_of_ne_zero (NeZero.ne N)) z hz

/-- The actual minimum at the smaller level divides the actual higher-level minimum. -/
lemma lpsOriginalCuspWidthNat_dvd_of_level_dvd (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat M ρ := by
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup M ρ)
  have hg := Subgroup.mem_strictPeriods_iff.mp hp
  have hn := Subgroup.mem_strictPeriods_iff.mpr (lpsOriginalCuspGroup_level_le N M hNM ρ hg)
  rw [lpsOriginalCuspGroup_periods_generated] at hn
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
  rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast] at hz
  exact lpsOriginalCuspWidth_dvd_of_positive_zmultiple _ _
    (lpsOriginalCuspWidthNat_positive N ρ) (lpsOriginalCuspWidthNat_positive M ρ) z hz

/-- The ratio of the two actual positive original natural cusp widths. -/
def lpsOriginalCuspLevelDegree (N M : ℕ) [NeZero N] [NeZero M] (ρ : SL(2, ℤ)) : ℕ :=
  lpsOriginalCuspWidthNat M ρ / lpsOriginalCuspWidthNat N ρ

/-- The actual cusp-width ratio recovers the higher-level width exactly. -/
lemma lpsOriginalCuspLevelDegree_mul_width (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ * lpsOriginalCuspLevelDegree N M ρ =
      lpsOriginalCuspWidthNat M ρ :=
  Nat.mul_div_cancel' (lpsOriginalCuspWidthNat_dvd_of_level_dvd N M hNM ρ)

/-- The actual level ratio is positive, without a supplied ramification bound. -/
lemma lpsOriginalCuspLevelDegree_positive (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) : 0 < lpsOriginalCuspLevelDegree N M ρ := by
  apply Nat.pos_of_ne_zero
  intro h
  have hm := lpsOriginalCuspLevelDegree_mul_width N M hNM ρ
  rw [h, mul_zero] at hm
  exact (Nat.ne_of_gt (lpsOriginalCuspWidthNat_positive M ρ)) hm.symm

/-- The genuine cusp-level ratio divides the higher original level. -/
lemma lpsOriginalCuspLevelDegree_dvd_level (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) : lpsOriginalCuspLevelDegree N M ρ ∣ M := by
  have h : lpsOriginalCuspLevelDegree N M ρ ∣ lpsOriginalCuspWidthNat M ρ := by
    refine ⟨lpsOriginalCuspWidthNat N ρ, ?_⟩
    rw [mul_comm]
    exact (lpsOriginalCuspLevelDegree_mul_width N M hNM ρ).symm
  exact h.trans (lpsOriginalCuspWidthNat_dvd_level M ρ)

/-- A divisor of the level cannot acquire a prime factor excluded from that level. -/
lemma lpsOriginalCuspWidthNat_not_dvd (N p : ℕ) [NeZero N]
    (hpN : ¬p ∣ N) (ρ : SL(2, ℤ)) : ¬p ∣ lpsOriginalCuspWidthNat N ρ := by
  intro h
  exact hpN (h.trans (lpsOriginalCuspWidthNat_dvd_level N ρ))

/-- The actual cusp-level ratio excludes every factor excluded from the higher level. -/
lemma lpsOriginalCuspLevelDegree_not_dvd (N M p : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (hpM : ¬p ∣ M) (ρ : SL(2, ℤ)) : ¬p ∣ lpsOriginalCuspLevelDegree N M ρ := by
  intro h
  exact hpM (h.trans (lpsOriginalCuspLevelDegree_dvd_level N M hNM ρ))

/-- The literal original exponential coordinates satisfy the exact integral power formula. -/
lemma lpsOriginalCuspLevelDegree_qParam (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (z : ℂ) :
    Function.Periodic.qParam (lpsOriginalCuspGroup M ρ).strictWidthInfty z ^
      lpsOriginalCuspLevelDegree N M ρ =
        Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty z := by
  change (Complex.exp ((2 : ℂ) * Real.pi * I * z /
    ((lpsOriginalCuspGroup M ρ).strictWidthInfty : ℂ))) ^ lpsOriginalCuspLevelDegree N M ρ =
      Complex.exp ((2 : ℂ) * Real.pi * I * z / ((lpsOriginalCuspGroup N ρ).strictWidthInfty : ℂ))
  rw [←Complex.exp_nat_mul]
  congr 1
  have hmR : (lpsOriginalCuspGroup M ρ).strictWidthInfty =
      (lpsOriginalCuspGroup N ρ).strictWidthInfty * (lpsOriginalCuspLevelDegree N M ρ : ℝ) := by
    rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast]
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (lpsOriginalCuspLevelDegree_mul_width N M hNM ρ).symm
    rw [Nat.cast_mul] at h
    exact h
  have hmC := congrArg Complex.ofReal hmR
  rw [Complex.ofReal_mul, Complex.ofReal_natCast] at hmC
  rw [hmC, div_mul_eq_div_div]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (lpsOriginalCuspLevelDegree_positive N M hNM ρ)))

/-- The canonical map between the actual original interior orbit quotients. -/
def lpsOriginalInteriorForgetLevel (N M : ℕ) (hNM : N ∣ M) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ →
      MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  Quotient.map id (by
    intro a b hab
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ a b at hab
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ a b
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨g, hg⟩ := hab
    exact ⟨⟨g.val, (Subgroup.map_mono (lpsGamma0_level_le N M hNM)) g.property⟩, hg⟩)

/-- The actual interior quotient map preserves the literal upper-half-plane representative. -/
lemma lpsOriginalInteriorForgetLevel_projection (N M : ℕ) (hNM : N ∣ M) (τ : ℍ) :
    lpsOriginalInteriorForgetLevel N M hNM ⟦τ⟧ = ⟦τ⟧ := rfl

/-- Every actual original lower-level interior orbit has a higher-level preimage. -/
lemma lpsOriginalInteriorForgetLevel_surjective (N M : ℕ) (hNM : N ∣ M) :
    Function.Surjective (lpsOriginalInteriorForgetLevel N M hNM) := by
  intro y
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep y
  exact ⟨⟦τ⟧, rfl⟩

/-- The canonical map on actual cusp orbits descends genuine cusp membership and action. -/
def lpsOriginalCuspForgetLevel (N M : ℕ) (hNM : N ∣ M) :
    CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) →
      CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.map
    (fun c : cuspsSubMulAction (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) =>
      (⟨c.val, c.property.mono (Subgroup.map_mono (lpsGamma0_level_le N M hNM))⟩ :
        cuspsSubMulAction (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))))
    (by
      intro a b hab
      change MulAction.orbitRel (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))
        (cuspsSubMulAction (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) a b at hab
      change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        (cuspsSubMulAction (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) _ _
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
      obtain ⟨g, hg⟩ := hab
      refine ⟨⟨g.val, (Subgroup.map_mono (lpsGamma0_level_le N M hNM)) g.property⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun x : cuspsSubMulAction
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) => (x.val : OnePoint ℝ)) hg)

/-- The actual cusp map preserves the same integral representative acting on infinity. -/
lemma lpsOriginalCuspForgetLevel_projection (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspForgetLevel N M hNM (lpsOriginalCuspOrbit M ρ) = lpsOriginalCuspOrbit N ρ := by
  rw [lpsOriginalCuspOrbit, lpsOriginalCuspOrbit, cosetToCuspOrbit_apply_mk,
    cosetToCuspOrbit_apply_mk]
  rfl

/-- Every genuine lower-level cusp orbit has a higher-level preimage. -/
lemma lpsOriginalCuspForgetLevel_surjective (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) : Function.Surjective (lpsOriginalCuspForgetLevel N M hNM) := by
  intro c
  obtain ⟨ρ, rfl⟩ := lpsOriginalCuspOrbit_surjective N c
  exact ⟨lpsOriginalCuspOrbit M ρ, lpsOriginalCuspForgetLevel_projection N M hNM ρ⟩

/-- The actual original filled-set map assembled from its genuine interior and cusp maps. -/
def lpsOriginalFilledForgetLevel (N M : ℕ) (hNM : N ∣ M) :
    LPSOriginalFilledCurve M → LPSOriginalFilledCurve N :=
  Sum.map (lpsOriginalInteriorForgetLevel N M hNM) (lpsOriginalCuspForgetLevel N M hNM)

/-- The original filled-set map recovers the literal upper-half-plane projection. -/
lemma lpsOriginalFilledForgetLevel_projection (N M : ℕ) (hNM : N ∣ M) (τ : ℍ) :
    lpsOriginalFilledForgetLevel N M hNM (Sum.inl ⟦τ⟧) = Sum.inl ⟦τ⟧ := rfl

/-- The original filled-set map sends the represented genuine cusp to that same represented cusp. -/
lemma lpsOriginalFilledForgetLevel_cusp (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalFilledForgetLevel N M hNM (Sum.inr (lpsOriginalCuspOrbit M ρ)) =
      Sum.inr (lpsOriginalCuspOrbit N ρ) := by
  exact congrArg Sum.inr (lpsOriginalCuspForgetLevel_projection N M hNM ρ)

/-- The actual original filled-set level map is surjective. -/
lemma lpsOriginalFilledForgetLevel_surjective (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) : Function.Surjective (lpsOriginalFilledForgetLevel N M hNM) := by
  intro y
  cases y with
  | inl y =>
    obtain ⟨x, hx⟩ := lpsOriginalInteriorForgetLevel_surjective N M hNM y
    exact ⟨Sum.inl x, congrArg Sum.inl hx⟩
  | inr c =>
    obtain ⟨x, hx⟩ := lpsOriginalCuspForgetLevel_surjective N M hNM c
    exact ⟨Sum.inr x, congrArg Sum.inr hx⟩

/-- The same original filled j function commutes with actual level descent. -/
lemma lpsOriginalFilledForgetLevel_j (N M : ℕ) (hNM : N ∣ M) (x : LPSOriginalFilledCurve M) :
    lpsOriginalFilledJ N (lpsOriginalFilledForgetLevel N M hNM x) = lpsOriginalFilledJ M x := by
  cases x with
  | inl y => induction y using Quotient.inductionOn; rfl
  | inr c => rfl

end
end QEC.Coding.TannerLiftedProduct
