import QEC.Locality.ConnectivityTradeoff.TwoPassDimension
/-!
# Baspin--Krishna connectivity-separator tradeoff

This module realizes the approved public binary-stabilizer QLDPC
specialization of [BK22, Theorem 23].  The source's undefined `r_0(n)` token
is deliberately absent: it is unused by the operative conclusion and Lean-QEC
assigns it no meaning.

The logarithmic branch has an explicit project-owned `gamma`-gap hypothesis
on the actually measured `cMax`.  It is not inferred from pointwise
`cMax < 1`.  The uniform branch is separate and uses one family-uniform
ceiling below one.
-/

noncomputable section

namespace QEC.Locality

universe u v

namespace BKQLDPCFamily

variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]

/-- The two-pass denominator is the public negative distance exponent. -/
private theorem two_pass_denominator_inv_eq_public_rpow
    {d c : ℝ} (hd : 0 < d) :
    (d ^ (1 - c) * d ^ (1 - c))⁻¹ = d ^ (2 * (c - 1)) := by
  rw [← Real.rpow_add hd]
  rw [show 2 * (c - 1) = -((1 - c) + (1 - c)) by ring, Real.rpow_neg hd.le]

/-- Rewrites the actual two-pass logarithmic bound into the approved public shape. -/
private theorem two_pass_logarithmic_gap_bound_public_shape
    {k n d c gamma : ℝ} (hd : 0 < d)
    (hbound : k ≤
      ((3 * Real.log n / (bkEntropyGap * gamma)) *
          (3 * Real.log n / (bkEntropyGap * gamma))) * n /
        ((d ^ (1 - c)) * (d ^ (1 - c))) ) :
    k ≤ ((3 / (bkEntropyGap * gamma)) * (3 / (bkEntropyGap * gamma))) * n *
      d ^ (2 * (c - 1)) * (Real.log n) ^ 2 := by
  calc
    k ≤ ((3 * Real.log n / (bkEntropyGap * gamma)) *
          (3 * Real.log n / (bkEntropyGap * gamma))) * n /
        ((d ^ (1 - c)) * (d ^ (1 - c))) := hbound
    _ = ((3 / (bkEntropyGap * gamma)) * (3 / (bkEntropyGap * gamma))) * n *
        d ^ (2 * (c - 1)) * (Real.log n) ^ 2 := by
      rw [div_eq_mul_inv, two_pass_denominator_inv_eq_public_rpow hd]
      ring

/-- Rewrites the actual two-pass uniform bound into the approved public shape. -/
private theorem two_pass_uniform_gap_bound_public_shape
    {k n d c ceiling : ℝ} (hd : 0 < d)
    (hbound : k ≤
      ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * n /
        ((d ^ (1 - c)) * (d ^ (1 - c))) ) :
    k ≤ ((3 / (bkEntropyGap * (1 - ceiling))) *
      (3 / (bkEntropyGap * (1 - ceiling)))) * n * d ^ (2 * (c - 1)) := by
  calc
    k ≤ ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * n /
        ((d ^ (1 - c)) * (d ^ (1 - c))) := hbound
    _ = ((3 / (bkEntropyGap * (1 - ceiling))) *
        (3 / (bkEntropyGap * (1 - ceiling)))) * n * d ^ (2 * (c - 1)) := by
      rw [div_eq_mul_inv, two_pass_denominator_inv_eq_public_rpow hd]

/--
The source-narrowed, Lean-QEC-repaired logarithmic BK terminal.

The `gamma` premise is visible and family-uniform.  It controls the measured
exponent only on a valid-index tail; it supplies neither a partition nor a
recovery, both of which come from the actual two-pass construction in #381.
-/
theorem exists_bk_logarithmic_gap_tradeoff
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
        (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1)) *
          (Real.log i.1) ^ 2) := by
  rcases hcofinal 0 with ⟨_, _, _⟩
  let K : ℝ := (3 / (bkEntropyGap * gamma)) * (3 / (bkEntropyGap * gamma))
  have hdenomPos : 0 < bkEntropyGap * gamma :=
    mul_pos bkEntropyGap_pos hgamma
  have hKPos : 0 < K := by
    dsimp [K]
    exact mul_pos (div_pos (by norm_num) hdenomPos) (div_pos (by norm_num) hdenomPos)
  rcases family.eventually_encodedQubits_cast_le_cMax_logarithmic_gap_bound
      hgamma hgap with ⟨start, hstart⟩
  refine ⟨K, hKPos, start, ?_⟩
  intro n hn hvalid
  have hdistance : (0 : ℝ) < family.distance n := by
    exact_mod_cast Nat.zero_lt_two.trans_le (family.distance_two_le n hvalid)
  simpa [K] using two_pass_logarithmic_gap_bound_public_shape hdistance
    (hstart n hn hvalid)

/--
The uniform-gap BK terminal, retaining the pointwise measured `cMax` in the
distance exponent while using a family-uniform coefficient ceiling.
-/
theorem exists_bk_uniform_gap_tradeoff
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices)
    (huniform : family.UniformCMaxBelowOne) :
    ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
        (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1))) := by
  rcases hcofinal 0 with ⟨_, _, _⟩
  rcases family.eventually_encodedQubits_cast_le_uniform_ceiling huniform with
    ⟨ceiling, hceiling0, hceiling1, start, hstart⟩
  let K : ℝ := (3 / (bkEntropyGap * (1 - ceiling))) *
    (3 / (bkEntropyGap * (1 - ceiling)))
  have hdenomPos : 0 < bkEntropyGap * (1 - ceiling) :=
    mul_pos bkEntropyGap_pos (sub_pos.mpr hceiling1)
  have hKPos : 0 < K := by
    dsimp [K]
    exact mul_pos (div_pos (by norm_num) hdenomPos) (div_pos (by norm_num) hdenomPos)
  refine ⟨K, hKPos, start, ?_⟩
  intro n hn hvalid
  have hdistance : (0 : ℝ) < family.distance n := by
    exact_mod_cast Nat.zero_lt_two.trans_le (family.distance_two_le n hvalid)
  simpa [K] using two_pass_uniform_gap_bound_public_shape hdistance
    (hstart n hn hvalid)

/--
The registered public BK terminal contains both approved branches.  It is a
binary-stabilizer QLDPC specialization over cofinally many valid indices, with
one chosen independent presentation and its measured induced-subgraph profile
at each index.  It does not assert generator invariance or define BK22's
undefined `r_0(n)` token.
-/
theorem bk_connectivity_separator_tradeoff
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices) :
    (∀ gamma : ℝ, 0 < gamma →
      family.EventuallyOnValidIndices (fun i ↦
        gamma ≤ (1 - family.cMax i) * Real.log i.1) →
      ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
        (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
          (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1)) *
            (Real.log i.1) ^ 2)) ∧
      (family.UniformCMaxBelowOne →
        ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
          (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
            (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1)))) := by
  constructor
  · intro gamma hgamma hgap
    exact family.exists_bk_logarithmic_gap_tradeoff hcofinal hgamma hgap
  · intro huniform
    exact family.exists_bk_uniform_gap_tradeoff hcofinal huniform

end BKQLDPCFamily

end QEC.Locality
