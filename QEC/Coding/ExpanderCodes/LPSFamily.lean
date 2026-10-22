import QEC.Coding.ExpanderCodes.JacobiFourSquareCount
import QEC.Coding.ExpanderCodes.TannerGraphExpansion

/-!
# The variable-prime LPS labelled group family

This file assembles the arithmetic residue-prime sequence and the normalized
quaternion labels into the concrete cofinal family of finite `PSL(2,q)`
groups used by the PK22 Tanner construction.  Jacobi's exact shell count is
available from `JacobiFourSquareCount`; the remaining graph-theoretic input
for the terminal construction is the LPS Ramanujan spectral estimate.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- The fixed finite direction type at degree prime `p`. -/
abbrev LPSGeneratorIndex (p : ℕ) :=
  {t // t ∈ lpsQuaternionShell p}

noncomputable instance : Fintype (LPSGeneratorIndex p) :=
  Fintype.ofFinset (lpsQuaternionShell p) fun _ => Iff.rfl

noncomputable instance : DecidableEq (LPSGeneratorIndex p) :=
  Classical.decEq _

/-- The source-compatible quotient prime at sequence index `n`. -/
def lpsResiduePrimeSequence
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    LPSResiduePrime p :=
  lpsResiduePrimeAt hp hp4 n

theorem lt_lpsResiduePrimeSequence_q
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    n < (lpsResiduePrimeSequence hp hp4 n).q :=
  lt_lpsResiduePrimeAt hp hp4 n

/-- The finite vertex group at one index of the LPS family. -/
abbrev LPSVertexGroup
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :=
  PSL(2, ZMod (lpsResiduePrimeSequence hp hp4 n).q)

/-- The normalized quaternion label in the actual `PSL(2,q)` vertex group. -/
noncomputable def lpsQuaternionLabel
    (a : LPSResiduePrime p) :
    LPSGeneratorIndex p → PSL(2, ZMod a.q) :=
  fun t => lpsQuaternionPSL a t.1
    (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)

theorem lpsQuaternionLabel_injective (a : LPSResiduePrime p) :
    Function.Injective (lpsQuaternionLabel a) :=
  lpsQuaternionPSL_injective a

theorem card_lpsGeneratorIndex :
    Fintype.card (LPSGeneratorIndex p) =
      (lpsQuaternionShell p).card := by
  classical
  simp [LPSGeneratorIndex]

/-- Quaternion conjugation is an involutive permutation of the fixed
direction type. -/
def lpsGeneratorConjEquiv (hp : 0 < p) :
    LPSGeneratorIndex p ≃ LPSGeneratorIndex p where
  toFun t := ⟨t.1.conj,
    (conj_mem_lpsQuaternionShell_iff hp t.1).mpr t.2⟩
  invFun t := ⟨t.1.conj,
    (conj_mem_lpsQuaternionShell_iff hp t.1).mpr t.2⟩
  left_inv t := by
    apply Subtype.ext
    exact t.1.conj_conj
  right_inv t := by
    apply Subtype.ext
    exact t.1.conj_conj

/-- The image of the fixed direction type is exactly the previously defined
finite generator set. -/
theorem image_lpsQuaternionLabel (a : LPSResiduePrime p) :
    Finset.univ.image (lpsQuaternionLabel a) =
      lpsQuaternionGeneratorsPSL a := by
  classical
  rfl

/-- Quaternion conjugation supplies the inverse-labelled direction. -/
theorem exists_lpsQuaternionLabel_eq_inv
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    ∃ u : LPSGeneratorIndex p,
      lpsQuaternionLabel a u = (lpsQuaternionLabel a t)⁻¹ := by
  let u : LPSGeneratorIndex p :=
    ⟨t.1.conj, (conj_mem_lpsQuaternionShell_iff
      a.degreePrime.pos t.1).mpr t.2⟩
  refine ⟨u, ?_⟩
  simpa [lpsQuaternionLabel, u] using
    lpsQuaternionPSL_conj_eq_inv a t.1
      (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)

@[simp] theorem lpsQuaternionLabel_conj
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    lpsQuaternionLabel a (lpsGeneratorConjEquiv a.degreePrime.pos t) =
      (lpsQuaternionLabel a t)⁻¹ := by
  simpa [lpsQuaternionLabel, lpsGeneratorConjEquiv] using
    lpsQuaternionPSL_conj_eq_inv a t.1
      (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)

/-- Exact order of the `n`th vertex group. -/
theorem card_lpsVertexGroup
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Fintype.card (LPSVertexGroup hp hp4 n) =
      let q := (lpsResiduePrimeSequence hp hp4 n).q
      q * (q ^ 2 - 1) / 2 :=
  (lpsResiduePrimeSequence hp hp4 n).card_psl

private theorem residuePrime_q_le_card_psl (a : LPSResiduePrime p) :
    a.q ≤ Fintype.card PSL(2, ZMod a.q) := by
  have hq : 3 ≤ a.q := by
    have hmod := a.modFour
    have hprime := a.prime.two_le
    omega
  have hsq : 2 ≤ a.q ^ 2 - 1 := by
    have hsq3 : 3 ≤ a.q ^ 2 := by
      calc
        3 ≤ 3 ^ 2 := by norm_num
        _ ≤ a.q ^ 2 := pow_le_pow_left' hq 2
    omega
  have hmul : 2 * a.q ≤ a.q * (a.q ^ 2 - 1) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left a.q hsq
  have hcard := a.two_mul_card_psl
  omega

/-- The `PSL(2,q)` vertex groups are cofinal in cardinality. -/
theorem lpsVertexGroup_card_cofinal
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∀ N : ℕ, ∃ n : ℕ,
      N ≤ Fintype.card (LPSVertexGroup hp hp4 n) := by
  intro N
  refine ⟨N, ?_⟩
  exact (Nat.le_of_lt (lt_lpsResiduePrimeSequence_q hp hp4 N)).trans
    (residuePrime_q_le_card_psl (lpsResiduePrimeSequence hp hp4 N))

/-- The concrete label at the `n`th member of the cofinal family. -/
noncomputable def lpsQuaternionFamilyLabel
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    LPSGeneratorIndex p → LPSVertexGroup hp hp4 n :=
  lpsQuaternionLabel (lpsResiduePrimeSequence hp hp4 n)

theorem lpsQuaternionFamilyLabel_injective
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsQuaternionFamilyLabel hp hp4 n) :=
  lpsQuaternionLabel_injective (lpsResiduePrimeSequence hp hp4 n)

/-- Once Jacobi's count identifies the normalized shell cardinality with
`p + 1`, this equivalence presents the LPS directions in the same `Fin`
coordinates used by the local-code matrices. -/
noncomputable def lpsFinGeneratorEquiv
    (hCount : (lpsQuaternionShell p).card = p + 1) :
    Fin (p + 1) ≃ LPSGeneratorIndex p :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, card_lpsGeneratorIndex]
    exact hCount.symm)

/-- The concrete LPS family label reindexed by `Fin (p + 1)`. -/
noncomputable def lpsFinQuaternionFamilyLabel
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    Fin (p + 1) → LPSVertexGroup hp hp4 n :=
  fun i => lpsQuaternionFamilyLabel hp hp4 n
    (lpsFinGeneratorEquiv hCount i)

theorem lpsFinQuaternionFamilyLabel_injective
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    Function.Injective (lpsFinQuaternionFamilyLabel hp hp4 hCount n) :=
  (lpsQuaternionFamilyLabel_injective hp hp4 n).comp
    (lpsFinGeneratorEquiv hCount).injective

/-- Direction reindexing leaves the concrete LPS Cayley multigraph exactly
unchanged. -/
theorem rightCayleyGraph_lpsFinQuaternionFamilyLabel
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n) =
      rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n) :=
  rightCayleyGraph_reindex
    (lpsQuaternionFamilyLabel hp hp4 n) (lpsFinGeneratorEquiv hCount)

/-- The labelled Cayley multigraph is regular of degree equal to the shell
cardinality; Jacobi's theorem will identify this number with `p+1`. -/
theorem lpsRightCayleyGraph_isRegular
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    SmallSetExpansion.IsRegular
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
      (lpsQuaternionShell p).card := by
  simpa [card_lpsGeneratorIndex] using
    rightCayleyGraph_isRegular (lpsQuaternionFamilyLabel hp hp4 n)

/-- Inverse closure of the normalized quaternion labels makes the Cayley
multigraph symmetric for every admissible residue prime, independently of
the particular cofinal enumeration used below. -/
theorem rightCayleyGraph_lpsQuaternionLabel_isSymmetric
    (a : LPSResiduePrime p) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsQuaternionLabel a)) := by
  intro g h
  let e := lpsGeneratorConjEquiv a.degreePrime.pos
  unfold rightCayleyGraph
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  refine
    { toFun := fun t => ⟨e t.1, ?_⟩
      invFun := fun t => ⟨e.symm t.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have ht : g * lpsQuaternionLabel a t.1 = h := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using t.2
    have hinv : lpsQuaternionLabel a (e t.1) =
        (lpsQuaternionLabel a t.1)⁻¹ := by
      simp [e]
    have heq : h * lpsQuaternionLabel a (e t.1) = g := by
      rw [hinv]
      exact mul_inv_eq_of_eq_mul ht.symm
    simpa using heq
  · have ht : h * lpsQuaternionLabel a t.1 = g := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using t.2
    have hinv : lpsQuaternionLabel a (e.symm t.1) =
        (lpsQuaternionLabel a t.1)⁻¹ := by
      have he := lpsQuaternionLabel_conj a (e.symm t.1)
      have he' := congrArg Inv.inv he
      simpa [e] using he'.symm
    have heq : g * lpsQuaternionLabel a (e.symm t.1) = h := by
      rw [hinv]
      exact mul_inv_eq_of_eq_mul ht.symm
    simpa using heq
  · intro t
    apply Subtype.ext
    exact e.symm_apply_apply t.1
  · intro t
    apply Subtype.ext
    exact e.apply_symm_apply t.1

/-- Inverse closure of the normalized quaternion labels makes the concrete
base Cayley multigraph symmetric. -/
theorem lpsRightCayleyGraph_isSymmetric
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) := by
  exact rightCayleyGraph_lpsQuaternionLabel_isSymmetric
    (lpsResiduePrimeSequence hp hp4 n)

/-- In `Fin (p + 1)` coordinates the concrete LPS Cayley multigraph is
exactly `(p + 1)`-regular. -/
theorem lpsFinRightCayleyGraph_isRegular
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    SmallSetExpansion.IsRegular
      (rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n))
      (p + 1) := by
  simpa using rightCayleyGraph_isRegular
    (lpsFinQuaternionFamilyLabel hp hp4 hCount n)

/-- The reindexed concrete LPS Cayley multigraph remains symmetric. -/
theorem lpsFinRightCayleyGraph_isSymmetric
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n)) := by
  rw [rightCayleyGraph_lpsFinQuaternionFamilyLabel hp hp4 hCount n]
  exact lpsRightCayleyGraph_isSymmetric hp hp4 n

/-- The source's base-Cayley mixing estimate, once proved, transfers directly
to the concrete bipartite double cover used by the Tanner product. -/
theorem lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound
    (hp : p.Prime) (hp4 : p % 4 = 1) (n degree : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : SmallSetExpansion.HasExpanderMixingBound
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n))
      degree spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (lpsQuaternionFamilyLabel hp hp4 n))
      degree spectral :=
  rightDoubleCoverGraph_hasPartiteExpanderMixingBound
    (lpsQuaternionFamilyLabel hp hp4 n) degree spectral
    hSpectralNonnegative hMixing

/-- Specialized spectral-to-double-cover bridge for the concrete LPS family.
The only non-elementary input left in this statement is the base Cayley
mean-zero bilinear estimate itself. -/
theorem lpsRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (lpsQuaternionFamilyLabel hp hp4 n))
      (lpsQuaternionShell p).card spectral := by
  simpa [card_lpsGeneratorIndex] using
    rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
      (lpsQuaternionFamilyLabel hp hp4 n) spectral
      (lpsRightCayleyGraph_isSymmetric hp hp4 n)
      hSpectralNonnegative hSpectral

/-- The spectral-to-double-cover bridge in the exact `Fin (p + 1)`
coordinates consumed by the local-code construction. -/
theorem lpsFinRightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph
        (lpsFinQuaternionFamilyLabel hp hp4 hCount n)) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph
        (lpsFinQuaternionFamilyLabel hp hp4 hCount n))
      (p + 1) spectral := by
  simpa using
    rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
      (lpsFinQuaternionFamilyLabel hp hp4 hCount n) spectral
      (lpsFinRightCayleyGraph_isSymmetric hp hp4 hCount n)
      hSpectralNonnegative hSpectral

end QEC.Coding.TannerLiftedProduct
