import QEC.Coding.FiberBundle.TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Fourier diagonalization of the HHO20 cyclic twist graph

The twist graph is a Cayley multigraph on `ZMod ell`.  Its additive
characters diagonalize every sampled translation.  This file proves that
fact for the concrete `outNeighbor` and `inNeighbor` maps and reduces the
HHO20 operator event to a uniform bound on the nonzero character
multipliers.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators ZMod

/-- The complexification of the unnormalized undirected adjacency action. -/
noncomputable def complexNeighborSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Complex)
    (u : ZMod ell) : Complex :=
  ∑ τ : Fin typeCount,
    (g (outNeighbor twistSample τ u) +
      g (inNeighbor twistSample τ u))

/-- Fourier multiplier of the sampled undirected cyclic Cayley graph. -/
noncomputable def cayleyMultiplier
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) : Complex :=
  ∑ τ : Fin typeCount,
    (ZMod.stdAddChar (step twistSample τ * frequency) +
      ZMod.stdAddChar (-(step twistSample τ * frequency)))

/--
All nonconstant Fourier multipliers have magnitude at most
`2 * typeCount / 50000`.
-/
def HasHHO20CayleySpectrum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ frequency : ZMod ell, frequency ≠ 0 →
    50000 * ‖cayleyMultiplier twistSample frequency‖ ≤
      2 * typeCount

/-- DFT of one forward type translation. -/
theorem dft_outNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (g : ZMod ell → Complex)
    (frequency : ZMod ell) :
    (∑ u : ZMod ell,
        ZMod.stdAddChar (-(u * frequency)) *
          g (outNeighbor twistSample τ u)) =
      ZMod.stdAddChar (step twistSample τ * frequency) *
        ∑ u : ZMod ell,
          ZMod.stdAddChar (-(u * frequency)) * g u := by
  calc
    _ = ∑ v : ZMod ell,
        ZMod.stdAddChar
          (-((inNeighbor twistSample τ v) * frequency)) * g v := by
      exact Fintype.sum_equiv
        (typeTranslation twistSample τ)
        _ _ (fun u => by
          simp [outNeighbor, inNeighbor])
    _ = ∑ v : ZMod ell,
        ZMod.stdAddChar (step twistSample τ * frequency) *
          (ZMod.stdAddChar (-(v * frequency)) * g v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [inNeighbor_eq_sub, ← mul_assoc,
        ← ZMod.stdAddChar.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- DFT of one inverse type translation. -/
theorem dft_inNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (g : ZMod ell → Complex)
    (frequency : ZMod ell) :
    (∑ u : ZMod ell,
        ZMod.stdAddChar (-(u * frequency)) *
          g (inNeighbor twistSample τ u)) =
      ZMod.stdAddChar (-(step twistSample τ * frequency)) *
        ∑ u : ZMod ell,
          ZMod.stdAddChar (-(u * frequency)) * g u := by
  calc
    _ = ∑ v : ZMod ell,
        ZMod.stdAddChar
          (-((outNeighbor twistSample τ v) * frequency)) * g v := by
      exact Fintype.sum_equiv
        (typeTranslation twistSample τ).symm
        _ _ (fun u => by
          simp [outNeighbor, inNeighbor])
    _ = ∑ v : ZMod ell,
        ZMod.stdAddChar (-(step twistSample τ * frequency)) *
          (ZMod.stdAddChar (-(v * frequency)) * g v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [outNeighbor_eq_add, ← mul_assoc,
        ← ZMod.stdAddChar.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- The cyclic twist-graph adjacency action is diagonal in the DFT basis. -/
theorem dft_complexNeighborSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Complex)
    (frequency : ZMod ell) :
    ZMod.dft (complexNeighborSum twistSample g) frequency =
      cayleyMultiplier twistSample frequency *
        ZMod.dft g frequency := by
  simp only [ZMod.dft_apply, complexNeighborSum, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_add, Finset.sum_add_distrib,
    dft_outNeighbor, dft_inNeighbor]
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  rw [cayleyMultiplier, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  ring

/-- Conjugating the negative standard character recovers the character. -/
@[simp]
theorem conj_stdAddChar_neg
    {ell : Nat}
    [NeZero ell]
    (x : ZMod ell) :
    star (ZMod.stdAddChar (-x)) =
      ZMod.stdAddChar x := by
  rw [AddChar.map_neg_eq_conj]
  simp

/-- Parseval identity for the unnormalized DFT on `ZMod ell`. -/
theorem dft_parseval
    {ell : Nat}
    [NeZero ell]
    (f g : ZMod ell → Complex) :
    (∑ frequency : ZMod ell,
        star (ZMod.dft f frequency) *
          ZMod.dft g frequency) =
      ell * ∑ u : ZMod ell, star (f u) * g u := by
  calc
    _ = ∑ frequency : ZMod ell,
        (∑ u : ZMod ell,
          ZMod.stdAddChar (u * frequency) *
            star (f u)) *
          ZMod.dft g frequency := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      congr 1
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul, star_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [star_mul]
      simp
      ring
    _ = ∑ u : ZMod ell,
        star (f u) *
          (∑ frequency : ZMod ell,
            ZMod.stdAddChar (u * frequency) *
              ZMod.dft g frequency) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _hu
      calc
        _ = ∑ frequency : ZMod ell,
            star (f u) *
              (ZMod.stdAddChar (u * frequency) *
                ZMod.dft g frequency) := by
          apply Finset.sum_congr rfl
          intro frequency _hfrequency
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ = ∑ u : ZMod ell,
        star (f u) *
          ZMod.dft (ZMod.dft g) (-u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      congr 1
      rw [ZMod.dft_apply]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      congr 1
      ring_nf
    _ = ∑ u : ZMod ell,
        star (f u) * (ell * g u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [congr_fun (ZMod.dft_dft g) (-u)]
      simp
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring

/-- Squared `ℓ₂` norm Parseval identity for the unnormalized DFT. -/
theorem sum_normSq_dft
    {ell : Nat}
    [NeZero ell]
    (g : ZMod ell → Complex) :
    (∑ frequency : ZMod ell,
        Complex.normSq (ZMod.dft g frequency)) =
      ell * ∑ u : ZMod ell, Complex.normSq (g u) := by
  have h := dft_parseval g g
  rw [← Complex.ofReal_inj]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  exact h

/--
A nonconstant character bound controls the full adjacency energy on every
zero-mean complex function.
-/
theorem complexNeighborSum_energy_bound_of_cayleySpectrum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hSpectrum : HasHHO20CayleySpectrum twistSample)
    (g : ZMod ell → Complex)
    (hzero : (∑ u : ZMod ell, g u) = 0) :
    (50000 : Real) ^ 2 *
        (∑ u : ZMod ell,
          Complex.normSq (complexNeighborSum twistSample g u)) ≤
      (2 * typeCount : Real) ^ 2 *
        ∑ u : ZMod ell, Complex.normSq (g u) := by
  have hPointwise (frequency : ZMod ell) :
      (50000 : Real) ^ 2 *
          Complex.normSq
            (ZMod.dft (complexNeighborSum twistSample g) frequency) ≤
        (2 * typeCount : Real) ^ 2 *
          Complex.normSq (ZMod.dft g frequency) := by
    rw [dft_complexNeighborSum, Complex.normSq_mul]
    by_cases hfrequency : frequency = 0
    · subst frequency
      rw [ZMod.dft_apply_zero, hzero]
      simp
    · have hBound := hSpectrum frequency hfrequency
      have hBoundSq :
          (50000 : Real) ^ 2 *
              Complex.normSq (cayleyMultiplier twistSample frequency) ≤
            (2 * typeCount : Real) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        simpa only [mul_pow] using
          (sq_le_sq₀
            (by positivity :
              (0 : Real) ≤
                50000 * ‖cayleyMultiplier twistSample frequency‖)
            (by positivity : (0 : Real) ≤ 2 * typeCount)).mpr hBound
      calc
        _ =
            ((50000 : Real) ^ 2 *
              Complex.normSq (cayleyMultiplier twistSample frequency)) *
                Complex.normSq (ZMod.dft g frequency) := by ring
        _ ≤
            (2 * typeCount : Real) ^ 2 *
              Complex.normSq (ZMod.dft g frequency) :=
          mul_le_mul_of_nonneg_right hBoundSq
            (Complex.normSq_nonneg _)
  have hSum :
      (∑ frequency : ZMod ell,
        (50000 : Real) ^ 2 *
          Complex.normSq
            (ZMod.dft (complexNeighborSum twistSample g) frequency)) ≤
        ∑ frequency : ZMod ell,
          (2 * typeCount : Real) ^ 2 *
            Complex.normSq (ZMod.dft g frequency) :=
    Finset.sum_le_sum fun frequency _hfrequency =>
      hPointwise frequency
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    sum_normSq_dft, sum_normSq_dft] at hSum
  have hScaled :
      (ell : Real) *
          ((50000 : Real) ^ 2 *
            ∑ u : ZMod ell,
              Complex.normSq (complexNeighborSum twistSample g u)) ≤
        (ell : Real) *
          ((2 * typeCount : Real) ^ 2 *
            ∑ u : ZMod ell, Complex.normSq (g u)) := by
    convert hSum using 1 <;> ring
  have hEll : (0 : Real) < ell := by
    exact_mod_cast NeZero.pos ell
  exact le_of_mul_le_mul_left hScaled hEll

/-- Complex adjacency agrees with the real adjacency on real-valued inputs. -/
theorem complexNeighborSum_ofReal
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Real)
    (u : ZMod ell) :
    complexNeighborSum twistSample (fun v => (g v : Complex)) u =
      (undirectedNeighborSum twistSample g u : Complex) := by
  simp [complexNeighborSum, undirectedNeighborSum]

/-- The cyclic character event implies the real operator-mixing event. -/
theorem hasHHO20OperatorMixing_of_cayleySpectrum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hSpectrum : HasHHO20CayleySpectrum twistSample) :
    HasHHO20OperatorMixing twistSample := by
  intro f g _hzeroF hzeroG
  have hzeroGC :
      (∑ u : ZMod ell, (g u : Complex)) = 0 := by
    exact_mod_cast hzeroG
  have hEnergyComplex :=
    complexNeighborSum_energy_bound_of_cayleySpectrum
      twistSample hSpectrum (fun u => (g u : Complex)) hzeroGC
  have hEnergy :
      (50000 : Real) ^ 2 *
          (∑ u : ZMod ell,
            (undirectedNeighborSum twistSample g u) ^ 2) ≤
        (2 * typeCount : Real) ^ 2 *
          ∑ u : ZMod ell, (g u) ^ 2 := by
    simpa only [complexNeighborSum_ofReal,
      Complex.normSq_ofReal, pow_two] using hEnergyComplex
  have hCauchy :
      (adjacencyPairing twistSample f g) ^ 2 ≤
        (∑ u : ZMod ell, (f u) ^ 2) *
          ∑ u : ZMod ell,
            (undirectedNeighborSum twistSample g u) ^ 2 := by
    simpa only [adjacencyPairing] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (ZMod ell))
        f (undirectedNeighborSum twistSample g))
  have hFnonneg :
      (0 : Real) ≤ ∑ u : ZMod ell, (f u) ^ 2 :=
    Finset.sum_nonneg fun _u _hu => sq_nonneg _
  calc
    (50000 * |adjacencyPairing twistSample f g|) ^ 2 =
        (50000 : Real) ^ 2 *
          (adjacencyPairing twistSample f g) ^ 2 := by
      rw [mul_pow, sq_abs]
    _ ≤
        (50000 : Real) ^ 2 *
          ((∑ u : ZMod ell, (f u) ^ 2) *
            ∑ u : ZMod ell,
              (undirectedNeighborSum twistSample g u) ^ 2) :=
      mul_le_mul_of_nonneg_left hCauchy (sq_nonneg _)
    _ =
        (∑ u : ZMod ell, (f u) ^ 2) *
          ((50000 : Real) ^ 2 *
            ∑ u : ZMod ell,
              (undirectedNeighborSum twistSample g u) ^ 2) := by ring
    _ ≤
        (∑ u : ZMod ell, (f u) ^ 2) *
          ((2 * typeCount : Real) ^ 2 *
            ∑ u : ZMod ell, (g u) ^ 2) :=
      mul_le_mul_of_nonneg_left hEnergy hFnonneg
    _ =
        (2 * typeCount : Real) ^ 2 *
          (∑ u : ZMod ell, (f u) ^ 2) *
          ∑ u : ZMod ell, (g u) ^ 2 := by ring

end QEC.Coding.FiberBundle.TwistGraph
