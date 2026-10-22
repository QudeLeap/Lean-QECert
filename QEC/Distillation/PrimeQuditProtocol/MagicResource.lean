import QEC.Distillation.PrimeQuditProtocol.CubicCSS
import QEC.Semantics.Entropy.Convexity
import QEC.Semantics.Instruments.Core
import QEC.Semantics.Entropy.Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
/-!
# KT19 prime-qudit magic-basis resources

This module constructs the source-selected p-dependent magic-basis-diagonal
resource of the KT19 distillation protocol:

- the single-qudit magic basis `M_(p,a) = Z^a U_{1,3} |+⟩` with its explicit
  amplitudes, orthonormality, and complete label instrument;
- the sitewise register states `|M_e⟩ = Z(e) U_{1,3}^{⊗n} |+^n⟩` and the
  character kets `|+_e⟩ = Z(e) |+^n⟩` with their Fourier orthogonality and
  completeness;
- the single-site and register density resources given by an arbitrary
  explicit per-site distribution `mu` on `ZMod p` labels, reconstructed as
  the IID convex combination (no twirl is needed: the resource is directly
  diagonal in the magic basis).

Everything here is parameterized by the actual prime `p`; the protocol and
recurrence layer lives in `KT19Protocol`.
-/

noncomputable section

namespace QEC.Distillation.KT19MagicResource

open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators


namespace KT19PrimeQuditCSS

universe u v w

variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
local instance : DecidableEq Site := Classical.decEq Site
local instance primeQuditRegisterLabelFintypeLocal (p : Nat) [NeZero p]
    (Site : Type u) [Fintype Site] :
    Fintype (PrimeQuditRegisterLabel p Site) := Fintype.ofFinite _

/-! ## Character separation over the prime field -/

/-- The canonical `ZMod p` character detects the zero label. -/
theorem phase_eq_one_iff (x : ZMod p) :
    phase p x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hx0
    have hshift : (ZMod.stdAddChar (N := p)).mulShift x = 1 := by
      ext y
      change phase p (x * y) = 1
      calc
        phase p (x * y) = phase p (y * x) := by rw [mul_comm]
        _ = phase p (y.val • x) := by
          congr 1
          rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
        _ = (phase p x) ^ y.val := AddChar.map_nsmul_eq_pow _ _ _
        _ = 1 := by simp [hx]
    exact (ZMod.isPrimitive_stdAddChar p hx0 hshift).elim
  · intro hx
    subst hx
    exact phase_zero p

/-- Summing the character over all labels separates the zero exponent. -/
theorem sum_phase_smul (c : ZMod p) :
    ∑ x : ZMod p, phase p (c * x) = if c = 0 then (p : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst c
    simp [ZMod.card]
  · let chi : AddChar (ZMod p) ℂ := {
      toFun := fun x => phase p (c * x)
      map_zero_eq_one' := by simp [phase_zero]
      map_add_eq_mul' := by
        intro x y
        rw [mul_add, phase_add]
    }
    have hchi : chi ≠ 1 := by
      intro h
      have h1 := congrArg (fun χ : AddChar (ZMod p) ℂ => χ 1) h
      change phase p (c * 1) = (1 : AddChar (ZMod p) ℂ) 1 at h1
      simp only [mul_one, AddChar.one_apply] at h1
      exact hc ((phase_eq_one_iff p c).1 h1)
    simpa [chi, hc] using AddChar.sum_eq_zero_of_ne_one hchi

/-- The shared real normalization constant of the single-qudit resource. -/
private theorem singleNorm_sq_mul_p :
    (Real.sqrt (p : Real) : Complex)⁻¹ * (Real.sqrt (p : Real) : Complex)⁻¹ * (p : ℂ) = 1 := by
  have hpos : (0 : Real) < (p : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hsqrt : (Real.sqrt (p : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  have hsquare :
      (Real.sqrt (p : Real) : Complex) * (Real.sqrt (p : Real) : Complex) = (p : Complex) := by
    exact_mod_cast Real.mul_self_sqrt hpos.le
  rw [← hsquare]
  field_simp [hsqrt]

/-! ## The single-qudit p-dependent magic basis -/

/-- The displayed magic-basis amplitude of one prime-qudit label. -/
def magicBasisAmplitude (a x : ZMod p) : Complex :=
  phase p (a * x + x ^ 3)

/-- The p-dependent magic-basis ket `Z^a U_{1,3} |+⟩`. -/
def magicBasisKet (a : ZMod p) : PrimeQudit p :=
  zPowerTransport p a (idealU13Resource p)

/-- The basis sum of the resource projects through pointwise evaluation. -/
private theorem sum_basisKet_apply (x : ZMod p) :
    (∑ y : ZMod p, quditBasisKet p y) x = ∑ y : ZMod p, (quditBasisKet p y) x := by
  rw [← PiLp.projₗ_apply (p := 2) (𝕜 := ℂ) (β := fun _ : ZMod p => ℂ) x]
  rw [map_sum]
  simp only [PiLp.projₗ_apply]

@[simp]
theorem magicBasisKet_apply (a x : ZMod p) :
    magicBasisKet p a x =
      (Real.sqrt (p : Real) : Complex)⁻¹ * magicBasisAmplitude p a x := by
  unfold magicBasisKet magicBasisAmplitude idealU13Resource
  rw [zPowerTransport_apply, u13Transport_apply]
  simp only [PiLp.smul_apply]
  rw [sum_basisKet_apply]
  change phase p (a * x) *
      (u13Amplitude p x * ((Real.sqrt (p : Real) : Complex)⁻¹ *
        (∑ y : ZMod p, (quditBasisKet p y) x))) = _
  simp only [u13Amplitude, quditBasisKet, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp only [Fintype.sum_ite_eq]
  rw [phase_add]
  ring

/-- Every magic-basis ket is a normalized physical state. -/
theorem magicBasisKet_inner_self (a : ZMod p) :
    inner ℂ (magicBasisKet p a) (magicBasisKet p a) = 1 := by
  rw [magicBasisKet, (zPowerTransport p a).map_inner, idealU13Resource_inner_self]

/-- The magic basis is orthonormal. -/
theorem magicBasisKet_inner (a b : ZMod p) :
    inner ℂ (magicBasisKet p a) (magicBasisKet p b) = if a = b then 1 else 0 := by
  rw [PiLp.inner_apply]
  simp_rw [magicBasisKet_apply]
  rw [Finset.sum_congr rfl (fun x _ => by
    have hphase :
        starRingEnd ℂ (phase p (a * x + x ^ 3)) * phase p (b * x + x ^ 3) =
          phase p ((b - a) * x) := by
      rw [phase_conj, ← phase_add]
      congr 1
      ring
    calc
      inner ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * x + x ^ 3))
          ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (b * x + x ^ 3)) =
          (Real.sqrt (p : Real) : Complex)⁻¹ * (Real.sqrt (p : Real) : Complex)⁻¹ *
            (starRingEnd ℂ (phase p (a * x + x ^ 3)) * phase p (b * x + x ^ 3)) := by
        rw [RCLike.inner_apply', map_mul, map_inv₀, Complex.conj_ofReal]
        ring
      _ = (Real.sqrt (p : Real) : Complex)⁻¹ * (Real.sqrt (p : Real) : Complex)⁻¹ *
            phase p ((b - a) * x) := by
        rw [hphase])]
  rw [← Finset.mul_sum]
  rw [sum_phase_smul]
  by_cases hab : a = b
  · subst b
    simp [singleNorm_sq_mul_p]
  · have hne : b - a ≠ 0 := by
      intro h
      exact hab (sub_eq_zero.mp h).symm
    simp [hab, hne]

/-- The magic-basis amplitudes separate labels through the character sum. -/
theorem sum_magicBasisCharacter (y x : ZMod p) :
    (∑ a : ZMod p, starRingEnd ℂ (magicBasisAmplitude p a y) * magicBasisAmplitude p a x) =
      if y = x then (p : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun a _ => calc
    starRingEnd ℂ (magicBasisAmplitude p a y) * magicBasisAmplitude p a x
        = phase p ((x - y) * a + (x ^ 3 - y ^ 3)) := by
      unfold magicBasisAmplitude
      rw [phase_conj, ← phase_add]
      congr 1
      ring)]
  rw [Finset.sum_congr rfl (fun a _ => by rw [phase_add])]
  rw [← Finset.sum_mul]
  rw [sum_phase_smul]
  by_cases hyx : y = x
  · subst y
    simp
  · have hne : x - y ≠ 0 := by
      intro h
      exact hyx (sub_eq_zero.mp h).symm
    simp [hyx, hne]

/-- For a normalized state the rank-one projector satisfies `χᵗ (χ χᵗ) = χ χᵗ`. -/
theorem rankOne_adjoint_comp_eq {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (χ : H) (hχ : inner ℂ χ χ = 1) :
    (LinearMap.adjoint (InnerProductSpace.rankOne ℂ χ χ).toLinearMap).comp
        (InnerProductSpace.rankOne ℂ χ χ).toLinearMap =
      (InnerProductSpace.rankOne ℂ χ χ).toLinearMap := by
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  change ((InnerProductSpace.rankOne ℂ χ χ).adjoint).toLinearMap.comp
      (InnerProductSpace.rankOne ℂ χ χ).toLinearMap = _
  rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply]
  change inner ℂ χ (inner ℂ χ z • χ) • χ = inner ℂ χ z • χ
  rw [inner_smul_right, hχ, mul_one]

/-- Summing the magic-basis rank-one projectors recovers the identity. -/
theorem sum_magicBasisKet_rankOne_eq_one :
    (∑ a : ZMod p,
        (InnerProductSpace.rankOne ℂ (magicBasisKet p a)
          (magicBasisKet p a)).toLinearMap) = 1 := by
  apply LinearMap.ext
  intro psi
  ext x
  simp only [LinearMap.sum_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, PiLp.inner_apply, RCLike.inner_apply']
  rw [← PiLp.projₗ_apply (p := 2) (𝕜 := ℂ) (β := fun _ : ZMod p => ℂ) x]
  rw [map_sum]
  simp only [PiLp.projₗ_apply, PiLp.smul_apply, Module.End.one_apply]
  change (∑ a : ZMod p, (∑ y : ZMod p,
      starRingEnd ℂ (magicBasisKet p a y) * psi y) * magicBasisKet p a x) = psi x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [magicBasisKet_apply]
  simp_rw [magicBasisAmplitude]
  have hsummand (y : ZMod p) (a : ZMod p) :
      starRingEnd ℂ (phase p (a * y + y ^ 3)) * phase p (a * x + x ^ 3) =
        phase p ((x - y) * a + (x ^ 3 - y ^ 3)) := by
    rw [phase_conj, ← phase_add]
    congr 1
    ring
  have hmain (y : ZMod p) :
      (∑ a : ZMod p, (starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ *
            phase p (a * y + y ^ 3)) * psi y) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * x + x ^ 3))) =
        psi y * ((Real.sqrt (p : Real) : Complex)⁻¹ *
          (Real.sqrt (p : Real) : Complex)⁻¹ *
            if y = x then (p : ℂ) else 0) := by
    rw [Finset.sum_congr rfl (fun a _ => calc
      (starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * y + y ^ 3)) * psi y) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ * phase p (a * x + x ^ 3)) =
          (Real.sqrt (p : Real) : Complex)⁻¹ * ((Real.sqrt (p : Real) : Complex)⁻¹ *
            (psi y * (starRingEnd ℂ (phase p (a * y + y ^ 3)) *
              phase p (a * x + x ^ 3)))) := by
        rw [map_mul, map_inv₀, Complex.conj_ofReal]
        ring
      _ = (Real.sqrt (p : Real) : Complex)⁻¹ * ((Real.sqrt (p : Real) : Complex)⁻¹ *
            (psi y * phase p ((x - y) * a + (x ^ 3 - y ^ 3)))) := by
        rw [hsummand y a])]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => by rw [phase_add, mul_comm])]
    rw [← Finset.mul_sum]
    rw [sum_phase_smul]
    by_cases hyx : y = x
    · subst y
      simp
      ring
    · have hne : x - y ≠ 0 := by
        intro h
        exact hyx (sub_eq_zero.mp h).symm
      simp [hyx, hne]
  rw [Finset.sum_congr rfl (fun y _ => hmain y)]
  rw [Finset.sum_eq_single x]
  · rw [show (if x = x then (p : ℂ) else 0) = (p : ℂ) by simp]
    rw [show (Real.sqrt (p : Real) : Complex)⁻¹ *
        (Real.sqrt (p : Real) : Complex)⁻¹ * (p : ℂ) = 1 by
      exact singleNorm_sq_mul_p p]
    simp
  · intro y _ hyx
    simp [hyx]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim

/-- The complete per-site magic-basis label instrument. -/
def magicBasisKrausFamily : FiniteKrausFamily (ZMod p) (PrimeQudit p) (PrimeQudit p) where
  operator a :=
    (InnerProductSpace.rankOne ℂ (magicBasisKet p a) (magicBasisKet p a)).toLinearMap

theorem magicBasisKrausFamily_complete : (magicBasisKrausFamily p).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [magicBasisKrausFamily]
  rw [Finset.sum_congr rfl (fun a _ =>
    rankOne_adjoint_comp_eq (magicBasisKet p a) (magicBasisKet_inner_self p a))]
  exact sum_magicBasisKet_rankOne_eq_one p

/-- The observed outcome of each magic-basis Kraus branch is its own label. -/
def magicBasisInstrument : FiniteInstrument (ZMod p) (ZMod p) (PrimeQudit p) (PrimeQudit p) where
  kraus := magicBasisKrausFamily p
  observe := id

/-- The single-site noisy resource with arbitrary explicit nonzero-label weights. -/
def magicResource (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DensityOperator (PrimeQudit p) :=
  DensityOperator.convexCombination Finset.univ mu
    (fun a => DensityOperator.pureDensity (magicBasisKet p a) (by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), magicBasisKet_inner_self]
      norm_num))
    (fun a _ => hmu_nonneg a) hmu_sum

/-! ## Word transports and register character kets -/

/-- The pairing of two register words over the prime field. -/
def registerPairing (e x : PrimeQuditRegisterLabel p Site) : ZMod p :=
  ∑ site : Site, e site * x site

/-- The canonical character phase attached to one register word. -/
def registerPhase (e x : PrimeQuditRegisterLabel p Site) : Complex :=
  phase p (registerPairing p e x)

/-- The sitewise generalized-`Z` word transport. -/
def zWordTransport (e : PrimeQuditRegisterLabel p Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  toLinearEquiv := diagonalLinearEquiv (registerPhase p e)
    (fun x => phase p (-registerPairing p e x))
    (by
      intro x
      change phase p (-registerPairing p e x) * phase p (registerPairing p e x) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p (registerPairing p e x) * phase p (-registerPairing p e x) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (registerPhase p e)
    (fun x => phase_mul_conj p (registerPairing p e x))

@[simp]
theorem zWordTransport_apply (e : PrimeQuditRegisterLabel p Site)
    (psi : PrimeQuditRegister p Site) (x : PrimeQuditRegisterLabel p Site) :
    zWordTransport p e psi x = registerPhase p e x * psi x :=
  rfl

/-- The inverse word transport applies the negated word phase. -/
@[simp]
theorem zWordTransport_symm_apply (e : PrimeQuditRegisterLabel p Site)
    (psi : PrimeQuditRegister p Site) (x : PrimeQuditRegisterLabel p Site) :
    (zWordTransport p e).symm psi x = phase p (-registerPairing p e x) * psi x := by
  unfold zWordTransport UnitaryTransport.symm diagonalLinearEquiv
  rfl

/-- Word transports compose by word addition. -/
theorem zWordTransport_trans (e f : PrimeQuditRegisterLabel p Site) :
    (zWordTransport p e).toLinearEquiv.trans (zWordTransport p f).toLinearEquiv =
      (zWordTransport p (e + f)).toLinearEquiv := by
  apply LinearEquiv.ext
  intro psi
  ext x
  simp only [LinearEquiv.trans_apply, zWordTransport_apply, registerPhase]
  rw [← mul_assoc]
  congr 1
  rw [← phase_add]
  congr 1
  simp [registerPairing, add_mul, Finset.sum_add_distrib, add_comm]

/-- The p-dependent ideal register resource `|+⟩^{⊗ n}`. -/
def idealRegisterState : PrimeQuditRegister p Site :=
  ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) •
    ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x

@[simp]
theorem idealRegisterState_apply (x : PrimeQuditRegisterLabel p Site) :
    idealRegisterState p x = (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site := by
  simp [idealRegisterState, registerBasisKet, EuclideanSpace.basisFun_apply,
    Finset.sum_apply]

/-- The register normalization constant is self-conjugate. -/
private theorem registerNorm_conj :
    starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) =
      (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site := by
  rw [map_pow, map_inv₀, Complex.conj_ofReal]

/-- The squared register normalization constant inverts the cardinality. -/
private theorem registerNorm_sq_mul_pow :
    ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
      ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
        (p : ℂ) ^ Fintype.card Site = 1 := by
  rw [← mul_pow, ← mul_pow, singleNorm_sq_mul_p]
  norm_num

theorem idealRegisterState_inner_self :
    inner ℂ (idealRegisterState p : PrimeQuditRegister p Site)
      (idealRegisterState p : PrimeQuditRegister p Site) = 1 := by
  rw [idealRegisterState]
  change inner ℂ (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) •
      ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)
    (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) •
      ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x) = 1
  rw [inner_smul_left, inner_smul_right]
  change starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
      (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
        inner ℂ (∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)
          (∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)) = 1
  rw [inner_sum (s := Finset.univ) (f := registerBasisKet p)
    (x := ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)]
  simp_rw [sum_inner (s := Finset.univ) (f := registerBasisKet p)]
  simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
  simp_rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]
  change ((Real.sqrt (p : Real) : Complex) ^ Fintype.card Site)⁻¹ *
      (((Real.sqrt (p : Real) : Complex) ^ Fintype.card Site)⁻¹ *
        ↑(Fintype.card (PrimeQuditRegisterLabel p Site))) = 1
  rw [← mul_assoc]
  have hcard : (Fintype.card (PrimeQuditRegisterLabel p Site) : ℂ) =
      (p : ℂ) ^ Fintype.card Site := by
    rw [show (Fintype.card (PrimeQuditRegisterLabel p Site) : ℂ) =
        (@Fintype.card (Site → ZMod p) Pi.instFintype : ℂ) by
      congr 1
      exact @Fintype.card_congr (PrimeQuditRegisterLabel p Site) (Site → ZMod p)
        (primeQuditRegisterLabelFintypeLocal p Site) Pi.instFintype
        (Equiv.refl (Site → ZMod p))]
    rw [Fintype.card_fun]
    norm_num [ZMod.card]
  rw [hcard]
  rw [← inv_pow]
  exact registerNorm_sq_mul_pow p

/-- The character ket `|+_e⟩ = Z(e) |+^n⟩` on a finite prime-qudit register. -/
def characterKet (e : PrimeQuditRegisterLabel p Site) : PrimeQuditRegister p Site :=
  zWordTransport p e (idealRegisterState p)

@[simp]
theorem characterKet_apply (e x : PrimeQuditRegisterLabel p Site) :
    characterKet p e x =
      (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
        phase p (registerPairing p e x) := by
  unfold characterKet
  rw [zWordTransport_apply]
  simp [idealRegisterState, registerPhase]
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
  ring

/-- The character kets are normalized physical register states. -/
theorem characterKet_inner_self (e : PrimeQuditRegisterLabel p Site) :
    inner ℂ (characterKet p e) (characterKet p e) = 1 := by
  rw [characterKet, (zWordTransport p e).map_inner, idealRegisterState_inner_self]

/-! ## The product-sum interchange over finite function types -/

/-- The last-element decomposition of a function on `Fin (n + 1)`. -/
def finSuccArrowEquiv (n : ℕ) (α : Type w) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f (Fin.last n), fun i => f i.castSucc)
  invFun p := Fin.snoc p.2 p.1
  left_inv f := by
    funext i
    by_cases hi : i = Fin.last n
    · subst hi
      simp
    · rw [show i = (i.castPred hi).castSucc by
        exact (Fin.castSucc_castPred i hi).symm]
      dsimp
      exact Fin.snoc_castSucc _ _ _
  right_inv p := by
    ext <;> simp

/-- The interchange of a finite product with a sum over functions. -/
private theorem Fintype_sum_fn_prod_fin {R : Type u} {α : Type w} [CommSemiring R] [Fintype α]
    (n : ℕ) (g : Fin n → α → R) :
    ∑ f : Fin n → α, ∏ i : Fin n, g i (f i) = ∏ i : Fin n, ∑ a : α, g i a := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ∑ f : Fin (n + 1) → α, ∏ i : Fin (n + 1), g i (f i) =
          ∑ f : Fin (n + 1) → α, g (Fin.last n) (f (Fin.last n)) *
            (∏ i : Fin n, g i.castSucc (f i.castSucc)) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [Fin.prod_univ_castSucc, mul_comm]
      _ = ∑ pair : α × (Fin n → α), g (Fin.last n) pair.1 *
            (∏ i : Fin n, g i.castSucc (pair.2 i)) := by
        rw [Fintype.sum_equiv (finSuccArrowEquiv n α)
          (fun f : Fin (n + 1) → α => g (Fin.last n) (f (Fin.last n)) *
            (∏ i : Fin n, g i.castSucc (f i.castSucc)))
          (fun pair : α × (Fin n → α) => g (Fin.last n) pair.1 *
            (∏ i : Fin n, g i.castSucc (pair.2 i)))]
        intro f
        rfl
      _ = (∑ a : α, g (Fin.last n) a) * (∏ i : Fin n, ∑ a : α, g i.castSucc a) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_congr rfl (fun a _ => by
          change (∑ y : Fin n → α, g (Fin.last n) a * (∏ i : Fin n, g i.castSucc (y i))) = _
          rw [← Finset.mul_sum])]
        rw [ih (fun i => g i.castSucc)]
        rw [← Finset.sum_mul]
      _ = ∏ i : Fin (n + 1), ∑ a : α, g i a := by
        rw [Fin.prod_univ_castSucc, mul_comm]

/-- The interchange of a finite product with a sum over functions on any finite type. -/
theorem Fintype_sum_fn_prod {R : Type u} {ι : Type v} {α : Type w} [CommSemiring R] [Fintype ι] [Fintype α]
    (g : ι → α → R) :
    ∑ f : ι → α, ∏ i : ι, g i (f i) = ∏ i : ι, ∑ a : α, g i a := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  rw [Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) (fun f => ∏ i : ι, g i (f i))
    (fun f => ∏ j : Fin (Fintype.card ι), g (e.symm j) (f j)) (by
      intro f
      rw [Fintype.prod_equiv e (fun i => g i (f i)) (fun j => g (e.symm j) (f (e.symm j)))]
      · rfl
      · intro i
        rw [Equiv.symm_apply_apply])]
  rw [Fintype_sum_fn_prod_fin (Fintype.card ι) (fun j => g (e.symm j))]
  rw [Fintype.prod_equiv e (fun i => ∑ a : α, g i a) (fun j => ∑ a : α, g (e.symm j) a)]
  intro i
  rw [Equiv.symm_apply_apply]

/-- The register-label universe agrees across equivalent `Fintype` instances. -/
theorem labelUniv_eq_piUniv :
    (@Finset.univ (PrimeQuditRegisterLabel p Site) (primeQuditRegisterLabelFintypeLocal p Site)) =
      (@Finset.univ (Site → ZMod p) Pi.instFintype) := by
  apply Finset.ext
  intro x
  simp

/-- Summing the character over all register labels separates the zero word. -/
theorem sum_register_phase (f : PrimeQuditRegisterLabel p Site) :
    ∑ x : PrimeQuditRegisterLabel p Site, phase p (registerPairing p f x) =
      if f = 0 then (p : ℂ) ^ Fintype.card Site else 0 := by
  calc
    ∑ x : PrimeQuditRegisterLabel p Site, phase p (registerPairing p f x) =
        ∑ x : PrimeQuditRegisterLabel p Site, ∏ site : Site, phase p (f site * x site) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [registerPairing]
      exact phase_finset_sum p Finset.univ (fun site => f site * x site)
    _ = ∏ site : Site, ∑ a : ZMod p, phase p (f site * a) := by
      rw [labelUniv_eq_piUniv]
      exact Fintype_sum_fn_prod (R := ℂ) (ι := Site) (α := ZMod p)
        (fun (site : Site) (a : ZMod p) => phase p (f site * a))
    _ = if f = 0 then (p : ℂ) ^ Fintype.card Site else 0 := by
      simp_rw [sum_phase_smul]
      by_cases hf : f = 0
      · subst f
        simp
      · have ⟨s, hs⟩ : ∃ site : Site, f site ≠ 0 := by
          by_contra h
          apply hf
          ext site
          by_contra hs'
          exact h ⟨site, hs'⟩
        rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs]), if_neg hf]

/-- The character kets form an orthonormal family. -/
theorem characterKet_inner (e f : PrimeQuditRegisterLabel p Site) :
    inner ℂ (characterKet p e) (characterKet p f) = if e = f then 1 else 0 := by
  rw [PiLp.inner_apply]
  have hpoint (x : PrimeQuditRegisterLabel p Site) :
      inner ℂ (characterKet p e x) (characterKet p f x) =
        ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            phase p (registerPairing p (f - e) x) := by
    rw [RCLike.inner_apply']
    simp only [characterKet_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal, phase_conj]
    rw [mul_mul_mul_comm]
    congr 1
    rw [← phase_add]
    congr 1
    simp [registerPairing, sub_mul, Finset.sum_sub_distrib]
    abel
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  rw [← Finset.mul_sum]
  rw [sum_register_phase p (f - e)]
  by_cases hef : e = f
  · subst f
    simp
    rw [← inv_pow]
    exact registerNorm_sq_mul_pow p
  · have hne : f - e ≠ 0 := by
      intro h
      exact hef (sub_eq_zero.mp h).symm
    simp [hef, hne]

/-- Summing the character-ket rank-one projectors recovers the register identity. -/
theorem sum_characterKet_rankOne_eq_one :
    (∑ e : PrimeQuditRegisterLabel p Site,
        (InnerProductSpace.rankOne ℂ (characterKet p e) (characterKet p e)).toLinearMap) = 1 := by
  apply LinearMap.ext
  intro psi
  ext x
  simp only [LinearMap.sum_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, PiLp.inner_apply, RCLike.inner_apply']
  rw [← PiLp.projₗ_apply (p := 2) (𝕜 := ℂ)
    (β := fun _ : PrimeQuditRegisterLabel p Site => ℂ) x]
  rw [map_sum]
  simp only [PiLp.projₗ_apply, PiLp.smul_apply, Module.End.one_apply]
  change (∑ e : PrimeQuditRegisterLabel p Site, (∑ y : PrimeQuditRegisterLabel p Site,
      starRingEnd ℂ (characterKet p e y) * psi y) * characterKet p e x) = psi x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hsummand (y : PrimeQuditRegisterLabel p Site) (e : PrimeQuditRegisterLabel p Site) :
      starRingEnd ℂ (phase p (registerPairing p e y)) * phase p (registerPairing p e x) =
        phase p (registerPairing p (x - y) e) := by
    rw [phase_conj, ← phase_add]
    congr 1
    simp only [registerPairing]
    rw [Finset.sum_congr rfl (fun site _ => mul_comm (e site) (y site))]
    rw [Finset.sum_congr rfl (fun site _ => mul_comm (e site) (x site))]
    conv_rhs =>
      rw [Finset.sum_congr rfl (fun site _ => by
        show (x - y) site * e site = x site * e site - y site * e site
        rw [Pi.sub_apply]
        exact sub_mul (x site) (y site) (e site))]
    rw [Finset.sum_sub_distrib]
    abel
  have hmain (y : PrimeQuditRegisterLabel p Site) :
      (∑ e : PrimeQuditRegisterLabel p Site, (starRingEnd ℂ (characterKet p e y) * psi y) *
          characterKet p e x) =
        psi y * (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
          ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            if y = x then (p : ℂ) ^ Fintype.card Site else 0) := by
    rw [Finset.sum_congr rfl (fun e _ => calc
      (starRingEnd ℂ (characterKet p e y) * psi y) * characterKet p e x =
          ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
              (psi y * (starRingEnd ℂ (phase p (registerPairing p e y)) *
                phase p (registerPairing p e x)))) := by
        simp only [characterKet_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal]
        ring
      _ = ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
            (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
              (psi y * phase p (registerPairing p (x - y) e))) := by
        rw [hsummand y e])]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [sum_register_phase p (x - y)]
    by_cases hyx : y = x
    · subst y
      simp
      ring
    · have hne : x - y ≠ 0 := by
        intro h
        exact hyx (sub_eq_zero.mp h).symm
      simp [hyx, hne]
  rw [Finset.sum_congr rfl (fun y _ => hmain y)]
  rw [Finset.sum_eq_single x]
  · rw [show (if x = x then (p : ℂ) ^ Fintype.card Site else 0) =
          (p : ℂ) ^ Fintype.card Site by simp]
    rw [show (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
        (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
          (p : ℂ) ^ Fintype.card Site = 1 by
      exact registerNorm_sq_mul_pow p]
    simp
  · intro y _ hyx
    simp [hyx]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim

/-! ## The sitewise magic register ket -/

/-- The sitewise magic register ket `|M_e⟩ = Z(e) U_{1,3}^{⊗ n} |+^n⟩`. -/
def magicRegisterKet (e : PrimeQuditRegisterLabel p Site) : PrimeQuditRegister p Site :=
  zWordTransport p e (physicalU13 p (idealRegisterState p))

@[simp]
theorem magicRegisterKet_apply (e x : PrimeQuditRegisterLabel p Site) :
    magicRegisterKet p e x =
      (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
        phase p (registerPairing p e x + cubicExponent p x) := by
  unfold magicRegisterKet
  rw [zWordTransport_apply, physicalU13_apply_phase]
  simp [idealRegisterState, registerPhase]
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
  rw [phase_add]
  ring

/-- The inverse physical cubic applies the negated cubic phase. -/
@[simp]
theorem physicalU13_symm_apply_phase (psi : PrimeQuditRegister p Site)
    (x : PrimeQuditRegisterLabel p Site) :
    (physicalU13 p).symm psi x = phase p (-cubicExponent p x) * psi x := by
  have hleft : ∀ x : PrimeQuditRegisterLabel p Site,
      phase p (cubicExponent p x) * phase p (-cubicExponent p x) = 1 := by
    intro x
    rw [← phase_add, add_neg_cancel, phase_zero]
  have hright : ∀ x : PrimeQuditRegisterLabel p Site,
      phase p (-cubicExponent p x) * phase p (cubicExponent p x) = 1 := by
    intro x
    rw [← phase_add, neg_add_cancel, phase_zero]
  have htrans (psi : PrimeQuditRegister p Site) :
      (physicalU13 p) (diagonalLinearEquiv (fun y => phase p (-cubicExponent p y))
        (fun y => phase p (cubicExponent p y)) hleft hright psi) = psi := by
    ext y
    rw [physicalU13_apply_phase]
    unfold diagonalLinearEquiv
    change phase p (cubicExponent p y) *
      ((diagonalOperator (fun z : PrimeQuditRegisterLabel p Site =>
        phase p (-cubicExponent p z))) psi) y = psi y
    rw [diagonalOperator_apply]
    rw [← mul_assoc, ← phase_add, add_neg_cancel, phase_zero]
    simp
  have hvec : (physicalU13 p).symm psi = diagonalLinearEquiv
      (fun y => phase p (-cubicExponent p y)) (fun y => phase p (cubicExponent p y))
      hleft hright psi := by
    apply (physicalU13 p).toLinearEquiv.injective
    rw [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
    exact (htrans psi).symm
  rw [hvec]
  unfold diagonalLinearEquiv
  change ((diagonalOperator (fun z : PrimeQuditRegisterLabel p Site =>
    phase p (-cubicExponent p z))) psi) x = phase p (-cubicExponent p x) * psi x
  rw [diagonalOperator_apply]

/-- The inverse physical cubic transports the magic register ket to its character ket. -/
theorem physicalU13_symm_magicRegisterKet (e : PrimeQuditRegisterLabel p Site) :
    (physicalU13 p).symm (magicRegisterKet p e) = characterKet p e := by
  ext x
  rw [physicalU13_symm_apply_phase, magicRegisterKet_apply, characterKet_apply]
  rw [← mul_assoc, mul_comm _ ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site)]
  rw [mul_assoc, ← phase_add]
  rw [show -cubicExponent p x + (registerPairing p e x + cubicExponent p x) =
      registerPairing p e x by abel]

/-- Every magic register ket is normalized. -/
theorem magicRegisterKet_inner_self (e : PrimeQuditRegisterLabel p Site) :
    inner ℂ (magicRegisterKet p e) (magicRegisterKet p e) = 1 := by
  rw [magicRegisterKet, (zWordTransport p e).map_inner, (physicalU13 p).map_inner,
    idealRegisterState_inner_self]

/-- Applying the physical cubic transport to a character ket recovers its
corresponding magic-register ket. -/
theorem physicalU13_characterKet (e : PrimeQuditRegisterLabel p Site) :
    physicalU13 p (characterKet p e) = magicRegisterKet p e := by
  rw [← physicalU13_symm_magicRegisterKet p e]
  exact (physicalU13 p).toLinearEquiv.apply_symm_apply (magicRegisterKet p e)

/-- The magic-register kets are an orthonormal basis, obtained by applying
the physical cubic unitary to the character basis. -/
theorem magicRegisterKet_inner (e f : PrimeQuditRegisterLabel p Site) :
    inner ℂ (magicRegisterKet p e) (magicRegisterKet p f) =
      if e = f then 1 else 0 := by
  calc
    inner ℂ (magicRegisterKet p e) (magicRegisterKet p f) =
        inner ℂ ((physicalU13 p).symm (magicRegisterKet p e))
          ((physicalU13 p).symm (magicRegisterKet p f)) :=
      ((physicalU13 p).symm.map_inner _ _).symm
    _ = if e = f then 1 else 0 := by
      simpa only [physicalU13_symm_magicRegisterKet] using characterKet_inner p e f

/-- Summing all magic-register rank-one projectors gives the identity on the
actual finite register. -/
theorem sum_magicRegisterKet_rankOne_eq_one :
    (∑ e : PrimeQuditRegisterLabel p Site,
        (InnerProductSpace.rankOne ℂ (magicRegisterKet p e)
          (magicRegisterKet p e)).toLinearMap) = 1 := by
  calc
    (∑ e : PrimeQuditRegisterLabel p Site,
        (InnerProductSpace.rankOne ℂ (magicRegisterKet p e)
          (magicRegisterKet p e)).toLinearMap) =
        ∑ e : PrimeQuditRegisterLabel p Site,
          (physicalU13 p).conjOperator
            (InnerProductSpace.rankOne ℂ (characterKet p e)
              (characterKet p e)).toLinearMap := by
      apply Finset.sum_congr rfl
      intro e _
      rw [QuditSubsystem.conjOperator_rankOne, physicalU13_characterKet]
    _ = (physicalU13 p).conjOperator
        (∑ e : PrimeQuditRegisterLabel p Site,
          (InnerProductSpace.rankOne ℂ (characterKet p e)
            (characterKet p e)).toLinearMap) := by
      rw [← (physicalU13 p).conjOperatorLinearMap_apply, map_sum]
      rfl
    _ = 1 := by
      rw [sum_characterKet_rankOne_eq_one, (physicalU13 p).conjOperator_one]

/-- The complete projective readout of the actual finite magic-register
basis.  It is used to define output label distributions operationally. -/
def magicRegisterKrausFamily :
    FiniteKrausFamily (PrimeQuditRegisterLabel p Site)
      (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  operator e :=
    (InnerProductSpace.rankOne ℂ (magicRegisterKet p e)
      (magicRegisterKet p e)).toLinearMap

theorem magicRegisterKrausFamily_complete :
    (magicRegisterKrausFamily p (Site := Site)).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [magicRegisterKrausFamily]
  rw [Finset.sum_congr rfl (fun e _ =>
    rankOne_adjoint_comp_eq (magicRegisterKet p e)
      (magicRegisterKet_inner_self p e))]
  exact sum_magicRegisterKet_rankOne_eq_one p

/-- The same magic-register measurement with its label retained as the
observable finite outcome. -/
def magicRegisterInstrument :
    FiniteInstrument (PrimeQuditRegisterLabel p Site)
      (PrimeQuditRegisterLabel p Site)
      (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  kraus := magicRegisterKrausFamily p
  observe := id

theorem magicRegisterInstrument_complete :
    (magicRegisterInstrument p (Site := Site)).kraus.Complete :=
  magicRegisterKrausFamily_complete p

/-! ## The IID magic register resource -/

/-- The IID product weight of one register error word. -/
def wordProbability (mu : ZMod p → ℝ) (e : PrimeQuditRegisterLabel p Site) : ℝ :=
  ∏ site : Site, mu (e site)

/-- Product weights of nonnegative per-site distributions are nonnegative. -/
theorem wordProbability_nonneg (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (e : PrimeQuditRegisterLabel p Site) :
    0 ≤ wordProbability p mu e := by
  unfold wordProbability
  exact Finset.prod_nonneg (fun site _ => hmu_nonneg (e site))

/-- The IID product weights of a normalized per-site distribution sum to one. -/
theorem sum_wordProbability_eq_one (mu : ZMod p → ℝ)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    ∑ e : PrimeQuditRegisterLabel p Site, wordProbability p mu e = 1 := by
  change (∑ e : Site → ZMod p, ∏ site : Site, mu (e site)) = 1
  rw [labelUniv_eq_piUniv]
  rw [Fintype_sum_fn_prod (R := ℝ) (ι := Site) (α := ZMod p)
    (fun (site : Site) (a : ZMod p) => mu a)]
  rw [hmu_sum]
  simp

/-- The IID magic register resource: the raw convex reconstruction of the
p-dependent magic-basis-diagonal tensor-power input (no twirl needed). -/
def magicRegisterResource (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DensityOperator (PrimeQuditRegister p Site) :=
  DensityOperator.convexCombination Finset.univ (wordProbability p mu)
    (fun e => DensityOperator.pureDensity (magicRegisterKet p e) (by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), magicRegisterKet_inner_self]
      norm_num))
    (fun e _ => wordProbability_nonneg p mu hmu_nonneg e)
    (sum_wordProbability_eq_one p mu hmu_sum)

/-- The mass placed by one per-site distribution on its nonzero labels. -/
def nonzeroMass (mu : ZMod p → ℝ) : ℝ :=
  ∑ a : ZMod p, if a = 0 then 0 else mu a

/-- For a normalized one-site distribution, the total nonzero-label mass is
exactly the complement of its zero-label mass. -/
theorem nonzeroMass_eq_one_sub_mu_zero (mu : ZMod p → ℝ)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    nonzeroMass p mu = 1 - mu 0 := by
  have hsum0 : (∑ b : ZMod p, if b = 0 then mu 0 else 0) = mu 0 := by
    simp
  have hsumAll :
      (∑ b : ZMod p, ((if b = 0 then 0 else mu b) + if b = 0 then mu 0 else 0)) =
        ∑ b : ZMod p, mu b := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b = 0 <;> simp [hb]
  have hsum' : (∑ b : ZMod p, if b = 0 then 0 else mu b) + mu 0 =
      ∑ b : ZMod p, mu b := by
    rw [← hsum0, ← Finset.sum_add_distrib, hsumAll]
  unfold nonzeroMass
  rw [hmu_sum] at hsum'
  linarith

/-- At rate `eps` (mass `1-eps` on zero), every nonzero label carries at most `eps`. -/
theorem mu_nonzero_le (mu : ZMod p → ℝ) (eps : ℝ)
    (hmu0 : mu 0 = 1 - eps) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (a : ZMod p) (ha : a ≠ 0) :
    mu a ≤ eps := by
  have hsum0 : (∑ b : ZMod p, if b = 0 then mu 0 else 0) = mu 0 := by simp
  have hsumAll :
      (∑ b : ZMod p, ((if b = 0 then 0 else mu b) + if b = 0 then mu 0 else 0)) =
        ∑ b : ZMod p, mu b := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b = 0 <;> simp [hb]
  have hsum' : (∑ b : ZMod p, if b = 0 then 0 else mu b) + mu 0 =
      ∑ b : ZMod p, mu b := by
    rw [← hsum0, ← Finset.sum_add_distrib, hsumAll]
  have hsum_nonzero : (∑ b : ZMod p, if b = 0 then 0 else mu b) = eps := by
    rw [hmu_sum] at hsum'
    rw [hmu0] at hsum'
    linarith
  have hle : mu a ≤ ∑ b : ZMod p, if b = 0 then 0 else mu b := by
    calc
      mu a = ∑ b : ZMod p, if b = a then (if b = 0 then 0 else mu b) else 0 := by
        simp [ha]
      _ ≤ ∑ b : ZMod p, if b = 0 then 0 else mu b := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hba : b = a
        · by_cases hb : b = 0
          · simp [hba]
          · simp [hba]
        · by_cases hb : b = 0
          · simp [hb]
          · simp [hba, hb, hmu_nonneg b]
  exact hle.trans_eq hsum_nonzero

end KT19PrimeQuditCSS

end QEC.Distillation.KT19MagicResource
