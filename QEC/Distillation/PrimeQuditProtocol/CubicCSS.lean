import QEC.Distillation.Core.TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Prime-qudit cubic CSS semantics for KT19

This module is intentionally independent of the binary triorthogonal route.
It uses the standard additive character of `ZMod p`, and its CSS input records
the complete (including repeated-index) cubic orthogonality condition.
-/

noncomputable section

namespace QEC.Distillation.KT19PrimeQuditCSS

open Semantics
open scoped BigOperators

universe u

/-- A computational-basis qudit whose labels are elements of `ZMod p`. -/
abbrev PrimeQudit (p : Nat) [NeZero p] : Type :=
  EuclideanSpace Complex (ZMod p)

/-- Labels for a finite prime-qudit register. -/
abbrev PrimeQuditRegisterLabel (p : Nat) (Site : Type u) : Type u :=
  Site → ZMod p

/-- Canonical finite enumeration of prime-field labels on any finite register. -/
noncomputable local instance primeQuditRegisterLabelFintype (p : Nat) [NeZero p]
    (Site : Type u) [Fintype Site] : Fintype (PrimeQuditRegisterLabel p Site) :=
  Fintype.ofFinite _

/-- A finite register of `p`-dimensional qudits. -/
abbrev PrimeQuditRegister (p : Nat) (Site : Type u) [NeZero p] : Type u :=
  EuclideanSpace Complex (PrimeQuditRegisterLabel p Site)

/-- The computational ket with the supplied prime-qudit label. -/
def quditBasisKet (p : Nat) [NeZero p] (x : ZMod p) : PrimeQudit p :=
  EuclideanSpace.basisFun (ZMod p) Complex x

/-- The computational ket of a labelled finite prime-qudit register. -/
def registerBasisKet (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (x : PrimeQuditRegisterLabel p Site) : PrimeQuditRegister p Site :=
  EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex x

/-- The primitive `p`-th root of unity fixed by the actual `ZMod p` additive character. -/
def phase (p : Nat) [NeZero p] (x : ZMod p) : Complex :=
  ZMod.stdAddChar x

@[simp]
theorem phase_zero (p : Nat) [NeZero p] : phase p 0 = 1 :=
  (ZMod.stdAddChar (N := p)).map_zero_eq_one

theorem phase_add (p : Nat) [NeZero p] (x y : ZMod p) :
    phase p (x + y) = phase p x * phase p y :=
  (ZMod.stdAddChar (N := p)).map_add_eq_mul x y

theorem phase_neg (p : Nat) [NeZero p] (x : ZMod p) :
    phase p (-x) = (phase p x)⁻¹ :=
  (ZMod.stdAddChar (N := p)).map_neg_eq_inv x

/-- Complex conjugation reverses the `ZMod p` additive character. -/
theorem phase_conj (p : Nat) [NeZero p] (x : ZMod p) :
    starRingEnd Complex (phase p x) = phase p (-x) := by
  simpa [phase] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) x).symm

/-- The actual root of unity has order dividing its nonzero modulus. -/
theorem phase_natCast_modulus (p : Nat) [NeZero p] : phase p (p : ZMod p) = 1 := by
  simpa using phase_zero p

/-- The unit-modulus identity needed by all diagonal prime-qudit phases. -/
theorem phase_mul_conj (p : Nat) [NeZero p] (x : ZMod p) :
    phase p x * starRingEnd Complex (phase p x) = 1 := by
  rw [phase_conj, ← phase_add, add_neg_cancel, phase_zero]

/-- The additive character turns every finite sum of field exponents into a product of phases. -/
theorem phase_finset_sum (p : Nat) [NeZero p] {Index : Type u}
    (indices : Finset Index) (f : Index → ZMod p) :
    phase p (∑ index ∈ indices, f index) = ∏ index ∈ indices, phase p (f index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [phase_zero]
  | insert index indices hindex ih =>
      simp only [Finset.sum_insert, hindex, not_false_eq_true, Finset.prod_insert, phase_add, ih]

/-- Finite products of the canonical phase are equivalently one phase at the summed exponent. -/
theorem phase_fintype_sum (p : Nat) [NeZero p] {Index : Type u} [Fintype Index]
    (f : Index → ZMod p) :
    (∏ index : Index, phase p (f index)) = phase p (∑ index : Index, f index) :=
  (phase_finset_sum p Finset.univ f).symm

/-- The single-qudit `Z` phase, defined by the canonical `ZMod p` character. -/
def zAmplitude (p : Nat) [NeZero p] (x : ZMod p) : Complex := phase p x

/-- The cubic `U_{1,3}` phase on one prime-qudit computational label. -/
def u13Amplitude (p : Nat) [NeZero p] (x : ZMod p) : Complex := phase p (x ^ 3)

theorem u13Amplitude_mul_conj (p : Nat) [NeZero p] (x : ZMod p) :
    u13Amplitude p x * starRingEnd Complex (u13Amplitude p x) = 1 :=
  phase_mul_conj p (x ^ 3)

/-- Pointwise multiplication by an arbitrary unit-modulus diagonal amplitude. -/
def diagonalOperator {Label : Type u} [Fintype Label] (amplitude : Label → Complex) :
    Operator (EuclideanSpace Complex Label) where
  toFun psi := WithLp.toLp 2 fun label => amplitude label * psi label
  map_add' := by
    intro psi chi
    ext label
    change amplitude label * (psi label + chi label) =
      amplitude label * psi label + amplitude label * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change amplitude label * (scalar * psi label) = scalar * (amplitude label * psi label)
    ring

@[simp]
theorem diagonalOperator_apply {Label : Type u} [Fintype Label]
    (amplitude : Label → Complex) (psi : EuclideanSpace Complex Label) (label : Label) :
    diagonalOperator amplitude psi label = amplitude label * psi label :=
  rfl

theorem diagonalOperator_map_inner {Label : Type u} [Fintype Label]
    (amplitude : Label → Complex)
    (hunit : ∀ label, amplitude label * starRingEnd Complex (amplitude label) = 1)
    (psi chi : EuclideanSpace Complex Label) :
    inner Complex (diagonalOperator amplitude psi) (diagonalOperator amplitude chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [diagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (amplitude label * chi label) *
        (starRingEnd Complex (amplitude label) * starRingEnd Complex (psi label)) =
        (amplitude label * starRingEnd Complex (amplitude label)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by rw [hunit]; ring

/-- A diagonal map together with its explicitly supplied inverse amplitude. -/
noncomputable def diagonalLinearEquiv {Label : Type u} [Fintype Label]
    (amplitude inverseAmplitude : Label → Complex)
    (hleft : ∀ label, inverseAmplitude label * amplitude label = 1)
    (hright : ∀ label, amplitude label * inverseAmplitude label = 1) :
    EuclideanSpace Complex Label ≃ₗ[Complex] EuclideanSpace Complex Label where
  toFun := diagonalOperator amplitude
  invFun := diagonalOperator inverseAmplitude
  left_inv := by
    intro psi
    ext label
    simp only [diagonalOperator_apply]
    rw [← mul_assoc, hleft]
    simp
  right_inv := by
    intro psi
    ext label
    simp only [diagonalOperator_apply]
    rw [← mul_assoc, hright]
    simp
  map_add' := (diagonalOperator amplitude).map_add
  map_smul' := (diagonalOperator amplitude).map_smul

/-- The single-qudit generalized `Z` transport. -/
noncomputable def zTransport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := diagonalLinearEquiv (zAmplitude p) (fun x => phase p (-x))
    (by
      intro x
      change phase p (-x) * phase p x = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p x * phase p (-x) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (zAmplitude p) (phase_mul_conj p)

@[simp]
theorem zTransport_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    zTransport p psi x = zAmplitude p x * psi x :=
  rfl

/-- Generalized Z applies the canonical p-phase to a computational ket. -/
theorem zTransport_apply_basis (p : Nat) [NeZero p] (x : ZMod p) :
    zTransport p (quditBasisKet p x) = zAmplitude p x • quditBasisKet p x := by
  classical
  ext label
  rw [zTransport_apply]
  by_cases hlabel : label = x
  · subst label
    simp [quditBasisKet, EuclideanSpace.basisFun_apply]
  · simp [quditBasisKet, EuclideanSpace.basisFun_apply, hlabel]

/-- The actual generalized-X permutation of computational labels. -/
def xLabelEquiv (p : Nat) [NeZero p] : ZMod p ≃ ZMod p where
  toFun x := x + 1
  invFun x := x - 1
  left_inv x := by ring
  right_inv x := by ring

/-- Generalized X as the finite Hilbert-space transport induced by label addition by one. -/
noncomputable def xLinearIsometry (p : Nat) [NeZero p] :
    PrimeQudit p ≃ₗᵢ[Complex] PrimeQudit p :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (xLabelEquiv p)

/-- The generalized-X unitary transport. -/
noncomputable def xTransport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := (xLinearIsometry p).toLinearEquiv
  map_inner := fun psi chi => (xLinearIsometry p).inner_map_map psi chi

@[simp]
theorem xTransport_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    xTransport p psi x = psi (x - 1) :=
  rfl

/-- Generalized X shifts a computational ket by one field element. -/
theorem xTransport_apply_basis (p : Nat) [NeZero p] (x : ZMod p) :
    xTransport p (quditBasisKet p x) = quditBasisKet p (x + 1) := by
  classical
  ext target
  by_cases htarget : target = x + 1
  · subst target
    simp [xTransport_apply, quditBasisKet, EuclideanSpace.basisFun_apply]
  · have htarget' : target - 1 ≠ x := by
      intro h
      apply htarget
      calc
        target = (target - 1) + 1 := by ring
        _ = x + 1 := by rw [h]
    simp [xTransport_apply, quditBasisKet, EuclideanSpace.basisFun_apply, htarget, htarget']

/-- The single-qudit cubic `U_{1,3}` transport. -/
noncomputable def u13Transport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := diagonalLinearEquiv (u13Amplitude p) (fun x => phase p (-(x ^ 3)))
    (by
      intro x
      change phase p (-(x ^ 3)) * phase p (x ^ 3) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p (x ^ 3) * phase p (-(x ^ 3)) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (u13Amplitude p) (u13Amplitude_mul_conj p)

@[simp]
theorem u13Transport_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    u13Transport p psi x = u13Amplitude p x * psi x :=
  rfl

@[simp]
theorem u13Transport_symm_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    (u13Transport p).symm psi x = phase p (-(x ^ 3)) * psi x :=
  rfl

/-- The inverse cubic transport has the negative cubic phase on a basis ket. -/
theorem u13Transport_symm_apply_basis (p : Nat) [NeZero p] (x : ZMod p) :
    (u13Transport p).symm (quditBasisKet p x) =
      phase p (-(x ^ 3)) • quditBasisKet p x := by
  classical
  ext label
  rw [u13Transport_symm_apply]
  by_cases hlabel : label = x
  · subst label
    simp [quditBasisKet, EuclideanSpace.basisFun_apply]
  · simp [quditBasisKet, EuclideanSpace.basisFun_apply, hlabel]

/-- The computational-basis cubic action of `U_{1,3}`. -/
theorem u13Transport_apply_basis (p : Nat) [NeZero p] (x : ZMod p) :
    u13Transport p (quditBasisKet p x) =
      u13Amplitude p x • quditBasisKet p x := by
  classical
  ext label
  by_cases hlabel : label = x
  · subst label
    simp [u13Transport_apply, quditBasisKet, EuclideanSpace.basisFun_apply]
  · simp [u13Transport_apply, quditBasisKet, EuclideanSpace.basisFun_apply, hlabel]

/-- A modulus used by the KT19 prime-qudit route: prime and at least five. -/
structure PrimeAtLeastFive (p : Nat) : Prop where
  prime : Nat.Prime p
  five_le : 5 ≤ p

/-- The p-dependent ideal `U_{1,3}` magic resource: `U_{1,3}|+⟩`. -/
def idealU13Resource (p : Nat) [NeZero p] : PrimeQudit p :=
  u13Transport p
    ((Real.sqrt (p : Real) : Complex)⁻¹ • ∑ x : ZMod p, quditBasisKet p x)

/-- The p-dependent ideal cubic resource is a normalized physical state. -/
theorem idealU13Resource_inner_self (p : Nat) [NeZero p] :
    inner Complex (idealU13Resource p) (idealU13Resource p) = 1 := by
  rw [idealU13Resource, (u13Transport p).map_inner]
  rw [inner_smul_left, inner_smul_right, inner_sum]
  simp_rw [sum_inner]
  simp only [quditBasisKet, EuclideanSpace.basisFun_apply]
  simp_rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]
  have hpos : (0 : Real) < (p : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hsqrt : (Real.sqrt (p : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  have hsquare :
      (Real.sqrt (p : Real) : Complex) * (Real.sqrt (p : Real) : Complex) =
        (p : Complex) := by
    exact_mod_cast Real.mul_self_sqrt hpos.le
  rw [← hsquare]
  field_simp [hsqrt]

/-- The cubic finite-difference exponent produced by conjugating generalized X. -/
def u13ConjugatedXExponent (p : Nat) [NeZero p] (x : ZMod p) : ZMod p :=
  (x + 1) ^ 3 - x ^ 3

/-- The quadratic phase produced when `U_{1,3}` conjugates generalized X. -/
def u13ConjugatedXAmplitude (p : Nat) [NeZero p] (x : ZMod p) : Complex :=
  phase p (u13ConjugatedXExponent p x)

/-- A generalized Z power, with an explicitly displayed linear phase exponent. -/
def zPowerAmplitude (p : Nat) [NeZero p] (slope x : ZMod p) : Complex :=
  phase p (slope * x)

/-- The actual generalized-Pauli Z-power transport. -/
noncomputable def zPowerTransport (p : Nat) [NeZero p] (slope : ZMod p) :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := diagonalLinearEquiv (zPowerAmplitude p slope)
    (fun x => phase p (-(slope * x)))
    (by
      intro x
      change phase p (-(slope * x)) * phase p (slope * x) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p (slope * x) * phase p (-(slope * x)) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (zPowerAmplitude p slope)
    (fun x => phase_mul_conj p (slope * x))

@[simp]
theorem zPowerTransport_apply (p : Nat) [NeZero p] (slope : ZMod p)
    (psi : PrimeQudit p) (x : ZMod p) :
    zPowerTransport p slope psi x = zPowerAmplitude p slope x * psi x :=
  rfl

/-- A generalized Z power applies its linear phase to a computational ket. -/
theorem zPowerTransport_apply_basis (p : Nat) [NeZero p] (slope x : ZMod p) :
    zPowerTransport p slope (quditBasisKet p x) =
      zPowerAmplitude p slope x • quditBasisKet p x := by
  classical
  ext label
  rw [zPowerTransport_apply]
  by_cases hlabel : label = x
  · subst label
    simp [quditBasisKet, EuclideanSpace.basisFun_apply]
  · simp [quditBasisKet, EuclideanSpace.basisFun_apply, hlabel]

/-- The cubic finite difference is visibly a quadratic polynomial. -/
theorem u13ConjugatedXExponent_eq_quadratic (p : Nat) [NeZero p] (x : ZMod p) :
    u13ConjugatedXExponent p x = 3 * x ^ 2 + 3 * x + 1 := by
  unfold u13ConjugatedXExponent
  ring

/-- The finite difference of the conjugated-X quadratic phase is linear. -/
theorem u13ConjugatedXExponent_firstDifference (p : Nat) [NeZero p] (x : ZMod p) :
    u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x = 6 * x + 6 := by
  unfold u13ConjugatedXExponent
  ring

/-- A KT19 prime modulus makes the resulting Pauli Z-power genuinely nontrivial. -/
theorem six_ne_zero (p : Nat) [NeZero p] (hp : PrimeAtLeastFive p) :
    (6 : ZMod p) ≠ 0 := by
  intro hzero
  have hfive : 5 ≤ p := hp.five_le
  have hp_dvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp (by simpa using hzero)
  rw [show 6 = 2 * 3 by norm_num] at hp_dvd
  rcases hp.prime.dvd_mul.mp hp_dvd with hp_two | hp_three
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_two
    omega
  · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp_three
    omega

/-- The next finite difference is, up to a global phase, the actual Pauli Z power. -/
theorem u13ConjugatedX_firstDifference_is_pauli (p : Nat) [NeZero p] (x : ZMod p) :
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) =
      phase p 6 * zPowerAmplitude p 6 x := by
  rw [u13ConjugatedXExponent_firstDifference]
  change phase p (6 * x + 6) = phase p 6 * phase p (6 * x)
  rw [phase_add, mul_comm]

/-- The linear finite difference acts as a global phase times the actual Pauli Z power. -/
theorem u13ConjugatedX_firstDifference_is_pauli_on_basis (p : Nat) [NeZero p]
    (x : ZMod p) :
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) •
        quditBasisKet p x =
      phase p 6 • zPowerTransport p 6 (quditBasisKet p x) := by
  rw [zPowerTransport_apply_basis, smul_smul,
    u13ConjugatedX_firstDifference_is_pauli]

/-- The prime-qudit hierarchy witness: cubic U13 has quadratic X conjugation whose
next finite difference is a nontrivial linear generalized-Pauli phase. -/
structure U13HierarchyWitness (p : Nat) [NeZero p] : Prop where
  quadratic_conjugatedX : ∀ x : ZMod p,
    u13ConjugatedXExponent p x = 3 * x ^ 2 + 3 * x + 1
  pauli_firstDifference : ∀ x : ZMod p,
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) =
      phase p 6 * zPowerAmplitude p 6 x
  pauli_firstDifference_on_basis : ∀ x : ZMod p,
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) •
        quditBasisKet p x =
      phase p 6 • zPowerTransport p 6 (quditBasisKet p x)
  pauli_slope_ne_zero : (6 : ZMod p) ≠ 0

/-- The p>=5 route has a concrete cubic-to-quadratic-to-Pauli hierarchy witness. -/
theorem u13_has_hierarchy (p : Nat) [NeZero p] (hp : PrimeAtLeastFive p) :
    U13HierarchyWitness p :=
  ⟨u13ConjugatedXExponent_eq_quadratic p,
    u13ConjugatedX_firstDifference_is_pauli p,
    u13ConjugatedX_firstDifference_is_pauli_on_basis p, six_ne_zero p hp⟩

/-- The explicit third-level conjugation identity used by the prime-qudit route. -/
theorem u13_conjugates_x_on_basis (p : Nat) [NeZero p]
    (hp : PrimeAtLeastFive p) (x : ZMod p) :
    u13Transport p (xTransport p ((u13Transport p).symm (quditBasisKet p x))) =
      u13ConjugatedXAmplitude p x • quditBasisKet p (x + 1) := by
  have hp_nonzero : p ≠ 0 := hp.prime.ne_zero
  rw [u13Transport_symm_apply_basis,
    map_smul, xTransport_apply_basis, map_smul, u13Transport_apply_basis]
  unfold u13ConjugatedXAmplitude
  rw [smul_smul]
  change (phase p (-(x ^ 3)) * phase p ((x + 1) ^ 3)) • quditBasisKet p (x + 1) =
    phase p ((x + 1) ^ 3 - x ^ 3) • quditBasisKet p (x + 1)
  congr 1
  rw [← phase_add]
  ring

/-- Canonically enumerate a finite set of physical prime-qudit sites. -/
noncomputable def siteEquivFin (Site : Type u) [Fintype Site] :
    Fin (Fintype.card Site) ≃ Site :=
  (Fintype.equivFin Site).symm

/-- The literal singleton support of one physical prime-qudit site. -/
def coordinateSupport {Site : Type u} [DecidableEq Site] (site : Site) : Finset Site :=
  {site}

@[simp]
theorem coordinateSupport_card {Site : Type u} [DecidableEq Site] (site : Site) :
    (coordinateSupport site).card = 1 := by simp [coordinateSupport]

theorem coordinateSupport_disjoint {Site : Type u} [DecidableEq Site]
    {first second : Site} (hne : first ≠ second) :
    Disjoint (coordinateSupport first) (coordinateSupport second) := by
  simpa [coordinateSupport] using (Finset.disjoint_singleton.mpr hne)

/-- The phase contribution from one physical site of a prime-qudit register. -/
def u13AtAmplitude (p : Nat) [NeZero p] {Site : Type u}
    (site : Site) (label : PrimeQuditRegisterLabel p Site) : Complex :=
  u13Amplitude p (label site)

/-- `U_{1,3}` acting at one literal physical site and as identity elsewhere. -/
noncomputable def u13AtTransport (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (site : Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  toLinearEquiv := diagonalLinearEquiv (u13AtAmplitude p site)
    (fun label => phase p (-(label site ^ 3)))
    (by
      intro label
      change phase p (-(label site ^ 3)) * phase p (label site ^ 3) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro label
      change phase p (label site ^ 3) * phase p (-(label site ^ 3)) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (u13AtAmplitude p site)
    (fun label => u13Amplitude_mul_conj p (label site))

@[simp]
theorem u13AtTransport_apply (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (site : Site)
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    u13AtTransport p site psi label = u13AtAmplitude p site label * psi label :=
  rfl

/-- The physical tensor product of the source-prescribed local `U_{1,3}` gates. -/
noncomputable def physicalU13 (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card Site) =>
    u13AtTransport p (siteEquivFin Site j)

private theorem composeU13AtTransports_apply (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (sites : List Site)
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    UnitaryTransport.composeList (sites.map (u13AtTransport p)) psi label =
      (sites.map fun site => u13AtAmplitude p site label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons site sites ih =>
      change UnitaryTransport.composeList (sites.map (u13AtTransport p))
          (u13AtTransport p site psi) label = _
      rw [ih]
      simp only [u13AtTransport_apply, List.map_cons, List.prod_cons]
      ring

/-- The physical tensor product has the product of the literal local cubic phases. -/
theorem physicalU13_apply (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p psi label =
      (∏ site : Site, u13AtAmplitude p site label) * psi label := by
  rw [physicalU13, UnitaryTransport.composeFamily]
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card Site) =>
        u13AtTransport p (siteEquivFin Site j)) =
        (List.ofFn (siteEquivFin Site)).map (u13AtTransport p) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, composeU13AtTransports_apply]
  rw [List.map_ofFn, Fin.prod_ofFn]
  congr 1
  exact Fintype.prod_equiv (siteEquivFin Site) _ _ (fun _ => rfl)

/-- The physical product has the stated cubic action on every register basis ket. -/
theorem physicalU13_apply_basis (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p (registerBasisKet p label) =
      (∏ site : Site, u13AtAmplitude p site label) • registerBasisKet p label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [physicalU13_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [physicalU13_apply, registerBasisKet, EuclideanSpace.basisFun_apply, htarget]

/-- The cubic field exponent accumulated by a computational-basis register label. -/
def cubicExponent (p : Nat) [NeZero p] {Site : Type u} [Fintype Site]
    (label : PrimeQuditRegisterLabel p Site) : ZMod p :=
  ∑ site : Site, label site ^ 3

/-- The physical product acts by the canonical phase of the complete cubic exponent. -/
theorem physicalU13_apply_phase (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p psi label = phase p (cubicExponent p label) * psi label := by
  rw [physicalU13_apply]
  change (∏ site : Site, phase p (label site ^ 3)) * psi label = _
  rw [phase_fintype_sum]
  rfl

/-- The physical product has its cubic-exponent phase on every computational ket. -/
theorem physicalU13_apply_basis_phase (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p (registerBasisKet p label) =
      phase p (cubicExponent p label) • registerBasisKet p label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [physicalU13_apply_phase, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [physicalU13_apply_phase, registerBasisKet, EuclideanSpace.basisFun_apply, htarget]

/-- The only allowed local physical gate is `U_{1,3}` on its displayed singleton support. -/
inductive U13LocalGate (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] : Finset Site → Type u
  | at (site : Site) : U13LocalGate p (coordinateSupport site)

/-- The literal support-indexed physical model for local prime-qudit cubic gates. -/
noncomputable def physicalU13GateModel (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] :
    FinitePhysicalGateModel Site (PrimeQuditRegister p Site) where
  LocalGate := U13LocalGate p
  realize gate := match gate with
    | .at site => u13AtTransport p site

/-- The physical cubic product factors over disjoint singleton physical sites. -/
noncomputable def physicalU13SitewiseFactorization (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] :
    SitewiseTransversalityData (physicalU13GateModel p (Site := Site)) (physicalU13 p) where
  factorCount := Fintype.card Site
  support j := coordinateSupport (siteEquivFin Site j)
  factor j := .at (siteEquivFin Site j)
  pairwise_disjoint := by
    intro i j hij
    exact coordinateSupport_disjoint ((siteEquivFin Site).injective.ne hij)
  realizes := rfl
  support_card_le_one := by
    intro j
    simp [coordinateSupport_card]

/-- The coordinatewise cubic pairing of three finite-field words. -/
def cubicPairing (p : Nat) {Site : Type u} [NeZero p] [Fintype Site]
    (x y z : PrimeQuditRegisterLabel p Site) : ZMod p :=
  ∑ site : Site, x site * y site * z site

theorem cubicExponent_eq_cubicPairing (p : Nat) [NeZero p] {Site : Type u} [Fintype Site]
    (label : PrimeQuditRegisterLabel p Site) :
    cubicExponent p label = cubicPairing p label label label := by
  unfold cubicExponent cubicPairing
  apply Finset.sum_congr rfl
  intro site _
  ring

/-- A finite matrix of logical and stabilizer rows for the prime-qudit CSS route. -/
structure CubicRowFamily (p : Nat) [NeZero p]
    (Logical Stabilizer Site : Type u)
    [Fintype Logical] [Fintype Stabilizer] [Fintype Site] where
  /-- Rows whose coefficients label the encoded computational basis. -/
  logicalRow : Logical → PrimeQuditRegisterLabel p Site
  /-- Rows summed uniformly in every stabilizer coset. -/
  stabilizerRow : Stabilizer → PrimeQuditRegisterLabel p Site
  /-- The displayed matrix rows are linearly independent over `ZMod p`. -/
  rowIndependent : ∀ (u : Logical → ZMod p) (h : Stabilizer → ZMod p),
    (∑ a : Logical, u a • logicalRow a) +
      ∑ s : Stabilizer, h s • stabilizerRow s = 0 → u = 0 ∧ h = 0
  /-- Every cubic term containing a stabilizer row vanishes, including repetitions. -/
  stabilizerTriple_zero : ∀ (a b c : Logical ⊕ Stabilizer),
    ((∃ s, a = Sum.inr s) ∨ (∃ s, b = Sum.inr s) ∨ (∃ s, c = Sum.inr s)) →
      cubicPairing p (Sum.elim logicalRow stabilizerRow a)
        (Sum.elim logicalRow stabilizerRow b) (Sum.elim logicalRow stabilizerRow c) = 0
  /-- A triple of logical rows vanishes unless all three indices agree. -/
  logicalTriple_offDiagonal_zero : ∀ (a b c : Logical),
    ¬ (a = b ∧ b = c) →
      cubicPairing p (logicalRow a) (logicalRow b) (logicalRow c) = 0

namespace CubicRowFamily

variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]

local instance : DecidableEq Logical := Classical.decEq _
local instance : DecidableEq Stabilizer := Classical.decEq _
local instance : DecidableEq Site := Classical.decEq _

/-- View logical and stabilizer matrix rows in one common finite index type. -/
def row (R : CubicRowFamily p Logical Stabilizer Site) :
    Logical ⊕ Stabilizer → PrimeQuditRegisterLabel p Site
  | Sum.inl a => R.logicalRow a
  | Sum.inr s => R.stabilizerRow s

theorem row_eq_sumElim (R : CubicRowFamily p Logical Stabilizer Site) :
    R.row = Sum.elim R.logicalRow R.stabilizerRow := by
  funext index
  cases index <;> rfl

@[simp]
theorem row_inl (R : CubicRowFamily p Logical Stabilizer Site) (a : Logical) :
    R.row (Sum.inl a) = R.logicalRow a := rfl

@[simp]
theorem row_inr (R : CubicRowFamily p Logical Stabilizer Site) (s : Stabilizer) :
    R.row (Sum.inr s) = R.stabilizerRow s := rfl

/-- The diagonal cubic coefficient determined by one logical matrix row. -/
def epsilon (R : CubicRowFamily p Logical Stabilizer Site) (a : Logical) : ZMod p :=
  cubicPairing p (R.logicalRow a) (R.logicalRow a) (R.logicalRow a)

/-- The logical component of the word selected by a logical label. -/
def logicalWord (R : CubicRowFamily p Logical Stabilizer Site) (u : Logical → ZMod p) :
    PrimeQuditRegisterLabel p Site :=
  ∑ a : Logical, u a • R.logicalRow a

/-- The stabilizer component of a word in a uniform coset. -/
def stabilizerWord (R : CubicRowFamily p Logical Stabilizer Site) (h : Stabilizer → ZMod p) :
    PrimeQuditRegisterLabel p Site :=
  ∑ s : Stabilizer, h s • R.stabilizerRow s

/-- The physical computational-basis label in the CSS coset for `u` and `h`.

The negative logical representative fixes the source-required inverse logical
cubic orientation without changing the physical `U_{1,3}` action.
-/
def cosetLabel (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    PrimeQuditRegisterLabel p Site :=
  -R.logicalWord u + R.stabilizerWord h

/-- Coefficients for logical and stabilizer rows in one common row index. -/
def combinedCoefficient (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    Logical ⊕ Stabilizer → ZMod p
  | Sum.inl a => -u a
  | Sum.inr s => h s

/-- A word assembled from arbitrary coefficients on all displayed matrix rows. -/
def combinedWord (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → ZMod p) : PrimeQuditRegisterLabel p Site :=
  ∑ r : Logical ⊕ Stabilizer, q r • R.row r

theorem cosetLabel_eq_combinedWord (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    R.cosetLabel u h = R.combinedWord (combinedCoefficient u h) := by
  classical
  ext site
  simp only [cosetLabel, combinedWord, logicalWord, stabilizerWord,
    Pi.neg_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    combinedCoefficient, row]
  rw [Fintype.sum_sum_type]
  simp

/-- Expanding a cubic pairing of arbitrary finite row combinations. -/
theorem cubicPairing_combinedWord (R : CubicRowFamily p Logical Stabilizer Site)
    (q r s : Logical ⊕ Stabilizer → ZMod p) :
    cubicPairing p (R.combinedWord q) (R.combinedWord r) (R.combinedWord s) =
      ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, q a * r b * s c * cubicPairing p (R.row a) (R.row b) (R.row c) := by
  classical
  unfold cubicPairing combinedWord
  simp only [Pi.smul_apply, Finset.sum_apply]
  have expand (site : Site) :
      (∑ a, q a * R.row a site) * (∑ b, r b * R.row b site) *
          (∑ c, s c * R.row c site) =
        ∑ a, ∑ b, ∑ c,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    calc
      (q a * R.row a site * ∑ b, r b * R.row b site) *
          ∑ c, s c * R.row c site =
        ∑ c, (q a * R.row a site * ∑ b, r b * R.row b site) *
          (s c * R.row c site) := by rw [Finset.mul_sum]
      _ = ∑ c, ∑ b,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
        apply Finset.sum_congr rfl
        intro c _
        calc
          (q a * R.row a site * ∑ b, r b * R.row b site) *
              (s c * R.row c site) =
              q a * R.row a site *
                ((∑ b, r b * R.row b site) * (s c * R.row c site)) := by ring
          _ = q a * R.row a site * ∑ b,
              (r b * R.row b site) * (s c * R.row c site) := by rw [Finset.sum_mul]
          _ = ∑ b, q a * R.row a site *
              ((r b * R.row b site) * (s c * R.row c site)) := by rw [Finset.mul_sum]
          _ = ∑ b,
              (q a * R.row a site) * (r b * R.row b site) *
                (s c * R.row c site) := by
              apply Finset.sum_congr rfl
              intro b _
              ring
      _ = ∑ b, ∑ c,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
        exact Finset.sum_comm
  calc
    (∑ site,
        (∑ a, q a * R.row a site) * (∑ b, r b * R.row b site) *
          (∑ c, s c * R.row c site)) =
        ∑ site, ∑ a, ∑ b, ∑ c,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
      apply Finset.sum_congr rfl
      intro site _
      exact expand site
    _ = ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, ∑ site : Site,
          q a * r b * s c * (R.row a site * R.row b site * R.row c site) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro site _
      ring
    _ = ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, q a * r b * s c *
          (∑ site : Site, R.row a site * R.row b site * R.row c site) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]

private theorem logicalTripleContribution_eq_diagonal (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical → ZMod p) (a : Logical) :
    ∑ b : Logical, ∑ c : Logical,
      q a * q b * q c * cubicPairing p (R.logicalRow a) (R.logicalRow b) (R.logicalRow c) =
      q a ^ 3 * R.epsilon a := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp only [epsilon]
      ring
    · intro c _ hca
      rw [R.logicalTriple_offDiagonal_zero a a c]
      · simp
      · intro hall
        exact hca hall.2.symm
    · simp
  · intro b _ hba
    apply Finset.sum_eq_zero
    intro c _
    rw [R.logicalTriple_offDiagonal_zero a b c]
    · simp
    · intro hall
      exact hba hall.1.symm
  · simp

private theorem logicalTripleSum_eq_diagonal (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical → ZMod p) :
    ∑ a : Logical, ∑ b : Logical, ∑ c : Logical,
      q a * q b * q c * cubicPairing p (R.logicalRow a) (R.logicalRow b) (R.logicalRow c) =
      ∑ a : Logical, q a ^ 3 * R.epsilon a := by
  apply Finset.sum_congr rfl
  intro a _
  exact R.logicalTripleContribution_eq_diagonal q a

/-- Strong row orthogonality reduces every cubic row combination to its diagonal logical terms. -/
theorem cubicPairing_combinedWord_eq_diagonal (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → ZMod p) :
    cubicPairing p (R.combinedWord q) (R.combinedWord q) (R.combinedWord q) =
      ∑ a : Logical, q (Sum.inl a) ^ 3 * R.epsilon a := by
  rw [R.cubicPairing_combinedWord]
  have houter :
      (∑ s : Stabilizer, ∑ b : Logical ⊕ Stabilizer, ∑ c : Logical ⊕ Stabilizer,
        q (Sum.inr s) * q b * q c *
          cubicPairing p (R.row (Sum.inr s)) (R.row b) (R.row c)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    have hzero : cubicPairing p (R.row (Sum.inr s)) (R.row b) (R.row c) = 0 := by
      rw [R.row_eq_sumElim]
      exact R.stabilizerTriple_zero (Sum.inr s) b c (Or.inl ⟨s, rfl⟩)
    rw [hzero]
    simp
  rw [Fintype.sum_sum_type, houter, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  have hsecond :
      (∑ s : Stabilizer, ∑ c : Logical ⊕ Stabilizer,
        q (Sum.inl a) * q (Sum.inr s) * q c *
          cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inr s)) (R.row c)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro c _
    have hzero : cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inr s)) (R.row c) = 0 := by
      rw [R.row_eq_sumElim]
      exact R.stabilizerTriple_zero (Sum.inl a) (Sum.inr s) c (Or.inr (Or.inl ⟨s, rfl⟩))
    rw [hzero]
    simp
  rw [Fintype.sum_sum_type, hsecond, add_zero]
  calc
    (∑ b : Logical, ∑ c : Logical ⊕ Stabilizer,
      q (Sum.inl a) * q (Sum.inl b) * q c *
        cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b)) (R.row c)) =
      ∑ b : Logical, ∑ c : Logical,
        q (Sum.inl a) * q (Sum.inl b) * q (Sum.inl c) *
          cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b)) (R.row (Sum.inl c)) := by
      apply Finset.sum_congr rfl
      intro b _
      have hthird :
          (∑ s : Stabilizer,
            q (Sum.inl a) * q (Sum.inl b) * q (Sum.inr s) *
              cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b)) (R.row (Sum.inr s))) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        have hzero : cubicPairing p (R.row (Sum.inl a)) (R.row (Sum.inl b))
            (R.row (Sum.inr s)) = 0 := by
          simpa [row] using R.stabilizerTriple_zero (Sum.inl a) (Sum.inl b) (Sum.inr s)
            (Or.inr (Or.inr ⟨s, rfl⟩))
        rw [hzero]
        simp
      rw [Fintype.sum_sum_type, hthird, add_zero]
    _ = q (Sum.inl a) ^ 3 * R.epsilon a := by
      simpa [row] using
        R.logicalTripleContribution_eq_diagonal (fun a => q (Sum.inl a)) a

/-- The cubic exponent of every CSS coset label is the negative logical diagonal form. -/
theorem cubicExponent_cosetLabel (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    cubicExponent p (R.cosetLabel u h) =
      -(∑ a : Logical, u a ^ 3 * R.epsilon a) := by
  rw [cubicExponent_eq_cubicPairing, R.cosetLabel_eq_combinedWord,
    R.cubicPairing_combinedWord_eq_diagonal]
  calc
    (∑ a : Logical, combinedCoefficient u h (Sum.inl a) ^ 3 * R.epsilon a) =
        ∑ a : Logical, -(u a ^ 3 * R.epsilon a) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [combinedCoefficient]
      ring
    _ = -(∑ a : Logical, u a ^ 3 * R.epsilon a) := by
      rw [Finset.sum_neg_distrib]

theorem logicalWord_sub (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) : R.logicalWord (u - v) = R.logicalWord u - R.logicalWord v := by
  classical
  ext site
  simp [logicalWord, Finset.sum_sub_distrib, sub_smul]

theorem stabilizerWord_sub (R : CubicRowFamily p Logical Stabilizer Site)
    (h k : Stabilizer → ZMod p) :
    R.stabilizerWord (h - k) = R.stabilizerWord h - R.stabilizerWord k := by
  classical
  ext site
  simp [stabilizerWord, Finset.sum_sub_distrib, sub_smul]

/-- Different logical labels select disjoint finite stabilizer cosets. -/
theorem cosetLabel_eq_implies_logical_eq (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) (h k : Stabilizer → ZMod p)
    (heq : R.cosetLabel u h = R.cosetLabel v k) : u = v := by
  have hzero : R.logicalWord (u - v) + R.stabilizerWord (k - h) = 0 := by
    rw [R.logicalWord_sub, R.stabilizerWord_sub]
    ext site
    have hpoint := congrFun heq site
    change -R.logicalWord u site + R.stabilizerWord h site =
      -R.logicalWord v site + R.stabilizerWord k site at hpoint
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    change R.logicalWord u site - R.logicalWord v site +
      (R.stabilizerWord k site - R.stabilizerWord h site) = 0
    linear_combination -hpoint
  have hIndependent := R.rowIndependent (u - v) (k - h) hzero
  have huv : u - v = 0 := hIndependent.1
  exact sub_eq_zero.mp huv

/-- For one logical label, stabilizer coefficients give distinct physical labels. -/
theorem cosetLabel_injective (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : Function.Injective (R.cosetLabel u) := by
  intro h k heq
  have hzero : R.logicalWord (u - u) + R.stabilizerWord (k - h) = 0 := by
    rw [R.logicalWord_sub, R.stabilizerWord_sub]
    ext site
    have hpoint := congrFun heq site
    change -R.logicalWord u site + R.stabilizerWord h site =
      -R.logicalWord u site + R.stabilizerWord k site at hpoint
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    rw [sub_self, zero_add]
    change R.stabilizerWord k site - R.stabilizerWord h site = 0
    linear_combination -hpoint
  have hIndependent := R.rowIndependent (u - u) (k - h) hzero
  exact (sub_eq_zero.mp hIndependent.2).symm

/-- The finite type of coefficient vectors summed in one stabilizer coset. -/
abbrev StabilizerLabel (p : Nat) (Stabilizer : Type u) := Stabilizer → ZMod p

/-- The source-faithful inverse-square-root normalization of one stabilizer coset. -/
def cosetNormalization (p : Nat) [NeZero p] (Stabilizer : Type u)
    [Fintype Stabilizer] : Complex :=
  (Real.sqrt (Nat.card (StabilizerLabel p Stabilizer) : Real) : Complex)⁻¹

/-- The actual uniform stabilizer-coset ket for a logical computational label. -/
def cosetKet (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : PrimeQuditRegister p Site :=
  cosetNormalization p Stabilizer •
    ∑ h : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel u h)

/-- Every coset summand has exactly the declared uniform amplitude. -/
theorem cosetKet_apply (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) (h : StabilizerLabel p Stabilizer) :
    inner Complex (registerBasisKet p (R.cosetLabel u h)) (R.cosetKet u) =
      cosetNormalization p Stabilizer := by
  classical
  unfold cosetKet
  rw [inner_smul_right, inner_sum]
  rw [Finset.sum_eq_single h]
  · simp [registerBasisKet]
  · intro h' _hh' hne
    have hlabel : R.cosetLabel u h' ≠ R.cosetLabel u h :=
      fun heq => hne (R.cosetLabel_injective u heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel.symm]
  · simp

private theorem uniformCosetSum_inner (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) :
    inner Complex
        (∑ h : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel u h))
        (∑ k : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel v k)) =
      if u = v then (Nat.card (StabilizerLabel p Stabilizer) : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases huv : u = v
  · subst v
    have hinner (h k : StabilizerLabel p Stabilizer) :
        inner Complex (registerBasisKet p (R.cosetLabel u h))
          (registerBasisKet p (R.cosetLabel u k)) = if h = k then 1 else 0 := by
      simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
      rw [EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply, (R.cosetLabel_injective u).eq_iff]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    have hlabel : R.cosetLabel u k ≠ R.cosetLabel v h :=
      fun heq => huv (R.cosetLabel_eq_implies_logical_eq u v k h heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel]

/-- The finite coset normalization has unit squared norm. -/
theorem cosetNormalization_conj_mul_card (R : CubicRowFamily p Logical Stabilizer Site) :
    starRingEnd Complex (cosetNormalization p Stabilizer) * cosetNormalization p Stabilizer *
        (Nat.card (StabilizerLabel p Stabilizer) : Complex) = 1 := by
  have hpos : (0 : Real) < Nat.card (StabilizerLabel p Stabilizer) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (StabilizerLabel p Stabilizer))
  have hsqrt :
      (Real.sqrt (Nat.card (StabilizerLabel p Stabilizer) : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  unfold cosetNormalization
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  norm_cast
  exact (Real.sq_sqrt hpos.le).symm

/-- The normalized finite stabilizer-coset states are orthonormal. -/
theorem cosetKet_inner (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) :
    inner Complex (R.cosetKet u) (R.cosetKet v) = if u = v then 1 else 0 := by
  unfold cosetKet
  rw [inner_smul_left, inner_smul_right, uniformCosetSum_inner]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    rw [← mul_assoc]
    exact R.cosetNormalization_conj_mul_card
  · simp [huv]

/-- The normalized coset family is an orthonormal computational basis for the code carrier. -/
theorem cosetKet_orthonormal (R : CubicRowFamily p Logical Stabilizer Site) :
    Orthonormal Complex R.cosetKet := by
  rw [orthonormal_iff_ite]
  intro u v
  exact R.cosetKet_inner u v

/-- Extend the actual coset kets linearly from logical computational amplitudes. -/
noncomputable def encodingLinearMap (R : CubicRowFamily p Logical Stabilizer Site) :
    PrimeQuditRegister p Logical →ₗ[Complex] PrimeQuditRegister p Site where
  toFun psi := ∑ u : Logical → ZMod p, psi u • R.cosetKet u
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]

/-- The explicit normalized-coset encoder preserves the logical inner product. -/
theorem encodingLinearMap_map_inner (R : CubicRowFamily p Logical Stabilizer Site)
    (psi chi : PrimeQuditRegister p Logical) :
    inner Complex (R.encodingLinearMap psi) (R.encodingLinearMap chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ u : Logical → ZMod p, psi u • R.cosetKet u)
      (∑ u : Logical → ZMod p, chi u • R.cosetKet u) = inner Complex psi chi
  rw [R.cosetKet_orthonormal.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]

/-- The normalized coset encoder promoted to a proved linear isometry. -/
noncomputable def encodingIsometry (R : CubicRowFamily p Logical Stabilizer Site) :
    PrimeQuditRegister p Logical →ₗᵢ[Complex] PrimeQuditRegister p Site :=
  R.encodingLinearMap.isometryOfInner R.encodingLinearMap_map_inner

/-- The actual physical CSS carrier: the range of the normalized coset isometry. -/
noncomputable def encodedCarrier (R : CubicRowFamily p Logical Stabilizer Site) :
    Submodule Complex (PrimeQuditRegister p Site) :=
  R.encodingIsometry.toLinearMap.range

/-- The range carrier viewed as a semantic quantum code. -/
noncomputable def quantumCode (R : CubicRowFamily p Logical Stabilizer Site) :
    QuantumCode (PrimeQuditRegister p Site) where
  carrier := R.encodedCarrier

/-- The complete CSS code, constructed only from the finite matrix data. -/
noncomputable def encodedCode (R : CubicRowFamily p Logical Stabilizer Site) :
    EncodedCode (PrimeQuditRegister p Logical) (PrimeQuditRegister p Site) where
  code := R.quantumCode
  encoding := LinearIsometry.equivRange R.encodingIsometry

/-- On a logical computational ket the semantic encoder is the stated uniform coset ket. -/
theorem encodingLinearMap_apply_logical_basis (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    R.encodingLinearMap (registerBasisKet p u) = R.cosetKet u := by
  change (∑ v : Logical → ZMod p, registerBasisKet p u v • R.cosetKet v) = R.cosetKet u
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]

/-- The encoded code exposes the same ambient vector on a logical basis ket. -/
theorem encodedCode_apply_logical_basis (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    R.encodedCode.encode (registerBasisKet p u) = R.cosetKet u :=
  R.encodingLinearMap_apply_logical_basis u

/-- The semantic encoded code has the concrete normalized-coset linear map as its encoder. -/
theorem encodedCode_encode_eq_encodingLinearMap (R : CubicRowFamily p Logical Stabilizer Site)
    (psi : PrimeQuditRegister p Logical) :
    R.encodedCode.encode psi = R.encodingLinearMap psi :=
  rfl

/-- The inverse logical cubic exponent determined by the diagonal row coefficients. -/
def logicalInverseExponent (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : ZMod p :=
  -(∑ a : Logical, u a ^ 3 * R.epsilon a)

/-- The specified inverse logical cubic phase. -/
def logicalInverseAmplitude (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : Complex :=
  phase p (R.logicalInverseExponent u)

/-- The inverse logical cubic transport specified by the displayed diagonal coefficients. -/
noncomputable def logicalInverseU13 (R : CubicRowFamily p Logical Stabilizer Site) :
    UnitaryTransport (PrimeQuditRegister p Logical) (PrimeQuditRegister p Logical) where
  toLinearEquiv := diagonalLinearEquiv R.logicalInverseAmplitude
    (fun u => phase p (-R.logicalInverseExponent u))
    (by
      intro u
      change phase p (-R.logicalInverseExponent u) * phase p (R.logicalInverseExponent u) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro u
      change phase p (R.logicalInverseExponent u) * phase p (-R.logicalInverseExponent u) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner R.logicalInverseAmplitude
    (fun u => phase_mul_conj p (R.logicalInverseExponent u))

@[simp]
theorem logicalInverseU13_apply (R : CubicRowFamily p Logical Stabilizer Site)
    (psi : PrimeQuditRegister p Logical) (u : Logical → ZMod p) :
    R.logicalInverseU13 psi u = R.logicalInverseAmplitude u * psi u :=
  rfl

/-- The physical cubic product gives the specified inverse logical phase on each coset ket. -/
theorem physicalU13_cosetKet (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    physicalU13 p (R.cosetKet u) = R.logicalInverseAmplitude u • R.cosetKet u := by
  unfold cosetKet
  rw [map_smul, map_sum]
  simp_rw [physicalU13_apply_basis_phase, R.cubicExponent_cosetLabel]
  change cosetNormalization p Stabilizer •
      (∑ h : StabilizerLabel p Stabilizer,
        R.logicalInverseAmplitude u • registerBasisKet p (R.cosetLabel u h)) =
      R.logicalInverseAmplitude u •
        (cosetNormalization p Stabilizer •
          ∑ h : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel u h))
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm]

/-- Full pointwise encoder-commuting equation for the physical and inverse logical cubic gates. -/
theorem physicalU13_intertwines_encodingLinearMap (R : CubicRowFamily p Logical Stabilizer Site)
    (psi : PrimeQuditRegister p Logical) :
    physicalU13 p (R.encodingLinearMap psi) =
    R.encodingLinearMap (R.logicalInverseU13 psi)
    := by
  unfold encodingLinearMap
  change physicalU13 p (∑ u : Logical → ZMod p, psi u • R.cosetKet u) =
    ∑ u : Logical → ZMod p, (R.logicalInverseU13 psi) u • R.cosetKet u
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [map_smul, R.physicalU13_cosetKet, smul_smul]
  change (psi u * R.logicalInverseAmplitude u) • R.cosetKet u =
    (R.logicalInverseAmplitude u * psi u) • R.cosetKet u
  rw [mul_comm]

end CubicRowFamily

namespace CubicRowFamily

variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]

/-- The literal physical `U_{1,3}` product associated with any prime-qudit row family. -/
noncomputable def physicalU13 (R : CubicRowFamily p Logical Stabilizer Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) :=
  _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p

/-- The support-indexed local physical-gate model for the row family's physical register. -/
noncomputable def physicalGateModel (R : CubicRowFamily p Logical Stabilizer Site) :
    FinitePhysicalGateModel Site (PrimeQuditRegister p Site) :=
  physicalU13GateModel p

/-- Literal singleton-site factorization of the row family's physical cubic product. -/
noncomputable def physicalU13SitewiseFactorization (R : CubicRowFamily p Logical Stabilizer Site) :
    SitewiseTransversalityData R.physicalGateModel R.physicalU13 :=
  _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13SitewiseFactorization p

end CubicRowFamily

namespace CubicRowFamily

variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]

/-- The p>=5 KT19 route exports the full semantic encoder-commuting predicate.

The cubic row algebra is intentionally stated at its natural `NeZero p`
generality.  This wrapper binds the reusable physical-to-inverse-logical API
to the prime, nondegenerate cubic hierarchy established by
`u13_has_hierarchy`.
-/
theorem physicalU13_implements_inverseLogicalU13 (R : CubicRowFamily p Logical Stabilizer Site)
    (hp : PrimeAtLeastFive p) :
    R.encodedCode.ImplementsLogicalGate R.physicalU13 R.logicalInverseU13 := by
  cases u13_has_hierarchy p hp
  intro psi
  change _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p
      (R.encodingLinearMap psi) =
    R.encodingLinearMap (R.logicalInverseU13 psi)
  exact R.physicalU13_intertwines_encodingLinearMap psi

end CubicRowFamily

/-- Relabel one qudit as the finite register indexed by `Fin 1`. -/
def singleLogicalLabelEquiv (p : Nat) [NeZero p] :
    ZMod p ≃ (Fin 1 → ZMod p) where
  toFun x := fun _ => x
  invFun label := label 0
  left_inv _ := rfl
  right_inv label := by
    funext index
    fin_cases index
    rfl

/-- The finite-register isometry identifying a one-coordinate register with one physical qudit. -/
noncomputable def singleLogicalRegisterEquiv (p : Nat) [NeZero p] :
    PrimeQudit p ≃ₗᵢ[Complex] PrimeQuditRegister p (Fin 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (singleLogicalLabelEquiv p)

/-- The preceding one-qudit/register identification as a semantic unitary transport. -/
noncomputable def singleLogicalRegisterTransport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQuditRegister p (Fin 1)) where
  toLinearEquiv := (singleLogicalRegisterEquiv p).toLinearEquiv
  map_inner := fun psi chi => (singleLogicalRegisterEquiv p).inner_map_map psi chi

/-- A genuine five-site, one-logical-coordinate prime-qudit matrix fixture. -/
noncomputable def fiveSiteSingleLogical : CubicRowFamily 5 (Fin 1) Empty (Fin 5) where
  logicalRow _ site := if site = 0 then 1 else 0
  stabilizerRow s := Empty.elim s
  rowIndependent := by
    intro u h hzero
    constructor
    · funext a
      fin_cases a
      have hpoint := congrFun hzero 0
      simpa using hpoint
    · funext s
      exact Empty.elim s
  stabilizerTriple_zero := by
    intro a b c hcontains
    rcases hcontains with ⟨s, _⟩ | ⟨s, _⟩ | ⟨s, _⟩ <;> exact Empty.elim s
  logicalTriple_offDiagonal_zero := by
    intro a b c hnot
    exfalso
    apply hnot
    fin_cases a
    fin_cases b
    fin_cases c
    exact ⟨rfl, rfl⟩

/-- The five-site fixture's diagonal coefficient is exactly one. -/
theorem fiveSiteSingleLogical_epsilon : fiveSiteSingleLogical.epsilon 0 = 1 := by
  simp [CubicRowFamily.epsilon, cubicPairing, fiveSiteSingleLogical]

/-- The prime-at-least-five witness for the finite p=5 fixture. -/
theorem primeAtLeastFive_five : PrimeAtLeastFive 5 := by
  constructor <;> norm_num

namespace fiveSiteSingleLogical

/-- The five-site fixture's encoder, presented on the literal one-qudit logical Hilbert space. -/
noncomputable def encodedCode :
    EncodedCode (PrimeQudit 5) (PrimeQuditRegister 5 (Fin 5)) where
  code := CubicRowFamily.quantumCode fiveSiteSingleLogical
  encoding := (singleLogicalRegisterEquiv 5).trans
    (CubicRowFamily.encodedCode fiveSiteSingleLogical).encoding

/-- The fixture's inverse logical cubic gate, transported back to one literal qudit. -/
noncomputable def logicalInverseU13 :
    UnitaryTransport (PrimeQudit 5) (PrimeQudit 5) where
  toLinearEquiv := ((singleLogicalRegisterTransport 5).trans
    (CubicRowFamily.logicalInverseU13 fiveSiteSingleLogical)).trans
      (singleLogicalRegisterTransport 5).symm |>.toLinearEquiv
  map_inner := ((singleLogicalRegisterTransport 5).trans
    (CubicRowFamily.logicalInverseU13 fiveSiteSingleLogical)).trans
      (singleLogicalRegisterTransport 5).symm |>.map_inner

end fiveSiteSingleLogical

/-- The p=5 fixture has the generic full encoder-commuting equation on one literal qudit. -/
theorem fiveSiteSingleLogical_intertwines_encoding (psi : PrimeQudit 5) :
    fiveSiteSingleLogical.physicalU13 (fiveSiteSingleLogical.encodedCode.encode psi) =
      fiveSiteSingleLogical.encodedCode.encode (fiveSiteSingleLogical.logicalInverseU13 psi) := by
  change physicalU13 5
      (fiveSiteSingleLogical.encodingLinearMap (singleLogicalRegisterEquiv 5 psi)) =
    fiveSiteSingleLogical.encodingLinearMap
      (singleLogicalRegisterEquiv 5
        ((singleLogicalRegisterEquiv 5).symm
          (CubicRowFamily.logicalInverseU13 fiveSiteSingleLogical
            (singleLogicalRegisterEquiv 5 psi))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact CubicRowFamily.physicalU13_intertwines_encodingLinearMap fiveSiteSingleLogical
    (singleLogicalRegisterEquiv 5 psi)

/-- The p=5 fixture satisfies the semantic implementation predicate, not merely basis preservation. -/
theorem fiveSiteSingleLogical_implements_inverseLogicalU13 :
    fiveSiteSingleLogical.encodedCode.ImplementsLogicalGate fiveSiteSingleLogical.physicalU13
      fiveSiteSingleLogical.logicalInverseU13 := by
  intro psi
  exact fiveSiteSingleLogical_intertwines_encoding psi

/-- The fixture exposes the literal singleton physical factorization. -/
noncomputable def fiveSiteSingleLogical_sitewiseFactorization :
    SitewiseTransversalityData fiveSiteSingleLogical.physicalGateModel
      fiveSiteSingleLogical.physicalU13 :=
  fiveSiteSingleLogical.physicalU13SitewiseFactorization

end QEC.Distillation.KT19PrimeQuditCSS
