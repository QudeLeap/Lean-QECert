import QEC.Coding.Core.Definitions
import QEC.Semantics.ErrorCorrection.Detectability
import QEC.Semantics.ErrorCorrection.FiniteAlphabetLocality
import QEC.Semantics.ErrorCorrection.QuditNoInformation
import QEC.Coding.QLDPC.BPTMeasurementDistance
import QEC.Semantics.ErrorCorrection.QuditMatrixElements
import QEC.Semantics.ErrorCorrection.QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# Finite-field Pauli shifts and phases

The computational basis of a register of finite-field symbols supports
literal shift and phase operators. The phase uses the primitive complex
additive character of an arbitrary finite field, so this file does not
specialize the PK22 construction to characteristic two.

The common X/Z fixed subspace is an actual quantum code. Orthogonal coset
indicator states form an explicit basis, giving its exact complex dimension.
Pauli Fourier expansion relates algebraic CSS distance to detectability of
arbitrary tensor-local operators in field coordinates. The full measurement-
distance identification remains to be established.
-/

noncomputable section

namespace QEC.Coding.FiniteFieldPauli

open Classical

universe u v

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/-- The field-labelled computational Hilbert space. -/
abbrev Register (F : Type u) (ι : Type v) [Field F] [Fintype F] [Fintype ι] :=
  EuclideanSpace Complex (Word F ι)

/-- The primitive additive character used for every field-valued phase. -/
def character (F : Type u) [Field F] [Fintype F] : AddChar F Complex :=
  AddChar.FiniteField.primitiveChar_to_Complex F

/-- Multiplication by any nonzero field element keeps the phase character nontrivial. -/
theorem character_isPrimitive : (character F).IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F

/-- Every nonzero field pairing can be exposed as a nontrivial phase by scaling. -/
theorem exists_character_mul_ne_one (a : F) (ha : a ≠ 0) :
    ∃ t : F, character F (a * t) ≠ 1 := by
  by_contra hnone
  have hall : ∀ t : F, character F (a * t) = 1 := by
    intro t
    by_contra ht
    exact hnone ⟨t, ht⟩
  have heq : (character F).mulShift a = 1 := by
    ext t
    simpa using hall t
  exact character_isPrimitive ha heq

/-- Finite-coordinate duality is involutive over every finite field. -/
theorem dual_dual_carrier_eq (C : LinearCode F ι) :
    C.dual.dual.carrier = C.carrier := by
  have hle : C.carrier ≤ C.dual.dual.carrier :=
    C.le_dual_of_le_dual C.dual le_rfl
  have hdim : Dimension C.dual.dual = Dimension C := by
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      LinearCode.dual_dimension_eq_length_sub_dimension]
    have hbound := C.dimension_le_length
    omega
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  simpa [Dimension_eq_finrank_carrier] using hdim.symm

/-- A word outside a code has a dual-code witness with nontrivial character phase. -/
theorem exists_dual_character_ne_one (C : LinearCode F ι)
    (z : Word F ι) (hz : z ∉ C.carrier) :
    ∃ a : Word F ι, a ∈ C.dual.carrier ∧
      character F (wordPairing (F := F) (ι := ι) z a) ≠ 1 := by
  have hpair : ∃ a : Word F ι, a ∈ C.dual.carrier ∧
      wordPairing (F := F) (ι := ι) z a ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hdual : z ∈ C.dual.dual.carrier :=
      (C.dual.mem_dual z).2 hnone
    rw [dual_dual_carrier_eq] at hdual
    exact hz hdual
  obtain ⟨a, ha, hnonzero⟩ := hpair
  obtain ⟨t, ht⟩ := exists_character_mul_ne_one
    (wordPairing (F := F) (ι := ι) z a) hnonzero
  refine ⟨t • a, C.dual.carrier.smul_mem t ha, ?_⟩
  rw [map_smul, smul_eq_mul, mul_comm]
  exact ht

/-- A field word induces a complex character through the nondegenerate pairing. -/
def wordCharacter (z : Word F ι) : AddChar (Word F ι) Complex where
  toFun η := character F (wordPairing (F := F) (ι := ι) z η)
  map_zero_eq_one' := by simp [character]
  map_add_eq_mul' η ξ := by
    rw [(wordPairing (F := F) (ι := ι) z).map_add]
    exact AddChar.map_add_eq_mul _ _ _

/-- Primitive field character and nondegenerate pairing enumerate word characters. -/
theorem wordCharacter_injective :
    Function.Injective (wordCharacter (F := F) (ι := ι)) := by
  intro z w hzw
  have hpair : ∀ η : Word F ι,
      wordPairing (F := F) (ι := ι) z η =
        wordPairing (F := F) (ι := ι) w η := by
    intro η
    apply AddChar.to_mulShift_inj_of_isPrimitive
      (character_isPrimitive (F := F))
    ext t
    have hvalue := congrArg (fun φ : AddChar (Word F ι) Complex => φ (t • η)) hzw
    simpa [wordCharacter, AddChar.mulShift_apply, map_smul, mul_comm] using hvalue
  have hzero : z - w = 0 := by
    apply (wordPairing_nondegenerate (F := F) (ι := ι)).left
    intro η
    rw [LinearMap.BilinForm.sub_left]
    exact sub_eq_zero.mpr (hpair η)
  exact sub_eq_zero.mp hzero

/-- The word pairing lists every additive character of the finite word group. -/
noncomputable def wordCharacterEquiv :
    Word F ι ≃ AddChar (Word F ι) Complex := by
  classical
  apply Equiv.ofBijective (wordCharacter (F := F) (ι := ι))
  rw [Fintype.bijective_iff_injective_and_card,
    AddChar.card_eq]
  exact ⟨wordCharacter_injective, rfl⟩

/-- The pairing characters form a concrete basis of complex word functions. -/
noncomputable def wordCharacterBasis :
    Module.Basis (Word F ι) Complex (Word F ι → Complex) :=
  (AddChar.complexBasis (Word F ι)).reindex
    (wordCharacterEquiv (F := F) (ι := ι)).symm

@[simp] theorem wordCharacterBasis_apply (z η : Word F ι) :
    wordCharacterBasis (F := F) (ι := ι) z η =
      character F (wordPairing (F := F) (ι := ι) z η) := by
  simp [wordCharacterBasis, Module.Basis.reindex_apply, wordCharacterEquiv,
    wordCharacter]

/-- Translation of complex-valued word functions. -/
def wordTranslate (t : Word F ι) :
    (Word F ι → Complex) →ₗ[Complex] (Word F ι → Complex) where
  toFun f := fun b => f (b + t)
  map_add' f g := by funext b; rfl
  map_smul' c f := by funext b; rfl

/-- Every pairing character is an eigenfunction of word translation. -/
theorem wordTranslate_wordCharacterBasis (t z : Word F ι) :
    wordTranslate t (wordCharacterBasis (F := F) (ι := ι) z) =
      (character F (wordPairing (F := F) (ι := ι) z t)) •
        wordCharacterBasis (F := F) (ι := ι) z := by
  funext b
  simp only [wordTranslate, LinearMap.coe_mk, AddHom.coe_mk,
    wordCharacterBasis_apply, Pi.smul_apply, smul_eq_mul]
  rw [(wordPairing (F := F) (ι := ι) z).map_add,
    AddChar.map_add_eq_mul]
  ring

/-- Translation invariance kills Fourier coefficients with nontrivial eigenphase. -/
theorem wordCharacterBasis_repr_eq_zero_of_translate_invariant
    (f : Word F ι → Complex) (t z : Word F ι)
    (hinv : wordTranslate t f = f)
    (hchar : character F (wordPairing (F := F) (ι := ι) z t) ≠ 1) :
    (wordCharacterBasis (F := F) (ι := ι)).repr f z = 0 := by
  let B := wordCharacterBasis (F := F) (ι := ι)
  have htranslate : wordTranslate t f =
      ∑ i : Word F ι, (B.repr f i) • wordTranslate t (B i) := by
    conv_lhs => rw [← B.sum_repr f]
    rw [map_sum]
    simp only [map_smul]
  have hcoeff : B.repr (wordTranslate t f) z =
      B.repr f z * character F (wordPairing (F := F) (ι := ι) z t) := by
    rw [htranslate]
    have heigen (i : Word F ι) : wordTranslate t (B i) =
        character F (wordPairing (F := F) (ι := ι) i t) • B i :=
      wordTranslate_wordCharacterBasis t i
    simp_rw [heigen, smul_smul]
    rw [B.repr_sum_self]
  rw [hinv] at hcoeff
  by_contra hnonzero
  have hphase : character F (wordPairing (F := F) (ι := ι) z t) = 1 := by
    apply mul_left_cancel₀ hnonzero
    simpa using hcoeff.symm
  exact hchar hphase

/-- Coordinatewise translation of computational-basis labels by `x`. -/
def shift (x : Word F ι) : Semantics.Operator (Register F ι) where
  toFun ψ := WithLp.toLp 2 (fun η => ψ (η + x))
  map_add' ψ φ := by
    ext η
    simp
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul]

@[simp] theorem shift_apply (x : Word F ι) (ψ : Register F ι) (η : Word F ι) :
    shift x ψ η = ψ (η + x) := rfl

/-- The phase at label `η` is the primitive character of `z · η`. -/
def phase (z : Word F ι) : Semantics.Operator (Register F ι) where
  toFun ψ := WithLp.toLp 2 (fun η =>
    character F (wordPairing (F := F) (ι := ι) z η) * ψ η)
  map_add' ψ φ := by
    ext η
    simp [mul_add]
  map_smul' c ψ := by
    ext η
    simp [smul_eq_mul, mul_left_comm]

@[simp] theorem phase_apply (z : Word F ι) (ψ : Register F ι) (η : Word F ι) :
    phase z ψ η = character F (wordPairing (F := F) (ι := ι) z η) * ψ η := rfl

/-- Shifts compose according to addition in the finite-field word space. -/
theorem shift_add (x y : Word F ι) : shift (x + y) = shift x * shift y := by
  ext ψ η
  simp [Module.End.mul_apply, add_comm, add_left_comm]

/-- Phases compose according to addition in the finite-field word space. -/
theorem phase_add (z w : Word F ι) : phase (z + w) = phase z * phase w := by
  ext ψ η
  simp only [Module.End.mul_apply, phase_apply, map_add, LinearMap.add_apply,
    AddChar.map_add_eq_mul, mul_assoc]

/-- A shift translates computational basis kets in the opposite direction. -/
theorem shift_basis (x a : Word F ι) :
    shift x (EuclideanSpace.basisFun (Word F ι) Complex a) =
      EuclideanSpace.basisFun (Word F ι) Complex (a - x) := by
  ext η
  simp only [shift_apply, EuclideanSpace.basisFun_apply]
  by_cases h : η + x = a
  · have h' : η = a - x := by
      funext j
      exact eq_sub_of_add_eq (congrFun h j)
    simp [h']
  · have h' : η ≠ a - x := by
      intro hEq
      apply h
      rw [hEq]
      abel
    simp [h, h']

/-- A phase acts diagonally on computational basis kets. -/
theorem phase_basis (z a : Word F ι) :
    phase z (EuclideanSpace.basisFun (Word F ι) Complex a) =
      (character F (wordPairing (F := F) (ι := ι) z a)) •
        EuclideanSpace.basisFun (Word F ι) Complex a := by
  ext η
  simp only [phase_apply, EuclideanSpace.basisFun_apply, PiLp.smul_apply,
    smul_eq_mul]
  by_cases h : η = a
  · subst η
    simp
  · simp [h]

/-- A vector fixed by every shift in a finite family is fixed by their sum. -/
theorem shift_finset_sum_fixed
    {κ : Type*} (s : Finset κ) (f : κ → Word F ι) (ψ : Register F ι)
    (hfixed : ∀ k ∈ s, shift (f k) ψ = ψ) :
    shift (∑ k ∈ s, f k) ψ = ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext η
      simp [shift_apply]
  | @insert k s hk ih =>
      have htail : shift (∑ j ∈ s, f j) ψ = ψ := by
        apply ih
        intro j hj
        exact hfixed j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hk, shift_add, Module.End.mul_apply, htail,
        hfixed k (Finset.mem_insert_self k s)]

/-- A vector fixed by every phase in a finite family is fixed by their sum. -/
theorem phase_finset_sum_fixed
    {κ : Type*} (s : Finset κ) (f : κ → Word F ι) (ψ : Register F ι)
    (hfixed : ∀ k ∈ s, phase (f k) ψ = ψ) :
    phase (∑ k ∈ s, f k) ψ = ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext η
      simp [phase_apply, character]
  | @insert k s hk ih =>
      have htail : phase (∑ j ∈ s, f j) ψ = ψ := by
        apply ih
        intro j hj
        exact hfixed j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hk, phase_add, Module.End.mul_apply, htail,
        hfixed k (Finset.mem_insert_self k s)]

/-- Fixing every scalar multiple of the images of coordinate basis vectors
implies fixedness under the whole image of a finite-dimensional word map. -/
theorem shift_linearMap_fixed_of_canonicalBasis
    {κ : Type*} [Fintype κ]
    (L : Word F κ →ₗ[F] Word F ι) (ψ : Register F ι)
    (hfixed : ∀ (k : κ) (a : F),
      shift (L (a • canonicalBasisWord k)) ψ = ψ)
    (y : Word F κ) :
    shift (L y) ψ = ψ := by
  classical
  let B := Pi.basisFun F κ
  have hBasis (k : κ) : B k = canonicalBasisWord k := by
    ext j
    simp [B, canonicalBasisWord, Pi.basisFun_apply]
  conv_lhs =>
    rw [← B.sum_repr y, map_sum]
  apply shift_finset_sum_fixed Finset.univ
  intro k _hk
  rw [hBasis]
  exact hfixed k (B.repr y k)

/-- Phase analogue of `shift_linearMap_fixed_of_canonicalBasis`. -/
theorem phase_linearMap_fixed_of_canonicalBasis
    {κ : Type*} [Fintype κ]
    (L : Word F κ →ₗ[F] Word F ι) (ψ : Register F ι)
    (hfixed : ∀ (k : κ) (a : F),
      phase (L (a • canonicalBasisWord k)) ψ = ψ)
    (y : Word F κ) :
    phase (L y) ψ = ψ := by
  classical
  let B := Pi.basisFun F κ
  have hBasis (k : κ) : B k = canonicalBasisWord k := by
    ext j
    simp [B, canonicalBasisWord, Pi.basisFun_apply]
  conv_lhs =>
    rw [← B.sum_repr y, map_sum]
  apply phase_finset_sum_fixed Finset.univ
  intro k _hk
  rw [hBasis]
  exact hfixed k (B.repr y k)

@[simp] theorem shift_zero : shift (0 : Word F ι) = 1 := by
  ext ψ η
  simp

@[simp] theorem phase_zero : phase (0 : Word F ι) = 1 := by
  ext ψ η
  simp [character]

/-- A shift is invertible, with inverse given by the opposite field word. -/
theorem shift_mul_shift_neg (x : Word F ι) : shift x * shift (-x) = 1 := by
  rw [← shift_add]
  simp

/-- A phase is invertible, with inverse given by the opposite field word. -/
theorem phase_mul_phase_neg (z : Word F ι) : phase z * phase (-z) = 1 := by
  rw [← phase_add]
  simp

/-- The field-valued word pairing is the exact X/Z commutation exponent. -/
theorem shift_mul_phase (x z : Word F ι) :
    shift x * phase z =
      (character F (wordPairing (F := F) (ι := ι) z x)) •
        (phase z * shift x) := by
  ext ψ η
  simp only [Module.End.mul_apply, shift_apply, phase_apply,
    LinearMap.smul_apply]
  rw [(wordPairing (F := F) (ι := ι) z).map_add]
  simp only [AddChar.map_add_eq_mul, PiLp.smul_apply, phase_apply,
    shift_apply, smul_eq_mul]
  ring

/-- Algebraically orthogonal X/Z words give commuting actual operators. -/
theorem shift_comm_phase_of_pairing_zero
    (x z : Word F ι)
    (horth : wordPairing (F := F) (ι := ι) z x = 0) :
    shift x * phase z = phase z * shift x := by
  rw [shift_mul_phase, horth]
  simp [character]

/-- Boundary-squared makes actual arbitrary-field CSS row checks commute. -/
theorem chainComplex_cssChecks_commute
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (x z : Word F ι)
    (hx : x ∈ K.firstCoboundaryCheckCode.carrier)
    (hz : z ∈ K.middleBoundaryCode.carrier) :
    shift x * phase z = phase z * shift x := by
  apply shift_comm_phase_of_pairing_zero
  exact (LinearCode.mem_dual K.firstCoboundaryCheckCode z).1
    (K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual hz) x hx

/-- The actual common fixed subspace of every X and Z check codeword. -/
def cssCarrier (xCode zCode : LinearCode F ι) :
    Submodule Complex (Register F ι) :=
  (⨅ x : xCode.carrier, LinearMap.ker (shift x.1 - 1)) ⊓
    (⨅ z : zCode.carrier, LinearMap.ker (phase z.1 - 1))

/-- The finite-field CSS code as a literal quantum subspace. -/
def cssQuantumCode (xCode zCode : LinearCode F ι) :
    Semantics.QuantumCode (Register F ι) where
  carrier := cssCarrier xCode zCode

/-- Membership in the CSS carrier is exactly simultaneous X/Z fixedness. -/
theorem mem_cssQuantumCode_iff (xCode zCode : LinearCode F ι)
    (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode xCode zCode).carrier ↔
      (∀ x : Word F ι, x ∈ xCode.carrier → shift x ψ = ψ) ∧
      (∀ z : Word F ι, z ∈ zCode.carrier → phase z ψ = ψ) := by
  simp [cssQuantumCode, cssCarrier, LinearMap.mem_ker, sub_eq_zero]

/-- For a finite chain complex it is enough to impose the scalar multiples of
individual boundary rows. These finite elementary X/Z checks have exactly the
same common fixed space as all words in the two CSS check codes. -/
theorem mem_chainComplex_cssQuantumCode_iff_elementaryChecks
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode
      K.firstCoboundaryCheckCode K.middleBoundaryCode).carrier ↔
      (∀ (k : κ₀) (a : F),
        shift (wordLinearMapTranspose K.boundary1
          (a • canonicalBasisWord k)) ψ = ψ) ∧
      (∀ (k : κ₂) (a : F),
        phase (K.boundary2 (a • canonicalBasisWord k)) ψ = ψ) := by
  constructor
  · intro hψ
    obtain ⟨hX, hZ⟩ := (mem_cssQuantumCode_iff
      K.firstCoboundaryCheckCode K.middleBoundaryCode ψ).1 hψ
    constructor
    · intro k a
      apply hX
      exact (K.mem_firstCoboundaryCheckCode_iff _).2
        ⟨a • canonicalBasisWord k, rfl⟩
    · intro k a
      apply hZ
      exact (K.mem_middleBoundaryCode_iff _).2
        ⟨a • canonicalBasisWord k, rfl⟩
  · rintro ⟨hX, hZ⟩
    apply (mem_cssQuantumCode_iff
      K.firstCoboundaryCheckCode K.middleBoundaryCode ψ).2
    constructor
    · intro x hx
      obtain ⟨y, rfl⟩ := (K.mem_firstCoboundaryCheckCode_iff x).1 hx
      exact shift_linearMap_fixed_of_canonicalBasis
        (wordLinearMapTranspose K.boundary1) ψ hX y
    · intro z hz
      obtain ⟨y, rfl⟩ := (K.mem_middleBoundaryCode_iff z).1 hz
      exact phase_linearMap_fixed_of_canonicalBasis K.boundary2 ψ hZ y

/-- The unnormalized indicator ket of a coset of the X-check code. -/
def cosetKet (xCode : LinearCode F ι) (a : Word F ι) : Register F ι := by
  classical
  exact WithLp.toLp 2 (fun η => if η - a ∈ xCode.carrier then 1 else 0)

@[simp] theorem cosetKet_apply (xCode : LinearCode F ι) (a η : Word F ι) :
    cosetKet xCode a η = if η - a ∈ xCode.carrier then 1 else 0 := by
  classical
  rfl

/-- Every X-check shift fixes a coset indicator ket. -/
theorem shift_cosetKet (xCode : LinearCode F ι) (a x : Word F ι)
    (hx : x ∈ xCode.carrier) :
    shift x (cosetKet xCode a) = cosetKet xCode a := by
  classical
  ext η
  rw [shift_apply, cosetKet_apply, cosetKet_apply]
  have hrewrite : η + x - a = (η - a) + x := by abel
  rw [hrewrite]
  have hmem : (η - a) + x ∈ xCode.carrier ↔ η - a ∈ xCode.carrier := by
    constructor
    · intro h
      have : (η - a) + x - x ∈ xCode.carrier := xCode.carrier.sub_mem h hx
      simpa using this
    · exact fun h => xCode.carrier.add_mem h hx
  by_cases h : η - a ∈ xCode.carrier <;> simp [h, hmem]

/-- Orthogonal Z checks fix a coset indicator whose label is Z-orthogonal. -/
theorem phase_cosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (a : Word F ι) (ha : a ∈ zCode.dual.carrier)
    (z : Word F ι) (hz : z ∈ zCode.carrier) :
    phase z (cosetKet xCode a) = cosetKet xCode a := by
  ext η
  rw [phase_apply, cosetKet_apply]
  by_cases hu : η - a ∈ xCode.carrier
  · have huPair : wordPairing (F := F) (ι := ι) z (η - a) = 0 :=
      zCode.dual_orthogonal hz (horth hu)
    have haPair : wordPairing (F := F) (ι := ι) z a = 0 :=
      zCode.dual_orthogonal hz ha
    have hη : η = (η - a) + a := by abel
    have hpair : wordPairing (F := F) (ι := ι) z η = 0 := by
      conv_lhs => rw [hη]
      rw [(wordPairing (F := F) (ι := ι) z).map_add, huPair, haPair]
      simp
    simp [hu, hpair, character]
  · simp [hu]

/-- A Z-Pauli commuting with X checks is diagonal on the X-coset states. -/
theorem phase_cosetKet_eigen (xCode : LinearCode F ι)
    (z a : Word F ι) (hz : z ∈ xCode.dual.carrier) :
    phase z (cosetKet xCode a) =
      (character F (wordPairing (F := F) (ι := ι) z a)) • cosetKet xCode a := by
  classical
  ext η
  rw [phase_apply, PiLp.smul_apply, cosetKet_apply]
  by_cases hu : η - a ∈ xCode.carrier
  · have hpair : wordPairing (F := F) (ι := ι) z (η - a) = 0 :=
      xCode.orthogonal_of_mem_dual hz hu
    have hη : η = (η - a) + a := by abel
    conv_lhs => rw [hη]
    rw [(wordPairing (F := F) (ι := ι) z).map_add, hpair]
    simp [hu, smul_eq_mul]
  · simp [hu, smul_eq_mul]

/-- An arbitrary X-Pauli translates the label of each X-coset indicator. -/
theorem shift_cosetKet_translate (xCode : LinearCode F ι)
    (a x : Word F ι) :
    shift x (cosetKet xCode a) = cosetKet xCode (a - x) := by
  classical
  ext η
  rw [shift_apply, cosetKet_apply, cosetKet_apply]
  have hrewrite : η + x - a = η - (a - x) := by abel
  rw [hrewrite]

/-- The normal-ordered finite-field Pauli operator. -/
def pauli (x z : Word F ι) : Semantics.Operator (Register F ι) :=
  shift x * phase z

/-- A normal-ordered Pauli acts on X-coset states by phase and translation. -/
theorem pauli_cosetKet (xCode : LinearCode F ι)
    (x z a : Word F ι) (hz : z ∈ xCode.dual.carrier) :
    pauli x z (cosetKet xCode a) =
      (character F (wordPairing (F := F) (ι := ι) z a)) •
        cosetKet xCode (a - x) := by
  rw [pauli, Module.End.mul_apply, phase_cosetKet_eigen xCode z a hz,
    map_smul, shift_cosetKet_translate]

@[simp] theorem pauli_apply (x z : Word F ι) (ψ : Register F ι)
    (η : Word F ι) :
    pauli x z ψ η =
      character F (wordPairing (F := F) (ι := ι) z (η + x)) * ψ (η + x) :=
  rfl

/-- Matrix entries grouped by the additive displacement between row and column. -/
def matrixDiagonal (E : Semantics.Operator (Register F ι))
    (x b : Word F ι) : Complex :=
  E (EuclideanSpace.basisFun (Word F ι) Complex b) (b - x)

/-- A Pauli occupies exactly one matrix displacement, with character entries. -/
theorem matrixDiagonal_pauli (x x' z b : Word F ι) :
    matrixDiagonal (pauli x z) x' b =
      if x' = x then character F (wordPairing (F := F) (ι := ι) z b)
      else 0 := by
  classical
  simp only [matrixDiagonal, pauli_apply, EuclideanSpace.basisFun_apply]
  by_cases h : x' = x
  · subst x'
    simp
  · have hneq : b - x' + x ≠ b := by
      intro heq
      apply h
      calc
        x' = b + x - (b - x' + x) := by abel
        _ = x := by rw [heq]; abel
    simp [h, hneq]

/-- Displacement-indexed matrix entries determine a finite register operator. -/
theorem matrixDiagonal_ext
    {E G : Semantics.Operator (Register F ι)}
    (h : ∀ x b : Word F ι, matrixDiagonal E x b = matrixDiagonal G x b) :
    E = G := by
  apply (EuclideanSpace.basisFun (Word F ι) Complex).toBasis.ext
  intro b
  ext η
  have hentry := h (b - η) b
  simpa [matrixDiagonal, show b - (b - η) = η by abel] using hentry

set_option maxHeartbeats 1000000 in
/-- A tensor-local operator has no matrix displacement outside its selected sites. -/
theorem matrixDiagonal_localOperator_eq_zero
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x b : Word F ι')
    (houtside : ∃ j : ι', j ∉ S.selected ∧ x j ≠ 0) :
    matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b = 0 := by
  obtain ⟨j, hj, hx⟩ := houtside
  have hdiff : ∃ j : ι', j ∉ S.selected ∧ (b - x) j ≠ b j := by
    refine ⟨j, hj, ?_⟩
    intro heq
    apply hx
    have heq' : b j - x j = b j := by simpa using heq
    exact sub_eq_self.mp heq'
  have hzero := Semantics.FiniteAlphabet.localOperator_basis_inner_eq_zero
    S E (b - x) b hdiff
  simpa [matrixDiagonal, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left] using hzero

set_option maxHeartbeats 1000000 in
/-- The matrix diagonal of a tensor-local operator in native field coordinates. -/
def localMatrixDiagonal
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x b : Word F ι') : Complex :=
  matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b

set_option maxHeartbeats 1000000 in
/-- A local operator's matrix diagonal is unchanged by shifting input labels outside its region. -/
theorem matrixDiagonal_localOperator_translate_of_x_inside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x t b : Word F ι')
    (hx : ∀ j : ι', j ∉ S.selected → x j = 0)
    (ht : ∀ j : ι', j ∈ S.selected → t j = 0) :
    localMatrixDiagonal S E x (b + t) = localMatrixDiagonal S E x b := by
  let L := Semantics.FiniteAlphabet.labelEquiv F ι'
  have hselected (y : Word F ι') :
      (S.splitLabel (L (y + t))).1 = (S.splitLabel (L y)).1 := by
    funext j
    have hj := ht j.1 j.2
    simp [Semantics.QuditSubsystem.splitLabel, L,
      Semantics.FiniteAlphabet.labelEquiv, hj]
  have hcomplement (y : Word F ι') :
      (S.splitLabel (L (y - x))).2 = (S.splitLabel (L y)).2 := by
    funext j
    have hj := hx j.1 j.2
    simp [Semantics.QuditSubsystem.splitLabel, L,
      Semantics.FiniteAlphabet.labelEquiv, hj]
  have hword : b + t - x = (b - x) + t := by abel
  have hform (y : Word F ι') :
      localMatrixDiagonal S E x y =
        inner Complex
            (EuclideanSpace.basisFun _ Complex (S.splitLabel (L (y - x))).1)
            (E (EuclideanSpace.basisFun _ Complex (S.splitLabel (L y)).1)) *
          inner Complex
            (EuclideanSpace.basisFun _ Complex (S.splitLabel (L (y - x))).2)
            (EuclideanSpace.basisFun _ Complex (S.splitLabel (L y)).2) := by
    simpa [localMatrixDiagonal, matrixDiagonal, L, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left] using
      (Semantics.FiniteAlphabet.localOperator_basis_inner S E (y - x) y)
  rw [hform (b + t), hform b,
    hcomplement (b + t), hcomplement b,
    hword, hselected (b - x), hselected b]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

set_option maxHeartbeats 1000000 in
/-- For an inside-region X displacement, every outside-region Z Fourier mode vanishes. -/
theorem localFourierCoefficient_eq_zero_of_z_outside_of_x_inside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι')
    (hx : ∀ j : ι', j ∉ S.selected → x j = 0)
    (hz : ∃ j : ι', j ∉ S.selected ∧ z j ≠ 0) :
    (wordCharacterBasis (F := F) (ι := ι')).repr
      (fun b => localMatrixDiagonal S E x b) z = 0 := by
  obtain ⟨j, hj, hzj⟩ := hz
  obtain ⟨s, hs⟩ := exists_character_mul_ne_one (z j) hzj
  let t : Word F ι' := Pi.single j s
  have ht : ∀ i : ι', i ∈ S.selected → t i = 0 := by
    intro i hi
    have hij : i ≠ j := by
      intro heq
      exact hj (heq ▸ hi)
    simp [t, hij]
  have hchar : character F (wordPairing (F := F) (ι := ι') z t) ≠ 1 := by
    simpa [t, wordPairing_apply, dotProduct_single] using hs
  have hinv : wordTranslate t (fun b : Word F ι' => localMatrixDiagonal S E x b) =
      (fun b : Word F ι' => localMatrixDiagonal S E x b) := by
    funext b
    exact matrixDiagonal_localOperator_translate_of_x_inside S E x t b hx ht
  exact wordCharacterBasis_repr_eq_zero_of_translate_invariant
    (fun b => localMatrixDiagonal S E x b) t z hinv hchar

@[simp] theorem matrixDiagonal_sum {α : Type*} (s : Finset α)
    (E : α → Semantics.Operator (Register F ι)) (x b : Word F ι) :
    matrixDiagonal (∑ a ∈ s, E a) x b =
      ∑ a ∈ s, matrixDiagonal (E a) x b := by
  simp [matrixDiagonal]

@[simp] theorem matrixDiagonal_smul (c : Complex)
    (E : Semantics.Operator (Register F ι)) (x b : Word F ι) :
    matrixDiagonal (c • E) x b = c * matrixDiagonal E x b := by
  simp [matrixDiagonal, smul_eq_mul]

/-- Fourier coefficient of one additive-displacement diagonal of an operator. -/
def pauliFourierCoefficient
    (E : Semantics.Operator (Register F ι))
    (x z : Word F ι) : Complex :=
  (wordCharacterBasis (F := F) (ι := ι)).repr
    (fun b => matrixDiagonal E x b) z

set_option maxHeartbeats 1000000 in
/-- Tensor-local operators have no Pauli Fourier displacement outside the region. -/
theorem pauliFourierCoefficient_localOperator_eq_zero_of_x_outside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι')
    (houtside : ∃ j : ι', j ∉ S.selected ∧ x j ≠ 0) :
    (wordCharacterBasis (F := F) (ι := ι')).repr
      (fun b => matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b) z = 0 := by
  have hzero : (fun b : Word F ι' =>
      matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b) = 0 := by
    funext b
    exact matrixDiagonal_localOperator_eq_zero S E x b houtside
  have hrepr := congrArg
    (fun f : Word F ι' → Complex =>
      (wordCharacterBasis (F := F) (ι := ι')).repr f z) hzero
  simpa only [map_zero, Finsupp.zero_apply] using hrepr

set_option maxHeartbeats 1000000 in
/-- Every Fourier mode of a tensor-local operator is supported inside its region. -/
theorem localFourierCoefficient_eq_zero_of_outside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι')
    (houtside : (∃ j : ι', j ∉ S.selected ∧ x j ≠ 0) ∨
      (∃ j : ι', j ∉ S.selected ∧ z j ≠ 0)) :
    (wordCharacterBasis (F := F) (ι := ι')).repr
      (fun b => localMatrixDiagonal S E x b) z = 0 := by
  rcases houtside with hxoutside | hzoutside
  · simpa only [localMatrixDiagonal] using
      pauliFourierCoefficient_localOperator_eq_zero_of_x_outside
        S E x z hxoutside
  · by_cases hxinside : ∀ j : ι', j ∉ S.selected → x j = 0
    · exact localFourierCoefficient_eq_zero_of_z_outside_of_x_inside
        S E x z hxinside hzoutside
    · push Not at hxinside
      simpa only [localMatrixDiagonal] using
        pauliFourierCoefficient_localOperator_eq_zero_of_x_outside
          S E x z hxinside

/-- Expand each matrix diagonal in its finite-field character basis. -/
def pauliFourierReconstruction
    (E : Semantics.Operator (Register F ι)) :
    Semantics.Operator (Register F ι) :=
  ∑ x : Word F ι, ∑ z : Word F ι,
    pauliFourierCoefficient E x z • pauli x z

/-- Every finite register operator is a linear combination of field Paulis. -/
theorem pauliFourierReconstruction_eq
    (E : Semantics.Operator (Register F ι)) :
    pauliFourierReconstruction E = E := by
  apply matrixDiagonal_ext
  intro x b
  have hrepr := congrFun
    ((wordCharacterBasis (F := F) (ι := ι)).sum_repr
      (fun b => matrixDiagonal E x b)) b
  simp only [Fintype.sum_apply, Pi.smul_apply, wordCharacterBasis_apply,
    smul_eq_mul] at hrepr
  simpa [pauliFourierReconstruction, pauliFourierCoefficient,
    matrixDiagonal_pauli] using hrepr

/-- Detectability is preserved by a complex scalar multiple. -/
theorem detectableOn_smul
    (C : Semantics.QuantumCode (Register F ι))
    (E : Semantics.Operator (Register F ι)) (a : Complex)
    (hE : Semantics.DetectableOn C E) :
    Semantics.DetectableOn C (a • E) := by
  obtain ⟨c, hc⟩ := hE
  refine ⟨a * c, ?_⟩
  intro u hu v hv
  change inner Complex u (a • E v) = (a * c) * inner Complex u v
  rw [inner_smul_right, hc u hu v hv]
  ring

/-- Detectability is preserved by adding two operators. -/
theorem detectableOn_add
    (C : Semantics.QuantumCode (Register F ι))
    (E G : Semantics.Operator (Register F ι))
    (hE : Semantics.DetectableOn C E)
    (hG : Semantics.DetectableOn C G) :
    Semantics.DetectableOn C (E + G) := by
  obtain ⟨a, ha⟩ := hE
  obtain ⟨b, hb⟩ := hG
  refine ⟨a + b, ?_⟩
  intro u hu v hv
  change inner Complex u (E v + G v) = (a + b) * inner Complex u v
  rw [inner_add_right, ha u hu v hv, hb u hu v hv]
  ring

/-- Detectability is preserved by a finite operator sum. -/
theorem detectableOn_sum {α : Type*}
    (C : Semantics.QuantumCode (Register F ι))
    (s : Finset α) (E : α → Semantics.Operator (Register F ι))
    (hE : ∀ a ∈ s, Semantics.DetectableOn C (E a)) :
    Semantics.DetectableOn C (∑ a ∈ s, E a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro u hu v hv
      simp
  | @insert a s has ih =>
      simp only [Finset.sum_insert has]
      exact detectableOn_add C (E a) (∑ b ∈ s, E b)
        (hE a (Finset.mem_insert_self a s))
        (ih (fun b hb => hE b (Finset.mem_insert_of_mem hb)))

/-- Translation of computational labels preserves the register inner product. -/
theorem inner_shift_shift (t : Word F ι) (u v : Register F ι) :
    inner Complex (shift t u) (shift t v) = inner Complex u v := by
  simp only [PiLp.inner_apply, shift_apply]
  exact Equiv.sum_comp (Equiv.addRight t)
    (fun η : Word F ι => inner Complex (u η) (v η))

/-- Translating a Pauli output exposes exactly its character commutator. -/
theorem shift_pauli (t x z : Word F ι) (ψ : Register F ι) :
    shift t (pauli x z ψ) =
      (character F (wordPairing (F := F) (ι := ι) z t)) •
        pauli x z (shift t ψ) := by
  ext η
  rw [shift_apply, pauli_apply, PiLp.smul_apply, pauli_apply,
    shift_apply]
  have hword : η + t + x = (η + x) + t := by abel
  rw [hword, (wordPairing (F := F) (ι := ι) z).map_add]
  simp only [AddChar.map_add_eq_mul, smul_eq_mul]
  ring

/-- A nonzero amplitude fixed by every Z check has a dual-code label. -/
theorem label_mem_dual_of_phase_fixed (zCode : LinearCode F ι)
    (ψ : Register F ι)
    (hfixed : ∀ z : Word F ι, z ∈ zCode.carrier → phase z ψ = ψ)
    (η : Word F ι) (hψ : ψ η ≠ 0) :
    η ∈ zCode.dual.carrier := by
  apply (zCode.mem_dual η).2
  intro z hz
  have hpair : wordPairing (F := F) (ι := ι) z η = 0 := by
    by_contra hne
    obtain ⟨t, ht⟩ := exists_character_mul_ne_one
      (wordPairing (F := F) (ι := ι) z η) hne
    have hscaled : t • z ∈ zCode.carrier := zCode.carrier.smul_mem t hz
    have hvalue := congrArg (fun φ : Register F ι => φ η)
      (hfixed (t • z) hscaled)
    rw [phase_apply] at hvalue
    have hpairscaled : wordPairing (F := F) (ι := ι) (t • z) η =
        wordPairing (F := F) (ι := ι) z η * t := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
    rw [hpairscaled] at hvalue
    have hchar : character F (wordPairing (F := F) (ι := ι) z η * t) = 1 := by
      apply mul_right_cancel₀ hψ
      simpa using hvalue
    exact ht hchar
  simpa [wordPairing_apply, dotProduct_comm] using hpair

/-- Fixedness under an X check is equality of amplitudes along that shift. -/
theorem apply_add_eq_of_shift_fixed (ψ : Register F ι)
    (x : Word F ι) (hfixed : shift x ψ = ψ) (η : Word F ι) :
    ψ (η + x) = ψ η := by
  have hvalue := congrArg (fun φ : Register F ι => φ η) hfixed
  simpa using hvalue

/-- The CSS carrier consists exactly of Z-dual-supported, X-coset-constant waves. -/
theorem mem_cssQuantumCode_iff_support_and_coset_constant
    (xCode zCode : LinearCode F ι) (ψ : Register F ι) :
    ψ ∈ (cssQuantumCode xCode zCode).carrier ↔
      (∀ η : Word F ι, η ∉ zCode.dual.carrier → ψ η = 0) ∧
      (∀ η x : Word F ι, x ∈ xCode.carrier → ψ (η + x) = ψ η) := by
  constructor
  · intro hψ
    obtain ⟨hX, hZ⟩ := (mem_cssQuantumCode_iff xCode zCode ψ).1 hψ
    constructor
    · intro η hη
      by_contra hnonzero
      exact hη (label_mem_dual_of_phase_fixed zCode ψ hZ η hnonzero)
    · intro η x hx
      exact apply_add_eq_of_shift_fixed ψ x (hX x hx) η
  · rintro ⟨hsupport, hconstant⟩
    apply (mem_cssQuantumCode_iff xCode zCode ψ).2
    constructor
    · intro x hx
      ext η
      exact hconstant η x hx
    · intro z hz
      ext η
      rw [phase_apply]
      by_cases hη : η ∈ zCode.dual.carrier
      · have hpair : wordPairing (F := F) (ι := ι) z η = 0 :=
          zCode.dual_orthogonal hz hη
        simp [hpair, character]
      · rw [hsupport η hη]
        simp

/-- Paulis in both CSS normalizer sectors preserve the actual code subspace. -/
theorem pauli_mem_cssQuantumCode (xCode zCode : LinearCode F ι)
    (x z : Word F ι)
    (hx : x ∈ zCode.dual.carrier)
    (hz : z ∈ xCode.dual.carrier)
    (ψ : Register F ι)
    (hψ : ψ ∈ (cssQuantumCode xCode zCode).carrier) :
    pauli x z ψ ∈ (cssQuantumCode xCode zCode).carrier := by
  obtain ⟨hsupport, hconstant⟩ :=
    (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode ψ).1 hψ
  apply (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode _).2
  constructor
  · intro η hη
    have hnot : η + x ∉ zCode.dual.carrier := by
      intro hsum
      have : (η + x) - x ∈ zCode.dual.carrier :=
        zCode.dual.carrier.sub_mem hsum hx
      exact hη (by simpa using this)
    simp [pauli_apply, hsupport (η + x) hnot]
  · intro η t ht
    have hpair : wordPairing (F := F) (ι := ι) z t = 0 :=
      xCode.orthogonal_of_mem_dual hz ht
    rw [pauli_apply, pauli_apply]
    have hword : η + t + x = (η + x) + t := by abel
    rw [hword, hconstant (η + x) t ht]
    rw [(wordPairing (F := F) (ι := ι) z).map_add, hpair]
    simp [character]

/-- Products of X and Z stabilizers act as the identity on the CSS carrier. -/
theorem pauli_eq_self_of_checks (xCode zCode : LinearCode F ι)
    (x z : Word F ι)
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier)
    (ψ : Register F ι) (hψ : ψ ∈ (cssQuantumCode xCode zCode).carrier) :
    pauli x z ψ = ψ := by
  obtain ⟨hX, hZ⟩ := (mem_cssQuantumCode_iff xCode zCode ψ).1 hψ
  rw [pauli, Module.End.mul_apply, hZ z hz, hX x hx]

/-- An X shift outside the Z-check normalizer has zero compression on the code. -/
theorem detectable_pauli_of_x_not_dual (xCode zCode : LinearCode F ι)
    (x z : Word F ι) (hx : x ∉ zCode.dual.carrier) :
    Semantics.DetectableOnWithScalar
      (cssQuantumCode xCode zCode) (pauli x z) 0 := by
  intro u hu v hv
  have hU :=
    (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode u).1 hu |>.1
  have hV :=
    (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode v).1 hv |>.1
  have hzero : inner Complex u (pauli x z v) = 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro η _
    by_cases hη : η ∈ zCode.dual.carrier
    · have hshift : η + x ∉ zCode.dual.carrier := by
        intro hsum
        have : (η + x) - η ∈ zCode.dual.carrier :=
          zCode.dual.carrier.sub_mem hsum hη
        exact hx (by simpa using this)
      rw [pauli_apply, hV (η + x) hshift]
      simp
    · rw [hU η hη]
      simp
  simpa using hzero

/-- A Z phase outside the X-check normalizer has zero compression on the code. -/
theorem detectable_pauli_of_z_not_dual (xCode zCode : LinearCode F ι)
    (x z : Word F ι) (hz : z ∉ xCode.dual.carrier) :
    Semantics.DetectableOnWithScalar
      (cssQuantumCode xCode zCode) (pauli x z) 0 := by
  obtain ⟨t, ht, hchar⟩ := exists_dual_character_ne_one xCode.dual z hz
  rw [dual_dual_carrier_eq] at ht
  intro u hu v hv
  have hU := (mem_cssQuantumCode_iff xCode zCode u).1 hu |>.1 t ht
  have hV := (mem_cssQuantumCode_iff xCode zCode v).1 hv |>.1 t ht
  have hfixed : inner Complex u (pauli x z v) =
      character F (wordPairing (F := F) (ι := ι) z t) *
        inner Complex u (pauli x z v) := by
    calc
      inner Complex u (pauli x z v) =
          inner Complex (shift t u) (shift t (pauli x z v)) :=
        (inner_shift_shift t u (pauli x z v)).symm
      _ = inner Complex u
          ((character F (wordPairing (F := F) (ι := ι) z t)) •
            pauli x z v) := by rw [hU, shift_pauli, hV]
      _ = character F (wordPairing (F := F) (ι := ι) z t) *
            inner Complex u (pauli x z v) := by simp
  have hzero : inner Complex u (pauli x z v) = 0 := by
    by_contra hnonzero
    have hcharOne : character F (wordPairing (F := F) (ι := ι) z t) = 1 :=
      mul_right_cancel₀ hnonzero (by simpa using hfixed.symm)
    exact hchar hcharOne
  simpa using hzero

/-- A detectable code-preserving operator has one scalar action on every code state. -/
theorem eq_smul_of_detectable_of_preserves
    (C : Semantics.QuantumCode (Register F ι))
    (E : Semantics.Operator (Register F ι))
    (hdetect : Semantics.DetectableOn C E)
    (hpreserve : ∀ ψ : Register F ι, ψ ∈ C.carrier → E ψ ∈ C.carrier) :
    ∃ c : Complex, ∀ ψ : Register F ι, ψ ∈ C.carrier → E ψ = c • ψ := by
  obtain ⟨c, hc⟩ := hdetect
  refine ⟨c, ?_⟩
  intro ψ hψ
  have hprojector := Semantics.projectorEquation_of_detectableOnWithScalar hc
  have hvalue := congrArg (fun A : Semantics.Operator (Register F ι) => A ψ) hprojector
  simpa [LinearMap.comp_apply, C.projector_eq_self_of_mem hψ,
    C.projector_eq_self_of_mem (hpreserve ψ hψ)] using hvalue

/-- Each Z-orthogonal X-coset provides an actual state in the CSS carrier. -/
theorem cosetKet_mem_cssQuantumCode (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (a : Word F ι) (ha : a ∈ zCode.dual.carrier) :
    cosetKet xCode a ∈ (cssQuantumCode xCode zCode).carrier := by
  rw [mem_cssQuantumCode_iff]
  constructor
  · intro x hx
    exact shift_cosetKet xCode a x hx
  · intro z hz
    exact phase_cosetKet xCode zCode horth a ha z hz

/-- A non-stabilizer X-normalizer Pauli is a genuine semantic logical operator. -/
theorem not_detectable_pauli_of_x_logical (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (x z : Word F ι)
    (hx : x ∈ zCode.dual.carrier) (hxnot : x ∉ xCode.carrier)
    (hz : z ∈ xCode.dual.carrier) :
    ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) := by
  intro hdetect
  obtain ⟨c, hc⟩ := eq_smul_of_detectable_of_preserves
    (cssQuantumCode xCode zCode) (pauli x z) hdetect
    (pauli_mem_cssQuantumCode xCode zCode x z hx hz)
  have hzero : (cosetKet xCode 0 : Register F ι) ∈
      (cssQuantumCode xCode zCode).carrier :=
    cosetKet_mem_cssQuantumCode xCode zCode horth 0
      zCode.dual.carrier.zero_mem
  have hvalue := congrArg (fun ψ : Register F ι => ψ (-x))
    (hc (cosetKet xCode 0) hzero)
  rw [pauli_cosetKet xCode x z 0 hz] at hvalue
  have hnot : -x ∉ xCode.carrier := by
    intro hneg
    exact hxnot (by simpa using xCode.carrier.neg_mem hneg)
  simp [cosetKet_apply, hnot, character] at hvalue

/-- A non-stabilizer Z-normalizer phase is a genuine semantic logical operator. -/
theorem not_detectable_phase_of_z_logical (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (z : Word F ι)
    (hz : z ∈ xCode.dual.carrier) (hznot : z ∉ zCode.carrier) :
    ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (phase z) := by
  intro hdetect
  obtain ⟨c, hc⟩ := eq_smul_of_detectable_of_preserves
    (cssQuantumCode xCode zCode) (phase z) hdetect (by
      intro ψ hψ
      simpa [pauli] using pauli_mem_cssQuantumCode xCode zCode 0 z
        zCode.dual.carrier.zero_mem hz ψ hψ)
  have hzero : (cosetKet xCode 0 : Register F ι) ∈
      (cssQuantumCode xCode zCode).carrier :=
    cosetKet_mem_cssQuantumCode xCode zCode horth 0
      zCode.dual.carrier.zero_mem
  have hvalue0 := congrArg (fun ψ : Register F ι => ψ 0)
    (hc (cosetKet xCode 0) hzero)
  rw [phase_cosetKet_eigen xCode z 0 hz] at hvalue0
  have hc_one : c = 1 := by
    simpa [cosetKet_apply, character] using hvalue0.symm
  obtain ⟨a, ha, hchar⟩ := exists_dual_character_ne_one zCode z hznot
  have hket : (cosetKet xCode a : Register F ι) ∈
      (cssQuantumCode xCode zCode).carrier :=
    cosetKet_mem_cssQuantumCode xCode zCode horth a ha
  have hvaluea := congrArg (fun ψ : Register F ι => ψ a)
    (hc (cosetKet xCode a) hket)
  rw [phase_cosetKet_eigen xCode z a hz] at hvaluea
  have hchar_eq : character F (wordPairing (F := F) (ι := ι) z a) = c := by
    simpa [cosetKet_apply] using hvaluea
  exact hchar (hchar_eq.trans hc_one)

/-- Every nontrivial Pauli in the CSS normalizer is semantically nondetectable. -/
theorem not_detectable_pauli_of_logical (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (x z : Word F ι)
    (hx : x ∈ zCode.dual.carrier) (hz : z ∈ xCode.dual.carrier)
    (hlogical : x ∉ xCode.carrier ∨ z ∉ zCode.carrier) :
    ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) := by
  rcases hlogical with hxnot | hznot
  · exact not_detectable_pauli_of_x_logical xCode zCode horth x z hx hxnot hz
  · by_cases hxcheck : x ∈ xCode.carrier
    · intro hdetect
      have hphase : Semantics.DetectableOn (cssQuantumCode xCode zCode)
          (phase z) := by
        obtain ⟨c, hc⟩ := hdetect
        refine ⟨c, ?_⟩
        intro u hu v hv
        have hphaseMem : phase z v ∈ (cssQuantumCode xCode zCode).carrier := by
          simpa [pauli] using pauli_mem_cssQuantumCode xCode zCode 0 z
            zCode.dual.carrier.zero_mem hz v hv
        have hX := (mem_cssQuantumCode_iff xCode zCode (phase z v)).1 hphaseMem |>.1
        have hsame : pauli x z v = phase z v := by
          rw [pauli, Module.End.mul_apply, hX x hxcheck]
        rw [← hsame]
        exact hc u hu v hv
      exact not_detectable_phase_of_z_logical xCode zCode horth z hz hznot hphase
    · exact not_detectable_pauli_of_x_logical xCode zCode horth x z hx hxcheck hz

/-- Exact semantic detectability criterion for arbitrary finite-field CSS Paulis. -/
theorem detectable_pauli_iff (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (x z : Word F ι) :
    Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) ↔
      x ∉ zCode.dual.carrier ∨ z ∉ xCode.dual.carrier ∨
        (x ∈ xCode.carrier ∧ z ∈ zCode.carrier) := by
  classical
  constructor
  · intro hdetect
    by_cases hx : x ∈ zCode.dual.carrier
    · by_cases hz : z ∈ xCode.dual.carrier
      · by_cases hxcheck : x ∈ xCode.carrier
        · by_cases hzcheck : z ∈ zCode.carrier
          · exact Or.inr (Or.inr ⟨hxcheck, hzcheck⟩)
          · exact False.elim ((not_detectable_pauli_of_logical xCode zCode
              horth x z hx hz (Or.inr hzcheck)) hdetect)
        · exact False.elim ((not_detectable_pauli_of_logical xCode zCode
            horth x z hx hz (Or.inl hxcheck)) hdetect)
      · exact Or.inr (Or.inl hz)
    · exact Or.inl hx
  · rintro (hx | hz | ⟨hx, hz⟩)
    · exact ⟨0, detectable_pauli_of_x_not_dual xCode zCode x z hx⟩
    · exact ⟨0, detectable_pauli_of_z_not_dual xCode zCode x z hz⟩
    · refine ⟨1, ?_⟩
      intro u hu v hv
      rw [pauli_eq_self_of_checks xCode zCode x z hx hz v hv]
      simp

/-- Coordinates on which a finite-field Pauli has an X or Z component. -/
def pauliSupport [DecidableEq F] (x z : Word F ι) : Finset ι := by
  classical
  exact hammingSupport x ∪ hammingSupport z

omit [Fintype F] in
/-- If a Pauli support escapes a region, some X or Z coordinate escapes it. -/
theorem pauliSupport_not_subset_iff_outside [DecidableEq F]
    (x z : Word F ι) (S : Finset ι) :
    ¬ pauliSupport x z ⊆ S ↔
      (∃ j : ι, j ∉ S ∧ x j ≠ 0) ∨
        (∃ j : ι, j ∉ S ∧ z j ≠ 0) := by
  classical
  simp only [Finset.not_subset, pauliSupport, Finset.mem_union,
    hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, (hx | hz), hj⟩
    · exact Or.inl ⟨j, hj, hx⟩
    · exact Or.inr ⟨j, hj, hz⟩
  · rintro (⟨j, hj, hx⟩ | ⟨j, hj, hz⟩)
    · exact ⟨j, Or.inl hx, hj⟩
    · exact ⟨j, Or.inr hz, hj⟩

set_option maxHeartbeats 1000000 in
/-- A tensor-local operator has no Pauli coefficient whose support leaves the region. -/
theorem pauliFourierCoefficient_localOperator_eq_zero_of_support_not_subset
    {ι' : Type u} [Fintype ι'] [DecidableEq ι'] [DecidableEq F]
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι') (houtside : ¬ pauliSupport x z ⊆ S.selected) :
    pauliFourierCoefficient (Semantics.FiniteAlphabet.localOperator S E) x z = 0 := by
  have houtside' := (pauliSupport_not_subset_iff_outside x z S.selected).mp houtside
  exact localFourierCoefficient_eq_zero_of_outside S E x z houtside'

omit [Fintype F] in
/-- A Pauli's X word weight is bounded by its total coordinate support. -/
theorem hammingWeight_x_le_pauliSupport [DecidableEq F]
    (x z : Word F ι) :
    HammingWeight x ≤ (pauliSupport x z).card := by
  exact Finset.card_le_card Finset.subset_union_left

omit [Fintype F] in
/-- A Pauli's Z word weight is bounded by its total coordinate support. -/
theorem hammingWeight_z_le_pauliSupport [DecidableEq F]
    (x z : Word F ι) :
    HammingWeight z ≤ (pauliSupport x z).card := by
  exact Finset.card_le_card Finset.subset_union_right

/-- Algebraic CSS distance lower-bounds every nondetectable finite-field Pauli. -/
theorem pauliSupport_card_ge_of_not_detectable
    [DecidableEq F] (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d)
    (x z : Word F ι)
    (hnot : ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z)) :
    d ≤ (pauliSupport x z).card := by
  have hx : x ∈ zCode.dual.carrier := by
    by_contra h
    exact hnot ((detectable_pauli_iff xCode zCode horth x z).2 (Or.inl h))
  have hz : z ∈ xCode.dual.carrier := by
    by_contra h
    exact hnot ((detectable_pauli_iff xCode zCode horth x z).2
      (Or.inr (Or.inl h)))
  have hlogical : x ∉ xCode.carrier ∨ z ∉ zCode.carrier := by
    by_contra h
    push Not at h
    exact hnot ((detectable_pauli_iff xCode zCode horth x z).2
      (Or.inr (Or.inr h)))
  obtain ⟨_, _, _, hleast⟩ := hminimum
  rcases hlogical with hxnot | hznot
  · exact (hleast x (Or.inl ⟨hx, hxnot⟩)).trans
      (hammingWeight_x_le_pauliSupport x z)
  · exact (hleast z (Or.inr ⟨hz, hznot⟩)).trans
      (hammingWeight_z_le_pauliSupport x z)

/-- The algebraic CSS minimum is attained by a nondetectable pure Pauli. -/
theorem exists_nondetectable_pauli_of_algebraicCSSMinimumDistance
    [DecidableEq F] (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    ∃ x z : Word F ι,
      ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) ∧
      (pauliSupport x z).card = d := by
  obtain ⟨a, ha, hweight, _⟩ := hminimum
  rcases ha with ⟨haDual, haNot⟩ | ⟨haDual, haNot⟩
  · refine ⟨a, 0, ?_, ?_⟩
    · exact not_detectable_pauli_of_logical xCode zCode horth a 0
        haDual xCode.dual.carrier.zero_mem (Or.inl haNot)
    · simpa [pauliSupport, hammingSupport, HammingWeight] using hweight
  · refine ⟨0, a, ?_, ?_⟩
    · exact not_detectable_pauli_of_logical xCode zCode horth 0 a
        zCode.dual.carrier.zero_mem haDual (Or.inr haNot)
    · simpa [pauliSupport, hammingSupport, HammingWeight] using hweight

set_option maxHeartbeats 1000000 in
/-- Algebraic CSS distance detects every operator on fewer than `d` field-symbol sites. -/
theorem detectableOn_localOperator_of_card_lt_algebraicCSSMinimumDistance
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d)
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (hcard : S.selected.card < d)
    (E : Semantics.Operator S.selectedSystem) :
    Semantics.DetectableOn (cssQuantumCode xCode zCode)
      (Semantics.FiniteAlphabet.localOperator S E) := by
  classical
  let L := Semantics.FiniteAlphabet.localOperator S E
  have hsum : Semantics.DetectableOn (cssQuantumCode xCode zCode)
      (pauliFourierReconstruction L) := by
    unfold pauliFourierReconstruction
    apply detectableOn_sum (cssQuantumCode xCode zCode) Finset.univ
    intro x _
    apply detectableOn_sum (cssQuantumCode xCode zCode) Finset.univ
    intro z _
    by_cases hsub : pauliSupport x z ⊆ S.selected
    · apply detectableOn_smul
      by_contra hnot
      have hd := pauliSupport_card_ge_of_not_detectable
        xCode zCode horth d hminimum x z hnot
      have hle := Finset.card_le_card hsub
      omega
    · have hzero :=
        pauliFourierCoefficient_localOperator_eq_zero_of_support_not_subset
          S E x z hsub
      change Semantics.DetectableOn (cssQuantumCode xCode zCode)
        (pauliFourierCoefficient
          (Semantics.FiniteAlphabet.localOperator S E) x z • pauli x z)
      rw [hzero, zero_smul]
      refine ⟨0, ?_⟩
      intro u hu v hv
      simp
  simpa only [pauliFourierReconstruction_eq] using hsum

/-- A coset indicator is nonzero because its center label has amplitude one. -/
theorem cosetKet_ne_zero (xCode : LinearCode F ι) (a : Word F ι) :
    cosetKet xCode a ≠ 0 := by
  intro hzero
  have hvalue := congrArg (fun ψ : Register F ι => ψ a) hzero
  simp [cosetKet_apply] at hvalue

/-- Different X-code cosets yield different physical indicator states. -/
theorem cosetKet_ne_of_sub_not_mem (xCode : LinearCode F ι)
    (a b : Word F ι) (hnot : a - b ∉ xCode.carrier) :
    cosetKet xCode a ≠ cosetKet xCode b := by
  intro heq
  have hvalue := congrArg (fun ψ : Register F ι => ψ a) heq
  simp [cosetKet_apply, hnot] at hvalue

/-- Distinct X-code cosets have disjoint computational-basis support. -/
theorem cosetKet_mul_eq_zero_of_sub_not_mem (xCode : LinearCode F ι)
    (a b η : Word F ι) (hnot : a - b ∉ xCode.carrier) :
    cosetKet xCode a η * cosetKet xCode b η = 0 := by
  by_cases ha : η - a ∈ xCode.carrier
  · have hb : η - b ∉ xCode.carrier := by
      intro hb
      apply hnot
      have hdiff : (η - b) - (η - a) = a - b := by abel
      rw [← hdiff]
      exact xCode.carrier.sub_mem hb ha
    simp [cosetKet_apply, ha, hb]
  · simp [cosetKet_apply, ha]

/-- One computational indicator state for each quotient coset. -/
def quotientCosetKet (xCode : LinearCode F ι)
    (q : Word F ι ⧸ xCode.carrier) : Register F ι :=
  cosetKet xCode (Quotient.out q)

/-- Evaluation at a representative distinguishes the quotient-coset indicators. -/
theorem quotientCosetKet_apply_out (xCode : LinearCode F ι)
    (q r : Word F ι ⧸ xCode.carrier) :
    quotientCosetKet xCode q (Quotient.out r) = if q = r then 1 else 0 := by
  classical
  rw [quotientCosetKet, cosetKet_apply]
  have hq : (Quotient.out r - Quotient.out q ∈ xCode.carrier) ↔ r = q := by
    rw [← Submodule.Quotient.eq]
    simp only [Submodule.Quotient.mk_out]
  simp only [hq, eq_comm]

/-- At any label, a quotient-coset indicator is the delta function of its coset. -/
theorem quotientCosetKet_apply (xCode : LinearCode F ι)
    (q : Word F ι ⧸ xCode.carrier) (η : Word F ι) :
    quotientCosetKet xCode q η =
      if q = Submodule.Quotient.mk η then 1 else 0 := by
  classical
  rw [quotientCosetKet, cosetKet_apply]
  have hq : (η - Quotient.out q ∈ xCode.carrier) ↔
      Submodule.Quotient.mk η = q := by
    rw [← Submodule.Quotient.eq]
    simp only [Submodule.Quotient.mk_out]
  simp only [hq, eq_comm]

/-- X-shift-invariant wavefunctions are reconstructed from their coset amplitudes. -/
theorem sum_quotientCosetKet_of_shift_fixed (xCode : LinearCode F ι)
    (ψ : Register F ι)
    (hfixed : ∀ η x : Word F ι, x ∈ xCode.carrier → ψ (η + x) = ψ η) :
    (∑ q : Word F ι ⧸ xCode.carrier,
      ψ (Quotient.out q) • quotientCosetKet xCode q) = ψ := by
  classical
  ext η
  have hrepresentative : ψ (Quotient.out (Submodule.Quotient.mk η :
      Word F ι ⧸ xCode.carrier)) = ψ η := by
    have hmem : Quotient.out (Submodule.Quotient.mk η :
        Word F ι ⧸ xCode.carrier) - η ∈ xCode.carrier := by
      apply (Submodule.Quotient.eq xCode.carrier).1
      exact (Submodule.Quotient.mk_out _).trans rfl
    have hrewrite : Quotient.out (Submodule.Quotient.mk η :
        Word F ι ⧸ xCode.carrier) =
        η + (Quotient.out (Submodule.Quotient.mk η :
          Word F ι ⧸ xCode.carrier) - η) := by abel
    conv_lhs => rw [hrewrite]
    exact hfixed η _ hmem
  simp [quotientCosetKet_apply, hrepresentative]

/-- Quotient cosets lying in the Z-check orthogonal code. -/
def AdmissibleCoset (xCode zCode : LinearCode F ι) :=
  {q : Word F ι ⧸ xCode.carrier // Quotient.out q ∈ zCode.dual.carrier}

instance instFintypeAdmissibleCoset (xCode zCode : LinearCode F ι) :
    Fintype (AdmissibleCoset xCode zCode) := by
  classical
  unfold AdmissibleCoset
  infer_instance

/-- Orthogonality makes membership in the Z-dual independent of a coset representative. -/
theorem out_mem_dual_iff (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (η : Word F ι) :
    Quotient.out (Submodule.Quotient.mk η : Word F ι ⧸ xCode.carrier)
      ∈ zCode.dual.carrier ↔ η ∈ zCode.dual.carrier := by
  have hmem : Quotient.out (Submodule.Quotient.mk η :
      Word F ι ⧸ xCode.carrier) - η ∈ zCode.dual.carrier := by
    apply horth
    apply (Submodule.Quotient.eq xCode.carrier).1
    exact (Submodule.Quotient.mk_out _).trans rfl
  constructor
  · intro h
    have : Quotient.out (Submodule.Quotient.mk η :
        Word F ι ⧸ xCode.carrier) -
        (Quotient.out (Submodule.Quotient.mk η :
          Word F ι ⧸ xCode.carrier) - η) ∈ zCode.dual.carrier :=
      zCode.dual.carrier.sub_mem h hmem
    simpa using this
  · intro h
    have : η + (Quotient.out (Submodule.Quotient.mk η :
        Word F ι ⧸ xCode.carrier) - η) ∈ zCode.dual.carrier :=
      zCode.dual.carrier.add_mem h hmem
    simpa using this

/-- An admissible coset indicator is a code state. -/
theorem admissibleCosetKet_mem_cssQuantumCode (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (q : AdmissibleCoset xCode zCode) :
    quotientCosetKet xCode q.1 ∈ (cssQuantumCode xCode zCode).carrier :=
  cosetKet_mem_cssQuantumCode xCode zCode horth (Quotient.out q.1) q.2

/-- Each admissible quotient coset as an element of the actual CSS codespace. -/
def admissibleCosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (q : AdmissibleCoset xCode zCode) :
    (cssQuantumCode xCode zCode).carrier :=
  ⟨quotientCosetKet xCode q.1,
    admissibleCosetKet_mem_cssQuantumCode xCode zCode horth q⟩

/-- Quotient-coset indicators are linearly independent as actual quantum states. -/
theorem quotientCosetKet_linearIndependent (xCode : LinearCode F ι) :
    LinearIndependent Complex (quotientCosetKet xCode) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have heval := congrArg (fun ψ : Register F ι => ψ (Quotient.out i)) hsum
  simpa [quotientCosetKet_apply_out, hi] using heval

/-- Admissible coset states remain independent inside the CSS carrier. -/
theorem admissibleCosetKet_linearIndependent (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    LinearIndependent Complex (admissibleCosetKet xCode zCode horth) := by
  apply LinearIndependent.of_comp
    ((cssQuantumCode xCode zCode).carrier.subtype)
  exact (quotientCosetKet_linearIndependent xCode).comp Subtype.val
    Subtype.val_injective

/-- Every CSS code state is a finite linear combination of admissible coset states. -/
theorem sum_admissibleCosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (ψ : (cssQuantumCode xCode zCode).carrier) :
    (∑ q : AdmissibleCoset xCode zCode,
      (ψ.1 (Quotient.out q.1)) • admissibleCosetKet xCode zCode horth q) = ψ := by
  classical
  apply Subtype.ext
  ext η
  have hsupport :=
    (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode ψ.1).1 ψ.2 |>.1
  by_cases hη : η ∈ zCode.dual.carrier
  · let qη : AdmissibleCoset xCode zCode :=
      ⟨Submodule.Quotient.mk η, (out_mem_dual_iff xCode zCode horth η).2 hη⟩
    have heq : ∀ q : AdmissibleCoset xCode zCode,
        (q.1 = Submodule.Quotient.mk η) ↔ q = qη := by
      intro q
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hconstant :=
      (mem_cssQuantumCode_iff_support_and_coset_constant xCode zCode ψ.1).1 ψ.2 |>.2
    have hrepr : ψ.1 (Quotient.out qη.1) = ψ.1 η := by
      have hmem : Quotient.out qη.1 - η ∈ xCode.carrier := by
        apply (Submodule.Quotient.eq xCode.carrier).1
        exact (Submodule.Quotient.mk_out _).trans rfl
      have hrewrite : Quotient.out qη.1 = η + (Quotient.out qη.1 - η) := by abel
      conv_lhs => rw [hrewrite]
      exact hconstant η _ hmem
    simp [admissibleCosetKet, quotientCosetKet_apply, heq, hrepr]
  · have hall : ∀ q : AdmissibleCoset xCode zCode,
        q.1 ≠ Submodule.Quotient.mk η := by
      intro q heq
      have hout : Quotient.out (Submodule.Quotient.mk η :
          Word F ι ⧸ xCode.carrier) ∈ zCode.dual.carrier := by
        rw [← heq]
        exact q.2
      exact hη ((out_mem_dual_iff xCode zCode horth η).1 hout)
    simp [admissibleCosetKet, quotientCosetKet_apply, hall, hsupport η hη]

/-- The admissible coset states span exactly the semantic CSS subspace. -/
theorem span_admissibleCosetKet (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    Submodule.span Complex (Set.range (admissibleCosetKet xCode zCode horth)) = ⊤ := by
  apply top_unique
  intro ψ _
  rw [← sum_admissibleCosetKet xCode zCode horth ψ]
  apply Submodule.sum_mem
  intro q _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q))

/-- A concrete orthogonal-coset basis for the arbitrary-field CSS codespace. -/
noncomputable def cssCosetBasis (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    Module.Basis (AdmissibleCoset xCode zCode) Complex
      (cssQuantumCode xCode zCode).carrier :=
  Module.Basis.mk (admissibleCosetKet_linearIndependent xCode zCode horth)
    (by rw [span_admissibleCosetKet xCode zCode horth])

/-- The physical CSS codespace dimension is the number of admissible cosets. -/
theorem cssQuantumCode_dimension_eq_card_cosets (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).dimension =
      Fintype.card (AdmissibleCoset xCode zCode) := by
  exact Module.finrank_eq_card_basis (cssCosetBasis xCode zCode horth)

/-- The X-check subspace, regarded as a subspace of the Z-orthogonal code. -/
def xWithinDual (xCode zCode : LinearCode F ι) :
    Submodule F zCode.dual.carrier :=
  xCode.carrier.comap zCode.dual.carrier.subtype

/-- A quotient of the Z-dual code maps to the corresponding admissible coset. -/
def dualQuotientToAdmissible (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (zCode.dual.carrier ⧸ xWithinDual xCode zCode) →
      AdmissibleCoset xCode zCode := by
  intro q
  refine Quotient.liftOn q (fun d =>
    ⟨Submodule.Quotient.mk d.1,
      (out_mem_dual_iff xCode zCode horth d.1).2 d.2⟩) ?_
  intro a b hab
  apply Subtype.ext
  apply (Submodule.Quotient.eq xCode.carrier).2
  have hmem := (Submodule.Quotient.eq (xWithinDual xCode zCode)).1
    (Quotient.sound hab)
  exact hmem

/-- The admissible cosets are exactly the quotient of Z-dual words by X checks. -/
noncomputable def admissibleCosetEquivDualQuotient (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (zCode.dual.carrier ⧸ xWithinDual xCode zCode) ≃
      AdmissibleCoset xCode zCode := by
  apply Equiv.ofBijective (dualQuotientToAdmissible xCode zCode horth)
  constructor
  · intro a b hab
    revert hab
    refine Quotient.inductionOn₂ a b ?_
    intro da db hab'
    apply (Submodule.Quotient.eq (xWithinDual xCode zCode)).2
    have heq : (Submodule.Quotient.mk da.1 : Word F ι ⧸ xCode.carrier) =
        Submodule.Quotient.mk db.1 := congrArg Subtype.val hab'
    exact (Submodule.Quotient.eq xCode.carrier).1 heq
  · intro q
    refine ⟨Submodule.Quotient.mk ⟨Quotient.out q.1, q.2⟩, ?_⟩
    apply Subtype.ext
    change (Submodule.Quotient.mk (Quotient.out q.1) :
      Word F ι ⧸ xCode.carrier) = q.1
    exact Submodule.Quotient.mk_out q.1

/-- The CSS codespace has the finite-field cardinal raised to its algebraic quotient rank. -/
theorem cssQuantumCode_dimension_eq_pow_quotient_finrank
    (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).dimension =
      (Fintype.card F) ^
        Module.finrank F (zCode.dual.carrier ⧸ xWithinDual xCode zCode) := by
  rw [cssQuantumCode_dimension_eq_card_cosets xCode zCode horth]
  rw [← Fintype.card_congr (admissibleCosetEquivDualQuotient xCode zCode horth)]
  exact Module.card_eq_pow_finrank

/-- A chain-complex CSS code encodes precisely its middle-cohomology rank. -/
theorem chainComplex_cssQuantumCode_dimension_eq_pow_cohomology
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    (cssQuantumCode K.firstCoboundaryCheckCode K.middleBoundaryCode).dimension =
      (Fintype.card F) ^ Module.finrank F K.middleCohomology := by
  rw [cssQuantumCode_dimension_eq_pow_quotient_finrank
    K.firstCoboundaryCheckCode K.middleBoundaryCode
    K.firstCoboundaryCheckCode_le_middleBoundaryCode_dual]
  exact congrArg ((Fintype.card F) ^ ·)
    K.pureXLogicalQuotientEquivMiddleCohomology.finrank_eq

/-- Finite chain complexes have equal middle homology and cohomology ranks. -/
theorem chainComplex_finrank_middleCohomology_eq_middleHomology
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    Module.finrank F K.middleCohomology = Module.finrank F K.middleHomology := by
  have hcoh := Submodule.finrank_quotient_add_finrank K.middleCoboundaryInCocycles
  have hcob : Module.finrank F K.middleCoboundaryInCocycles =
      Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hcohSum : Module.finrank F K.middleCohomology +
      Dimension K.firstCoboundaryCheckCode =
      Dimension K.middleCocycleCode := by
    rw [← hcob, Dimension_eq_finrank_carrier]
    exact hcoh
  have hhom := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  have hbound : Module.finrank F K.middleBoundaryInCycles =
      Dimension K.middleBoundaryCode := K.finrank_middleBoundaryInCycles_eq
  have hhomSum : Module.finrank F K.middleHomology +
      Dimension K.middleBoundaryCode = Dimension K.middleCycleCode := by
    rw [← hbound, Dimension_eq_finrank_carrier]
    exact hhom
  have hdualZ : Dimension K.middleCocycleCode +
      Dimension K.middleBoundaryCode = Length F ι := by
    have h := K.middleBoundaryCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.middleBoundaryCode.dual =
        Dimension K.middleCocycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
    omega
  have hdualX : Dimension K.middleCycleCode +
      Dimension K.firstCoboundaryCheckCode = Length F ι := by
    have h := K.firstCoboundaryCheckCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.firstCoboundaryCheckCode.dual =
        Dimension K.middleCycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    omega
  omega

/-- An orthogonal CSS pair has a genuinely nonzero semantic codespace. -/
theorem cssQuantumCode_carrier_ne_bot (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).carrier ≠ ⊥ := by
  intro hbot
  have hmem : cosetKet xCode 0 ∈ (cssQuantumCode xCode zCode).carrier :=
    cosetKet_mem_cssQuantumCode xCode zCode horth 0 zCode.dual.carrier.zero_mem
  rw [hbot] at hmem
  exact cosetKet_ne_zero xCode 0 (by simpa using hmem)

/-- A coordinatewise enumeration of finite-field labels by standard qudit labels. -/
def fieldLabelEquiv {ι' : Type u} [Fintype ι'] :
    Word F ι' ≃ Semantics.Qudit.Label (fun _ : ι' => Fintype.card F) :=
  Equiv.piCongrRight fun _ => Fintype.equivFin F

/-- The explicit basis relabelling from field symbols to standard qudits. -/
def registerUnitary {ι' : Type u} [Fintype ι'] :
    Semantics.UnitaryTransport (Register F ι')
      (Semantics.Qudit.QuditRegister (fun _ : ι' => Fintype.card F)) where
  toLinearEquiv := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (fieldLabelEquiv (F := F) (ι' := ι'))).toLinearEquiv
  map_inner := (LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (fieldLabelEquiv (F := F) (ι' := ι'))).inner_map_map

/-- Both finite-field label relabellings act identically on register vectors. -/
theorem registerUnitary_apply_eq_finiteAlphabet {ι' : Type u} [Fintype ι']
    [DecidableEq ι'] (ψ : Register F ι') :
    registerUnitary (F := F) ψ =
      Semantics.FiniteAlphabet.registerUnitary F ι' ψ := by
  rfl

/-- Inverse relabelling sends a standard basis ket back to its field label. -/
theorem registerUnitary_symm_apply_basis
    {ι' : Type u} [Fintype ι'] (a : Word F ι') :
    (registerUnitary (F := F) (ι' := ι')).symm
        (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex a := by
  change (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.symm
    (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) = _
  apply (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.injective
  rw [(registerUnitary (F := F) (ι' := ι')).toLinearEquiv.apply_symm_apply]
  exact (Semantics.FiniteAlphabet.registerUnitary_apply_basis F ι' a).symm

/-- Restrict a field word to the coordinates selected by a qudit region. -/
def restrictWordToRegion
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') : Word F S.SelectedCoordinates :=
  fun j => x j.1

/-- Restrict a field word to the complement of a selected region. -/
def restrictWordToComplement
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') : Word F S.ComplementCoordinates :=
  fun j => x j.1

omit [Field F] in
@[simp]
theorem splitLabel_fieldLabelEquiv_first
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') :
    (S.splitLabel (fieldLabelEquiv (F := F) x)).1 =
      fieldLabelEquiv (F := F) (restrictWordToRegion S x) := by
  rfl

omit [Field F] in
@[simp]
theorem splitLabel_fieldLabelEquiv_second
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') :
    (S.splitLabel (fieldLabelEquiv (F := F) x)).2 =
      fieldLabelEquiv (F := F) (restrictWordToComplement S x) := by
  rfl

/-- Restricting both words preserves their pairing when the first word
vanishes outside the selected region. -/
theorem wordPairing_restrictWordToRegion_eq
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (z a : Word F ι') (hz : ∀ j, j ∉ S.selected → z j = 0) :
    wordPairing (F := F) (ι := S.SelectedCoordinates)
        (restrictWordToRegion S z) (restrictWordToRegion S a) =
      wordPairing (F := F) (ι := ι') z a := by
  simp only [wordPairing_apply, dotProduct, restrictWordToRegion]
  let emb : S.SelectedCoordinates ↪ ι' := Function.Embedding.subtype _
  have hmap : Finset.univ.map emb = S.selected := by
    ext j
    simp [emb]
  calc
    (∑ j : S.SelectedCoordinates, z j.1 * a j.1) =
        ∑ j ∈ Finset.univ.map emb, z j * a j := by
      rw [Finset.sum_map]
      simp [emb]
    _ = ∑ j ∈ S.selected, z j * a j := by rw [hmap]
    _ = ∑ j : ι', z j * a j := by
      apply Finset.sum_subset (Finset.subset_univ S.selected)
      intro j _hj hjS
      simp [hz j hjS]

/-- The selected-register shift determined by a global field word. -/
def selectedShift
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') : Semantics.Operator S.selectedSystem where
  toFun ψ := WithLp.toLp 2 (fun labels =>
    ψ (fieldLabelEquiv (F := F)
      ((fieldLabelEquiv (F := F)).symm labels + restrictWordToRegion S x)))
  map_add' ψ φ := by ext labels; simp
  map_smul' c ψ := by ext labels; simp [smul_eq_mul]

/-- The selected-register phase determined by a global field word. -/
def selectedPhase
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (z : Word F ι') : Semantics.Operator S.selectedSystem where
  toFun ψ := WithLp.toLp 2 (fun labels =>
    character F (wordPairing (F := F) (ι := S.SelectedCoordinates)
      (restrictWordToRegion S z) ((fieldLabelEquiv (F := F)).symm labels)) *
        ψ labels)
  map_add' ψ φ := by ext labels; simp [mul_add]
  map_smul' c ψ := by ext labels; simp [smul_eq_mul, mul_left_comm]

/-- The selected shift translates the relabelled selected-coordinate basis. -/
theorem selectedShift_apply_basis
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') (a : Word F S.SelectedCoordinates) :
    selectedShift S x
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex
        (fieldLabelEquiv (F := F) (a - restrictWordToRegion S x)) := by
  ext labels
  simp only [selectedShift, LinearMap.coe_mk, AddHom.coe_mk,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  let E := fieldLabelEquiv (F := F) (ι' := S.SelectedCoordinates)
  let rx := restrictWordToRegion S x
  change (if E (E.symm labels + rx) = E a then 1 else 0) =
    if labels = E (a - rx) then 1 else 0
  have hiff : E (E.symm labels + rx) = E a ↔ labels = E (a - rx) := by
    constructor
    · intro h
      have hField : E.symm labels + rx = a := E.injective h
      apply E.symm.injective
      simp only [Equiv.symm_apply_apply]
      exact funext fun j => eq_sub_of_add_eq (congrFun hField j)
    · intro h
      subst labels
      simpa only [Equiv.symm_apply_apply] using congrArg E (sub_add_cancel a rx)
  simp only [hiff]

/-- The selected phase is diagonal in the relabelled selected-coordinate basis. -/
theorem selectedPhase_apply_basis
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (z : Word F ι') (a : Word F S.SelectedCoordinates) :
    selectedPhase S z
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) a)) =
      (character F (wordPairing (F := F) (ι := S.SelectedCoordinates)
        (restrictWordToRegion S z) a)) •
        EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a) := by
  ext labels
  simp only [selectedPhase, LinearMap.coe_mk, AddHom.coe_mk,
    EuclideanSpace.basisFun_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : labels = fieldLabelEquiv (F := F) a
  · subst labels
    simp
  · simp [h]

set_option maxRecDepth 4096 in
/-- Extending the selected shift by identity gives the global field shift
after field-to-qudit relabelling whenever the word vanishes off the selected
region. -/
theorem extendLocalToRegister_selectedShift
    {ι' : Type u} [Fintype ι']
    (S : @Semantics.QuditSubsystem ι' inferInstance (Classical.decEq ι')
      (fun _ : ι' => Fintype.card F))
    (x : Word F ι') (hx : ∀ j, j ∉ S.selected → x j = 0) :
    S.extendLocalToRegister (selectedShift S x) =
      (registerUnitary (F := F) (ι' := ι')).conjOperator (shift x) := by
  let _ : DecidableEq ι' := Classical.decEq ι'
  apply (EuclideanSpace.basisFun
    (Semantics.Qudit.Label (fun _ : ι' => Fintype.card F)) Complex).toBasis.ext
  intro labels
  let a : Word F ι' := (fieldLabelEquiv (F := F)).symm labels
  have hlabels : labels = fieldLabelEquiv (F := F) a := by
    exact ((fieldLabelEquiv (F := F)).apply_symm_apply labels).symm
  rw [hlabels]
  change S.extendLocalToRegister (selectedShift S x)
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
    (registerUnitary (F := F) (ι' := ι')).conjOperator (shift x)
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a))
  unfold Semantics.QuditSubsystem.extendLocalToRegister
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  simp only [Semantics.UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.symm_symm]
  rw [
    S.registerFactorization_apply_basis,
    splitLabel_fieldLabelEquiv_first,
    splitLabel_fieldLabelEquiv_second,
    S.extendLocal_apply_tmul,
    selectedShift_apply_basis]
  change S.registerFactorization.symm
      ((EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F)
            (restrictWordToRegion S a - restrictWordToRegion S x))) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) (restrictWordToComplement S a)))) = _
  have hfactor := S.registerFactorization_symm_apply_basis
    (fieldLabelEquiv (F := F)
        (restrictWordToRegion S a - restrictWordToRegion S x),
      fieldLabelEquiv (F := F) (restrictWordToComplement S a))
  change S.registerFactorization.symm.toLinearEquiv
      ((EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F)
            (restrictWordToRegion S a - restrictWordToRegion S x))) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) (restrictWordToComplement S a)))) = _
  rw [hfactor]
  have hLabel : S.recombineLabel
      (fieldLabelEquiv (F := F)
          (restrictWordToRegion S a - restrictWordToRegion S x),
        fieldLabelEquiv (F := F) (restrictWordToComplement S a)) =
      fieldLabelEquiv (F := F) (a - x) := by
    funext j
    by_cases hj : j ∈ S.selected
    · simp [Semantics.QuditSubsystem.recombineLabel, hj,
        restrictWordToRegion, fieldLabelEquiv]
    · simp [Semantics.QuditSubsystem.recombineLabel, hj,
        restrictWordToComplement, fieldLabelEquiv, hx j hj]
  rw [hLabel]
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  have hinv : (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.symm
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex a := by
    change (registerUnitary (F := F) (ι' := ι')).symm
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) = _
    exact registerUnitary_symm_apply_basis (F := F) a
  rw [hinv, shift_basis]
  exact (Semantics.FiniteAlphabet.registerUnitary_apply_basis F ι' (a - x)).symm

set_option maxRecDepth 4096 in
/-- Extending the selected phase by identity gives the global field phase
after field-to-qudit relabelling whenever the word vanishes off the selected
region. -/
theorem extendLocalToRegister_selectedPhase
    {ι' : Type u} [Fintype ι']
    (S : @Semantics.QuditSubsystem ι' inferInstance (Classical.decEq ι')
      (fun _ : ι' => Fintype.card F))
    (z : Word F ι') (hz : ∀ j, j ∉ S.selected → z j = 0) :
    S.extendLocalToRegister (selectedPhase S z) =
      (registerUnitary (F := F) (ι' := ι')).conjOperator (phase z) := by
  let _ : DecidableEq ι' := Classical.decEq ι'
  apply (EuclideanSpace.basisFun
    (Semantics.Qudit.Label (fun _ : ι' => Fintype.card F)) Complex).toBasis.ext
  intro labels
  let a : Word F ι' := (fieldLabelEquiv (F := F)).symm labels
  have hlabels : labels = fieldLabelEquiv (F := F) a :=
    ((fieldLabelEquiv (F := F)).apply_symm_apply labels).symm
  rw [hlabels]
  change S.extendLocalToRegister (selectedPhase S z)
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
    (registerUnitary (F := F) (ι' := ι')).conjOperator (phase z)
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a))
  unfold Semantics.QuditSubsystem.extendLocalToRegister
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  simp only [Semantics.UnitaryTransport.symm_toLinearEquiv,
    LinearEquiv.symm_symm]
  rw [S.registerFactorization_apply_basis,
    splitLabel_fieldLabelEquiv_first,
    splitLabel_fieldLabelEquiv_second,
    S.extendLocal_apply_tmul,
    selectedPhase_apply_basis,
    ← TensorProduct.smul_tmul', map_smul]
  have hfactor := S.registerFactorization_symm_apply_basis
    (fieldLabelEquiv (F := F) (restrictWordToRegion S a),
      fieldLabelEquiv (F := F) (restrictWordToComplement S a))
  change _ • S.registerFactorization.symm.toLinearEquiv
      ((EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) (restrictWordToRegion S a))) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) (restrictWordToComplement S a)))) = _
  rw [hfactor]
  have hRecombine : S.recombineLabel
      (fieldLabelEquiv (F := F) (restrictWordToRegion S a),
        fieldLabelEquiv (F := F) (restrictWordToComplement S a)) =
      fieldLabelEquiv (F := F) a := by
    funext j
    by_cases hj : j ∈ S.selected
    · simp [Semantics.QuditSubsystem.recombineLabel, hj,
        restrictWordToRegion, fieldLabelEquiv]
    · simp [Semantics.QuditSubsystem.recombineLabel, hj,
        restrictWordToComplement, fieldLabelEquiv]
  rw [hRecombine, Semantics.UnitaryTransport.conjOperator_apply]
  have hinv : (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.symm
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex a := by
    change (registerUnitary (F := F) (ι' := ι')).symm
      (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) = _
    exact registerUnitary_symm_apply_basis (F := F) a
  rw [hinv, phase_basis, map_smul]
  rw [wordPairing_restrictWordToRegion_eq S z a hz]
  congr 1
  exact (Semantics.FiniteAlphabet.registerUnitary_apply_basis F ι' a).symm

/-- The CSS subspace transported to the canonical finite-qudit register. -/
def cssQuditCode {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι') :
    Semantics.QuantumCode
      (Semantics.Qudit.QuditRegister (fun _ : ι' => Fintype.card F)) :=
  (cssQuantumCode xCode zCode).transport (registerUnitary (F := F))

set_option maxHeartbeats 1000000 in
/-- Algebraic CSS distance detects every small-region operator after qudit relabelling. -/
theorem detectableOn_cssQuditCode_extendLocal_of_card_lt
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d)
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (hcard : S.selected.card < d)
    (E : Semantics.Operator S.selectedSystem) :
    Semantics.DetectableOn (cssQuditCode xCode zCode)
      (S.extendLocalToRegister E) := by
  let U := registerUnitary (F := F) (ι' := ι')
  obtain ⟨c, hc⟩ := detectableOn_localOperator_of_card_lt_algebraicCSSMinimumDistance
    xCode zCode horth d hminimum S hcard E
  refine ⟨c, ?_⟩
  rintro x ⟨x₀, hx, rfl⟩ y ⟨y₀, hy, rfl⟩
  change inner Complex (U x₀) (S.extendLocalToRegister E (U y₀)) =
    c * inner Complex (U x₀) (U y₀)
  have hE : U (Semantics.FiniteAlphabet.localOperator S E y₀) =
      S.extendLocalToRegister E (U y₀) := by
    rw [registerUnitary_apply_eq_finiteAlphabet,
      registerUnitary_apply_eq_finiteAlphabet]
    simp [Semantics.FiniteAlphabet.localOperator,
      Semantics.UnitaryTransport.conjOperator, Semantics.UnitaryTransport.symm]
  rw [← hE, U.map_inner, U.map_inner]
  exact hc x₀ hx y₀ hy

set_option maxHeartbeats 1000000 in
/-- Algebraic CSS minimum distance implies the semantic BPT measurement-distance bound. -/
theorem cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    Semantics.QuditSubsystem.BPTMeasurementDistance
      (cssQuditCode xCode zCode) d := by
  intro S hcard
  apply (S.noInformationOn_iff_allLocalScalarCompression
    (cssQuditCode xCode zCode)).2
  intro E
  apply (Semantics.QuditSubsystem.scalarCompression_iff_detectableOn
    (cssQuditCode xCode zCode) (S.extendLocalToRegister E)).2
  exact detectableOn_cssQuditCode_extendLocal_of_card_lt
    xCode zCode horth d hminimum S
    (by simpa [Semantics.QuditSubsystem.SelectedCoordinates] using hcard) E

set_option maxHeartbeats 1000000 in
/-- A nontrivial CSS logical Pauli makes the full qudit region informative. -/
theorem cssQuditCode_not_noInformationOn_fullRegion
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    ¬ Semantics.QuditSubsystem.NoInformationOn (cssQuditCode xCode zCode)
      (Semantics.QuditSubsystem.fullRegion (fun _ : ι' => Fintype.card F)) := by
  let q : ι' → Nat := fun _ => Fintype.card F
  let U := registerUnitary (F := F) (ι' := ι')
  obtain ⟨x, z, hnot, _⟩ :=
    exists_nondetectable_pauli_of_algebraicCSSMinimumDistance
      xCode zCode horth d hminimum
  have hnotU : ¬ Semantics.DetectableOn (cssQuditCode xCode zCode)
      (U.conjOperator (pauli x z)) := by
    intro hdetect
    obtain ⟨c, hc⟩ := hdetect
    apply hnot
    refine ⟨c, ?_⟩
    intro a ha b hb
    have hh := hc (U a) ⟨a, ha, rfl⟩ (U b) ⟨b, hb, rfl⟩
    simpa only [Semantics.UnitaryTransport.conjOperator_apply,
      LinearEquiv.symm_apply_apply, U.map_inner] using hh
  have hq : ∀ j : ι', 0 < q j := by
    intro j
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  obtain ⟨E, hE⟩ := Semantics.QuditSubsystem.fullRegion_extension_surjective
    q hq (U.conjOperator (pauli x z))
  intro hInfo
  have hScalar := ((Semantics.QuditSubsystem.fullRegion q).noInformationOn_iff_allLocalScalarCompression
    (cssQuditCode xCode zCode)).1 hInfo E
  have hDetect := (Semantics.QuditSubsystem.scalarCompression_iff_detectableOn
    (cssQuditCode xCode zCode) _).1 hScalar
  rw [hE] at hDetect
  exact hnotU hDetect

set_option maxHeartbeats 1000000 in
/-- Algebraic CSS distance lower-bounds the semantic distance used by qLDPC families. -/
theorem algebraicCSSMinimumDistance_le_semanticQuditDistance
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    d ≤ QLDPC.semanticQuditDistance (fun _ : ι' => Fintype.card F)
      (cssQuditCode xCode zCode) := by
  exact QLDPC.le_semanticQuditDistance_of_bptMeasurementDistance
    (cssQuditCode xCode zCode) d
    (cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
      xCode zCode horth d hminimum)
    (cssQuditCode_not_noInformationOn_fullRegion
      xCode zCode horth d hminimum)

/-- The explicit field-to-qudit relabelling preserves the actual codespace dimension. -/
theorem cssQuditCode_dimension_eq {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι') :
    (cssQuditCode xCode zCode).dimension =
      (cssQuantumCode xCode zCode).dimension := by
  exact LinearEquiv.finrank_map_eq (registerUnitary (F := F) (ι' := ι')).toLinearEquiv
    (cssQuantumCode xCode zCode).carrier

/-- The transported finite-qudit code retains the chain-complex cohomology dimension. -/
theorem chainComplex_cssQuditCode_dimension_eq_pow_cohomology
    {ι' κ₀ κ₂ : Type u} [Fintype ι'] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι') (Word F κ₂)) :
    (cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode).dimension =
      (Fintype.card F) ^ Module.finrank F K.middleCohomology := by
  rw [cssQuditCode_dimension_eq]
  exact chainComplex_cssQuantumCode_dimension_eq_pow_cohomology K

/-- The semantic qudit codespace has dimension `|F|` to the middle-homology rank. -/
theorem chainComplex_cssQuditCode_dimension_eq_pow_homology
    {ι' κ₀ κ₂ : Type u} [Fintype ι'] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι') (Word F κ₂)) :
    (cssQuditCode K.firstCoboundaryCheckCode K.middleBoundaryCode).dimension =
      (Fintype.card F) ^ Module.finrank F K.middleHomology := by
  rw [chainComplex_cssQuditCode_dimension_eq_pow_cohomology K,
    chainComplex_finrank_middleCohomology_eq_middleHomology K]

end QEC.Coding.FiniteFieldPauli
