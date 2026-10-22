import QEC.Coding.Core.Definitions

/-!
# The concrete BK05 punctured Reed--Muller codes

This module fixes the finite binary coordinate convention used in
Bravyi--Kitaev's fifteen-qubit H-state route.  `Fin 15` enumerates the
nonzero points `0001, 0010, ..., 1111` of `F_2^4`; `Fin 0` selects the
leftmost source coordinate `x_1` and `Fin 3` the rightmost coordinate `x_4`.

The finite images below are intentionally transparent.  Subsequent lemmas
prove their dimensions, dual/coset identities, divisibility, and weight
enumerators by finite computation; no enumerator or protocol probability is
stored as an assumption or table here.
-/

namespace QEC.Distillation.BK15

open QEC Coding

/-- The binary field used by the BK05 code. -/
abbrev Bit := ZMod 2

/-- The fifteen punctured binary coordinates of the BK05 construction. -/
abbrev Word := Coding.Word Bit (Fin 15)

/-- The six square-free quadratic monomials in four Boolean variables. -/
abbrev QuadraticIndex := { ij : Fin 4 × Fin 4 // ij.1 < ij.2 }

/-- The `j`-th source-coordinate bit of the nonzero point represented by `i`.

`i.val + 1` gives the source ordering from `0001` through `1111`; reversing
the bit position makes `Fin 0` mean source variable `x_1`.
-/
def pointBit (j : Fin 4) (i : Fin 15) : Bit :=
  (((i.val + 1) / 2 ^ (3 - j.val)) % 2 : Nat)

/-- The punctured evaluation word of source coordinate `x_j`. -/
def linearGenerator (j : Fin 4) : Word := fun i => pointBit j i

/-- The punctured evaluation word of source monomial `x_i x_j`, with `i < j`. -/
def quadraticGenerator (ij : QuadraticIndex) : Word := fun i =>
  pointBit ij.1.1 i * pointBit ij.1.2 i

/-- The four explicitly ordered linear generators of `L1`. -/
def l1CoefficientMap : (Fin 4 → Bit) →ₗ[Bit] Word where
  toFun a := fun i => ∑ j : Fin 4, a j * linearGenerator j i
  map_add' := by
    intro a b
    ext i
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    ext i
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc]

/-- The ten explicitly ordered generators of `L2`: four linear and six quadratic. -/
def l2Generator : Sum (Fin 4) QuadraticIndex → Word
  | Sum.inl j => linearGenerator j
  | Sum.inr ij => quadraticGenerator ij

/-- The concrete degree-at-most-two punctured evaluation map. -/
def l2CoefficientMap : (Sum (Fin 4) QuadraticIndex → Bit) →ₗ[Bit] Word where
  toFun a := fun i => ∑ g : Sum (Fin 4) QuadraticIndex, a g * l2Generator g i
  map_add' := by
    intro a b
    ext i
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    ext i
    change
      (∑ g : Sum (Fin 4) QuadraticIndex,
        (c * a g) * l2Generator g i) =
        c * ∑ g : Sum (Fin 4) QuadraticIndex,
          a g * l2Generator g i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring

/-- BK05's punctured first-order Reed--Muller subspace `L1`. -/
def L1 : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l1CoefficientMap

/-- BK05's punctured degree-at-most-two subspace `L2`. -/
def L2 : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l2CoefficientMap

/-- The source's all-ones logical-coset representative `[1]`. -/
def allOnes : Word := fun _ => 1

/-- Coordinatewise multiplication of binary words. -/
def pointwiseProduct (u v : Word) : Word := fun i => u i * v i

/--
The concrete coefficient map for the source decomposition
`L1⊥ = L2 ⊕ [1]`.

The final bit selects the two cosets. Its injectivity is established below,
so this is a genuine direct finite presentation rather than a quotient or an
uninterpreted collection of words.
-/
def l1DualCoefficientMap :
    ((Sum (Fin 4) QuadraticIndex → Bit) × Bit) →ₗ[Bit] Word where
  toFun bc := l2CoefficientMap bc.1 + bc.2 • allOnes
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    module
  map_smul' := by
    intro c a
    ext i
    simp [Prod.smul_fst, Prod.smul_snd, map_smul,
      smul_eq_mul, mul_add, mul_assoc]

/--
The concrete coefficient map for the source decomposition
`L2⊥ = L1 ⊕ [1]`.
-/
def l2DualCoefficientMap : ((Fin 4 → Bit) × Bit) →ₗ[Bit] Word where
  toFun ac := l1CoefficientMap ac.1 + ac.2 • allOnes
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    module
  map_smul' := by
    intro c a
    ext i
    simp [Prod.smul_fst, Prod.smul_snd, map_smul,
      smul_eq_mul, mul_add, mul_assoc]

/-- The explicit direct-sum model which will be identified with `L1.dual`. -/
def L1DualModel : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l1DualCoefficientMap

/-- The explicit direct-sum model which will be identified with `L2.dual`. -/
def L2DualModel : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l2DualCoefficientMap

/-- The four linear parity functionals whose kernel is `L1.dual`. -/
def l1Syndrome : Word →ₗ[Bit] (Fin 4 → Bit) where
  toFun w := fun j => wordPairing w (linearGenerator j)
  map_add' := by
    intro u v
    ext j
    simpa [wordPairing_apply] using add_dotProduct u v (linearGenerator j)
  map_smul' := by
    intro c u
    ext j
    simpa [wordPairing_apply] using smul_dotProduct c u (linearGenerator j)

/-- The ten degree-at-most-two parity functionals whose kernel is `L2.dual`. -/
def l2Syndrome : Word →ₗ[Bit] (Sum (Fin 4) QuadraticIndex → Bit) where
  toFun w := fun g => wordPairing w (l2Generator g)
  map_add' := by
    intro u v
    ext g
    simpa [wordPairing_apply] using add_dotProduct u v (l2Generator g)
  map_smul' := by
    intro c u
    ext g
    simpa [wordPairing_apply] using smul_dotProduct c u (l2Generator g)

/-- The transparent finite enumeration of `L1`, generated from all four-bit coefficients. -/
def l1Words : Finset Word := Finset.univ.image l1CoefficientMap

/-- The transparent finite enumeration of `L2`, generated from all ten coefficients. -/
def l2Words : Finset Word := Finset.univ.image l2CoefficientMap

/-- The explicit nontrivial logical coset `L2 + [1]`. -/
def l2LogicalCosetWords : Finset Word := l2Words.image fun w => w + allOnes

/-- The explicit nontrivial logical coset `L1 + [1]`. -/
def l1LogicalCosetWords : Finset Word := l1Words.image fun w => w + allOnes

/-- A transparent enumeration of the proved `L1` dual model. -/
def l1DualWords : Finset Word := Finset.univ.image l1DualCoefficientMap

/-- A transparent enumeration of the proved `L2` dual model. -/
def l2DualWords : Finset Word := Finset.univ.image l2DualCoefficientMap

/-- Count words of a specified Hamming weight in a transparent finite enumeration. -/
def weightCount (words : Finset Word) (weight : Nat) : Nat :=
  (words.filter fun w => HammingWeight w = weight).card

/-- Every coefficient image used to enumerate `L1` is a genuine `L1` codeword. -/
theorem l1CoefficientMap_mem (a : Fin 4 → Bit) :
    l1CoefficientMap a ∈ L1.carrier :=
  ⟨a, rfl⟩

/-- Every coefficient image used to enumerate `L2` is a genuine `L2` codeword. -/
theorem l2CoefficientMap_mem (a : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap a ∈ L2.carrier :=
  ⟨a, rfl⟩

/-- The six source monomials are the six ordered pairs in four variables. -/
theorem quadraticIndex_card : Fintype.card QuadraticIndex = 6 := by
  native_decide

/-- The four selected linear evaluations have no coefficient redundancy. -/
theorem l1CoefficientMap_injective : Function.Injective l1CoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  native_decide

/-- The four linear plus six quadratic evaluations have no coefficient redundancy. -/
theorem l2CoefficientMap_injective : Function.Injective l2CoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  native_decide

/-- The two direct-sum coefficient presentations are injective. -/
theorem l1DualCoefficientMap_injective : Function.Injective l1DualCoefficientMap := by
  -- A linear map is injective iff its kernel is zero; enumerate inputs, not pairs.
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  native_decide

/-- The two direct-sum coefficient presentations are injective. -/
theorem l2DualCoefficientMap_injective : Function.Injective l2DualCoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  native_decide

/-- The BK05 `L1` code has its source dimension four. -/
theorem l1_dimension : Dimension L1 = 4 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l1CoefficientMap) = 4
  rw [LinearMap.finrank_range_of_inj l1CoefficientMap_injective,
    Module.finrank_pi]
  simp

/-- The BK05 `L2` code has its source dimension ten. -/
theorem l2_dimension : Dimension L2 = 10 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l2CoefficientMap) = 10
  rw [LinearMap.finrank_range_of_inj l2CoefficientMap_injective,
    Module.finrank_pi]
  simp [quadraticIndex_card]

/-- The explicit `L2 ⊕ [1]` presentation has binary dimension eleven. -/
theorem l1DualModel_dimension : Dimension L1DualModel = 11 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l1DualCoefficientMap) = 11
  rw [LinearMap.finrank_range_of_inj l1DualCoefficientMap_injective,
    Module.finrank_prod, Module.finrank_pi]
  simp [quadraticIndex_card]

/-- The explicit `L1 ⊕ [1]` presentation has binary dimension five. -/
theorem l2DualModel_dimension : Dimension L2DualModel = 5 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l2DualCoefficientMap) = 5
  rw [LinearMap.finrank_range_of_inj l2DualCoefficientMap_injective,
    Module.finrank_prod, Module.finrank_pi]
  simp

/-- `L1` is concretely contained in the degree-at-most-two code `L2`. -/
theorem l1_coefficient_has_l2_presentation :
    ∀ a : Fin 4 → Bit,
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit,
        l2CoefficientMap b = l1CoefficientMap a := by
  native_decide

theorem L1_le_L2 : L1.carrier ≤ L2.carrier := by
  rintro w ⟨a, rfl⟩
  rcases l1_coefficient_has_l2_presentation a with ⟨b, hb⟩
  exact ⟨b, hb⟩

/-- Every `L2` generator is orthogonal to every `L1` generator combination. -/
theorem l2_l1_pairing_zero :
    ∀ (b : Sum (Fin 4) QuadraticIndex → Bit) (a : Fin 4 → Bit),
      wordPairing (l2CoefficientMap b) (l1CoefficientMap a) = 0 := by
  native_decide

/-- The concrete `L2` code lies in the dual of `L1`. -/
theorem L2_le_L1_dual : L2.carrier ≤ L1.dual.carrier := by
  rintro w ⟨b, rfl⟩
  refine (L1.mem_dual _).2 ?_
  rintro c ⟨a, rfl⟩
  exact l2_l1_pairing_zero b a

/-- The all-ones logical representative is not an `L2` word. -/
theorem allOnes_not_l2_coefficient_image :
    ∀ b : Sum (Fin 4) QuadraticIndex → Bit, l2CoefficientMap b ≠ allOnes := by
  native_decide

theorem allOnes_not_mem_L2 : allOnes ∉ L2.carrier := by
  rintro ⟨b, hb⟩
  exact allOnes_not_l2_coefficient_image b hb

/-- The all-ones logical representative is not an `L1` word. -/
theorem allOnes_not_l1_coefficient_image :
    ∀ a : Fin 4 → Bit, l1CoefficientMap a ≠ allOnes := by
  native_decide

theorem allOnes_not_mem_L1 : allOnes ∉ L1.carrier := by
  rintro ⟨a, ha⟩
  exact allOnes_not_l1_coefficient_image a ha

/-- The explicit `L2 ⊕ [1]` model is orthogonal to `L1`. -/
theorem l1DualModel_l1_pairing_zero :
    ∀ (bc : (Sum (Fin 4) QuadraticIndex → Bit) × Bit) (a : Fin 4 → Bit),
      wordPairing (l1DualCoefficientMap bc) (l1CoefficientMap a) = 0 := by
  native_decide

theorem L1DualModel_le_L1_dual : L1DualModel.carrier ≤ L1.dual.carrier := by
  rintro w ⟨bc, rfl⟩
  refine (L1.mem_dual _).2 ?_
  rintro c ⟨a, rfl⟩
  exact l1DualModel_l1_pairing_zero bc a

/-- The explicit `L1 ⊕ [1]` model is orthogonal to `L2`. -/
theorem l2DualModel_l2_pairing_zero :
    ∀ (ac : (Fin 4 → Bit) × Bit) (b : Sum (Fin 4) QuadraticIndex → Bit),
      wordPairing (l2DualCoefficientMap ac) (l2CoefficientMap b) = 0 := by
  native_decide

theorem L2DualModel_le_L2_dual : L2DualModel.carrier ≤ L2.dual.carrier := by
  rintro w ⟨ac, rfl⟩
  refine (L2.mem_dual _).2 ?_
  rintro c ⟨b, rfl⟩
  exact l2DualModel_l2_pairing_zero ac b

/-- The finite-coordinate dual dimension of `L1` is eleven. -/
theorem l1_dual_dimension : Dimension L1.dual = 11 := by
  rw [LinearCode.dual_dimension_eq_length_sub_dimension, l1_dimension]
  native_decide

/-- The finite-coordinate dual dimension of `L2` is five. -/
theorem l2_dual_dimension : Dimension L2.dual = 5 := by
  rw [LinearCode.dual_dimension_eq_length_sub_dimension, l2_dimension]
  native_decide

/-- The source relation `L1⊥ = L2 ⊕ [1]`, in a concrete injective presentation. -/
theorem l1_dual_carrier_eq_model : L1.dual.carrier = L1DualModel.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq L1DualModel_le_L1_dual
  simpa only [Dimension_eq_finrank_carrier] using
    l1DualModel_dimension.trans l1_dual_dimension.symm

/-- The source relation `L2⊥ = L1 ⊕ [1]`, in a concrete injective presentation. -/
theorem l2_dual_carrier_eq_model : L2.dual.carrier = L2DualModel.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq L2DualModel_le_L2_dual
  simpa only [Dimension_eq_finrank_carrier] using
    l2DualModel_dimension.trans l2_dual_dimension.symm

/-- A dual `L1` word has a unique concrete `L2 + c[1]` decomposition. -/
theorem mem_l1_dual_iff_exists_l2_plus_allOnes (w : Word) :
    w ∈ L1.dual.carrier ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, ∃ c : Bit,
        w = l2CoefficientMap b + c • allOnes := by
  constructor
  · intro hw
    rw [l1_dual_carrier_eq_model] at hw
    rcases hw with ⟨bc, hbc⟩
    exact ⟨bc.1, bc.2, hbc.symm⟩
  · rintro ⟨b, c, rfl⟩
    rw [l1_dual_carrier_eq_model]
    exact ⟨(b, c), rfl⟩

/-- A dual `L2` word has a unique concrete `L1 + c[1]` decomposition. -/
theorem mem_l2_dual_iff_exists_l1_plus_allOnes (w : Word) :
    w ∈ L2.dual.carrier ↔
      ∃ a : Fin 4 → Bit, ∃ c : Bit,
        w = l1CoefficientMap a + c • allOnes := by
  constructor
  · intro hw
    rw [l2_dual_carrier_eq_model] at hw
    rcases hw with ⟨ac, hac⟩
    exact ⟨ac.1, ac.2, hac.symm⟩
  · rintro ⟨a, c, rfl⟩
    rw [l2_dual_carrier_eq_model]
    exact ⟨(a, c), rfl⟩

/-- The `L2 + c[1]` decomposition is unique. -/
theorem l1_dual_decomposition_unique
    {b b' : Sum (Fin 4) QuadraticIndex → Bit} {c c' : Bit}
    (h : l2CoefficientMap b + c • allOnes = l2CoefficientMap b' + c' • allOnes) :
    b = b' ∧ c = c' := by
  change l1DualCoefficientMap (b, c) = l1DualCoefficientMap (b', c') at h
  have hPair : (b, c) = (b', c') := l1DualCoefficientMap_injective h
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- The `L1 + c[1]` decomposition is unique. -/
theorem l2_dual_decomposition_unique
    {a a' : Fin 4 → Bit} {c c' : Bit}
    (h : l1CoefficientMap a + c • allOnes = l1CoefficientMap a' + c' • allOnes) :
    a = a' ∧ c = c' := by
  change l2DualCoefficientMap (a, c) = l2DualCoefficientMap (a', c') at h
  have hPair : (a, c) = (a', c') := l2DualCoefficientMap_injective h
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- Each displayed linear generator is a coefficient-map image. -/
theorem linearGenerator_is_l1_coefficient_image :
    ∀ j : Fin 4, l1CoefficientMap (Pi.single j 1) = linearGenerator j := by
  native_decide

/-- Each displayed degree-at-most-two generator is a coefficient-map image. -/
theorem l2Generator_is_l2_coefficient_image :
    ∀ g : Sum (Fin 4) QuadraticIndex,
      l2CoefficientMap (Pi.single g 1) = l2Generator g := by
  native_decide

theorem linearGenerator_mem_L1 (j : Fin 4) : linearGenerator j ∈ L1.carrier :=
  ⟨Pi.single j 1, linearGenerator_is_l1_coefficient_image j⟩

theorem l2Generator_mem_L2 (g : Sum (Fin 4) QuadraticIndex) :
    l2Generator g ∈ L2.carrier :=
  ⟨Pi.single g 1, l2Generator_is_l2_coefficient_image g⟩

/-- Expand an `L1` word in its four concrete generator words. -/
theorem l1CoefficientMap_eq_sum (a : Fin 4 → Bit) :
    l1CoefficientMap a = ∑ j : Fin 4, a j • linearGenerator j := by
  ext i
  simp [l1CoefficientMap, Pi.smul_apply]

/-- Expand an `L2` word in its ten concrete generator words. -/
theorem l2CoefficientMap_eq_sum (b : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap b = ∑ g : Sum (Fin 4) QuadraticIndex, b g • l2Generator g := by
  ext i
  simp [l2CoefficientMap, Pi.smul_apply]

/-- Pairing against an `L1` word is the corresponding finite generator sum. -/
theorem wordPairing_l1CoefficientMap (w : Word) (a : Fin 4 → Bit) :
    wordPairing w (l1CoefficientMap a) =
      ∑ j : Fin 4, a j • wordPairing w (linearGenerator j) := by
  simp only [l1CoefficientMap_eq_sum, map_sum, map_smul]

/-- Pairing against an `L2` word is the corresponding finite generator sum. -/
theorem wordPairing_l2CoefficientMap (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit) :
    wordPairing w (l2CoefficientMap b) =
      ∑ g : Sum (Fin 4) QuadraticIndex, b g • wordPairing w (l2Generator g) := by
  simp only [l2CoefficientMap_eq_sum, map_sum, map_smul]

theorem l1Syndrome_zero_pairing (w : Word) (a : Fin 4 → Bit)
    (hzero : l1Syndrome w = 0) : wordPairing w (l1CoefficientMap a) = 0 := by
  rw [wordPairing_l1CoefficientMap]
  apply Finset.sum_eq_zero
  intro j _
  have hj := congrFun hzero j
  change wordPairing w (linearGenerator j) = 0 at hj
  rw [hj, smul_zero]

theorem l2Syndrome_zero_pairing (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit)
    (hzero : l2Syndrome w = 0) : wordPairing w (l2CoefficientMap b) = 0 := by
  rw [wordPairing_l2CoefficientMap]
  apply Finset.sum_eq_zero
  intro g _
  have hg := congrFun hzero g
  change wordPairing w (l2Generator g) = 0 at hg
  rw [hg, smul_zero]

/-- The `L1` dual is exactly the kernel of its four concrete parity checks. -/
theorem l1_dual_carrier_eq_l1Syndrome_ker :
    L1.dual.carrier = LinearMap.ker l1Syndrome := by
  apply le_antisymm
  · intro w hw
    change l1Syndrome w = 0
    funext j
    have hj := (L1.mem_dual w).1 hw (linearGenerator j) (linearGenerator_mem_L1 j)
    simpa [l1Syndrome] using hj
  · intro w hw
    change l1Syndrome w = 0 at hw
    refine (L1.mem_dual w).2 ?_
    rintro c ⟨a, rfl⟩
    exact l1Syndrome_zero_pairing w a hw

/-- The `L2` dual is exactly the kernel of its ten concrete parity checks. -/
theorem l2_dual_carrier_eq_l2Syndrome_ker :
    L2.dual.carrier = LinearMap.ker l2Syndrome := by
  apply le_antisymm
  · intro w hw
    change l2Syndrome w = 0
    funext g
    have hg := (L2.mem_dual w).1 hw (l2Generator g) (l2Generator_mem_L2 g)
    simpa [l2Syndrome] using hg
  · intro w hw
    change l2Syndrome w = 0 at hw
    refine (L2.mem_dual w).2 ?_
    rintro c ⟨b, rfl⟩
    exact l2Syndrome_zero_pairing w b hw

/-- All `L1` weights are divisible by eight. -/
theorem l1_weight_divisible_by_eight :
    ∀ a : Fin 4 → Bit, HammingWeight (l1CoefficientMap a) % 8 = 0 := by
  native_decide

/-- All `L2` weights are even. -/
theorem l2_weight_even :
    ∀ b : Sum (Fin 4) QuadraticIndex → Bit,
      HammingWeight (l2CoefficientMap b) % 2 = 0 := by
  native_decide

/-- Products of two `L1` words have weight divisible by four. -/
theorem l1_pointwiseProduct_weight_divisible_by_four :
    ∀ (a b : Fin 4 → Bit),
      HammingWeight (pointwiseProduct (l1CoefficientMap a) (l1CoefficientMap b)) % 4 = 0 := by
  native_decide

/-- Products of an `L1` word with an `L2`-dual word have weight divisible by four. -/
theorem l1_l2Dual_pointwiseProduct_weight_divisible_by_four :
    ∀ (a : Fin 4 → Bit) (ac : (Fin 4 → Bit) × Bit),
      HammingWeight (pointwiseProduct (l1CoefficientMap a) (l2DualCoefficientMap ac)) % 4 = 0 := by
  native_decide

/-- The nontrivial `L2 + [1]` logical coset is disjoint from `L2`. -/
theorem l2Words_disjoint_l2LogicalCosetWords : Disjoint l2Words l2LogicalCosetWords := by
  apply Finset.disjoint_left.mpr
  intro w hw hcoset
  rw [l2Words, Finset.mem_image] at hw
  rcases hw with ⟨a, _, ha⟩
  rw [l2LogicalCosetWords, Finset.mem_image] at hcoset
  rcases hcoset with ⟨u, hu, hu_eq⟩
  rw [l2Words, Finset.mem_image] at hu
  rcases hu with ⟨b, _, hb⟩
  apply allOnes_not_mem_L2
  have hdiff : l2CoefficientMap a - l2CoefficientMap b = allOnes := by
    rw [ha, hb, ← hu_eq]
    abel
  rw [← hdiff]
  exact L2.carrier.sub_mem (l2CoefficientMap_mem a) (l2CoefficientMap_mem b)

/-- The nontrivial `L1 + [1]` coset is disjoint from `L1`. -/
theorem l1Words_disjoint_l1LogicalCosetWords : Disjoint l1Words l1LogicalCosetWords := by
  apply Finset.disjoint_left.mpr
  intro w hw hcoset
  rw [l1Words, Finset.mem_image] at hw
  rcases hw with ⟨a, _, ha⟩
  rw [l1LogicalCosetWords, Finset.mem_image] at hcoset
  rcases hcoset with ⟨u, hu, hu_eq⟩
  rw [l1Words, Finset.mem_image] at hu
  rcases hu with ⟨b, _, hb⟩
  apply allOnes_not_mem_L1
  have hdiff : l1CoefficientMap a - l1CoefficientMap b = allOnes := by
    rw [ha, hb, ← hu_eq]
    abel
  rw [← hdiff]
  exact L1.carrier.sub_mem (l1CoefficientMap_mem a) (l1CoefficientMap_mem b)

/-- The direct finite enumerations have their expected cardinalities. -/
theorem l1Words_card : l1Words.card = 16 := by
  rw [l1Words, Finset.card_image_of_injective _ l1CoefficientMap_injective]
  native_decide

theorem l2Words_card : l2Words.card = 1024 := by
  rw [l2Words, Finset.card_image_of_injective _ l2CoefficientMap_injective]
  native_decide

theorem l1DualWords_card : l1DualWords.card = 2048 := by
  rw [l1DualWords, Finset.card_image_of_injective _ l1DualCoefficientMap_injective]
  native_decide

theorem l2DualWords_card : l2DualWords.card = 32 := by
  rw [l2DualWords, Finset.card_image_of_injective _ l2DualCoefficientMap_injective]
  native_decide

theorem l2LogicalCosetWords_card : l2LogicalCosetWords.card = 1024 := by
  rw [l2LogicalCosetWords,
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), l2Words_card]

theorem l1LogicalCosetWords_card : l1LogicalCosetWords.card = 16 := by
  rw [l1LogicalCosetWords,
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), l1Words_card]

set_option maxRecDepth 16384 in
/-- The finite enumeration `l1DualWords` is extensionally the dual of `L1`. -/
theorem mem_l1DualWords_iff (w : Word) : w ∈ l1DualWords ↔ w ∈ L1.dual.carrier := by
  constructor
  · intro hw
    rw [l1DualWords, Finset.mem_image] at hw
    rcases hw with ⟨bc, -, hbc⟩
    rw [l1_dual_carrier_eq_model]
    exact ⟨bc, hbc⟩
  · intro hw
    rw [l1_dual_carrier_eq_model] at hw
    rcases hw with ⟨bc, hbc⟩
    rw [l1DualWords, Finset.mem_image]
    exact ⟨bc, Finset.mem_univ _, hbc⟩

/-- The finite enumeration `l2DualWords` is extensionally the dual of `L2`. -/
theorem mem_l2DualWords_iff (w : Word) : w ∈ l2DualWords ↔ w ∈ L2.dual.carrier := by
  constructor
  · intro hw
    rw [l2DualWords, Finset.mem_image] at hw
    rcases hw with ⟨ac, -, hac⟩
    rw [l2_dual_carrier_eq_model]
    exact ⟨ac, hac⟩
  · intro hw
    rw [l2_dual_carrier_eq_model] at hw
    rcases hw with ⟨ac, hac⟩
    rw [l2DualWords, Finset.mem_image]
    exact ⟨ac, Finset.mem_univ _, hac⟩

/-- The `L2 + [1]` enumeration has its direct coefficient characterization. -/
theorem mem_l2LogicalCosetWords_iff (w : Word) :
    w ∈ l2LogicalCosetWords ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, w = l2CoefficientMap b + allOnes := by
  constructor
  · intro hw
    rw [l2LogicalCosetWords, Finset.mem_image] at hw
    rcases hw with ⟨u, hu, huEq⟩
    rw [l2Words, Finset.mem_image] at hu
    rcases hu with ⟨b, -, hbEq⟩
    exact ⟨b, by simpa [hbEq] using huEq.symm⟩
  · rintro ⟨b, rfl⟩
    rw [l2LogicalCosetWords, Finset.mem_image]
    refine ⟨l2CoefficientMap b, ?_, rfl⟩
    rw [l2Words, Finset.mem_image]
    exact ⟨b, Finset.mem_univ _, rfl⟩

/-- The `L1 + [1]` enumeration has its direct coefficient characterization. -/
theorem mem_l1LogicalCosetWords_iff (w : Word) :
    w ∈ l1LogicalCosetWords ↔
      ∃ a : Fin 4 → Bit, w = l1CoefficientMap a + allOnes := by
  constructor
  · intro hw
    rw [l1LogicalCosetWords, Finset.mem_image] at hw
    rcases hw with ⟨u, hu, huEq⟩
    rw [l1Words, Finset.mem_image] at hu
    rcases hu with ⟨a, -, haEq⟩
    exact ⟨a, by simpa [haEq] using huEq.symm⟩
  · rintro ⟨a, rfl⟩
    rw [l1LogicalCosetWords, Finset.mem_image]
    refine ⟨l1CoefficientMap a, ?_, rfl⟩
    rw [l1Words, Finset.mem_image]
    exact ⟨a, Finset.mem_univ _, rfl⟩

/-- Exact finite weight enumerator of `L1`, computed from its explicit image. -/
theorem l1_weight_enumerator (weight : Fin 16) :
    weightCount l1Words weight.1 =
      if weight = 0 then 1 else if weight = 8 then 15 else 0 := by
  rw [weightCount, l1Words, Finset.filter_image,
    Finset.card_image_of_injective _ l1CoefficientMap_injective]
  revert weight
  native_decide

/-- Exact finite weight enumerator of `L2`, computed from its explicit image. -/
theorem l2_weight_enumerator (weight : Fin 16) :
    weightCount l2Words weight.1 =
      if weight = 0 then 1 else if weight = 4 then 105 else
      if weight = 6 then 280 else if weight = 8 then 435 else
      if weight = 10 then 168 else if weight = 12 then 35 else 0 := by
  rw [weightCount, l2Words, Finset.filter_image,
    Finset.card_image_of_injective _ l2CoefficientMap_injective]
  revert weight
  native_decide

/-- Exact finite weight enumerator of the logical coset `L2 + [1]`. -/
theorem l2LogicalCoset_weight_enumerator (weight : Fin 16) :
    weightCount l2LogicalCosetWords weight.1 =
      if weight = 3 then 35 else if weight = 5 then 168 else
      if weight = 7 then 435 else if weight = 9 then 280 else
      if weight = 11 then 105 else if weight = 15 then 1 else 0 := by
  have hshift : Function.Injective (fun w : Word => w + allOnes) :=
    fun _ _ h => add_right_cancel h
  rw [weightCount, l2LogicalCosetWords, l2Words, Finset.image_image,
    Finset.filter_image, Finset.card_image_of_injective _
      (hshift.comp l2CoefficientMap_injective)]
  revert weight
  native_decide

/-- Exact finite weight enumerator of the proved dual `L1⊥`. -/
theorem l1Dual_weight_enumerator (weight : Fin 16) :
    weightCount l1DualWords weight.1 =
      if weight = 0 then 1 else if weight = 3 then 35 else
      if weight = 4 then 105 else if weight = 5 then 168 else
      if weight = 6 then 280 else if weight = 7 then 435 else
      if weight = 8 then 435 else if weight = 9 then 280 else
      if weight = 10 then 168 else if weight = 11 then 105 else
      if weight = 12 then 35 else if weight = 15 then 1 else 0 := by
  -- Count injective coefficient images without repeatedly deduplicating all words.
  rw [weightCount, l1DualWords, Finset.filter_image,
    Finset.card_image_of_injective _ l1DualCoefficientMap_injective]
  revert weight
  native_decide

/-- Exact finite weight enumerator of the proved dual `L2⊥`. -/
theorem l2Dual_weight_enumerator (weight : Fin 16) :
    weightCount l2DualWords weight.1 =
      if weight = 0 then 1 else if weight = 7 then 15 else
      if weight = 8 then 15 else if weight = 15 then 1 else 0 := by
  rw [weightCount, l2DualWords, Finset.filter_image,
    Finset.card_image_of_injective _ l2DualCoefficientMap_injective]
  revert weight
  native_decide

end QEC.Distillation.BK15
