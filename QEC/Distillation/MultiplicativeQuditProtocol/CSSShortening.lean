import QEC.Coding.Core.Definitions
import QEC.Distillation.MultiplicativeQuditProtocol.Register
import QEC.Distillation.Core.TransversalGate
/-!
# Multiplicative-code CSS shortening for Ngu24

This module formalizes the source-level star-product and shortening boundary
for the finite-field construction.  It deliberately stops before any gate
action.
-/

noncomputable section

namespace QEC.Distillation.Ngu24MultiplicativeCSS

open Coding Semantics
open scoped BigOperators

universe u

variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]

local instance : DecidableEq Logical := Classical.decEq _
local instance : DecidableEq (Word F Logical) := Classical.decEq _
local instance : Fintype (Word F Logical) := Fintype.ofFinite _

/-- Componentwise multiplication of finite-field words. -/
def wordStar (x y : Word F I) : Word F I := fun i => x i * y i

omit [Fintype F] [Fintype I] in
@[simp] theorem wordStar_apply (x y : Word F I) (i : I) : wordStar x y i = x i * y i := rfl

omit [Fintype F] [Fintype I] in
theorem wordStar_comm (x y : Word F I) : wordStar x y = wordStar y x := by
  ext i
  exact mul_comm _ _

omit [Fintype F] [Fintype I] in
theorem wordStar_assoc (x y z : Word F I) :
    wordStar (wordStar x y) z = wordStar x (wordStar y z) := by
  ext i
  exact mul_assoc _ _ _

omit [Fintype F] [Fintype I] in
theorem wordStar_add (x y z : Word F I) :
    wordStar (x + y) z = wordStar x z + wordStar y z := by
  ext i
  exact add_mul _ _ _

omit [Fintype F] [Fintype I] in
theorem wordStar_add_right (x y z : Word F I) :
    wordStar x (y + z) = wordStar x y + wordStar x z := by
  ext i
  exact mul_add _ _ _

omit [Fintype F] [Fintype I] in
theorem smul_wordStar (a : F) (x y : Word F I) :
    a • wordStar x y = wordStar (a • x) y := by
  ext i
  simp [wordStar, mul_assoc]

/-- The span of all componentwise products of two codewords. -/
def starSquare (C : LinearCode F I) : Submodule F (Word F I) :=
  Submodule.span F {w | ∃ x ∈ C.carrier, ∃ y ∈ C.carrier, wordStar x y = w}

theorem wordStar_mem_starSquare (C : LinearCode F I) {x y : Word F I}
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) : wordStar x y ∈ starSquare C :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

/-- Restriction of a codeword to the chosen pivot coordinates. -/
def pivotRestrict (C : LinearCode F I) (pivotEmbedding : Logical ↪ I) :
    C.carrier →ₗ[F] (Logical → F) where
  toFun x := fun a => x.1 (pivotEmbedding a)
  map_add' := by
    intro x y
    ext a
    rfl
  map_smul' := by
    intro a x
    ext b
    rfl

/-- The input data that occur before the source's systematic shortening. -/
structure SourceInput (F I Logical : Type u) [Field F] [Fintype F] [Fintype I]
    [Fintype Logical] where
  code : LinearCode F I
  pivotEmbedding : Logical ↪ I
  pivotRestrict_surjective : Function.Surjective (pivotRestrict code pivotEmbedding)
  one_mem_code : (1 : Word F I) ∈ (code : Submodule F (Word F I))
  starSquare_le_dual : starSquare code ≤ (code.dual : Submodule F (Word F I))

namespace SourceInput

/-- A noncomputable linear section supplied by finite-coordinate surjectivity. -/
noncomputable def pivotSection (data : SourceInput F I Logical) :
    (Logical → F) →ₗ[F] data.code.carrier :=
  (pivotRestrict data.code data.pivotEmbedding).splittingOfFunOnFintypeSurjective
    data.pivotRestrict_surjective

/-- The constructed section is a right inverse of pivot restriction. -/
theorem pivotRestrict_pivotSection (data : SourceInput F I Logical) (u : Logical → F) :
    pivotRestrict data.code data.pivotEmbedding (data.pivotSection u) = u :=
  (pivotRestrict data.code data.pivotEmbedding).leftInverse_splittingOfFunOnFintypeSurjective
    data.pivotRestrict_surjective u

/-- Coordinates retained after removing the pivot positions. -/
def PivotComplement (data : SourceInput F I Logical) : Type u :=
  {i : I // i ∉ Set.range data.pivotEmbedding}

noncomputable instance pivotComplementFintype (data : SourceInput F I Logical) :
    Fintype data.PivotComplement := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun i => i ∉ Set.range data.pivotEmbedding)
    (by simp)

noncomputable instance pivotComplementDecidableEq (data : SourceInput F I Logical) :
    DecidableEq data.PivotComplement := Classical.decEq _

/-- Puncture a full word by retaining only pivot-complement coordinates. -/
def puncture (data : SourceInput F I Logical) :
    Word F I →ₗ[F] Word F data.PivotComplement where
  toFun x := fun i => x i.1
  map_add' := by
    intro x y
    ext i
    rfl
  map_smul' := by
    intro a x
    ext i
    rfl

/-- Codewords that vanish on every removed pivot coordinate. -/
def shortenedKernel (data : SourceInput F I Logical) : Submodule F data.code.carrier :=
  (pivotRestrict data.code data.pivotEmbedding).ker

/-- The actual punctured image of the shortened kernel. -/
def shortenedCode (data : SourceInput F I Logical) :
    Submodule F (Word F data.PivotComplement) :=
  data.shortenedKernel.map (data.puncture.comp data.code.carrier.subtype)

/-- The full systematic representative selected by the derived pivot section. -/
def systematicLogicalWord (data : SourceInput F I Logical) (u : Logical → F) : Word F I :=
  data.pivotSection u

/-- The physical, punctured systematic representative. -/
def puncturedLogicalWord (data : SourceInput F I Logical) (u : Logical → F) :
    Word F data.PivotComplement :=
  data.puncture (data.systematicLogicalWord u)

/-- Restriction of an arbitrary full word to the logical pivot coordinates. -/
def pivotCoordinates (data : SourceInput F I Logical) (x : Word F I) : Word F Logical :=
  fun a => x (data.pivotEmbedding a)

@[simp]
theorem pivotCoordinates_systematicLogicalWord (data : SourceInput F I Logical)
    (u : Word F Logical) : data.pivotCoordinates (data.systematicLogicalWord u) = u := by
  ext a
  exact congrFun (data.pivotRestrict_pivotSection u) a

/-- A shortened-kernel word is zero at every removed pivot coordinate. -/
theorem shortenedKernel_pivot_zero (data : SourceInput F I Logical)
    (h : data.shortenedKernel) (a : Logical) : h.1.1 (data.pivotEmbedding a) = 0 := by
  have hzero : pivotRestrict data.code data.pivotEmbedding h.1 = 0 := h.2
  exact congrFun hzero a

/-- Puncturing preserves pairing when the left word vanishes on all pivots. -/
theorem wordPairing_puncture_eq_of_pivot_zero (data : SourceInput F I Logical)
    (left right : Word F I) (hzero : data.pivotCoordinates left = 0) :
    wordPairing (data.puncture left) (data.puncture right) = wordPairing left right := by
  classical
  letI : Fintype (Set.range data.pivotEmbedding) :=
    Fintype.subtype (Finset.univ.filter fun i => i ∈ Set.range data.pivotEmbedding)
      (by simp)
  have hpivot (point : {i : I // i ∈ Set.range data.pivotEmbedding}) :
      left point.1 = 0 := by
    rcases point.2 with ⟨a, ha⟩
    rw [← ha]
    exact congrFun hzero a
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => i ∈ Set.range data.pivotEmbedding)
    (fun i => left i * right i)
  have hpivot_sum :
      (∑ point : {i : I // i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    rw [hpivot point]
    simp
  have hsplit' :
      (∑ point : {i : I // i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) +
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : I, left point * right point := by
    exact hsplit
  let complementEquiv : {i : I // ¬ i ∈ Set.range data.pivotEmbedding} ≃
      data.PivotComplement := Equiv.refl _
  have hcomplement :
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => left point.1 * right point.1)
      (fun point => left point.1 * right point.1) (fun _ => rfl)
  calc
    wordPairing (data.puncture left) (data.puncture right) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := rfl
    _ = ∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1 := hcomplement.symm
    _ = ∑ point : I, left point * right point := by
      rw [hpivot_sum, zero_add] at hsplit'
      exact hsplit'
    _ = wordPairing left right := rfl

/-- Puncture equality makes the full pairing entirely visible on pivots. -/
theorem wordPairing_pivot_eq_of_puncture_eq_zero (data : SourceInput F I Logical)
    (left right : Word F I) (hzero : data.puncture left = 0) :
    wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) =
      wordPairing left right := by
  classical
  letI : Fintype (Set.range data.pivotEmbedding) :=
    Fintype.subtype (Finset.univ.filter fun i => i ∈ Set.range data.pivotEmbedding)
      (by simp)
  have hcomplement (point : data.PivotComplement) : left point.1 = 0 :=
    congrFun hzero point
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => i ∈ Set.range data.pivotEmbedding)
    (fun i => left i * right i)
  have hcomplement_sum :
      (∑ point : data.PivotComplement, left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    rw [hcomplement point]
    simp
  have hsplit' :
      (∑ point : {i : I // i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) +
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : I, left point * right point := by
    exact hsplit
  let rangeEquiv : Logical ≃ Set.range data.pivotEmbedding :=
    Equiv.ofInjective data.pivotEmbedding data.pivotEmbedding.injective
  have hrange :
      (∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1) =
        ∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => left point.1 * right point.1)
      (fun a => left (data.pivotEmbedding a) * right (data.pivotEmbedding a))
      (fun point => by
        have hpoint : data.pivotEmbedding (rangeEquiv.symm point) = point.1 :=
          congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change left point.1 * right point.1 =
          left (data.pivotEmbedding (rangeEquiv.symm point)) *
            right (data.pivotEmbedding (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv : {i : I // ¬ i ∈ Set.range data.pivotEmbedding} ≃
      data.PivotComplement := Equiv.refl _
  have hcomplement_equiv :
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => left point.1 * right point.1)
      (fun point => left point.1 * right point.1) (fun _ => rfl)
  calc
    wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) =
        ∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a) := rfl
    _ = ∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1 := hrange.symm
    _ = ∑ point : I, left point * right point := by
      rw [hcomplement_equiv, hcomplement_sum, add_zero] at hsplit'
      exact hsplit'
    _ = wordPairing left right := rfl

omit [Fintype F] in
/-- Pairing against a coordinate unit reads that coordinate. -/
theorem wordPairing_canonicalBasisWord_right (x : Word F Logical) (a : Logical) :
    wordPairing x (canonicalBasisWord a) = x a := by
  classical
  rw [wordPairing_apply, canonicalBasisWord, dotProduct_single_one]

/-- Puncturing is injective on the actual shortened kernel. -/
theorem puncture_injective_on_shortenedKernel (data : SourceInput F I Logical) :
    Function.Injective (fun h : data.shortenedKernel => data.puncture h.1.1) := by
  intro h k hEq
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hpivot : i ∈ Set.range data.pivotEmbedding
  · rcases hpivot with ⟨a, rfl⟩
    rw [data.shortenedKernel_pivot_zero h a, data.shortenedKernel_pivot_zero k a]
  · exact congrFun hEq ⟨i, hpivot⟩

/-- The physical label of a shortened-code coset element. -/
def shortenedCosetLabel (data : SourceInput F I Logical) (u : Word F Logical)
    (h : data.shortenedKernel) : Word F data.PivotComplement :=
  data.puncturedLogicalWord u + data.puncture h.1.1

/-- Distinct logical labels determine disjoint shortened cosets. -/
theorem shortenedCosetLabel_eq_implies_logical_eq (data : SourceInput F I Logical)
    (u v : Word F Logical) (h k : data.shortenedKernel)
    (hEq : data.shortenedCosetLabel u h = data.shortenedCosetLabel v k) : u = v := by
  let difference : Word F I :=
    (data.systematicLogicalWord u + h.1.1) - (data.systematicLogicalWord v + k.1.1)
  have hdifference : difference ∈ data.code.carrier := by
    exact data.code.carrier.sub_mem
      (data.code.carrier.add_mem (data.pivotSection u).property h.1.2)
      (data.code.carrier.add_mem (data.pivotSection v).property k.1.2)
  have hpuncture : data.puncture difference = 0 := by
    change (data.puncture (data.systematicLogicalWord u) + data.puncture h.1.1) -
        (data.puncture (data.systematicLogicalWord v) + data.puncture k.1.1) = 0
    rw [sub_eq_zero]
    exact hEq
  funext a
  have hstar : wordStar difference (data.systematicLogicalWord (canonicalBasisWord a)) ∈
      data.code.dual.carrier :=
    data.starSquare_le_dual (wordStar_mem_starSquare data.code hdifference
      (data.pivotSection (canonicalBasisWord a)).property)
  have hpairRaw := data.code.dual_orthogonal data.one_mem_code hstar
  have hpair : wordPairing difference (data.systematicLogicalWord (canonicalBasisWord a)) = 0 := by
    simpa [wordPairing_apply, wordStar, dotProduct, mul_comm] using hpairRaw
  have hpivot := data.wordPairing_pivot_eq_of_puncture_eq_zero difference
    (data.systematicLogicalWord (canonicalBasisWord a)) hpuncture
  have hzero : wordPairing (data.pivotCoordinates difference)
      (canonicalBasisWord a) = 0 := by
    have hsystematic : data.pivotCoordinates
        (data.systematicLogicalWord (canonicalBasisWord a)) = canonicalBasisWord a :=
      data.pivotCoordinates_systematicLogicalWord (canonicalBasisWord a)
    calc
      wordPairing (data.pivotCoordinates difference) (canonicalBasisWord a) =
          wordPairing (data.pivotCoordinates difference)
            (data.pivotCoordinates (data.systematicLogicalWord (canonicalBasisWord a))) := by
              rw [hsystematic]
      _ = wordPairing difference (data.systematicLogicalWord (canonicalBasisWord a)) := hpivot
      _ = 0 := hpair
  have hcoordinate : data.pivotCoordinates difference a = 0 := by
    rw [wordPairing_canonicalBasisWord_right] at hzero
    exact hzero
  change u a = v a
  have hu : data.systematicLogicalWord u (data.pivotEmbedding a) = u a :=
    congrFun (data.pivotRestrict_pivotSection u) a
  have hv : data.systematicLogicalWord v (data.pivotEmbedding a) = v a :=
    congrFun (data.pivotRestrict_pivotSection v) a
  change (data.systematicLogicalWord u + h.1.1 -
      (data.systematicLogicalWord v + k.1.1)) (data.pivotEmbedding a) = 0 at hcoordinate
  simp only [Pi.add_apply, Pi.sub_apply] at hcoordinate
  rw [hu, hv, data.shortenedKernel_pivot_zero h a,
    data.shortenedKernel_pivot_zero k a] at hcoordinate
  simpa using sub_eq_zero.mp hcoordinate

/-- The actual finite shortened-kernel carrier used in every uniform coset. -/
abbrev H0 (data : SourceInput F I Logical) := data.shortenedKernel

noncomputable instance h0Fintype (data : SourceInput F I Logical) : Fintype (H0 data) :=
  Fintype.ofFinite _

/-- The source-faithful finite-field coset normalization. -/
def cosetNormalization (H0 : Type u) [Fintype H0] : Complex :=
  (Real.sqrt (Nat.card H0 : Real) : Complex)⁻¹

/-- For one logical label, different shortened-kernel words have different physical labels. -/
theorem shortenedCosetLabel_injective (data : SourceInput F I Logical)
    (u : Word F Logical) : Function.Injective (data.shortenedCosetLabel u) := by
  intro h k hEq
  apply data.puncture_injective_on_shortenedKernel
  apply add_left_cancel (a := data.puncturedLogicalWord u)
  simpa [shortenedCosetLabel] using hEq

/-- The explicit uniform computational-basis sum over the shortened kernel. -/
def shortenedCosetKet (data : SourceInput F I Logical) (u : Word F Logical) :
    ComputationalBasisRegister F data.PivotComplement :=
  cosetNormalization (H0 data) •
    ∑ h : H0 data, registerBasisKet (data.shortenedCosetLabel u h)

/-- Every summand has exactly the declared uniform amplitude. -/
theorem shortenedCosetKet_apply (data : SourceInput F I Logical) (u : Word F Logical)
    (h : H0 data) :
    inner Complex (registerBasisKet (data.shortenedCosetLabel u h)) (data.shortenedCosetKet u) =
      cosetNormalization (H0 data) := by
  classical
  unfold shortenedCosetKet
  rw [inner_smul_right, inner_sum]
  rw [Finset.sum_eq_single h]
  · simp [registerBasisKet]
  · intro h' _hh' hne
    have hlabel : data.shortenedCosetLabel u h' ≠ data.shortenedCosetLabel u h :=
      fun heq => hne (data.shortenedCosetLabel_injective u heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel.symm]
  · simp

private theorem uniformCosetSum_inner (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    inner Complex
        (∑ h : H0 data, registerBasisKet (data.shortenedCosetLabel u h))
        (∑ k : H0 data, registerBasisKet (data.shortenedCosetLabel v k)) =
      if u = v then (Nat.card (H0 data) : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases huv : u = v
  · subst v
    have hinner (h k : H0 data) :
        inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
          (registerBasisKet (data.shortenedCosetLabel u k)) = if h = k then 1 else 0 := by
      simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
      rw [EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply, (data.shortenedCosetLabel_injective u).eq_iff]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    have hlabel : data.shortenedCosetLabel u k ≠ data.shortenedCosetLabel v h :=
      fun heq => huv (data.shortenedCosetLabel_eq_implies_logical_eq u v k h heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel]

/-- The uniform factor has unit squared norm because the shortened kernel is finite and nonempty. -/
theorem cosetNormalization_conj_mul_card (data : SourceInput F I Logical) :
    starRingEnd Complex (cosetNormalization (H0 data)) * cosetNormalization (H0 data) *
        (Nat.card (H0 data) : Complex) = 1 := by
  have hpos : (0 : Real) < Nat.card (H0 data) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (H0 data))
  have hsqrt : (Real.sqrt (Nat.card (H0 data) : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  unfold cosetNormalization
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  norm_cast
  exact (Real.sq_sqrt hpos.le).symm

/-- Distinct logical labels give an orthonormal family of normalized coset states. -/
theorem shortenedCosetKet_inner (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    inner Complex (data.shortenedCosetKet u) (data.shortenedCosetKet v) =
      if u = v then 1 else 0 := by
  unfold shortenedCosetKet
  rw [inner_smul_left, inner_smul_right, uniformCosetSum_inner]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    rw [← mul_assoc]
    exact data.cosetNormalization_conj_mul_card
  · simp [huv]

/-- The normalized coset family is orthonormal in the computational register. -/
theorem shortenedCosetKet_orthonormal (data : SourceInput F I Logical) :
    Orthonormal Complex (data.shortenedCosetKet) := by
  rw [orthonormal_iff_ite]
  intro u v
  exact data.shortenedCosetKet_inner u v

/-- The source-backed linear encoder, specified by its action on computational labels. -/
noncomputable def encodingLinearMap (data : SourceInput F I Logical) :
    ComputationalBasisRegister F Logical →ₗ[Complex]
      ComputationalBasisRegister F data.PivotComplement where
  toFun psi := ∑ u : Word F Logical, psi u • data.shortenedCosetKet u
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]

/-- The explicit encoder preserves the computational-register inner product. -/
theorem encodingLinearMap_map_inner (data : SourceInput F I Logical)
    (psi chi : ComputationalBasisRegister F Logical) :
    inner Complex (data.encodingLinearMap psi) (data.encodingLinearMap chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ u : Word F Logical, psi u • data.shortenedCosetKet u)
      (∑ u : Word F Logical, chi u • data.shortenedCosetKet u) =
        inner Complex psi chi
  rw [data.shortenedCosetKet_orthonormal.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]

/-- The linear encoder promoted to an isometry using its proved inner-product formula. -/
noncomputable def encodingIsometry (data : SourceInput F I Logical) :
    ComputationalBasisRegister F Logical →ₗᵢ[Complex]
      ComputationalBasisRegister F data.PivotComplement :=
  data.encodingLinearMap.isometryOfInner data.encodingLinearMap_map_inner

/-- The physical carrier is exactly the proved range of the isometric encoder. -/
noncomputable def encodedCarrier (data : SourceInput F I Logical) :
    Submodule Complex (ComputationalBasisRegister F data.PivotComplement) :=
  (encodingIsometry data).toLinearMap.range

/-- The range carrier viewed as a semantic quantum code. -/
noncomputable def quantumCode (data : SourceInput F I Logical) :
    QuantumCode (ComputationalBasisRegister F data.PivotComplement) where
  carrier := data.encodedCarrier

/-- The complete source-backed encoded code, with no caller-supplied carrier witness. -/
noncomputable def encodedCode (data : SourceInput F I Logical) :
    EncodedCode (ComputationalBasisRegister F Logical)
      (ComputationalBasisRegister F data.PivotComplement) where
  code := data.quantumCode
  encoding := LinearIsometry.equivRange (data.encodingIsometry)

/-- On a logical computational basis ket, the encoder is the stated shortened coset ket. -/
theorem encodingLinearMap_apply_logical_basis (data : SourceInput F I Logical)
    (u : Word F Logical) :
    data.encodingLinearMap (registerBasisKet u) = data.shortenedCosetKet u := by
  change (∑ v : Word F Logical, registerBasisKet u v • data.shortenedCosetKet v) =
    data.shortenedCosetKet u
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]

/-- The semantic encoded code exposes the same ambient vector on each logical basis ket. -/
theorem encodedCode_apply_logical_basis (data : SourceInput F I Logical)
    (u : Word F Logical) :
    data.encodedCode.encode (registerBasisKet u) = data.shortenedCosetKet u := by
  exact data.encodingLinearMap_apply_logical_basis u

/-- Systematic representatives agree with their logical labels at the pivots. -/
theorem systematicLogicalWord_pivot (data : SourceInput F I Logical)
    (u : Logical → F) (a : Logical) :
    data.systematicLogicalWord u (data.pivotEmbedding a) = u a := by
  have h := congrFun (data.pivotRestrict_pivotSection u) a
  exact h

/-- Every systematic representative is a codeword. -/
theorem systematicLogicalWord_mem_code (data : SourceInput F I Logical) (u : Logical → F) :
    data.systematicLogicalWord u ∈ data.code.carrier :=
  (data.pivotSection u).property

/-- The all-ones hypothesis turns star-square containment into pair orthogonality. -/
theorem shortenedCode_pairing (data : SourceInput F I Logical) {x y : Word F I}
    (hx : x ∈ data.code.carrier) (hy : y ∈ data.code.carrier) :
    wordPairing x y = 0 := by
  have hxy : wordStar x y ∈ data.code.dual.carrier :=
    data.starSquare_le_dual (wordStar_mem_starSquare data.code hx hy)
  have h := data.code.dual_orthogonal data.one_mem_code hxy
  simpa [wordPairing_apply, wordStar, dotProduct, mul_comm] using h

/-- Every full pairing is the sum of its pivot and punctured contributions. -/
theorem wordPairing_partition (data : SourceInput F I Logical)
    (left right : Word F I) :
    wordPairing left right =
      wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) +
        wordPairing (data.puncture left) (data.puncture right) := by
  classical
  letI : Fintype (Set.range data.pivotEmbedding) :=
    Fintype.subtype (Finset.univ.filter fun i => i ∈ Set.range data.pivotEmbedding)
      (by simp)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => i ∈ Set.range data.pivotEmbedding)
    (fun i => left i * right i)
  let rangeEquiv : Logical ≃ Set.range data.pivotEmbedding :=
    Equiv.ofInjective data.pivotEmbedding data.pivotEmbedding.injective
  have hrange :
      (∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1) =
        ∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => left point.1 * right point.1)
      (fun a => left (data.pivotEmbedding a) * right (data.pivotEmbedding a))
      (fun point => by
        have hpoint : data.pivotEmbedding (rangeEquiv.symm point) = point.1 :=
          congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change left point.1 * right point.1 =
          left (data.pivotEmbedding (rangeEquiv.symm point)) *
            right (data.pivotEmbedding (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv : {i : I // ¬ i ∈ Set.range data.pivotEmbedding} ≃
      data.PivotComplement := Equiv.refl _
  have hcomplement :
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => left point.1 * right point.1)
      (fun point => left point.1 * right point.1) (fun _ => rfl)
  calc
    wordPairing left right = ∑ point : I, left point * right point := rfl
    _ = (∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1) +
        ∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
          left point.1 * right point.1 := hsplit.symm
    _ = (∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a)) +
        ∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
          left point.1 * right point.1 := by rw [hrange]
    _ = (∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a)) +
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by rw [hcomplement]
    _ = wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) +
        wordPairing (data.puncture left) (data.puncture right) := rfl

/-- Punctured systematic representatives have the negative logical pairing over any field. -/
theorem puncturedLogicalWord_pairing_eq_neg (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncturedLogicalWord v) =
      -wordPairing u v := by
  have hfull : wordPairing (data.systematicLogicalWord u)
      (data.systematicLogicalWord v) = 0 :=
    data.shortenedCode_pairing (data.systematicLogicalWord_mem_code u)
      (data.systematicLogicalWord_mem_code v)
  have hpartition := data.wordPairing_partition
    (data.systematicLogicalWord u) (data.systematicLogicalWord v)
  rw [data.pivotCoordinates_systematicLogicalWord,
    data.pivotCoordinates_systematicLogicalWord, hfull] at hpartition
  exact eq_neg_of_add_eq_zero_right hpartition.symm

omit [Fintype F] in
private theorem neg_eq_self_of_char_two [CharP F 2] (a : F) : -a = a := by
  apply (eq_neg_of_add_eq_zero_left ?_).symm
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_mul, htwo, zero_mul]

/-- In characteristic two, the source's positive logical pairing is recovered. -/
theorem puncturedLogicalWord_pairing_eq_of_char_two (data : SourceInput F I Logical)
    [CharP F 2] (u v : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncturedLogicalWord v) =
      wordPairing u v := by
  rw [data.puncturedLogicalWord_pairing_eq_neg]
  exact neg_eq_self_of_char_two _

/-- Logical basis representatives have the exact negative Kronecker pairing over any field. -/
theorem puncturedLogicalBasis_pairing_eq_neg_delta (data : SourceInput F I Logical)
    (a b : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncturedLogicalWord (canonicalBasisWord b)) =
        -(if a = b then 1 else 0) := by
  rw [data.puncturedLogicalWord_pairing_eq_neg,
    wordPairing_canonicalBasisWord_right]
  by_cases hab : a = b
  · subst b
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, hab]

/-- The logical-basis pairing has the source's positive delta form in characteristic two. -/
theorem puncturedLogicalBasis_pairing_eq_delta_of_char_two (data : SourceInput F I Logical)
    [CharP F 2] (a b : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncturedLogicalWord (canonicalBasisWord b)) =
        if a = b then 1 else 0 := by
  rw [data.puncturedLogicalWord_pairing_eq_of_char_two,
    wordPairing_canonicalBasisWord_right]
  by_cases hab : a = b
  · subst b
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, hab]

/-- Pairing with the actual punctured all-ones word is the negative logical coordinate sum. -/
theorem puncturedLogicalWord_pairing_puncture_one_eq_neg_sum
    (data : SourceInput F I Logical) (u : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncture (1 : Word F I)) =
      -(∑ a : Logical, u a) := by
  have hfull : wordPairing (data.systematicLogicalWord u) (1 : Word F I) = 0 :=
    data.shortenedCode_pairing (data.systematicLogicalWord_mem_code u) data.one_mem_code
  have hpartition := data.wordPairing_partition (data.systematicLogicalWord u) (1 : Word F I)
  have hpivot_one : data.pivotCoordinates (1 : Word F I) = (1 : Word F Logical) := rfl
  rw [data.pivotCoordinates_systematicLogicalWord, hpivot_one, hfull] at hpartition
  have hneg : wordPairing (data.puncture (data.systematicLogicalWord u))
      (data.puncture (1 : Word F I)) = -wordPairing u (1 : Word F Logical) :=
    eq_neg_of_add_eq_zero_right hpartition.symm
  simpa [puncturedLogicalWord, wordPairing_apply, dotProduct] using hneg

/-- Characteristic two changes the preceding negative coordinate sum to the source's positive form. -/
theorem puncturedLogicalWord_pairing_puncture_one_eq_sum_of_char_two
    (data : SourceInput F I Logical) [CharP F 2] (u : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncture (1 : Word F I)) =
      ∑ a : Logical, u a := by
  rw [data.puncturedLogicalWord_pairing_puncture_one_eq_neg_sum]
  exact neg_eq_self_of_char_two _

/-- Each logical basis representative has negative unit pairing with the punctured all-ones word. -/
theorem puncturedLogicalBasis_pairing_puncture_one_eq_neg_one
    (data : SourceInput F I Logical) (a : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncture (1 : Word F I)) = -1 := by
  simpa [canonicalBasisWord] using
    data.puncturedLogicalWord_pairing_puncture_one_eq_neg_sum (canonicalBasisWord a)

/-- In characteristic two, the all-ones pairing of a logical basis representative is one. -/
theorem puncturedLogicalBasis_pairing_puncture_one_eq_one_of_char_two
    (data : SourceInput F I Logical) [CharP F 2] (a : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncture (1 : Word F I)) = 1 := by
  rw [data.puncturedLogicalBasis_pairing_puncture_one_eq_neg_one]
  exact neg_eq_self_of_char_two _

/-- A systematic logical word has its stated pivot restriction. -/
theorem systematicLogicalWord_one_support (data : SourceInput F I Logical)
    (u : Logical → F) :
    pivotRestrict data.code data.pivotEmbedding (data.pivotSection u) = u :=
  data.pivotRestrict_pivotSection u

/-- Star-square containment gives the source's full-word triple-pairing consequence. -/
theorem starSquare_triple_pairing_eq_zero (data : SourceInput F I Logical)
    {x y z : Word F I} (hx : x ∈ data.code.carrier) (hy : y ∈ data.code.carrier)
    (hz : z ∈ data.code.carrier) :
    wordPairing (wordStar x y) z = 0 := by
  have hxy : wordStar x y ∈ data.code.dual.carrier :=
    data.starSquare_le_dual (wordStar_mem_starSquare data.code hx hy)
  exact data.code.orthogonal_of_mem_dual hxy hz

end SourceInput

end QEC.Distillation.Ngu24MultiplicativeCSS
