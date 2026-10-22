import QEC.Coding.ReedSolomon.FullLength

/-!
# Punctured and shortened prime-field Reed--Solomon codes for KT19

The full-length layer is in `KT19ReedSolomon`.  This companion keeps the
source's puncturing operation honest: selected coordinates are the residues
whose canonical values are below `k`, shortening imposes zero values exactly
there, and puncturing is an actual restriction image on the complementary
coordinate type.

The distance proof uses a root-cardinality bound and a nodal root-product
witness; no MDS, duality, or distance conclusion is carried as data.
-/

noncomputable section

namespace QEC
namespace Coding
namespace KT19ReedSolomon

open scoped BigOperators

private local instance instNeZeroOfPrime (p : Nat) [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : Nat.Prime p).ne_zero⟩

/-- The actual selected residues for a `k`-coordinate puncture. -/
def selectedPunctureLocations (p k : Nat) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter fun point => point.val < k

/-- The complementary retained residues. -/
def keptPunctureLocations (p k : Nat) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ \ selectedPunctureLocations p k

/-- Coordinates removed by the puncture. -/
abbrev SelectedPunctureLocation (p k : Nat) [Fact p.Prime] :=
  ↥(selectedPunctureLocations p k)

/-- Coordinates retained by the puncture. -/
abbrev KeptPunctureLocation (p k : Nat) [Fact p.Prime] :=
  ↥(keptPunctureLocations p k)

private noncomputable def selectedPunctureEquivFin (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) : SelectedPunctureLocation p k ≃ Fin k := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine
    { toFun := fun point => ⟨point.1.val, by
        exact (Finset.mem_filter.mp point.2).2⟩
      invFun := fun index => ⟨(index.1 : ZMod p), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (index.2.trans_le hkp)]
        exact index.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Subtype.ext
    exact ZMod.natCast_zmod_val point.1
  · intro index
    apply Fin.ext
    change ((index.1 : ZMod p).val) = index.1
    exact ZMod.val_natCast_of_lt (index.2.trans_le hkp)

/-- The selected finite set has the requested cardinality. -/
theorem selectedPunctureLocations_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    (selectedPunctureLocations p k).card = k := by
  have hcard := Fintype.card_congr (selectedPunctureEquivFin p k hkp)
  simpa using hcard

/-- The retained finite set has cardinality `p-k`. -/
theorem keptPunctureLocations_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    (keptPunctureLocations p k).card = p - k := by
  rw [keptPunctureLocations, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, ZMod.card, selectedPunctureLocations_card p k hkp]

private theorem keptPunctureLocation_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fintype.card (KeptPunctureLocation p k) = p - k := by
  simpa using keptPunctureLocations_card p k hkp

/-- Restriction to the selected coordinates. -/
def restrictSelected (p k : Nat) [Fact p.Prime] :
    Word (ZMod p) (ZMod p) →ₗ[ZMod p]
      Word (ZMod p) (SelectedPunctureLocation p k) where
  toFun word point := word point.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the retained coordinates. -/
def restrictKept (p k : Nat) [Fact p.Prime] :
    Word (ZMod p) (ZMod p) →ₗ[ZMod p]
      Word (ZMod p) (KeptPunctureLocation p k) where
  toFun word point := word point.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrictSelected_apply {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) (point : SelectedPunctureLocation p k) :
    restrictSelected p k word point = word point.1 :=
  rfl

@[simp]
theorem restrictKept_apply {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) (point : KeptPunctureLocation p k) :
    restrictKept p k word point = word point.1 :=
  rfl

/-- Zero extension from retained to full coordinates. -/
def zeroExtendKept (p k : Nat) [Fact p.Prime] :
    Word (ZMod p) (KeptPunctureLocation p k) →ₗ[ZMod p]
      Word (ZMod p) (ZMod p) where
  toFun word point :=
    if hpoint : point ∈ keptPunctureLocations p k then word ⟨point, hpoint⟩ else 0
  map_add' left right := by
    funext point
    by_cases hpoint : point ∈ keptPunctureLocations p k <;> simp [hpoint]
  map_smul' scalar word := by
    funext point
    by_cases hpoint : point ∈ keptPunctureLocations p k <;> simp [hpoint]

@[simp]
theorem restrictKept_zeroExtendKept {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    restrictKept p k (zeroExtendKept p k word) = word := by
  ext point
  simp [zeroExtendKept, point.2]

@[simp]
private theorem restrictSelected_zeroExtendKept {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    restrictSelected p k (zeroExtendKept p k word) = 0 := by
  ext point
  simp [zeroExtendKept, keptPunctureLocations, point.2]

/-- Puncturing is the actual image of a full Reed--Solomon code under retained
coordinate restriction. -/
def puncturedReedSolomonCode (p l k : Nat) [Fact p.Prime] :
    LinearCode (ZMod p) (KeptPunctureLocation p k) where
  carrier := (reedSolomonCode p l).carrier.map (restrictKept p k)

@[simp]
theorem mem_puncturedReedSolomonCode {p l k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    word ∈ (puncturedReedSolomonCode p l k).carrier ↔
      ∃ full : Word (ZMod p) (ZMod p),
        full ∈ (reedSolomonCode p l).carrier ∧ restrictKept p k full = word := by
  simp [puncturedReedSolomonCode]

/-- The full codewords satisfying the literal zero condition on selected
coordinates. -/
def shortenedReedSolomonDomain (p l k : Nat) [Fact p.Prime] :
    Submodule (ZMod p) (Word (ZMod p) (ZMod p)) :=
  (reedSolomonCode p l).carrier ⊓ LinearMap.ker (restrictSelected p k)

/-- Shortening is the retained restriction of the actual zero-condition
submodule. -/
def shortenedReedSolomonCode (p l k : Nat) [Fact p.Prime] :
    LinearCode (ZMod p) (KeptPunctureLocation p k) where
  carrier := (shortenedReedSolomonDomain p l k).map (restrictKept p k)

@[simp]
theorem mem_shortenedReedSolomonCode {p l k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    word ∈ (shortenedReedSolomonCode p l k).carrier ↔
      ∃ full : Word (ZMod p) (ZMod p),
        full ∈ (reedSolomonCode p l).carrier ∧
          restrictSelected p k full = 0 ∧ restrictKept p k full = word := by
  simp [shortenedReedSolomonCode, shortenedReedSolomonDomain, and_assoc]

theorem shortenedReedSolomonCode_le_puncturedReedSolomonCode
    (p l k : Nat) [Fact p.Prime] :
    (shortenedReedSolomonCode p l k).carrier ≤
      (puncturedReedSolomonCode p l k).carrier := by
  intro word hword
  rcases (mem_shortenedReedSolomonCode word).1 hword with
    ⟨full, hfull, _hselected, rfl⟩
  exact (mem_puncturedReedSolomonCode _).2 ⟨full, hfull, rfl⟩

private theorem wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
    {p k : Nat} [Fact p.Prime]
    (left right : Word (ZMod p) (ZMod p))
    (hselected : restrictSelected p k left = 0) :
    wordPairing (restrictKept p k left) (restrictKept p k right) =
      wordPairing left right := by
  classical
  letI selectedPunctureSubtypeFintype :
      Fintype {point : ZMod p // point ∈ selectedPunctureLocations p k} :=
    Subtype.fintype _
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : ZMod p => point ∈ selectedPunctureLocations p k)
      (fun point => left point * right point)
  let complementKept :
      {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k} ≃
        KeptPunctureLocation p k :=
    { toFun := fun point => ⟨point.1,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, point.2⟩⟩
      invFun := fun point => ⟨point.1, (Finset.mem_sdiff.mp point.2).2⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change (∑ point : KeptPunctureLocation p k, left point.1 * right point.1) =
    ∑ point : ZMod p, left point * right point
  have hselectedSum :
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    have hpoint : left point.1 = 0 := by
      simpa using congrFun hselected
        (⟨point.1, point.2⟩ : SelectedPunctureLocation p k)
    rw [hpoint]
    simp
  have hcomplement :
      (∑ point : {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) =
        ∑ point : ZMod p, left point * right point := by
    rw [hselectedSum, zero_add] at hsplit
    exact hsplit
  have hequiv :
      (∑ point : {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) =
        ∑ point : KeptPunctureLocation p k, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  exact hequiv.symm.trans hcomplement

private def degreeLTEmbed (p a b : Nat) (hab : a ≤ b) :
    Polynomial.degreeLT (ZMod p) a →ₗ[ZMod p] Polynomial.degreeLT (ZMod p) b :=
  Submodule.inclusion (Polynomial.degreeLT_mono (R := ZMod p) hab)

private noncomputable def selectedInterpolation (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    Polynomial.degreeLT (ZMod p) k := by
  let equivalence := Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)
  let raw := equivalence.symm word
  refine ⟨raw.1, ?_⟩
  simpa [selectedPunctureLocations_card p k hkp] using raw.2

private theorem restrictSelected_evaluation_selectedInterpolation
    (p k : Nat) [Fact p.Prime] (hkp : k ≤ p)
    (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    restrictSelected p k (evaluationLinearMap p k (selectedInterpolation p k hkp word)) =
      word := by
  ext point
  change
    ((Lagrange.funEquivDegreeLT
      (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
      (by
        intro left hleft right hright heq
        exact heq)).symm word).1.eval point.1 = word point
  exact congrFun ((Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)).apply_symm_apply word) point

private theorem restrictSelected_evaluation_degreeLTEmbed
    (p a b k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hab : a ≤ b)
    (word : Word (ZMod p) (SelectedPunctureLocation p k))
    (hka : k = a) :
    restrictSelected p k
      (evaluationLinearMap p b
        (degreeLTEmbed p a b hab (by simpa [hka] using selectedInterpolation p k hkp word))) =
      word := by
  subst a
  change restrictSelected p k
      (evaluationLinearMap p k (selectedInterpolation p k hkp word)) = word
  exact restrictSelected_evaluation_selectedInterpolation p k hkp word

private theorem restrictSelected_surjective_on_reedSolomonCode
    (p l k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) :
    Function.Surjective
      ((restrictSelected p k).domRestrict (reedSolomonCode p l).carrier) := by
  intro word
  let polynomial : Polynomial.degreeLT (ZMod p) l :=
    degreeLTEmbed p k l hkl (selectedInterpolation p k hkp word)
  refine ⟨⟨evaluationLinearMap p l polynomial,
    evaluation_mem_reedSolomonCode p l polynomial⟩, ?_⟩
  exact restrictSelected_evaluation_degreeLTEmbed p k l k hkp hkl word rfl

private def shortenedDomainEquivRestrictSelectedKernel {p l k : Nat} [Fact p.Prime] :
    shortenedReedSolomonDomain p l k ≃ₗ[ZMod p]
      LinearMap.ker ((restrictSelected p k).domRestrict (reedSolomonCode p l).carrier) where
  toFun word :=
    ⟨⟨word.1, word.property.1⟩, by
      change restrictSelected p k word.1 = 0
      exact word.property.2⟩
  invFun word :=
    ⟨word.1.1, ⟨word.1.property, by
      change restrictSelected p k word.1.1 = 0
      exact word.property⟩⟩
  left_inv word := Subtype.ext rfl
  right_inv word := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictKept_injective_on_shortenedReedSolomonDomain
    {p l k : Nat} [Fact p.Prime] :
    Function.Injective
      ((restrictKept p k).domRestrict (shortenedReedSolomonDomain p l k)) := by
  intro left right heq
  apply Subtype.ext
  funext point
  by_cases hselected : point ∈ selectedPunctureLocations p k
  · have hleft : restrictSelected p k left.1 = 0 := left.property.2
    have hright : restrictSelected p k right.1 = 0 := right.property.2
    have hpoint := congrFun hleft ⟨point, hselected⟩
    have hpoint' := congrFun hright ⟨point, hselected⟩
    simpa using hpoint.trans hpoint'.symm
  · have hkept : point ∈ keptPunctureLocations p k := by
      simp [keptPunctureLocations, hselected]
    have hpoint := congrFun heq ⟨point, hkept⟩
    simpa using hpoint

/-- The dimension of the actual shortened code, obtained by selected-value
interpolation, rank-nullity, and injective restriction to retained points. -/
theorem shortenedReedSolomonCode_dimension (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (hkl : k ≤ l) (hlp : l ≤ p) :
    Dimension (shortenedReedSolomonCode p l k) = l - k := by
  let selectedMap := (restrictSelected p k).domRestrict (reedSolomonCode p l).carrier
  have hsurjective : Function.Surjective selectedMap := by
    exact restrictSelected_surjective_on_reedSolomonCode p l k hkp hkl
  have hrange : LinearMap.range selectedMap = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  have hrank := LinearMap.finrank_range_add_finrank_ker selectedMap
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card] at hrank
  have hrank' :
      k + Module.finrank (ZMod p) (LinearMap.ker selectedMap) =
        Dimension (reedSolomonCode p l) := by
    simpa [selectedMap, Dimension, selectedPunctureLocations_card p k hkp] using hrank
  have hdomain :
      Module.finrank (ZMod p) (shortenedReedSolomonDomain p l k) =
        Module.finrank (ZMod p) (LinearMap.ker selectedMap) := by
    exact LinearEquiv.finrank_eq shortenedDomainEquivRestrictSelectedKernel
  have hcode :
      Dimension (shortenedReedSolomonCode p l k) =
        Module.finrank (ZMod p) (shortenedReedSolomonDomain p l k) := by
    change Module.finrank (ZMod p)
      ((shortenedReedSolomonDomain p l k).map (restrictKept p k)) = _
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj
      restrictKept_injective_on_shortenedReedSolomonDomain
  have hrank'' :
      k + Module.finrank (ZMod p) (LinearMap.ker selectedMap) = l :=
    hrank'.trans (reedSolomonCode_dimension p l hlp)
  calc
    Dimension (shortenedReedSolomonCode p l k) =
        Module.finrank (ZMod p) (shortenedReedSolomonDomain p l k) := hcode
    _ = Module.finrank (ZMod p) (LinearMap.ker selectedMap) := hdomain
    _ = l - k := by omega

private theorem restrictKept_injective_on_reedSolomonCode
    (p l k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hlength : l ≤ p - k) :
    Function.Injective
      ((restrictKept p k).domRestrict (reedSolomonCode p l).carrier) := by
  intro left right heq
  rcases (mem_reedSolomonCode p l left.1).1 left.2 with ⟨leftPolynomial, hleft⟩
  rcases (mem_reedSolomonCode p l right.1).1 right.2 with ⟨rightPolynomial, hright⟩
  have hpolynomials : leftPolynomial = rightPolynomial := by
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (keptPunctureLocations p k)
    · exact (Polynomial.mem_degreeLT.mp leftPolynomial.2).trans_le
        (by simpa [keptPunctureLocations_card p k hkp] using hlength)
    · exact (Polynomial.mem_degreeLT.mp rightPolynomial.2).trans_le
        (by simpa [keptPunctureLocations_card p k hkp] using hlength)
    · intro point hpoint
      have hpoint' := congrFun heq ⟨point, hpoint⟩
      calc
        leftPolynomial.1.eval point = left.1 point := by
          exact congrFun hleft point
        _ = right.1 point := by
          change left.1 point = right.1 point at hpoint'
          exact hpoint'
        _ = rightPolynomial.1.eval point := by
          exact (congrFun hright point).symm
  apply Subtype.ext
  calc
    left.1 = evaluationLinearMap p l leftPolynomial := hleft.symm
    _ = evaluationLinearMap p l rightPolynomial :=
      congrArg (evaluationLinearMap p l) hpolynomials
    _ = right.1 := hright

/-- Restricting to at least `l` retained locations does not decrease the
dimension of the degree-`< l` evaluation code. -/
theorem puncturedReedSolomonCode_dimension (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (hlength : l ≤ p - k) :
    Dimension (puncturedReedSolomonCode p l k) = l := by
  change Module.finrank (ZMod p)
    ((reedSolomonCode p l).carrier.map (restrictKept p k)) = l
  rw [← LinearMap.range_domRestrict]
  rw [LinearMap.finrank_range_of_inj
    (restrictKept_injective_on_reedSolomonCode p l k hkp hlength)]
  exact reedSolomonCode_dimension p l (Nat.le_trans hlength (Nat.sub_le _ _))

private theorem puncturedReedSolomonCode_le_dual_shortenedComplementary
    (p l k : Nat) [Fact p.Prime] (hlp : l ≤ p) :
    (puncturedReedSolomonCode p l k).carrier ≤
      (shortenedReedSolomonCode p (p - l) k).dual.carrier := by
  intro word hword
  refine ((shortenedReedSolomonCode p (p - l) k).mem_dual word).2 ?_
  intro shortened hshortened
  rcases (mem_puncturedReedSolomonCode word).1 hword with
    ⟨fullWord, hfullWord, hrestrictWord⟩
  rcases (mem_shortenedReedSolomonCode shortened).1 hshortened with
    ⟨fullShortened, hfullShortened, hselected, hrestrictShortened⟩
  have hfullWordDual : fullWord ∈ (reedSolomonCode p (p - l)).dual.carrier := by
    rw [reedSolomonCode_dual p (p - l) (Nat.sub_le _ _)]
    simpa only [Nat.sub_sub_self hlp] using hfullWord
  have horthogonal := (reedSolomonCode p (p - l)).orthogonal_of_mem_dual
    hfullWordDual hfullShortened
  rw [← hrestrictWord, ← hrestrictShortened]
  calc
    wordPairing (restrictKept p k fullWord)
        (restrictKept p k fullShortened) =
        wordPairing (restrictKept p k fullShortened)
          (restrictKept p k fullWord) := by
      simp only [wordPairing_apply, dotProduct_comm]
    _ = wordPairing fullShortened fullWord :=
      wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
        fullShortened fullWord hselected
    _ = 0 := by
      simpa [wordPairing_apply, dotProduct_comm] using horthogonal

/-- Complementary shortening/puncturing duality for the source's actual
coordinate partition. -/
theorem shortenedReedSolomonCode_dual_eq_punctured (p l k : Nat) [Fact p.Prime]
    (h : Admissible p l k) :
    (shortenedReedSolomonCode p (p - l) k).dual.carrier =
      (puncturedReedSolomonCode p l k).carrier := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hkm : k ≤ p - l := by omega
  have hkeptLength : l ≤ p - k := by omega
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact puncturedReedSolomonCode_le_dual_shortenedComplementary p l k hlp
  · change Dimension (puncturedReedSolomonCode p l k) =
      Dimension (shortenedReedSolomonCode p (p - l) k).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      puncturedReedSolomonCode_dimension p l k hkp hkeptLength,
      shortenedReedSolomonCode_dimension p (p - l) k hkp hkm (Nat.sub_le _ _)]
    simp [Length, keptPunctureLocation_card p k hkp]
    omega

/-- A genuine universal lower-bound property for a concrete linear code. -/
def MinimumDistanceAtLeast {F : Type} {ι : Type} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (code : LinearCode F ι) (d : Nat) : Prop :=
  ∀ word : Word F ι, word ∈ code.carrier → word ≠ 0 → d ≤ HammingWeight word

private theorem puncturedComplementaryReedSolomon_weight_lower_bound
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistanceAtLeast (puncturedReedSolomonCode p (p - l) k) (l + 1 - k) := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  intro word hword hwordNe
  rcases (mem_puncturedReedSolomonCode word).1 hword with
    ⟨full, hfull, hrestrict⟩
  rcases (mem_reedSolomonCode p (p - l) full).1 hfull with ⟨polynomial, hpoly⟩
  have hpolynomialNe : polynomial.1 ≠ 0 := by
    intro hzero
    apply hwordNe
    rw [← hrestrict, ← hpoly]
    ext point
    simp [evaluationLinearMap_apply, hzero]
  let zeroCoordinates : Finset (KeptPunctureLocation p k) :=
    Finset.univ.filter fun point => word point = 0
  let zeroImage : Finset (ZMod p) :=
    zeroCoordinates.map ⟨Subtype.val, Subtype.val_injective⟩
  have hroots : zeroImage.val ⊆ polynomial.1.roots := by
    intro point hpoint
    rcases Finset.mem_map.1 hpoint with ⟨kept, hkept, rfl⟩
    rw [Polynomial.mem_roots hpolynomialNe]
    change polynomial.1.eval kept.1 = 0
    have hzero := (Finset.mem_filter.1 hkept).2
    simpa [zeroCoordinates, ← hrestrict, ← hpoly] using hzero
  have hzeroCard : zeroCoordinates.card ≤ polynomial.1.natDegree := by
    rw [← Finset.card_map]
    exact Polynomial.card_le_degree_of_subset_roots hroots
  have hdegree : polynomial.1.natDegree < p - l := by
    have hdegree' := Polynomial.mem_degreeLT.mp polynomial.2
    rw [Polynomial.degree_eq_natDegree hpolynomialNe] at hdegree'
    exact_mod_cast hdegree'
  have hkeptCard : Fintype.card (KeptPunctureLocation p k) = p - k :=
    keptPunctureLocation_card p k hkp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun point : KeptPunctureLocation p k => word point ≠ 0)
  have hweightPartition : HammingWeight word + zeroCoordinates.card =
      Fintype.card (KeptPunctureLocation p k) := by
    simpa [HammingWeight, hammingSupport, zeroCoordinates] using hpartition
  rw [hkeptCard] at hweightPartition
  omega

private noncomputable def complementaryWitnessRoots
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) : Finset (ZMod p) :=
  Classical.choose (Finset.exists_subset_card_eq
    (s := keptPunctureLocations p k) (n := p - l - 1) (by
      rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
      rw [keptPunctureLocations_card p k (hkl.trans hlp)]
      omega))

private theorem complementaryWitnessRoots_subset
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    complementaryWitnessRoots p l k h ⊆ keptPunctureLocations p k :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := keptPunctureLocations p k) (n := p - l - 1) (by
      rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
      rw [keptPunctureLocations_card p k (hkl.trans hlp)]
      omega))).1

private theorem complementaryWitnessRoots_card
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    (complementaryWitnessRoots p l k h).card = p - l - 1 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := keptPunctureLocations p k) (n := p - l - 1) (by
      rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
      rw [keptPunctureLocations_card p k (hkl.trans hlp)]
      omega))).2

private noncomputable def complementaryWitnessPolynomial
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    Polynomial.degreeLT (ZMod p) (p - l) :=
  ⟨Lagrange.nodal (complementaryWitnessRoots p l k h) (fun point : ZMod p => point), by
    have hpTwo : 2 ≤ p := h.1.two_le
    have hk : 1 ≤ k := h.2.1
    have hkl : k ≤ l := h.2.2.1
    have hlp : l ≤ p := h.2.2.2.1
    have hproduct : 3 * l ≤ p + 1 := h.2.2.2.2
    have hcomplementPos : 0 < p - l := by omega
    rw [Polynomial.mem_degreeLT, Lagrange.degree_nodal,
      complementaryWitnessRoots_card p l k h]
    exact_mod_cast (by omega : p - l - 1 < p - l)⟩

private theorem complementaryWitness_evaluation_zero_iff
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k)
    (point : KeptPunctureLocation p k) :
    evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h) point.1 = 0 ↔
      point.1 ∈ complementaryWitnessRoots p l k h := by
  constructor
  · intro hzero
    by_contra hnot
    have hne : ∀ root ∈ complementaryWitnessRoots p l k h, point.1 ≠ root := by
      intro root hroot heq
      apply hnot
      simpa [heq] using hroot
    have hnodalNe :
        (Lagrange.nodal (complementaryWitnessRoots p l k h)
          (fun root : ZMod p => root)).eval point.1 ≠ 0 :=
      Lagrange.eval_nodal_not_at_node
        (s := complementaryWitnessRoots p l k h)
        (v := fun root : ZMod p => root) (x := point.1) hne
    apply hnodalNe
    simpa only [evaluationLinearMap_apply, complementaryWitnessPolynomial] using hzero
  · intro hroot
    simpa [evaluationLinearMap_apply, complementaryWitnessPolynomial] using
      (Lagrange.eval_nodal_at_node
        (s := complementaryWitnessRoots p l k h)
        (v := fun root : ZMod p => root) (i := point.1) hroot)

private theorem complementaryWitness_weight
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    HammingWeight
      (restrictKept p k
        (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h))) =
      l + 1 - k := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  let word := restrictKept p k
    (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k
      ⟨hp, hk, hkl, hlp, hproduct⟩))
  let zeroCoordinates : Finset (KeptPunctureLocation p k) :=
    Finset.univ.filter fun point => word point = 0
  let zeroImage : Finset (ZMod p) :=
    zeroCoordinates.map ⟨Subtype.val, Subtype.val_injective⟩
  have hzeroImage : zeroImage = complementaryWitnessRoots p l k
      ⟨hp, hk, hkl, hlp, hproduct⟩ := by
    ext point
    constructor
    · intro hpoint
      rcases Finset.mem_map.1 hpoint with ⟨kept, hkept, rfl⟩
      have hzero := (Finset.mem_filter.1 hkept).2
      exact (complementaryWitness_evaluation_zero_iff p l k
        ⟨hp, hk, hkl, hlp, hproduct⟩ kept).1 (by simpa [word] using hzero)
    · intro hpoint
      have hkept : point ∈ keptPunctureLocations p k :=
        complementaryWitnessRoots_subset p l k ⟨hp, hk, hkl, hlp, hproduct⟩ hpoint
      refine Finset.mem_map.2 ⟨⟨point, hkept⟩, ?_, rfl⟩
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (complementaryWitness_evaluation_zero_iff p l k
        ⟨hp, hk, hkl, hlp, hproduct⟩ ⟨point, hkept⟩).2 hpoint
  have hmapCard : zeroImage.card = zeroCoordinates.card := by
    simp only [zeroImage, Finset.card_map]
  have hzeroCard : zeroCoordinates.card = p - l - 1 := by
    calc
      zeroCoordinates.card = zeroImage.card := hmapCard.symm
      _ = (complementaryWitnessRoots p l k
          ⟨hp, hk, hkl, hlp, hproduct⟩).card :=
        congrArg Finset.card hzeroImage
      _ = p - l - 1 := complementaryWitnessRoots_card p l k
        ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkeptCard : Fintype.card (KeptPunctureLocation p k) = p - k :=
    keptPunctureLocation_card p k hkp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun point : KeptPunctureLocation p k => word point ≠ 0)
  have hweightPartition : HammingWeight word + zeroCoordinates.card =
      Fintype.card (KeptPunctureLocation p k) := by
    simpa [HammingWeight, hammingSupport, zeroCoordinates] using hpartition
  rw [hkeptCard] at hweightPartition
  change HammingWeight word = _
  omega

private theorem complementaryWitness_nonzero
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    restrictKept p k
      (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h)) ≠ 0 := by
  have hweight := complementaryWitness_weight p l k h
  intro hzero
  have hweightZero : 0 = l + 1 - k := by
    simpa [hzero] using hweight
  have : l + 1 - k = 0 := hweightZero.symm
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  omega

/-- The complementary punctured Reed--Solomon code has its actual exact
distance.  The lower half counts polynomial roots; the upper half is the
explicit nodal product over retained locations. -/
theorem puncturedComplementaryReedSolomon_minimumDistance
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistance (puncturedReedSolomonCode p (p - l) k) (l + 1 - k) := by
  let witness := restrictKept p k
    (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h))
  have hwitness : witness ∈ (puncturedReedSolomonCode p (p - l) k).carrier := by
    apply (mem_puncturedReedSolomonCode witness).2
    refine ⟨evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h),
      evaluation_mem_reedSolomonCode p (p - l) (complementaryWitnessPolynomial p l k h), rfl⟩
  have hwitnessNe : witness ≠ 0 := by
    exact complementaryWitness_nonzero p l k h
  have hwitnessWeight : HammingWeight witness = l + 1 - k := by
    exact complementaryWitness_weight p l k h
  refine ⟨witness, hwitness, hwitnessNe, hwitnessWeight, ?_⟩
  exact puncturedComplementaryReedSolomon_weight_lower_bound p l k h

/-- The source-advertised `l-k` distance is exported only as a safe lower
bound; the preceding theorem retains the stronger exact `l+1-k` result. -/
theorem puncturedComplementaryReedSolomon_safeDistance
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistanceAtLeast (puncturedReedSolomonCode p (p - l) k) (l - k) := by
  rcases puncturedComplementaryReedSolomon_minimumDistance p l k h with
    ⟨witness, hwitness, hwitnessNe, hwitnessWeight, hleast⟩
  intro word hword hwordNe
  exact (by omega : l - k ≤ l + 1 - k).trans (hleast word hword hwordNe)

/-- The actual retained length. -/
noncomputable def kt19Length (p k : Nat) [Fact p.Prime] : Nat :=
  Length (ZMod p) (KeptPunctureLocation p k)

/-- The CSS logical dimension determined by the two actual shortened
Reed--Solomon stabilizer spaces. -/
noncomputable def kt19LogicalDimension (p l k : Nat) [Fact p.Prime] : Nat :=
  kt19Length p k - Dimension (shortenedReedSolomonCode p l k) -
    Dimension (shortenedReedSolomonCode p (p - l) k)

/-- The safe source-facing distance parameter. -/
def kt19SafeDistance (p l k : Nat) : Nat := l - k

/-- The source-correct concrete family parameters.  The length and logical
dimension are computed from the retained coordinate type and actual shortened
code dimensions, while the safe distance is justified by the exact punctured
distance theorem above. -/
theorem kt19_family_parameters (p l k : Nat) [Fact p.Prime]
    (h : Admissible p l k) :
    kt19Length p k = p - k ∧
      kt19LogicalDimension p l k = k ∧
        kt19SafeDistance p l k ≥ l - k := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hkm : k ≤ p - l := by omega
  have hlength : kt19Length p k = p - k := by
    simp [kt19Length, Length, keptPunctureLocation_card p k hkp]
  refine ⟨hlength, ?_, by simp [kt19SafeDistance]⟩
  rw [kt19LogicalDimension, hlength,
    shortenedReedSolomonCode_dimension p l k hkp hkl hlp,
    shortenedReedSolomonCode_dimension p (p - l) k hkp hkm (Nat.sub_le _ _)]
  omega

end KT19ReedSolomon
end Coding
end QEC
