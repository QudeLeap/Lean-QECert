import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXQConcreteCoherence

/-!
# Exact native RX differential masks and their least incidence closure

All masks are the original `MultiscaleDecoder.maskWord`; every incidence,
coordinate and selected map is the original actual alternating construction.
The operator identity quantifies over all lower correction words. It is not
inferred from one recovered syndrome, whose coefficients may cancel.

The finite closure below is derived from actual Q--Z incidence. It does not
replace the original decoding graph or its marked components. In particular,
this module asserts neither the original ALL-component mask contract nor a
single-Q-parent selected-image contract, both of which have actual obstructions.

-/
noncomputable section
namespace QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators

/-! A finite linear algebra lemma, using the original mask operation. -/
private def maskLinear {C : Type} [Fintype C] [DecidableEq C]
    (A : Finset C) : Word BDL26Field C →ₗ[BDL26Field] Word BDL26Field C where
  toFun := maskWord A
  map_add' a b := by
    funext p
    by_cases hp : p ∈ A <;> simp [maskWord, hp]
  map_smul' c a := by
    funext p
    by_cases hp : p ∈ A <;> simp [maskWord, hp]

private theorem mask_basis {C : Type} [Fintype C] [DecidableEq C]
    (A : Finset C) (q : C) :
    maskWord A (canonicalBasisWord (F := BDL26Field) q) =
      if q ∈ A then canonicalBasisWord q else 0 := by
  funext p
  by_cases hq : q ∈ A <;> by_cases hp : p = q
  · subst p; simp [maskWord, hq]
  · simp [maskWord, canonicalBasisWord, hq, hp]
  · subst p; simp [maskWord, hq]
  · simp [maskWord, canonicalBasisWord, hq, hp]

private theorem word_decomposition {C : Type} [Fintype C] [DecidableEq C]
    (w : Word BDL26Field C) :
    (∑ q : C, w q • canonicalBasisWord (F := BDL26Field) q) = w := by
  funext p
  simp [canonicalBasisWord, Pi.single_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eq_comm]

/-- An all-input mask identity is exactly a condition on every NONZERO
matrix coefficient. Zero coefficients impose no condition on either mask. -/
theorem mask_commutes_iff_matrix
    {C E : Type} [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]
    (T : Word BDL26Field C →ₗ[BDL26Field] Word BDL26Field E)
    (A : Finset C) (B : Finset E) :
    (∀ w, maskWord B (T w) = T (maskWord A w)) ↔
      ∀ q p, T (canonicalBasisWord q) p ≠ 0 → (p ∈ B ↔ q ∈ A) := by
  constructor
  · intro hw q p hqp
    have hm := congrFun (hw (canonicalBasisWord q)) p
    rw [mask_basis] at hm
    by_cases hp : p ∈ B <;> by_cases hq : q ∈ A
    · exact iff_of_true hp hq
    · have hz : T (canonicalBasisWord q) p = 0 := by
        simpa [maskWord, hp, hq] using hm
      exact (hqp hz).elim
    · have hz : T (canonicalBasisWord q) p = 0 := by
        simpa [maskWord, hp, hq] using hm.symm
      exact (hqp hz).elim
    · exact iff_of_false hp hq
  · intro hc
    have hb : ∀ q, maskWord B (T (canonicalBasisWord q)) =
        T (maskWord A (canonicalBasisWord q)) := by
      intro q
      rw [mask_basis]
      funext p
      by_cases hqp : T (canonicalBasisWord q) p = 0
      · by_cases hp : p ∈ B <;> by_cases hq : q ∈ A <;>
          simp [maskWord, hp, hq, hqp]
      · have hh := hc q p hqp
        by_cases hp : p ∈ B
        · have hq := hh.mp hp
          simp [maskWord, hp, hq]
        · have hq : q ∉ A := fun h => hp (hh.mpr h)
          simp [maskWord, hp, hq]
    have he : (maskLinear B).comp T = T.comp (maskLinear A) := by
      apply LinearMap.ext
      intro w
      rw [← word_decomposition w]
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro q _
      exact congrArg (fun v => w q • v) (hb q)
    intro w
    exact LinearMap.congr_fun he w

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

/-- The actual full native syndrome operator, not an assumed basis-image API. -/
def nativeDifferential :
    Word BDL26Field (state S i.val).presentation.Q →ₗ[BDL26Field]
      Word BDL26Field (FamilyZ S depth i.succ) :=
  ((indexedDecoderData S depth).selectedMap i).map2.comp
    ((indexedFamily S depth).coboundary1 i.castSucc)

@[simp] theorem nativeDifferential_basis (q : (state S i.val).presentation.Q) :
    nativeDifferential S depth i (canonicalBasisWord q) = basisImage S depth i q := rfl

/-- Exact all-input characterization at every actual legal RX step. Both real
Z copies occur, and no constraint is introduced on unselected connectors. -/
theorem native_mask_commutes_iff (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) :
    (∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) ↔
    ∀ q z (copy : Fin 2), (state S i.val).presentation.qz q z = true →
      (((rxData S depth i h).induced.zPairEquiv (z,copy)).val ∈ B ↔ q ∈ A) := by
  rw [mask_commutes_iff_matrix]
  constructor
  · intro hc q z copy hqz
    apply hc q _
    rw [nativeDifferential_basis, basisImage_pair, if_pos hqz]
    exact one_ne_zero
  · intro hc q p hqp
    have hm : p ∈ hammingSupport (basisImage S depth i q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqp⟩
    obtain ⟨z,copy,hqz,rfl⟩ := (basisImage_mem_iff S depth i h q p).mp hm
    exact hc q z copy hqz

/-- The existing true selected regions, joined without a new owner model. -/
def nativeRegion (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q) : Finset (FamilyZ S depth i.succ) :=
  A.biUnion (BDL26RXQBlockTransport.twoCopyIncidentZ S depth i h)

private theorem pair_mem_basis_support (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q) (z : (state S i.val).presentation.Z)
    (copy : Fin 2) :
    ((rxData S depth i h).induced.zPairEquiv (z,copy)).val ∈
      hammingSupport (basisImage S depth i q) ↔
      (state S i.val).presentation.qz q z = true := by
  by_cases hqz : (state S i.val).presentation.qz q z = true <;>
    simp [hammingSupport, basisImage_pair S depth i h, hqz]

@[simp] theorem pair_mem_nativeRegion (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (z : (state S i.val).presentation.Z) (copy : Fin 2) :
    ((rxData S depth i h).induced.zPairEquiv (z,copy)).val ∈ nativeRegion S depth i h A ↔
      ∃ q ∈ A, (state S i.val).presentation.qz q z = true := by
  simp only [nativeRegion, Finset.mem_biUnion, ← basisImage_support S depth i h,
    pair_mem_basis_support S depth i h]

/-- Stability under sharing an ACTUAL Z incidence. This is derived incidence
algebra and is not a replacement definition of the #848 decoding graph. -/
def IncidenceSaturated (A : Finset (state S i.val).presentation.Q) : Prop :=
  ∀ q ∈ A, ∀ r z, (state S i.val).presentation.qz q z = true →
    (state S i.val).presentation.qz r z = true → r ∈ A

/-- This is the exact additional closure required by a forward incident-Z mask.
It cannot be omitted even if a particular input has syndrome cancellation. -/
theorem nativeRegion_commutes_iff_saturated (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q) :
    (∀ w, maskWord (nativeRegion S depth i h A) (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) ↔ IncidenceSaturated S depth i A := by
  rw [native_mask_commutes_iff S depth i h]
  constructor
  · intro hc q hq r z hqz hrz
    exact (hc r z 0 hrz).mp
      ((pair_mem_nativeRegion S depth i h A z 0).mpr ⟨q,hq,hqz⟩)
  · intro hs q z copy hqz
    rw [pair_mem_nativeRegion]
    constructor
    · rintro ⟨r,hr,hrz⟩
      exact hs r hr q z hrz hqz
    · intro hq
      exact ⟨q,hq,hqz⟩

/-- Every commuting lower/upper pair forces shared-Z saturation on its lower
mask, even if its upper mask additionally contains arbitrary exterior points. -/
theorem commuting_lower_saturated (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ))
    (hc : ∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) : IncidenceSaturated S depth i A := by
  have hh := (native_mask_commutes_iff S depth i h A B).mp hc
  intro q hq r z hqz hrz
  exact (hh r z 0 hrz).mp ((hh q z 0 hqz).mpr hq)

/-- Construct the least finite incidence-saturated superset; no caller supplies
an admissible lower mask or a saturation certificate. -/
def incidenceHull (A : Finset (state S i.val).presentation.Q) :
    Finset (state S i.val).presentation.Q :=
  Finset.univ.filter (fun q => ∀ C : Finset (state S i.val).presentation.Q,
    A ⊆ C → IncidenceSaturated S depth i C → q ∈ C)

@[simp] theorem mem_incidenceHull (A : Finset (state S i.val).presentation.Q)
    (q : (state S i.val).presentation.Q) : q ∈ incidenceHull S depth i A ↔
    ∀ C : Finset (state S i.val).presentation.Q,
      A ⊆ C → IncidenceSaturated S depth i C → q ∈ C := by
  simp [incidenceHull]

theorem subset_incidenceHull (A : Finset (state S i.val).presentation.Q) :
    A ⊆ incidenceHull S depth i A := by
  intro q hq
  exact (mem_incidenceHull S depth i A q).mpr (fun C hC _ => hC hq)

theorem incidenceHull_saturated (A : Finset (state S i.val).presentation.Q) :
    IncidenceSaturated S depth i (incidenceHull S depth i A) := by
  intro q hq r z hqz hrz
  apply (mem_incidenceHull S depth i A r).mpr
  intro C hC hs
  exact hs q ((mem_incidenceHull S depth i A q).mp hq C hC hs) r z hqz hrz

theorem incidenceHull_minimal (A C : Finset (state S i.val).presentation.Q)
    (hA : A ⊆ C) (hs : IncidenceSaturated S depth i C) :
    incidenceHull S depth i A ⊆ C := by
  intro q hq
  exact (mem_incidenceHull S depth i A q).mp hq C hA hs

theorem incidenceHull_eq_iff (A : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i A = A ↔ IncidenceSaturated S depth i A := by
  constructor
  · intro he
    rw [← he]
    exact incidenceHull_saturated S depth i A
  · intro hs
    exact Finset.Subset.antisymm
      (incidenceHull_minimal S depth i A A (fun _ h => h) hs)
      (subset_incidenceHull S depth i A)

@[simp] theorem incidenceHull_idempotent (A : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i (incidenceHull S depth i A) = incidenceHull S depth i A :=
  (incidenceHull_eq_iff S depth i _).mpr (incidenceHull_saturated S depth i A)

/-- A constructed, non-oracular all-input native mask theorem. -/
theorem incidenceHull_native_mask (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (w : Word BDL26Field (state S i.val).presentation.Q) :
    maskWord (nativeRegion S depth i h (incidenceHull S depth i A))
        (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord (incidenceHull S depth i A) w) :=
  (nativeRegion_commutes_iff_saturated S depth i h _).mpr
    (incidenceHull_saturated S depth i A) w

/-- Any commuting masks containing the seed must contain the constructed lower
hull and its WHOLE two-copy native selected region. -/
theorem incidenceHull_le_every_commuting_pair (h : i.val % 2 = 0)
    (seed A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed ⊆ A)
    (hc : ∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) :
    incidenceHull S depth i seed ⊆ A ∧
      nativeRegion S depth i h (incidenceHull S depth i seed) ⊆ B := by
  have hl := incidenceHull_minimal S depth i seed A hseed
    (commuting_lower_saturated S depth i h A B hc)
  refine ⟨hl, ?_⟩
  intro p hp
  obtain ⟨q,hq,hp⟩ := Finset.mem_biUnion.mp hp
  have hm : p ∈ hammingSupport (basisImage S depth i q) :=
    (basisImage_support S depth i h q).symm ▸ hp
  obtain ⟨z,copy,hqz,rfl⟩ := (basisImage_mem_iff S depth i h q p).mp hm
  exact ((native_mask_commutes_iff S depth i h A B).mp hc q z copy hqz).mpr (hl hq)

/-- Every original unselected coordinate is zero for every input. This keeps
all genuine unparented connectors, rather than discarding them from the domain. -/
theorem nativeDifferential_exterior (h : i.val % 2 = 0)
    (w : Word BDL26Field (state S i.val).presentation.Q)
    (p : FamilyZ S depth i.succ) (hp : p ∉ (rxData S depth i h).zSector) :
    nativeDifferential S depth i w p = 0 := by
  have hrx : (indexedDecoderData S depth).selectedMap i =
      (indexedDecoderData S depth).rxMap i := by
    rw [selectedMap_eq]
    rfl
  change ((indexedDecoderData S depth).selectedMap i).map2 _ p = 0
  rw [hrx]
  exact (rxData S depth i h).induced.map2_auxiliary_zero _ p
    (by simpa only [← (rxData S depth i h).zSector_eq_induced] using hp)

theorem nativeDifferential_connector (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (w : Word BDL26Field (state S i.val).presentation.Q) :
    parent S (i.val+1) (Vertex.z (connector S depth i h q)) = none ∧
      nativeDifferential S depth i w (connector S depth i h q) = 0 :=
  ⟨connector_parent_none S depth i h q,
    nativeDifferential_exterior S depth i h w _ (connector_exterior S depth i h q)⟩

/-- A shared Z incidence gives an explicit BASIS input violating the naive
forward mask whenever its other incident Q is omitted. No cancellation or
single-word implication is used to infer the all-input criterion. -/
theorem shared_unselected_basis_obstruction (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (q r : (state S i.val).presentation.Q) (z : (state S i.val).presentation.Z)
    (hq : q ∈ A) (hr : r ∉ A)
    (hqz : (state S i.val).presentation.qz q z = true)
    (hrz : (state S i.val).presentation.qz r z = true) :
    maskWord (nativeRegion S depth i h A)
        (nativeDifferential S depth i (canonicalBasisWord r)) ≠
      nativeDifferential S depth i (maskWord A (canonicalBasisWord r)) := by
  intro he
  rw [mask_basis, if_neg hr, map_zero] at he
  have hp : ((rxData S depth i h).induced.zPairEquiv (z,0)).val ∈
      nativeRegion S depth i h A :=
    (pair_mem_nativeRegion S depth i h A z 0).mpr ⟨q,hq,hqz⟩
  have hv := congrFun he ((rxData S depth i h).induced.zPairEquiv (z,0)).val
  have hone : (1 : BDL26Field) = 0 := by
    simpa [maskWord, hp, nativeDifferential_basis, basisImage_pair S depth i h, hrz] using hv
  exact one_ne_zero hone

open BDL26FiniteAlternatingCore

/-- A genuine finite seed witness at EVERY actual first RX step and every
original odd scale: Q0 and Q4 share Z0, so the singleton Q0 mask fails on e4. -/
theorem first_step_singleton_obstruction (S : OddScale) (depth : Nat) (hd : 0 < depth) :
    maskWord (nativeRegion S depth ⟨0,hd⟩ (by rfl) {(0 : BaseQubit)})
        (nativeDifferential S depth ⟨0,hd⟩ (canonicalBasisWord (4 : BaseQubit))) ≠
      nativeDifferential S depth ⟨0,hd⟩
        (maskWord {(0 : BaseQubit)} (canonicalBasisWord (4 : BaseQubit))) := by
  apply shared_unselected_basis_obstruction S depth ⟨0,hd⟩ (by rfl)
    {(0 : BaseQubit)} (0 : BaseQubit) (4 : BaseQubit) (0 : BaseZ)
  · exact Finset.mem_singleton_self (0 : BaseQubit)
  · change (4 : BaseQubit) ∉ ({(0 : BaseQubit)} : Finset BaseQubit)
    decide
  · change baseTannerSquarePresentation.qz (0 : BaseQubit) (0 : BaseZ) = true
    decide
  · change baseTannerSquarePresentation.qz (4 : BaseQubit) (0 : BaseZ) = true
    decide

/-- The least closed singleton mask is STRICTLY larger in this actual example;
it contains the second real Q coordinate forced by the shared Z. -/
theorem first_step_hull_forces_other_q (S : OddScale) (depth : Nat) (hd : 0 < depth) :
    (4 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} ∧
      incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} ≠ {(0 : BaseQubit)} := by
  have h0 : (0 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} :=
    subset_incidenceHull S depth ⟨0,hd⟩ _ (Finset.mem_singleton_self (0 : BaseQubit))
  have h4 : (4 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} := by
    apply incidenceHull_saturated S depth ⟨0,hd⟩ _ (0 : BaseQubit) h0 (4 : BaseQubit) (0 : BaseZ)
    · change baseTannerSquarePresentation.qz (0 : BaseQubit) (0 : BaseZ) = true
      decide
    · change baseTannerSquarePresentation.qz (4 : BaseQubit) (0 : BaseZ) = true
      decide
  refine ⟨h4, ?_⟩
  intro he
  rw [he] at h4
  have hnot : (4 : BaseQubit) ∉ ({(0 : BaseQubit)} : Finset BaseQubit) := by decide
  exact hnot h4

end QEC.Coding.BDL26RXDifferentialMasks
end
