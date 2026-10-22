import QEC.Coding.HypergraphProduct.Distance
import QEC.Coding.QuditQubitConversion.U7Gate
import QEC.Distillation.MultiplicativeQuditProtocol.Phase
import QEC.Distillation.MultiplicativeQuditProtocol.Register
import QEC.Distillation.Core.TransversalGate
/-!
# WHY24 weighted-triorthogonal F1024 CSS codes

This file formalizes the finite matrix-to-code construction in WHY24,
`main.tex:963-1236`.  Its input contains only the two source matrix equations
and the nonzero coordinate weights.  Logical independence, the CSS sectors,
distance comparison, normalized encoding, logical Paulis, and the full
sitewise `U_1^(7)` implementation are derived below.
-/

noncomputable section

namespace QEC.Distillation.Why24WeightedTriorthogonalCSS

open QEC.Coding QEC.Semantics
open scoped BigOperators

/-- A finite F1024 word on the displayed physical sites. -/
abbrev Why24Word (Site : Type) := QEC.Coding.Word F1024 Site

/-- The source's asymmetric seventh-degree pairing. -/
def seventhPairing {Site : Type} [Fintype Site]
    (x y z : Why24Word Site) : F1024 :=
  ∑ site : Site, x site ^ 4 * y site ^ 2 * z site

/-- The source's coordinate-weighted bilinear pairing. -/
def weightedPairing {Site : Type} [Fintype Site]
    (sigma x y : Why24Word Site) : F1024 :=
  ∑ site : Site, sigma site * x site * y site

/-- The seventh-power exponent accumulated by a finite F1024 register label. -/
def seventhExponent {Index : Type} [Fintype Index]
    (label : Why24Word Index) : F1024 :=
  ∑ index : Index, label index ^ 7

/-- The right-hand side of the raw seventh-degree matrix equation. -/
def seventhTarget {Logical Stabilizer : Type} [DecidableEq Logical]
    (a b c : Logical ⊕ Stabilizer) : F1024 :=
  match a, b, c with
  | Sum.inl i, Sum.inl j, Sum.inl k => if i = j ∧ j = k then 1 else 0
  | _, _, _ => 0

/-- The right-hand side of the raw weighted bilinear matrix equation. -/
def weightedTarget {Logical Stabilizer : Type} [DecidableEq Logical]
    (tau : Logical → F1024) (a b : Logical ⊕ Stabilizer) : F1024 :=
  match a, b with
  | Sum.inl i, Sum.inl j => if i = j then tau i else 0
  | _, _ => 0

/--
WHY24's raw weighted-triorthogonal matrix data over the concrete field F1024.

No independence, code, distance, encoding, or gate-action conclusion is
stored in this structure.
-/
structure WeightedTriorthogonalMatrix
    (Logical Stabilizer Site : Type)
    [Fintype Logical] [DecidableEq Logical]
    [Fintype Stabilizer] [DecidableEq Stabilizer]
    [Fintype Site] [DecidableEq Site] where
  /-- Rows which label the encoded logical computational basis. -/
  logicalRow : Logical → Why24Word Site
  /-- Rows whose actual span is the X-stabilizer code `G₀`. -/
  stabilizerRow : Stabilizer → Why24Word Site
  /-- Nonzero coordinate weights in the source bilinear equation. -/
  sigma : Why24Word Site
  /-- Nonzero logical diagonal values in the source bilinear equation. -/
  tau : Logical → F1024
  sigma_ne_zero : ∀ site, sigma site ≠ 0
  tau_ne_zero : ∀ logical, tau logical ≠ 0
  seventh_condition : ∀ a b c : Logical ⊕ Stabilizer,
    seventhPairing (Sum.elim logicalRow stabilizerRow a)
      (Sum.elim logicalRow stabilizerRow b)
      (Sum.elim logicalRow stabilizerRow c) = seventhTarget a b c
  weighted_condition : ∀ a b : Logical ⊕ Stabilizer,
    weightedPairing sigma (Sum.elim logicalRow stabilizerRow a)
      (Sum.elim logicalRow stabilizerRow b) = weightedTarget tau a b

namespace WeightedTriorthogonalMatrix

variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]

/-- View logical and stabilizer rows in one finite index type. -/
def row (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Logical ⊕ Stabilizer → Why24Word Site :=
  Sum.elim R.logicalRow R.stabilizerRow

@[simp]
theorem row_inl (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) (a : Logical) :
    R.row (Sum.inl a) = R.logicalRow a :=
  rfl

@[simp]
theorem row_inr (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) (s : Stabilizer) :
    R.row (Sum.inr s) = R.stabilizerRow s :=
  rfl

/-- The actual span of the logical rows `G₁`. -/
def logicalCode (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearCode F1024 Site where
  carrier := Submodule.span F1024 (Set.range R.logicalRow)

/-- The actual span of the stabilizer rows `G₀`. -/
def stabilizerCode (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearCode F1024 Site where
  carrier := Submodule.span F1024 (Set.range R.stabilizerRow)

/-- The actual span `G` of all displayed matrix rows. -/
def rowCode (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearCode F1024 Site where
  carrier := Submodule.span F1024 (Set.range R.row)

/-- The logical component selected by a finite field label. -/
def logicalWord (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) : Why24Word Site :=
  ∑ a : Logical, u a • R.logicalRow a

/-- A word assembled from coefficients on all displayed rows. -/
def combinedWord (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → F1024) : Why24Word Site :=
  ∑ r : Logical ⊕ Stabilizer, q r • R.row r

/-- Weighted pairing is additive in its first word argument. -/
theorem weightedPairing_add_left (sigma x y z : Why24Word Site) :
    weightedPairing sigma (x + y) z =
      weightedPairing sigma x z + weightedPairing sigma y z := by
  unfold weightedPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro site _
  simp only [Pi.add_apply]
  ring

/-- Weighted pairing is additive in its second word argument. -/
theorem weightedPairing_add_right (sigma x y z : Why24Word Site) :
    weightedPairing sigma x (y + z) =
      weightedPairing sigma x y + weightedPairing sigma x z := by
  unfold weightedPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro site _
  simp only [Pi.add_apply]
  ring

/-- Weighted pairing is linear in its first word argument. -/
theorem weightedPairing_smul_left (sigma x y : Why24Word Site) (c : F1024) :
    weightedPairing sigma (c • x) y = c * weightedPairing sigma x y := by
  unfold weightedPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro site _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Weighted pairing is linear in its second word argument. -/
theorem weightedPairing_smul_right (sigma x y : Why24Word Site) (c : F1024) :
    weightedPairing sigma x (c • y) = c * weightedPairing sigma x y := by
  unfold weightedPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro site _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Weighted pairing with a fixed right word as an actual linear map. -/
def weightedPairingLeftLinearMap (sigma y : Why24Word Site) :
    Why24Word Site →ₗ[F1024] F1024 where
  toFun x := weightedPairing sigma x y
  map_add' x z := weightedPairing_add_left sigma x z y
  map_smul' c x := by
    change weightedPairing sigma (c • x) y = c • weightedPairing sigma x y
    rw [weightedPairing_smul_left]
    rfl

@[simp]
theorem weightedPairingLeftLinearMap_apply
    (sigma x y : Why24Word Site) :
    weightedPairingLeftLinearMap sigma y x = weightedPairing sigma x y :=
  rfl

/-- Pairing a logical-row combination with one logical row extracts its coefficient. -/
theorem weightedPairing_logicalWord_logicalRow
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (a : Logical) :
    weightedPairing R.sigma (R.logicalWord u) (R.logicalRow a) =
      u a * R.tau a := by
  classical
  unfold logicalWord
  change weightedPairingLeftLinearMap R.sigma (R.logicalRow a)
      (∑ b, u b • R.logicalRow b) = _
  rw [map_sum]
  simp only [map_smul, weightedPairingLeftLinearMap_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · have h := R.weighted_condition (Sum.inl a) (Sum.inl a)
    simpa [weightedTarget] using congrArg (fun z => u a * z) h
  · intro b _ hba
    have h := R.weighted_condition (Sum.inl b) (Sum.inl a)
    have hzero : weightedPairing R.sigma (R.logicalRow b) (R.logicalRow a) = 0 := by
      simpa [weightedTarget, hba] using h
    rw [hzero, mul_zero]
  · simp

/-- Every stabilizer-span word pairs to zero with every logical row. -/
theorem weightedPairing_stabilizerCode_logicalRow
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.stabilizerCode.carrier) (a : Logical) :
    weightedPairing R.sigma x (R.logicalRow a) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨s, rfl⟩
      have h := R.weighted_condition (Sum.inr s) (Sum.inl a)
      simpa [weightedTarget] using h
  | zero => simp [weightedPairing]
  | add x y _ _ hx hy =>
      rw [weightedPairing_add_left, hx, hy, add_zero]
  | smul c x _ hx =>
      rw [weightedPairing_smul_left, hx, mul_zero]

/-- A logical-span word with all weighted logical pairings zero is zero. -/
theorem eq_zero_of_mem_logicalCode_of_weightedPairing_eq_zero
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.logicalCode.carrier)
    (hpair : ∀ a, weightedPairing R.sigma x (R.logicalRow a) = 0) :
    x = 0 := by
  classical
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun F1024).mp hx
  change R.logicalWord u = x at hu
  have hu0 : u = 0 := by
    funext a
    have h := hpair a
    rw [← hu, R.weightedPairing_logicalWord_logicalRow] at h
    exact (mul_eq_zero.mp h).resolve_right (R.tau_ne_zero a)
  rw [← hu, hu0]
  simp [logicalWord]

/-- WHY24 Lemma `matrixProps` (i): the logical rows are linearly independent. -/
theorem logicalRows_linearIndependent
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    LinearIndependent F1024 R.logicalRow := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro u hu a
  have hpair := congrArg
    (fun x => weightedPairing R.sigma x (R.logicalRow a)) hu
  have hzero : weightedPairing R.sigma (R.logicalWord u) (R.logicalRow a) = 0 := by
    change weightedPairing R.sigma (∑ i, u i • R.logicalRow i) (R.logicalRow a) = 0
    simpa [weightedPairing] using hpair
  rw [R.weightedPairing_logicalWord_logicalRow] at hzero
  exact (mul_eq_zero.mp hzero).resolve_right (R.tau_ne_zero a)

/-- WHY24 Lemma `matrixProps` (ii): `G₀` and `G₁` meet only at zero. -/
theorem stabilizerCode_disjoint_logicalCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.stabilizerCode.carrier ⊓ R.logicalCode.carrier = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxStabilizer : x ∈ R.stabilizerCode.carrier := hx.1
    have hxLogical : x ∈ R.logicalCode.carrier := hx.2
    have hx0 : x = 0 := R.eq_zero_of_mem_logicalCode_of_weightedPairing_eq_zero
      hxLogical (fun a => R.weightedPairing_stabilizerCode_logicalRow hxStabilizer a)
    simpa [hx0]
  · exact bot_le

/-- The full displayed row span is exactly `G₀ + G₁`. -/
theorem rowCode_eq_stabilizerCode_sup_logicalCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.rowCode.carrier =
      R.stabilizerCode.carrier ⊔ R.logicalCode.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨index, rfl⟩
    rcases index with a | s
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨s, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr s, rfl⟩
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl a, rfl⟩

/-- Coordinatewise multiplication by the source weights `sigma_i`. -/
noncomputable def sigmaEquiv
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Why24Word Site ≃ₗ[F1024] Why24Word Site where
  toFun x := fun site => R.sigma site * x site
  invFun x := fun site => (R.sigma site)⁻¹ * x site
  left_inv x := by
    funext site
    field_simp [R.sigma_ne_zero site]
  right_inv x := by
    funext site
    field_simp [R.sigma_ne_zero site]
  map_add' x y := by
    funext site
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext site
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem sigmaEquiv_apply
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (x : Why24Word Site) (site : Site) :
    R.sigmaEquiv x site = R.sigma site * x site :=
  rfl

/-- The invertible coordinate scaling preserves support exactly. -/
theorem hammingSupport_sigmaEquiv
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (x : Why24Word Site) :
    hammingSupport (R.sigmaEquiv x) = hammingSupport x := by
  ext site
  simp [hammingSupport, R.sigma_ne_zero site]

/-- The source coordinate scaling preserves Hamming weight. -/
theorem HammingWeight_sigmaEquiv
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (x : Why24Word Site) :
    HammingWeight (R.sigmaEquiv x) = HammingWeight x := by
  simp only [HammingWeight, R.hammingSupport_sigmaEquiv]

/-- Weighted pairing is ordinary pairing after coordinate scaling. -/
theorem wordPairing_sigmaEquiv
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (x y : Why24Word Site) :
    wordPairing (R.sigmaEquiv x) y = weightedPairing R.sigma x y := by
  unfold wordPairing dotProduct weightedPairing
  apply Finset.sum_congr rfl
  intro site _
  simp only [sigmaEquiv_apply]

/-- Every scaled full-row word is orthogonal to the stabilizer span. -/
theorem sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.rowCode.carrier) :
    R.sigmaEquiv x ∈ R.stabilizerCode.dual.carrier := by
  refine (R.stabilizerCode.mem_dual (R.sigmaEquiv x)).2 ?_
  intro y hy
  rw [R.wordPairing_sigmaEquiv]
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨index, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨s, rfl⟩
          have h := R.weighted_condition index (Sum.inr s)
          simpa [row, weightedTarget] using h
      | zero => simp [weightedPairing]
      | add y z _ _ hy hz => rw [weightedPairing_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [weightedPairing_smul_right, hy, mul_zero]
  | zero => simp [weightedPairing]
  | add x z _ _ hx hz => rw [weightedPairing_add_left, hx, hz, add_zero]
  | smul c x _ hx => rw [weightedPairing_smul_left, hx, mul_zero]

/-- A nontrivial X-sector representative maps to a nontrivial Z-sector representative. -/
theorem sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.rowCode.carrier)
    (hxOutside : x ∉ R.stabilizerCode.carrier) :
    R.sigmaEquiv x ∉ R.rowCode.dual.carrier := by
  classical
  intro hxDual
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun F1024).mp hx
  change R.combinedWord q = x at hq
  have hlogical : ∀ a : Logical, q (Sum.inl a) = 0 := by
    intro a
    have horth := R.rowCode.orthogonal_of_mem_dual hxDual
      (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    rw [R.wordPairing_sigmaEquiv] at horth
    change weightedPairing R.sigma x (R.logicalRow a) = 0 at horth
    have hpair :
        weightedPairing R.sigma (R.combinedWord q) (R.logicalRow a) =
          q (Sum.inl a) * R.tau a := by
      unfold combinedWord
      change weightedPairingLeftLinearMap R.sigma (R.logicalRow a)
          (∑ r, q r • R.row r) = _
      rw [map_sum]
      simp only [map_smul, weightedPairingLeftLinearMap_apply, smul_eq_mul]
      rw [Fintype.sum_sum_type]
      simp only [row_inl, row_inr]
      have hstabilizer :
          (∑ s : Stabilizer,
            q (Sum.inr s) * weightedPairing R.sigma (R.stabilizerRow s)
              (R.logicalRow a)) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        have h := R.weighted_condition (Sum.inr s) (Sum.inl a)
        have hzero : weightedPairing R.sigma (R.stabilizerRow s) (R.logicalRow a) = 0 := by
          simpa [weightedTarget] using h
        rw [hzero, mul_zero]
      rw [hstabilizer, add_zero]
      have hlogicalSum := R.weightedPairing_logicalWord_logicalRow
        (fun b => q (Sum.inl b)) a
      change weightedPairingLeftLinearMap R.sigma (R.logicalRow a)
          (∑ b, q (Sum.inl b) • R.logicalRow b) =
        q (Sum.inl a) * R.tau a at hlogicalSum
      rw [map_sum] at hlogicalSum
      simpa only [map_smul, weightedPairingLeftLinearMap_apply, smul_eq_mul] using hlogicalSum
    rw [← hq, hpair] at horth
    exact (mul_eq_zero.mp horth).resolve_right (R.tau_ne_zero a)
  apply hxOutside
  rw [← hq]
  have hsplit :
      R.combinedWord q =
        (∑ a : Logical, q (Sum.inl a) • R.logicalRow a) +
          ∑ s : Stabilizer, q (Sum.inr s) • R.stabilizerRow s := by
    simp [combinedWord, row, Fintype.sum_sum_type]
  rw [hsplit]
  have hzero : (∑ a : Logical, q (Sum.inl a) • R.logicalRow a) = 0 := by
    simp [hlogical]
  rw [hzero, zero_add]
  exact Submodule.sum_mem R.stabilizerCode.carrier
    (fun s _ => R.stabilizerCode.carrier.smul_mem _
      (Submodule.subset_span ⟨s, rfl⟩))

/-- The pure-X logical-sector distance `min |G \ G₀|`, with infinity if empty. -/
noncomputable def cssXDistance
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) : WithTop Nat := by
  classical
  exact HypergraphProduct.finitePredicateMinimum
    (fun x : Why24Word Site => x ∈ R.rowCode.carrier ∧ x ∉ R.stabilizerCode.carrier)
    HammingWeight

/-- The pure-Z logical-sector distance `min |G₀^perp \ G^perp|`, with infinity if empty. -/
noncomputable def cssZDistance
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) : WithTop Nat := by
  classical
  exact HypergraphProduct.finitePredicateMinimum
    (fun x : Why24Word Site =>
      x ∈ R.stabilizerCode.dual.carrier ∧ x ∉ R.rowCode.dual.carrier)
    HammingWeight

/-- WHY24's distance comparison `d_X >= d_Z`. -/
theorem cssZDistance_le_cssXDistance
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.cssZDistance ≤ R.cssXDistance := by
  classical
  apply HypergraphProduct.le_finitePredicateMinimum
  intro x hx
  have hmapped :
      R.sigmaEquiv x ∈ R.stabilizerCode.dual.carrier ∧
        R.sigmaEquiv x ∉ R.rowCode.dual.carrier :=
    ⟨R.sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode hx.1,
      R.sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode hx.1 hx.2⟩
  calc
    R.cssZDistance ≤ (HammingWeight (R.sigmaEquiv x) : WithTop Nat) :=
      HypergraphProduct.finitePredicateMinimum_le_of hmapped
    _ = (HammingWeight x : WithTop Nat) := by rw [R.HammingWeight_sigmaEquiv]

/-- The source logical-Z representative associated with one logical row. -/
def dualLogicalRow
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) : Why24Word Site :=
  (R.tau a)⁻¹ • R.sigmaEquiv (R.logicalRow a)

/-- Logical rows and source dual logical rows have the exact Kronecker pairing. -/
theorem logicalRow_dualLogicalRow_pairing
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a b : Logical) :
    wordPairing (R.logicalRow a) (R.dualLogicalRow b) =
      if a = b then 1 else 0 := by
  classical
  rw [wordPairing_apply]
  unfold dualLogicalRow dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, sigmaEquiv_apply]
  have h := R.weighted_condition (Sum.inl b) (Sum.inl a)
  by_cases hab : a = b
  · subst b
    simp only [weightedTarget, ite_true] at h
    change weightedPairing R.sigma (R.logicalRow a) (R.logicalRow a) = R.tau a at h
    rw [show (∑ site : Site,
        R.logicalRow a site * ((R.tau a)⁻¹ *
          (R.sigma site * R.logicalRow a site))) =
        (R.tau a)⁻¹ * weightedPairing R.sigma (R.logicalRow a) (R.logicalRow a) by
          unfold weightedPairing
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro site _
          ring]
    rw [h, if_pos rfl]
    field_simp [R.tau_ne_zero a]
  · have hba : b ≠ a := fun h => hab h.symm
    simp only [weightedTarget, if_neg hba] at h
    change weightedPairing R.sigma (R.logicalRow b) (R.logicalRow a) = 0 at h
    rw [if_neg hab]
    rw [show (∑ site : Site,
        R.logicalRow a site * ((R.tau b)⁻¹ *
          (R.sigma site * R.logicalRow b site))) =
        (R.tau b)⁻¹ * weightedPairing R.sigma (R.logicalRow b) (R.logicalRow a) by
          unfold weightedPairing
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro site _
          ring]
    rw [h, mul_zero]

/-- The logical-row combination is additive. -/
theorem logicalWord_add
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    R.logicalWord (u + v) = R.logicalWord u + R.logicalWord v := by
  classical
  ext site
  simp only [logicalWord, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    add_smul, smul_eq_mul]
  rw [Finset.sum_add_distrib]

/-- The logical-row combination respects subtraction. -/
theorem logicalWord_sub
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    R.logicalWord (u - v) = R.logicalWord u - R.logicalWord v := by
  classical
  ext site
  simp only [logicalWord, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    sub_smul, smul_eq_mul]
  rw [Finset.sum_sub_distrib]

/-- Every logical combination lies in the logical row span. -/
theorem logicalWord_mem_logicalCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.logicalWord u ∈ R.logicalCode.carrier := by
  exact Submodule.sum_mem R.logicalCode.carrier
    (fun a _ => R.logicalCode.carrier.smul_mem _
      (Submodule.subset_span ⟨a, rfl⟩))

/-- A zero logical combination has only zero coefficients. -/
theorem logicalWord_eq_zero_iff
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.logicalWord u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext a
    exact (Fintype.linearIndependent_iff.mp R.logicalRows_linearIndependent) u h a
  · intro h
    rw [h]
    simp [logicalWord]

/-- The physical computational-basis label in the CSS coset for `u` and `h`. -/
def cosetLabel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.stabilizerCode.carrier) : Why24Word Site :=
  R.logicalWord u + (h : Why24Word Site)

/-- Within one logical coset, actual stabilizer words give distinct labels. -/
theorem cosetLabel_injective
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) : Function.Injective (R.cosetLabel u) := by
  intro h k heq
  apply Subtype.ext
  exact add_left_cancel heq

/-- Distinct logical labels select disjoint stabilizer cosets. -/
theorem cosetLabel_eq_implies_logical_eq
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024)
    (h k : R.stabilizerCode.carrier)
    (heq : R.cosetLabel u h = R.cosetLabel v k) : u = v := by
  have hdifference :
      R.logicalWord (u - v) = (k : Why24Word Site) - (h : Why24Word Site) := by
    rw [R.logicalWord_sub]
    unfold cosetLabel at heq
    ext site
    have hsite := congrFun heq site
    change R.logicalWord u site + h.1 site =
      R.logicalWord v site + k.1 site at hsite
    change R.logicalWord u site - R.logicalWord v site = k.1 site - h.1 site
    linear_combination hsite
  have hlogical : R.logicalWord (u - v) ∈ R.logicalCode.carrier :=
    R.logicalWord_mem_logicalCode (u - v)
  have hstabilizer : R.logicalWord (u - v) ∈ R.stabilizerCode.carrier := by
    rw [hdifference]
    exact R.stabilizerCode.carrier.sub_mem k.property h.property
  have hzero : R.logicalWord (u - v) = 0 := by
    have hintersection : R.logicalWord (u - v) ∈
        R.stabilizerCode.carrier ⊓ R.logicalCode.carrier :=
      ⟨hstabilizer, hlogical⟩
    rw [R.stabilizerCode_disjoint_logicalCode] at hintersection
    simpa using hintersection
  have huv : u - v = 0 := (R.logicalWord_eq_zero_iff (u - v)).mp hzero
  exact sub_eq_zero.mp huv

/-- The actual finite stabilizer carrier used in every uniform coset. -/
abbrev StabilizerCarrier
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :=
  R.stabilizerCode.carrier

noncomputable instance stabilizerCarrierFintype
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Fintype R.StabilizerCarrier :=
  Fintype.ofFinite _

/-- Source-faithful inverse-square-root normalization of the actual `G₀` carrier. -/
def cosetNormalization
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) : Complex :=
  (Real.sqrt (Nat.card R.StabilizerCarrier : Real) : Complex)⁻¹

/-- The actual normalized uniform stabilizer-coset ket. -/
def cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) : ComputationalBasisRegister F1024 Site :=
  R.cosetNormalization •
    ∑ h : R.StabilizerCarrier, registerBasisKet (R.cosetLabel u h)

/-- Every coset summand has the declared uniform amplitude. -/
theorem cosetKet_apply
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.StabilizerCarrier) :
    inner Complex (registerBasisKet (R.cosetLabel u h)) (R.cosetKet u) =
      R.cosetNormalization := by
  classical
  unfold cosetKet
  rw [inner_smul_right, inner_sum]
  rw [Finset.sum_eq_single h]
  · simp [registerBasisKet]
  · intro h' _ hne
    have hlabel : R.cosetLabel u h' ≠ R.cosetLabel u h :=
      fun heq => hne (R.cosetLabel_injective u heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel.symm]
  · simp

private theorem uniformCosetSum_inner
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    inner Complex
        (∑ h : R.StabilizerCarrier, registerBasisKet (R.cosetLabel u h))
        (∑ k : R.StabilizerCarrier, registerBasisKet (R.cosetLabel v k)) =
      if u = v then (Nat.card R.StabilizerCarrier : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases huv : u = v
  · subst v
    have hinner (h k : R.StabilizerCarrier) :
        inner Complex (registerBasisKet (R.cosetLabel u h))
          (registerBasisKet (R.cosetLabel u k)) = if h = k then 1 else 0 := by
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

private theorem cosetNormalization_conj_mul_card
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    starRingEnd Complex R.cosetNormalization * R.cosetNormalization *
        (Nat.card R.StabilizerCarrier : Complex) = 1 := by
  have hpos : (0 : Real) < Nat.card R.StabilizerCarrier := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card R.StabilizerCarrier)
  have hsqrt :
      (Real.sqrt (Nat.card R.StabilizerCarrier : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  unfold cosetNormalization
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  norm_cast
  exact (Real.sq_sqrt hpos.le).symm

/-- The normalized finite stabilizer-coset states are orthonormal. -/
theorem cosetKet_inner
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    inner Complex (R.cosetKet u) (R.cosetKet v) = if u = v then 1 else 0 := by
  unfold cosetKet
  rw [inner_smul_left, inner_smul_right, uniformCosetSum_inner]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    rw [← mul_assoc]
    exact R.cosetNormalization_conj_mul_card
  · simp [huv]

/-- The normalized coset family is an orthonormal computational family. -/
theorem cosetKet_orthonormal
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Orthonormal Complex R.cosetKet := by
  rw [orthonormal_iff_ite]
  intro u v
  exact R.cosetKet_inner u v

/-- Extend the normalized coset kets linearly from logical amplitudes. -/
noncomputable def encodingLinearMap
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    ComputationalBasisRegister F1024 Logical →ₗ[Complex]
      ComputationalBasisRegister F1024 Site where
  toFun psi := ∑ u : Logical → F1024, psi u • R.cosetKet u
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]

/-- The explicit normalized-coset encoder preserves inner products. -/
theorem encodingLinearMap_map_inner
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (psi chi : ComputationalBasisRegister F1024 Logical) :
    inner Complex (R.encodingLinearMap psi) (R.encodingLinearMap chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ u : Logical → F1024, psi u • R.cosetKet u)
      (∑ u : Logical → F1024, chi u • R.cosetKet u) = inner Complex psi chi
  rw [R.cosetKet_orthonormal.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]

/-- The normalized coset encoder as a linear isometry. -/
noncomputable def encodingIsometry
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    ComputationalBasisRegister F1024 Logical →ₗᵢ[Complex]
      ComputationalBasisRegister F1024 Site :=
  R.encodingLinearMap.isometryOfInner R.encodingLinearMap_map_inner

/-- The actual physical CSS carrier: the range of the normalized encoder. -/
noncomputable def encodedCarrier
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Submodule Complex (ComputationalBasisRegister F1024 Site) :=
  R.encodingIsometry.toLinearMap.range

/-- The normalized CSS carrier as a semantic quantum code. -/
noncomputable def quantumCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    QuantumCode (ComputationalBasisRegister F1024 Site) where
  carrier := R.encodedCarrier

/-- The complete normalized CSS encoding derived from the raw matrix. -/
noncomputable def encodedCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    EncodedCode (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Site) where
  code := R.quantumCode
  encoding := LinearIsometry.equivRange R.encodingIsometry

/-- The encoder sends a logical basis ket to the stated normalized coset ket. -/
theorem encodingLinearMap_apply_logical_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.encodingLinearMap (registerBasisKet u) = R.cosetKet u := by
  change (∑ v : Logical → F1024, registerBasisKet u v • R.cosetKet v) = R.cosetKet u
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]

/-- The semantic encoded code has the same basis action as the concrete encoder. -/
theorem encodedCode_apply_logical_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.encodedCode.encode (registerBasisKet u) = R.cosetKet u :=
  R.encodingLinearMap_apply_logical_basis u

/-- The semantic encoder is the concrete normalized-coset linear map. -/
theorem encodedCode_encode_eq_encodingLinearMap
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (psi : ComputationalBasisRegister F1024 Logical) :
    R.encodedCode.encode psi = R.encodingLinearMap psi :=
  rfl

/-- The CSS carrier encodes exactly one F1024 qudit per logical row. -/
theorem encodedCode_finrank_carrier
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    Module.finrank Complex R.encodedCode.code.carrier =
      1024 ^ Fintype.card Logical := by
  rw [← R.encodedCode.encoding.finrank_eq]
  rw [finrank_euclideanSpace]
  change Fintype.card (Logical → F1024) = _
  rw [Fintype.card_fun, f1024_card]

/-! ### Actual field-Pauli transports and derived logical operators -/

/-- Coordinatewise field translation on a finite F1024 register. -/
noncomputable def wordXOperator {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    Operator (ComputationalBasisRegister F1024 Index) where
  toFun psi := WithLp.toLp 2 fun label => psi (label + word)
  map_add' psi chi := by
    ext label
    simp
  map_smul' c psi := by
    ext label
    simp [smul_eq_mul]

@[simp]
theorem wordXOperator_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordXOperator word psi label = psi (label + word) :=
  rfl

private theorem add_word_add_word {Index : Type}
    (label word : Why24Word Index) :
    (label + word) + word = label := by
  funext site
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem wordXOperator_map_inner {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi chi : ComputationalBasisRegister F1024 Index) :
    inner Complex (wordXOperator word psi) (wordXOperator word chi) =
      inner Complex psi chi := by
  simp only [PiLp.inner_apply, wordXOperator_apply, RCLike.inner_apply']
  exact Fintype.sum_equiv (Equiv.addRight word)
    (fun label => star (psi (label + word)) * chi (label + word))
    (fun label => star (psi label) * chi label) (fun _ => rfl)

/-- The actual coordinatewise field-X unitary on a finite register. -/
noncomputable def wordXTransport {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) where
  toLinearEquiv :=
    { toFun := wordXOperator word
      invFun := wordXOperator word
      left_inv := by
        intro psi
        ext label
        simp only [wordXOperator_apply]
        rw [add_word_add_word]
      right_inv := by
        intro psi
        ext label
        simp only [wordXOperator_apply]
        rw [add_word_add_word]
      map_add' := (wordXOperator word).map_add
      map_smul' := (wordXOperator word).map_smul }
  map_inner := wordXOperator_map_inner word

@[simp]
theorem wordXTransport_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordXTransport word psi label = psi (label + word) :=
  rfl

/-- Field-X sends a computational ket to the translated ket. -/
theorem wordXTransport_apply_basis {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (word label : Why24Word Index) :
    wordXTransport word (registerBasisKet label) = registerBasisKet (label + word) := by
  classical
  ext target
  rw [wordXTransport_apply]
  by_cases htarget : target = label + word
  · subst target
    rw [add_word_add_word]
    simp [registerBasisKet, EuclideanSpace.basisFun_apply]
  · have hshift : target + word ≠ label := by
      intro h
      apply htarget
      calc
        target = (target + word) + word := (add_word_add_word target word).symm
        _ = label + word := by rw [h]
    simp [registerBasisKet, EuclideanSpace.basisFun_apply, htarget, hshift]

/-- The trace sign attached to a field element. -/
def tracePhase (x : F1024) : Complex :=
  additiveCharacter x

theorem tracePhase_add (x y : F1024) :
    tracePhase (x + y) = tracePhase x * tracePhase y :=
  additiveCharacter_add x y

theorem tracePhase_square (x : F1024) :
    tracePhase x * tracePhase x = 1 :=
  additiveCharacter_square x

theorem tracePhase_conj (x : F1024) :
    starRingEnd Complex (tracePhase x) = tracePhase x :=
  additiveCharacter_conj x

/-- The trace phase selected by a finite field-Z word. -/
def wordZAmplitude {Index : Type} [Fintype Index]
    (word label : Why24Word Index) : Complex :=
  tracePhase (wordPairing word label)

/-- The actual diagonal field-Z operator on a finite register. -/
noncomputable def wordZOperator {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    Operator (ComputationalBasisRegister F1024 Index) where
  toFun psi := WithLp.toLp 2 fun label => wordZAmplitude word label * psi label
  map_add' psi chi := by
    ext label
    change wordZAmplitude word label * (psi label + chi label) =
      wordZAmplitude word label * psi label + wordZAmplitude word label * chi label
    ring
  map_smul' c psi := by
    ext label
    change wordZAmplitude word label * (c * psi label) =
      c * (wordZAmplitude word label * psi label)
    ring

@[simp]
theorem wordZOperator_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordZOperator word psi label = wordZAmplitude word label * psi label :=
  rfl

private theorem wordZOperator_map_inner {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi chi : ComputationalBasisRegister F1024 Index) :
    inner Complex (wordZOperator word psi) (wordZOperator word chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [wordZOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (wordZAmplitude word label * chi label) *
        (starRingEnd Complex (wordZAmplitude word label) *
          starRingEnd Complex (psi label)) =
      (wordZAmplitude word label * starRingEnd Complex (wordZAmplitude word label)) *
        (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      unfold wordZAmplitude
      rw [tracePhase_conj, tracePhase_square, one_mul]

/-- The actual trace-phase field-Z unitary on a finite register. -/
noncomputable def wordZTransport {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index) :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) where
  toLinearEquiv :=
    { toFun := wordZOperator word
      invFun := wordZOperator word
      left_inv := by
        intro psi
        ext label
        simp only [wordZOperator_apply]
        rw [← mul_assoc]
        unfold wordZAmplitude
        rw [tracePhase_square, one_mul]
      right_inv := by
        intro psi
        ext label
        simp only [wordZOperator_apply]
        rw [← mul_assoc]
        unfold wordZAmplitude
        rw [tracePhase_square, one_mul]
      map_add' := (wordZOperator word).map_add
      map_smul' := (wordZOperator word).map_smul }
  map_inner := wordZOperator_map_inner word

@[simp]
theorem wordZTransport_apply {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Why24Word Index)
    (psi : ComputationalBasisRegister F1024 Index)
    (label : ComputationalBasisRegisterLabel F1024 Index) :
    wordZTransport word psi label = wordZAmplitude word label * psi label :=
  rfl

/-- Field-Z acts diagonally on a computational ket. -/
theorem wordZTransport_apply_basis {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (word label : Why24Word Index) :
    wordZTransport word (registerBasisKet label) =
      wordZAmplitude word label • registerBasisKet label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [wordZTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [wordZTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply, htarget]

/-- The one-coordinate logical register word. -/
def logicalBasisWord (a : Logical) (value : F1024) : Why24Word Logical :=
  Pi.single a value

/-- Combining one logical basis word selects the corresponding physical row. -/
theorem logicalWord_logicalBasisWord
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (value : F1024) :
    R.logicalWord (logicalBasisWord a value) = value • R.logicalRow a := by
  classical
  unfold logicalWord logicalBasisWord
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Pi.single_apply, hba]
  · simp

/-- The physical representative of logical `X^beta` on logical site `a`. -/
noncomputable def logicalXPhysical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (ComputationalBasisRegister F1024 Site) :=
  wordXTransport (beta • R.logicalRow a)

/-- The specified logical-register `X^beta` on logical site `a`. -/
noncomputable def logicalXLogical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Logical) :=
  wordXTransport (logicalBasisWord a beta)

/-- The physical representative of logical `Z^gamma` on logical site `a`. -/
noncomputable def logicalZPhysical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (ComputationalBasisRegister F1024 Site) :=
  wordZTransport (gamma • R.dualLogicalRow a)

/-- The specified logical-register `Z^gamma` on logical site `a`. -/
noncomputable def logicalZLogical
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) :
    UnitaryTransport (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Logical) :=
  wordZTransport (logicalBasisWord a gamma)

/-- The physical X representative translates the appropriate normalized coset. -/
theorem logicalXPhysical_cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) (u : Logical → F1024) :
    R.logicalXPhysical a beta (R.cosetKet u) =
      R.cosetKet (u + logicalBasisWord a beta) := by
  unfold logicalXPhysical cosetKet
  rw [map_smul, map_sum]
  simp_rw [wordXTransport_apply_basis]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  unfold cosetLabel
  rw [R.logicalWord_add, R.logicalWord_logicalBasisWord]
  abel

/-- The dual logical row is orthogonal to the complete stabilizer span. -/
theorem dualLogicalRow_mem_stabilizerCode_dual
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) :
    R.dualLogicalRow a ∈ R.stabilizerCode.dual.carrier := by
  unfold dualLogicalRow
  exact R.stabilizerCode.dual.carrier.smul_mem _
    (R.sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode
      (Submodule.subset_span ⟨Sum.inl a, rfl⟩))

/-- Pairing a logical word with one dual logical row extracts one logical coordinate. -/
theorem logicalWord_dualLogicalRow_pairing
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (a : Logical) :
    wordPairing (R.logicalWord u) (R.dualLogicalRow a) = u a := by
  classical
  unfold logicalWord
  simp [R.logicalRow_dualLogicalRow_pairing]

/-- The physical Z representative has the expected phase on every coset label. -/
theorem wordPairing_dualLogicalRow_cosetLabel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.StabilizerCarrier) (a : Logical) :
    wordPairing (R.dualLogicalRow a) (R.cosetLabel u h) = u a := by
  unfold cosetLabel
  rw [(wordPairing (R.dualLogicalRow a)).map_add]
  have hlogical : wordPairing (R.dualLogicalRow a) (R.logicalWord u) = u a := by
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
    exact R.logicalWord_dualLogicalRow_pairing u a
  have hstabilizer : wordPairing (R.dualLogicalRow a) (h : Why24Word Site) = 0 :=
    R.stabilizerCode.orthogonal_of_mem_dual
      (R.dualLogicalRow_mem_stabilizerCode_dual a) h.property
  rw [hlogical, hstabilizer, add_zero]

/-- The physical Z representative gives the expected logical phase on a normalized coset. -/
theorem logicalZPhysical_cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) (u : Logical → F1024) :
    R.logicalZPhysical a gamma (R.cosetKet u) =
      tracePhase (gamma * u a) • R.cosetKet u := by
  unfold logicalZPhysical cosetKet
  rw [map_smul, map_sum]
  simp_rw [wordZTransport_apply_basis]
  have hamplitude (h : R.StabilizerCarrier) :
      wordZAmplitude (gamma • R.dualLogicalRow a) (R.cosetLabel u h) =
        tracePhase (gamma * u a) := by
    unfold wordZAmplitude
    rw [wordPairing.map_smul]
    change tracePhase (gamma * wordPairing (R.dualLogicalRow a) (R.cosetLabel u h)) = _
    rw [R.wordPairing_dualLogicalRow_cosetLabel]
  simp_rw [hamplitude]
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm]

/-- Physical and logical X agree on every encoded computational basis state. -/
theorem logicalXPhysical_intertwines_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) (u : Logical → F1024) :
    R.logicalXPhysical a beta
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalXLogical a beta (registerBasisKet u)) := by
  rw [R.encodedCode_apply_logical_basis, R.logicalXPhysical_cosetKet]
  unfold logicalXLogical
  rw [wordXTransport_apply_basis, R.encodedCode_apply_logical_basis]

/-- Physical and logical Z agree on every encoded computational basis state. -/
theorem logicalZPhysical_intertwines_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) (u : Logical → F1024) :
    R.logicalZPhysical a gamma
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalZLogical a gamma (registerBasisKet u)) := by
  rw [R.encodedCode_apply_logical_basis, R.logicalZPhysical_cosetKet]
  unfold logicalZLogical
  rw [wordZTransport_apply_basis, R.encodedCode_encode_eq_encodingLinearMap,
    map_smul, R.encodingLinearMap_apply_logical_basis]
  congr 1
  unfold wordZAmplitude logicalBasisWord tracePhase
  simp [wordPairing_apply, dotProduct, Pi.single_apply]

/-- Full encoder-commuting equation for each physical logical-X representative. -/
theorem logicalXPhysical_implements
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) :
    R.encodedCode.ImplementsLogicalGate
      (R.logicalXPhysical a beta) (R.logicalXLogical a beta) := by
  intro psi
  let encodeAmbient :
      ComputationalBasisRegister F1024 Logical →ₗ[Complex]
        ComputationalBasisRegister F1024 Site :=
    R.encodedCode.code.carrier.subtype.comp R.encodedCode.encoding.toLinearMap
  have hlinear :
      (R.logicalXPhysical a beta).toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp (R.logicalXLogical a beta).toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Logical → F1024) Complex).toBasis.ext
    intro u
    change R.logicalXPhysical a beta
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalXLogical a beta (registerBasisKet u))
    exact R.logicalXPhysical_intertwines_basis a beta u
  exact LinearMap.congr_fun hlinear psi

/-- Full encoder-commuting equation for each physical logical-Z representative. -/
theorem logicalZPhysical_implements
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) :
    R.encodedCode.ImplementsLogicalGate
      (R.logicalZPhysical a gamma) (R.logicalZLogical a gamma) := by
  intro psi
  let encodeAmbient :
      ComputationalBasisRegister F1024 Logical →ₗ[Complex]
        ComputationalBasisRegister F1024 Site :=
    R.encodedCode.code.carrier.subtype.comp R.encodedCode.encoding.toLinearMap
  have hlinear :
      (R.logicalZPhysical a gamma).toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp (R.logicalZLogical a gamma).toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Logical → F1024) Complex).toBasis.ext
    intro u
    change R.logicalZPhysical a gamma
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalZLogical a gamma (registerBasisKet u))
    exact R.logicalZPhysical_intertwines_basis a gamma u
  exact LinearMap.congr_fun hlinear psi

/-! ### Symbolic seventh-power identity -/

/-- The seventh-power exponent is the diagonal asymmetric seventh pairing. -/
theorem seventhExponent_eq_seventhPairing {Index : Type} [Fintype Index]
    (label : Why24Word Index) :
    seventhExponent label = seventhPairing label label label := by
  unfold seventhExponent seventhPairing
  apply Finset.sum_congr rfl
  intro index _
  ring

private theorem fintype_sum_pow_two {Index : Type} [Fintype Index]
    (value : Index → F1024) :
    (∑ index : Index, value index) ^ 2 =
      ∑ index : Index, value index ^ 2 := by
  simpa using
    (sum_pow_char (R := F1024) (p := 2)
      (Finset.univ : Finset Index) value)

private theorem fintype_sum_pow_four {Index : Type} [Fintype Index]
    (value : Index → F1024) :
    (∑ index : Index, value index) ^ 4 =
      ∑ index : Index, value index ^ 4 := by
  calc
    (∑ index : Index, value index) ^ 4 =
        ((∑ index : Index, value index) ^ 2) ^ 2 := by ring
    _ = (∑ index : Index, value index ^ 2) ^ 2 := by
      rw [fintype_sum_pow_two]
    _ = ∑ index : Index, (value index ^ 2) ^ 2 := by
      rw [fintype_sum_pow_two]
    _ = ∑ index : Index, value index ^ 4 := by
      apply Finset.sum_congr rfl
      intro index _
      ring

private theorem fintype_sum_mul_sum_mul_sum {Index : Type} [Fintype Index]
    (first second third : Index → F1024) :
    (∑ index : Index, first index) * (∑ index : Index, second index) *
        (∑ index : Index, third index) =
      ∑ i : Index, ∑ j : Index, ∑ k : Index,
        first i * second j * third k := by
  calc
    (∑ index : Index, first index) * (∑ index : Index, second index) *
        (∑ index : Index, third index) =
        (∑ i : Index, ∑ j : Index, first i * second j) *
          (∑ index : Index, third index) := by
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i : Index, (∑ j : Index, first i * second j) *
          (∑ index : Index, third index) := by rw [Finset.sum_mul]
    _ = ∑ i : Index, ∑ j : Index, ∑ k : Index,
          first i * second j * third k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]

private theorem fintype_sum_rotate_four
    {First Second Third Fourth : Type}
    [Fintype First] [Fintype Second] [Fintype Third] [Fintype Fourth]
    (value : First → Second → Third → Fourth → F1024) :
    (∑ fourth : Fourth, ∑ first : First, ∑ second : Second, ∑ third : Third,
        value first second third fourth) =
      ∑ first : First, ∑ second : Second, ∑ third : Third, ∑ fourth : Fourth,
        value first second third fourth := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second _
  rw [Finset.sum_comm]

private theorem seventhPairing_sum_smul
    {RowIndex SiteIndex : Type} [Fintype RowIndex] [Fintype SiteIndex]
    (coefficient : RowIndex → F1024) (rowFamily : RowIndex → Why24Word SiteIndex) :
    seventhPairing
        (∑ row : RowIndex, coefficient row • rowFamily row)
        (∑ row : RowIndex, coefficient row • rowFamily row)
        (∑ row : RowIndex, coefficient row • rowFamily row) =
      ∑ first : RowIndex, ∑ second : RowIndex, ∑ third : RowIndex,
        coefficient first ^ 4 * coefficient second ^ 2 * coefficient third *
          seventhPairing (rowFamily first) (rowFamily second) (rowFamily third) := by
  unfold seventhPairing
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [fintype_sum_pow_four, fintype_sum_pow_two, mul_pow]
  conv_lhs =>
    enter [2, site]
    rw [fintype_sum_mul_sum_mul_sum]
  rw [fintype_sum_rotate_four]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro site _
  ring

/-- The raw seventh-degree matrix equation determines every combined row word. -/
theorem seventhPairing_combinedWord
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (coefficient : Logical ⊕ Stabilizer → F1024) :
    seventhPairing (R.combinedWord coefficient) (R.combinedWord coefficient)
        (R.combinedWord coefficient) =
      ∑ logical : Logical, coefficient (Sum.inl logical) ^ 7 := by
  unfold combinedWord
  rw [seventhPairing_sum_smul]
  change
    (∑ first : Logical ⊕ Stabilizer,
      ∑ second : Logical ⊕ Stabilizer,
      ∑ third : Logical ⊕ Stabilizer,
        coefficient first ^ 4 * coefficient second ^ 2 * coefficient third *
          seventhPairing (Sum.elim R.logicalRow R.stabilizerRow first)
            (Sum.elim R.logicalRow R.stabilizerRow second)
            (Sum.elim R.logicalRow R.stabilizerRow third)) = _
  simp_rw [R.seventh_condition]
  simp [seventhTarget, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro logical _
  rw [Finset.sum_eq_single logical]
  · rw [Finset.sum_eq_single logical]
    · simp
      ring
    · intro third _ hthird
      have hne : logical ≠ third := Ne.symm hthird
      simp [hne]
    · simp
  · intro second _ hsecond
    apply Finset.sum_eq_zero
    intro third _
    have hne : logical ≠ second := Ne.symm hsecond
    simp [hne]
  · simp

/-- Every physical label in a logical stabilizer coset has the logical seventh exponent. -/
theorem seventhExponent_cosetLabel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.StabilizerCarrier) :
    seventhExponent (R.cosetLabel u h) = ∑ logical : Logical, u logical ^ 7 := by
  classical
  obtain ⟨stabilizerCoefficient, hstabilizer⟩ :=
    (Submodule.mem_span_range_iff_exists_fun F1024).mp h.property
  let coefficient : Logical ⊕ Stabilizer → F1024 :=
    Sum.elim u stabilizerCoefficient
  have hcombined : R.combinedWord coefficient = R.cosetLabel u h := by
    unfold combinedWord cosetLabel logicalWord coefficient
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, row_inl, row_inr]
    rw [hstabilizer]
  rw [← hcombined, seventhExponent_eq_seventhPairing,
    R.seventhPairing_combinedWord]
  rfl

/-! ### Literal singleton-site `U_1^(7)` product -/

@[simp]
theorem tracePhase_zero : tracePhase 0 = 1 := by
  simp [tracePhase, additiveCharacter, fieldTrace,
    PauliSymplectic.binaryPhaseScalar]

private theorem tracePhase_finset_sum {Index : Type} [DecidableEq Index]
    (indices : Finset Index) (value : Index → F1024) :
    tracePhase (∑ index ∈ indices, value index) =
      ∏ index ∈ indices, tracePhase (value index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, tracePhase_add, Finset.prod_insert hindex, ih]

theorem tracePhase_fintype_sum {Index : Type} [Fintype Index]
    (value : Index → F1024) :
    tracePhase (∑ index : Index, value index) =
      ∏ index : Index, tracePhase (value index) := by
  classical
  simpa using tracePhase_finset_sum (Finset.univ : Finset Index) value

/-- The phase contributed by #885's `U_1^(7)` at one displayed register site. -/
def uOneSevenAtAmplitude {Index : Type} (index : Index)
    (label : Why24Word Index) : Complex :=
  tracePhase (label index ^ 7)

/-- Each local coefficient is exactly the corresponding matrix coefficient of #885's gate. -/
theorem uOneSevenAtAmplitude_eq_why24UOneSeven {Index : Type}
    (index : Index) (label : Why24Word Index) :
    uOneSevenAtAmplitude index label =
      why24UOneSeven (why24QuditComputationalBasis (label index)) (label index) := by
  simp [uOneSevenAtAmplitude, tracePhase, additiveCharacter, fieldTrace,
    why24UOneSeven, why24QuditComputationalBasis]

/-- The diagonal operator which applies #885's gate at one literal register site. -/
noncomputable def uOneSevenAtOperator {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index) :
    Operator (ComputationalBasisRegister F1024 Index) where
  toFun psi := WithLp.toLp 2 fun label => uOneSevenAtAmplitude index label * psi label
  map_add' psi chi := by
    ext label
    change uOneSevenAtAmplitude index label * (psi label + chi label) =
      uOneSevenAtAmplitude index label * psi label +
        uOneSevenAtAmplitude index label * chi label
    ring
  map_smul' scalar psi := by
    ext label
    change uOneSevenAtAmplitude index label * (scalar * psi label) =
      scalar * (uOneSevenAtAmplitude index label * psi label)
    ring

@[simp]
theorem uOneSevenAtOperator_apply {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index)
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    uOneSevenAtOperator index psi label = uOneSevenAtAmplitude index label * psi label :=
  rfl

private theorem uOneSevenAtOperator_map_inner {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index)
    (psi chi : ComputationalBasisRegister F1024 Index) :
    inner Complex (uOneSevenAtOperator index psi) (uOneSevenAtOperator index chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [uOneSevenAtOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (uOneSevenAtAmplitude index label * chi label) *
        (starRingEnd Complex (uOneSevenAtAmplitude index label) *
          starRingEnd Complex (psi label)) =
      (uOneSevenAtAmplitude index label *
          starRingEnd Complex (uOneSevenAtAmplitude index label)) *
        (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      unfold uOneSevenAtAmplitude
      rw [tracePhase_conj, tracePhase_square, one_mul]

/-- #885's `U_1^(7)` lifted to one literal site of a finite register. -/
noncomputable def uOneSevenAtTransport {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index) :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) where
  toLinearEquiv :=
    { toFun := uOneSevenAtOperator index
      invFun := uOneSevenAtOperator index
      left_inv := by
        intro psi
        ext label
        simp only [uOneSevenAtOperator_apply]
        rw [← mul_assoc]
        unfold uOneSevenAtAmplitude
        rw [tracePhase_square, one_mul]
      right_inv := by
        intro psi
        ext label
        simp only [uOneSevenAtOperator_apply]
        rw [← mul_assoc]
        unfold uOneSevenAtAmplitude
        rw [tracePhase_square, one_mul]
      map_add' := (uOneSevenAtOperator index).map_add
      map_smul' := (uOneSevenAtOperator index).map_smul }
  map_inner := uOneSevenAtOperator_map_inner index

@[simp]
theorem uOneSevenAtTransport_apply {Index : Type}
    [Fintype Index] [DecidableEq Index] (index : Index)
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    uOneSevenAtTransport index psi label = uOneSevenAtAmplitude index label * psi label :=
  rfl

/-- Canonically enumerate a finite set of WHY24 physical sites. -/
noncomputable def why24SiteEquivFin (Index : Type) [Fintype Index] :
    Fin (Fintype.card Index) ≃ Index :=
  (Fintype.equivFin Index).symm

/-- The complete tensor product of literal local #885 `U_1^(7)` factors. -/
noncomputable def registerUOneSeven {Index : Type}
    [Fintype Index] [DecidableEq Index] :
    UnitaryTransport (ComputationalBasisRegister F1024 Index)
      (ComputationalBasisRegister F1024 Index) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card Index) =>
    uOneSevenAtTransport (why24SiteEquivFin Index j)

private theorem composeUOneSevenAtTransports_apply {Index : Type}
    [Fintype Index] [DecidableEq Index] (indices : List Index)
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    UnitaryTransport.composeList (indices.map uOneSevenAtTransport) psi label =
      (indices.map fun index => uOneSevenAtAmplitude index label).prod * psi label := by
  induction indices generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons index indices ih =>
      change UnitaryTransport.composeList (indices.map uOneSevenAtTransport)
          (uOneSevenAtTransport index psi) label = _
      rw [ih]
      simp only [uOneSevenAtTransport_apply, List.map_cons, List.prod_cons]
      ring

/-- The register product has the product of all literal local #885 phases. -/
theorem registerUOneSeven_apply {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    registerUOneSeven psi label =
      (∏ index : Index, uOneSevenAtAmplitude index label) * psi label := by
  rw [registerUOneSeven, UnitaryTransport.composeFamily]
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card Index) =>
        uOneSevenAtTransport (why24SiteEquivFin Index j)) =
        (List.ofFn (why24SiteEquivFin Index)).map uOneSevenAtTransport := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, composeUOneSevenAtTransports_apply]
  rw [List.map_ofFn, Fin.prod_ofFn]
  congr 1
  exact Fintype.prod_equiv (why24SiteEquivFin Index) _ _ (fun _ => rfl)

/-- The physical tensor product acts by the trace phase of the full seventh exponent. -/
theorem registerUOneSeven_apply_phase {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (psi : ComputationalBasisRegister F1024 Index) (label : Why24Word Index) :
    registerUOneSeven psi label = tracePhase (seventhExponent label) * psi label := by
  rw [registerUOneSeven_apply]
  unfold uOneSevenAtAmplitude seventhExponent
  rw [tracePhase_fintype_sum]

/-- The physical product has its seventh-exponent phase on every computational ket. -/
theorem registerUOneSeven_apply_basis {Index : Type}
    [Fintype Index] [DecidableEq Index] (label : Why24Word Index) :
    registerUOneSeven (registerBasisKet label) =
      tracePhase (seventhExponent label) • registerBasisKet label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [registerUOneSeven_apply_phase, registerBasisKet,
      EuclideanSpace.basisFun_apply]
  · simp [registerUOneSeven_apply_phase, registerBasisKet,
      EuclideanSpace.basisFun_apply, htarget]

/-- The literal singleton support of one WHY24 physical site. -/
def why24CoordinateSupport {Index : Type} [DecidableEq Index]
    (index : Index) : Finset Index :=
  {index}

@[simp]
theorem why24CoordinateSupport_card {Index : Type} [DecidableEq Index]
    (index : Index) : (why24CoordinateSupport index).card = 1 := by
  simp [why24CoordinateSupport]

theorem why24CoordinateSupport_disjoint {Index : Type} [DecidableEq Index]
    {first second : Index} (hne : first ≠ second) :
    Disjoint (why24CoordinateSupport first) (why24CoordinateSupport second) := by
  simpa [why24CoordinateSupport] using (Finset.disjoint_singleton.mpr hne)

/-- The only local factor is #885's `U_1^(7)` on its displayed singleton support. -/
inductive UOneSevenLocalGate {Index : Type}
    [Fintype Index] [DecidableEq Index] : Finset Index → Type
  | at (index : Index) : UOneSevenLocalGate (why24CoordinateSupport index)

/-- The literal support-indexed physical model for local #885 `U_1^(7)` factors. -/
noncomputable def registerUOneSevenGateModel {Index : Type}
    [Fintype Index] [DecidableEq Index] :
    FinitePhysicalGateModel Index (ComputationalBasisRegister F1024 Index) where
  LocalGate := UOneSevenLocalGate
  realize gate := match gate with
    | .at index => uOneSevenAtTransport index

/-- The register product factors over disjoint singleton physical sites. -/
noncomputable def registerUOneSevenSitewiseFactorization {Index : Type}
    [Fintype Index] [DecidableEq Index] :
    SitewiseTransversalityData (registerUOneSevenGateModel (Index := Index))
      (registerUOneSeven (Index := Index)) where
  factorCount := Fintype.card Index
  support j := why24CoordinateSupport (why24SiteEquivFin Index j)
  factor j := .at (why24SiteEquivFin Index j)
  pairwise_disjoint := by
    intro i j hij
    exact why24CoordinateSupport_disjoint ((why24SiteEquivFin Index).injective.ne hij)
  realizes := rfl
  support_card_le_one := by
    intro j
    simp

/-! ### Encoded physical-to-logical `U_1^(7)` implementation -/

/-- The literal physical product of #885 `U_1^(7)` gates for this row matrix. -/
noncomputable def physicalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    UnitaryTransport (ComputationalBasisRegister F1024 Site)
      (ComputationalBasisRegister F1024 Site) :=
  registerUOneSeven

/-- The specified product of #885 `U_1^(7)` gates on the logical register. -/
noncomputable def logicalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    UnitaryTransport (ComputationalBasisRegister F1024 Logical)
      (ComputationalBasisRegister F1024 Logical) :=
  registerUOneSeven

/-- The singleton-support physical-gate model attached to this row matrix. -/
noncomputable def physicalGateModel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    FinitePhysicalGateModel Site (ComputationalBasisRegister F1024 Site) :=
  registerUOneSevenGateModel

/-- Literal singleton-site factorization of the matrix's physical `U_1^(7)` product. -/
noncomputable def physicalUOneSevenSitewiseFactorization
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    SitewiseTransversalityData R.physicalGateModel R.physicalUOneSeven :=
  registerUOneSevenSitewiseFactorization

/-- The physical product gives the logical seventh phase on each normalized coset ket. -/
theorem physicalUOneSeven_cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.physicalUOneSeven (R.cosetKet u) =
      tracePhase (∑ logical : Logical, u logical ^ 7) • R.cosetKet u := by
  unfold physicalUOneSeven cosetKet
  rw [map_smul, map_sum]
  simp_rw [registerUOneSeven_apply_basis, R.seventhExponent_cosetLabel]
  change R.cosetNormalization •
      (∑ h : R.StabilizerCarrier,
        tracePhase (∑ logical : Logical, u logical ^ 7) •
          registerBasisKet (R.cosetLabel u h)) =
    tracePhase (∑ logical : Logical, u logical ^ 7) •
      (R.cosetNormalization •
        ∑ h : R.StabilizerCarrier, registerBasisKet (R.cosetLabel u h))
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm]

/-- Physical and logical seventh-power gates agree on every encoded basis state. -/
theorem physicalUOneSeven_intertwines_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) :
    R.physicalUOneSeven (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalUOneSeven (registerBasisKet u)) := by
  rw [R.encodedCode_apply_logical_basis, R.physicalUOneSeven_cosetKet]
  unfold logicalUOneSeven
  rw [registerUOneSeven_apply_basis,
    R.encodedCode_encode_eq_encodingLinearMap, map_smul,
    R.encodingLinearMap_apply_logical_basis]
  rfl

/-- WHY24's complete encoder-commuting physical-to-logical `U_1^(7)` equation. -/
theorem physicalUOneSeven_implements_logicalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.encodedCode.ImplementsLogicalGate R.physicalUOneSeven R.logicalUOneSeven := by
  intro psi
  let encodeAmbient :
      ComputationalBasisRegister F1024 Logical →ₗ[Complex]
        ComputationalBasisRegister F1024 Site :=
    R.encodedCode.code.carrier.subtype.comp R.encodedCode.encoding.toLinearMap
  have hlinear :
      R.physicalUOneSeven.toLinearEquiv.toLinearMap.comp encodeAmbient =
        encodeAmbient.comp R.logicalUOneSeven.toLinearEquiv.toLinearMap := by
    apply (EuclideanSpace.basisFun (Logical → F1024) Complex).toBasis.ext
    intro u
    change R.physicalUOneSeven
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalUOneSeven (registerBasisKet u))
    exact R.physicalUOneSeven_intertwines_basis u
  exact LinearMap.congr_fun hlinear psi

/-- The full WHY24 transversal package: exact implementation plus literal singleton factors. -/
noncomputable def sitewiseTransversalUOneSeven
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    SitewiseTransversalLogicalGate R.encodedCode R.logicalUOneSeven R.physicalGateModel where
  physicalGate := R.physicalUOneSeven
  implements := R.physicalUOneSeven_implements_logicalUOneSeven
  transversality := R.physicalUOneSevenSitewiseFactorization

end WeightedTriorthogonalMatrix

end QEC.Distillation.Why24WeightedTriorthogonalCSS
