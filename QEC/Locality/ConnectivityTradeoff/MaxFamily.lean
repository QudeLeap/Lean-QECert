import QEC.Locality.SeparatorProfile.Core
import QEC.Coding.QLDPC.Core
/-!
# Baspin--Krishna measured separator exponents for a QLDPC family

This module implements the source convention selected by the BK route audit.
The family is explicitly a Nat-indexed family of binary stabilizer
QLDPC codes.  At every valid index `n`, the physical coordinate type has
cardinality `n`, the certified distance lies in `2 <= d(n) <= n`, and the
connectivity graph is the graph of one fixed generator presentation.

The balance convention is exactly the `2/3` convention implemented by
`twoThirdsSeparationProfile`.  For an integral scale `r` in `[d(n), n]`,

`c_n(r) = log_r(s_n(r))`

uses the measured profile `s_n(r)` of that actual graph.  The value `c_max(n)`
is the attained finite maximum of these observed exponents.  The profile power
bound is proved below from this maximum; it is not stored in the family data.

The dangling source token `r_0(n)` is intentionally absent: the pinned source
does not define it and neither displayed conclusion uses it.  This module also
contains no asymptotic tradeoff conclusion and does not prove the terminal BK
tradeoff.
-/

noncomputable section

namespace QEC.Locality

universe u v

/-- A finite graph is nontrivial for the BK logarithm domain when it has an actual edge. -/
def ConnectivityGraph.HasEdge {ι : Type u} [Fintype ι]
    (G : ConnectivityGraph ι) : Prop :=
  ∃ p q : ι, G.adjacent p q

/--
An actual graph edge forces the measured `2/3` separation profile to be
positive at every scale at least two.
-/
theorem twoThirdsSeparationProfile_pos_of_hasEdge
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (hEdge : G.HasEdge) {scale : Nat}
    (hscale : 2 ≤ scale) :
    0 < twoThirdsSeparationProfile G scale := by
  rcases hEdge with ⟨p, q, hpq⟩
  have hpne : p ≠ q := by
    intro hpqEq
    subst q
    exact G.loopless p hpq
  let vertices : Finset ι := {p, q}
  have hverticesCard : vertices.card = 2 := by
    simp [vertices, hpne]
  have hminimumPos :
      0 < minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by
    apply Nat.pos_of_ne_zero
    intro hminimumZero
    rcases exists_minimumTwoThirdsBalancedVertexSeparator G vertices with
      ⟨separator, _hseparatorSubset, hbalanced, hseparatorCard⟩
    have hseparatorEmpty : separator = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hseparatorCard, hminimumZero]
    subst separator
    rcases hbalanced with
      ⟨left, right, _hemptySubset, hpartition, _hdisjoint,
        hleftBalanced, hrightBalanced, hnoEdge⟩
    have hpartition' : left ∪ right = vertices := by
      simpa using hpartition
    have hpSide : p ∈ left ∨ p ∈ right := by
      have : p ∈ left ∪ right := by
        rw [hpartition']
        simp [vertices]
      exact Finset.mem_union.mp this
    have hqSide : q ∈ left ∨ q ∈ right := by
      have : q ∈ left ∪ right := by
        rw [hpartition']
        simp [vertices]
      exact Finset.mem_union.mp this
    rcases hpSide with hpLeft | hpRight
    · rcases hqSide with hqLeft | hqRight
      · have hverticesSubset : vertices ⊆ left := by
          intro x hx
          simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hpLeft
          · exact hqLeft
        have htwoLe : 2 ≤ left.card := by
          simpa [hverticesCard] using Finset.card_le_card hverticesSubset
        omega
      · exact (hnoEdge hpLeft hqRight) hpq
    · rcases hqSide with hqLeft | hqRight
      · exact (hnoEdge hqLeft hpRight) (G.symmetric hpq)
      · have hverticesSubset : vertices ⊆ right := by
          intro x hx
          simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hpRight
          · exact hqRight
        have htwoLe : 2 ≤ right.card := by
          simpa [hverticesCard] using Finset.card_le_card hverticesSubset
        omega
  have hminimumLeProfile :
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤
        twoThirdsSeparationProfile G scale := by
    apply minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    · simp
    · omega
  omega

/-- The measured profile at scale `r` never exceeds `r`. -/
theorem twoThirdsSeparationProfile_le_scale
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) :
    twoThirdsSeparationProfile G scale ≤ scale := by
  classical
  apply Finset.max'_le
  intro size hsize
  rcases Finset.mem_image.mp hsize with ⟨vertices, hvertices, hvalue⟩
  rw [← hvalue]
  have hcard := (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices
  exact (minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card G vertices).trans hcard.2

/-- With at least two vertices, deleting all but one is a proper balanced separator. -/
theorem minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (hcard : 2 ≤ vertices.card) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices < vertices.card := by
  have hnonempty : vertices.Nonempty := Finset.card_pos.mp (by omega)
  rcases hnonempty with ⟨p, hp⟩
  apply lt_of_le_of_lt
    (minimumTwoThirdsBalancedVertexSeparatorSize_le_card
      G vertices (vertices.erase p) (Finset.erase_subset p vertices) ?_)
    (Finset.card_erase_lt_of_mem hp)
  refine ⟨{p}, ∅, ?_⟩
  refine ⟨Finset.erase_subset p vertices, ?_, by simp, ?_, by simp, ?_⟩
  · simpa using (Finset.sdiff_erase_self hp).symm
  · simp only [Finset.card_singleton]
    omega
  · simp [NoEdgeBetween]

/-- At every scale at least two, the measured profile is strictly below its scale. -/
theorem twoThirdsSeparationProfile_lt_scale
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) {scale : Nat} (hscale : 2 ≤ scale) :
    twoThirdsSeparationProfile G scale < scale := by
  classical
  unfold twoThirdsSeparationProfile
  rw [Finset.max'_lt_iff]
  intro size hsize
  rcases Finset.mem_image.mp hsize with ⟨vertices, hvertices, hvalue⟩
  rw [← hvalue]
  have hcard := (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices
  by_cases hfull : vertices.card = scale
  · rw [← hfull]
    exact minimumTwoThirdsBalancedVertexSeparatorSize_lt_vertex_card
      G vertices (by omega)
  · have hminimumLe :=
      minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card G vertices
    omega

/--
The exact family data selected from the literal QLDPC scope shared by the
source definition and theorem.  The LDPC property is explicit and applies to
the valid-index subfamily; it is not inferred from a generic quantum-code
family.
-/
structure BKQLDPCFamily
    (ι : Nat → Type u) (κ : Nat → Type v)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)] where
  validIndex : Nat → Prop
  parameterData : ∀ n, Coding.StabilizerCode.StabilizerParameterData
    (ι := ι n) (κ := κ n)
  blockLength_eq_index : ∀ n, validIndex n → (parameterData n).blockLength = n
  distance_two_le : ∀ n, validIndex n → 2 ≤ (parameterData n).distance
  distance_le_index : ∀ n, validIndex n → (parameterData n).distance ≤ n
  fixedGeneratorGraph_hasEdge : ∀ n, validIndex n →
    (parameterData n).presentation.fixedGeneratorInteractionGraph.HasEdge
  isQLDPC : QLDPC.IsLDPCStabilizerFamily
    (fun i : {n : Nat // validIndex n} => (parameterData i.1).presentation.code)

namespace BKQLDPCFamily

variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]

/-- The family index is the subtype of valid natural block-length indices. -/
abbrev Index (family : BKQLDPCFamily ι κ) := {n : Nat // family.validIndex n}

/-- The actual source-valid binary stabilizer presentation at any family index. -/
abbrev presentation (family : BKQLDPCFamily ι κ) (n : Nat) :=
  (family.parameterData n).presentation

/-- The physical block length computed from the actual finite presentation. -/
abbrev blockLength (family : BKQLDPCFamily ι κ) (n : Nat) : Nat :=
  (family.parameterData n).blockLength

/-- The encoded-qubit count proved from the stabilizer normalizer quotient. -/
abbrev encodedQubits (family : BKQLDPCFamily ι κ) (n : Nat) : Nat :=
  (family.parameterData n).encodedQubits

/-- The semantic stabilizer distance certified by the family parameter data. -/
abbrev distance (family : BKQLDPCFamily ι κ) (n : Nat) : Nat :=
  (family.parameterData n).distance

/-- The actual fixed-generator connectivity graph at a valid family index. -/
abbrev fixedGeneratorGraph (family : BKQLDPCFamily ι κ) (i : family.Index) :
    ConnectivityGraph (ι i.1) :=
  (family.parameterData i.1).presentation.fixedGeneratorInteractionGraph

/-- The observed `2/3` balanced separation profile of the actual fixed-generator graph. -/
noncomputable def measuredSeparationProfile
    (family : BKQLDPCFamily ι κ) (i : family.Index) (r : Nat) : Nat :=
  twoThirdsSeparationProfile (family.fixedGeneratorGraph i) r

/-- The integral scales in the source interval `[d(n), n]`. -/
def validScales (family : BKQLDPCFamily ι κ) (i : family.Index) : Finset Nat :=
  Finset.Icc (family.distance i.1) i.1

/-- The selected family index is exactly the physical block length. -/
theorem index_card (family : BKQLDPCFamily ι κ) (i : family.Index) :
    Fintype.card (ι i.1) = i.1 :=
  family.blockLength_eq_index i.1 i.2

/-- The finite source scale interval is nonempty at every valid index. -/
theorem validScales_nonempty (family : BKQLDPCFamily ι κ) (i : family.Index) :
    (family.validScales i).Nonempty := by
  exact ⟨family.distance i.1,
    Finset.mem_Icc.mpr ⟨le_rfl, family.distance_le_index i.1 i.2⟩⟩

/-- Membership unfolds to the exact natural range `d(n) <= r <= n`. -/
theorem mem_validScales_iff (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) :
    r ∈ family.validScales i ↔ family.distance i.1 ≤ r ∧ r ≤ i.1 := by
  simp [validScales]

/-- Every source-valid scale has logarithm base strictly larger than one. -/
theorem one_lt_validScale (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    1 < r := by
  have hdistance : 2 ≤ family.distance i.1 := by
    simpa [distance] using family.distance_two_le i.1 i.2
  have hrange := (family.mem_validScales_iff i r).1 hr
  omega

/-- The measured graph profile is positive throughout the source scale interval. -/
theorem measuredSeparationProfile_pos (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    0 < family.measuredSeparationProfile i r := by
  apply twoThirdsSeparationProfile_pos_of_hasEdge
  · exact family.fixedGeneratorGraph_hasEdge i.1 i.2
  · have hdistance : 2 ≤ family.distance i.1 := by
      simpa [distance] using family.distance_two_le i.1 i.2
    have hrange := (family.mem_validScales_iff i r).1 hr
    omega

/-- The observed profile is bounded by its natural scale. -/
theorem measuredSeparationProfile_le_scale (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) :
    family.measuredSeparationProfile i r ≤ r :=
  twoThirdsSeparationProfile_le_scale (family.fixedGeneratorGraph i) r

/-- The observed profile is strictly below every source-valid scale. -/
theorem measuredSeparationProfile_lt_scale (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.measuredSeparationProfile i r < r := by
  apply twoThirdsSeparationProfile_lt_scale
  have hdistance : 2 ≤ family.distance i.1 := by
    simpa [distance] using family.distance_two_le i.1 i.2
  have hrange := (family.mem_validScales_iff i r).1 hr
  omega

/-- The source quantity `c_n(r) = log_r(s_n(r))`, defined from the observed profile. -/
noncomputable def cN (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) : ℝ :=
  Real.logb (r : ℝ) (family.measuredSeparationProfile i r : ℝ)

/-- The finite set of observed exponents over `[d(n), n]`. -/
noncomputable def observedExponents
    (family : BKQLDPCFamily ι κ) (i : family.Index) : Finset ℝ :=
  (family.validScales i).image (family.cN i)

/-- The observed exponent set is nonempty. -/
theorem observedExponents_nonempty (family : BKQLDPCFamily ι κ) (i : family.Index) :
    (family.observedExponents i).Nonempty := by
  rcases family.validScales_nonempty i with ⟨r, hr⟩
  exact ⟨family.cN i r, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩

/-- The exact finite maximum `c_max(n)` of the measured exponents. -/
noncomputable def cMax (family : BKQLDPCFamily ι κ) (i : family.Index) : ℝ :=
  (family.observedExponents i).max' (family.observedExponents_nonempty i)

/-- Eventual quantification over valid block-length indices only. -/
def EventuallyOnValidIndices
    (family : BKQLDPCFamily ι κ) (predicate : family.Index → Prop) : Prop :=
  ∃ start : Nat, ∀ (n : Nat), start ≤ n →
    ∀ hvalid : family.validIndex n, predicate ⟨n, hvalid⟩

/-- Valid block-length indices are cofinal, so eventual statements are not finite-family vacuities. -/
def HasCofinalValidIndices (family : BKQLDPCFamily ι κ) : Prop :=
  ∀ start : Nat, ∃ n : Nat, start ≤ n ∧ family.validIndex n

/--
The source log-free branch uses one family-uniform constant below one.  This is
a hypothesis on the measured `cMax`; it contains no tradeoff conclusion.
-/
def UniformCMaxBelowOne (family : BKQLDPCFamily ι κ) : Prop :=
  ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
    family.EventuallyOnValidIndices (fun i => family.cMax i ≤ ceiling)

/-- The finite maximum is attained at an explicit scale in `[d(n), n]`. -/
theorem exists_validScale_cN_eq_cMax
    (family : BKQLDPCFamily ι κ) (i : family.Index) :
    ∃ r ∈ family.validScales i, family.cN i r = family.cMax i := by
  have hmem : family.cMax i ∈ family.observedExponents i := by
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨r, hr, hvalue⟩
  exact ⟨r, hr, hvalue⟩

/-- Every observed exponent lies in the source-valid closed range `[0, 1]`. -/
theorem cN_nonneg (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    0 ≤ family.cN i r := by
  apply Real.logb_nonneg
  · exact_mod_cast family.one_lt_validScale i hr
  · exact_mod_cast Nat.succ_le_iff.mpr (family.measuredSeparationProfile_pos i hr)

theorem cN_le_one (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.cN i r ≤ 1 := by
  calc
    family.cN i r ≤ Real.logb (r : ℝ) (r : ℝ) := by
      apply Real.logb_le_logb_of_le
      · exact_mod_cast family.one_lt_validScale i hr
      · exact_mod_cast family.measuredSeparationProfile_pos i hr
      · exact_mod_cast family.measuredSeparationProfile_le_scale i r
    _ = 1 := Real.logb_self_eq_one (by
      exact_mod_cast family.one_lt_validScale i hr)

theorem cN_lt_one (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.cN i r < 1 := by
  calc
    family.cN i r < Real.logb (r : ℝ) (r : ℝ) := by
      apply Real.logb_lt_logb
      · exact_mod_cast family.one_lt_validScale i hr
      · exact_mod_cast family.measuredSeparationProfile_pos i hr
      · exact_mod_cast family.measuredSeparationProfile_lt_scale i hr
    _ = 1 := Real.logb_self_eq_one (by
      exact_mod_cast family.one_lt_validScale i hr)

/-- The finite maximum inherits the proved exponent domain. -/
theorem cMax_nonneg (family : BKQLDPCFamily ι κ) (i : family.Index) :
    0 ≤ family.cMax i := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_nonneg i hr

theorem cMax_le_one (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i ≤ 1 := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_le_one i hr

theorem cMax_lt_one (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i < 1 := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_lt_one i hr

/-- Every observed scale exponent is bounded by the attained finite maximum. -/
theorem cN_le_cMax (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.cN i r ≤ family.cMax i := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- On the proved logarithm domain, exponentiating `c_n(r)` recovers the observed profile. -/
theorem rpow_cN_eq_measuredSeparationProfile
    (family : BKQLDPCFamily ι κ) (i : family.Index)
    {r : Nat} (hr : r ∈ family.validScales i) :
    Real.rpow (r : ℝ) (family.cN i r) =
      (family.measuredSeparationProfile i r : ℝ) := by
  have hrPos : (0 : ℝ) < r := by
    exact_mod_cast Nat.zero_lt_of_lt (family.one_lt_validScale i hr)
  have hrNeOne : (r : ℝ) ≠ 1 := by
    exact ne_of_gt (by exact_mod_cast family.one_lt_validScale i hr)
  have hprofilePos : (0 : ℝ) < family.measuredSeparationProfile i r := by
    exact_mod_cast family.measuredSeparationProfile_pos i hr
  exact Real.rpow_logb hrPos hrNeOne hprofilePos

/--
The measured profile upper bound is derived from the observed finite maximum.
It is not an assumption field and is stated only on the source interval.
-/
theorem measuredSeparationProfile_le_rpow_cMax
    (family : BKQLDPCFamily ι κ) (i : family.Index)
    {r : Nat} (hr : r ∈ family.validScales i) :
    (family.measuredSeparationProfile i r : ℝ) ≤
      Real.rpow (r : ℝ) (family.cMax i) := by
  rw [← family.rpow_cN_eq_measuredSeparationProfile i hr]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast Nat.le_of_lt (family.one_lt_validScale i hr)
  · exact family.cN_le_cMax i hr

end BKQLDPCFamily
end QEC.Locality
