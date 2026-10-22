import QEC.Coding.QuantumTanner.Core
import QEC.Coding.CSS.WeightDescent
import QEC.Coding.ChainComplex.Duality
import QEC.Coding.QuantumTanner.TensorDistance

/-!
# Local checks and weight descent for Quantum Tanner codes

Finite link counting and the local-to-global descent step in [LZ22, proofs of
Claim claim:Se and Theorem thm:123]. The local reducing checks needed by
Theorem thm:main remain explicit premises: this module does not construct them
from expansion and puncture-resistant robustness, or prove asymptotic goodness.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical

universe v

namespace LeftRightCayleySquareComplex

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- The actual restriction to the injectively indexed link of a vertex. -/
def localRestriction (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) : Word (ZMod 2) Square →ₗ[ZMod 2] Word (ZMod 2) (A × B) where
  toFun x ab := x (X.link vertex ab)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem localExtension_apply_link (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (c : Word (ZMod 2) (A × B)) (ab : A × B) :
    X.localExtension vertex c (X.link vertex ab) = c ab := by
  simp [localExtension, Pi.single_apply, (X.link_injective vertex).eq_iff]

@[simp]
theorem localRestriction_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (c : Word (ZMod 2) (A × B)) :
    X.localRestriction vertex (X.localExtension vertex c) = c := by
  ext ab
  exact X.localExtension_apply_link vertex c ab

theorem localExtension_eq_zero_of_not_incident
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (c : Word (ZMod 2) (A × B)) {q : Square}
    (hq : q ∉ Finset.univ.image (X.link vertex)) :
    X.localExtension vertex c q = 0 := by
  by_contra hne
  exact hq (X.localExtension_support_subset vertex c (by simpa [hammingSupport] using hne))

theorem support_inter_link (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (x : Word (ZMod 2) Square) :
    hammingSupport x ∩ Finset.univ.image (X.link vertex) =
      (hammingSupport (X.localRestriction vertex x)).image (X.link vertex) := by
  ext q
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hq, ab, rfl⟩
    exact ⟨ab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩,
      rfl⟩
  · rintro ⟨ab, hab, rfl⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hab).2⟩,
      ab, rfl⟩

/-- Partition global weight into the link weight and the unchanged exterior. -/
theorem hammingWeight_partition_link
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) :
    HammingWeight x = HammingWeight (X.localRestriction vertex x) +
      (hammingSupport x \ Finset.univ.image (X.link vertex)).card := by
  have h := Finset.card_inter_add_card_sdiff
    (hammingSupport x) (Finset.univ.image (X.link vertex))
  rw [X.support_inter_link vertex x,
    Finset.card_image_of_injective _ (X.link_injective vertex)] at h
  exact h.symm

/-- Adding an extended local word changes no exterior coordinate. -/
theorem support_sdiff_link_add_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    hammingSupport (x + X.localExtension vertex c) \ Finset.univ.image (X.link vertex) =
      hammingSupport x \ Finset.univ.image (X.link vertex) := by
  ext q
  by_cases hq : q ∈ Finset.univ.image (X.link vertex)
  · simp [hq]
  · simp [hammingSupport, hq, X.localExtension_eq_zero_of_not_incident vertex c hq]

/-- Exact local/global weight-change identity, without expansion assumptions. -/
theorem hammingWeight_add_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    HammingWeight (x + X.localExtension vertex c) +
      HammingWeight (X.localRestriction vertex x) =
    HammingWeight x + HammingWeight (X.localRestriction vertex x + c) := by
  have hx := X.hammingWeight_partition_link vertex x
  have hadd := X.hammingWeight_partition_link vertex (x + X.localExtension vertex c)
  rw [map_add, X.localRestriction_localExtension,
    X.support_sdiff_link_add_localExtension] at hadd
  omega

/-- A locally weight-reducing tensor check really reduces the global word. -/
theorem hammingWeight_add_localExtension_lt_iff
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    HammingWeight (x + X.localExtension vertex c) < HammingWeight x ↔
      HammingWeight (X.localRestriction vertex x + c) <
        HammingWeight (X.localRestriction vertex x) := by
  have h := X.hammingWeight_add_localExtension vertex x c
  omega

/-- The local weight counts exactly the nonzero incident global coordinates. -/
theorem hammingWeight_localRestriction_eq_sum
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) :
    HammingWeight (X.localRestriction vertex x) =
      ∑ q : Square, if x q ≠ 0 ∧ X.Incident vertex q then 1 else 0 := by
  have hset : hammingSupport x ∩ Finset.univ.image (X.link vertex) =
      Finset.univ.filter (fun q => x q ≠ 0 ∧ X.Incident vertex q) := by
    ext q
    simp [hammingSupport, Incident]
  have hcard := congrArg Finset.card (X.support_inter_link vertex x)
  rw [Finset.card_image_of_injective _ (X.link_injective vertex)] at hcard
  change (hammingSupport (X.localRestriction vertex x)).card = _
  rw [← hcard, hset, Finset.card_filter]

/-- Each nonzero square is counted at exactly two vertices on either side.
This is the finite counting step used in [LZ22, proof of Claim claim:Se]. -/
theorem sum_hammingWeight_localRestriction
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) :
    (∑ g : G, HammingWeight (X.localRestriction (g, side) x)) =
      2 * HammingWeight x := by
  simp_rw [X.hammingWeight_localRestriction_eq_sum]
  rw [Finset.sum_comm]
  calc
    (∑ q : Square, ∑ g : G, if x q ≠ 0 ∧ X.Incident (g, side) q then 1 else 0) =
        ∑ q : Square, if x q ≠ 0 then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hq : x q = 0
      · simp [hq]
      · rw [if_pos hq]
        calc
          (∑ g : G, if x q ≠ 0 ∧ X.Incident (g, side) q then 1 else 0) =
              ∑ g : G, if X.Incident (g, side) q then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro g _hg
            by_cases hi : X.Incident (g, side) q
            · rw [if_pos ⟨hq, hi⟩, if_pos hi]
            · rw [if_neg (fun h => hi h.2), if_neg hi]
          _ = (Finset.univ.filter fun g => X.Incident (g, side) q).card :=
            (Finset.card_filter _ _).symm
          _ = 2 := X.incidentVerticesOnSide_card q side
    _ = 2 * HammingWeight x := by
      rw [HammingWeight, hammingSupport, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      split <;> simp_all

/-- Counting all incidences on either side gives the actual block-length
identity. It follows from the square-complex interface, not a family premise. -/
theorem card_group_mul_local_degree_eq_twice_card_square
    (X : LeftRightCayleySquareComplex G A B Square) :
    Fintype.card G * (Fintype.card A * Fintype.card B) = 2 * Fintype.card Square := by
  simpa [HammingWeight, hammingSupport, localRestriction] using
    X.sum_hammingWeight_localRestriction false (fun _ => (1 : ZMod 2))

/-- Vertices whose actual local view is nonzero. -/
def activeVerticesOnSide (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) : Finset G :=
  Finset.univ.filter fun g => X.localRestriction (g, side) x ≠ 0

/-- A lower bound on each nonzero local view bounds the active vertex count.
The local-code lower bound is explicit; no expansion estimate is assumed here. -/
theorem activeVerticesOnSide_card_mul_le
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (localDistance : Nat)
    (hlocal : ∀ g, X.localRestriction (g, side) x ≠ 0 →
      localDistance ≤ HammingWeight (X.localRestriction (g, side) x)) :
    localDistance * (X.activeVerticesOnSide side x).card ≤ 2 * HammingWeight x := by
  calc
    localDistance * (X.activeVerticesOnSide side x).card =
        ∑ g : G, if X.localRestriction (g, side) x ≠ 0 then localDistance else 0 := by
      rw [activeVerticesOnSide, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _hg
      split <;> simp_all
    _ ≤ ∑ g : G, HammingWeight (X.localRestriction (g, side) x) := by
      apply Finset.sum_le_sum
      intro g _hg
      split
      · next hne => exact hlocal g hne
      · exact Nat.zero_le _
    _ = 2 * HammingWeight x := X.sum_hammingWeight_localRestriction side x

/-- Restriction is adjoint to zero extension for the actual coordinate pairing. -/
theorem wordPairing_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    wordPairing x (X.localExtension vertex c) =
      wordPairing (X.localRestriction vertex x) c := by
  simp only [wordPairing_apply, localExtension, LinearMap.coe_mk, AddHom.coe_mk,
    dotProduct_sum, dotProduct_smul]
  simp [dotProduct, localRestriction, Pi.single_apply, mul_comm]

end LeftRightCayleySquareComplex

/-- Every selected generator lies in the range of its actual generator map. -/
theorem generator_mem_range_linearMapOfGenerators
    {F : Type} {ι κ : Type v} [Field F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) (k : κ) :
    generator k ∈ LinearMap.range (linearMapOfGenerators generator) := by
  refine ⟨Pi.single k 1, ?_⟩
  simp [linearMapOfGenerators, Pi.single_apply]

namespace RawData

variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

/-- Extending any word in the tensor of the dual local codes gives a genuine
X check, not just a selected basis check. -/
theorem localExtension_mem_range_xGeneratorMap
    (D : RawData G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier) :
    D.complex.localExtension (g, true) c ∈ LinearMap.range D.xGeneratorMap := by
  have hbasis : ∑ i, D.xBasis.repr ⟨c, hc⟩ i • (D.xBasis i).val = c := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (D.xBasis.sum_repr ⟨c, hc⟩)
  rw [← hbasis, map_sum]
  apply Submodule.sum_mem
  intro i _hi
  rw [map_smul]
  exact Submodule.smul_mem _ _ (generator_mem_range_linearMapOfGenerators
    D.xGenerator (g, i))

/-- The primal tensor code analog gives a genuine Z check. -/
theorem localExtension_mem_range_zGeneratorMap
    (D : RawData G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA D.codeB).carrier) :
    D.complex.localExtension (g, false) c ∈ LinearMap.range D.zGeneratorMap := by
  have hbasis : ∑ i, D.zBasis.repr ⟨c, hc⟩ i • (D.zBasis i).val = c := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (D.zBasis.sum_repr ⟨c, hc⟩)
  rw [← hbasis, map_sum]
  apply Submodule.sum_mem
  intro i _hi
  rw [map_smul]
  exact Submodule.smul_mem _ _ (generator_mem_range_linearMapOfGenerators
    D.zGenerator (g, i))

end RawData

namespace Data

variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

/-- A dual-local-code tensor word extends into the actual X-check subcode. -/
theorem localExtension_mem_firstCoboundaryCheckCode
    (D : Data G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier) :
    D.complex.localExtension (g, true) c ∈ D.chainComplex.firstCoboundaryCheckCode.carrier := by
  change D.complex.localExtension (g, true) c ∈
    LinearMap.range (wordLinearMapTranspose (wordLinearMapTranspose D.toRawData.xGeneratorMap))
  rw [wordLinearMapTranspose_transpose]
  exact D.toRawData.localExtension_mem_range_xGeneratorMap g c hc

/-- A primal tensor word extends into the actual Z-check subcode. -/
theorem localExtension_mem_middleBoundaryCode
    (D : Data G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA D.codeB).carrier) :
    D.complex.localExtension (g, false) c ∈ D.chainComplex.middleBoundaryCode.carrier := by
  exact D.toRawData.localExtension_mem_range_zGeneratorMap g c hc

/-- Orthogonality to the global Z checks implies orthogonality to the primal
local tensor code on the false side, using the actual check subcode. -/
theorem localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, false) x ∈ (tensorCode D.codeA D.codeB).dual.carrier := by
  refine (LinearCode.mem_dual _ _).2 ?_
  intro c hc
  rw [← D.complex.wordPairing_localExtension (g, false) x c]
  exact D.chainComplex.middleBoundaryCode.orthogonal_of_mem_dual hx
    (D.localExtension_mem_middleBoundaryCode g c hc)

/-- The symmetric ambient sector satisfies the corresponding true-side
constraints, using the tensor of the dual local codes. -/
theorem localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, true) x ∈
      (tensorCode D.codeA.dual D.codeB.dual).dual.carrier := by
  refine (LinearCode.mem_dual _ _).2 ?_
  intro c hc
  rw [← D.complex.wordPairing_localExtension (g, true) x c]
  exact D.chainComplex.firstCoboundaryCheckCode.orthogonal_of_mem_dual hx
    (D.localExtension_mem_firstCoboundaryCheckCode g c hc)

/-- The false-side local view belongs to the sum of the dual row/column codes,
not to the primal tensor intersection. -/
theorem localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, false) x ∈
      (dualTensorCode D.codeA.dual D.codeB.dual).carrier := by
  rw [← tensorCode_dual_carrier_eq]
  exact D.localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual x hx g

/-- The true-side local view belongs to the primal row/column sum. -/
theorem localRestriction_mem_dualTensorCode_of_mem_firstCoboundaryCheckCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, true) x ∈ (dualTensorCode D.codeA D.codeB).carrier := by
  rw [← tensorCode_dual_dual_carrier_eq]
  exact D.localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual x hx g

/-- The active false-side vertex count follows from the two dual-code distance
bounds and actual global orthogonality, without an extra local-distance premise. -/
theorem activeVertices_false_card_mul_le_of_mem_middleBoundaryCode_dual
    (D : Data G A B Square XBasis ZBasis) (dA dB : Nat)
    (hA : ∀ a : Word (ZMod 2) A, a ∈ D.codeA.dual.carrier → a ≠ 0 →
      dA ≤ HammingWeight a)
    (hB : ∀ b : Word (ZMod 2) B, b ∈ D.codeB.dual.carrier → b ≠ 0 →
      dB ≤ HammingWeight b)
    (x : Word (ZMod 2) Square) (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) :
    min dA dB * (D.complex.activeVerticesOnSide false x).card ≤ 2 * HammingWeight x := by
  apply D.complex.activeVerticesOnSide_card_mul_le false x (min dA dB)
  intro g hne
  exact hammingWeight_ge_min_of_mem_dualTensorCode D.codeA.dual D.codeB.dual dA dB hA hB _
    (D.localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual x hx g) hne

/-- The symmetric active true-side count uses the two primal-code distances. -/
theorem activeVertices_true_card_mul_le_of_mem_firstCoboundaryCheckCode_dual
    (D : Data G A B Square XBasis ZBasis) (dA dB : Nat)
    (hA : ∀ a : Word (ZMod 2) A, a ∈ D.codeA.carrier → a ≠ 0 → dA ≤ HammingWeight a)
    (hB : ∀ b : Word (ZMod 2) B, b ∈ D.codeB.carrier → b ≠ 0 → dB ≤ HammingWeight b)
    (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier) :
    min dA dB * (D.complex.activeVerticesOnSide true x).card ≤ 2 * HammingWeight x := by
  apply D.complex.activeVerticesOnSide_card_mul_le true x (min dA dB)
  intro g hne
  exact hammingWeight_ge_min_of_mem_dualTensorCode D.codeA D.codeB dA dB hA hB _
    (D.localRestriction_mem_dualTensorCode_of_mem_firstCoboundaryCheckCode_dual x hx g) hne

/-- The two local reduction statements imply a lower bound for the actual
Quantum Tanner CSS minimum. Their geometric existence is a separate obligation. -/
theorem minimumDistance_ge_of_local_weight_descent
    (D : Data G A B Square XBasis ZBasis) (threshold : Nat)
    (hreduceX : ∀ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.middleBoundaryCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B),
        c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier ∧
        HammingWeight (D.complex.localRestriction (g, true) x + c) <
          HammingWeight (D.complex.localRestriction (g, true) x))
    (hreduceZ : ∀ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B),
        c ∈ (tensorCode D.codeA D.codeB).carrier ∧
        HammingWeight (D.complex.localRestriction (g, false) x + c) <
          HammingWeight (D.complex.localRestriction (g, false) x))
    {distance : Nat}
    (hmin : AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
      D.chainComplex.middleBoundaryCode distance) : threshold ≤ distance := by
  apply algebraicCSSMinimumDistance_ge_of_add_weight_descent
    D.chainComplex.firstCoboundaryCheckCode D.chainComplex.middleBoundaryCode
    D.chainComplex.firstCoboundaryCheckCode_le_middleBoundaryCode_dual
    D.chainComplex.middleBoundaryCode_le_firstCoboundaryCheckCode_dual threshold
    ?_ ?_ hmin
  · intro x hx hne hsmall
    obtain ⟨g, c, hc, hdecrease⟩ := hreduceX x hx hne hsmall
    exact ⟨D.complex.localExtension (g, true) c,
      D.localExtension_mem_firstCoboundaryCheckCode g c hc,
      (D.complex.hammingWeight_add_localExtension_lt_iff (g, true) x c).2 hdecrease⟩
  · intro x hx hne hsmall
    obtain ⟨g, c, hc, hdecrease⟩ := hreduceZ x hx hne hsmall
    exact ⟨D.complex.localExtension (g, false) c,
      D.localExtension_mem_middleBoundaryCode g c hc,
      (D.complex.hammingWeight_add_localExtension_lt_iff (g, false) x c).2 hdecrease⟩

end Data

end QEC.Coding.QuantumTanner
