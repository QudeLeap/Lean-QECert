import QEC.Coding.ExpanderCodes.TannerPairExistence
import QEC.Coding.QLDPC.AsymptoticallyGoodFamily

/-!
# Families of PK22 Tanner lifted-product presentations

This module packages a cofinal family of labelled finite groups into the
semantic quantum-code-family interface.  It proves uniform locality and the
fixed local-ratio rate estimate without storing either conclusion as data.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u

variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]

/-- Physical coordinates of the Tanner lifted product at one family index. -/
abbrev FamilyQubitIndex (a : A) :=
  LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') (G a)

/-- Scalar-decorated semantic checks at one family index. -/
abbrev FamilyCheckIndex (a : A) :=
  QEC.Coding.FiniteFieldCSSPresentation.CheckIndex F
    (LiftedProduct.C0Index (Fin 2 × R) W (G a))
    (LiftedProduct.C2Index W (Fin 2 × R') (G a))

noncomputable local instance : DecidableEq F := Classical.decEq F
noncomputable local instance (a : A) : DecidableEq
    (FamilyQubitIndex (W := W) (R := R) (R' := R') (G := G) a) :=
  Classical.decEq _

/-- Canonical PK22 graph radius obtained by taking a `1 / |W|` fraction of
the voltage group.  Since `W` is fixed along the family, this is still linear
in every semantic block length. -/
def canonicalRadius (a : A) : Nat :=
  Fintype.card (G a) / Fintype.card W

/-- A concrete positive relative-distance constant compatible with
`canonicalRadius`.  It is intentionally conservative: two integer divisions
are absorbed by the factor `2 |W|^2`. -/
noncomputable def canonicalRelativeDistance : ℝ :=
  1 /
    (2 * (Fintype.card W : ℝ) ^ 2 *
      ((Fintype.card W : ℝ) ^ 2 +
        4 * Fintype.card R * Fintype.card R'))

/-- Two successive positive-denominator divisions lose at most the displayed
factor.  This is the integer rounding lemma behind the canonical relative
distance. -/
theorem le_two_mul_sq_mul_div_div_add_one
    (n w : Nat) (hw : 0 < w) :
    n ≤ 2 * w * w * (n / w / (2 * w) + 1) := by
  have hmod : n % w < w := Nat.mod_lt n hw
  have hn : n ≤ w * (n / w + 1) := by
    calc
      n = w * (n / w) + n % w := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod n w).symm
      _ ≤ w * (n / w) + w :=
        Nat.add_le_add_left (Nat.le_of_lt hmod) _
      _ = w * (n / w + 1) := by ring
  have htw : 0 < 2 * w := Nat.mul_pos (by omega) hw
  have hqmod : (n / w) % (2 * w) < 2 * w := Nat.mod_lt (n / w) htw
  have hq : n / w + 1 ≤ (2 * w) * (n / w / (2 * w) + 1) := by
    calc
      n / w + 1 =
          (2 * w) * (n / w / (2 * w)) + (n / w) % (2 * w) + 1 := by
        exact congrArg (fun z => z + 1)
          (Nat.div_add_mod (n / w) (2 * w)).symm
      _ ≤ (2 * w) * (n / w / (2 * w)) + (2 * w) := by omega
      _ = (2 * w) * (n / w / (2 * w) + 1) := by ring
  calc
    n ≤ w * (n / w + 1) := hn
    _ ≤ w * ((2 * w) * (n / w / (2 * w) + 1)) :=
      Nat.mul_le_mul_left w hq
    _ = 2 * w * w * (n / w / (2 * w) + 1) := by ring

omit [DecidableEq W] [(a : A) → Group (G a)]
    [(a : A) → DecidableEq (G a)] in
/-- The canonical radius makes the uniform-density contribution at most one
in the division-free expander-mixing estimate. -/
theorem canonicalRadius_density (a : A) :
    (Fintype.card W : ℝ) * canonicalRadius (W := W) (G := G) a ≤
      (1 : ℝ) * Fintype.card (Fin 2 × G a) := by
  have hNat : Fintype.card W * canonicalRadius (W := W) (G := G) a ≤
      Fintype.card (G a) := by
    simpa [canonicalRadius, Nat.mul_comm] using
      Nat.div_mul_le_self (Fintype.card (G a)) (Fintype.card W)
  norm_num [Fintype.card_prod, Fintype.card_fin]
  exact_mod_cast hNat.trans (Nat.le_mul_of_pos_left _ (by omega))

omit [DecidableEq W] [(a : A) → Group (G a)]
    [(a : A) → DecidableEq (G a)] in
/-- The canonical radius has density at most one when normalized by the size
of a single bipartite part. -/
theorem canonicalRadius_partiteDensity (a : A) :
    (Fintype.card W : ℝ) * canonicalRadius (W := W) (G := G) a ≤
      (1 : ℝ) * Fintype.card (G a) := by
  have hNat : Fintype.card W * canonicalRadius (W := W) (G := G) a ≤
      Fintype.card (G a) := by
    simpa [canonicalRadius, Nat.mul_comm] using
      Nat.div_mul_le_self (Fintype.card (G a)) (Fintype.card W)
  norm_num
  exact_mod_cast hNat

omit [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- The canonical relative-distance constant is strictly positive whenever
the local direction type is nonempty. -/
theorem canonicalRelativeDistance_pos (hW : 0 < Fintype.card W) :
    0 < canonicalRelativeDistance (W := W) (R := R) (R' := R') := by
  unfold canonicalRelativeDistance
  positivity

/-- The canonical radius lower bound is a fixed positive fraction of the
actual semantic block length, uniformly over the voltage group. -/
theorem canonicalRelativeDistance_mul_blockLength_le
    (a : A) (label : W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W) :
    canonicalRelativeDistance (W := W) (R := R) (R' := R') *
        ((semanticPresentation label h h').blockLength : ℝ) ≤
      (canonicalRadius (W := W) (G := G) a /
          (2 * Fintype.card W) + 1 : Nat) := by
  let w : Nat := Fintype.card W
  let g : Nat := Fintype.card (G a)
  let c : Nat := w ^ 2 + 4 * Fintype.card R * Fintype.card R'
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hRound : g ≤ 2 * w * w * (g / w / (2 * w) + 1) :=
    le_two_mul_sq_mul_div_div_add_one g w (by simpa [w] using hW)
  have hRoundReal : (g : ℝ) ≤
      ((2 * w * w * (g / w / (2 * w) + 1) : Nat) : ℝ) := by
    exact_mod_cast hRound
  have hwReal : (0 : ℝ) < w := by exact_mod_cast hW
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hc
  have hScaled :
      (g : ℝ) / (2 * (w : ℝ) ^ 2) ≤
        ((g / w / (2 * w) + 1 : Nat) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    push_cast at hRoundReal
    calc
      (g : ℝ) ≤
          2 * (w : ℝ) * w * ((g / w / (2 * w) : Nat) + 1) :=
        hRoundReal
      _ = ((g / w / (2 * w) + 1 : Nat) : ℝ) *
          (2 * (w : ℝ) ^ 2) := by push_cast; ring
  calc
    canonicalRelativeDistance (W := W) (R := R) (R' := R') *
          ((semanticPresentation label h h').blockLength : ℝ) =
        (g : ℝ) / (2 * (w : ℝ) ^ 2) := by
      change canonicalRelativeDistance (W := W) (R := R) (R' := R') *
        (Fintype.card
          (LiftedProduct.QubitIndex
            (Fin 2 × R) W W (Fin 2 × R') (G a)) : ℝ) = _
      unfold canonicalRelativeDistance
      rw [card_qubitIndex]
      dsimp [w, g, c]
      push_cast
      field_simp
    _ ≤ ((g / w / (2 * w) + 1 : Nat) : ℝ) := hScaled
    _ = (canonicalRadius (W := W) (G := G) a /
          (2 * Fintype.card W) + 1 : Nat) := by
      simp [canonicalRadius, w, g]

/-- The actual semantic Tanner presentations over a cofinal labelled group
family.  Cofinality is proved from the group orders and the nonempty local
direction set; no rate, distance, or locality conclusion is stored here. -/
noncomputable def semanticFamily
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a)) :
    QEC.QLDPC.QuantumCodeFamily A
      (fun a => FamilyQubitIndex
        (W := W) (R := R) (R' := R') (G := G) a)
      (fun a => FamilyCheckIndex
        (F := F) (W := W) (R := R) (R' := R') (G := G) a) where
  presentation a := semanticPresentation (label a) h h'
  cofinal_blockLength N := by
    obtain ⟨a, ha⟩ := hGroupCofinal N
    refine ⟨a, ha.trans ?_⟩
    change Fintype.card (G a) ≤ Fintype.card
      (FamilyQubitIndex (W := W) (R := R) (R' := R') (G := G) a)
    rw [card_qubitIndex]
    apply Nat.le_mul_of_pos_right
    exact Nat.add_pos_left (Nat.mul_pos hW hW) _

/-- The Tanner family has one locality bound independent of its group index. -/
theorem semanticFamily_hasUniformLDPC
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a)) :
    QEC.QLDPC.HasUniformLDPC
      (semanticFamily label h h' hW hGroupCofinal) := by
  refine ⟨2 * (Fintype.card W + Fintype.card R + Fintype.card R') *
    Fintype.card F, ?_⟩
  intro a
  exact semanticPresentation_boundedLocality (label a) h h'

/-- A single local-dimension ratio gives the requested rate bound at every
member of the cofinal semantic Tanner family. -/
theorem semanticFamily_hasEventualRateAtLeast_of_local_ratio
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (rate : ℝ)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRateAtLeast
      (semanticFamily label h h' hW hGroupCofinal) rate := by
  refine ⟨0, ?_⟩
  intro a _ha
  exact rate_le_semanticPresentation_encodedQudits_of_local_ratio
    (label a) h h' rate hRatio

/-- Uniform deterministic PK22 hypotheses at every group index give a
family-level eventual relative-distance bound for the actual semantic
presentations.  The threshold is zero because the supplied graph-radius
comparison is already uniform. -/
theorem semanticFamily_hasEventualRelativeDistanceAtLeast_of_doubleCoverExpansion
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : A → Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : ∀ a, SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph (label a)) (radius a) lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R'))
    (relativeDistance : ℝ)
    (hRelative : ∀ a,
      relativeDistance * ((semanticPresentation (label a) h h').blockLength : ℝ) ≤
        (radius a / (2 * Fintype.card W) + 1 : Nat)) :
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (semanticFamily label h h' hW hGroupCofinal) relativeDistance := by
  refine ⟨0, ?_⟩
  intro a _ha
  change relativeDistance *
      ((semanticPresentation (label a) h h').blockLength : ℝ) ≤
    ((semanticPresentation (label a) h h').distance : ℝ)
  have hSemantic := semanticPresentation_distance_ge_of_doubleCoverExpansion
    (label a) h h' hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    (radius a) lambda hLambda (hBase a)
    hVerticalThreshold hEdgeThreshold hFaceThreshold
    (finrank_middleHomology_pos_of_local_ratio
      (label a) h h' rate hRatePositive hW hRatio)
  have hSemanticReal :
      ((radius a / (2 * Fintype.card W) + 1 : Nat) : ℝ) ≤
        ((semanticPresentation (label a) h h').distance : ℝ) := by
    exact_mod_cast hSemantic
  exact (hRelative a).trans hSemanticReal

/-- A uniform two-sided spectral bound on the labelled double covers gives a
fully concrete eventual relative-distance bound.  Both the graph radius and
the positive relative-distance constant are the canonical definitions above;
neither is supplied as conclusion-bearing data. -/
theorem semanticFamily_hasEventualRelativeDistanceAtLeast_of_bilinearBound
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : ∀ a, SmallSetExpansion.HasMeanZeroBilinearBound
      (rightDoubleCoverGraph (label a)) spectral)
    (hVerticalThreshold : (2 * m : ℝ) + (spectral + 1) ≤ d)
    (hEdgeThreshold : 2 * (2 * (spectral + 1)) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (semanticFamily label h h' hW hGroupCofinal)
      (canonicalRelativeDistance (W := W) (R := R) (R' := R')) := by
  apply semanticFamily_hasEventualRelativeDistanceAtLeast_of_doubleCoverExpansion
    label h h' hW hGroupCofinal hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    (canonicalRadius (W := W) (G := G)) (spectral + 1)
  · linarith
  · intro a
    exact rightDoubleCoverGraph_expanding_of_bilinearBound
      (label a) (canonicalRadius (W := W) (G := G) a) spectral 1
      hSpectralNonnegative (hSpectral a) (canonicalRadius_density a)
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold
  · exact hRatePositive
  · exact hRatio
  · intro a
    exact canonicalRelativeDistance_mul_blockLength_le
      a (label a) h h' hW

/-- Source-compatible partite-mixing form of the semantic distance theorem.
Unlike a full mean-zero bound on the double cover, this hypothesis permits
the unavoidable side-sign trivial eigenmode. -/
theorem semanticFamily_hasEventualRelativeDistanceAtLeast_of_partiteMixingBound
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : ∀ a, HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (label a)) (Fintype.card W) spectral)
    (hVerticalThreshold : (2 * m : ℝ) + (spectral + 1) ≤ d)
    (hEdgeThreshold : 2 * (2 * (spectral + 1)) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (semanticFamily label h h' hW hGroupCofinal)
      (canonicalRelativeDistance (W := W) (R := R) (R' := R')) := by
  apply semanticFamily_hasEventualRelativeDistanceAtLeast_of_doubleCoverExpansion
    label h h' hW hGroupCofinal hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    (canonicalRadius (W := W) (G := G)) (spectral + 1)
  · linarith
  · intro a
    exact rightDoubleCoverGraph_expanding_of_partiteMixingBound
      (label a) (canonicalRadius (W := W) (G := G) a) spectral 1
      (hMixing a) (canonicalRadius_partiteDensity a)
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold
  · exact hRatePositive
  · exact hRatio
  · intro a
    exact canonicalRelativeDistance_mul_blockLength_le
      a (label a) h h' hW

/-- The semantic Tanner family is asymptotically good once the same local
codes work in both orientations and the labelled double covers have a
uniform positive expansion constant and a radius linear in the resulting
block length.  Every conclusion is derived from construction data: neither
LDPC locality, rate, distance, nor asymptotic goodness is an input. -/
theorem semanticFamily_isAsymptoticallyGood_of_doubleCoverExpansion
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : A → Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : ∀ a, SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph (label a)) (radius a) lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R'))
    (relativeDistance : ℝ) (hRelativeDistancePositive : 0 < relativeDistance)
    (hRelative : ∀ a,
      relativeDistance * ((semanticPresentation (label a) h h').blockLength : ℝ) ≤
        (radius a / (2 * Fintype.card W) + 1 : Nat)) :
    QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
      (semanticFamily label h h' hW hGroupCofinal) := by
  refine ⟨semanticFamily_hasUniformLDPC label h h' hW hGroupCofinal,
    ⟨rate, hRatePositive,
      semanticFamily_hasEventualRateAtLeast_of_local_ratio
        label h h' hW hGroupCofinal rate hRatio⟩,
    ⟨relativeDistance, hRelativeDistancePositive, ?_⟩⟩
  exact semanticFamily_hasEventualRelativeDistanceAtLeast_of_doubleCoverExpansion
    label h h' hW hGroupCofinal hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    radius lambda hLambda hBase hVerticalThreshold hEdgeThreshold hFaceThreshold
    rate hRatePositive hRatio relativeDistance hRelative

/-- Spectral-input form of the semantic PK22 family theorem.  The graph
radius, density correction, and positive relative-distance constant are all
derived canonically, leaving only the genuine local-code and graph spectral
inputs for the eventual explicit construction. -/
theorem semanticFamily_isAsymptoticallyGood_of_bilinearBound
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : ∀ a, SmallSetExpansion.HasMeanZeroBilinearBound
      (rightDoubleCoverGraph (label a)) spectral)
    (hVerticalThreshold : (2 * m : ℝ) + (spectral + 1) ≤ d)
    (hEdgeThreshold : 2 * (2 * (spectral + 1)) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
      (semanticFamily label h h' hW hGroupCofinal) := by
  refine ⟨semanticFamily_hasUniformLDPC label h h' hW hGroupCofinal,
    ⟨rate, hRatePositive,
      semanticFamily_hasEventualRateAtLeast_of_local_ratio
        label h h' hW hGroupCofinal rate hRatio⟩,
    ⟨canonicalRelativeDistance (W := W) (R := R) (R' := R'),
      canonicalRelativeDistance_pos hW, ?_⟩⟩
  exact semanticFamily_hasEventualRelativeDistanceAtLeast_of_bilinearBound
    label h h' hW hGroupCofinal hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    spectral hSpectralNonnegative hSpectral
    hVerticalThreshold hEdgeThreshold hFaceThreshold
    rate hRatePositive hRatio

/-- Source-compatible terminal family assembly from a part-normalized
bipartite mixing estimate.  This is the form intended for the LPS/PSL double
cover, whose side-sign mode rules out a subdegree full mean-zero bound. -/
theorem semanticFamily_isAsymptoticallyGood_of_partiteMixingBound
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : ∀ a, HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (label a)) (Fintype.card W) spectral)
    (hVerticalThreshold : (2 * m : ℝ) + (spectral + 1) ≤ d)
    (hEdgeThreshold : 2 * (2 * (spectral + 1)) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
      (semanticFamily label h h' hW hGroupCofinal) := by
  refine ⟨semanticFamily_hasUniformLDPC label h h' hW hGroupCofinal,
    ⟨rate, hRatePositive,
      semanticFamily_hasEventualRateAtLeast_of_local_ratio
        label h h' hW hGroupCofinal rate hRatio⟩,
    ⟨canonicalRelativeDistance (W := W) (R := R) (R' := R'),
      canonicalRelativeDistance_pos hW, ?_⟩⟩
  exact semanticFamily_hasEventualRelativeDistanceAtLeast_of_partiteMixingBound
    label h h' hW hGroupCofinal hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    spectral hSpectralNonnegative hMixing
    hVerticalThreshold hEdgeThreshold hFaceThreshold
    rate hRatePositive hRatio

end QEC.Coding.TannerLiftedProduct
