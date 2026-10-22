import QEC.Coding.BalancedProduct.GVPlus
import QEC.Coding.BalancedProduct.LPSGraph
import QEC.Coding.BalancedProduct.TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units

/-!
# The BE20 local check and LPS Tanner incidence labels

This file joins two previously independent concrete ingredients of the
Breuckmann--Eberhardt construction:

* the proved length-402 Gilbert--Varshamov+ local code; and
* the proved 402-regular source-oriented LPS Cayley graph.

The local parity check is derived from the systematic matrix, rather than
supplied as extra data.  At every LPS vertex, incident unoriented edges are
then labelled bijectively by the 402 local coordinates.  Thus no external
matrix representation or unproved labelling assumption enters the Tanner
construction.
-/

noncomputable section

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSTanner

open Classical
open GVPlus LPSGenerators LPSGraph

/-- The 200 checks naturally associated with the systematic generator
matrix `[I_202 | A]`: a word `(x,y)` is accepted exactly when `y = xA`. -/
def localParityCheck :
    Word (ZMod 2) LocalCoordinate →ₗ[ZMod 2] Word (ZMod 2) (Fin 200) where
  toFun := fun w j =>
    w (Sum.inr j) - Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j
  map_add' := by
    intro x y
    funext j
    change (x (Sum.inr j) + y (Sum.inr j)) -
        Matrix.vecMul
          ((fun i => x (Sum.inl i)) + (fun i => y (Sum.inl i))) localMatrix j =
      (x (Sum.inr j) - Matrix.vecMul (fun i => x (Sum.inl i)) localMatrix j) +
        (y (Sum.inr j) - Matrix.vecMul (fun i => y (Sum.inl i)) localMatrix j)
    rw [Matrix.add_vecMul]
    exact add_sub_add_comm _ _ _ _
  map_smul' := by
    intro a x
    funext j
    change a * x (Sum.inr j) -
        Matrix.vecMul (a • fun i => x (Sum.inl i)) localMatrix j =
      a * (x (Sum.inr j) -
        Matrix.vecMul (fun i => x (Sum.inl i)) localMatrix j)
    rw [Matrix.smul_vecMul]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_sub _ _ _).symm

@[simp]
theorem localParityCheck_apply (w : Word (ZMod 2) LocalCoordinate) (j : Fin 200) :
    localParityCheck w j =
      w (Sum.inr j) - Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j :=
  rfl

@[simp]
theorem localParityCheck_systematicEncode (m : Fin 202 → ZMod 2) :
    localParityCheck (systematicEncode localMatrix m) = 0 := by
  funext j
  simp [localParityCheck, systematicEncode]

/-- The concrete local parity check has exactly the already-proved GV+ code
as its kernel. -/
theorem mem_localParityCheck_kernel_iff
    (w : Word (ZMod 2) LocalCoordinate) :
    w ∈ (parityCheckKernelCode localParityCheck).carrier ↔
      w ∈ localCode.carrier := by
  rw [mem_parityCheckKernelCode]
  change localParityCheck w = 0 ↔
    w ∈ (systematicCode localMatrix).carrier
  rw [mem_systematicCode]
  constructor
  · intro hw
    refine ⟨fun i => w (Sum.inl i), ?_⟩
    funext x
    cases x with
    | inl i => rfl
    | inr j =>
        have hj := congrFun hw j
        change w (Sum.inr j) -
          Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j = 0 at hj
        exact (sub_eq_zero.mp hj).symm
  · rintro ⟨m, rfl⟩
    exact localParityCheck_systematicEncode m

/-- The concrete type of the 402 LPS generators. -/
abbrev Generator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  {s : PGL(2, ZMod q) // s ∈ lpsGenerators401 q hq}

theorem card_generator401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (Generator401 q hq) = 402 := by
  simpa [Generator401] using card_lpsGenerators401 q hq40 hq

/-- An arbitrary once-and-for-all identification of the 402 LPS generators
with the 402 coordinates of the fixed local code.  BE20's estimates are
independent of this choice. -/
def generatorCoordinateEquiv
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Generator401 q hq ≃ LocalCoordinate :=
  Fintype.equivOfCardEq <|
    (card_generator401 q hq40 hq).trans localCoordinate_card.symm

/-- At a vertex `g`, left multiplication by a generator parametrizes all
neighbors, with no collisions. -/
def generatorNeighborEquiv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    Generator401 q hq ≃ (lpsCayleyGraph401 q hq).neighborSet g :=
  Equiv.ofBijective
    (fun s : Generator401 q hq =>
      ⟨s.1 * g,
        (lpsCayleyGraph401_adj_iff q hq g (s.1 * g)).2
          ⟨s.1, s.2, rfl⟩⟩)
    ⟨by
      intro s t hst
      apply Subtype.ext
      apply mul_right_cancel (b := g)
      exact congrArg Subtype.val hst,
     by
      rintro ⟨w, hw⟩
      rcases (lpsCayleyGraph401_adj_iff q hq g w).1 hw with ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩⟩

/-- The canonical generator label of an unoriented edge incident to `g`. -/
def incidentGeneratorEquiv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).incidenceSet g ≃ Generator401 q hq :=
  ((lpsCayleyGraph401 q hq).incidenceSetEquivNeighborSet g).trans
    (generatorNeighborEquiv q hq g).symm

/-- The actual BE20 half-edge label: every edge incident to `g` receives one
local-code coordinate. -/
def incidentCoordinateEquiv
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).incidenceSet g ≃ LocalCoordinate :=
  (incidentGeneratorEquiv q hq g).trans
    (generatorCoordinateEquiv q hq40 hq)

theorem incidentCoordinateEquiv_bijective
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    Function.Bijective (incidentCoordinateEquiv q hq40 hq g) :=
  (incidentCoordinateEquiv q hq40 hq g).bijective

/-- The finite vertex type of the source-oriented LPS graph. -/
abbrev Vertex401 (q : ℕ) := PGL(2, ZMod q)

/-- Genuine unoriented edges of the source-oriented LPS graph. -/
abbrev Edge401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  (lpsCayleyGraph401 q hq).edgeSet

noncomputable local instance edge401Fintype
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    Fintype (Edge401 q hq) := by
  letI : DecidableRel (lpsCayleyGraph401 q hq).Adj := Classical.decRel _
  exact SimpleGraph.fintypeEdgeSet (lpsCayleyGraph401 q hq)

/-- Global Tanner checks: 200 local checks at each LPS vertex. -/
abbrev Check401 (q : ℕ) := Vertex401 q × Fin 200

/-- Regard a global edge, together with an endpoint-membership proof, as a
half-edge at that endpoint. -/
def edgeAsIncident
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    (lpsCayleyGraph401 q hq).incidenceSet g :=
  ⟨e.1, e.2, hg⟩

/-- The local coordinate assigned to the half-edge `(g,e)`. -/
def edgeLocalCoordinate
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) : LocalCoordinate :=
  incidentCoordinateEquiv q hq40 hq g (edgeAsIncident q hq e g hg)

/-- One entry of the concrete local parity-check matrix, reconstructed from
the linear map rather than introduced as external matrix data. -/
def localCheckCoefficient (a : LocalCoordinate) (j : Fin 200) : ZMod 2 :=
  localParityCheck (canonicalBasisWord a) j

theorem wordPairing_canonicalBasisWord_right
    {ι : Type*} [Fintype ι]
    (z : Word (ZMod 2) ι) (i : ι) :
    wordPairing z (canonicalBasisWord i) = z i := by
  classical
  rw [wordPairing_apply]
  change (∑ j : ι, z j * canonicalBasisWord i j) = z i
  rw [Fintype.sum_eq_single i]
  · simp [canonicalBasisWord]
  · intro j hji
    simp [canonicalBasisWord, hji]

theorem wordLinearMapTranspose_apply_eq_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
    (y : Word (ZMod 2) κ) (i : ι) :
    wordLinearMapTranspose P y i =
      ∑ k : κ, y k * P (canonicalBasisWord i) k := by
  classical
  rw [wordLinearMapTranspose]
  rfl

/-- Forget the distinguished endpoint of an incident edge while retaining
the proof that it is a genuine global edge. -/
def incidentAsEdge
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {g : Vertex401 q}
    (e : (lpsCayleyGraph401 q hq).incidenceSet g) : Edge401 q hq :=
  ⟨e.1, e.2.1⟩

@[simp]
theorem incidentAsEdge_edgeAsIncident
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    incidentAsEdge q hq (edgeAsIncident q hq e g hg) = e := by
  rfl

/-- Restrict a global edge word to the 402 edges incident to `g`, expressed
in the fixed local-code coordinates. -/
def localView
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) :
    Word (ZMod 2) (Edge401 q hq) →ₗ[ZMod 2]
      Word (ZMod 2) LocalCoordinate where
  toFun := fun x a =>
    x (incidentAsEdge q hq
      ((incidentCoordinateEquiv q hq40 hq g).symm a))
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

theorem localView_basis_of_endpoint
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    localView q hq40 hq g (canonicalBasisWord e) =
      canonicalBasisWord (edgeLocalCoordinate q hq40 hq e g hg) := by
  classical
  let Λ := incidentCoordinateEquiv q hq40 hq g
  let i := edgeAsIncident q hq e g hg
  change (fun a =>
      (canonicalBasisWord (F := ZMod 2) e)
        (incidentAsEdge q hq (Λ.symm a))) =
    canonicalBasisWord (Λ i)
  funext a
  by_cases ha : a = Λ i
  · subst a
    have hedge : incidentAsEdge q hq (Λ.symm (Λ i)) = e := by
      rw [Λ.symm_apply_apply]
      exact incidentAsEdge_edgeAsIncident q hq e g hg
    rw [hedge]
    simp [canonicalBasisWord]
  · have hne : incidentAsEdge q hq (Λ.symm a) ≠ e := by
      intro hedge
      apply ha
      have hi : Λ.symm a = i := by
        have hval : (Λ.symm a).1 = i.1 :=
          congrArg (fun z : Edge401 q hq => z.1) hedge
        exact Subtype.ext hval
      calc
        a = Λ (Λ.symm a) := (Λ.apply_symm_apply a).symm
        _ = Λ i := congrArg Λ hi
    have hleft :
        (canonicalBasisWord (F := ZMod 2) e)
          (incidentAsEdge q hq (Λ.symm a)) = 0 := by
      simp [canonicalBasisWord, hne]
    have hright :
        (canonicalBasisWord (F := ZMod 2) (Λ i)) a = 0 := by
      simp [canonicalBasisWord, ha]
    exact hleft.trans hright.symm

theorem localView_basis_of_not_endpoint
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∉ e.1) :
    localView q hq40 hq g (canonicalBasisWord e) = 0 := by
  classical
  funext a
  let i := (incidentCoordinateEquiv q hq40 hq g).symm a
  have hne : incidentAsEdge q hq i ≠ e := by
    intro hie
    apply hg
    have hgi : g ∈ (incidentAsEdge q hq i).1 := i.2.2
    exact hie ▸ hgi
  change (canonicalBasisWord (F := ZMod 2) e)
    (incidentAsEdge q hq i) = 0
  simp [canonicalBasisWord, hne]

/-- The actual global Tanner boundary.  Its `(g,j)` output is the concrete
local parity check applied to the labelled restriction at `g`. -/
def tannerBoundary
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Word (ZMod 2) (Edge401 q hq) →ₗ[ZMod 2]
      Word (ZMod 2) (Check401 q) where
  toFun := fun x gj => localParityCheck (localView q hq40 hq gj.1 x) gj.2
  map_add' := by
    intro x y
    funext gj
    exact congrFun
      ((localParityCheck.comp (localView q hq40 hq gj.1)).map_add x y) gj.2
  map_smul' := by
    intro a x
    funext gj
    exact congrFun
      ((localParityCheck.comp (localView q hq40 hq gj.1)).map_smul a x) gj.2

theorem tannerBoundary_apply
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) (j : Fin 200) :
    tannerBoundary q hq40 hq x (g, j) =
      localParityCheck (localView q hq40 hq g x) j :=
  rfl

/-- Coordinate form of BE20's defining equation: a basis edge contributes
at an endpoint exactly the local parity-check column selected by that
half-edge label, and contributes zero at every non-endpoint. -/
theorem tannerBoundary_basis_apply
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq)
    (g : Vertex401 q) (j : Fin 200) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) =
      if hg : g ∈ e.1 then
        localCheckCoefficient (edgeLocalCoordinate q hq40 hq e g hg) j
      else 0 := by
  split_ifs with hg
  · rw [tannerBoundary_apply, localView_basis_of_endpoint q hq40 hq e g hg]
    rfl
  · rw [tannerBoundary_apply, localView_basis_of_not_endpoint q hq40 hq e g hg]
    exact congrFun localParityCheck.map_zero j

theorem tannerBoundary_basis_apply_of_endpoint
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq)
    (g : Vertex401 q) (j : Fin 200)
    (hg : g ∈ e.1) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) =
      localCheckCoefficient
        (edgeLocalCoordinate q hq40 hq e g hg) j := by
  rw [tannerBoundary_basis_apply]
  split
  · rfl
  · contradiction

theorem tannerBoundary_basis_apply_of_not_endpoint
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq)
    (g : Vertex401 q) (j : Fin 200)
    (hg : g ∉ e.1) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) = 0 := by
  rw [tannerBoundary_basis_apply]
  split
  · contradiction
  · rfl

/-- Every global edge column is supported on 200 checks at each of its two
endpoints, hence has weight at most 400. -/
theorem tannerBoundary_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) :
    HammingWeight (tannerBoundary q hq40 hq (canonicalBasisWord e)) ≤ 400 := by
  classical
  let Support := {c : Check401 q // c ∈ hammingSupport
    (tannerBoundary q hq40 hq (canonicalBasisWord e))}
  let EndpointCheck := (↑e.1.toFinset × Fin 200)
  have hendpoint (c : Support) : c.1.1 ∈ e.1 := by
    by_contra hg
    have hzero := tannerBoundary_basis_apply_of_not_endpoint
      q hq40 hq e c.1.1 c.1.2 hg
    have hnonzero :
        tannerBoundary q hq40 hq (canonicalBasisWord e) c.1 ≠ 0 := by
      exact (Finset.mem_filter.mp c.2).2
    exact hnonzero hzero
  let selected : Support → EndpointCheck := fun c =>
    (⟨c.1.1, by simpa using hendpoint c⟩, c.1.2)
  have hselected : Function.Injective selected := by
    intro c d hcd
    have hfirst : c.1.1 = d.1.1 :=
      congrArg (fun z => z.1.1) hcd
    have hsecond : c.1.2 = d.1.2 :=
      congrArg (fun z => z.2) hcd
    apply Subtype.ext
    exact Prod.ext hfirst hsecond
  have hcard := Fintype.card_le_of_injective selected hselected
  have hedgeCard : e.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e.1
      ((lpsCayleyGraph401 q hq).not_isDiag_of_mem_edgeSet e.2)
  have htarget : Fintype.card EndpointCheck = 400 := by
    dsimp [EndpointCheck]
    rw [Fintype.card_prod]
    rw [Fintype.card_coe, hedgeCard]
    norm_num
  rw [htarget] at hcard
  simpa [Support, HammingWeight] using hcard

/-- Pairing with the derived local check is represented by the genuine
systematic dual word. -/
theorem wordPairing_systematicDualEncode_eq_localParityCheck
    (y : Word (ZMod 2) (Fin 200))
    (w : Word (ZMod 2) LocalCoordinate) :
    wordPairing (systematicDualEncode localMatrix y) w =
      wordPairing y (localParityCheck w) := by
  classical
  simp only [wordPairing_apply, dotProduct, Fintype.sum_sum_type,
    systematicDualEncode, localParityCheck_apply]
  have hcontract :
      (∑ i, w (Sum.inl i) * Matrix.mulVec localMatrix y i) =
        ∑ j, y j * Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j := by
    calc
      _ = dotProduct (fun i => w (Sum.inl i))
          (Matrix.mulVec localMatrix y) := rfl
      _ = dotProduct
          (Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix) y :=
        Matrix.dotProduct_mulVec (fun i => w (Sum.inl i)) localMatrix y
      _ = _ := by simp [dotProduct, mul_comm]
  have hneg :
      (∑ i, -Matrix.mulVec localMatrix y i * w (Sum.inl i)) =
        -(∑ i, w (Sum.inl i) * Matrix.mulVec localMatrix y i) := by
    calc
      _ = ∑ i, -(w (Sum.inl i) * Matrix.mulVec localMatrix y i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by simp
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← hcontract]
  rw [hneg]
  ring

/-- The transpose of the reconstructed parity check is not an abstract row
space: it is exactly the complementary systematic dual encoding. -/
theorem wordLinearMapTranspose_localParityCheck
    (y : Word (ZMod 2) (Fin 200)) :
    wordLinearMapTranspose localParityCheck y =
      systematicDualEncode localMatrix y := by
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate
    (F := ZMod 2) (ι := LocalCoordinate)).left
  intro w
  simp only [map_sub, LinearMap.sub_apply]
  rw [wordPairing_wordLinearMapTranspose]
  rw [wordPairing_systematicDualEncode_eq_localParityCheck]
  simp

/-- Every nonzero local check combination touches at least 41 incident
variables, by the already-proved genuine dual distance. -/
theorem localTranspose_weight_lower_bound
    (y : Word (ZMod 2) (Fin 200)) (hy : y ≠ 0) :
    41 ≤ HammingWeight (wordLinearMapTranspose localParityCheck y) := by
  rw [wordLinearMapTranspose_localParityCheck]
  exact localMatrix_dual_weight_lower_bound y hy

/-- A nonzero local word below the proved distance 41 cannot satisfy every
local check.  This is the local algebraic input to the Sipser--Spielman/BE20
small-set expansion argument. -/
theorem localParityCheck_ne_zero_of_ne_zero_of_weight_lt
    (w : Word (ZMod 2) LocalCoordinate)
    (hw0 : w ≠ 0)
    (hw : HammingWeight w < 41) :
    localParityCheck w ≠ 0 := by
  intro hcheck
  have hkernel :
      w ∈ (parityCheckKernelCode localParityCheck).carrier :=
    (mem_parityCheckKernelCode localParityCheck w).2 hcheck
  have hcode : w ∈ localCode.carrier :=
    (mem_localParityCheck_kernel_iff w).1 hkernel
  have hlower := localCode_primal_weight_lower_bound w hcode hw0
  omega

/-- If the labelled restriction of an edge word at `g` is nonzero and has
fewer than 41 nonzero incident edges, then at least one of the 200 Tanner
checks at `g` is violated. -/
theorem exists_violated_check_at_vertex
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q)
    (hlocal0 : localView q hq40 hq g x ≠ 0)
    (hlocalWeight : HammingWeight (localView q hq40 hq g x) < 41) :
    ∃ j : Fin 200, tannerBoundary q hq40 hq x (g, j) ≠ 0 := by
  have hsyndrome :=
    localParityCheck_ne_zero_of_ne_zero_of_weight_lt
      (localView q hq40 hq g x) hlocal0 hlocalWeight
  by_contra hnone
  apply hsyndrome
  funext j
  rw [← tannerBoundary_apply q hq40 hq x g j]
  exact not_ne_iff.mp ((not_exists.mp hnone) j)

/-- Vertices at which a global edge word has a nonzero local restriction of
weight below the local distance. -/
def activeLightVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : Finset (Vertex401 q) := by
  classical
  exact Finset.univ.filter fun g =>
    localView q hq40 hq g x ≠ 0 ∧
      HammingWeight (localView q hq40 hq g x) < 41

theorem mem_activeLightVertices_iff
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    g ∈ activeLightVertices q hq40 hq x ↔
      localView q hq40 hq g x ≠ 0 ∧
        HammingWeight (localView q hq40 hq g x) < 41 := by
  classical
  simp only [activeLightVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Violated checks selected at distinct active vertices are distinct global
check coordinates.  Hence the global syndrome weight is at least the number
of active light vertices. -/
theorem card_activeLightVertices_le_boundary_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (activeLightVertices q hq40 hq x).card ≤
      HammingWeight (tannerBoundary q hq40 hq x) := by
  classical
  let Active := {g : Vertex401 q //
    g ∈ activeLightVertices q hq40 hq x}
  have hviolate (g : Active) :
      ∃ j : Fin 200, tannerBoundary q hq40 hq x (g.1, j) ≠ 0 := by
    have hg := (mem_activeLightVertices_iff q hq40 hq x g.1).1 g.2
    exact exists_violated_check_at_vertex q hq40 hq x g.1 hg.1 hg.2
  let chosen : Active → Fin 200 := fun g => Classical.choose (hviolate g)
  have hchosen (g : Active) :
      tannerBoundary q hq40 hq x (g.1, chosen g) ≠ 0 :=
    Classical.choose_spec (hviolate g)
  let selected : Active →
      {c : Check401 q // c ∈ hammingSupport (tannerBoundary q hq40 hq x)} :=
    fun g => ⟨(g.1, chosen g), by
      simp [hammingSupport, hchosen g]⟩
  have hselected : Function.Injective selected := by
    intro g h hgh
    apply Subtype.ext
    exact congrArg (fun c => c.1.1) hgh
  have hcard := Fintype.card_le_of_injective selected hselected
  simpa [Active, HammingWeight] using hcard

/-- Pure combinatorial aggregation interface.  Once graph expansion proves
that every relatively small support has sufficiently many active light
vertices, the concrete Tanner boundary satisfies the project's exact
small-set-expansion predicate.  The premise mentions no syndrome conclusion
and is discharged later from the LPS spectral estimate. -/
theorem tannerBoundary_smallSetExpandingAtRelativeRadius_of_activeLightVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : ℕ)
    (hradius : 0 < radiusDenominator)
    (hexpansion : 0 < expansionDenominator)
    (hactive : ∀ x : Word (ZMod 2) (Edge401 q hq),
      radiusDenominator * HammingWeight x ≤
          radiusNumerator * Fintype.card (Edge401 q hq) →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator *
          (activeLightVertices q hq40 hq x).card) :
    (tannerBoundary q hq40 hq).SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator := by
  refine ⟨hradius, hexpansion, ?_⟩
  intro x hx
  exact (hactive x hx).trans <|
    Nat.mul_le_mul_left expansionDenominator
      (card_activeLightVertices_le_boundary_weight q hq40 hq x)

/-! ## Dual local-to-global bridge -/

/-- The 200 local check coefficients of a global check word at one vertex. -/
def checkBlock
    (q : ℕ) (g : Vertex401 q) :
    Word (ZMod 2) (Check401 q) →ₗ[ZMod 2]
      Word (ZMod 2) (Fin 200) where
  toFun := fun y j => y (g, j)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

@[simp]
theorem checkBlock_basis_same
    (q : ℕ) (g : Vertex401 q) (j : Fin 200) :
    checkBlock q g (canonicalBasisWord (g, j)) =
      canonicalBasisWord j := by
  classical
  funext k
  by_cases hkj : k = j
  · subst k
    simp [checkBlock, canonicalBasisWord]
  · have hpair : (g, k) ≠ (g, j) := by
      intro h
      exact hkj (congrArg Prod.snd h)
    simp [checkBlock, canonicalBasisWord, hkj, hpair]

theorem checkBlock_basis_of_ne
    (q : ℕ) (g w : Vertex401 q) (j : Fin 200)
    (hwg : w ≠ g) :
    checkBlock q w (canonicalBasisWord (g, j)) = 0 := by
  classical
  funext k
  have hpair : (w, k) ≠ (g, j) := by
    intro h
    exact hwg (congrArg Prod.fst h)
  simp [checkBlock, canonicalBasisWord, hpair]

/- The global transpose on an edge is the sum of the two endpoint-local
transpose words, evaluated in their respective half-edge labels. -/
set_option maxRecDepth 5000 in
theorem wordLinearMapTranspose_tannerBoundary_apply
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (e : Edge401 q hq) :
    wordLinearMapTranspose (tannerBoundary q hq40 hq) y e =
      ∑ g : Vertex401 q,
        if hg : g ∈ e.1 then
          wordLinearMapTranspose localParityCheck (checkBlock q g y)
            (edgeLocalCoordinate q hq40 hq e g hg)
        else 0 := by
  classical
  calc
    wordLinearMapTranspose (tannerBoundary q hq40 hq) y e =
        wordPairing
          (wordLinearMapTranspose (tannerBoundary q hq40 hq) y)
          (canonicalBasisWord e) :=
      (wordPairing_canonicalBasisWord_right _ e).symm
    _ = wordPairing y
        (tannerBoundary q hq40 hq (canonicalBasisWord e)) :=
      wordPairing_wordLinearMapTranspose
        (tannerBoundary q hq40 hq) y (canonicalBasisWord e)
    _ = _ := by
      rw [wordPairing_apply]
      change (∑ k : Check401 q, y k *
        tannerBoundary q hq40 hq (canonicalBasisWord e) k) = _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro g _hgUniv
      by_cases hg : g ∈ e.1
      · split
        · rw [wordLinearMapTranspose_apply_eq_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [tannerBoundary_basis_apply_of_endpoint q hq40 hq e g j hg]
          rfl
        · contradiction
      · simp [tannerBoundary_basis_apply_of_not_endpoint q hq40 hq e g _ hg,
          hg]

/-- If exactly one endpoint of an edge carries a nonzero check block, the
global transpose on that edge is that endpoint's local transpose entry. -/
theorem wordLinearMapTranspose_tannerBoundary_apply_of_exposed
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1)
    (hother : ∀ w : Vertex401 q, w ∈ e.1 → w ≠ g →
      checkBlock q w y = 0) :
    wordLinearMapTranspose (tannerBoundary q hq40 hq) y e =
      wordLinearMapTranspose localParityCheck (checkBlock q g y)
        (edgeLocalCoordinate q hq40 hq e g hg) := by
  classical
  rw [wordLinearMapTranspose_tannerBoundary_apply]
  rw [Fintype.sum_eq_single g]
  · simp [hg]
  · intro w hwg
    split_ifs with hw
    · rw [hother w hw hwg]
      exact congrFun (wordLinearMapTranspose localParityCheck).map_zero _
    · rfl

theorem wordLinearMapTranspose_tannerBoundary_basis_apply_of_not_incident
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) (j : Fin 200)
    (e : Edge401 q hq) (hg : g ∉ e.1) :
    wordLinearMapTranspose (tannerBoundary q hq40 hq)
      (canonicalBasisWord (g, j)) e = 0 := by
  classical
  rw [wordLinearMapTranspose_tannerBoundary_apply]
  apply Finset.sum_eq_zero
  intro w _hwUniv
  split_ifs with hw
  · have hwg : w ≠ g := by
      intro hwgeq
      exact hg (hwgeq ▸ hw)
    rw [checkBlock_basis_of_ne q g w j hwg]
    exact congrFun (wordLinearMapTranspose localParityCheck).map_zero _
  · rfl

/-- Every global Tanner check row touches only the 402 graph edges incident to
its vertex. -/
theorem transpose_tannerBoundary_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) (j : Fin 200) :
    HammingWeight
      (wordLinearMapTranspose (tannerBoundary q hq40 hq)
        (canonicalBasisWord (g, j))) ≤ 402 := by
  classical
  let Support := {e : Edge401 q hq // e ∈ hammingSupport
    (wordLinearMapTranspose (tannerBoundary q hq40 hq)
      (canonicalBasisWord (g, j)))}
  have hincident (e : Support) : g ∈ e.1.1 := by
    by_contra hg
    have hzero :=
      wordLinearMapTranspose_tannerBoundary_basis_apply_of_not_incident
        q hq40 hq g j e.1 hg
    have hnonzero :
        wordLinearMapTranspose (tannerBoundary q hq40 hq)
          (canonicalBasisWord (g, j)) e.1 ≠ 0 :=
      (Finset.mem_filter.mp e.2).2
    exact hnonzero hzero
  let selected : Support →
      (lpsCayleyGraph401 q hq).incidenceSet g := fun e =>
    ⟨e.1.1, e.1.2, hincident e⟩
  have hselected : Function.Injective selected := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : (lpsCayleyGraph401 q hq).incidenceSet g => z.1) hef
  have hcard := Fintype.card_le_of_injective selected hselected
  have hincidenceCard :
      Fintype.card ((lpsCayleyGraph401 q hq).incidenceSet g) = 402 :=
    (Fintype.card_congr (incidentCoordinateEquiv q hq40 hq g)).trans
      localCoordinate_card
  rw [hincidenceCard] at hcard
  simpa [Support, HammingWeight] using hcard

/-- Concrete evidence that a supported vertex exposes a nonzero local-dual
coordinate on an edge whose other endpoint carries no check block. -/
structure DualExposureWitness
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) where
  edge : Edge401 q hq
  endpoint : g ∈ edge.1
  centerNonzero : checkBlock q g y ≠ 0
  localNonzero :
    wordLinearMapTranspose localParityCheck (checkBlock q g y)
      (edgeLocalCoordinate q hq40 hq edge g endpoint) ≠ 0
  otherZero : ∀ w : Vertex401 q, w ∈ edge.1 → w ≠ g →
    checkBlock q w y = 0

/-- Vertices possessing a dual exposure witness.  The spectral/combinatorial
step will prove that a positive fraction of every small check support lies in
this finset. -/
def dualExposedVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) : Finset (Vertex401 q) := by
  classical
  exact Finset.univ.filter fun g =>
    Nonempty (DualExposureWitness q hq40 hq y g)

theorem mem_dualExposedVertices_iff
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    g ∈ dualExposedVertices q hq40 hq y ↔
      Nonempty (DualExposureWitness q hq40 hq y g) := by
  classical
  simp [dualExposedVertices]

/-- Exposure witnesses at distinct supported vertices select distinct global
edges, and every selected edge is nonzero in the global transpose. -/
theorem card_dualExposedVertices_le_transpose_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    (dualExposedVertices q hq40 hq y).card ≤
      HammingWeight
        (wordLinearMapTranspose (tannerBoundary q hq40 hq) y) := by
  classical
  let Exposed := {g : Vertex401 q //
    g ∈ dualExposedVertices q hq40 hq y}
  let witness : (g : Exposed) →
      DualExposureWitness q hq40 hq y g.1 := fun g =>
    Classical.choice
      ((mem_dualExposedVertices_iff q hq40 hq y g.1).1 g.2)
  have hglobal (g : Exposed) :
      wordLinearMapTranspose (tannerBoundary q hq40 hq) y
        (witness g).edge ≠ 0 := by
    rw [wordLinearMapTranspose_tannerBoundary_apply_of_exposed
      q hq40 hq y (witness g).edge g.1
      (witness g).endpoint (witness g).otherZero]
    exact (witness g).localNonzero
  let selected : Exposed →
      {e : Edge401 q hq // e ∈ hammingSupport
        (wordLinearMapTranspose (tannerBoundary q hq40 hq) y)} :=
    fun g => ⟨(witness g).edge, by
      simp [hammingSupport, hglobal g]⟩
  have hselected : Function.Injective selected := by
    intro g h heq
    apply Subtype.ext
    by_contra hgh
    have hedge : (witness g).edge = (witness h).edge :=
      congrArg Subtype.val heq
    have hhmem : h.1 ∈ (witness g).edge.1 := by
      rw [hedge]
      exact (witness h).endpoint
    have hzero := (witness g).otherZero h.1 hhmem (Ne.symm hgh)
    exact (witness h).centerNonzero hzero
  have hcard := Fintype.card_le_of_injective selected hselected
  simpa [Exposed, HammingWeight] using hcard

/-- Dual aggregation interface parallel to the primal one.  A graph-side
lower bound on exposed supported vertices implies exact small-set expansion
of the actual global transpose. -/
theorem transpose_tannerBoundary_smallSetExpandingAtRelativeRadius_of_dualExposed
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : ℕ)
    (hradius : 0 < radiusDenominator)
    (hexpansion : 0 < expansionDenominator)
    (hexposed : ∀ y : Word (ZMod 2) (Check401 q),
      radiusDenominator * HammingWeight y ≤
          radiusNumerator * Fintype.card (Check401 q) →
      expansionNumerator * HammingWeight y ≤
        expansionDenominator *
          (dualExposedVertices q hq40 hq y).card) :
    (wordLinearMapTranspose
      (tannerBoundary q hq40 hq)).SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator := by
  refine ⟨hradius, hexpansion, ?_⟩
  intro y hy
  exact (hexposed y hy).trans <|
    Nat.mul_le_mul_left expansionDenominator
      (card_dualExposedVertices_le_transpose_weight q hq40 hq y)

end QEC.Coding.BalancedProduct.LPSTanner
