import QEC.Coding.BalancedProduct.Cyclic
import QEC.Coding.BalancedProduct.CyclicLocality
import QEC.Coding.BalancedProduct.FreeOrbitCoordinates
import QEC.Coding.BalancedProduct.LPSTannerExpansion
import QEC.Coding.BalancedProduct.PKDistance
import Mathlib.Data.Fintype.EquivFin

/-!
# The LPS Tanner map as a cyclic group-algebra matrix

This module equips the concrete LPS vertices, edges, and Tanner checks with
the upper-unipotent cyclic action.  Freeness is proved from the arithmetic
and edge-freeness lemmas, after which the actual Tanner coefficient matrix is
compressed orbitwise into the group algebra.
-/

noncomputable section

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSQuotientTanner

open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance

/-- The canonical cyclic group maps injectively to the upper-unipotent
subgroup used by BE20. -/
def cyclicUpperHom (q : ℕ) :
    CyclicGroup q →* PGL(2, ZMod q) where
  toFun h := upperUnipotentPGL h.toAdd
  map_one' := by simp
  map_mul' x y := by
    exact upperUnipotentPGL_add x.toAdd y.toAdd

theorem cyclicUpperHom_injective (q : ℕ) :
    Function.Injective (cyclicUpperHom q) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  exact upperUnipotentPGL_injective hxy

/-- Right multiplication by the cyclic upper-unipotent element, presented as
a left action.  Commutativity of the cyclic source makes the action law agree
with the right-multiplication convention of the LPS graph. -/
instance cyclicVertexMulAction (q : ℕ) :
    MulAction (CyclicGroup q) (Vertex401 q) where
  smul h g := g * cyclicUpperHom q h
  one_smul g := by
    change g * cyclicUpperHom q 1 = g
    rw [map_one, mul_one]
  mul_smul x y g := by
    change g * cyclicUpperHom q (x * y) =
      (g * cyclicUpperHom q y) * cyclicUpperHom q x
    rw [map_mul, mul_assoc]
    congr 1
    rw [← map_mul, mul_comm, map_mul]

@[simp]
theorem cyclic_smul_vertex (q : ℕ) (h : CyclicGroup q) (g : Vertex401 q) :
    h • g = g * cyclicUpperHom q h := rfl

instance cyclicVertexIsCancelSMul (q : ℕ) :
    IsCancelSMul (CyclicGroup q) (Vertex401 q) where
  right_cancel' x y g hxy := by
    apply cyclicUpperHom_injective q
    apply mul_left_cancel (a := g)
    exact hxy

/-- The induced action on genuine unoriented LPS edges. -/
def smulEdge401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) : Edge401 q hq ≃ Edge401 q hq :=
  (lpsRightIso401 q hq (cyclicUpperHom q h)).mapEdgeSet

instance cyclicEdgeMulAction
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    MulAction (CyclicGroup q) (Edge401 q hq) where
  smul h e := smulEdge401 q hq h e
  one_smul e := by
    apply Subtype.ext
    change Sym2.map (Equiv.mulRight (cyclicUpperHom q 1)) e.1 = e.1
    rw [map_one]
    have hfun : (Equiv.mulRight (1 : Vertex401 q) : Vertex401 q → Vertex401 q) = id := by
      funext g
      simp
    rw [hfun]
    exact congrFun Sym2.map_id e.1
  mul_smul x y e := by
    apply Subtype.ext
    change Sym2.map (Equiv.mulRight (cyclicUpperHom q (x * y))) e.1 =
      Sym2.map (Equiv.mulRight (cyclicUpperHom q x))
        (Sym2.map (Equiv.mulRight (cyclicUpperHom q y)) e.1)
    rw [Sym2.map_map]
    let f : Vertex401 q → Vertex401 q :=
      fun g => g * cyclicUpperHom q (x * y)
    let k : Vertex401 q → Vertex401 q :=
      fun g => (g * cyclicUpperHom q y) * cyclicUpperHom q x
    have hfk : f = k := by
      funext g
      dsimp [f, k]
      rw [map_mul, mul_assoc]
      congr 1
      rw [← map_mul, mul_comm, map_mul]
    exact congrArg (fun z => Sym2.map z e.1) hfk

@[simp]
theorem cyclic_smul_edge_val
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) :
    (h • e).1 = Sym2.map (Equiv.mulRight (cyclicUpperHom q h)) e.1 := rfl

instance cyclicEdgeIsCancelSMul
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    IsCancelSMul (CyclicGroup q) (Edge401 q hq) where
  right_cancel' x y e hxy := by
    have hfix : (x * y⁻¹) • e = e := by
      rw [mul_smul]
      calc
        x • (y⁻¹ • e) = y⁻¹ • (x • e) := by
          rw [← mul_smul, ← mul_smul, mul_comm]
        _ = y⁻¹ • (y • e) := congrArg (fun z => y⁻¹ • z) hxy
        _ = e := inv_smul_smul y e
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    have hedge :
        s((e.1.out.1 * cyclicUpperHom q (x * y⁻¹)),
          (e.1.out.2 * cyclicUpperHom q (x * y⁻¹))) = e.1 := by
      have hv := congrArg Subtype.val hfix
      rw [cyclic_smul_edge_val, ← hout] at hv
      rw [Sym2.map_mk] at hv
      change
        s((e.1.out.1 * cyclicUpperHom q (x * y⁻¹)),
          (e.1.out.2 * cyclicUpperHom q (x * y⁻¹))) =
            s(e.1.out.1, e.1.out.2) at hv
      exact hv.trans hout
    have hadj : (lpsCayleyGraph401 q hq).Adj e.1.out.1 e.1.out.2 := by
      have he := e.2
      rw [← hout, SimpleGraph.mem_edgeSet] at he
      exact he
    let u : upperUnipotentSubgroup (R := ZMod q) :=
      ⟨cyclicUpperHom q (x * y⁻¹), upperUnipotentPGL_mem _⟩
    have hu : u = 1 := by
      apply (upperUnipotent_edge_fixed_iff_one q hq hadj u).1
      change
        s((e.1.out.1 * cyclicUpperHom q (x * y⁻¹)),
          (e.1.out.2 * cyclicUpperHom q (x * y⁻¹))) =
            s(e.1.out.1, e.1.out.2)
      exact hedge.trans hout.symm
    have hupper : cyclicUpperHom q (x * y⁻¹) = 1 :=
      congrArg Subtype.val hu
    have hxyOne : x * y⁻¹ = 1 :=
      cyclicUpperHom_injective q (by simpa using hupper)
    exact (mul_inv_eq_one.mp hxyOne)

/-- Tanner checks inherit the vertex action and retain their local-check
coordinate. -/
instance cyclicCheckMulAction (q : ℕ) :
    MulAction (CyclicGroup q) (Check401 q) where
  smul h gj := (h • gj.1, gj.2)
  one_smul gj := by
    apply Prod.ext
    · exact one_smul _ _
    · rfl
  mul_smul x y gj := by
    apply Prod.ext
    · exact mul_smul x y gj.1
    · rfl

@[simp]
theorem cyclic_smul_check (q : ℕ) (h : CyclicGroup q) (g : Vertex401 q)
    (j : Fin 200) : h • (g, j) = (h • g, j) := rfl

instance cyclicCheckIsCancelSMul (q : ℕ) :
    IsCancelSMul (CyclicGroup q) (Check401 q) where
  right_cancel' x y gj hxy := by
    apply IsCancelSMul.right_cancel x y gj.1
    exact congrArg Prod.fst hxy

/-! ## Equivariance of the concrete Tanner labels -/

theorem mem_smul_edge_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) (g : Vertex401 q) :
    h • g ∈ (h • e).1 ↔ g ∈ e.1 := by
  rw [cyclic_smul_edge_val, Sym2.mem_map]
  constructor
  · rintro ⟨w, hw, hwh⟩
    have hwg : w = g := by
      apply (Equiv.mulRight (cyclicUpperHom q h)).injective
      exact hwh
    simpa [hwg] using hw
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- Right multiplication preserves the generator label, hence also the fixed
local-code coordinate, of every incident half-edge. -/
theorem edgeLocalCoordinate_smul
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    edgeLocalCoordinate q hq40 hq (h • e) (h • g)
        ((mem_smul_edge_iff q hq h e g).2 hg) =
      edgeLocalCoordinate q hq40 hq e g hg := by
  let X := lpsCayleyGraph401 q hq
  let u := cyclicUpperHom q h
  let i := edgeAsIncident q hq e g hg
  let hg' := (mem_smul_edge_iff q hq h e g).2 hg
  let i' := edgeAsIncident q hq (h • e) (h • g) hg'
  let E := X.incidenceSetEquivNeighborSet g
  let E' := X.incidenceSetEquivNeighborSet (h • g)
  let w := E i
  have hw' : X.Adj (h • g) (w.1 * u) := by
    exact (lpsCayleyGraph401_adj_mul_right_iff q hq g w.1 u).2 w.2
  let w' : X.neighborSet (h • g) := ⟨w.1 * u, hw'⟩
  have hEi : E' i' = w' := by
    have horiginal : s(g, w.1) = e.1 := by
      have hs := congrArg Subtype.val (E.symm_apply_apply i)
      exact hs
    have htransport : s(h • g, w.1 * u) = (h • e).1 := by
      rw [cyclic_smul_vertex, cyclic_smul_edge_val, ← horiginal,
        Sym2.map_mk]
      rfl
    have hinv : E'.symm w' = i' := by
      apply Subtype.ext
      exact htransport
    calc
      E' i' = E' (E'.symm w') := congrArg E' hinv.symm
      _ = w' := E'.apply_symm_apply w'
  let s0 := incidentGeneratorEquiv q hq g i
  have hs0 : generatorNeighborEquiv q hq (h • g) s0 = w' := by
    apply Subtype.ext
    have hs0old : generatorNeighborEquiv q hq g s0 = w := by
      exact (generatorNeighborEquiv q hq g).apply_symm_apply w
    have hs0val := congrArg Subtype.val hs0old
    change s0.1 * g = w.1 at hs0val
    change s0.1 * (g * u) = w.1 * u
    rw [← mul_assoc, hs0val]
  have hgen : incidentGeneratorEquiv q hq (h • g) i' = s0 := by
    change (generatorNeighborEquiv q hq (h • g)).symm (E' i') = s0
    rw [hEi, ← hs0]
    exact (generatorNeighborEquiv q hq (h • g)).symm_apply_apply s0
  change generatorCoordinateEquiv q hq40 hq
      (incidentGeneratorEquiv q hq (h • g) i') =
    generatorCoordinateEquiv q hq40 hq (incidentGeneratorEquiv q hq g i)
  exact congrArg (generatorCoordinateEquiv q hq40 hq) hgen

/-! ## Orbit compression into the group algebra -/

/-- Matrix coefficient of the actual concrete Tanner boundary. -/
def tannerCoefficient
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Matrix (Check401 q) (Edge401 q hq) (ZMod 2) :=
  fun c e => tannerBoundary q hq40 hq (canonicalBasisWord e) c

theorem tannerCoefficient_smul
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (c : Check401 q) (e : Edge401 q hq) :
    tannerCoefficient q hq40 hq (h • c) (h • e) =
      tannerCoefficient q hq40 hq c e := by
  rcases c with ⟨g, j⟩
  change tannerBoundary q hq40 hq (canonicalBasisWord (h • e)) (h • g, j) =
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j)
  by_cases hg : g ∈ e.1
  · have hg' : h • g ∈ (h • e).1 :=
      (mem_smul_edge_iff q hq h e g).2 hg
    rw [tannerBoundary_basis_apply_of_endpoint q hq40 hq (h • e) (h • g) j hg',
      tannerBoundary_basis_apply_of_endpoint q hq40 hq e g j hg]
    exact congrArg (fun a => localCheckCoefficient a j)
      (edgeLocalCoordinate_smul q hq40 hq h e g hg)
  · have hg' : h • g ∉ (h • e).1 := by
      intro hmem
      exact hg ((mem_smul_edge_iff q hq h e g).1 hmem)
    rw [tannerBoundary_basis_apply_of_not_endpoint q hq40 hq (h • e) (h • g) j hg',
      tannerBoundary_basis_apply_of_not_endpoint q hq40 hq e g j hg]

/-- Orbit rows (Tanner checks modulo the upper-unipotent action). -/
abbrev CheckOrbit401 (q : ℕ) :=
  OrbitIndex (CyclicGroup q) (Check401 q)

/-- Orbit columns (LPS edges modulo the upper-unipotent action). -/
abbrev EdgeOrbit401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  OrbitIndex (CyclicGroup q) (Edge401 q hq)

/-- The group-algebra Tanner matrix obtained from the actual LPS Tanner
boundary, with no matrix supplied as external data. -/
def lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Matrix (CheckOrbit401 q) (EdgeOrbit401 q hq)
      (MonoidAlgebra (ZMod 2) (CyclicGroup q)) :=
  groupAlgebraMatrix (CyclicGroup q) (tannerCoefficient q hq40 hq)

/-- Entrywise, the right-regular expansion of the compressed matrix is the
actual Tanner coefficient matrix in free-orbit coordinates. -/
theorem rightRegular_lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (ro : CheckOrbit401 q) (co : EdgeOrbit401 q hq)
    (go gi : CyclicGroup q) :
    LiftedProduct.rightRegularMatrix
        (lpsTannerGroupAlgebraMatrix q hq40 hq ro co) go gi =
      tannerCoefficient q hq40 hq
        ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, go))
        ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, gi)) := by
  exact rightRegularMatrix_groupAlgebraMatrix
    (CyclicGroup q) (tannerCoefficient q hq40 hq)
    (tannerCoefficient_smul q hq40 hq) ro co go gi

noncomputable instance edge401Fintype'
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Fintype (Edge401 q hq) := by
  letI : DecidableRel (lpsCayleyGraph401 q hq).Adj := Classical.decRel _
  exact SimpleGraph.fintypeEdgeSet (lpsCayleyGraph401 q hq)

noncomputable instance checkOrbitFintype
    (q : ℕ) [Fact q.Prime] : Fintype (CheckOrbit401 q) := by
  letI : Finite (Check401 q) := inferInstance
  letI : Finite (CheckOrbit401 q) :=
    Quotient.finite (MulAction.orbitRel (CyclicGroup q) (Check401 q))
  exact Fintype.ofFinite _

noncomputable instance edgeOrbitFintype
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Fintype (EdgeOrbit401 q hq) := by
  letI : Finite (Edge401 q hq) := inferInstance
  letI : Finite (EdgeOrbit401 q hq) :=
    Quotient.finite (MulAction.orbitRel (CyclicGroup q) (Edge401 q hq))
  exact Fintype.ofFinite _

noncomputable instance checkOrbitDecidableEq
    (q : ℕ) [Fact q.Prime] : DecidableEq (CheckOrbit401 q) :=
  Classical.decEq _

noncomputable instance edgeOrbitDecidableEq
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : DecidableEq (EdgeOrbit401 q hq) :=
  Classical.decEq _

/-- Reindex an actual LPS edge word by its free-orbit coordinates. -/
def edgeWordInOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    Word (ZMod 2) (EdgeOrbit401 q hq × CyclicGroup q) :=
  fun p => x ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm p)

/-- Reindex an actual LPS check word by its free-orbit coordinates. -/
def checkWordInOrbitCoordinates
    (q : ℕ)
    (y : Word (ZMod 2) (Check401 q)) :
    Word (ZMod 2) (CheckOrbit401 q × CyclicGroup q) :=
  fun p => y ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm p)

/-- Convert an orbit-coordinate check word back to actual LPS checks. -/
def checkWordFromOrbitCoordinates
    (q : ℕ)
    (z : Word (ZMod 2) (CheckOrbit401 q × CyclicGroup q)) :
    Word (ZMod 2) (Check401 q) :=
  fun c => z (freeOrbitEquiv (CyclicGroup q) (Check401 q) c)

theorem checkWordIn_fromOrbitCoordinates
    (q : ℕ)
    (z : Word (ZMod 2) (CheckOrbit401 q × CyclicGroup q)) :
    checkWordInOrbitCoordinates q (checkWordFromOrbitCoordinates q z) = z := by
  funext p
  simp [checkWordInOrbitCoordinates, checkWordFromOrbitCoordinates]

/-- Convert an orbit-coordinate edge word back to the actual LPS edges. -/
def edgeWordFromOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (z : Word (ZMod 2) (EdgeOrbit401 q hq × CyclicGroup q)) :
    Word (ZMod 2) (Edge401 q hq) :=
  fun e => z (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq) e)

theorem edgeWordIn_fromOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (z : Word (ZMod 2) (EdgeOrbit401 q hq × CyclicGroup q)) :
    edgeWordInOrbitCoordinates q hq (edgeWordFromOrbitCoordinates q hq z) = z := by
  funext p
  simp [edgeWordInOrbitCoordinates, edgeWordFromOrbitCoordinates]

theorem HammingWeight_edgeWordInOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    HammingWeight (edgeWordInOrbitCoordinates q hq x) = HammingWeight x := by
  exact HammingWeight_precomp_equiv
    (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm x

theorem HammingWeight_checkWordInOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight (checkWordInOrbitCoordinates q y) = HammingWeight y := by
  exact HammingWeight_precomp_equiv
    (freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm y

/-- Every value of the concrete Tanner linear map is the sum of its basis
coefficients against the input word. -/
theorem tannerBoundary_eq_sum_tannerCoefficient
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) (c : Check401 q) :
    tannerBoundary q hq40 hq x c =
      ∑ e : Edge401 q hq, tannerCoefficient q hq40 hq c e * x e := by
  have hx : x = ∑ e : Edge401 q hq, x e • canonicalBasisWord e := by
    funext k
    classical
    rw [Finset.sum_apply]
    rw [Fintype.sum_eq_single k]
    · simp [canonicalBasisWord]
    · intro e hek
      simp [canonicalBasisWord, hek]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [LinearMapClass.map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, tannerCoefficient]
  apply Finset.sum_congr rfl
  intro e _he
  exact mul_comm (x e)
    (tannerBoundary q hq40 hq (canonicalBasisWord e) c)

/-- The horizontal `tannerAction` of the compressed group-algebra matrix is
definitionally the concrete Tanner boundary after the proved orbit
reindexings. -/
theorem tannerAction_lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)
        (edgeWordInOrbitCoordinates q hq x) =
      checkWordInOrbitCoordinates q (tannerBoundary q hq40 hq x) := by
  funext p
  rcases p with ⟨ro, go⟩
  rw [tannerAction_apply]
  change
    (∑ co : EdgeOrbit401 q hq, ∑ gi : CyclicGroup q,
      LiftedProduct.rightRegularMatrix
          (lpsTannerGroupAlgebraMatrix q hq40 hq ro co) go gi *
        x ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, gi))) =
      tannerBoundary q hq40 hq x
        ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, go))
  rw [tannerBoundary_eq_sum_tannerCoefficient]
  exact sum_rightRegularMatrix_groupAlgebraMatrix
    (CyclicGroup q) (tannerCoefficient q hq40 hq)
    (tannerCoefficient_smul q hq40 hq) x ro go

/-- The star-transposed group-algebra action is the actual transpose Tanner
map after the same proved orbit reindexings. -/
theorem tannerAction_starTranspose_lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    tannerAction
        (LiftedProduct.starTranspose
          (lpsTannerGroupAlgebraMatrix q hq40 hq))
        (checkWordInOrbitCoordinates q y) =
      edgeWordInOrbitCoordinates q hq
        (wordLinearMapTranspose (tannerBoundary q hq40 hq) y) := by
  funext p
  rcases p with ⟨co, go⟩
  rw [tannerAction_apply]
  change
    (∑ ro : CheckOrbit401 q, ∑ gi : CyclicGroup q,
      LiftedProduct.rightRegularMatrix
          (LiftedProduct.starTranspose
            (lpsTannerGroupAlgebraMatrix q hq40 hq) co ro) go gi *
        y ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, gi))) =
      wordLinearMapTranspose (tannerBoundary q hq40 hq) y
        ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, go))
  rw [LPSTanner.wordLinearMapTranspose_apply_eq_sum]
  have hsum := sum_rightRegularMatrix_starTranspose_groupAlgebraMatrix
    (CyclicGroup q) (tannerCoefficient q hq40 hq)
    (tannerCoefficient_smul q hq40 hq) y co go
  have hsum' :
      (∑ ro : CheckOrbit401 q, ∑ gi : CyclicGroup q,
        LiftedProduct.rightRegularMatrix
            (LiftedProduct.starTranspose
              (lpsTannerGroupAlgebraMatrix q hq40 hq) co ro) go gi *
          y ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, gi))) =
        ∑ c : Check401 q,
          tannerCoefficient q hq40 hq c
              ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, go)) *
            y c := by
    simpa only [lpsTannerGroupAlgebraMatrix] using hsum
  rw [hsum']
  apply Finset.sum_congr rfl
  intro c _hc
  change tannerCoefficient q hq40 hq c
      ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, go)) * y c =
    y c * tannerCoefficient q hq40 hq c
      ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, go))
  exact mul_comm _ _

/-- The proved primal LPS Tanner expansion transported to the exact
group-algebra `tannerAction` used by the PK distance theorem. -/
theorem lpsTannerAction_boundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    LinearMap.SmallSetExpandingAtRelativeRadius
      (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq))
      1 10000000 44 41123 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro z hz
  let x := edgeWordFromOrbitCoordinates q hq z
  have hzEq : edgeWordInOrbitCoordinates q hq x = z :=
    edgeWordIn_fromOrbitCoordinates q hq z
  have hwIn : HammingWeight x = HammingWeight z := by
    rw [← hzEq, HammingWeight_edgeWordInOrbitCoordinates]
  have hactual :=
    (LPSTannerExpansion.be20Tanner_boundary_expansion q hq40 hq hLPS).2.2 x
  have hradius : 10000000 * HammingWeight x ≤
      1 * Fintype.card (Edge401 q hq) := by
    rw [hwIn]
    simpa only [Fintype.card_congr
      (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq))] using hz
  have hexpand := hactual hradius
  have hmap := tannerAction_lpsTannerGroupAlgebraMatrix q hq40 hq x
  rw [hzEq] at hmap
  rw [hwIn] at hexpand
  rw [hmap, HammingWeight_checkWordInOrbitCoordinates]
  exact hexpand

/-- The proved transpose LPS Tanner expansion transported to the exact
star-transposed group-algebra action used by the dual PK cases. -/
theorem lpsTannerAction_coboundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    LinearMap.SmallSetExpandingAtRelativeRadius
      (tannerAction (LiftedProduct.starTranspose
        (lpsTannerGroupAlgebraMatrix q hq40 hq)))
      1 10000000 11 102500 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro z hz
  let y := checkWordFromOrbitCoordinates q z
  have hzEq : checkWordInOrbitCoordinates q y = z :=
    checkWordIn_fromOrbitCoordinates q z
  have hwIn : HammingWeight y = HammingWeight z := by
    rw [← hzEq, HammingWeight_checkWordInOrbitCoordinates]
  have hactual :=
    (LPSTannerExpansion.be20Tanner_coboundary_expansion q hq40 hq hLPS).2.2 y
  have hradius : 10000000 * HammingWeight y ≤
      1 * Fintype.card (Check401 q) := by
    rw [hwIn]
    simpa only [Fintype.card_congr
      (freeOrbitEquiv (CyclicGroup q) (Check401 q))] using hz
  have hexpand := hactual hradius
  have hmap :=
    tannerAction_starTranspose_lpsTannerGroupAlgebraMatrix q hq40 hq y
  rw [hzEq] at hmap
  rw [hwIn] at hexpand
  rw [hmap, HammingWeight_edgeWordInOrbitCoordinates]
  exact hexpand

set_option maxRecDepth 4000 in
/-- The actual LPS edge set is the free cyclic cover of its edge-orbit set. -/
theorem card_edge401_eq_cyclic_mul_edgeOrbit
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    Fintype.card (Edge401 q hq) =
      q * Fintype.card (EdgeOrbit401 q hq) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hEdge :
      Fintype.card (EdgeOrbit401 q hq × CyclicGroup q) =
        Fintype.card (Edge401 q hq) :=
    Fintype.card_congr (freeOrbitEquiv
      (CyclicGroup q) (Edge401 q hq)).symm
  rw [← hEdge, Fintype.card_prod]
  simp [CyclicGroup, ZMod.card, mul_comm]

/-- The relative LPS expansion supplies precisely the lifted radius obtained
from the quotient edge-orbit scale `|E/H| / 10^7`. -/
theorem lpsTannerAction_boundary_expansion_at_quotientScale
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)).SmallSetExpanding
      (q * (Fintype.card (EdgeOrbit401 q hq) / 10000000)) 44 41123 := by
  have hRelative := lpsTannerAction_boundary_expansion q hq40 hq hLPS
  refine ⟨hRelative.2.1, ?_⟩
  intro z hz
  apply hRelative.2.2 z
  calc
    10000000 * HammingWeight z ≤
        10000000 * (q * (Fintype.card (EdgeOrbit401 q hq) / 10000000)) :=
      Nat.mul_le_mul_left _ hz
    _ = q * (10000000 *
        (Fintype.card (EdgeOrbit401 q hq) / 10000000)) := by ring
    _ ≤ q * Fintype.card (EdgeOrbit401 q hq) :=
      Nat.mul_le_mul_left q (Nat.mul_div_le _ _)
    _ = Fintype.card (Edge401 q hq) :=
      (card_edge401_eq_cyclic_mul_edgeOrbit q hq).symm
    _ = 1 * Fintype.card (EdgeOrbit401 q hq × CyclicGroup q) := by
      rw [one_mul]
      exact Fintype.card_congr
        (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq))

/-- Any attained quotient Tanner minimum is at least the explicit orbit-scale
lower bound forced by the proved LPS expansion. -/
theorem quotientTanner_minimumDistance_lowerBound
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    {actualDistance : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode
          actualDistance) :
    Fintype.card (EdgeOrbit401 q hq) / 10000000 ≤ actualDistance := by
  apply quotientMinimumDistance_ge_of_smallSetExpanding
    (distanceLowerBound := Fintype.card (EdgeOrbit401 q hq) / 10000000)
    (expansionNumerator := 44) (expansionDenominator := 41123)
    (lpsTannerGroupAlgebraMatrix q hq40 hq) hMinimum (by norm_num)
  simpa [CyclicGroup, ZMod.card] using
    lpsTannerAction_boundary_expansion_at_quotientScale q hq40 hq hLPS

set_option maxRecDepth 4000 in
/-- The actual LPS check set is the free cyclic cover of its check-orbit set. -/
theorem card_check401_eq_cyclic_mul_checkOrbit
    (q : ℕ) [Fact q.Prime] :
    Fintype.card (Check401 q) = q * Fintype.card (CheckOrbit401 q) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hCheck :
      Fintype.card (Check401 q) =
        Fintype.card (CheckOrbit401 q × CyclicGroup q) :=
    Fintype.card_congr (freeOrbitEquiv (CyclicGroup q) (Check401 q))
  rw [hCheck, Fintype.card_prod]
  simp [CyclicGroup, ZMod.card, mul_comm]

/-- The actual balanced-product qubit count is the sum of the lifted Tanner
edge and check coordinates.  This is the source-repaired finite identity
`N = |X₁| + (s - k_L)|X₀|`, before specializing `s = 402` and `k_L = 202`. -/
theorem lpsHorizontalSubsystem_blocklength_eq_edge_add_check
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit (CyclicGroup q)) =
      Fintype.card (Edge401 q hq) + Fintype.card (Check401 q) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [Cyclic.card_qubitIndex, Nat.mul_add,
    ← card_edge401_eq_cyclic_mul_edgeOrbit q hq,
    ← card_check401_eq_cyclic_mul_checkOrbit q]

/-- For the concrete BE20 local code `[402,202,≥41]`, the corrected exact
blocklength is `N = 201|X₀| + 200|X₀| = 401|X₀|`.  No source or spectral
premise is used. -/
theorem lpsHorizontalSubsystem_blocklength_eq
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit (CyclicGroup q)) =
      401 * Fintype.card (Vertex401 q) := by
  rw [lpsHorizontalSubsystem_blocklength_eq_edge_add_check q hq,
    LPSTannerExpansion.card_edge401_eq q hq40 hq,
    LPSTannerExpansion.card_check401_eq q]
  omega

/-- The transpose relative expansion at the quotient check-orbit scale. -/
theorem lpsTannerAction_coboundary_expansion_at_quotientScale
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (tannerAction (LiftedProduct.starTranspose
      (lpsTannerGroupAlgebraMatrix q hq40 hq))).SmallSetExpanding
        (q * (Fintype.card (CheckOrbit401 q) / 10000000)) 11 102500 := by
  have hRelative := lpsTannerAction_coboundary_expansion q hq40 hq hLPS
  refine ⟨hRelative.2.1, ?_⟩
  intro z hz
  apply hRelative.2.2 z
  calc
    10000000 * HammingWeight z ≤
        10000000 * (q * (Fintype.card (CheckOrbit401 q) / 10000000)) :=
      Nat.mul_le_mul_left _ hz
    _ = q * (10000000 *
        (Fintype.card (CheckOrbit401 q) / 10000000)) := by ring
    _ ≤ q * Fintype.card (CheckOrbit401 q) :=
      Nat.mul_le_mul_left q (Nat.mul_div_le _ _)
    _ = Fintype.card (Check401 q) :=
      (card_check401_eq_cyclic_mul_checkOrbit q).symm
    _ = 1 * Fintype.card (CheckOrbit401 q × CyclicGroup q) := by
      rw [one_mul]
      exact Fintype.card_congr
        (freeOrbitEquiv (CyclicGroup q) (Check401 q))

/-- Every column of the compressed Tanner action has weight at most `400`,
because an actual LPS edge meets 200 local checks at each endpoint. -/
theorem lpsTannerAction_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (i : EdgeOrbit401 q hq × CyclicGroup q) :
    HammingWeight
      (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)
        (Pi.single i 1)) ≤ 400 := by
  let e : Edge401 q hq :=
    (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm i
  let z := edgeWordFromOrbitCoordinates q hq (Pi.single i 1)
  have hz : z = canonicalBasisWord e := by
    funext e'
    classical
    simp only [z, edgeWordFromOrbitCoordinates, canonicalBasisWord,
      Pi.single_apply]
    by_cases he : e' = e
    · subst e'
      simp [e]
    · have hfree :
          freeOrbitEquiv (CyclicGroup q) (Edge401 q hq) e' ≠ i := by
        intro heq
        apply he
        simpa [e] using
          ((Equiv.apply_eq_iff_eq_symm_apply
            (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq))).mp heq)
      have horbit :
          (orbitOf (CyclicGroup q) (Edge401 q hq) e',
            groupCoordinate (CyclicGroup q) (Edge401 q hq) e') ≠ i := by
        change freeOrbitEquiv (CyclicGroup q) (Edge401 q hq) e' ≠ i
        exact hfree
      simp [horbit, he]
  have hzCoordinates :
      edgeWordInOrbitCoordinates q hq z = Pi.single i 1 :=
    edgeWordIn_fromOrbitCoordinates q hq (Pi.single i 1)
  have hmap := tannerAction_lpsTannerGroupAlgebraMatrix q hq40 hq z
  rw [hzCoordinates] at hmap
  rw [hmap, HammingWeight_checkWordInOrbitCoordinates, hz]
  exact LPSTanner.tannerBoundary_basis_weight_le q hq40 hq e

/-- Every column of the star-transposed compressed Tanner action has weight at
most the graph degree `402`; no matrix sparsity is supplied externally. -/
theorem lpsTannerAction_starTranspose_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (i : CheckOrbit401 q × CyclicGroup q) :
    HammingWeight
      (tannerAction (LiftedProduct.starTranspose
        (lpsTannerGroupAlgebraMatrix q hq40 hq)) (Pi.single i 1)) ≤ 402 := by
  let c : Check401 q :=
    (freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm i
  let y := checkWordFromOrbitCoordinates q (Pi.single i 1)
  have hy : y = canonicalBasisWord c := by
    funext c'
    classical
    simp only [y, checkWordFromOrbitCoordinates, canonicalBasisWord,
      Pi.single_apply]
    by_cases hc : c' = c
    · subst c'
      simp [c]
    · have hfree : freeOrbitEquiv (CyclicGroup q) (Check401 q) c' ≠ i := by
        intro heq
        apply hc
        simpa [c] using
          ((Equiv.apply_eq_iff_eq_symm_apply
            (freeOrbitEquiv (CyclicGroup q) (Check401 q))).mp heq)
      have horbit :
          (orbitOf (CyclicGroup q) (Check401 q) c',
            groupCoordinate (CyclicGroup q) (Check401 q) c') ≠ i := by
        change freeOrbitEquiv (CyclicGroup q) (Check401 q) c' ≠ i
        exact hfree
      simp [horbit, hc]
  have hyCoordinates : checkWordInOrbitCoordinates q y = Pi.single i 1 :=
    checkWordIn_fromOrbitCoordinates q (Pi.single i 1)
  have hmap :=
    tannerAction_starTranspose_lpsTannerGroupAlgebraMatrix q hq40 hq y
  rw [hyCoordinates] at hmap
  rw [hmap, HammingWeight_edgeWordInOrbitCoordinates, hy]
  rcases c with ⟨g, j⟩
  exact LPSTanner.transpose_tannerBoundary_basis_weight_le q hq40 hq g j

/-- The actual BE20 cyclic balanced product has uniform check weight and
variable degree at most `404 = max 400 402 + 2`.  This conclusion uses only
the constructed Tanner and cyclic matrices; it does not use the external LPS
Ramanujan assumption. -/
theorem lpsHorizontalSubsystem_boundedLocality
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.liftedProductData
          (lpsTannerGroupAlgebraMatrix q hq40 hq)
          (Cyclic.cyclicGenerator q))).localityProfile
      404 := by
  simpa using
    (CyclicLocality.boundaryIncidence_boundedLocality_of_tannerAction_bounds
      (forwardBound := 400) (transposeBound := 402)
      (lpsTannerGroupAlgebraMatrix q hq40 hq)
      (Cyclic.cyclicGenerator q)
      (lpsTannerAction_basis_weight_le q hq40 hq)
      (lpsTannerAction_starTranspose_basis_weight_le q hq40 hq))

/-- Explicit quotient-distance scale supplied by the primal expansion. -/
def lpsPrimalQuotientDistanceScale
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Nat :=
  Fintype.card (EdgeOrbit401 q hq) / 10000000

/-- Explicit quotient-distance scale supplied by the transpose expansion. -/
def lpsDualQuotientDistanceScale
    (q : ℕ) [Fact q.Prime] : Nat :=
  Fintype.card (CheckOrbit401 q) / 10000000

/-- Integral dressed-Z lower bound obtained from the exact PK constants. -/
def lpsDressedZLowerBound
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Nat :=
  (q * lpsPrimalQuotientDistanceScale q hq) / 3739

/-- Integral dressed-X lower bound obtained from the exact PK constants. -/
def lpsDressedXLowerBound
    (q : ℕ) [Fact q.Prime] : Nat :=
  min (q * lpsDualQuotientDistanceScale q) (q / 804) / 37273

/-! ## Quotient Tanner dimension and attained minimum distances -/

set_option maxRecDepth 4000 in
theorem card_checkOrbit_lt_card_edgeOrbit
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (CheckOrbit401 q) < Fintype.card (EdgeOrbit401 q hq) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hEdge := Fintype.card_congr
    (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq))
  have hCheck := Fintype.card_congr
    (freeOrbitEquiv (CyclicGroup q) (Check401 q))
  have hActual :
      Fintype.card (Check401 q) < Fintype.card (Edge401 q hq) := by
    rw [LPSTannerExpansion.card_check401_eq q,
      LPSTannerExpansion.card_edge401_eq q hq40 hq]
    have hvpos : 0 < Fintype.card (Vertex401 q) := Fintype.card_pos
    omega
  apply (Nat.mul_lt_mul_right (Fintype.card_pos :
    0 < Fintype.card (CyclicGroup q))).mp
  calc
    Fintype.card (CheckOrbit401 q) * Fintype.card (CyclicGroup q) =
        Fintype.card (CheckOrbit401 q × CyclicGroup q) :=
          (Fintype.card_prod _ _).symm
    _ = Fintype.card (Check401 q) := hCheck.symm
    _ < Fintype.card (Edge401 q hq) := hActual
    _ = Fintype.card (EdgeOrbit401 q hq × CyclicGroup q) := hEdge
    _ = Fintype.card (EdgeOrbit401 q hq) * Fintype.card (CyclicGroup q) :=
      Fintype.card_prod _ _

/-- Rank-nullity for the actual quotient Tanner boundary gives the source
dimension lower bound.  No independence or full-rank property of the checks
is assumed. -/
theorem quotientTanner_middleHomology_finrank_lowerBound
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (EdgeOrbit401 q hq) - Fintype.card (CheckOrbit401 q) ≤
      Module.finrank (ZMod 2)
        (HorizontalSubsystem.quotientTannerComplex
          (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleHomology := by
  let A := lpsTannerGroupAlgebraMatrix q hq40 hq
  change Fintype.card (EdgeOrbit401 q hq) -
      Fintype.card (CheckOrbit401 q) ≤
    Module.finrank (ZMod 2)
      (HorizontalSubsystem.quotientTannerComplex A).middleHomology
  rw [HorizontalSubsystem.finrank_quotientTannerComplex_middleHomology_eq_ker]
  have hRankNullity :=
    (HorizontalSubsystem.quotientBoundary A).finrank_range_add_finrank_ker
  have hRangeLe :
      Module.finrank (ZMod 2)
          (LinearMap.range (HorizontalSubsystem.quotientBoundary A)) ≤
        Module.finrank (ZMod 2) (Word (ZMod 2) (CheckOrbit401 q)) :=
    Submodule.finrank_le _
  have hDomain :
      Module.finrank (ZMod 2) (Word (ZMod 2) (EdgeOrbit401 q hq)) =
        Fintype.card (EdgeOrbit401 q hq) := by
    simp
  have hCodomain :
      Module.finrank (ZMod 2) (Word (ZMod 2) (CheckOrbit401 q)) =
        Fintype.card (CheckOrbit401 q) := by
    simp
  rw [hDomain] at hRankNullity
  rw [hCodomain] at hRangeLe
  omega

/-- The selected horizontal subsystem has at least the quotient Tanner
rank-nullity dimension.  The only input is the constructed finite matrix. -/
theorem lpsHorizontalSubsystem_logicalQubits_lowerBound
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    let hOdd : Odd q :=
      (Fact.out : q.Prime).odd_of_ne_two (by omega)
    let D := HorizontalSubsystem.horizontalSubsystem
      (lpsTannerGroupAlgebraMatrix q hq40 hq)
      (Cyclic.cyclicGenerator q)
      (by simpa [CyclicGroup, ZMod.card] using hOdd)
    Fintype.card (EdgeOrbit401 q hq) - Fintype.card (CheckOrbit401 q) ≤
      D.logicalQubits := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  dsimp only
  rw [HorizontalSubsystem.horizontalSubsystem_logicalQubits]
  exact quotientTanner_middleHomology_finrank_lowerBound q hq40 hq

/-- The orbit-rank lower bound is exactly of order `|X₀|/q`: multiplying
the edge-orbit/check-orbit difference by the free-orbit size recovers the
number of LPS vertices. -/
theorem cyclic_mul_edgeOrbit_sub_checkOrbit
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    q * (Fintype.card (EdgeOrbit401 q hq) -
        Fintype.card (CheckOrbit401 q)) =
      Fintype.card (Vertex401 q) := by
  rw [Nat.mul_sub_left_distrib,
    ← card_edge401_eq_cyclic_mul_edgeOrbit q hq,
    ← card_check401_eq_cyclic_mul_checkOrbit q,
    LPSTannerExpansion.card_edge401_eq q hq40 hq,
    LPSTannerExpansion.card_check401_eq q]
  omega

theorem quotientTanner_middleCycleCode_exists_nonzero
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    ∃ x : Word (ZMod 2) (EdgeOrbit401 q hq),
      x ∈ (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode.carrier ∧
      x ≠ 0 := by
  let A := lpsTannerGroupAlgebraMatrix q hq40 hq
  have hfinrank :
      Module.finrank (ZMod 2) (Word (ZMod 2) (CheckOrbit401 q)) <
        Module.finrank (ZMod 2) (Word (ZMod 2) (EdgeOrbit401 q hq)) := by
    simpa [finrank_word_eq_length, Length] using
      card_checkOrbit_lt_card_edgeOrbit q hq40 hq
  have hker : LinearMap.ker (HorizontalSubsystem.quotientBoundary A) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hker with ⟨x, hx, hx0⟩
  refine ⟨x, ?_, hx0⟩
  rw [(HorizontalSubsystem.quotientTannerComplex A).mem_middleCycleCode_iff]
  exact hx

theorem exists_quotientTanner_minimumDistance
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    ∃ d : ℕ, MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode d := by
  apply exists_minimumDistance_of_exists_nonzero
  exact quotientTanner_middleCycleCode_exists_nonzero q hq40 hq

/-- Concrete finite-code dressed-distance bounds.  The cardinal lower bounds
only select sufficiently large family members; `hLPS` remains the sole
mathematical input about the LPS graphs. -/
theorem lpsHorizontalSubsystem_dressedDistanceBounds
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq804 : 804 ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq))
    (hCheckOrbitLarge : 10000000 ≤ Fintype.card (CheckOrbit401 q)) :
    let hOdd : Odd q :=
      (Fact.out : q.Prime).odd_of_ne_two (by omega)
    let D := HorizontalSubsystem.horizontalSubsystem
      (lpsTannerGroupAlgebraMatrix q hq40 hq)
      (Cyclic.cyclicGenerator q)
      (by simpa [CyclicGroup, ZMod.card] using hOdd)
    D.DressedZDistanceAtLeast (lpsDressedZLowerBound q hq) ∧
      D.DressedXDistanceAtLeast (lpsDressedXLowerBound q) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  dsimp only
  let A := lpsTannerGroupAlgebraMatrix q hq40 hq
  let dZ := lpsPrimalQuotientDistanceScale q hq
  let dX := lpsDualQuotientDistanceScale q
  have hOdd : Odd q := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  have hdZPositive : 0 < dZ := by
    exact Nat.div_pos hEdgeOrbitLarge (by norm_num)
  have hdXPositive : 0 < dX := by
    exact Nat.div_pos hCheckOrbitLarge (by norm_num)
  have hPrimalExpansion : (tannerAction A).SmallSetExpanding
      (q * dZ) 44 41123 := by
    exact lpsTannerAction_boundary_expansion_at_quotientScale q hq40 hq hLPS
  have hDualExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dX) 11 102500 := by
    exact lpsTannerAction_coboundary_expansion_at_quotientScale q hq40 hq hLPS
  constructor
  · obtain ⟨actualDistance, hMinimum⟩ :=
      exists_quotientTanner_minimumDistance q hq40 hq
    have hDistanceLower : dZ ≤ actualDistance := by
      exact quotientTanner_minimumDistance_lowerBound q hq40 hq hLPS hMinimum
    apply PKDistance.horizontalSubsystem_dressedZDistanceAtLeast_of_caseOne_distanceLowerBound
      q hOdd A hMinimum hDistanceLower hdZPositive 44 41123 hPrimalExpansion
    change 164492 * ((q * dZ) / 3739) ≤ 44 * (q * dZ)
    calc
      164492 * ((q * dZ) / 3739) ≤
          (44 * 3739) * ((q * dZ) / 3739) := by
        exact Nat.mul_le_mul_right _ (by norm_num)
      _ = 44 * (3739 * ((q * dZ) / 3739)) := by ring
      _ ≤ 44 * (q * dZ) :=
        Nat.mul_le_mul_left 44 (Nat.mul_div_le _ _)
  · apply PKDistance.horizontalSubsystem_dressedXDistanceAtLeast_of_expansion
      q (by omega) hOdd A hdXPositive 402 (q / 804) (q * dX) 11 102500
        (by norm_num) (by norm_num)
    · exact Nat.div_pos hq804 (by norm_num)
    · simpa using (Nat.mul_div_le q 804)
    · exact lpsTannerAction_starTranspose_basis_weight_le q hq40 hq
    · have hdXOne : 1 ≤ dX := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdXPositive)
      calc
        q / 804 ≤ q := Nat.div_le_self _ _
        _ = q * 1 := by omega
        _ ≤ q * dX := Nat.mul_le_mul_left q hdXOne
    · exact hDualExpansion
    · exact hDualExpansion
    · change 410000 *
          (min (q * dX) (q / 804) / 37273) ≤
        11 * min (q * dX) (q / 804)
      calc
        410000 * (min (q * dX) (q / 804) / 37273) ≤
            (11 * 37273) * (min (q * dX) (q / 804) / 37273) := by
          exact Nat.mul_le_mul_right _ (by norm_num)
        _ = 11 * (37273 *
            (min (q * dX) (q / 804) / 37273)) := by ring
        _ ≤ 11 * min (q * dX) (q / 804) :=
          Nat.mul_le_mul_left 11 (Nat.mul_div_le _ _)

end QEC.Coding.BalancedProduct.LPSQuotientTanner
