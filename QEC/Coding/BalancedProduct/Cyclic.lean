import QEC.Coding.ExpanderCodes.LiftedProduct

/-!
# The cyclic factor in the BE20 balanced product

The balanced product used by Breuckmann--Eberhardt is the lifted product of an
equivariant Tanner boundary with the length-`q` cycle boundary `1 + x`.  This
module constructs that second boundary as an actual group-algebra element and
feeds it into the existing lifted-product chain complex.
-/

namespace QEC.Coding.BalancedProduct.Cyclic

universe u v

/-- The multiplicative type tag on the additive cyclic group `Z/qZ`. -/
abbrev CyclicGroup (q : Nat) := Multiplicative (ZMod q)

/-- The distinguished additive-one generator, viewed multiplicatively. -/
def cyclicGenerator (q : Nat) : CyclicGroup q :=
  Multiplicative.ofAdd (1 : ZMod q)

/-- Canonical enumeration of the cyclic balancing group by residues
`0,…,q-1`. -/
def finCyclicEquiv (q : Nat) [NeZero q] : Fin q ≃ CyclicGroup q where
  toFun k := Multiplicative.ofAdd (ZMod.finEquiv q k)
  invFun g := (ZMod.finEquiv q).symm g.toAdd
  left_inv k := by simp
  right_inv g := by simp

@[simp]
theorem finCyclicEquiv_apply_eq_generator_pow
    (q : Nat) [NeZero q] (k : Fin q) :
    finCyclicEquiv q k = cyclicGenerator q ^ k.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      apply Multiplicative.toAdd.injective
      simp [finCyclicEquiv, cyclicGenerator]
      have hval : (ZMod.finEquiv (q + 1) k).val = k.val := rfl
      rw [← hval, ZMod.natCast_zmod_val]

/-- Canonical enumeration in the opposite cyclic orientation. -/
def finCyclicInvEquiv (q : Nat) [NeZero q] : Fin q ≃ CyclicGroup q :=
  (finCyclicEquiv q).trans (Equiv.inv (CyclicGroup q))

@[simp]
theorem finCyclicInvEquiv_apply_eq_invGenerator_pow
    (q : Nat) [NeZero q] (k : Fin q) :
    finCyclicInvEquiv q k = (cyclicGenerator q)⁻¹ ^ k.val := by
  change (finCyclicEquiv q k)⁻¹ = (cyclicGenerator q)⁻¹ ^ k.val
  rw [finCyclicEquiv_apply_eq_generator_pow]
  exact (inv_pow (cyclicGenerator q) k.val).symm

/-- The binary group-algebra boundary `1 + x` of the cyclic graph. -/
noncomputable def cyclicBoundaryElement {G : Type u} [Group G] (x : G) :
    MonoidAlgebra (ZMod 2) G :=
  MonoidAlgebra.single 1 1 + MonoidAlgebra.single x 1

/-- The support of `1 + x` is contained in its two displayed monomials. -/
theorem cyclicBoundaryElement_support_subset
    {G : Type u} [Group G] [DecidableEq G] (x : G) :
    (cyclicBoundaryElement x).coeff.support ⊆ {1, x} := by
  intro g hg
  rw [cyclicBoundaryElement, MonoidAlgebra.coeff_add,
    MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single] at hg
  rcases Finset.mem_union.mp (Finsupp.support_add hg) with hgOne | hgX
  · have : g ∈ ({1} : Finset G) := Finsupp.support_single_subset hgOne
    simp only [Finset.mem_singleton] at this
    simp [this]
  · have : g ∈ ({x} : Finset G) := Finsupp.support_single_subset hgX
    simp only [Finset.mem_singleton] at this
    simp [this]

theorem cyclicBoundaryElement_support_card_le_two
    {G : Type u} [Group G] [DecidableEq G] (x : G) :
    (cyclicBoundaryElement x).coeff.support.card ≤ 2 := by
  calc
    (cyclicBoundaryElement x).coeff.support.card ≤ ({1, x} : Finset G).card :=
      Finset.card_le_card (cyclicBoundaryElement_support_subset x)
    _ ≤ 2 := by
      simpa using Finset.card_insert_le (1 : G) {x}

/-- Star-conjugating the oriented cyclic boundary reverses its generator. -/
theorem groupConj_cyclicBoundaryElement
    {G : Type u} [Group G] (x : G) :
    LiftedProduct.groupConj (cyclicBoundaryElement x) =
      cyclicBoundaryElement x⁻¹ := by
  classical
  ext g
  have hx : g = x⁻¹ ↔ x = g⁻¹ := by
    constructor
    · intro h
      subst g
      simp
    · intro h
      calc
        g = (g⁻¹)⁻¹ := by simp
        _ = x⁻¹ := by rw [← h]
  rw [LiftedProduct.groupConj_apply]
  unfold cyclicBoundaryElement
  have hadd (a b : MonoidAlgebra (ZMod 2) G) (y : G) :
      (a + b).coeff y = a.coeff y + b.coeff y := rfl
  rw [hadd, hadd]
  change
    (MonoidAlgebra.single 1 1).coeff g⁻¹ + (MonoidAlgebra.single x 1).coeff g⁻¹ =
      (MonoidAlgebra.single 1 1).coeff g + (MonoidAlgebra.single x⁻¹ 1).coeff g
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hOneIff : (1 : G) = g⁻¹ ↔ 1 = g := by
    constructor
    · intro h
      have hg : g = 1 := by
        calc
          g = (g⁻¹)⁻¹ := by simp
          _ = 1 := by rw [← h]; simp
      exact hg.symm
    · intro h
      subst g
      simp
  have hXIff : x = g⁻¹ ↔ x⁻¹ = g := by
    constructor
    · intro h
      exact (hx.mpr h).symm
    · intro h
      exact hx.mp h.symm
  rw [hOneIff, hXIff]

/-- The one-row, one-column group-algebra matrix containing `1 + x`. -/
noncomputable def cyclicBoundaryMatrix {G : Type u} [Group G] (x : G) :
    Matrix Unit Unit (MonoidAlgebra (ZMod 2) G) :=
  fun _ _ => cyclicBoundaryElement x

/-- The star-transpose of the one-column cyclic boundary reverses the chosen
orientation and makes no other change. -/
theorem starTranspose_cyclicBoundaryMatrix
    {G : Type u} [Group G] (x : G) :
    LiftedProduct.starTranspose (cyclicBoundaryMatrix x) =
      cyclicBoundaryMatrix x⁻¹ := by
  funext r c
  cases r
  cases c
  exact groupConj_cyclicBoundaryElement x

/--
Lifted-product data for an equivariant binary boundary `A` and the cyclic
boundary `1 + x`.  No homology, distance, or expansion conclusion is stored in
this definition.
-/
noncomputable def liftedProductData
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    LiftedProduct.Data (ZMod 2) G aRow aCol Unit Unit where
  A := A
  B := cyclicBoundaryMatrix x

@[simp]
theorem liftedProductData_A
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    (liftedProductData A x).A = A := rfl

@[simp]
theorem liftedProductData_B_apply
    {G : Type u} {aRow aCol : Type v} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (r c : Unit) :
    (liftedProductData A x).B r c = cyclicBoundaryElement x := rfl

/-- BE20 cyclic balanced-product data for the canonical generator of `Z/qZ`. -/
noncomputable def data
    {aRow aCol : Type} (q : Nat)
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) (CyclicGroup q))) :
    LiftedProduct.Data (ZMod 2) (CyclicGroup q) aRow aCol Unit Unit :=
  liftedProductData (G := CyclicGroup q) (aRow := aRow) (aCol := aCol)
    A (cyclicGenerator q)

/-- The honest three-term complex underlying the cyclic balanced product. -/
noncomputable abbrev chainComplex
    {aRow aCol : Type} [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) (CyclicGroup q))) :=
  LiftedProduct.chainComplex (data (aRow := aRow) (aCol := aCol) q A)

/-- Exact qubit count before identifying the Tanner-orbit cardinalities. -/
theorem card_qubitIndex
    {aRow aCol : Type} [Fintype aRow] [Fintype aCol]
    (q : Nat) [NeZero q] :
    Fintype.card
        (LiftedProduct.QubitIndex aRow aCol Unit Unit (CyclicGroup q)) =
      q * (Fintype.card aCol + Fintype.card aRow) := by
  rw [LiftedProduct.card_qubitIndex]
  simp [CyclicGroup, ZMod.card]

end QEC.Coding.BalancedProduct.Cyclic
