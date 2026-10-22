import QEC.Semantics.ErrorCorrection.CodeSupport
import QEC.Semantics.ErrorCorrection.QuditSubsystem
/-!
# Finite-qudit two-dimensional commuting-projector models

This module records the finite-dimensional square-lattice and local-projector
data used by the BPT commuting-projector setup.  It constructs the common
fixed code and its full orthogonal projector from the finite projector family.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators

universe u v

/-- A finite rectangular square-lattice patch with open-boundary coordinates. -/
structure BPTSquareLattice where
  rows : Nat
  columns : Nat
  rows_positive : 0 < rows
  columns_positive : 0 < columns

namespace BPTSquareLattice

/-- The finite open-boundary sites of a rectangular square-lattice patch. -/
abbrev Site (L : BPTSquareLattice) : Type := Fin L.rows × Fin L.columns

/-- The number of sites in the finite square-lattice patch. -/
def siteCount (L : BPTSquareLattice) : Nat := Fintype.card L.Site

/--
The open-boundary portion of the coordinate square with lower-left corner
`origin` and side length `width`.
-/
def square (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat) : Finset L.Site :=
  Finset.univ.filter fun site =>
    origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + width ∧
      origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + width

@[simp]
theorem mem_square_iff (L : BPTSquareLattice) (origin : Nat × Nat) (width : Nat)
    (site : L.Site) :
    site ∈ L.square origin width ↔
      origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + width ∧
        origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + width := by
  simp [square]

end BPTSquareLattice

/--
Finite-dimensional qudit data on an open-boundary square lattice, including a
positive uniform bound on the site-wise local dimensions.
-/
structure BPTQuditLattice where
  lattice : BPTSquareLattice
  localDimension : lattice.Site → Nat
  localDimension_positive : ∀ site, 0 < localDimension site
  uniformDimensionBound : Nat
  uniformDimensionBound_positive : 0 < uniformDimensionBound
  localDimension_le_uniform : ∀ site, localDimension site ≤ uniformDimensionBound

namespace BPTQuditLattice

abbrev Site (L : BPTQuditLattice) : Type := L.lattice.Site

/-- The canonical finite-dimensional register for the lattice's actual local dimensions. -/
abbrev Register (L : BPTQuditLattice) : Type :=
  Semantics.Qudit.QuditRegister L.localDimension

/-- Bridge a finite geometric region to the concrete finite-qudit subsystem. -/
def subsystem (L : BPTQuditLattice) (region : Finset L.Site) :
    Semantics.QuditSubsystem L.localDimension where
  selected := region

@[simp]
theorem subsystem_selected (L : BPTQuditLattice) (region : Finset L.Site) :
    (L.subsystem region).selected = region :=
  rfl

@[simp]
theorem mem_subsystem_selected_iff (L : BPTQuditLattice) (region : Finset L.Site)
    (site : L.Site) :
    site ∈ (L.subsystem region).selected ↔ site ∈ region :=
  Iff.rfl

/-- The concrete erasure channel associated with a finite lattice region. -/
noncomputable def erasureChannel (L : BPTQuditLattice) (region : Finset L.Site) :
    Semantics.QuantumChannel L.Register (L.subsystem region).complementSystem :=
  (L.subsystem region).erasureChannelFromRegister

/-- The lattice-region erasure channel is exactly the concrete subsystem channel. -/
theorem erasureChannel_specification (L : BPTQuditLattice) (region : Finset L.Site) :
    L.erasureChannel region = (L.subsystem region).erasureChannelFromRegister :=
  rfl

end BPTQuditLattice

/--
Identity extension respects composition of local operators.  This is the
algebraic local-extension fact used to instantiate projector laws.
-/
theorem localExtension_comp {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι → Nat} (S : Semantics.QuditSubsystem q)
    (A B : Semantics.Operator S.selectedSystem) :
    (S.extendLocalToRegister A).comp (S.extendLocalToRegister B) =
      S.extendLocalToRegister (A.comp B) := by
  unfold Semantics.QuditSubsystem.extendLocalToRegister
  rw [← S.registerFactorization.symm.conjOperator_comp]
  unfold Semantics.QuditSubsystem.extendLocal
  rw [← TensorProduct.map_comp]
  simp

/-- Identity extension commutes with taking finite-dimensional adjoints. -/
theorem localExtension_adjoint {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι → Nat} (S : Semantics.QuditSubsystem q)
    (A : Semantics.Operator S.selectedSystem) :
    LinearMap.adjoint (S.extendLocalToRegister A) =
      S.extendLocalToRegister (LinearMap.adjoint A) := by
  simp [Semantics.QuditSubsystem.extendLocalToRegister,
    Semantics.QuditSubsystem.extendLocal, TensorProduct.adjoint_map]

/--
A finite family of actual commuting local projectors on a canonical qudit
register.  The projector laws are raw model assumptions; the common-code and
full-projector consequences below are derived lemmas.
-/
structure BPTCommutingProjectorModel (L : BPTQuditLattice) (κ : Type v) [Fintype κ] where
  interactionRange : Nat
  interactionRange_positive : 0 < interactionRange
  support : κ → Finset L.Site
  squareOrigin : κ → Nat × Nat
  support_subset_square : ∀ check,
    support check ⊆ L.lattice.square (squareOrigin check) interactionRange
  localProjector : (check : κ) →
    Semantics.Operator (L.subsystem (support check)).selectedSystem
  projector_idempotent : ∀ check,
    ((L.subsystem (support check)).extendLocalToRegister (localProjector check)).comp
        ((L.subsystem (support check)).extendLocalToRegister (localProjector check)) =
      (L.subsystem (support check)).extendLocalToRegister (localProjector check)
  projector_self_adjoint : ∀ check,
    LinearMap.adjoint
        ((L.subsystem (support check)).extendLocalToRegister (localProjector check)) =
      (L.subsystem (support check)).extendLocalToRegister (localProjector check)
  projector_commutes : ∀ check other,
    ((L.subsystem (support check)).extendLocalToRegister (localProjector check)).comp
        ((L.subsystem (support other)).extendLocalToRegister (localProjector other)) =
      ((L.subsystem (support other)).extendLocalToRegister (localProjector other)).comp
        ((L.subsystem (support check)).extendLocalToRegister (localProjector check))

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]

/-- The actual global projector obtained by extending its local operator. -/
noncomputable def projector (M : BPTCommutingProjectorModel L κ) (check : κ) :
    Semantics.Operator L.Register :=
  (L.subsystem (M.support check)).extendLocalToRegister (M.localProjector check)

/-- Each actual projector is explicitly supported on its recorded finite site set. -/
theorem projector_supported_on (M : BPTCommutingProjectorModel L κ) (check : κ) :
    (L.subsystem (M.support check)).OperatorSupportedOnRegister (M.projector check) := by
  exact (L.subsystem (M.support check)).extendLocalToRegister_operatorSupportedOn
    (M.localProjector check)

/-- The recorded square cover applies to the actual projector's recorded support. -/
theorem projector_support_subset_square (M : BPTCommutingProjectorModel L κ) (check : κ) :
    M.support check ⊆ L.lattice.square (M.squareOrigin check) M.interactionRange :=
  M.support_subset_square check

/-- The actual global projectors satisfy their supplied idempotence law. -/
theorem projector_is_idempotent (M : BPTCommutingProjectorModel L κ) (check : κ) :
    (M.projector check).comp (M.projector check) = M.projector check :=
  M.projector_idempotent check

/-- The actual global projectors satisfy their supplied self-adjointness law. -/
theorem projector_adjoint_eq_self (M : BPTCommutingProjectorModel L κ) (check : κ) :
    LinearMap.adjoint (M.projector check) = M.projector check :=
  M.projector_self_adjoint check

/-- Pairwise commutation in the multiplicative operator monoid. -/
theorem projector_commute (M : BPTCommutingProjectorModel L κ) (check other : κ) :
    Commute (M.projector check) (M.projector other) := by
  change (M.projector check).comp (M.projector other) =
    (M.projector other).comp (M.projector check)
  exact M.projector_commutes check other

/-- The finite family is pairwise commuting on every finite subfamily. -/
private theorem projector_pairwise_commute (M : BPTCommutingProjectorModel L κ)
    (checks : Finset κ) :
    (checks : Set κ).Pairwise (Function.onFun Commute M.projector) := by
  intro check _ other _ _
  exact M.projector_commute check other

/-- The source-style finite product of the commuting actual projectors. -/
noncomputable def projectorProduct (M : BPTCommutingProjectorModel L κ) :
    Semantics.Operator L.Register :=
  Finset.univ.noncommProd M.projector (M.projector_pairwise_commute Finset.univ)

/-- A common fixed vector is fixed by the finite projector product. -/
private theorem projectorProduct_apply_eq_self_of_fixed
    (M : BPTCommutingProjectorModel L κ) (vector : L.Register)
    (hfixed : ∀ check, M.projector check vector = vector) :
    M.projectorProduct vector = vector := by
  unfold projectorProduct
  refine Finset.noncommProd_induction Finset.univ M.projector
    (M.projector_pairwise_commute Finset.univ) (fun product => product vector = vector) ?_ ?_ ?_
  · intro A B hA hB
    simp only [Module.End.mul_apply, hB, hA]
  · rfl
  · intro check _
    exact hfixed check

/-- Multiplying the finite product by any included projector changes nothing. -/
private theorem projectorProduct_mul_projector_eq
    (M : BPTCommutingProjectorModel L κ) (check : κ) :
    M.projectorProduct * M.projector check = M.projectorProduct := by
  classical
  let reduced : Semantics.Operator L.Register :=
    (Finset.univ.erase check).noncommProd M.projector
      (M.projector_pairwise_commute (Finset.univ.erase check))
  have hfactor : reduced * M.projector check = M.projectorProduct := by
    simpa [reduced, projectorProduct] using
      (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
        M.projector (M.projector_pairwise_commute Finset.univ))
  calc
    M.projectorProduct * M.projector check =
        (reduced * M.projector check) * M.projector check := by rw [hfactor]
    _ = reduced * (M.projector check * M.projector check) := by rw [mul_assoc]
    _ = reduced * M.projector check := by
      rw [show M.projector check * M.projector check = M.projector check by
        simpa [Module.End.mul_eq_comp] using M.projector_is_idempotent check]
    _ = M.projectorProduct := hfactor

/-- The finite projector product lands in the actual common-fixed subspace. -/
private theorem projectorProduct_is_fixed
    (M : BPTCommutingProjectorModel L κ) (vector : L.Register) (check : κ) :
    M.projector check (M.projectorProduct vector) = M.projectorProduct vector := by
  have hcomm : Commute (M.projector check) M.projectorProduct := by
    unfold projectorProduct
    exact Finset.noncommProd_commute Finset.univ M.projector
      (M.projector_pairwise_commute Finset.univ) (M.projector check)
      (fun other _ => M.projector_commute check other)
  have hright := M.projectorProduct_mul_projector_eq check
  calc
    M.projector check (M.projectorProduct vector) =
        ((M.projector check * M.projectorProduct) vector) := rfl
    _ = ((M.projectorProduct * M.projector check) vector) := by rw [hcomm.eq]
    _ = M.projectorProduct vector := by
      exact congrArg (fun operator => operator vector) hright

/-- The literal common `+1` fixed subspace of the actual projector family. -/
def commonFixedSubmodule (M : BPTCommutingProjectorModel L κ) : Submodule Complex L.Register where
  carrier := {vector | ∀ check, M.projector check vector = vector}
  zero_mem' := by
    intro check
    exact (M.projector check).map_zero
  add_mem' := by
    intro left right hleft hright check
    simp [map_add, hleft check, hright check]
  smul_mem' := by
    intro scalar vector hvector check
    simp [map_smul, hvector check]

/-- The code space is the actual common `+1` eigenspace of the finite family. -/
def codeSpace (M : BPTCommutingProjectorModel L κ) : Semantics.QuantumCode L.Register where
  carrier := M.commonFixedSubmodule

/-- Exact membership specification for the common-fixed code space. -/
theorem mem_codeSpace_iff (M : BPTCommutingProjectorModel L κ) (vector : L.Register) :
    vector ∈ M.codeSpace.carrier ↔ ∀ check, M.projector check vector = vector :=
  Iff.rfl

/-- The full code projector constructed from the actual common-fixed code space. -/
noncomputable def fullCodeProjector (M : BPTCommutingProjectorModel L κ) :
    Semantics.Operator L.Register :=
  M.codeSpace.projector

/-- The constructed full projector fixes exactly the common-fixed code space. -/
theorem fullCodeProjector_fixed_iff (M : BPTCommutingProjectorModel L κ)
    (vector : L.Register) :
    M.fullCodeProjector vector = vector ↔ ∀ check, M.projector check vector = vector := by
  rw [show M.fullCodeProjector = M.codeSpace.projector from rfl,
    M.codeSpace.projector_eq_self_iff_mem]
  exact M.mem_codeSpace_iff vector

/-- The full projector is idempotent because it is the code-space projection. -/
theorem fullCodeProjector_idempotent (M : BPTCommutingProjectorModel L κ) :
    M.fullCodeProjector.comp M.fullCodeProjector = M.fullCodeProjector :=
  M.codeSpace.projector_idempotent

/-- The full projector is self-adjoint because it is the code-space projection. -/
theorem fullCodeProjector_adjoint_eq_self (M : BPTCommutingProjectorModel L κ) :
    LinearMap.adjoint M.fullCodeProjector = M.fullCodeProjector :=
  M.codeSpace.projector_adjoint_eq_self

/-- Finite products of the commuting self-adjoint projectors are self-adjoint. -/
private theorem projectorProductOn_adjoint_eq_self (M : BPTCommutingProjectorModel L κ)
    (checks : Finset κ)
    (hcomm : (checks : Set κ).Pairwise (Function.onFun Commute M.projector)) :
    LinearMap.adjoint (checks.noncommProd M.projector hcomm) =
      checks.noncommProd M.projector hcomm := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set κ).Pairwise (Function.onFun Commute M.projector) :=
        hcomm.mono (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector hcomm =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector hcomm hnotmem]
      have hcommRest : Commute (M.projector check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute checks M.projector hrest (M.projector check)
          (fun other _ => M.projector_commute check other)
      calc
        LinearMap.adjoint ((insert check checks).noncommProd M.projector hcomm) =
            LinearMap.adjoint (M.projector check * productRest) := by rw [hfactor]
        _ = LinearMap.adjoint productRest * LinearMap.adjoint (M.projector check) := by
          rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]
        _ = productRest * M.projector check := by
          rw [show LinearMap.adjoint productRest = productRest by
            dsimp [productRest]
            exact induction hrest, M.projector_adjoint_eq_self]
        _ = M.projector check * productRest := hcommRest.eq.symm
        _ = (insert check checks).noncommProd M.projector hcomm := hfactor.symm

/-- The source-style finite product is self-adjoint. -/
theorem projectorProduct_adjoint_eq_self (M : BPTCommutingProjectorModel L κ) :
    LinearMap.adjoint M.projectorProduct = M.projectorProduct :=
  M.projectorProductOn_adjoint_eq_self Finset.univ
    (M.projector_pairwise_commute Finset.univ)

/-- The finite product maps every vector into the common-fixed code space. -/
theorem projectorProduct_mem_codeSpace (M : BPTCommutingProjectorModel L κ)
    (vector : L.Register) : M.projectorProduct vector ∈ M.codeSpace.carrier := by
  exact M.mem_codeSpace_iff (M.projectorProduct vector) |>.2
    (fun check => M.projectorProduct_is_fixed vector check)

/-- The constructed full projector equals the finite product of actual projectors. -/
theorem projectorProduct_eq_fullCodeProjector (M : BPTCommutingProjectorModel L κ) :
    M.projectorProduct = M.fullCodeProjector := by
  have hproduct_after_code :
      M.projectorProduct.comp M.fullCodeProjector = M.fullCodeProjector := by
    apply LinearMap.ext
    intro vector
    change M.projectorProduct (M.fullCodeProjector vector) = M.fullCodeProjector vector
    apply M.projectorProduct_apply_eq_self_of_fixed
    intro check
    have hfixed : M.fullCodeProjector (M.fullCodeProjector vector) =
        M.fullCodeProjector vector :=
      congrArg (fun A : Semantics.Operator L.Register => A vector) M.fullCodeProjector_idempotent
    exact (M.fullCodeProjector_fixed_iff (M.fullCodeProjector vector)).1 hfixed check
  have hcode_after_product :
      M.fullCodeProjector.comp M.projectorProduct = M.projectorProduct := by
    apply LinearMap.ext
    intro vector
    change M.fullCodeProjector (M.projectorProduct vector) = M.projectorProduct vector
    exact M.codeSpace.projector_eq_self_of_mem (M.projectorProduct_mem_codeSpace vector)
  have hcode_after_product_eq_code :
      M.fullCodeProjector.comp M.projectorProduct = M.fullCodeProjector := by
    have hadjoint := congrArg LinearMap.adjoint hproduct_after_code
    simpa [LinearMap.adjoint_comp, M.projectorProduct_adjoint_eq_self,
      M.fullCodeProjector_adjoint_eq_self] using hadjoint
  calc
    M.projectorProduct = M.fullCodeProjector.comp M.projectorProduct := hcode_after_product.symm
    _ = M.fullCodeProjector := hcode_after_product_eq_code

/-- A code-dimension/power-of-two witness identifies a finite encoded-qubit parameter. -/
structure EncodedQubitParameter (M : BPTCommutingProjectorModel L κ) where
  encodedQubits : Nat
  codeDimension_eq_two_pow : M.codeSpace.dimension = 2 ^ encodedQubits

/-- The code-dimension witness supplies the source convention `k = log2(dim C)`. -/
theorem EncodedQubitParameter.encodedQubits_eq_log2
    {M : BPTCommutingProjectorModel L κ} (parameter : EncodedQubitParameter M) :
    Nat.log 2 M.codeSpace.dimension = parameter.encodedQubits := by
  rw [parameter.codeDimension_eq_two_pow]
  exact Nat.log_pow (by omega) parameter.encodedQubits

/-- The encoded-qubit parameter explicitly witnesses a power-of-two code dimension. -/
theorem EncodedQubitParameter.codeDimension_is_power_of_two
    {M : BPTCommutingProjectorModel L κ} (parameter : EncodedQubitParameter M) :
    ∃ k, M.codeSpace.dimension = 2 ^ k :=
  ⟨parameter.encodedQubits, parameter.codeDimension_eq_two_pow⟩

/-- A projector support couples a region to its complement exactly when it meets both. -/
def supportCouples (M : BPTCommutingProjectorModel L κ) (check : κ)
    (region : Finset L.Site) : Prop :=
  ((M.support check) ∩ region).Nonempty ∧ ((M.support check) \ region).Nonempty

/-- The source boundary is the union of supports that couple the region to its complement. -/
noncomputable def boundary (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Finset L.Site :=
  (Finset.univ.filter fun check => M.supportCouples check region).biUnion M.support

/-- The portion of the source boundary that lies inside the region. -/
noncomputable def internalBoundary (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Finset L.Site :=
  M.boundary region ∩ region

/-- The external source boundary, defined only from actual coupled supports. -/
noncomputable def externalBoundary (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Finset L.Site :=
  M.boundary region \ region

/-- Membership in the source boundary has an exact support-coupling witness. -/
theorem mem_boundary_iff (M : BPTCommutingProjectorModel L κ) (region : Finset L.Site)
    (site : L.Site) :
    site ∈ M.boundary region ↔
      ∃ check, M.supportCouples check region ∧ site ∈ M.support check := by
  simp [boundary]

/-- Every coupled support is contained in the source boundary. -/
theorem support_subset_boundary_of_couples (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) (check : κ) (hcouples : M.supportCouples check region) :
    M.support check ⊆ M.boundary region := by
  intro site hsite
  exact M.mem_boundary_iff region site |>.2 ⟨check, hcouples, hsite⟩

/-- Membership in the external boundary is a complement-side support-coupling witness. -/
theorem mem_externalBoundary_iff (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) (site : L.Site) :
    site ∈ M.externalBoundary region ↔
      site ∉ region ∧ ∃ check, M.supportCouples check region ∧ site ∈ M.support check := by
  rw [externalBoundary, Finset.mem_sdiff, M.mem_boundary_iff]
  constructor
  · rintro ⟨⟨check, hcouples, hsite⟩, hnotmem⟩
    exact ⟨hnotmem, check, hcouples, hsite⟩
  · rintro ⟨hnotmem, check, hcouples, hsite⟩
    exact ⟨⟨check, hcouples, hsite⟩, hnotmem⟩

/-- The external boundary lies in the complement of the region by construction. -/
theorem externalBoundary_disjoint_region (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : Disjoint (M.externalBoundary region) region := by
  rw [Finset.disjoint_left]
  intro site hboundary hregion
  exact (Finset.mem_sdiff.mp hboundary).2 hregion

/-- The source boundary splits into its internal and external portions. -/
theorem boundary_eq_internal_union_external (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    M.boundary region = M.internalBoundary region ∪ M.externalBoundary region := by
  ext site
  simp [internalBoundary, externalBoundary]
  tauto

/-- Bridge a model region to its selected finite-qudit subsystem. -/
def regionSubsystem (_M : BPTCommutingProjectorModel L κ) (region : Finset L.Site) :
    Semantics.QuditSubsystem L.localDimension :=
  L.subsystem region

/-- The model-region bridge preserves the exact selected site set. -/
@[simp]
theorem regionSubsystem_selected (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : (M.regionSubsystem region).selected = region :=
  L.subsystem_selected region

/-- The model-region bridge has the expected pointwise membership specification. -/
@[simp]
theorem mem_regionSubsystem_selected_iff (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) (site : L.Site) :
    site ∈ (M.regionSubsystem region).selected ↔ site ∈ region :=
  L.mem_subsystem_selected_iff region site

/-- The concrete erasure channel for a model region. -/
noncomputable def regionErasureChannel (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    Semantics.QuantumChannel L.Register (M.regionSubsystem region).complementSystem :=
  (M.regionSubsystem region).erasureChannelFromRegister

/-- The model-region erasure channel is exactly the selected subsystem channel. -/
theorem regionErasureChannel_specification (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    M.regionErasureChannel region = (M.regionSubsystem region).erasureChannelFromRegister :=
  rfl

end BPTCommutingProjectorModel

end Bounds
end QEC
