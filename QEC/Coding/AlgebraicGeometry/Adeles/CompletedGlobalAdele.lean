import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.ValuedField
import QEC.Coding.AlgebraicGeometry.Adeles.Adele

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Completed local fields and the completed global adele ring

For a normalized global place `P`, this file constructs the completion of the
function field at `P`, its valuation ring, and the restricted product of all
local completions.  This is the topological adele ring used by the automorphic
side of the LSV proof chain.

This object is deliberately separate from `GlobalPlace.GlobalAdele`.  The
latter is an `F`-valued algebraic restricted product used by the intrinsic
Riemann--Roch formalization; the object here has a different local field in each
coordinate.

No local compactness, Haar measure, quotient measure, automorphic
decomposition, or spectral conclusion is asserted in this file.
-/

namespace QEC.Coding.AlgebraicGeometry

open Filter
open scoped RestrictedProduct WithZero

noncomputable section

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

/-- The completion of `F` at the normalized valuation represented by `P`. -/
abbrev LocalCompletion (P : GlobalPlace k F) : Type _ :=
  P.valuation.Completion

/-- The canonical embedding of the function field into its completion at `P`. -/
def completionEmbedding (P : GlobalPlace k F) : F →+* P.LocalCompletion :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv P.valuation).symm

@[simp]
theorem completionEmbedding_apply (P : GlobalPlace k F) (f : F) :
    P.completionEmbedding f = (f : P.LocalCompletion) :=
  rfl

/-- The global function field is dense in each of its local completions. -/
theorem denseRange_completionEmbedding (P : GlobalPlace k F) :
    DenseRange P.completionEmbedding :=
  UniformSpace.Completion.denseRange_coe.comp
    (WithVal.equiv P.valuation).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- The canonical map into a local completion loses no global function. -/
theorem completionEmbedding_injective (P : GlobalPlace k F) :
    Function.Injective P.completionEmbedding :=
  P.completionEmbedding.injective

/-- The completed valuation extends the original normalized valuation exactly. -/
@[simp]
theorem valuation_completionEmbedding (P : GlobalPlace k F) (f : F) :
    Valued.v (P.completionEmbedding f) = P.valuation f := by
  rw [completionEmbedding_apply, Valued.valuedCompletion_apply]
  exact WithVal.valued_toVal P.valuation f

/-- The valuation ring inside the local completion at `P`. -/
abbrev LocalIntegerRing (P : GlobalPlace k F) : ValuationSubring P.LocalCompletion :=
  (Valued.v : Valuation P.LocalCompletion ℤᵐ⁰).valuationSubring

/-- Membership in the completed integer ring is the original non-pole bound
on embedded global functions. -/
theorem completionEmbedding_mem_localIntegerRing_iff
    (P : GlobalPlace k F) (f : F) :
    P.completionEmbedding f ∈ P.LocalIntegerRing ↔ f ∈ P.valuationRing := by
  rw [Valuation.mem_valuationSubring_iff, valuation_completionEmbedding,
    mem_valuationRing_iff]

variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

/-- The completed global adele ring: the restricted product of the local
completions with respect to their valuation rings. -/
abbrev CompletedGlobalAdele : Type _ :=
  Πʳ P : GlobalPlace k F, [P.LocalCompletion, P.LocalIntegerRing]

/-- The diagonal embedding of the function field into the completed global
adele ring.  Its well-definedness is the finite-pole theorem already proved
for the intrinsic global-place carrier. -/
def completedDiagonal : F →+* CompletedGlobalAdele (k := k) (F := F) where
  toFun f := ⟨fun P ↦ P.completionEmbedding f, by
    filter_upwards [eventually_mem_valuationRing (k := k) (F := F) f] with P hP
    exact (completionEmbedding_mem_localIntegerRing_iff P f).mpr hP⟩
  map_one' := Subtype.ext <| funext fun P ↦ map_one P.completionEmbedding
  map_mul' f g := Subtype.ext <| funext fun P ↦ map_mul P.completionEmbedding f g
  map_zero' := Subtype.ext <| funext fun P ↦ map_zero P.completionEmbedding
  map_add' f g := Subtype.ext <| funext fun P ↦ map_add P.completionEmbedding f g

@[simp]
theorem completedDiagonal_apply (f : F) (P : GlobalPlace k F) :
    completedDiagonal (k := k) (F := F) f P = P.completionEmbedding f :=
  rfl

/-- The restricted-product topology makes the completed global adeles a
topological ring because every local integer ring is open. -/
instance : IsTopologicalRing (CompletedGlobalAdele (k := k) (F := F)) := by
  letI : Fact (∀ P : GlobalPlace k F,
      IsOpen (P.LocalIntegerRing : Set P.LocalCompletion)) :=
    ⟨fun P ↦ Valued.isOpen_valuationSubring P.LocalCompletion⟩
  infer_instance

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
