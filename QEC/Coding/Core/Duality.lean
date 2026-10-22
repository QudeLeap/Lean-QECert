import QEC.Coding.Core.Definitions

/-!
# Finite-coordinate linear-code duality

Double duality and the sum/intersection identities for the nondegenerate
symmetric word pairing. These foundations are independent of CSS protocols.
-/

noncomputable section

namespace QEC.Coding.LinearCode

universe u v

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/-- A linear code is determined by its carrier. -/
theorem eq_of_carrier_eq {C D : LinearCode F ι} (h : C.carrier = D.carrier) : C = D := by
  cases C
  cases D
  cases h
  rfl

/-- Finite-dimensional orthogonal complementation is involutive. -/
theorem dual_dual_carrier_eq (C : LinearCode F ι) : C.dual.dual.carrier = C.carrier := by
  let pairing := LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))
  have hNondegenerate : pairing.Nondegenerate :=
    (wordPairing_nondegenerate (F := F) (ι := ι)).flip
  have hRefl : pairing.IsRefl := by
    intro x y hxy
    change wordPairing y x = 0 at hxy
    change wordPairing x y = 0
    rw [wordPairing_apply, dotProduct_comm]
    exact hxy
  change pairing.orthogonal (pairing.orthogonal C.carrier) = C.carrier
  exact pairing.orthogonal_orthogonal hNondegenerate hRefl C.carrier

/-- The same involution at the code level. -/
theorem dual_dual_eq (C : LinearCode F ι) : C.dual.dual = C :=
  eq_of_carrier_eq (dual_dual_carrier_eq C)

/-- The dual of a sum is the intersection of the duals. -/
theorem dual_sup_carrier_eq (C D : LinearCode F ι) :
    ({ carrier := C.carrier ⊔ D.carrier } : LinearCode F ι).dual.carrier =
      C.dual.carrier ⊓ D.dual.carrier := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    exact ⟨(C.mem_dual x).2 (fun c hc =>
        (mem_dual _ x).1 hx c (Submodule.mem_sup_left hc)),
      (D.mem_dual x).2 (fun d hd =>
        (mem_dual _ x).1 hx d (Submodule.mem_sup_right hd))⟩
  · rintro ⟨hC, hD⟩
    refine (mem_dual _ x).2 ?_
    intro y hy
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, C.orthogonal_of_mem_dual hC hc, D.orthogonal_of_mem_dual hD hd,
      add_zero]

/-- The dual of an intersection is the sum of the duals. -/
theorem dual_inf_carrier_eq (C D : LinearCode F ι) :
    ({ carrier := C.carrier ⊓ D.carrier } : LinearCode F ι).dual.carrier =
      C.dual.carrier ⊔ D.dual.carrier := by
  let S : LinearCode F ι := ⟨C.dual.carrier ⊔ D.dual.carrier⟩
  have hS : S.dual = ({ carrier := C.carrier ⊓ D.carrier } : LinearCode F ι) := by
    apply eq_of_carrier_eq
    change ({ carrier := C.dual.carrier ⊔ D.dual.carrier } : LinearCode F ι).dual.carrier = _
    rw [dual_sup_carrier_eq, dual_dual_carrier_eq, dual_dual_carrier_eq]
  rw [← hS, dual_dual_carrier_eq]

end QEC.Coding.LinearCode
