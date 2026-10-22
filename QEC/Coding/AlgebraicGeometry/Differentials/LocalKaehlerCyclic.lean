import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module

/-!
# Local Kahler generators and injection

Derivation generation and Nakayama prove actual local cyclicity from ordinary residue, finite-generation and parameter data. A faithful field embedding and nonzero parameter differential then prove injection.

Derived internal PK22 ex:Xpq machinery, pinned main.tex484–486, for parent #449.
This proves actual differential injection and compatible affine preimages.
Genuine global differential sheaf/gluing/GAGA, good reduction, Hecke/Frobenius/Weil
and the exact arbitrary-finite-field public quantum family remain outstanding.
No public node changes status.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [CommRing k] [CommRing V] [Algebra k V]
variable [IsLocalRing V] [Algebra.EssFiniteType k V]

/-- A genuine split residue map and principal maximal ideal generate the finite local Kahler module by the parameter differential, using Nakayama. -/
lemma localKaehler_span_parameter_of_splitResidue
    (e : V →ₐ[k] k) (he : RingHom.ker e = IsLocalRing.maximalIdeal V)
    (pi : V) (hpi : IsLocalRing.maximalIdeal V = Ideal.span {pi}) :
    Submodule.span V {KaehlerDifferential.D k V pi} = ⊤ := by
  let U := Submodule.span V {KaehlerDifferential.D k V pi}
  let m := IsLocalRing.maximalIdeal V
  have hpim : pi ∈ m := by change pi ∈ IsLocalRing.maximalIdeal V; rw [hpi]; exact Ideal.mem_span_singleton_self pi
  have htop : (⊤ : Submodule V (KaehlerDifferential k V)) ≤ U ⊔ m • ⊤ := by
    conv_lhs => rw [← KaehlerDifferential.span_range_derivation]
    apply Submodule.span_le.mpr
    rintro _ ⟨f,rfl⟩
    have hmem : f - algebraMap k V (e f) ∈ m := by
      change f - algebraMap k V (e f) ∈ IsLocalRing.maximalIdeal V
      rw [← he]
      change e (f-algebraMap k V (e f)) = 0
      simp
    change f - algebraMap k V (e f) ∈ IsLocalRing.maximalIdeal V at hmem
    rw [hpi] at hmem
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hmem
    have hf : f = a*pi + algebraMap k V (e f) := (eq_sub_iff_add_eq.mp ha).symm
    rw [hf,map_add,Derivation.leibniz,Derivation.map_algebraMap,add_zero]
    exact (U ⊔ m • ⊤).add_mem
      (Submodule.mem_sup_left (U.smul_mem a (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul hpim (Submodule.mem_top)))
  apply top_le_iff.mp
  exact Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) htop

variable (K : Type*) [Field K] [Algebra k K] [Algebra V K]
variable [IsScalarTower k V K] [SMulCommClass k V K]

/- Actual cyclicity above and the nonzero parameter differential in the
fraction field prove injectivity; actual consumers must derive these ordinary
residue/parameter/embedding/nonzero data, never assume the target injection. -/
/-- Derived cyclicity and a nonzero parameter differential under a faithful field embedding make the actual local differential map injective. -/
lemma localKaehler_map_injective_of_splitResidue
    (e : V →ₐ[k] k) (he : RingHom.ker e = IsLocalRing.maximalIdeal V)
    (pi : V) (hpi : IsLocalRing.maximalIdeal V = Ideal.span {pi})
    (hfaith : Function.Injective (algebraMap V K))
    (hd : KaehlerDifferential.D k K (algebraMap V K pi) ≠ 0) :
    Function.Injective (KaehlerDifferential.map k k V K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro omega homega
  have hspan : omega ∈ Submodule.span V {KaehlerDifferential.D k V pi} := by
    rw [localKaehler_span_parameter_of_splitResidue k V e he pi hpi]
    trivial
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hz : (KaehlerDifferential.map k k V K) (c • KaehlerDifferential.D k V pi) = 0 := by
    rw [hc]
    exact homega
  rw [map_smul,KaehlerDifferential.map_D] at hz
  rw [← IsScalarTower.algebraMap_smul K c] at hz
  have hc0 : c = 0 := hfaith (by
    rw [map_zero]
    exact (smul_eq_zero.mp hz).resolve_right hd)
  rw [← hc,hc0,zero_smul]
  exact Submodule.zero_mem _
end
end QEC.Coding.AlgebraicGeometry
