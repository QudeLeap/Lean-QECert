import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Transport of the different along integral algebra equivalences

These lemmas transport Mathlib's trace-defined different and its prime
multiplicities. They do not assume a local different calculation.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

/-- The fraction-field equivalence induced by an integral algebra equivalence. -/
private noncomputable def fractionRingAlgEquivOfAlgEquiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) :
    FractionRing B ≃ₐ[FractionRing A] FractionRing C :=
  IsFractionRing.fieldEquivOfAlgEquiv
    (FractionRing A) (FractionRing B) (FractionRing C) sigma

/-- The induced fraction-field automorphism preserves the embedded integral
ring. -/
private theorem fractionRingAlgEquivOfAlgEquiv_mem_one_iff
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (x : FractionRing B) :
    fractionRingAlgEquivOfAlgEquiv A B C sigma x ∈
        (1 : Submodule C (FractionRing C)) ↔
      x ∈ (1 : Submodule B (FractionRing B)) := by
  let e := fractionRingAlgEquivOfAlgEquiv A B C sigma
  constructor
  · intro hx
    rw [Submodule.mem_one] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    refine ⟨sigma.symm c, ?_⟩
    exact e.injective (by
      simpa only [e, fractionRingAlgEquivOfAlgEquiv,
        IsFractionRing.fieldEquivOfAlgEquiv_algebraMap,
        AlgEquiv.apply_symm_apply] using hc)
  · intro hx
    rw [Submodule.mem_one] at hx ⊢
    obtain ⟨b, rfl⟩ := hx
    refine ⟨sigma b, ?_⟩
    exact (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap
      (FractionRing A) (FractionRing B) (FractionRing C) sigma b).symm

/-- The trace dual of the integral ring is invariant under every integral
algebra equivalence. -/
private theorem fractionRingAlgEquivOfAlgEquiv_mem_traceDual_one_iff
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (x : FractionRing B) :
    fractionRingAlgEquivOfAlgEquiv A B C sigma x ∈
        Submodule.traceDual A (FractionRing A)
          (1 : Submodule C (FractionRing C)) ↔
      x ∈ Submodule.traceDual A (FractionRing A)
        (1 : Submodule B (FractionRing B)) := by
  let e := fractionRingAlgEquivOfAlgEquiv A B C sigma
  have htrace (u v : FractionRing B) :
      Algebra.traceForm (FractionRing A) (FractionRing C) (e u) (e v) =
        Algebra.traceForm (FractionRing A) (FractionRing B) u v := by
    change Algebra.trace (FractionRing A) (FractionRing C) (e u * e v) =
      Algebra.trace (FractionRing A) (FractionRing B) (u * v)
    rw [← map_mul]
    exact Algebra.trace_eq_of_algEquiv e (u * v)
  constructor
  · intro hx
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    have hea : e a ∈ (1 : Submodule C (FractionRing C)) :=
      (fractionRingAlgEquivOfAlgEquiv_mem_one_iff A B C sigma a).2 ha
    have h := hx (e a) hea
    rwa [htrace] at h
  · intro hx
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    have hpre : e.symm a ∈ (1 : Submodule B (FractionRing B)) := by
      apply (fractionRingAlgEquivOfAlgEquiv_mem_one_iff
        A B C sigma (e.symm a)).1
      simpa only [e, AlgEquiv.apply_symm_apply] using ha
    have h := hx (e.symm a) hpre
    have htrace' :
        Algebra.traceForm (FractionRing A) (FractionRing C) (e x) a =
          Algebra.traceForm (FractionRing A) (FractionRing B) x (e.symm a) := by
      simpa only [e, AlgEquiv.apply_symm_apply] using htrace x (e.symm a)
    rwa [htrace']

/-- Consequently the inverse trace dual, hence the fractional different,
has invariant membership. -/
private theorem fractionRingAlgEquivOfAlgEquiv_mem_inverseTraceDual_iff
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (x : FractionRing B) :
    fractionRingAlgEquivOfAlgEquiv A B C sigma x ∈
        (1 / Submodule.traceDual A (FractionRing A)
          (1 : Submodule C (FractionRing C))) ↔
      x ∈ (1 / Submodule.traceDual A (FractionRing A)
        (1 : Submodule B (FractionRing B))) := by
  let e := fractionRingAlgEquivOfAlgEquiv A B C sigma
  rw [Submodule.mem_div_iff_forall_mul_mem,
    Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro hx a ha
    have hea : e a ∈ Submodule.traceDual A (FractionRing A)
        (1 : Submodule C (FractionRing C)) :=
      (fractionRingAlgEquivOfAlgEquiv_mem_traceDual_one_iff
        A B C sigma a).2 ha
    have hproduct := hx (e a) hea
    apply (fractionRingAlgEquivOfAlgEquiv_mem_one_iff
      A B C sigma (x * a)).1
    simpa only [e, map_mul] using hproduct
  · intro hx a ha
    have hpre : e.symm a ∈ Submodule.traceDual A (FractionRing A)
        (1 : Submodule B (FractionRing B)) := by
      apply (fractionRingAlgEquivOfAlgEquiv_mem_traceDual_one_iff
        A B C sigma (e.symm a)).1
      simpa only [e, AlgEquiv.apply_symm_apply] using ha
    have hproduct := hx (e.symm a) hpre
    apply (fractionRingAlgEquivOfAlgEquiv_mem_one_iff
      A B C sigma (x * e.symm a)).2 at hproduct
    simpa only [e, map_mul, AlgEquiv.apply_symm_apply] using hproduct

/-- The trace-defined different ideal is transported by an algebra
equivalence between integral carriers. -/
theorem differentIdeal_map_algEquiv_eq
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) :
    Ideal.map sigma (differentIdeal A B) = differentIdeal A C := by
  have hmem (x : B) :
      sigma x ∈ differentIdeal A C ↔ x ∈ differentIdeal A B := by
    change algebraMap C (FractionRing C) (sigma x) ∈
          (1 / Submodule.traceDual A (FractionRing A)
            (1 : Submodule C (FractionRing C))) ↔
        algebraMap B (FractionRing B) x ∈
          (1 / Submodule.traceDual A (FractionRing A)
            (1 : Submodule B (FractionRing B)))
    simpa only [fractionRingAlgEquivOfAlgEquiv,
      IsFractionRing.fieldEquivOfAlgEquiv_algebraMap] using
        (fractionRingAlgEquivOfAlgEquiv_mem_inverseTraceDual_iff
          A B C sigma (algebraMap B (FractionRing B) x))
  ext x
  constructor
  · rw [Ideal.mem_map_of_equiv]
    rintro ⟨y, hy, rfl⟩
    exact (hmem y).2 hy
  · intro hx
    rw [Ideal.mem_map_of_equiv]
    refine ⟨sigma.symm x, ?_, sigma.apply_symm_apply x⟩
    exact (hmem (sigma.symm x)).1 (by
      simpa only [sigma.apply_symm_apply] using hx)

/- Triviality of the different is invariant under an algebra equivalence of
the upper integral carriers. -/
theorem differentIdeal_eq_top_of_algEquiv
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (σ : B ≃ₐ[A] C)
    (hC : differentIdeal A C = ⊤) :
    differentIdeal A B = ⊤ := by
  exact (Ideal.map_eq_top_of_bijective
    (I := differentIdeal A B) σ.toRingHom σ.bijective).mp
      ((differentIdeal_map_algEquiv_eq A B C σ).trans hC)

/-- A ring equivalence acts multiplicatively on ideals.  This private
bundling lets multiplicity transport use its ordinary equivalence theorem. -/
private def idealMapRingEquiv
    (B C : Type*) [CommSemiring B] [CommSemiring C]
    (sigma : B ≃+* C) : Ideal B ≃+* Ideal C where
  toFun I := Ideal.map sigma I
  invFun I := Ideal.map sigma.symm I
  map_add' I J := (Ideal.mapHom sigma).map_add I J
  map_mul' I J := Ideal.map_mul sigma I J
  left_inv I := by
    calc
      Ideal.map sigma.symm (Ideal.map sigma I) =
          Ideal.map (sigma.symm.toRingHom.comp sigma.toRingHom) I :=
        I.map_map sigma.toRingHom sigma.symm.toRingHom
      _ = I := by
        rw [sigma.symm_toRingHom_comp_toRingHom, Ideal.map_id]
  right_inv I := by
    calc
      Ideal.map sigma (Ideal.map sigma.symm I) =
          Ideal.map (sigma.toRingHom.comp sigma.symm.toRingHom) I :=
        I.map_map sigma.symm.toRingHom sigma.toRingHom
      _ = I := by
        rw [sigma.toRingHom_comp_symm_toRingHom, Ideal.map_id]

/-- Different multiplicities are preserved by an equivalence of integral algebras. -/
theorem differentIdeal_multiplicity_map_algEquiv_eq
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (P : Ideal B) :
    multiplicity (Ideal.map sigma P) (differentIdeal A C) =
      multiplicity P (differentIdeal A B) := by
  calc
    multiplicity (Ideal.map sigma P) (differentIdeal A C) =
        multiplicity (Ideal.map sigma P)
          (Ideal.map sigma (differentIdeal A B)) := by
      rw [differentIdeal_map_algEquiv_eq A B C sigma]
    _ = multiplicity P (differentIdeal A B) := by
      exact multiplicity_map_eq
        (idealMapRingEquiv B C sigma.toRingEquiv)


end

end QEC.Coding.AlgebraicGeometry
