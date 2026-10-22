import QEC.Coding.AlgebraicGeometry.Residues.Direct.SimplePoleTraceResidue
import QEC.Coding.AlgebraicGeometry.Residues.Inverse.SimplePoleTraceResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.GlobalResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The global residue theorem for finite function fields

The direct finite fibres and the inverse fibre over infinity exhaust the
actual normalized global places.  Trace--residue compatibility on those
fibres therefore transports the already proved rational global residue
theorem through a finite separable function-field extension.

This module proves only the global residue theorem for differentials having
at most simple poles.  It does not assert duality, a genus or canonical-degree
formula, or Riemann--Roch.
-/

open scoped BigOperators Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry.FunctionFieldGlobalResidue

open UniqueFactorizationMonoid
open FunctionFieldDifferential

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

local instance : Module.Finite (R k) (B k F) :=
  AffinePlace.finite_ringOfIntegers k F

omit [Finite k] in
private theorem algebraMap_baseResidue_eq_quotientResidueEquiv_C
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (c : k) :
    algebraMap k p.asIdeal.ResidueField c =
      Ideal.Factors.quotientResidueEquiv p.asIdeal
        (Ideal.Quotient.mk p.asIdeal (Polynomial.C c)) := by
  rw [Ideal.Factors.quotientResidueEquiv_mk]
  rfl

private theorem directBaseResidueRationalAdicEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (c : k) :
    letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
      GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
    DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
        (algebraMap k p.asIdeal.ResidueField c) =
      algebraMap k (GlobalPlace.rationalAdic p).residueField c := by
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  rw [algebraMap_baseResidue_eq_quotientResidueEquiv_C (k := k),
    DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv,
    GlobalPlace.rationalAdicIdealResidueEquiv_mk]
  change (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing p (Polynomial.C c)) =
    (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.constantsToValuationRing (GlobalPlace.rationalAdic p) c)
  apply congrArg (GlobalPlace.residue (GlobalPlace.rationalAdic p))
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]

private theorem trace_directBaseResidueRationalAdicEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (z : p.asIdeal.ResidueField) :
    letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
      GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
    Algebra.trace k (GlobalPlace.rationalAdic p).residueField
        (DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p z) =
      Algebra.trace k p.asIdeal.ResidueField z := by
  let E := DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  have hcompat : RingHom.comp
      (algebraMap k (GlobalPlace.rationalAdic p).residueField)
      (RingEquiv.refl k).toRingHom =
    RingHom.comp E.toRingHom (algebraMap k p.asIdeal.ResidueField) := by
    apply DFunLike.ext _ _
    intro c
    change algebraMap k (GlobalPlace.rationalAdic p).residueField c =
      E (algebraMap k p.asIdeal.ResidueField c)
    exact (directBaseResidueRationalAdicEquiv_algebraMap
      (k := k) p c).symm
  exact (Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.refl k) E hcompat z).symm

private theorem directFactorBaseResidueMap_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (c : k) :
    DirectFactorTraceResidue.directFactorBaseResidueMap k F p P
        (algebraMap k p.asIdeal.ResidueField c) =
      GlobalPlace.constantsToResidue
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F p P)) c := by
  let upperIdeal : Ideal (B k F) := (P : Ideal (B k F))
  let upper := AffinePlace.globalPlace k F
    (DirectIntegralDifferentialResidue.directFactorPlace k F p P)
  letI : upperIdeal.IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime upperIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal upperIdeal
  letI : Algebra (Localization.AtPrime upperIdeal)
      upperIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra
      (R₀ := Localization.AtPrime upperIdeal) (Localization.AtPrime upperIdeal)
  have hbase :
      algebraMap p.asIdeal.ResidueField upperIdeal.ResidueField
          (algebraMap k p.asIdeal.ResidueField c) =
        algebraMap (B k F) upperIdeal.ResidueField
          (algebraMap (R k) (B k F) (Polynomial.C c)) := by
    rw [algebraMap_baseResidue_eq_quotientResidueEquiv_C (k := k),
      Ideal.Factors.quotientResidueEquiv_mk]
    change algebraMap p.asIdeal.ResidueField upperIdeal.ResidueField
        (IsLocalRing.residue (Localization.AtPrime p.asIdeal)
          (algebraMap (R k) (Localization.AtPrime p.asIdeal)
            (Polynomial.C c))) =
      IsLocalRing.residue (Localization.AtPrime upperIdeal)
        (algebraMap (B k F) (Localization.AtPrime upperIdeal)
          (algebraMap (R k) (B k F) (Polynomial.C c)))
    rw [IsLocalRing.ResidueField.algebraMap_residue
      (R := Localization.AtPrime p.asIdeal)
      (S := Localization.AtPrime upperIdeal)]
    apply congrArg (IsLocalRing.residue (Localization.AtPrime upperIdeal))
    rw [← IsScalarTower.algebraMap_apply (R k)
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime upperIdeal)]
    rw [← IsScalarTower.algebraMap_apply (R k) (B k F)
      (Localization.AtPrime upperIdeal)]
  change DirectFactorResidueTransport.directFactorResidueEquiv k F p P
      (algebraMap p.asIdeal.ResidueField upperIdeal.ResidueField
        (algebraMap k p.asIdeal.ResidueField c)) =
    upper.residue (GlobalPlace.constantsToValuationRing upper c)
  rw [hbase,
    DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap]
  apply congrArg upper.residue
  apply Subtype.ext
  change algebraMap (B k F) F
      (algebraMap (R k) (B k F) (Polynomial.C c)) = algebraMap k F c
  rfl

private theorem trace_directFactorPlaceTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (x : (AffinePlace.globalPlace k F
      (DirectIntegralDifferentialResidue.directFactorPlace k F p P)).residueField) :
    Algebra.trace k p.asIdeal.ResidueField
        (DirectFactorTraceResidue.directFactorPlaceTrace k F p P x) =
      let upper := AffinePlace.globalPlace k F
        (DirectIntegralDifferentialResidue.directFactorPlace k F p P)
      letI : Algebra k upper.residueField := GlobalPlace.residueAlgebra upper
      Algebra.trace k upper.residueField x := by
  let K := p.asIdeal.ResidueField
  let upper := AffinePlace.globalPlace k F
    (DirectIntegralDifferentialResidue.directFactorPlace k F p P)
  letI : Algebra k upper.residueField := GlobalPlace.residueAlgebra upper
  letI : Algebra K upper.residueField :=
    (DirectFactorTraceResidue.directFactorBaseResidueMap k F p P).toAlgebra
  letI : IsScalarTower k K upper.residueField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change GlobalPlace.constantsToResidue upper c =
        DirectFactorTraceResidue.directFactorBaseResidueMap k F p P
          (algebraMap k K c)
      exact (directFactorBaseResidueMap_algebraMap
        (k := k) (F := F) p P c).symm
  letI : Finite upper.residueField := GlobalPlace.finite_residueField upper
  letI : Finite (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.finite_residueField (GlobalPlace.rationalAdic p)
  letI : Finite K := Finite.of_equiv
    (GlobalPlace.rationalAdic p).residueField
    (DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p).toEquiv.symm
  letI : Module.Finite K upper.residueField :=
    (Module.finite_iff_finite).mpr inferInstance
  letI : Module.Finite k K := (Module.finite_iff_finite).mpr inferInstance
  change Algebra.trace k K (Algebra.trace K upper.residueField x) =
    Algebra.trace k upper.residueField x
  exact Algebra.trace_trace x

private theorem
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_directFactors
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (omega : Differential k F)
    (homega : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F p P))) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        ∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Differential.simplePoleTraceResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F
              (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
            omega (homega P) := by
  classical
  obtain ⟨htrace, hresidue⟩ :=
    DirectSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
      (k := k) (F := F) p omega homega
  refine ⟨htrace, ?_⟩
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  change Algebra.trace k (GlobalPlace.rationalAdic p).residueField
      (Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        ⟨functionFieldDifferentialTrace (k := k) (F := F) omega,
          htrace⟩) = _
  rw [hresidue,
    trace_directBaseResidueRationalAdicEquiv (k := k), map_sum]
  apply Finset.sum_congr rfl
  intro P _
  let upper := AffinePlace.globalPlace k F
    (DirectIntegralDifferentialResidue.directFactorPlace k F p P)
  letI : Algebra k upper.residueField := GlobalPlace.residueAlgebra upper
  change Algebra.trace k p.asIdeal.ResidueField
      (DirectFactorTraceResidue.directFactorPlaceTrace k F p P
        (Differential.simplePoleResidue (k := k) (F := F) upper
          ⟨omega, homega P⟩)) =
    Algebra.trace k upper.residueField
      (Differential.simplePoleResidue (k := k) (F := F) upper
        ⟨omega, homega P⟩)
  exact trace_directFactorPlaceTrace (k := k) (F := F) p P _

private noncomputable def directFactorsEquivAffineFibre
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset ≃
      {C : AffinePlace.carrier k F // C.under (R k) = p} := by
  classical
  refine
    { toFun := fun P => ⟨
        DirectIntegralDifferentialResidue.directFactorPlace k F p P, ?_⟩
      invFun := fun C => ⟨C.1.asIdeal, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hP : (P : Ideal (B k F)) ∈
        IsDedekindDomain.primesOverFinset p.asIdeal (B k F) := P.property
    have hover :=
      ((IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (B k F)).mp hP).2
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact hover.over.symm
  · change C.1.asIdeal ∈
      IsDedekindDomain.primesOverFinset p.asIdeal (B k F)
    apply (IsDedekindDomain.mem_primesOverFinset_iff
      p.ne_bot (B k F)).mpr
    refine ⟨C.1.isPrime, ?_⟩
    exact ⟨(congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      C.property).symm⟩
  · intro P
    apply Subtype.ext
    rfl
  · intro C
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rfl

private noncomputable instance directAffineFibreFintype
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    Fintype {C : AffinePlace.carrier k F // C.under (R k) = p} :=
  Fintype.ofEquiv
    ((factors (Ideal.map
      (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (directFactorsEquivAffineFibre (k := k) (F := F) p)

private theorem sum_directFactors_eq_sum_affineFibre
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (g : AffinePlace.carrier k F → k) :
    (∑ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      g (DirectIntegralDifferentialResidue.directFactorPlace k F p P)) =
      ∑ C : {C : AffinePlace.carrier k F // C.under (R k) = p}, g C.1 := by
  let e := directFactorsEquivAffineFibre (k := k) (F := F) p
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem mapDomain_under_apply_eq_sum_affineFibre
    (f : AffinePlace.carrier k F →₀ k)
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    (Finsupp.mapDomain
      (IsDedekindDomain.HeightOneSpectrum.under (R k)) f) p =
      ∑ C : {C : AffinePlace.carrier k F // C.under (R k) = p}, f C.1 := by
  classical
  let pred := fun C : AffinePlace.carrier k F => C.under (R k) = p
  let filtered := f.filter pred
  have hsupport : ∀ C ∈ filtered.support, pred C := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  have hrestrict :
      (filtered.subtypeDomain pred).sum (fun _ value => value) =
        filtered.sum (fun _ value => value) :=
    Finsupp.sum_subtypeDomain_index
      (v := filtered) (p := pred)
      (h := fun (_ : AffinePlace.carrier k F) (value : k) => value)
      hsupport
  obtain ⟨P₀, hP₀max, hP₀over⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := B k F) p.asIdeal
  have hP₀mem : P₀ ∈
      IsDedekindDomain.primesOverFinset p.asIdeal (B k F) :=
    (IsDedekindDomain.mem_primesOverFinset_iff
      p.ne_bot (B k F)).mpr ⟨hP₀max.isPrime, hP₀over⟩
  let factor₀ : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset :=
    ⟨P₀, hP₀mem⟩
  have hfactor₀ :
      (DirectIntegralDifferentialResidue.directFactorPlace k F p factor₀).under
          (R k) = p :=
    (directFactorsEquivAffineFibre (k := k) (F := F) p factor₀).property
  calc
    (Finsupp.mapDomain
        (IsDedekindDomain.HeightOneSpectrum.under (R k)) f) p =
        filtered.sum (fun _ value => value) := by
      calc
        (Finsupp.mapDomain
            (IsDedekindDomain.HeightOneSpectrum.under (R k)) f) p =
            (Finsupp.mapDomain
              (IsDedekindDomain.HeightOneSpectrum.under (R k)) f)
              ((DirectIntegralDifferentialResidue.directFactorPlace
                k F p factor₀).under (R k)) := by rw [hfactor₀]
        _ = ∑ C ∈ f.support with
              C.under (R k) =
                (DirectIntegralDifferentialResidue.directFactorPlace
                  k F p factor₀).under (R k), f C :=
          Finsupp.mapDomain_apply_eq_sum _ _
        _ = filtered.sum (fun _ value => value) := by
          rw [hfactor₀]
          simp only [filtered, Finsupp.sum, Finsupp.support_filter,
            Finsupp.filter_apply, pred]
          apply Finset.sum_congr rfl
          intro C hC
          rw [if_pos (Finset.mem_filter.mp hC).2]
    _ = (filtered.subtypeDomain pred).sum (fun _ value => value) :=
      hrestrict.symm
    _ = ∑ C : {C : AffinePlace.carrier k F // C.under (R k) = p}, f C.1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      apply Finset.sum_congr rfl
      intro C _
      simp only [Finsupp.subtypeDomain_apply, filtered,
        Finsupp.filter_apply, pred, if_pos C.property]

private theorem
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_affineMapDomain
    (omega : Differential k F)
    (homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega)
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        (Finsupp.mapDomain
          (IsDedekindDomain.HeightOneSpectrum.under (R k))
          (GlobalPlace.affineFinsupp (k := k) (F := F)
            (Differential.globalSimplePoleResidue
              (k := k) (F := F) omega homega))) p := by
  classical
  have hfactor : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F p P)) :=
    fun P => homega _
  obtain ⟨htrace, hresidue⟩ :=
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_directFactors
      (k := k) (F := F) p omega hfactor
  refine ⟨htrace, hresidue.trans ?_⟩
  let affineResidues := GlobalPlace.affineFinsupp (k := k) (F := F)
    (Differential.globalSimplePoleResidue
      (k := k) (F := F) omega homega)
  let residueAtAffine : AffinePlace.carrier k F → k := fun C =>
    Differential.simplePoleTraceResidue (k := k) (F := F)
      (AffinePlace.globalPlace k F C) omega (homega _)
  calc
    (∑ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      Differential.simplePoleTraceResidue (k := k) (F := F)
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F p P))
        omega (hfactor P)) =
        ∑ C : {C : AffinePlace.carrier k F // C.under (R k) = p},
          Differential.simplePoleTraceResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F C.1) omega (homega _) :=
      by
        simpa only [residueAtAffine] using
          (sum_directFactors_eq_sum_affineFibre
            (k := k) (F := F) p residueAtAffine)
    _ = ∑ C : {C : AffinePlace.carrier k F // C.under (R k) = p},
        affineResidues C.1 := by
      apply Finset.sum_congr rfl
      intro C _
      rfl
    _ = (Finsupp.mapDomain
        (IsDedekindDomain.HeightOneSpectrum.under (R k))
        affineResidues) p :=
      (mapDomain_under_apply_eq_sum_affineFibre
        (k := k) (F := F) affineResidues p).symm

private theorem
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_infinityFibreSum
    (omega : Differential k F)
    (homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalInfinity k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        (GlobalPlace.infinityFibreFinsupp (k := k) (F := F)
          (Differential.globalSimplePoleResidue
            (k := k) (F := F) omega homega)).sum
          (fun _ residue => residue) := by
  classical
  have hinfinity : ∀ D : InverseAffinePlace.infinityFibre k F,
      omega ∈ Differential.simplePoleDifferentialLattice
        (InverseAffinePlace.infinityFibreGlobalPlace
          (k := k) (F := F) D) :=
    fun D => homega _
  obtain ⟨htrace, hresidue⟩ :=
    InverseSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre
      (k := k) (F := F) omega hinfinity
  refine ⟨htrace, hresidue.trans ?_⟩
  let infinityResidues := GlobalPlace.infinityFibreFinsupp (k := k) (F := F)
    (Differential.globalSimplePoleResidue
      (k := k) (F := F) omega homega)
  calc
    (∑ D : InverseAffinePlace.infinityFibre k F,
      Differential.simplePoleTraceResidue (k := k) (F := F)
        (InverseAffinePlace.infinityFibreGlobalPlace
          (k := k) (F := F) D) omega (hinfinity D)) =
        ∑ D : InverseAffinePlace.infinityFibre k F, infinityResidues D := by
      apply Finset.sum_congr rfl
      intro D _
      rfl
    _ = infinityResidues.sum (fun _ residue => residue) := by
      symm
      exact Finsupp.sum_fintype _ _ (fun _ => rfl)

private theorem functionFieldDifferentialTrace_isGlobalSimplePole
    (omega : Differential k F)
    (homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega) :
    Differential.IsGlobalSimplePole (k := k) (F := RatFunc k)
      (functionFieldDifferentialTrace (k := k) (F := F) omega) := by
  intro P
  obtain ⟨place, rfl⟩ :=
    (GlobalPlace.rationalPlaceEquiv (k := k)).surjective P
  cases place with
  | none =>
      obtain ⟨htrace, _⟩ :=
        functionFieldDifferentialTrace_simplePoleTraceResidue_eq_infinityFibreSum
          (k := k) (F := F) omega homega
      exact htrace
  | some p =>
      obtain ⟨htrace, _⟩ :=
        functionFieldDifferentialTrace_simplePoleTraceResidue_eq_affineMapDomain
          (k := k) (F := F) omega homega p
      exact htrace

private theorem globalSimplePoleResidueSum_eq_traceResidueSum
    (omega : Differential k F)
    (homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega) :
    Differential.globalSimplePoleResidueSum (k := k) (F := F) omega homega =
      Differential.globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        (functionFieldDifferentialTrace (k := k) (F := F) omega)
        (functionFieldDifferentialTrace_isGlobalSimplePole
          (k := k) (F := F) omega homega) := by
  classical
  let traceOmega := functionFieldDifferentialTrace (k := k) (F := F) omega
  let htraceGlobal : Differential.IsGlobalSimplePole
      (k := k) (F := RatFunc k) traceOmega :=
    functionFieldDifferentialTrace_isGlobalSimplePole
      (k := k) (F := F) omega homega
  let sourceResidues := Differential.globalSimplePoleResidue
    (k := k) (F := F) omega homega
  let affineResidues := GlobalPlace.affineFinsupp (k := k) (F := F)
    sourceResidues
  let infinityResidues := GlobalPlace.infinityFibreFinsupp
    (k := k) (F := F) sourceResidues
  let baseAffine := Finsupp.mapDomain
    (IsDedekindDomain.HeightOneSpectrum.under (R k)) affineResidues
  let traceResidues := Differential.globalSimplePoleResidue
    (k := k) (F := RatFunc k) traceOmega htraceGlobal
  let traceByOption := Finsupp.equivMapDomain
    (GlobalPlace.rationalPlaceEquiv (k := k)).symm traceResidues
  have hatAdic (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
      traceByOption (some p) = baseAffine p := by
    obtain ⟨htrace, hresidue⟩ :=
      functionFieldDifferentialTrace_simplePoleTraceResidue_eq_affineMapDomain
        (k := k) (F := F) omega homega p
    change Differential.globalSimplePoleResidue
        (k := k) (F := RatFunc k) traceOmega htraceGlobal
          (GlobalPlace.rationalAdic p) = baseAffine p
    rw [Differential.globalSimplePoleResidue_apply]
    exact hresidue
  have hatInfinity : traceByOption none =
      infinityResidues.sum (fun _ residue => residue) := by
    obtain ⟨htrace, hresidue⟩ :=
      functionFieldDifferentialTrace_simplePoleTraceResidue_eq_infinityFibreSum
        (k := k) (F := F) omega homega
    change Differential.globalSimplePoleResidue
        (k := k) (F := RatFunc k) traceOmega htraceGlobal
          (GlobalPlace.rationalInfinity k) = _
    rw [Differential.globalSimplePoleResidue_apply]
    exact hresidue
  have hsome : traceByOption.some = baseAffine := by
    ext p
    exact hatAdic p
  have hbaseSum :
      baseAffine.sum (fun _ residue => residue) =
        affineResidues.sum (fun _ residue => residue) := by
    exact
      (Finsupp.sum_mapDomain_index_addMonoidHom
        (s := affineResidues)
        (f := IsDedekindDomain.HeightOneSpectrum.under (R k))
        (fun _ => AddMonoidHom.id k))
  have hoptionSum :
      traceByOption.sum (fun _ residue => residue) =
        traceByOption none +
          traceByOption.some.sum (fun _ residue => residue) := by
    exact Finsupp.sum_option_index traceByOption
      (fun _ residue => residue) (fun _ => rfl) (fun _ _ _ => rfl)
  have hsourceSplit :
      sourceResidues.sum (fun _ residue => residue) =
        affineResidues.sum (fun _ residue => residue) +
          infinityResidues.sum (fun _ residue => residue) := by
    exact GlobalPlace.finsupp_sum_eq_affine_add_infinityFibre sourceResidues
  change sourceResidues.sum (fun _ residue => residue) =
    traceResidues.sum (fun _ residue => residue)
  calc
    sourceResidues.sum (fun _ residue => residue) =
        affineResidues.sum (fun _ residue => residue) +
          infinityResidues.sum (fun _ residue => residue) := hsourceSplit
    _ = baseAffine.sum (fun _ residue => residue) +
          infinityResidues.sum (fun _ residue => residue) := by rw [hbaseSum]
    _ = infinityResidues.sum (fun _ residue => residue) +
          baseAffine.sum (fun _ residue => residue) := add_comm _ _
    _ = traceByOption none +
          traceByOption.some.sum (fun _ residue => residue) := by
      rw [hatInfinity, hsome]
    _ = traceByOption.sum (fun _ residue => residue) := hoptionSum.symm
    _ = traceResidues.sum (fun _ residue => residue) := by
      simpa only [traceByOption] using
        (Finsupp.sum_equivMapDomain
          (GlobalPlace.rationalPlaceEquiv (k := k)).symm traceResidues
          (fun _ residue => residue))

end QEC.Coding.AlgebraicGeometry.FunctionFieldGlobalResidue

namespace QEC.Coding.AlgebraicGeometry.Differential

open FunctionFieldDifferential

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

/-- The sum of the traced normalized residues of a global function-field
differential with at most simple poles is zero. -/
theorem globalSimplePoleResidueSum_eq_zero
    (omega : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega) :
    globalSimplePoleResidueSum (k := k) (F := F) omega homega = 0 := by
  let traceOmega := functionFieldDifferentialTrace (k := k) (F := F) omega
  let htraceGlobal : IsGlobalSimplePole
      (k := k) (F := RatFunc k) traceOmega :=
    FunctionFieldGlobalResidue.functionFieldDifferentialTrace_isGlobalSimplePole
      (k := k) (F := F) omega homega
  calc
    globalSimplePoleResidueSum (k := k) (F := F) omega homega =
        globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          traceOmega htraceGlobal := by
      exact
        FunctionFieldGlobalResidue.globalSimplePoleResidueSum_eq_traceResidueSum
          (k := k) (F := F) omega homega
    _ = 0 := by
      let f := functionFieldDifferentialCoordinate
        (k := k) (F := RatFunc k) traceOmega
      have htraceAsScalar : traceOmega =
          f • functionFieldDifferentialGenerator
            (k := k) (F := RatFunc k) :=
        functionFieldDifferential_eq_coordinate_smul_generator
          (k := k) (F := RatFunc k) traceOmega
      by_cases hf : f = 0
      · have htraceZero : traceOmega = 0 := by
          rw [htraceAsScalar, hf, zero_smul]
        simpa only [htraceZero] using
          (globalSimplePoleResidueSum_zero (k := k) (F := RatFunc k))
      · have hscalarGlobal : IsGlobalSimplePole
            (k := k) (F := RatFunc k)
            (f • functionFieldDifferentialGenerator
              (k := k) (F := RatFunc k)) := by
          simpa only [← htraceAsScalar] using htraceGlobal
        simpa only [← htraceAsScalar] using
          (globalSimplePoleResidueSum_ratFunc
            (k := k) f hf hscalarGlobal)

end QEC.Coding.AlgebraicGeometry.Differential
