import QEC.Coding.ExpanderCodes.LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases

/-!
# LPSOriginalIntegerQExpansion

Construct actual integer coefficients for the SAME original K(q)=q*j(q).
The true Bernoulli values give E4=1+240A and E6=1-504B for the literal
integer divisor-sum series. Genuine twelve-divisibility of every divisor's
5*d^3+7*d^5 makes (5A+7B)/12 an integer series. The literal polynomial
identity Delta=(5A+7B)/12+100A^2-147B^2+8000A^3 gives actual integer Delta.
Its shifted denominator has constant one; the actual formal unit inverse
constructs integer K. Faithful coefficient maps identify it with the SAME
existing rational K and the SAME analytic Taylor series. The final result
quantifies every coefficient and supplies its actual integer witness.

This does not prove an integer original modular equation, exact minimal
degree, ALL compact meromorphic-field identification, a canonical original
proper arithmetic model, uniform good reduction or Hecke/Frobenius/Weil.
The public PK22 main theorem remains subsequent mathematics. This internal
original-family coefficient bridge is motivated by pinned PK22 ex:Xpq/
th:qLDPC and the audited Milne modular-equation route; no new public source
claim is introduced. No analytic infinite-product identity is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

/-- Actual twelve-divisibility of the cubic/quintic divisor combination, proved by complete modular residues. -/
lemma lpsOriginalSigmaDivisorTwelve (d : ℕ) : 12∣5*d^3+7*d^5 := by
  apply Nat.dvd_of_mod_eq_zero
  simp only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.mod_mod]
  have hd : d%12<12 := Nat.mod_lt d (by decide)
  interval_cases h : d%12 <;> norm_num

/-- Actual twelve-divisibility of the genuine sigma3/sigma5 combination via divisor finite sums. -/
lemma lpsOriginalSigmaCombinationTwelve (n : ℕ) :
    12∣5*ArithmeticFunction.sigma 3 n+7*ArithmeticFunction.sigma 5 n := by
  rw [ArithmeticFunction.sigma_apply,ArithmeticFunction.sigma_apply,
    Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _=>lpsOriginalSigmaDivisorTwelve d

/-- Concrete integer divisor-sum formal series at every natural weight. -/
def lpsOriginalSigmaZSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n=>(ArithmeticFunction.sigma k n:ℤ)

/-- The actual mapped integer divisor-sum series has zero constant coefficient. -/
lemma lpsOriginalSigmaZSeries_constant (k : ℕ) :
    PowerSeries.constantCoeff
      (PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries k))=0 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map]
  simp [lpsOriginalSigmaZSeries,PowerSeries.coeff_mk,ArithmeticFunction.map_zero]

/-- Actual Bernoulli-four evaluation identifies the existing rational E4 series with one plus240 sigma3. -/
lemma lpsOriginalE4QSeries_sigma : lpsOriginalEisensteinQSeries 4=
    1+PowerSeries.C (240:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3) := by
  ext n
  have hB : bernoulli 4= -1/30 := by decide +kernel
  by_cases hn : n=0
  · subst n
    norm_num [lpsOriginalEisensteinQSeries,
      PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,hB]
    simpa only [algebraMap_int_eq] using lpsOriginalSigmaZSeries_constant 3
  · norm_num [lpsOriginalEisensteinQSeries,lpsOriginalSigmaZSeries,
      PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,hn,hB]

/-- Actual Bernoulli-six evaluation identifies the existing rational E6 series with one minus504 sigma5. -/
lemma lpsOriginalE6QSeries_sigma : lpsOriginalEisensteinQSeries 6=
    1-PowerSeries.C (504:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5) := by
  ext n
  have hB : bernoulli 6=1/42 := by decide +kernel
  by_cases hn : n=0
  · subst n
    norm_num [lpsOriginalEisensteinQSeries,
      PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,hB]
    have hz : PowerSeries.constantCoeff
        (PowerSeries.map (Int.castRingHom ℚ) (lpsOriginalSigmaZSeries 5))=0 := by
      simpa only [algebraMap_int_eq] using lpsOriginalSigmaZSeries_constant 5
    rw [hz]
    norm_num
  · norm_num [lpsOriginalEisensteinQSeries,lpsOriginalSigmaZSeries,
      PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,PowerSeries.coeff_map,hn,hB]

/-- Concrete integer combination series using genuine exact natural division by twelve. -/
def lpsOriginalSigmaCombinationZSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n=>((5*ArithmeticFunction.sigma 3 n+7*ArithmeticFunction.sigma 5 n)/12:ℕ)

/-- The faithful rational map of that exact integer combination equals the actual divided sigma combination. -/
lemma lpsOriginalSigmaCombinationZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalSigmaCombinationZSeries=
      PowerSeries.C (12:ℚ)⁻¹*
        (PowerSeries.C (5:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3)+
          PowerSeries.C (7:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5)) := by
  ext n
  simp only [PowerSeries.coeff_map,PowerSeries.coeff_C_mul,map_add,
    lpsOriginalSigmaCombinationZSeries,lpsOriginalSigmaZSeries,PowerSeries.coeff_mk]
  norm_cast
  rw [Nat.cast_div (lpsOriginalSigmaCombinationTwelve n) (by norm_num : (12:ℚ)≠0)]
  push_cast
  ring

/-- Concrete integer Delta series from the literal Eisenstein polynomial identity and divisible combination. -/
def lpsOriginalDeltaZSeries : PowerSeries ℤ :=
  lpsOriginalSigmaCombinationZSeries+
    PowerSeries.C 100*(lpsOriginalSigmaZSeries 3)^2-
    PowerSeries.C 147*(lpsOriginalSigmaZSeries 5)^2+
    PowerSeries.C 8000*(lpsOriginalSigmaZSeries 3)^3

/-- Actual integer Delta maps to the SAME existing rational Delta by genuine ring cancellation. -/
lemma lpsOriginalDeltaZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalDeltaZSeries=lpsOriginalDeltaQSeries := by
  let A := PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3)
  let B := PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5)
  let T := PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalSigmaCombinationZSeries
  have hT : (1728:PowerSeries ℚ)*T=720*A+1008*B := by
    rw [show T=PowerSeries.C (12:ℚ)⁻¹*(PowerSeries.C 5*A+PowerSeries.C 7*B) from
      lpsOriginalSigmaCombinationZSeries_map]
    change PowerSeries.C (1728:ℚ)*(PowerSeries.C (12:ℚ)⁻¹*(PowerSeries.C 5*A+PowerSeries.C 7*B))=_
    rw [←mul_assoc,←map_mul]
    norm_num [map_ofNat]
    ring
  have hden : (1728:PowerSeries ℚ)≠0 := by
    intro h
    have hc:=congrArg (PowerSeries.constantCoeff : PowerSeries ℚ→+*ℚ) h
    norm_num [map_ofNat] at hc
  apply mul_left_cancel₀ hden
  have hr : (1728:PowerSeries ℚ)*lpsOriginalDeltaQSeries=
      (lpsOriginalEisensteinQSeries 4)^3-(lpsOriginalEisensteinQSeries 6)^2 := by
    unfold lpsOriginalDeltaQSeries
    change PowerSeries.C (1728:ℚ)*(PowerSeries.C (1728:ℚ)⁻¹*_) = _
    rw [←mul_assoc,←map_mul]
    norm_num
  rw [hr,lpsOriginalE4QSeries_sigma,lpsOriginalE6QSeries_sigma]
  simp only [lpsOriginalDeltaZSeries,map_add,map_sub,map_mul,map_pow,PowerSeries.map_C]
  change (1728:PowerSeries ℚ)*(T+100*A^2-147*B^2+8000*A^3)=(1+240*A)^3-(1-504*B)^2
  calc
    _=1728*T+172800*A^2-254016*B^2+13824000*A^3 := by ring
    _=(1+240*A)^3-(1-504*B)^2 := by rw [hT];ring

/-- Concrete integer divided-slope series from the actual Delta coefficient shift. -/
def lpsOriginalDeltaSlopeZSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n=>lpsOriginalDeltaZSeries.coeff (n+1)

/-- The actual integer divided slope maps to the SAME existing rational divided slope. -/
lemma lpsOriginalDeltaSlopeZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalDeltaSlopeZSeries=lpsOriginalDeltaSlopeQSeries := by
  ext n
  have h:=congrArg (fun S : PowerSeries ℚ=>S.coeff (n+1)) lpsOriginalDeltaZSeries_map
  simpa only [PowerSeries.coeff_map,PowerSeries.coeff_mk,lpsOriginalDeltaSlopeZSeries,
    lpsOriginalDeltaSlopeQSeries] using h

/-- The actual integer divided slope has constant one through the faithful coefficient map. -/
lemma lpsOriginalDeltaSlopeZSeries_constant :
    PowerSeries.constantCoeff lpsOriginalDeltaSlopeZSeries=1 := by
  have h:=congrArg (fun S : PowerSeries ℚ=>S.coeff 0) lpsOriginalDeltaSlopeZSeries_map
  rw [PowerSeries.coeff_map] at h
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,eq_intCast] at h
  rw [lpsOriginalDeltaSlopeQSeries_constant] at h
  exact_mod_cast h

/-- Concrete integer E4 series with actual divisor coefficients. -/
def lpsOriginalE4ZSeries : PowerSeries ℤ :=
  1+PowerSeries.C 240*lpsOriginalSigmaZSeries 3

/-- The actual integer E4 maps to the SAME existing rational E4. -/
lemma lpsOriginalE4ZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalE4ZSeries=lpsOriginalEisensteinQSeries 4 := by
  rw [lpsOriginalE4QSeries_sigma]
  simp only [lpsOriginalE4ZSeries,map_add,map_one,map_mul,map_ofNat]

/-- Concrete integer K series via the actual constant-one formal unit inverse. -/
def lpsOriginalJZSeries : PowerSeries ℤ :=
  lpsOriginalE4ZSeries^3*PowerSeries.invOfUnit lpsOriginalDeltaSlopeZSeries 1

/-- The actual integer K series maps to the SAME existing rational K by genuine unit cancellation. -/
lemma lpsOriginalJZSeries_mapQ :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalJZSeries=lpsOriginalJQSeries := by
  have hD : lpsOriginalDeltaSlopeQSeries≠0 := by
    intro h
    have h0:=congrArg PowerSeries.constantCoeff h
    rw [lpsOriginalDeltaSlopeQSeries_constant,map_zero] at h0
    exact one_ne_zero h0
  apply mul_left_cancel₀ hD
  have hL : lpsOriginalDeltaSlopeQSeries*
      PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalJZSeries=(lpsOriginalEisensteinQSeries 4)^3 := by
    rw [←lpsOriginalDeltaSlopeZSeries_map,lpsOriginalJZSeries,←map_mul]
    rw [mul_left_comm,PowerSeries.mul_invOfUnit _ 1 lpsOriginalDeltaSlopeZSeries_constant,
      mul_one,map_pow,lpsOriginalE4ZSeries_map]
  have hR : lpsOriginalDeltaSlopeQSeries*lpsOriginalJQSeries=(lpsOriginalEisensteinQSeries 4)^3 := by
    unfold lpsOriginalJQSeries
    rw [mul_left_comm,PowerSeries.mul_invOfUnit _ 1 lpsOriginalDeltaSlopeQSeries_constant,mul_one]
  exact hL.trans hR.symm

/-- The actual integer K series maps to the SAME analytic Taylor series of original K=q-times-j. -/
lemma lpsOriginalJZSeries_mapC :
    PowerSeries.map (algebraMap ℤ ℂ) lpsOriginalJZSeries=
      lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by
  have h:=congrArg (PowerSeries.map (algebraMap ℚ ℂ)) lpsOriginalJZSeries_mapQ
  have hc : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)=algebraMap ℤ ℂ := by
    ext z
    simp
  rw [←RingHom.comp_apply,←PowerSeries.map_comp,hc,lpsOriginalJQSeries_map] at h
  exact h

/-- Every genuine Taylor coefficient of SAME original K is an actual integer cast; no supplied coefficient law. -/
lemma lpsOriginalJQCoefficient_integer (n : ℕ) :
    ∃ a : ℤ,(a:ℂ)=(n.factorial:ℂ)⁻¹*iteratedDeriv n lpsOriginalJQCoefficient 0 := by
  refine ⟨lpsOriginalJZSeries.coeff n,?_⟩
  have h:=congrArg (fun S : PowerSeries ℂ=>S.coeff n) lpsOriginalJZSeries_mapC
  simpa only [PowerSeries.coeff_map,eq_intCast,lpsOriginalTaylorSeries_coeff] using h


end
end QEC.Coding.TannerLiftedProduct
