import QEC.Coding.ExpanderCodes.LPSIntegerThreeSquareCount
import QEC.Coding.ExpanderCodes.LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# First-coordinate congruences and actual LPS return counts

For a prime q not dividing 2*r, a representation of r^2 by the native
trace form has first coordinate a in the two classes a=+r or a=-r modulo
q^2. Its actual norm equation also gives -r<=a<=r. The two bounded integer
classes each contain at most 2*r/q^2+1 values, by an explicit offset and
quotient injection. No root-class cardinality or spectral result is assumed.

Combining the actual first-coordinate image bound with the previously
proved three-square fiber bound gives
card(lpsTraceQuadraticShell q (r^2)) <= 192*(2*r/q^2+1)*K^7
whenever K>0 and r^2<=4*q^2*K^8. The actual finite scaling equivalence
transfers this to the congruence shell. For the native LPSResiduePrime,
q does not divide 2*p^k; the proved factor-two quaternion/closed-word
identity then gives an alternating closed reduced-word count bound
96*(2*p^k/q^2+1)*K^7 at length 2*k.

This is an internally derived, weaker arithmetic prerequisite motivated by
Davidoff--Sarnak--Valette section4.4, printed pages125-128. It supplies no
centered PSL2 eigenvalue multiplicity, optimized Chebyshev estimate,
unconditional spectral gap or Ramanujan theorem. Any spectral amplification
and retuned code construction remain separate proof obligations. The exact
PK22 arbitrary-finite-field, every-rate, explicit unbounded qLDPC family
remains unproved. Parent issue449 stays OPEN; public records and the selected
Gauss/curve route are unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsTraceQuadraticForm_decompose (q : ℕ) (t : LPSQuaternion) :
    lpsTraceQuadraticForm q t = t.a^2+4*(q : ℤ)^2*(t.b^2+t.c^2+t.d^2) := by
  unfold lpsTraceQuadraticForm
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma lpsPrimeSquare_dvd_difference_or_sum (q a r : ℤ) (hq : Prime q)
    (hqr : ¬q ∣ 2*r) (h : q^2 ∣ (a-r)*(a+r)) : q^2 ∣ a-r ∨ q^2 ∣ a+r := by
  by_cases hm : q ∣ a-r
  · have hp : ¬q ∣ a+r := by
      intro hp
      apply hqr
      have hd : q ∣ (a+r)-(a-r) := dvd_sub hp hm
      have he : (a+r)-(a-r)=2*r := by ring
      rw [he] at hd
      exact hd
    exact Or.inl (hq.pow_dvd_of_dvd_mul_right 2 hp h)
  · exact Or.inr (hq.pow_dvd_of_dvd_mul_left 2 hm h)

lemma lpsTraceQuadraticShell_firstCoordinate_congruence (q r : ℕ) (hq : q.Prime)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (t : LPSQuaternion)
    (ht : t ∈ lpsTraceQuadraticShell q (r^2)) :
    (q : ℤ)^2 ∣ t.a-(r : ℤ) ∨ (q : ℤ)^2 ∣ t.a+(r : ℤ) := by
  have hn := (mem_lpsTraceQuadraticShell_iff hq.pos t).mp ht
  rw [lpsTraceQuadraticForm_decompose] at hn
  have hn' : t.a^2+4*(q : ℤ)^2*(t.b^2+t.c^2+t.d^2)=(r : ℤ)^2 := by exact_mod_cast hn
  apply lpsPrimeSquare_dvd_difference_or_sum (q : ℤ) t.a (r : ℤ)
    (Nat.prime_iff_prime_int.mp hq) hqr
  refine ⟨-(4*(t.b^2+t.c^2+t.d^2)), ?_⟩
  linear_combination hn'

lemma lpsTraceQuadraticShell_firstCoordinate_bounds (q r : ℕ) (hq : 0 < q)
    (t : LPSQuaternion) (ht : t ∈ lpsTraceQuadraticShell q (r^2)) :
    -(r : ℤ) ≤ t.a ∧ t.a ≤ (r : ℤ) := by
  have hn := (mem_lpsTraceQuadraticShell_iff hq t).mp ht
  rw [lpsTraceQuadraticForm_decompose] at hn
  have hn' : t.a^2+4*(q : ℤ)^2*(t.b^2+t.c^2+t.d^2)=(r : ℤ)^2 := by exact_mod_cast hn
  have him : 0 ≤ 4*(q : ℤ)^2*(t.b^2+t.c^2+t.d^2) := by positivity
  have hsq : t.a^2 ≤ (r : ℤ)^2 := by linarith
  have hab : |t.a| ≤ (r : ℤ) := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    (by simpa only [sq_abs] using hsq)
  exact abs_le.mp hab

lemma lpsIntegerOffset_toNat_facts (x : ℤ) (r M : ℕ)
    (hb : -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ)) (hd : (M : ℤ) ∣ x+(r : ℤ)) :
    ((x+(r : ℤ)).toNat : ℤ)=x+(r : ℤ) ∧ (x+(r : ℤ)).toNat ≤ 2*r ∧
      M ∣ (x+(r : ℤ)).toNat := by
  have hc : ((x+(r : ℤ)).toNat : ℤ)=x+(r : ℤ) := Int.toNat_of_nonneg (by omega)
  refine ⟨hc, ?_, ?_⟩
  · have hh : ((x+(r : ℤ)).toNat : ℤ) ≤ ((2*r : ℕ) : ℤ) := by rw [hc]; omega
    exact_mod_cast hh
  · have hh : (M : ℤ) ∣ ((x+(r : ℤ)).toNat : ℤ) := by rw [hc]; exact hd
    exact_mod_cast hh

lemma lpsIntegerSet_card_le_negativeRoot_class (s : Finset ℤ) (r M : ℕ)
    (hs : ∀ x ∈ s, -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ) ∧ (M : ℤ) ∣ x+(r : ℤ)) :
    s.card ≤ 2*r/M+1 := by
  classical
  let f : ℤ → ℕ := fun x => (x+(r : ℤ)).toNat/M
  have hmap : Set.MapsTo f (s : Set ℤ) (Finset.range (2*r/M+1) : Set ℕ) := by
    intro x hx
    have hh := hs x hx
    have hf := lpsIntegerOffset_toNat_facts x r M ⟨hh.1,hh.2.1⟩ hh.2.2
    have hq : f x ≤ 2*r/M := Nat.div_le_div_right hf.2.1
    exact Finset.mem_range.mpr (by omega)
  have hi : (s : Set ℤ).InjOn f := by
    intro x hx y hy he
    have hxf := lpsIntegerOffset_toNat_facts x r M ⟨(hs x hx).1,(hs x hx).2.1⟩ (hs x hx).2.2
    have hyf := lpsIntegerOffset_toNat_facts y r M ⟨(hs y hy).1,(hs y hy).2.1⟩ (hs y hy).2.2
    have hxn : (x+(r : ℤ)).toNat/M*M=(x+(r : ℤ)).toNat := Nat.div_mul_cancel hxf.2.2
    have hyn : (y+(r : ℤ)).toNat/M*M=(y+(r : ℤ)).toNat := Nat.div_mul_cancel hyf.2.2
    have hn : (x+(r : ℤ)).toNat=(y+(r : ℤ)).toNat := by
      calc
        _ = f x*M := hxn.symm
        _ = f y*M := by rw [he]
        _ = (y+(r : ℤ)).toNat := hyn
    have hz := congrArg (fun u : ℕ => (u : ℤ)) hn
    rw [hxf.1,hyf.1] at hz
    omega
  simpa using Finset.card_le_card_of_injOn f hmap hi

lemma lpsIntegerSet_card_le_positiveRoot_class (s : Finset ℤ) (r M : ℕ)
    (hs : ∀ x ∈ s, -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ) ∧ (M : ℤ) ∣ x-(r : ℤ)) :
    s.card ≤ 2*r/M+1 := by
  classical
  have he : (s.image (fun x => -x)).card=s.card := Finset.card_image_of_injective s neg_injective
  rw [← he]
  apply lpsIntegerSet_card_le_negativeRoot_class _ r M
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  have hh := hs x hx
  refine ⟨by omega, by omega, ?_⟩
  have hd : (M : ℤ) ∣ -(x-(r : ℤ)) := dvd_neg.mpr hh.2.2
  have he : -(x-(r : ℤ))=-x+(r : ℤ) := by ring
  rw [he] at hd
  exact hd

lemma lpsTraceQuadraticShell_firstCoordinate_image_card_le (q r : ℕ) (hq : q.Prime)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) :
    ((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card ≤ 2*(2*r/q^2+1) := by
  classical
  let s := (lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a
  let sm := s.filter fun x => ((q^2 : ℕ) : ℤ) ∣ x+(r : ℤ)
  let sp := s.filter fun x => ((q^2 : ℕ) : ℤ) ∣ x-(r : ℤ)
  have hsub : s ⊆ sm ∪ sp := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    have hc := lpsTraceQuadraticShell_firstCoordinate_congruence q r hq hqr t ht
    rcases hc with hc | hc
    · apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩, by exact_mod_cast hc⟩)
    · apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩, by exact_mod_cast hc⟩)
  have hm : sm.card ≤ 2*r/q^2+1 := by
    apply lpsIntegerSet_card_le_negativeRoot_class sm r (q^2)
    intro x hx
    obtain ⟨hxS,hxd⟩ := Finset.mem_filter.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxS
    have hb := lpsTraceQuadraticShell_firstCoordinate_bounds q r hq.pos t ht
    exact ⟨hb.1,hb.2,hxd⟩
  have hp : sp.card ≤ 2*r/q^2+1 := by
    apply lpsIntegerSet_card_le_positiveRoot_class sp r (q^2)
    intro x hx
    obtain ⟨hxS,hxd⟩ := Finset.mem_filter.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hxS
    have hb := lpsTraceQuadraticShell_firstCoordinate_bounds q r hq.pos t ht
    exact ⟨hb.1,hb.2,hxd⟩
  calc
    s.card ≤ (sm ∪ sp).card := Finset.card_le_card hsub
    _ ≤ sm.card+sp.card := Finset.card_union_le _ _
    _ ≤ 2*(2*r/q^2+1) := by omega

lemma card_lpsTraceQuadraticShell_square_le (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^8) :
    (lpsTraceQuadraticShell q (r^2)).card ≤ 192*(2*r/q^2+1)*K^7 := by
  classical
  have hf := Finset.card_le_mul_card_image (lpsTraceQuadraticShell q (r^2)) (96*K^7)
    (fun x _ => card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh q (r^2) K hq.pos hK hcap x)
  have hi := lpsTraceQuadraticShell_firstCoordinate_image_card_le q r hq hqr
  calc
    _ ≤ (96*K^7)*((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card := hf
    _ ≤ (96*K^7)*(2*(2*r/q^2+1)) := Nat.mul_le_mul_left _ hi
    _ = 192*(2*r/q^2+1)*K^7 := by ring

lemma card_lpsTraceCongruenceShell_square_le (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^8) :
    (lpsTraceCongruenceShell q (r^2)).card ≤ 192*(2*r/q^2+1)*K^7 := by
  have hr : 0 < r := by
    by_contra h
    have hr0 : r=0 := by omega
    apply hqr
    simp [hr0]
  rw [← card_lpsTraceQuadraticShell_eq_congruenceShell hq.pos (pow_pos hr 2)]
  exact card_lpsTraceQuadraticShell_square_le q r K hq hK hqr hcap

lemma lpsResiduePrime_not_dvd_twice_degree_pow {p : ℕ} (a : LPSResiduePrime p) (k : ℕ) :
    ¬(a.q : ℤ) ∣ 2*((p : ℤ)^k) := by
  intro hd
  have hdNat : a.q ∣ 2*p^k := by exact_mod_cast hd
  rcases a.prime.dvd_mul.mp hdNat with htwo | hpow
  · exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2)
      (by have hp := a.degreePrime.two_le; have hlarge := a.large; omega) htwo
  · exact Nat.not_dvd_of_pos_of_lt a.degreePrime.pos
      (by have hp := a.degreePrime.pos; have hlarge := a.large; omega)
      (a.prime.dvd_of_dvd_pow hpow)

lemma lpsAlternatingClosedReducedWordCount_even_le {p : ℕ} (a : LPSResiduePrime p)
    (k K : ℕ) (hK : 0 < K) (hcap : p^(2*k) ≤ 4*a.q^2*K^8) :
    lpsAlternatingClosedReducedWordCount a (2*k) ≤ 96*(2*p^k/a.q^2+1)*K^7 := by
  have hq : ¬(a.q : ℤ) ∣ 2*((p^k : ℕ) : ℤ) := by
    exact_mod_cast lpsResiduePrime_not_dvd_twice_degree_pow a k
  have hcap' : (p^k)^2 ≤ 4*a.q^2*K^8 := by simpa only [← pow_mul, Nat.mul_comm k 2] using hcap
  have hb := card_lpsTraceCongruenceShell_square_le a.q (p^k) K a.prime hK hq hcap'
  have hc := card_traceCongruenceShell_eq_two_mul_alternatingClosedCount a (2*k)
  have hn : p^(2*k)=(p^k)^2 := by rw [← pow_mul]; congr 1; omega
  have htwice : 2*lpsAlternatingClosedReducedWordCount a (2*k) ≤ 2*(96*(2*p^k/a.q^2+1)*K^7) := by
    calc
      _ = (lpsTraceCongruenceShell a.q (p^(2*k))).card := hc.symm
      _ = (lpsTraceCongruenceShell a.q ((p^k)^2)).card := by rw [hn]
      _ ≤ 192*(2*p^k/a.q^2+1)*K^7 := hb
      _ = 2*(96*(2*p^k/a.q^2+1)*K^7) := by ring
  exact Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)

end
end QEC.Coding.TannerLiftedProduct
