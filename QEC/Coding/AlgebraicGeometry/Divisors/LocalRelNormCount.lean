import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace QEC.Coding.AlgebraicGeometry.LocalRelNormCount

open UniqueFactorizationMonoid

variable (R S : Type*)
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
variable [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- The exponent at the lower prime determined by the actual relative ideal
norm of an upper prime.  Existence follows from ideal norm support, not from a
specified residue-degree equality. -/
noncomputable def primeRelNormExponent (P : Ideal S) (p : Ideal R)
    [P.LiesOver p] [p.IsPrime] : Nat :=
  Nat.find (Ideal.exists_relNorm_eq_pow_of_isPrime P p)

/-- The constructed exponent has its defining relative-norm equality. -/
theorem relNorm_eq_pow_primeRelNormExponent (P : Ideal S) (p : Ideal R)
    [P.LiesOver p] [p.IsPrime] :
    Ideal.relNorm R P = p ^ primeRelNormExponent R S P p :=
  Nat.find_spec (Ideal.exists_relNorm_eq_pow_of_isPrime P p)

/-- The local exponent is exactly the normalized-factor coefficient of the
actual relative ideal norm at the lower prime.  This reduces the desired
principal norm count formula to identifying this existing exponent with the
actual inertia degree. -/
theorem count_normalizedFactors_relNorm_eq_primeRelNormExponent
    (P : Ideal S) (p : Ideal R) (hp0 : p ≠ ⊥)
    [P.LiesOver p] [p.IsPrime] :
    Multiset.count p (normalizedFactors (Ideal.relNorm R P)) =
      primeRelNormExponent R S P p := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  rw [relNorm_eq_pow_primeRelNormExponent R S P p,
    normalizedFactors_of_irreducible_pow hp.irreducible, normalize_eq,
    Multiset.count_replicate, if_pos rfl]

/-- Direct-chart shape of the missing last step.  Here `e` is the constructed
coefficient above, and the intended equality is `e = p.inertiaDeg' P`; proving
that equality requires the separable local determinant/length argument in the
companion dossier. -/
theorem relNorm_prime_count_boundary
    (P : Ideal S) (p : Ideal R) (hp0 : p ≠ ⊥)
    [P.LiesOver p] [p.IsPrime] :
    Multiset.count p (normalizedFactors (Ideal.relNorm R P)) =
      primeRelNormExponent R S P p :=
  count_normalizedFactors_relNorm_eq_primeRelNormExponent R S P p hp0

end QEC.Coding.AlgebraicGeometry.LocalRelNormCount
