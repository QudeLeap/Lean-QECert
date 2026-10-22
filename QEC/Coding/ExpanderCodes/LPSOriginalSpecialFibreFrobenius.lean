import QEC.Coding.AlgebraicGeometry.Schemes.AbsoluteFrobenius
import QEC.Coding.ExpanderCodes.LPSOriginalIntegerProperModel

/-!
# Frobenius of the original arithmetic special fibre

Form the actual pullback of the original proper integer normalization over
Spec(ZMod p). Its constructed absolute Frobenius has identity point map,
p-power section/stalk maps, and preserves the prime-field structure. It is
finite by the already proved integer model's properness and genuine base
change, and commutes with the actual base-changed projective j projection.

This internal geometric prerequisite supports the original LPS route behind
pinned PK22 ex:Xpq, main.tex:484-486, and th:qLDPC, main.tex:231-238. It does
not prove smooth/good reduction, Hecke=Frobenius+Verschiebung, a Weil trace
identity, an LPS spectral bound or the final quantum family. No inverse,
good reduction or desired Frobenius property is assumed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0<N)

def lpsOriginalPrimeSpecToInteger : Spec (.of (ZMod p)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p)))

abbrev lpsOriginalSpecialFibre : Scheme :=
  pullback (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p)

def lpsOriginalSpecialFibreToPrimeField : lpsOriginalSpecialFibre p N hN ⟶ Spec (.of (ZMod p)) :=
  pullback.snd (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p)

def lpsOriginalSpecialFibreFrobenius : lpsOriginalSpecialFibre p N hN ⟶ lpsOriginalSpecialFibre p N hN :=
  absoluteFrobenius p _ (lpsOriginalSpecialFibreToPrimeField p N hN)

lemma lpsOriginalSpecialFibreFrobenius_stalk (x : lpsOriginalSpecialFibre p N hN)
    (s : (lpsOriginalSpecialFibre p N hN).presheaf.stalk x) :
    (lpsOriginalSpecialFibreFrobenius p N hN).stalkMap x s = s^p :=
  absoluteFrobenius_stalk_apply p _ (lpsOriginalSpecialFibreToPrimeField p N hN) x s

lemma lpsOriginalSpecialFibreFrobenius_apply (x : lpsOriginalSpecialFibre p N hN) :
    lpsOriginalSpecialFibreFrobenius p N hN x = x :=
  absoluteFrobenius_apply p _ (lpsOriginalSpecialFibreToPrimeField p N hN) x

lemma lpsOriginalSpecialFibreFrobenius_app (U : (lpsOriginalSpecialFibre p N hN).Opens)
    (s : Γ(lpsOriginalSpecialFibre p N hN, U)) :
    (lpsOriginalSpecialFibreFrobenius p N hN).app U s = s^p :=
  absoluteFrobenius_app_apply p _ (lpsOriginalSpecialFibreToPrimeField p N hN) U s

lemma lpsOriginalSpecialFibreFrobenius_overPrimeField :
    lpsOriginalSpecialFibreFrobenius p N hN ≫ lpsOriginalSpecialFibreToPrimeField p N hN =
      lpsOriginalSpecialFibreToPrimeField p N hN :=
  absoluteFrobenius_overPrimeField p _ (lpsOriginalSpecialFibreToPrimeField p N hN)

lemma lpsOriginalSpecialFibreFrobenius_finite [NeZero N] : IsFinite (lpsOriginalSpecialFibreFrobenius p N hN) := by
  let : LocallyOfFiniteType (lpsOriginalSpecialFibreToPrimeField p N hN) := by
    exact _root_.AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ N hN)
        (lpsOriginalPrimeSpecToInteger p))
      (lpsOriginalIntegerNormalGluedToSpecZ_proper N hN).toLocallyOfFiniteType
  exact absoluteFrobenius_finite p _ (lpsOriginalSpecialFibreToPrimeField p N hN)


abbrev lpsOriginalProjectiveJSpecialFibre : Scheme :=
  pullback lpsOriginalIntegerProjectiveJLineToSpecZ (lpsOriginalPrimeSpecToInteger p)

def lpsOriginalProjectiveJSpecialFibreToPrimeField :
    lpsOriginalProjectiveJSpecialFibre p ⟶ Spec (.of (ZMod p)) :=
  pullback.snd lpsOriginalIntegerProjectiveJLineToSpecZ (lpsOriginalPrimeSpecToInteger p)

def lpsOriginalSpecialFibreToProjectiveJ :
    lpsOriginalSpecialFibre p N hN ⟶ lpsOriginalProjectiveJSpecialFibre p :=
  pullback.lift
    (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p) ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
    (lpsOriginalSpecialFibreToPrimeField p N hN)
    (by
      change (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p) ≫
        lpsOriginalIntegerNormalGluedToProjectiveJ N hN) ≫ lpsOriginalIntegerProjectiveJLineToSpecZ =
        pullback.snd (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p) ≫ lpsOriginalPrimeSpecToInteger p
      rw [Category.assoc]
      exact pullback.condition)

lemma lpsOriginalSpecialFibreFrobenius_j_natural :
    lpsOriginalSpecialFibreFrobenius p N hN ≫ lpsOriginalSpecialFibreToProjectiveJ p N hN =
      lpsOriginalSpecialFibreToProjectiveJ p N hN ≫
        absoluteFrobenius p _ (lpsOriginalProjectiveJSpecialFibreToPrimeField p) :=
  absoluteFrobenius_natural p _ (lpsOriginalSpecialFibreToPrimeField p N hN)
    (lpsOriginalSpecialFibreToProjectiveJ p N hN) (lpsOriginalProjectiveJSpecialFibreToPrimeField p)

end
end QEC.Coding.TannerLiftedProduct
