import QEC.Coding.ExpanderCodes.LPSOriginalSecondIntegerHecke
import QEC.Coding.ExpanderCodes.LPSOriginalSpecialFibreFrobenius

/-!
# Finite original special-fibre Hecke correspondence

Base change the proved original integral Fricke involution and both integer
level maps to characteristic l. The lift square is cartesian, so finiteness
is transported from the actual integer maps. Pair the two maps into the
fibre product of the target curve over Spec F_l; properness of that curve
and the finite first map prove that the actual pair is finite. Absolute
l-power Frobenius is natural for the actual second map.

Internal derived geometric prerequisite of the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (484–486) and th:qLDPC (231–238).
No special-fibre component degree, normalization multiplicity, Frobenius plus
Verschiebung cycle identity, complete good reduction, Weil bound, principal
full-level representation spectrum or exact quantum family is claimed.
Parent issue449 remains OPEN and pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

/-- Actual base change of a proved integer-model morphism. -/
def lpsOriginalSpecialFibreLift (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    lpsOriginalSpecialFibre l M hM ⟶ lpsOriginalSpecialFibre l N hN :=
  pullback.lift
    (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM)
      (lpsOriginalPrimeSpecToInteger l) ≫ a)
    (lpsOriginalSpecialFibreToPrimeField l M hM)
    (by
      rw [Category.assoc, ha]
      exact pullback.condition)

lemma lpsOriginalSpecialFibreLift_fst (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    lpsOriginalSpecialFibreLift l N M hN hM a ha ≫
      pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger l) =
    pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l) ≫ a :=
  pullback.lift_fst _ _ _

lemma lpsOriginalSpecialFibreLift_overPrimeField (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    lpsOriginalSpecialFibreLift l N M hN hM a ha ≫
      lpsOriginalSpecialFibreToPrimeField l N hN =
    lpsOriginalSpecialFibreToPrimeField l M hM :=
  pullback.lift_snd _ _ _

lemma lpsOriginalSpecialFibreLift_isPullback (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) :
    IsPullback (lpsOriginalSpecialFibreLift l N M hN hM a ha)
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l))
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger l)) a := by
  have outer : IsPullback
      (lpsOriginalSpecialFibreLift l N M hN hM a ha ≫ lpsOriginalSpecialFibreToPrimeField l N hN)
      (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ M hM) (lpsOriginalPrimeSpecToInteger l))
      (lpsOriginalPrimeSpecToInteger l) (a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
    rw [lpsOriginalSpecialFibreLift_overPrimeField, ha]
    exact (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ M hM)
      (lpsOriginalPrimeSpecToInteger l)).flip
  exact outer.of_right (lpsOriginalSpecialFibreLift_fst l N M hN hM a ha)
    (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (lpsOriginalPrimeSpecToInteger l)).flip

lemma lpsOriginalSpecialFibreLift_finite (l N M : ℕ) [Fact l.Prime]
    (hN : 0 < N) (hM : 0 < M)
    (a : lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN)
    (ha : a ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ M hM) (hf : IsFinite a) :
    IsFinite (lpsOriginalSpecialFibreLift l N M hN hM a ha) :=
  (inferInstance : MorphismProperty.IsStableUnderBaseChange @IsFinite).of_isPullback
    (lpsOriginalSpecialFibreLift_isPullback l N M hN hM a ha).flip hf

def lpsOriginalSpecialFibreFricke (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibre l N hN ⟶ lpsOriginalSpecialFibre l N hN :=
  lpsOriginalSpecialFibreLift l N N hN hN (lpsOriginalIntegerNormalGluedFricke N hN)
    (lpsOriginalIntegerNormalGluedFricke_overSpecZ N hN)

lemma lpsOriginalSpecialFibreFricke_overPrimeField
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibreFricke l N hN ≫ lpsOriginalSpecialFibreToPrimeField l N hN =
      lpsOriginalSpecialFibreToPrimeField l N hN :=
  lpsOriginalSpecialFibreLift_overPrimeField _ _ _ _ _ _ _

lemma lpsOriginalSpecialFibreFricke_involutive
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibreFricke l N hN ≫ lpsOriginalSpecialFibreFricke l N hN =
      𝟙 (lpsOriginalSpecialFibre l N hN) := by
  apply pullback.hom_ext
  · simp only [lpsOriginalSpecialFibreFricke,Category.assoc,lpsOriginalSpecialFibreLift_fst]
    rw [← Category.assoc,lpsOriginalSpecialFibreLift_fst,Category.assoc,
      lpsOriginalIntegerNormalGluedFricke_involutive,Category.comp_id,Category.id_comp]
  · change (lpsOriginalSpecialFibreFricke l N hN ≫ lpsOriginalSpecialFibreFricke l N hN) ≫
      lpsOriginalSpecialFibreToPrimeField l N hN = lpsOriginalSpecialFibreToPrimeField l N hN
    rw [Category.assoc,lpsOriginalSpecialFibreFricke_overPrimeField,
      lpsOriginalSpecialFibreFricke_overPrimeField]

def lpsOriginalSpecialFibreFrickeIso
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    lpsOriginalSpecialFibre l N hN ≅ lpsOriginalSpecialFibre l N hN where
  hom := lpsOriginalSpecialFibreFricke l N hN
  inv := lpsOriginalSpecialFibreFricke l N hN
  hom_inv_id := lpsOriginalSpecialFibreFricke_involutive l N hN
  inv_hom_id := lpsOriginalSpecialFibreFricke_involutive l N hN

def lpsOriginalSpecialFibreForgetLevel
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibre l M hM ⟶ lpsOriginalSpecialFibre l N hN :=
  lpsOriginalSpecialFibreLift l N M hN hM
    (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ N M hNM h4N hN hM)

lemma lpsOriginalSpecialFibreForgetLevel_finite
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM) :=
  lpsOriginalSpecialFibreLift_finite _ _ _ _ _ _ _
    (lpsOriginalIntegerNormalGluedForgetLevel_finite N M hNM h4N hN hM)

lemma lpsOriginalSpecialFibreForgetLevel_overPrimeField
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreToPrimeField l N hN = lpsOriginalSpecialFibreToPrimeField l M hM :=
  lpsOriginalSpecialFibreLift_overPrimeField _ _ _ _ _ _ _

def lpsOriginalSpecialFibreSecondLevelMap
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibre l M hM ⟶ lpsOriginalSpecialFibre l N hN :=
  lpsOriginalSpecialFibreLift l N M hN hM
    (lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalGluedSecondLevelMap_overSpecZ N M hNM h4N hN hM)

lemma lpsOriginalSpecialFibreSecondLevelMap_finite
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM) :=
  lpsOriginalSpecialFibreLift_finite _ _ _ _ _ _ _
    (lpsOriginalIntegerNormalGluedSecondLevelMap_finite N M hNM h4N hN hM)

lemma lpsOriginalSpecialFibreSecondLevelMap_overPrimeField
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreToPrimeField l N hN = lpsOriginalSpecialFibreToPrimeField l M hM :=
  lpsOriginalSpecialFibreLift_overPrimeField _ _ _ _ _ _ _

lemma lpsOriginalSpecialFibreToPrimeField_proper
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    IsProper (lpsOriginalSpecialFibreToPrimeField l N hN) :=
  IsProper.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (lpsOriginalPrimeSpecToInteger l)) (lpsOriginalIntegerNormalGluedToSpecZ_proper N hN)

/-- Actual special-fibre correspondence source to the fibre product of target curves. -/
def lpsOriginalSpecialFibreHeckePair
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibre l M hM ⟶
      pullback (lpsOriginalSpecialFibreToPrimeField l N hN)
        (lpsOriginalSpecialFibreToPrimeField l N hN) :=
  pullback.lift (lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM)
    (lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM)
    ((lpsOriginalSpecialFibreForgetLevel_overPrimeField l N M hNM h4N hN hM).trans
      (lpsOriginalSpecialFibreSecondLevelMap_overPrimeField l N M hNM h4N hN hM).symm)

lemma lpsOriginalSpecialFibreHeckePair_fst
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.fst
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN) =
    lpsOriginalSpecialFibreForgetLevel l N M hNM h4N hN hM :=
  pullback.lift_fst _ _ _

lemma lpsOriginalSpecialFibreHeckePair_snd
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.snd
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN) =
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM :=
  pullback.lift_snd _ _ _

lemma lpsOriginalSpecialFibreHeckePair_finite
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM) := by
  let : IsProper (lpsOriginalSpecialFibreToPrimeField l N hN) :=
    lpsOriginalSpecialFibreToPrimeField_proper l N hN
  let : IsFinite (lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM ≫ pullback.fst
      (lpsOriginalSpecialFibreToPrimeField l N hN) (lpsOriginalSpecialFibreToPrimeField l N hN)) := by
    rw [lpsOriginalSpecialFibreHeckePair_fst]
    exact lpsOriginalSpecialFibreForgetLevel_finite l N M hNM h4N hN hM
  exact IsFinite.of_comp (lpsOriginalSpecialFibreHeckePair l N M hNM h4N hN hM)
    (pullback.fst (lpsOriginalSpecialFibreToPrimeField l N hN)
      (lpsOriginalSpecialFibreToPrimeField l N hN))

lemma lpsOriginalSpecialFibreSecondLevelMap_frobenius_natural
    (l N M : ℕ) [Fact l.Prime] [NeZero N] [NeZero M]
    (hNM : N ∣ M) (h4N : 4 ∣ N) (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalSpecialFibreFrobenius l M hM ≫
      lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM =
    lpsOriginalSpecialFibreSecondLevelMap l N M hNM h4N hN hM ≫
      lpsOriginalSpecialFibreFrobenius l N hN :=
  absoluteFrobenius_natural l _ _ _ _

end
end QEC.Coding.TannerLiftedProduct
