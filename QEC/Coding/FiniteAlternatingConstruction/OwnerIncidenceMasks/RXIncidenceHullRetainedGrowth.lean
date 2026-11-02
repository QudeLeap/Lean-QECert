import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXIncidenceHullSuccessors
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXIncidenceHullRZ
import QEC.Coding.FiniteAlternatingConstruction.QuantitativeBounds

/-!
# A singleton incidence hull contains exponentially many actual retained roots

The injection below follows the two original Q roots through each actual
replacement. Only those explicitly retained coordinates are counted: no
connectivity of the entire successor Q carrier is assumed.
-/
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks

/-- Five actual base Q choices and the literal copy bit at every replacement. -/
def Retained : Nat → Type
  | 0 => BaseQubit
  | n+1 => Retained n × BDL26FiniteTannerSquare.Two

instance retainedFintype (n : Nat) : Fintype (Retained n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype BaseQubit)
  | succ n ih =>
      letI : Fintype (Retained n) := ih
      change Fintype (Retained n × BDL26FiniteTannerSquare.Two)
      infer_instance

instance retainedDecidableEq (n : Nat) : DecidableEq (Retained n) := Classical.decEq _

def retainedZero : (n : Nat) → Retained n
  | 0 => (0 : BaseQubit)
  | n+1 => (retainedZero n,0)

/-- The existing actual successor root injection, selected by original parity.
The explicit cast keeps the canonical state's dependent Q carrier intact. -/
def nextRoots (S : OddScale) (n : Nat) (C : ConstructionState) :
    C.presentation.Q × BDL26FiniteTannerSquare.Two ↪ (nextState S n C).presentation.Q :=
  if h : n % 2 = 0 then
    let E := Equiv.cast (congrArg (fun D : ConstructionState => D.presentation.Q)
      (show rxState S C = nextState S n C from (if_pos h).symm))
    { toFun := fun qt => E (rxQubitRoots C.presentation S qt)
      inj' := fun _ _ he => (rxQubitRoots C.presentation S).injective (E.injective he) }
  else
    let E := Equiv.cast (congrArg (fun D : ConstructionState => D.presentation.Q)
      (show rzState S C = nextState S n C from (if_neg h).symm))
    { toFun := fun qt => E (rzQubitRoots C.presentation S qt)
      inj' := fun _ _ he => (rzQubitRoots C.presentation S).injective (E.injective he) }

private theorem cast_path {C D : ConstructionState} (h : C = D)
    {q r : C.presentation.Q} (path : SharedZPath C.presentation q r) :
    SharedZPath D.presentation
      (Equiv.cast (congrArg (fun E : ConstructionState => E.presentation.Q) h) q)
      (Equiv.cast (congrArg (fun E : ConstructionState => E.presentation.Q) h) r) := by
  cases h
  exact path

private theorem rx_roots_apply (P : TannerSquarePresentation) (S : OddScale)
    (qt : P.Q × BDL26FiniteTannerSquare.Two) :
    rxQubitRoots P S qt = BDL26RXIncidenceHullSuccessors.rxRoot P S qt.1 qt.2 := rfl

private theorem rz_roots_apply (P : TannerSquarePresentation)
    (A : BDL26TannerLocalRegularity.TannerSquareAdmissible P) (S : OddScale)
    (qt : P.Q × BDL26FiniteTannerSquare.Two) :
    rzQubitRoots P S qt = BDL26RXIncidenceHullRZ.rzRoot P A S qt.1 qt.2 := rfl

/-- Every actual root-copy injection preserves the old component relation. -/
theorem nextRoots_paths (S : OddScale) (n : Nat) (C : ConstructionState)
    {q r : C.presentation.Q} (path : SharedZPath C.presentation q r)
    (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (nextState S n C).presentation
      (nextRoots S n C (q,a)) (nextRoots S n C (r,b)) := by
  by_cases h : n % 2 = 0
  · simpa only [nextRoots,dif_pos h,Function.Embedding.coeFn_mk,rx_roots_apply C.presentation S] using
      cast_path (show rxState S C = nextState S n C from (if_pos h).symm)
        (rx_path_roots C.presentation C.admissible.toTannerSquareAdmissible S path a b)
  · simpa only [nextRoots,dif_neg h,Function.Embedding.coeFn_mk,
      rz_roots_apply C.presentation C.admissible.toTannerSquareAdmissible S] using
      cast_path (show rzState S C = nextState S n C from (if_neg h).symm)
        (BDL26RXIncidenceHullRZ.rz_path_roots
          C.presentation C.admissible.toTannerSquareAdmissible S path a b)

/-- An explicit injection into the original recursively selected carrier. -/
def retainedRoots (S : OddScale) : (n : Nat) → Retained n ↪ (state S n).presentation.Q
  | 0 => ⟨id,Function.injective_id⟩
  | n+1 =>
      { toFun := fun a => nextRoots S n (state S n) (retainedRoots S n a.1,a.2)
        inj' := by
          intro a b he
          have hp := (nextRoots S n (state S n)).injective he
          have hfirst : a.1 = b.1 :=
            (retainedRoots S n).injective
              (congrArg (fun v : (state S n).presentation.Q × BDL26FiniteTannerSquare.Two => v.1) hp)
          have hsecond : a.2 = b.2 :=
            congrArg (fun v : (state S n).presentation.Q × BDL26FiniteTannerSquare.Two => v.2) hp
          exact Prod.ext hfirst hsecond }

theorem retainedRoots_connected (S : OddScale) (n : Nat) (a b : Retained n) :
    SharedZPath (state S n).presentation (retainedRoots S n a) (retainedRoots S n b) := by
  induction n with
  | zero => exact base_path a b
  | succ n ih =>
      exact nextRoots_paths S n (state S n) (ih a.1 b.1) a.2 b.2

theorem retained_card (n : Nat) : Fintype.card (Retained n) = 5*2^n := by
  induction n with
  | zero => exact baseQubit_card.trans (by norm_num)
  | succ n ih =>
      change Fintype.card (Retained n × BDL26FiniteTannerSquare.Two) = _
      rw [Fintype.card_prod,ih]
      simp only [BDL26FiniteTannerSquare.Two,Fintype.card_fin]
      rw [pow_succ]
      ring

/-- The explicit bounded-size seed family. -/
def seed (S : OddScale) (n : Nat) : Finset (state S n).presentation.Q :=
  {retainedRoots S n (retainedZero n)}

theorem seed_card (S : OddScale) (n : Nat) : (seed S n).card = 1 := by
  simp [seed]

/-- The original singleton hull contains all five times two-to-the-level
retained coordinates. This is an ACTUAL hull bound, not a global Q count. -/
theorem singleton_hull_card_lower (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    5*2^i.val ≤ (incidenceHull S depth i (seed S i.val)).card := by
  have hsub : (Finset.univ.map (retainedRoots S i.val)) ⊆
      incidenceHull S depth i (seed S i.val) := by
    intro r hr
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hr
    exact (mem_incidenceHull_iff_path S depth i (seed S i.val) _).mpr
      ⟨retainedRoots S i.val (retainedZero i.val),by simp [seed],
        retainedRoots_connected S i.val (retainedZero i.val) a⟩
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_map,Finset.card_univ,retained_card] using hc

/-- Any all-word commuting pair containing this one seed must pay the same
exponential lower bound on its lower mask. -/
theorem commuting_pair_card_lower (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed S i.val ⊆ A)
    (commutes : ∀ w, MultiscaleDecoder.maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (MultiscaleDecoder.maskWord A w)) :
    5*2^i.val ≤ A.card :=
  (singleton_hull_card_lower S depth i).trans
    (Finset.card_le_card
      (incidenceHull_le_every_commuting_pair S depth i h _ A B hseed commutes).1)

/-- At EVERY fixed legal odd scale, singleton hulls exceed every proposed
depth-independent cardinal bound already at legal even-source RX steps. -/
theorem no_uniform_singleton_bound (S : OddScale) (C : Nat) :
    ∃ (depth : Nat) (i : StepIndex depth), i.val % 2 = 0 ∧
      (seed S i.val).card = 1 ∧ C < (incidenceHull S depth i (seed S i.val)).card := by
  let m := 2*(C+1)
  let i : StepIndex (m+1) := ⟨m,by omega⟩
  refine ⟨m+1,i,?_,seed_card S i.val,?_⟩
  · change (2*(C+1)) % 2 = 0
    omega
  · have hg := singleton_hull_card_lower S (m+1) i
    have hp : i.val < 2^i.val := i.val.lt_two_pow_self
    have hm : C < i.val := by change C < 2*(C+1); omega
    omega

end QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
end
