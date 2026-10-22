import QEC.Coding.FiberBundle.RandomBase
import Mathlib.Probability.Distributions.Uniform

/-!
# The HHO20 random rotation twists

This module formalizes the construction in
`hastings-haah-odonnell-2020-fiber-bundle/bundle.tex:891-932`.
Checks have deterministic types.  Every possible Tanner incidence receives an
independent uniformly random head/tail bit, and every check type receives an
independent uniformly random nonzero multiple of the fiber scale.
-/

namespace QEC.Coding.FiberBundle.RandomTwist

open scoped BigOperators

/-- An index for either a head/tail choice or a type-level twist choice. -/
abbrev ChoiceIndex (r typeCount : Nat) :=
  Sum (Fin (3 * r) × Fin (4 * r)) (Fin typeCount)

/-- The value sampled at each kind of random-choice index. -/
def ChoiceValue (ell : Nat) {r typeCount : Nat} :
    ChoiceIndex r typeCount → Type
  | Sum.inl _ => Bool
  | Sum.inr _ => Fin (ell - 1)

instance instFintypeChoiceValue
    (ell : Nat) {r typeCount : Nat} :
    ∀ i : ChoiceIndex r typeCount, Fintype (ChoiceValue ell i)
  | Sum.inl _ => by
      change Fintype Bool
      infer_instance
  | Sum.inr _ => by
      change Fintype (Fin (ell - 1))
      infer_instance

/-- All head/tail and type-twist choices produced by one random draw. -/
abbrev Sample (r typeCount ell : Nat) :=
  ∀ i : ChoiceIndex r typeCount, ChoiceValue ell i

/-- The check type selected by the construction's fixed cyclic partition. -/
def checkType
    {r : Nat} (typeCount : Nat) [NeZero typeCount]
    (a : Fin (3 * r)) : Fin typeCount :=
  ⟨a.val % typeCount, Nat.mod_lt _ (NeZero.pos typeCount)⟩

/-- Read the random head/tail bit for a check-variable pair. -/
def isTail
    {r typeCount ell : Nat}
    (sample : Sample r typeCount ell)
    (a : Fin (3 * r)) (b : Fin (4 * r)) : Bool :=
  sample (Sum.inl (a, b))

/-- Read the nonzero type-level twist index. -/
def typeTwist
    {r typeCount ell : Nat}
    (sample : Sample r typeCount ell)
    (τ : Fin typeCount) : Fin (ell - 1) :=
  sample (Sum.inr τ)

/--
The per-incidence rotation index.  Heads receive zero; tails receive the
nonzero index attached to their check type.
-/
def connectionIndex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (sample : Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r)) : Fin ell :=
  if isTail sample a b then
    ⟨(typeTwist sample (checkType typeCount a)).val + 1, by
      have h :=
        (typeTwist sample (checkType typeCount a)).isLt
      omega⟩
  else
    0

/-- The coordinate PMF used by the independent twist sampler. -/
noncomputable def coordinatePMF
    (ell : Nat) [NeZero (ell - 1)]
    {r typeCount : Nat} :
    ∀ i : ChoiceIndex r typeCount, PMF (ChoiceValue ell i)
  | Sum.inl _ =>
      PMF.bernoulli (1 / 2 : NNReal) (by norm_num)
  | Sum.inr _ =>
      PMF.uniformOfFintype (Fin (ell - 1))

/--
The exact independent distribution of all HHO20 head/tail and type-twist
choices.
-/
noncomputable def distribution
    (r typeCount ell : Nat)
    [NeZero (ell - 1)] :
    PMF (Sample r typeCount ell) :=
  RandomBase.independentProduct (coordinatePMF ell)

@[simp]
theorem distribution_apply
    (r typeCount ell : Nat)
    [NeZero (ell - 1)]
    (sample : Sample r typeCount ell) :
    distribution r typeCount ell sample =
      ∏ i : ChoiceIndex r typeCount,
        coordinatePMF ell i (sample i) := by
  rfl

/--
Combine construction-selected base and twist samples into the actual HHO20
cycle-bundle chain data.  No matrix, rank, distance, or expansion certificate
is accepted from the caller.
-/
def fiberBundleData
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : Sample r typeCount ell) :
    Data
      (Fin (3 * r)) (Fin (4 * r))
      (ZMod (ell * ell)) (ZMod (ell * ell)) :=
  multipleRotationCycleData ell
    (RandomBase.boundary baseSample)
    (connectionIndex twistSample)

end QEC.Coding.FiberBundle.RandomTwist
