import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ProbabilityDecay
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.DependencyCounts
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.LLLCriterion

/-! # Constructed numerical parameters for the actual geometric event family -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- Both auxiliary triangle labels are counted, including geometrically collapsed labels. -/
def triangleDensityBound : ℕ := 4*56^3

noncomputable def capCutoff (m : ℕ) : ℝ := Real.cos (1/(12*(m : ℝ)))
def anchorRadius (m : ℕ) : ℕ := 12*m+4
def dependencyBound (M : ℕ) : ℕ := 12*56*M^3

noncomputable def densityHandoff (m : ℕ) : ℝ :=
  64*Real.pi*triangleDensityBound*(2*(6*(m : ℝ))+1)^2/
    ((6*(m : ℝ)*widthFactor-1)*((m : ℝ)-1))

/-- This record contains only numerical inequalities. Its existence is proved below before
any input presentation, probability conclusion, or successful assignment is introduced. -/
structure GeometricParameters (densityLower : ℝ) where
  m : ℕ
  t : ℝ
  M : ℕ
  lambda : ℕ
  m_two : 2 ≤ m
  width_positive : 1 < 6*(m : ℝ)*widthFactor
  t_positive : 0 < t
  density_lower : densityLower < t
  triangle_density : (triangleDensityBound : ℝ) < t
  handoff : densityHandoff m < t
  pool : (2*anchorRadius m+1 : ℕ)^3*(250*t) ≤ (M : ℝ)
  lambda_one : 1 ≤ lambda
  rounding : 13 ≤ (2*(6*(m : ℝ))+1)*(lambda : ℝ)
  probability : 4*probabilityCoefficient (6*m) (capCutoff m)*
    ((dependencyBound M : ℝ)+1) ≤ (lambda : ℝ)

/-- The order is cap/color constants, density, pool/dependency bound, then scale. -/
theorem geometricParameters_nonempty (densityLower : ℝ) :
    Nonempty (GeometricParameters densityLower) := by
  obtain ⟨m,hm,hw⟩ := exists_cap_integer
  obtain ⟨t,ht,htp,hth⟩ := exists_input_density
    (max densityLower triangleDensityBound) (densityHandoff m)
  obtain ⟨M,hM⟩ := exists_local_pool_bound t (anchorRadius m)
  obtain ⟨lambda,hl,hr,hprob⟩ := exists_integer_scale
    (alpha := 6*(m : ℝ))
    (probabilityConstant := probabilityCoefficient (6*m) (capCutoff m))
    (by positivity) (dependencyBound M)
  exact ⟨⟨m,t,M,lambda,hm,hw,ht,
    (le_max_left _ _).trans_lt htp,(le_max_right _ _).trans_lt htp,
    hth,hM,hl,hr,hprob⟩⟩

theorem capCutoff_bounds {m : ℕ} (hm : 2 ≤ m) :
    -1 < capCutoff m ∧ capCutoff m < 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 1/(12*(m : ℝ)) := by positivity
  have hsmall : 1/(12*(m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 12*(m : ℝ))).mpr
    linarith
  have hpi := Real.two_le_pi
  exact cos_mem_open_unit hp (by linarith)

theorem GeometricParameters.probability_ratio {densityLower : ℝ}
    (p : GeometricParameters densityLower) :
    probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) ≤
      1/(4*((dependencyBound p.M : ℝ)+1)) := by
  have hl : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hd : 0 < 4*((dependencyBound p.M : ℝ)+1) := by positivity
  apply (div_le_div_iff₀ hl hd).mpr
  nlinarith [p.probability]

end QEC.Coding.BDL26RandomPerturbation
