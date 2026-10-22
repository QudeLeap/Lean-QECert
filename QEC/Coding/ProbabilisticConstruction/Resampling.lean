import QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
import QEC.Coding.ProbabilisticConstruction.Resampling.ParameterizedExecution
import QEC.Coding.ProbabilisticConstruction.Resampling.Cost

/-!
# Measurable product-variable resampling

This module implements the ordered Moser--Tardos resampling execution on an
independent countable table with arbitrary measurable coordinate laws. Its
expected counts, almost-sure termination and primitive cost bound are derived
from actual history witnesses, independent table coordinates and finite proper
tree partition sums. Coordinate spaces are not required to be finite or discrete.

Main API in `QEC.Coding.ProbabilisticConstruction.Resampling`:
* `measurable_counters`, `measurable_selected`, `resampled_read_fresh`;
* `expected_totalCount_le`, `expected_totalSteps_le`;
* `halts_and_output_good_ae`, `measurable_output`;
* `expected_executionCost_le`, `measurable_executionCost`.

The cost model uses exact continuous samples and decidable local predicates as
idealized primitives. No finite-bit, worst-case or geometric construction claim
is made by this internal theorem.
-/
