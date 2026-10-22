import QEC.Coding.QuditQubitConversion.AppendixANF.Cubic.Data

/-! One bounded cubic coefficient probe for the WHY24 Appendix-A certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

set_option maxRecDepth 2048 in
theorem sourceCoefficient_triple_0_1_2_probe :
    sourceTripleCoefficient 0 1 2 = cubicGateCoefficient 0 1 2 := by
  decide

end QEC.Coding.Why24AppendixANF
