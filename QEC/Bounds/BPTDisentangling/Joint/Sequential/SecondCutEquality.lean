import QEC.Bounds.BPTDisentangling.Joint.Sequential.BlockData

/-! # Equality composition helper for the second-cut joint block -/

namespace QEC
namespace Bounds

/-- Map an input equality once, then compose it with an equality at the mapped value. -/
theorem map_eq_of_eq_of_map_eq {α β : Type*} (f : α → β) {x y : α} {z : β}
    (hxy : x = y) (hyz : f y = z) : f x = z :=
  (congrArg f hxy).trans hyz

end Bounds
end QEC
