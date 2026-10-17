import Mathlib.Data.Int.Basic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SecondPinching

/-- Literal bivariate coefficient. No parsing or arithmetic acceptance occurs here. -/
structure ReleasedPowerTerm where
  rDegree : Nat
  yDegree : Nat
  coefficient : Int
  deriving Inhabited, Repr

/-- Original compressed leaf data. Pools are flattened in pool/row/column order;
assignments use the original zero-based row-major control order. -/
structure ReleasedLeafData where
  nullCorners : Array (Array Int)
  witnessPools : Array (Array Int)
  poolSizes : Array Nat
  witnessIndices : Array (Array Nat)
  deriving Inhabited, Repr

end SecondPinching
