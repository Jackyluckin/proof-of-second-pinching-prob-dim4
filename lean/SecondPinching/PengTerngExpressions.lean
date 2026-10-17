import SecondPinching.MovingFrameFourth

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- Derivative of the Gauss-substituted Ricci polynomial with respect to h. -/
def ricciVariation (h U : Matrix4) : Fourth4 := fun i j k l =>
  (1 : Matrix4) i l*U j k-(1 : Matrix4) i k*U j l+U i k*(1 : Matrix4) j l-U i l*(1 : Matrix4) j k+
  U i l*(h*h) j k+h i l*(U*h+h*U) j k-U i k*(h*h) j l-h i k*(U*h+h*U) j l+
  (U*h+h*U) i k*h j l+(h*h) i k*U j l-(U*h+h*U) i l*h j k-(h*h) i l*U j k

/-- Divergence of the Ricci polynomial after covariant differentiation. -/
def ricciVariationDivergence (h : Matrix4) (T : Cubic4) : Cubic4 := fun i j k =>
  ∑ l, ricciVariation h (fun a b => T a b l) i j k l

/-- Ricci curvature acting on all three slots of nabla h. -/
def cubicCurvatureTrace (h : Matrix4) (T : Cubic4) : Cubic4 := fun i j k =>
  ∑ l, cubicConnectionAction (fun a r => gaussCurvature h r a k l) T i j l

/-- The rough Laplacian obtained by differentiating Simons and commuting the
last derivatives. This is an algebraic expression, not a definition of Delta T. -/
def pengTerngCubic (h : Matrix4) (T : Cubic4) : Cubic4 := fun i j k =>
  (4-matrixNormSq h)*T i j k-2*h i j*cubicWeightedTrace h T k+
  ricciVariationDivergence h T i j k+cubicCurvatureTrace h T i j k

end
end SecondPinching
