import SecondPinching.ImmersionTraceLaplacians
import SecondPinching.ImmersionCubicFlux
import SecondPinching.MomentNormalization

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The potential Sf4/4 from eq:divergences; S is the fixed scalar parameter. -/
def immersionQuarticPotential (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (x : Chart4) : ℝ :=
  (S/4)*immersionQuarticTrace F e x

/-- The even potential f3^2/6, which does not require a global choice of normal. -/
def immersionCubicPotential (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (x : Chart4) : ℝ :=
  (1/6 : ℝ)*(immersionCubicTrace F e x)^2

theorem immersionQuarticPotential_laplacian (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarLaplacian F e (immersionQuarticPotential F e S) x =
      S*((4-S)*immersionQuarticTrace F e x+
        2*intrinsicCubicA (immersionFrameSecond F e x) (immersionFrameThird F e x)+
        intrinsicCubicB (immersionFrameSecond F e x) (immersionFrameThird F e x)) := by
  unfold immersionQuarticPotential
  rw [immersionScalarLaplacian_const_mul F e _ (S/4) (contDiffOn_immersionQuarticTrace F e) x hx,
    immersionScalarLaplacian_quarticTrace F e hminimal x hx,hSnorm x hx]
  ring

theorem immersionCubicPotential_laplacian (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarLaplacian F e (immersionCubicPotential F e) x =
      (4-S)*(immersionCubicTrace F e x)^2+
        2*immersionCubicTrace F e x*intrinsicCubicC (immersionFrameSecond F e x) (immersionFrameThird F e x)+
        3*(intrinsicCubicD (immersionFrameSecond F e x) (immersionFrameThird F e x) ⬝ᵥ
          intrinsicCubicD (immersionFrameSecond F e x) (immersionFrameThird F e x)) := by
  have hu := contDiffOn_immersionCubicTrace F e
  unfold immersionCubicPotential
  rw [immersionScalarLaplacian_const_mul F e _ (1/6) (hu.pow 2) x hx,
    immersionScalarLaplacian_square F e _ hu x hx,
    immersionScalarLaplacian_cubicTrace F e hminimal x hx,immersionCubicTrace_gradient_norm F e x hx,
    hSnorm x hx]
  ring

/-- First pointwise identity of eq:divergences for the existing L4 expression. -/
theorem immersionL4_divergence_identity (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4<S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (x : Chart4) (hx : x ∈ F.domain) :
    intrinsicCorrectionL4 (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) (pinchingParameter S) =
      immersionScalarLaplacian F e (immersionQuarticPotential F e S) x/S^4 := by
  have hs : S≠0 := by linarith
  rw [immersionNormalizedA,immersionNormalizedTau,normalizedCorrectionL4 S hS,
    immersionQuarticPotential_laplacian F e S hminimal hSnorm x hx]
  unfold immersionQuarticTrace
  field_simp

theorem immersionL3_divergence_identity (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4<S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (x : Chart4) (hx : x ∈ F.domain) :
    intrinsicCorrectionL3 (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) (pinchingParameter S) =
      immersionScalarLaplacian F e (immersionCubicPotential F e) x/S^4 := by
  rw [immersionNormalizedA,immersionNormalizedTau,normalizedCorrectionL3 S hS,
    immersionCubicPotential_laplacian F e S hminimal hSnorm x hx]
  rfl

/-- Third pointwise identity of eq:divergences. The flux is independently
identified with h grad(f3)/3, and d is not assumed to vanish. -/
theorem immersionJ_divergence_identity (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4<S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (x : Chart4) (hx : x ∈ F.domain) :
    intrinsicCorrectionJ (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) (pinchingParameter S) =
      -immersionVectorDivergence F e (immersionCubicFlux F e) x/S^3 := by
  rw [immersionNormalizedA,immersionNormalizedTau,normalizedCorrectionJ S hS _ _
    (immersionFrameSecond_symmetric F e x hx) (hminimal x hx) (hSnorm x hx),
    immersionCubicFlux_divergence_of_constant F e S hminimal hSnorm x hx]
  rfl

end
end SecondPinching
