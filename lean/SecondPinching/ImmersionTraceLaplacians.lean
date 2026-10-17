import SecondPinching.TracePowerContractions
import SecondPinching.TracePowerRegularity

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Trace a weighted-gradient formula only after subtracting the connection
on its free covector index. The gradient equality is required on an open domain. -/
theorem immersionScalarLaplacian_of_weighted_gradient
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (u : Chart4 → ℝ)
    (Q : Chart4 → Matrix4) (a : ℝ) (x : Chart4) (hx : x ∈ F.domain)
    (hQ : DifferentiableAt ℝ Q x) (hsQ : (Q x).IsSymm) (U : Fin 4 → Matrix4)
    (hdQ : ∀ k, matrixDerivative Q x (e.coefficients x k) =
      immersionFrameConnection F e x k*Q x+Q x*(immersionFrameConnection F e x k)ᵀ+U k)
    (hgrad : ∀ y ∈ F.domain, ∀ k,
      fderiv ℝ u y (e.coefficients y k) = a*cubicWeightedTrace (Q y) (immersionFrameThird F e y) k) :
    immersionScalarLaplacian F e u x =
      a*(∑ k, matrixInner (U k) (cubicLastSlice (immersionFrameThird F e x) k))+
        a*matrixInner (Q x) (roughTrace (immersionFrameFourth F e x)) := by
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hd (k : Fin 4) : fderiv ℝ (fun y => fderiv ℝ u y (e.coefficients y k)) x (e.coefficients x k) =
      a*(matrixInner (U k) (cubicLastSlice (immersionFrameThird F e x) k)+
        weightedTrace (Q x) (immersionFrameFourth F e x) k k+
        ∑ r, immersionFrameConnection F e x k k r*cubicWeightedTrace (Q x) (immersionFrameThird F e x) r) := by
    have hg : (fun y => fderiv ℝ u y (e.coefficients y k)) =ᶠ[𝓝 x]
        fun y => a*cubicWeightedTrace (Q y) (immersionFrameThird F e y) k :=
      Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => hgrad y hy k)
    rw [hg.fderiv_eq]
    erw [fderiv_fun_mul (differentiableAt_const a) (differentiableAt_weightedTrace Q _ x hQ ht k)]
    simp only [add_apply,smul_apply,smul_eq_mul,fderiv_const_apply,zero_apply,mul_zero,add_zero]
    rw [immersion_weightedTrace_derivative F e Q x hx k k hQ hsQ (U k) (hdQ k)]
    rfl
  unfold immersionScalarLaplacian
  simp only [hd,hgrad x hx]
  have hc (k : Fin 4) : (∑ r, immersionFrameConnection F e x k k r*
      (a*cubicWeightedTrace (Q x) (immersionFrameThird F e x) r)) =
      a*(∑ r, immersionFrameConnection F e x k k r*cubicWeightedTrace (Q x) (immersionFrameThird F e x) r) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
  simp only [hc]
  have he (b c d : ℝ) : a*(b+c+d)-a*d=a*b+a*c := by ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum]
  change _ = _+a*matrixInner (Q x) (roughTrace (immersionFrameFourth F e x))
  rw [← trace_weightedTrace_eq_roughPairing]
  rfl

/-- The cubic trace identity eq:f3, with S=|h|^2 allowed to vary. -/
theorem immersionScalarLaplacian_cubicTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarLaplacian F e (immersionCubicTrace F e) x =
      3*(4-matrixNormSq (immersionFrameSecond F e x))*immersionCubicTrace F e x+
        6*intrinsicCubicC (immersionFrameSecond F e x) (immersionFrameThird F e x) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he := immersionScalarLaplacian_of_weighted_gradient F e (immersionCubicTrace F e)
    (fun y => (immersionFrameSecond F e y)^2) 3 x hx
    (differentiableAt_matrix_pow _ _ hh 2) ((immersionFrameSecond_symmetric F e x hx).pow 2)
    (fun k => squareVariation (immersionFrameSecond F e x) (cubicLastSlice (immersionFrameThird F e x) k))
    (immersionFrameSquare_derivative F e x hx) (immersionCubicTrace_derivative F e)
  rw [sum_squareVariation_pairings _ _ (immersionFrameThird_symmetric F e x hx),
    immersionFrameFourth_simons F e hminimal x hx,matrixInner_smul_right,
    matrixInner_power_self _ (immersionFrameSecond_symmetric F e x hx) 2] at he
  rw [he]
  unfold immersionCubicTrace cubicMoment
  ring

/-- The quartic trace identity eq:f4, with no constant-S assumption. -/
theorem immersionScalarLaplacian_quarticTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarLaplacian F e (immersionQuarticTrace F e) x =
      4*(4-matrixNormSq (immersionFrameSecond F e x))*immersionQuarticTrace F e x+
        8*intrinsicCubicA (immersionFrameSecond F e x) (immersionFrameThird F e x)+
        4*intrinsicCubicB (immersionFrameSecond F e x) (immersionFrameThird F e x) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he := immersionScalarLaplacian_of_weighted_gradient F e (immersionQuarticTrace F e)
    (fun y => (immersionFrameSecond F e y)^3) 4 x hx
    (differentiableAt_matrix_pow _ _ hh 3) ((immersionFrameSecond_symmetric F e x hx).pow 3)
    (fun k => cubeVariation (immersionFrameSecond F e x) (cubicLastSlice (immersionFrameThird F e x) k))
    (immersionFrameCube_derivative F e x hx) (immersionQuarticTrace_derivative F e)
  rw [sum_cubeVariation_pairings _ _ (immersionFrameSecond_symmetric F e x hx)
    (immersionFrameThird_symmetric F e x hx),immersionFrameFourth_simons F e hminimal x hx,
    matrixInner_smul_right,matrixInner_power_self _ (immersionFrameSecond_symmetric F e x hx) 3] at he
  rw [he]
  unfold immersionQuarticTrace quarticMoment
  ring

theorem immersionCubicTrace_gradient_norm (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarGradientNormSq F e (immersionCubicTrace F e) x =
      9*(intrinsicCubicD (immersionFrameSecond F e x) (immersionFrameThird F e x) ⬝ᵥ
        intrinsicCubicD (immersionFrameSecond F e x) (immersionFrameThird F e x)) := by
  simp only [immersionScalarGradientNormSq,immersionCubicTrace_derivative F e x hx,
    intrinsicCubicD,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; ring

end
end SecondPinching
