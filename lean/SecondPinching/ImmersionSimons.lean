import SecondPinching.ImmersionRicci
import SecondPinching.HessianSimonsAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The tensor Simons identity for the actual immersion. Minimality is local;
S is still the function |h|^2 and need not be constant. -/
theorem immersionFrameFourth_simons (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) :
    roughTrace (immersionFrameFourth F e x) =
      (4-matrixNormSq (immersionFrameSecond F e x)) • immersionFrameSecond F e x :=
  roughTrace_of_ricci _ _ (immersionFrameSecond_symmetric F e x hx)
    (hminimal x hx) (immersionFrameFourth_firstThree F e x hx)
    (immersionFrameFourth_trace_of_minimality F e hminimal x hx)
    (immersionFrameFourth_ricci F e x hx)

/-- Trace of the scalar covariant Hessian in the actual orthonormal frame:
sum_k (e_k(e_k u)-(nabla_{e_k} e_k)u). The connection is constructed from f,B. -/
def immersionScalarLaplacian (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) : ℝ :=
  ∑ k, (fderiv ℝ (fun y => fderiv ℝ u y (e.coefficients y k)) x (e.coefficients x k) -
    ∑ r, immersionFrameConnection F e x k k r*fderiv ℝ u x (e.coefficients x r))

/-- Metric product rule for the scalar rough Laplacian, before minimality
or constancy of S is used. All connection contributions cancel explicitly. -/
theorem immersionScalarLaplacian_norm (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    (1/2 : ℝ)*immersionScalarLaplacian F e (fun y => matrixNormSq (immersionFrameSecond F e y)) x =
      cubicNormSq (immersionFrameThird F e x)+
      matrixInner (immersionFrameSecond F e x) (roughTrace (immersionFrameFourth F e x)) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hd (k : Fin 4) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => matrixNormSq (immersionFrameSecond F e z)) y
        (e.coefficients y k)) x (e.coefficients x k) =
      2*(weightedTrace (immersionFrameSecond F e x) (immersionFrameFourth F e x) k k+
        cubicGramMatrix (immersionFrameThird F e x) k k+
        ∑ r, immersionFrameConnection F e x k k r*
          cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) r) := by
    have he : (fun y => fderiv ℝ (fun z => matrixNormSq (immersionFrameSecond F e z)) y
        (e.coefficients y k)) =ᶠ[𝓝 x]
        fun y => 2*cubicWeightedTrace (immersionFrameSecond F e y) (immersionFrameThird F e y) k :=
      Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
        (fun y hy => immersionFrameSecond_norm_derivative F e y hy k)
    have hw : DifferentiableAt ℝ (fun y =>
        cubicWeightedTrace (immersionFrameSecond F e y) (immersionFrameThird F e y) k) x := by
      unfold cubicWeightedTrace; fun_prop
    rw [he.fderiv_eq]
    erw [fderiv_fun_mul (differentiableAt_const (2 : ℝ)) hw]
    simp only [add_apply,smul_apply,smul_eq_mul,fderiv_const_apply,zero_apply,mul_zero,add_zero]
    rw [immersionFrameThird_weighted_derivative F e x hx k k]
  unfold immersionScalarLaplacian
  simp only [hd,immersionFrameSecond_norm_derivative F e x hx]
  have hs : (∑ k, (2*(weightedTrace (immersionFrameSecond F e x) (immersionFrameFourth F e x) k k+
      cubicGramMatrix (immersionFrameThird F e x) k k+
      ∑ r, immersionFrameConnection F e x k k r*
        cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) r)-
      ∑ r, immersionFrameConnection F e x k k r*
        (2*cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) r))) =
      2*Matrix.trace (weightedTrace (immersionFrameSecond F e x) (immersionFrameFourth F e x))+
      2*Matrix.trace (cubicGramMatrix (immersionFrameThird F e x)) := by
    simp only [Matrix.trace,Matrix.diag,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    have hc : (∑ r, immersionFrameConnection F e x k k r*
        (2*cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) r)) =
        2*(∑ r, immersionFrameConnection F e x k k r*
          cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) r) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
    rw [hc]; ring
  change (1/2 : ℝ)*(∑ k, _) = _
  erw [hs]
  rw [trace_weightedTrace_eq_roughPairing,trace_cubicGramMatrix]
  ring

/-- The scalar equation in eq:simons, with the manuscript's Laplacian sign.
It is valid without assuming that |h|^2 is constant. -/
theorem immersionScalarLaplacian_simons (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) :
    (1/2 : ℝ)*immersionScalarLaplacian F e (fun y => matrixNormSq (immersionFrameSecond F e y)) x =
      cubicNormSq (immersionFrameThird F e x)+
      matrixNormSq (immersionFrameSecond F e x)*(4-matrixNormSq (immersionFrameSecond F e x)) := by
  rw [immersionScalarLaplacian_norm F e x hx,immersionFrameFourth_simons F e hminimal x hx,
    matrixInner_smul_right,matrixInner_self,mul_comm (4-_)]

/-- The domain-local Simons norm consequence is derived from actual
minimality and constant |h|^2. It is no longer an interface assumption. -/
theorem immersionFrameThird_norm_of_minimal_constant (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    cubicNormSq (immersionFrameThird F e x) = S*(S-4) := by
  have he := simons_norm_of_constant_norm_contraction _ _ _
    (immersionFrameFourth_weighted_of_constant_norm F e S hSnorm x hx)
    (immersionFrameFourth_simons F e hminimal x hx)
  simpa only [hSnorm x hx] using he

end
end SecondPinching
