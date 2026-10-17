import SecondPinching.CubicFluxHessian
import SecondPinching.CubicFluxAlgebra
import SecondPinching.VectorDivergenceProduct

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The vector h D in the proof of lem:mean. Here D is the raw cubic-trace
covector, equal to grad(f3)/3; it is not the normalized Hessian also named D. -/
def immersionCubicFlux (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (x : Chart4) : Vector4 :=
  immersionFrameSecond F e x*ᵥ
    intrinsicCubicD (immersionFrameSecond F e x) (immersionFrameThird F e x)

theorem immersionCubicFlux_eq_gradient (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionCubicFlux F e x = immersionFrameSecond F e x*ᵥ
      ((1/3 : ℝ) • immersionScalarGradient F e (immersionCubicTrace F e) x) := by
  have hg : immersionScalarGradient F e (immersionCubicTrace F e) x =
      (3 : ℝ) • intrinsicCubicD (immersionFrameSecond F e x) (immersionFrameThird F e x) := by
    funext k; exact immersionCubicTrace_derivative F e x hx k
  rw [hg,smul_smul]
  norm_num
  rfl

/-- The first line of the manuscript's divergence computation, in an
arbitrary smooth orthonormal frame. S need not be constant here. -/
theorem immersionCubicFlux_divergence (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionVectorDivergence F e (immersionCubicFlux F e) x =
      2*intrinsicCubicB (immersionFrameSecond F e x) (immersionFrameThird F e x)+
        matrixInner (immersionFrameSecond F e x)
          (weightedTrace ((immersionFrameSecond F e x)^2) (immersionFrameFourth F e x)) := by
  let X : Chart4 → Vector4 := fun y =>
    intrinsicCubicD (immersionFrameSecond F e y) (immersionFrameThird F e y)
  let Z : Matrix4 := fun r k =>
    matrixInner (squareVariation (immersionFrameSecond F e x) (cubicLastSlice (immersionFrameThird F e x) k))
      (cubicLastSlice (immersionFrameThird F e x) r)+
    weightedTrace ((immersionFrameSecond F e x)^2) (immersionFrameFourth F e x) r k
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hX : DifferentiableAt ℝ X x := by
    apply differentiableAt_pi.mpr; intro k
    exact differentiableAt_weightedTrace _ _ x (differentiableAt_matrix_pow _ _ hh 2) ht k
  have hdX (i k : Fin 4) : fderiv ℝ (fun y => X y i) x (e.coefficients x k) =
      (immersionFrameConnection F e x k*ᵥX x) i+Z i k := by
    change fderiv ℝ (fun y => cubicWeightedTrace ((immersionFrameSecond F e y)^2)
      (immersionFrameThird F e y) i) x (e.coefficients x k) = _
    rw [immersion_squareTrace_derivative F e x hx i k]
    change _ = (∑ r, immersionFrameConnection F e x k i r*
      cubicWeightedTrace ((immersionFrameSecond F e x)^2) (immersionFrameThird F e x) r)+
      (matrixInner (squareVariation (immersionFrameSecond F e x)
        (Matrix.of (fun a b => immersionFrameThird F e x a b k)))
        (Matrix.of (fun a b => immersionFrameThird F e x a b i))+
        weightedTrace ((immersionFrameSecond F e x)^2) (immersionFrameFourth F e x) i k)
    ring
  have he := immersionVectorDivergence_mulVec F e (immersionFrameSecond F e) X x hx hh hX
    (fun k => cubicLastSlice (immersionFrameThird F e x) k) Z
    (immersionFrameSecond_frame_derivative F e x hx) hdX
  have hz : cubicTrace (immersionFrameThird F e x)=0 := by
    funext k
    exact immersionFrameThird_trace_of_minimal_germ F e x hx
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hminimal) k
  rw [cubic_trace_divergence_term _ _ (immersionFrameThird_symmetric F e x hx) hz,zero_add] at he
  simp only [Z,mul_add,Finset.sum_add_distrib] at he
  rw [weighted_squareVariation_pairings _ _ (immersionFrameSecond_symmetric F e x hx)
    (immersionFrameThird_symmetric F e x hx),
    matrixInner_transposed_entries _ _ (immersionFrameSecond_symmetric F e x hx)] at he
  exact he

/-- The complete raw divergence identity in the proof of lem:mean, obtained
from actual Ricci and the twice-differentiated constant-S equation. -/
theorem immersionCubicFlux_divergence_of_constant (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionVectorDivergence F e (immersionCubicFlux F e) x =
      2*intrinsicCubicB (immersionFrameSecond F e x) (immersionFrameThird F e x)-
      intrinsicCubicA (immersionFrameSecond F e x) (immersionFrameThird F e x)+
      S*immersionQuarticTrace F e x-(immersionCubicTrace F e x)^2-S^2 := by
  rw [immersionCubicFlux_divergence F e hminimal x hx,
    cubic_flux_hessian _ _ _ (immersionFrameSecond_symmetric F e x hx) (hminimal x hx)
      (immersionFrameFourth_firstThree F e x hx) (immersionFrameFourth_ricci F e x hx)
      (immersionFrameFourth_weighted_of_constant_norm F e S hSnorm x hx),hSnorm x hx]
  unfold immersionCubicTrace immersionQuarticTrace
  ring

end
end SecondPinching
