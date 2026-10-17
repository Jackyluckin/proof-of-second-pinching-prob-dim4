import SecondPinching.SimonsDifferentiation
import SecondPinching.PengTerngNormAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Squared norm of the actual differential in an orthonormal immersion frame. -/
def immersionScalarGradientNormSq (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) : ℝ :=
  ∑ k, (fderiv ℝ u x (e.coefficients x k))^2

theorem immersionScalarGradientNormSq_secondForm (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarGradientNormSq F e (fun y => matrixNormSq (immersionFrameSecond F e y)) x =
      4*(cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) ⬝ᵥ
        cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x)) := by
  have hd (k : Fin 4) : fderiv ℝ (fun y => matrixNormSq (immersionFrameSecond F e y)) x
      (e.coefficients x k) = 2*cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) k :=
    immersionFrameSecond_norm_derivative F e x hx k
  simp only [immersionScalarGradientNormSq,hd,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; ring

/-- The full variable-S Peng--Terng identity, eq:PT, derived from the actual
immersion, its Levi-Civita connection and its covariant derivatives. -/
theorem immersionScalarLaplacian_pengTerng (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) :
    (1/2 : ℝ)*immersionScalarLaplacian F e (fun y => cubicNormSq (immersionFrameThird F e y)) x =
      fourthNormSq (immersionFrameFourth F e x)+
      (11-matrixNormSq (immersionFrameSecond F e x))*cubicNormSq (immersionFrameThird F e x)-
      3*(intrinsicCubicA (immersionFrameSecond F e x) (immersionFrameThird F e x)-
        2*intrinsicCubicB (immersionFrameSecond F e x) (immersionFrameThird F e x))-
      (3/2 : ℝ)*immersionScalarGradientNormSq F e
        (fun y => matrixNormSq (immersionFrameSecond F e y)) x := by
  have ht : cubicTrace (immersionFrameThird F e x) = 0 := by
    funext k
    exact immersionFrameThird_trace_of_minimal_germ F e x hx
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hminimal) k
  rw [immersionScalarLaplacian_cubic_norm F e x hx,
    immersionFrameFifth_roughTrace F e hminimal x hx,
    pengTerngCubic_inner _ _ (immersionFrameSecond_symmetric F e x hx)
      (immersionFrameThird_symmetric F e x hx) (hminimal x hx) ht,
    immersionScalarGradientNormSq_secondForm F e x hx]
  ring

theorem immersionScalarLaplacian_of_constant (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (c : ℝ) (hu : ∀ y ∈ F.domain, u y = c)
    (x : Chart4) (hx : x ∈ F.domain) : immersionScalarLaplacian F e u x = 0 := by
  have hd (y : Chart4) (hy : y ∈ F.domain) : fderiv ℝ u y = 0 := by
    have hg : u =ᶠ[𝓝 y] fun _ => c :=
      Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hy) hu
    simp only [hg.fderiv_eq,fderiv_const_apply]
  have he (k : Fin 4) : (fun y => fderiv ℝ u y (e.coefficients y k)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    apply Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
    intro y hy
    exact congrArg (fun L : Chart4 →L[ℝ] ℝ => L (e.coefficients y k)) (hd y hy)
  unfold immersionScalarLaplacian
  simp only [(he _).fderiv_eq,fderiv_const_apply,zero_apply,hd x hx,mul_zero,
    Finset.sum_const_zero,sub_zero]

theorem immersionScalarGradientNormSq_of_constant (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (c : ℝ) (hu : ∀ y ∈ F.domain, u y = c)
    (x : Chart4) (hx : x ∈ F.domain) : immersionScalarGradientNormSq F e u x = 0 := by
  have hg : u =ᶠ[𝓝 x] fun _ => c :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hu
  simp only [immersionScalarGradientNormSq,hg.fderiv_eq,fderiv_const_apply,zero_apply,
    zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]

/-- The constant-S consequence of eq:PT. The vanishing Laplacian is derived
from the Simons norm formula on the whole open domain. -/
theorem immersionFrameFourth_norm_of_minimal_constant (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    fourthNormSq (immersionFrameFourth F e x) =
      3*(intrinsicCubicA (immersionFrameSecond F e x) (immersionFrameThird F e x)-
        2*intrinsicCubicB (immersionFrameSecond F e x) (immersionFrameThird F e x))+
      (S-11)*S*(S-4) := by
  have he := immersionScalarLaplacian_pengTerng F e hminimal x hx
  rw [immersionScalarLaplacian_of_constant F e _ (S*(S-4))
    (immersionFrameThird_norm_of_minimal_constant F e S hminimal hSnorm) x hx,
    immersionScalarGradientNormSq_of_constant F e _ S hSnorm x hx,hSnorm x hx,
    immersionFrameThird_norm_of_minimal_constant F e S hminimal hSnorm x hx] at he
  nlinarith [he]

end
end SecondPinching
