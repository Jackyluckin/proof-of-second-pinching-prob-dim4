import SecondPinching.TracePowerRegularity

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Components of the actual differential in the supplied orthonormal frame. -/
def immersionScalarGradient (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) : Vector4 := fun k => fderiv ℝ u x (e.coefficients x k)

/-- Trace of the actual covariant derivative of a vector, represented using
orthonormal components. Skewness identifies vector and covector conventions. -/
def immersionVectorDivergence (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (X : Chart4 → Vector4) (x : Chart4) : ℝ :=
  ∑ k, (fderiv ℝ (fun y => X y k) x (e.coefficients x k)-
    ∑ r, immersionFrameConnection F e x k k r*X x r)

theorem immersionVectorDivergence_gradient (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) :
    immersionVectorDivergence F e (immersionScalarGradient F e u) x = immersionScalarLaplacian F e u x := rfl

theorem immersionScalarGradient_norm (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) :
    immersionScalarGradient F e u x ⬝ᵥ immersionScalarGradient F e u x =
      immersionScalarGradientNormSq F e u x := by
  simp only [immersionScalarGradient,dotProduct,immersionScalarGradientNormSq,pow_two]

theorem contDiffOn_immersionScalarGradient (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (hu : ContDiffOn ℝ ∞ u F.domain) :
    ContDiffOn ℝ ∞ (immersionScalarGradient F e u) F.domain := by
  have hd := hu.fderiv_of_isOpen F.isOpen_domain (m := ∞) (by simp)
  apply contDiffOn_pi.mpr; intro k
  exact hd.clm_apply (contDiffOn_pi.mp e.smooth k)

theorem immersionVectorDivergence_congr_germ (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (X Y : Chart4 → Vector4) (x : Chart4) (he : X =ᶠ[𝓝 x] Y) :
    immersionVectorDivergence F e X x = immersionVectorDivergence F e Y x := by
  have h0 : X x = Y x := he.eq_of_nhds
  have hc (k : Fin 4) : (fun y => X y k) =ᶠ[𝓝 x] fun y => Y y k :=
    he.mono (fun y hy => congrFun hy k)
  simp only [immersionVectorDivergence,(hc _).fderiv_eq,h0]

theorem immersionVectorDivergence_smul (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (X : Chart4 → Vector4) (x : Chart4)
    (hu : DifferentiableAt ℝ u x) (hX : DifferentiableAt ℝ X x) :
    immersionVectorDivergence F e (fun y => u y • X y) x =
      u x*immersionVectorDivergence F e X x+immersionScalarGradient F e u x ⬝ᵥ X x := by
  have hx (k : Fin 4) := differentiableAt_pi.mp hX k
  have he (k : Fin 4) : (∑ r, immersionFrameConnection F e x k k r*
      (u x*X x r)) = u x*(∑ r, immersionFrameConnection F e x k k r*X x r) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
  unfold immersionVectorDivergence immersionScalarGradient dotProduct
  simp only [Pi.smul_apply,smul_eq_mul,fderiv_fun_mul hu (hx _),add_apply,smul_apply]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [he k]
  ring

theorem immersionVectorDivergence_const_smul (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (X : Chart4 → Vector4) (x : Chart4) (a : ℝ) (hX : DifferentiableAt ℝ X x) :
    immersionVectorDivergence F e (fun y => a • X y) x = a*immersionVectorDivergence F e X x := by
  rw [immersionVectorDivergence_smul F e (fun _ => a) X x (differentiableAt_const a) hX]
  have hz : immersionScalarGradient F e (fun _ => a) x = 0 := by
    funext k
    exact congrArg (fun L : Chart4 →L[ℝ] ℝ => L (e.coefficients x k)) (fderiv_const_apply (𝕜 := ℝ) (x := x) a)
  rw [hz]
  simp

theorem immersionScalarGradient_const_mul (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) (a : ℝ) (hu : DifferentiableAt ℝ u x) :
    immersionScalarGradient F e (fun y => a*u y) x = a • immersionScalarGradient F e u x := by
  funext k
  unfold immersionScalarGradient
  rw [fderiv_fun_mul (differentiableAt_const a) hu]
  simp

theorem immersionScalarGradient_square (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (x : Chart4) (hu : DifferentiableAt ℝ u x) :
    immersionScalarGradient F e (fun y => (u y)^2) x = (2*u x) • immersionScalarGradient F e u x := by
  funext k
  simp only [immersionScalarGradient,pow_two]
  rw [fderiv_fun_mul hu hu]
  simp only [add_apply,smul_apply,Pi.smul_apply,smul_eq_mul,immersionScalarGradient]
  ring

theorem immersionScalarLaplacian_const_mul (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (a : ℝ) (hu : ContDiffOn ℝ ∞ u F.domain)
    (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarLaplacian F e (fun y => a*u y) x = a*immersionScalarLaplacian F e u x := by
  have hg : immersionScalarGradient F e (fun y => a*u y) =ᶠ[𝓝 x]
      fun y => a • immersionScalarGradient F e u y := by
    apply Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
    intro y hy
    exact immersionScalarGradient_const_mul F e u y a
      (((hu y hy).contDiffAt (F.isOpen_domain.mem_nhds hy)).differentiableAt (by simp))
  have hgrad := (((contDiffOn_immersionScalarGradient F e u hu) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [← immersionVectorDivergence_gradient,immersionVectorDivergence_congr_germ F e _ _ x hg,
    immersionVectorDivergence_const_smul F e _ x a hgrad,immersionVectorDivergence_gradient]

theorem immersionScalarLaplacian_square (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u : Chart4 → ℝ) (hu : ContDiffOn ℝ ∞ u F.domain) (x : Chart4) (hx : x ∈ F.domain) :
    immersionScalarLaplacian F e (fun y => (u y)^2) x =
      2*u x*immersionScalarLaplacian F e u x+2*immersionScalarGradientNormSq F e u x := by
  have hd := ((hu x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hg : immersionScalarGradient F e (fun y => (u y)^2) =ᶠ[𝓝 x]
      fun y => (2*u y) • immersionScalarGradient F e u y := by
    apply Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
    intro y hy
    exact immersionScalarGradient_square F e u y
      (((hu y hy).contDiffAt (F.isOpen_domain.mem_nhds hy)).differentiableAt (by simp))
  have hgrad := (((contDiffOn_immersionScalarGradient F e u hu) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [← immersionVectorDivergence_gradient,immersionVectorDivergence_congr_germ F e _ _ x hg,
    immersionVectorDivergence_smul F e (fun y => 2*u y) _ x ((differentiableAt_const (2 : ℝ)).mul hd) hgrad,
    immersionVectorDivergence_gradient,immersionScalarGradient_const_mul F e u x 2 hd]
  have he : ((2 : ℝ) • immersionScalarGradient F e u x) ⬝ᵥ immersionScalarGradient F e u x =
      2*immersionScalarGradientNormSq F e u x := by
    rw [← immersionScalarGradient_norm]
    simp only [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  rw [he]

end
end SecondPinching
