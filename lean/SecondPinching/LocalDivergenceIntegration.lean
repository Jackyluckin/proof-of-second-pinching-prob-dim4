import SecondPinching.ImmersionDivergenceCoordinates
import SecondPinching.CompactCoordinateDivergence

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The coordinate vector density to which Euclidean Stokes is applied.
The cutoff has compact support inside the immersion domain. -/
def immersionCutoffFlux (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (χ : Chart4 → ℝ) (X : Chart4 → Vector4) (x : Chart4) : Vector4 :=
  immersionVolumeDensity F x •
    immersionVectorCoordinates F e (fun y => χ y • X y) x

theorem immersionCutoffFlux_eq_zero (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (χ : Chart4 → ℝ) (X : Chart4 → Vector4) (x : Chart4) (hχ : χ x=0) :
    immersionCutoffFlux F e χ X x=0 := by
  simp only [immersionCutoffFlux,immersionVectorCoordinates,hχ,zero_smul,Matrix.mulVec_zero,smul_zero]

theorem hasCompactSupport_immersionCutoffFlux (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (χ : Chart4 → ℝ) (X : Chart4 → Vector4) (hc : HasCompactSupport χ) :
    HasCompactSupport (immersionCutoffFlux F e χ X) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (immersionCutoffFlux_eq_zero F e χ X x (image_eq_zero_of_notMem_tsupport hn))

theorem contDiff_immersionCutoffFlux (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (χ : Chart4 → ℝ) (X : Chart4 → Vector4) (hχ : ContDiff ℝ ∞ χ)
    (hX : ContDiffOn ℝ ∞ X F.domain) (hs : tsupport χ ⊆ F.domain) :
    ContDiff ℝ ∞ (immersionCutoffFlux F e χ X) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hd := F.isOpen_domain.mem_nhds (hs hx)
    have hr := ((contDiffOn_immersionVolumeDensity F) x (hs hx)).contDiffAt hd
    have hb := (e.smooth x (hs hx)).contDiffAt hd
    have hv := (hX x (hs hx)).contDiffAt hd
    have hc := hχ.contDiffAt (x := x)
    unfold immersionCutoffFlux immersionVectorCoordinates Matrix.mulVec dotProduct
    simp only [Matrix.transpose_apply,Pi.smul_apply,smul_eq_mul]
    fun_prop
  · apply contDiffAt_const.congr_of_eventuallyEq
    exact (notMem_tsupport_iff_eventuallyEq.mp hx).mono
      (fun y hy => immersionCutoffFlux_eq_zero F e χ X y hy)

/-- The product rule is established on the domain. Outside it the cutoff
and its derivative vanish on a neighbourhood, so both sides are zero. -/
theorem coordinateDivergence_immersionCutoffFlux (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (χ : Chart4 → ℝ) (X : Chart4 → Vector4)
    (hχ : ContDiff ℝ ∞ χ) (hX : ContDiffOn ℝ ∞ X F.domain)
    (hs : tsupport χ ⊆ F.domain) (x : Chart4) :
    coordinateDivergence (immersionCutoffFlux F e χ X) x =
      immersionVolumeDensity F x * (χ x * immersionVectorDivergence F e X x +
        immersionScalarGradient F e χ x ⬝ᵥ X x) := by
  by_cases hx : x ∈ F.domain
  · have hc := (hχ.differentiable (by simp)) x
    have hv := ((hX x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    change coordinateDivergence (fun y => immersionVolumeDensity F y •
      immersionVectorCoordinates F e (fun z => χ z • X z) y) x = _
    exact (immersionVectorDivergence_density F e (fun y => χ y • X y) x hx (hc.smul hv)).trans
      (congrArg (fun a : ℝ => immersionVolumeDensity F x * a)
        (immersionVectorDivergence_smul F e χ X x hc hv))
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have hz := image_eq_zero_of_notMem_tsupport hn
    have hd := fderiv_of_notMem_tsupport ℝ hn
    have he : immersionCutoffFlux F e χ X =ᶠ[𝓝 x] fun _ => 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).mono
        (fun y hy => immersionCutoffFlux_eq_zero F e χ X y hy)
    have h0 : coordinateDivergence (immersionCutoffFlux F e χ X) x=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hei : (fun y => immersionCutoffFlux F e χ X y i) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        he.mono (fun y hy => congrFun hy i)
      rw [hei.fderiv_eq]
      simp
    rw [h0]
    simp only [hz,zero_mul,zero_add,immersionScalarGradient,hd,zero_apply,dotProduct,
      zero_mul,Finset.sum_const_zero,mul_zero]

/-- Local integration by parts for the actual induced metric. Only the
cutoff, not the vector field, is required to have compact support. -/
theorem integral_immersionDivergence_cutoff (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (χ : Chart4 → ℝ) (X : Chart4 → Vector4)
    (hχ : ContDiff ℝ ∞ χ) (hX : ContDiffOn ℝ ∞ X F.domain)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ F.domain) :
    (∫ x : Chart4, immersionVolumeDensity F x *
      (χ x * immersionVectorDivergence F e X x + immersionScalarGradient F e χ x ⬝ᵥ X x))=0 := by
  have he : (fun x => immersionVolumeDensity F x *
      (χ x * immersionVectorDivergence F e X x + immersionScalarGradient F e χ x ⬝ᵥ X x)) =
      coordinateDivergence (immersionCutoffFlux F e χ X) := by
    funext x
    exact (coordinateDivergence_immersionCutoffFlux F e χ X hχ hX hs x).symm
  rw [he]
  exact integral_coordinateDivergence_eq_zero _ (contDiff_immersionCutoffFlux F e χ X hχ hX hs)
    (hasCompactSupport_immersionCutoffFlux F e χ X hc)

theorem integral_immersionLaplacian_cutoff (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (χ u : Chart4 → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiffOn ℝ ∞ u F.domain)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ F.domain) :
    (∫ x : Chart4, immersionVolumeDensity F x *
      (χ x * immersionScalarLaplacian F e u x +
        immersionScalarGradient F e χ x ⬝ᵥ immersionScalarGradient F e u x))=0 :=
  integral_immersionDivergence_cutoff F e χ (immersionScalarGradient F e u) hχ
    (contDiffOn_immersionScalarGradient F e u hu) hc hs

/-- A local scalar multiple of a divergence inherits the cutoff formula.
The representation is only used on the immersion domain. -/
theorem integral_immersionCorrection_cutoff (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (χ L : Chart4 → ℝ) (X : Chart4 → Vector4) (c : ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hX : ContDiffOn ℝ ∞ X F.domain)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ F.domain)
    (hL : ∀ x ∈ F.domain, L x=c * immersionVectorDivergence F e X x) :
    (∫ x : Chart4, immersionVolumeDensity F x *
      (χ x * L x + c * (immersionScalarGradient F e χ x ⬝ᵥ X x)))=0 := by
  have he (x : Chart4) : immersionVolumeDensity F x *
      (χ x * L x + c * (immersionScalarGradient F e χ x ⬝ᵥ X x)) =
      c * (immersionVolumeDensity F x *
        (χ x * immersionVectorDivergence F e X x + immersionScalarGradient F e χ x ⬝ᵥ X x)) := by
    by_cases hx : x ∈ F.domain
    · rw [hL x hx]; ring
    · have hn : x ∉ tsupport χ := fun h => hx (hs h)
      have hz := image_eq_zero_of_notMem_tsupport hn
      have hd := fderiv_of_notMem_tsupport ℝ hn
      simp only [hz,zero_mul,zero_add,immersionScalarGradient,hd,zero_apply,dotProduct,
        Finset.sum_const_zero,mul_zero]
  simp_rw [he]
  rw [integral_const_mul,integral_immersionDivergence_cutoff F e χ X hχ hX hc hs,mul_zero]

end
end SecondPinching
