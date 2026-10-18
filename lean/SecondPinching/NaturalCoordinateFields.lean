import SecondPinching.ImmersionCoordinateVector
import SecondPinching.GradientCoordinateTransition
import SecondPinching.CubicFluxCoordinateTransition
import SecondPinching.ImmersionCorrectionIntegration
import SecondPinching.CoordinateCutoffIntegration

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section

theorem contDiffOn_immersionVectorCoordinates (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (X : Chart4 → Vector4) (hX : ContDiffOn ℝ ∞ X F.domain) :
    ContDiffOn ℝ ∞ (immersionVectorCoordinates F e X) F.domain := by
  have hb := e.smooth
  unfold immersionVectorCoordinates Matrix.mulVec dotProduct
  simp only [Matrix.transpose_apply]
  fun_prop

theorem immersionCoordinateDivergence_const_smul (F : LocalSphereImmersion)
    (Y : Chart4 → Vector4) (c : ℝ) (x : Chart4) (hY : DifferentiableAt ℝ Y x) :
    immersionCoordinateDivergence F (fun y => c • Y y) x=c*immersionCoordinateDivergence F Y x := by
  exact (immersionCoordinateDivergence_smul F (fun _ => c) Y x (differentiableAt_const c) hY).trans
    (by simp)

theorem immersionCoordinateDivergence_congr_germ (F : LocalSphereImmersion)
    (Y Z : Chart4 → Vector4) (x : Chart4) (he : Y =ᶠ[𝓝 x] Z) :
    immersionCoordinateDivergence F Y x=immersionCoordinateDivergence F Z x := by
  have h0 : Y x=Z x := he.eq_of_nhds
  have hc (i : Fin 4) : (fun y => Y y i) =ᶠ[𝓝 x] fun y => Z y i :=
    he.mono (fun y hy => congrFun hy i)
  simp only [immersionCoordinateDivergence,(hc _).fderiv_eq,h0]

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- The actual gradient of a globally smooth scalar, in coordinate components.
The transition law is proved from the actual metric frames and the chain rule. -/
def gradientCoordinateVector (F : GlobalSphereImmersion M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) : ImmersionCoordinateVector F where
  components := fun p => immersionVectorCoordinates (globalImmersionLocal F p) (globalImmersionLocalFrame F p)
    (immersionScalarGradient (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (scalarInImmersionChart p u))
  smooth := fun p => contDiffOn_immersionVectorCoordinates _ _ _
    (contDiffOn_immersionScalarGradient _ _ _ (scalarInImmersionChart_smooth F p u hu))
  transition := by
    intro p q x hp hq
    let P := globalImmersionReparametrization F p q
    obtain ⟨hx,he⟩ := globalImmersionReparametrization_point F p q x hp hq
    have hd := (((scalarInImmersionChart_smooth F p u hu) _ (P.mapsTo hx)).contDiffAt
      ((globalImmersionLocal F p).isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
    have h := immersionGradient_coordinate_components (globalImmersionLocal F p) (globalImmersionLocal F q)
      P (globalImmersionLocalFrame F p) (globalImmersionLocalFrame F q)
      (scalarInImmersionChart p u) (scalarInImmersionChart q u) (chartAt Chart4 q x) hx hq.2
      (globalImmersionReparametrization_germ F p q _ hx) hd
      (scalarInImmersionChart_transition_germ F p q u _ hx)
    rw [he] at h
    exact h

/-- The even raw flux h grad(f3)/3 is a genuine global tangent field,
although neither a global f3 nor a global unit normal is assumed. -/
def cubicFluxCoordinateVector (F : GlobalSphereImmersion M) : ImmersionCoordinateVector F where
  components := fun p => immersionVectorCoordinates (globalImmersionLocal F p) (globalImmersionLocalFrame F p)
    (immersionCubicFlux (globalImmersionLocal F p) (globalImmersionLocalFrame F p))
  smooth := fun p => contDiffOn_immersionVectorCoordinates _ _ _ (contDiffOn_immersionCubicFlux _ _)
  transition := by
    intro p q x hp hq
    obtain ⟨hx,he⟩ := globalImmersionReparametrization_point F p q x hp hq
    have h := immersionCubicFlux_coordinate_components (globalImmersionLocal F p) (globalImmersionLocal F q)
      (globalImmersionReparametrization F p q) (globalImmersionLocalFrame F p) (globalImmersionLocalFrame F q)
      (chartAt Chart4 q x) hx hq.2 (globalImmersionReparametrization_germ F p q _ hx)
    rw [he] at h
    exact h

def scaleCoordinateVector (F : GlobalSphereImmersion M) (c : ℝ) (Y : ImmersionCoordinateVector F) :
    ImmersionCoordinateVector F where
  components := fun p x => c • Y.components p x
  smooth := fun p => (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Chart4 => c)
    (globalImmersionLocal F p).domain).smul (Y.smooth p)
  transition := by
    intro p q x hp hq
    rw [map_smul]
    exact congrArg (fun v : Vector4 => c • v) (Y.transition p q x hp hq)

theorem gradientCoordinateVector_divergence (F : GlobalSphereImmersion M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) (p : M) (x : Chart4)
    (hx : x ∈ (globalImmersionLocal F p).domain) :
    immersionCoordinateDivergence (globalImmersionLocal F p) ((gradientCoordinateVector F u hu).components p) x =
      immersionScalarLaplacian (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (scalarInImmersionChart p u) x := by
  have h := contDiffOn_immersionScalarGradient (globalImmersionLocal F p) (globalImmersionLocalFrame F p)
    (scalarInImmersionChart p u) (scalarInImmersionChart_smooth F p u hu)
  exact (immersionCoordinateDivergence_eq_frame _ _ _ x hx
    ((h x hx).contDiffAt ((globalImmersionLocal F p).isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp))).trans
      (immersionVectorDivergence_gradient _ _ _ x)

theorem cubicFluxCoordinateVector_divergence (F : GlobalSphereImmersion M) (p : M) (x : Chart4)
    (hx : x ∈ (globalImmersionLocal F p).domain) :
    immersionCoordinateDivergence (globalImmersionLocal F p) ((cubicFluxCoordinateVector F).components p) x =
      immersionVectorDivergence (globalImmersionLocal F p) (globalImmersionLocalFrame F p)
        (immersionCubicFlux (globalImmersionLocal F p) (globalImmersionLocalFrame F p)) x := by
  have h := contDiffOn_immersionCubicFlux (globalImmersionLocal F p) (globalImmersionLocalFrame F p)
  exact immersionCoordinateDivergence_eq_frame _ _ _ x hx
    ((h x hx).contDiffAt ((globalImmersionLocal F p).isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp))

theorem scaleCoordinateVector_divergence (F : GlobalSphereImmersion M) (c : ℝ)
    (Y : ImmersionCoordinateVector F) (p : M) (x : Chart4) (hx : x ∈ (globalImmersionLocal F p).domain) :
    immersionCoordinateDivergence (globalImmersionLocal F p) ((scaleCoordinateVector F c Y).components p) x =
      c*immersionCoordinateDivergence (globalImmersionLocal F p) (Y.components p) x := by
  exact immersionCoordinateDivergence_const_smul (globalImmersionLocal F p) (Y.components p) c x
    (((Y.smooth p x hx).contDiffAt ((globalImmersionLocal F p).isOpen_domain.mem_nhds hx)).differentiableAt (by simp))

end
end SecondPinching
