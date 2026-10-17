import SecondPinching.GlobalDivergenceTheorem
import SecondPinching.NaturalCoordinateFields

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section

theorem immersionScalarGradient_congr_germ (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u v : Chart4 → ℝ) (x : Chart4) (he : u =ᶠ[𝓝 x] v) :
    immersionScalarGradient F e u =ᶠ[𝓝 x] immersionScalarGradient F e v := by
  filter_upwards [he.fderiv (𝕜:=ℝ)] with y hy
  funext i
  exact congrArg (fun L : Chart4 →L[ℝ] ℝ => L (e.coefficients y i)) hy

theorem immersionScalarLaplacian_congr_germ (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (u v : Chart4 → ℝ) (x : Chart4) (he : u =ᶠ[𝓝 x] v) :
    immersionScalarLaplacian F e u x=immersionScalarLaplacian F e v x :=
  immersionVectorDivergence_congr_germ F e _ _ x (immersionScalarGradient_congr_germ F e u v x he)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem scalarInImmersionChart_eq_local (F : GlobalSphereImmersion M)
    (u : M → ℝ) (v : M → Chart4 → ℝ)
    (hr : ∀ p y, y ∈ globalImmersionLocalSource F p → u y=v p (chartAt Chart4 p y))
    (p : M) (x : Chart4) (hx : x ∈ (globalImmersionLocal F p).domain) :
    scalarInImmersionChart p u x=v p x := by
  obtain ⟨hy,he⟩ := inverse_coordinate_mem_localSource F p x hx
  have h := hr p ((chartAt Chart4 p).symm x) hy
  rw [he] at h
  exact h

theorem scalarInImmersionChart_local_germ (F : GlobalSphereImmersion M)
    (u : M → ℝ) (v : M → Chart4 → ℝ)
    (hr : ∀ p y, y ∈ globalImmersionLocalSource F p → u y=v p (chartAt Chart4 p y))
    (p : M) (x : Chart4) (hx : x ∈ (globalImmersionLocal F p).domain) :
    scalarInImmersionChart p u =ᶠ[𝓝 x] v p :=
  Filter.eventuallyEq_of_mem ((globalImmersionLocal F p).isOpen_domain.mem_nhds hx)
    (fun y hy => scalarInImmersionChart_eq_local F u v hr p y hy)

theorem gradientCoordinateVector_divergence_of_representation (F : GlobalSphereImmersion M)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) (v : M → Chart4 → ℝ)
    (hr : ∀ p y, y ∈ globalImmersionLocalSource F p → u y=v p (chartAt Chart4 p y))
    (p : M) (x : Chart4) (hx : x ∈ (globalImmersionLocal F p).domain) :
    immersionCoordinateDivergence (globalImmersionLocal F p) ((gradientCoordinateVector F u hu).components p) x =
      immersionScalarLaplacian (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (v p) x := by
  rw [gradientCoordinateVector_divergence F u hu p x hx]
  exact immersionScalarLaplacian_congr_germ _ _ _ _ x (scalarInImmersionChart_local_germ F u v hr p x hx)

end
end SecondPinching
