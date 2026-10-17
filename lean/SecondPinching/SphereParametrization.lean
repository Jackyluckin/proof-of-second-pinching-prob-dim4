import SecondPinching.GlobalSphereImmersion
import SecondPinching.ImmersionNormal

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u

/-- Local immersion data before any choice of a unit normal. -/
structure SphereParametrization where
  domain : Set Chart4
  isOpen_domain : IsOpen domain
  map : Chart4 → Ambient6
  smooth_map : ContDiffOn ℝ ∞ map domain
  injective_derivative : ∀ x ∈ domain, Function.Injective (fderiv ℝ map x)
  sphere : ∀ x ∈ domain, inner ℝ (map x) (map x)=1

def globalSphereParametrization {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] (F : GlobalSphereImmersion M) (p : M) : SphereParametrization where
  domain := (chartAt Chart4 p).target
  isOpen_domain := (chartAt Chart4 p).open_target
  map := globalImmersionCoordinateMap F p
  smooth_map := contDiffOn_globalImmersionCoordinateMap F p
  injective_derivative := globalImmersionCoordinateMap_injective_derivative F p
  sphere := fun x _ => globalImmersionCoordinate_sphere F p x

theorem parametrization_radial_tangent (F : SphereParametrization) (x : Chart4)
    (hx : x ∈ F.domain) (v : Chart4) : inner ℝ (F.map x) (fderiv ℝ F.map x v)=0 := by
  have hf := ((F.smooth_map x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => inner ℝ (F.map y) (F.map y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => F.sphere y hy)
  have h := congrArg (fun L : Chart4 →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜:=ℝ))
  rw [fderiv_inner_apply ℝ hf hf] at h
  simp only [fderiv_const_apply,zero_apply] at h
  have hc : inner ℝ (fderiv ℝ F.map x v) (F.map x) =
      inner ℝ (F.map x) (fderiv ℝ F.map x v) := real_inner_comm _ _
  rw [hc] at h
  linarith

/-- The five radial and tangent directions, before a sixth direction is
chosen. This map need not be onto the six-dimensional ambient space. -/
def parametrizationRadialTangentMap (F : SphereParametrization) (x : Chart4) :
    (ℝ × Chart4) →ₗ[ℝ] Ambient6 where
  toFun c := c.1 • F.map x + fderiv ℝ F.map x c.2
  map_add' a b := by simp [add_smul,add_assoc,add_left_comm,add_comm]
  map_smul' a b := by simp [smul_add,smul_smul]

end
end SecondPinching
