import SecondPinching.ImmersionCoordinates
import Mathlib.Geometry.Manifold.ImmersionDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Manifold ContDiff Topology
namespace SecondPinching
noncomputable section
universe u

/-- A smooth immersion of a four-manifold into the unit sphere, represented
by its ambient map. Only the derivative is required to be injective. -/
structure GlobalSphereImmersion (M : Type u) [TopologicalSpace M] [ChartedSpace Chart4 M] where
  map : M → Ambient6
  smooth : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,Ambient6) ∞ map
  injective_derivative : ∀ p, Function.Injective (mfderiv 𝓘(ℝ,Chart4) 𝓘(ℝ,Ambient6) map p)
  sphere : ∀ p, inner ℝ (map p) (map p)=1

variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]

/-- The actual coordinate representative is composition with the inverse
of a chart of the given manifold. No normal or frame has yet been chosen. -/
def globalImmersionCoordinateMap (F : GlobalSphereImmersion M) (p : M) : Chart4 → Ambient6 :=
  F.map ∘ (chartAt Chart4 p).symm

theorem globalImmersionCoordinate_sphere (F : GlobalSphereImmersion M) (p : M) (x : Chart4) :
    inner ℝ (globalImmersionCoordinateMap F p x) (globalImmersionCoordinateMap F p x)=1 :=
  F.sphere _

variable [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem contDiffOn_globalImmersionCoordinateMap (F : GlobalSphereImmersion M) (p : M) :
    ContDiffOn ℝ ∞ (globalImmersionCoordinateMap F p) (chartAt Chart4 p).target := by
  exact (F.smooth.comp_contMDiffOn (contMDiffOn_chart_symm (I:=𝓘(ℝ,Chart4)) (x:=p))).contDiffOn

theorem globalImmersionCoordinateMap_injective_derivative (F : GlobalSphereImmersion M)
    (p : M) (x : Chart4) (hx : x ∈ (chartAt Chart4 p).target) :
    Function.Injective (fderiv ℝ (globalImmersionCoordinateMap F p) x) := by
  have he := mdifferentiable_chart (I:=𝓘(ℝ,Chart4)) p
  have hg := he.mdifferentiableAt_symm hx
  have hf := F.smooth.mdifferentiableAt (by simp) (x:=(chartAt Chart4 p).symm x)
  unfold globalImmersionCoordinateMap
  rw [← mfderiv_eq_fderiv,mfderiv_comp x hf hg]
  exact (F.injective_derivative _).comp (he.symm.mfderiv_injective hx)

end
end SecondPinching
