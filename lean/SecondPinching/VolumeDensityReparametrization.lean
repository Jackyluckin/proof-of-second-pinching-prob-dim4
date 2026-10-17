import SecondPinching.ImmersionVolumeDensity
import SecondPinching.ImmersionReparametrization

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The coordinate density transforms by the absolute Jacobian determinant.
The row convention for the Jacobian and either orientation are both allowed. -/
theorem immersionVolumeDensity_reparametrized (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) :
    immersionVolumeDensity (reparametrizedImmersion F P) x =
      |(coordinateJacobian P.map x).det| * immersionVolumeDensity F (P.map x) := by
  unfold immersionVolumeDensity
  rw [reparametrized_metric F P x hx,sqrt_det_frameMatrix]

end
end SecondPinching
