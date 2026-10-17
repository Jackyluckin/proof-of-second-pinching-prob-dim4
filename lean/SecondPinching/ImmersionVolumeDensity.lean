import SecondPinching.DeterminantDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Positive coordinate volume density of the actual induced metric.
It depends on the immersion map, not on a chosen normal or orthonormal frame. -/
def immersionVolumeDensity (F : LocalSphereImmersion) (x : Chart4) : ℝ :=
  Real.sqrt (immersionMetric F.map x).det

theorem immersionVolumeDensity_pos (F : LocalSphereImmersion) (x : Chart4) (hx : x ∈ F.domain) :
    0 < immersionVolumeDensity F x := by
  apply Real.sqrt_pos.mpr
  exact (immersionMetric_posDef F.map x (F.injective_derivative x hx)).det_pos

theorem immersionVolumeDensity_sq (F : LocalSphereImmersion) (x : Chart4) (hx : x ∈ F.domain) :
    (immersionVolumeDensity F x)^2=(immersionMetric F.map x).det :=
  Real.sq_sqrt ((immersionMetric_posDef F.map x (F.injective_derivative x hx)).det_pos.le)

theorem contDiffOn_immersionVolumeDensity (F : LocalSphereImmersion) :
    ContDiffOn ℝ ∞ (immersionVolumeDensity F) F.domain := by
  apply (contDiffOn_matrix4_det (contDiffOn_immersionMetric F.isOpen_domain F.smooth_map)).sqrt
  intro x hx
  exact immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx)

theorem immersionMetric_det_derivative (F : LocalSphereImmersion) (x : Chart4) (hx : x ∈ F.domain)
    (k : Fin 4) :
    fderiv ℝ (fun y => (immersionMetric F.map y).det) x (coordinateUnit k) =
      2*(immersionMetric F.map x).det*
        Matrix.trace (coordinateConnectionMatrix (immersionChristoffel F.map) x k) := by
  have hg := (((contDiffOn_immersionMetric F.isOpen_domain F.smooth_map) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [fderiv_matrix_det _ _ _ hg,immersionMetric_matrix_derivative F x hx k,
    determinant_metric_variation]

/-- The density derivative is derived from the actual metric and connection;
it is not imposed as a volume-compatibility premise. -/
theorem immersionVolumeDensity_derivative (F : LocalSphereImmersion) (x : Chart4) (hx : x ∈ F.domain)
    (k : Fin 4) :
    fderiv ℝ (immersionVolumeDensity F) x (coordinateUnit k) =
      immersionVolumeDensity F x*∑ i, immersionChristoffel F.map x i i k := by
  have hd := (((contDiffOn_matrix4_det (contDiffOn_immersionMetric F.isOpen_domain F.smooth_map)) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hn := immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx)
  have hp := immersionVolumeDensity_pos F x hx
  unfold immersionVolumeDensity
  rw [fderiv_sqrt hd hn]
  simp only [smul_apply,smul_eq_mul,immersionMetric_det_derivative F x hx k]
  change (1/(2*immersionVolumeDensity F x))*(2*(immersionMetric F.map x).det*
    (∑ i, immersionChristoffel F.map x i i k)) =
    immersionVolumeDensity F x*(∑ i, immersionChristoffel F.map x i i k)
  calc
    _ = (1/(2*immersionVolumeDensity F x))*(2*(immersionVolumeDensity F x)^2*
        (∑ i, immersionChristoffel F.map x i i k)) :=
      congrArg (fun d : ℝ => (1/(2*immersionVolumeDensity F x))*(2*d*
        (∑ i, immersionChristoffel F.map x i i k))) (immersionVolumeDensity_sq F x hx).symm
    _ = _ := by field_simp

/-- The absolute determinant, rather than an orientation sign, is the
coordinate factor for this density. -/
theorem sqrt_det_frameMatrix (B g : Matrix4) :
    Real.sqrt (frameMatrix B g).det=|B.det| * Real.sqrt g.det := by
  have he : (frameMatrix B g).det=(B.det)^2*g.det := by
    simp only [frameMatrix_eq_conjugate,Matrix.det_mul,Matrix.det_transpose]
    ring
  rw [he,Real.sqrt_mul (sq_nonneg B.det),Real.sqrt_sq_eq_abs]

end
end SecondPinching
