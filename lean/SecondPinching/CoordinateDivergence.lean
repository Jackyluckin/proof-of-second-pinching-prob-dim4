import SecondPinching.ImmersionVolumeDensity

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Ordinary Euclidean divergence in the four coordinate directions. -/
def coordinateDivergence (Y : Chart4 → Vector4) (x : Chart4) : ℝ :=
  ∑ i, fderiv ℝ (fun y => Y y i) x (coordinateUnit i)

/-- Trace of the actual induced covariant derivative in a coordinate basis.
The vector indices here are contravariant coordinate components. -/
def immersionCoordinateDivergence (F : LocalSphereImmersion) (Y : Chart4 → Vector4) (x : Chart4) : ℝ :=
  ∑ i, (fderiv ℝ (fun y => Y y i) x (coordinateUnit i)+
    ∑ j, immersionChristoffel F.map x i j i*Y x j)

/-- Metric compatibility and torsion-freeness give the density formula.
Both facts are proved for the actual induced connection before this theorem. -/
theorem immersionCoordinateDivergence_density (F : LocalSphereImmersion) (Y : Chart4 → Vector4)
    (x : Chart4) (hx : x ∈ F.domain) (hY : DifferentiableAt ℝ Y x) :
    coordinateDivergence (fun y => immersionVolumeDensity F y • Y y) x =
      immersionVolumeDensity F x*immersionCoordinateDivergence F Y x := by
  have hr := (((contDiffOn_immersionVolumeDensity F) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hy (i : Fin 4) := differentiableAt_pi.mp hY i
  have hd (i : Fin 4) :
      fderiv ℝ (fun y => immersionVolumeDensity F y*Y y i) x (coordinateUnit i) =
        immersionVolumeDensity F x*fderiv ℝ (fun y => Y y i) x (coordinateUnit i)+
        Y x i*(immersionVolumeDensity F x*∑ j, immersionChristoffel F.map x j j i) := by
    rw [fderiv_fun_mul hr (hy i)]
    simp only [add_apply,smul_apply,smul_eq_mul,immersionVolumeDensity_derivative F x hx i]
  unfold coordinateDivergence immersionCoordinateDivergence
  simp only [Pi.smul_apply,smul_eq_mul,hd,Finset.sum_add_distrib,mul_add,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [immersionChristoffel_symmetric F x hx i i j]
  ring

end
end SecondPinching
