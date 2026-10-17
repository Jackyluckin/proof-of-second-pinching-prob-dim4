import SecondPinching.CoordinateDivergence
import SecondPinching.FrameDivergenceAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Coordinate components of a vector represented in the smooth orthonormal
frame. The rows of the frame matrix are coordinate vectors. -/
def immersionVectorCoordinates (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (X : Chart4 → Vector4) (x : Chart4) : Vector4 :=
  (e.coefficients x)ᵀ *ᵥ X x

theorem differentiableAt_immersionVectorCoordinates (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (X : Chart4 → Vector4) (x : Chart4)
    (hx : x ∈ F.domain) (hX : DifferentiableAt ℝ X x) :
    DifferentiableAt ℝ (immersionVectorCoordinates F e X) x := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  unfold immersionVectorCoordinates Matrix.mulVec dotProduct
  simp only [Matrix.transpose_apply]
  fun_prop

/-- The induced covariant derivative has the same vector components in both
bases. The connection identities are consequences of the actual immersion. -/
theorem immersionVectorCoordinates_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (X : Chart4 → Vector4) (x : Chart4)
    (hx : x ∈ F.domain) (hX : DifferentiableAt ℝ X x) (k : Fin 4) :
    (fun i => fderiv ℝ (fun y => immersionVectorCoordinates F e X y i) x (coordinateUnit k)) +
      (coordinateConnectionMatrix (immersionChristoffel F.map) x k)ᵀ *ᵥ
        immersionVectorCoordinates F e X x =
    (e.coefficients x)ᵀ *ᵥ
      ((fun r => fderiv ℝ (fun y => X y r) x (coordinateUnit k)) -
        immersionMovingConnection F e x k *ᵥ X x) := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hbt : DifferentiableAt ℝ (fun y => (e.coefficients y)ᵀ) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hb j) i
  have hd : (fun i => fderiv ℝ (fun y => immersionVectorCoordinates F e X y i) x
      (coordinateUnit k)) =
      (matrixDerivative e.coefficients x (coordinateUnit k))ᵀ *ᵥ X x +
        (e.coefficients x)ᵀ *ᵥ (fun r => fderiv ℝ (fun y => X y r) x (coordinateUnit k)) := by
    funext i
    exact fderiv_mulVec_component (fun y => (e.coefficients y)ᵀ) X x (coordinateUnit k) hbt hX i
  rw [hd]
  exact transpose_connection_vector_identity _ _ _ _ _ _
    (immersionMovingConnection_action F e x hx k) (immersionMovingConnection_skew F e x hx k)

theorem immersionCoordinateDivergence_eq_frame (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (X : Chart4 → Vector4) (x : Chart4)
    (hx : x ∈ F.domain) (hX : DifferentiableAt ℝ X x) :
    immersionCoordinateDivergence F (immersionVectorCoordinates F e X) x =
      immersionVectorDivergence F e X x := by
  unfold immersionCoordinateDivergence
  have he (i : Fin 4) := congrFun (immersionVectorCoordinates_derivative F e X x hx hX i) i
  simp only [Pi.add_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    coordinateConnectionMatrix] at he
  simp_rw [he]
  change (∑ i, ((e.coefficients x)ᵀ *ᵥ
    ((fun r => fderiv ℝ (fun y => X y r) x (coordinateUnit i)) -
      immersionMovingConnection F e x i *ᵥ X x)) i) = _
  rw [frame_divergence_sum_identity (e.coefficients x)
    (fun r i => fderiv ℝ (fun y => X y r) x (coordinateUnit i))
    (immersionMovingConnection F e x) (X x)]
  unfold immersionVectorDivergence
  apply Finset.sum_congr rfl; intro r _
  apply congrArg₂ (fun a b : ℝ => a-b)
  · exact (scalar_fderiv_coordinate_expansion (fun y => X y r) x (e.coefficients x r)).symm
  · apply Finset.sum_congr rfl; intro s _
    congr 1

/-- Local divergence with the actual induced volume density, valid without
choosing an orientation. -/
theorem immersionVectorDivergence_density (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (X : Chart4 → Vector4) (x : Chart4)
    (hx : x ∈ F.domain) (hX : DifferentiableAt ℝ X x) :
    coordinateDivergence (fun y => immersionVolumeDensity F y •
      immersionVectorCoordinates F e X y) x =
      immersionVolumeDensity F x * immersionVectorDivergence F e X x := by
  rw [immersionCoordinateDivergence_density F _ x hx
    (differentiableAt_immersionVectorCoordinates F e X x hx hX),
    immersionCoordinateDivergence_eq_frame F e X x hx hX]

end
end SecondPinching
