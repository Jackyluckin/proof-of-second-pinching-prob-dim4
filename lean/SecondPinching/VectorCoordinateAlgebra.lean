import SecondPinching.CoordinateVolumeChange
import SecondPinching.ImmersionScalarCalculus

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem fderiv_eq_coordinateJacobian_mulVec (φ : Chart4 → Chart4) (x v : Chart4) :
    fderiv ℝ φ x v=(coordinateJacobian φ x)ᵀ *ᵥ v := by
  rw [coordinateJacobian_eq_transpose_toMatrix,Matrix.transpose_transpose]
  exact (LinearMap.toMatrix'_mulVec (fderiv ℝ φ x).toLinearMap v).symm

theorem matrix_row_mul (A B : Matrix4) (i : Fin 4) : (A*B) i=Bᵀ *ᵥ A i := by
  funext j
  simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  apply Finset.sum_congr rfl; intro k _; ring

/-- Components in the two orthonormal frames yield the contravariant
coordinate transition law. Orthogonality is used as Q^t Q=I. -/
theorem vector_frame_to_coordinate_transition (B B' J Q : Matrix4)
    (hQ : OrthogonalFrame Q) (hB : B'*J=Q*B) (v : Vector4) :
    Bᵀ *ᵥ v=Jᵀ *ᵥ (B'ᵀ *ᵥ frameVector Q v) := by
  symm
  calc
    _ = (B'*J)ᵀ *ᵥ frameVector Q v := by rw [Matrix.transpose_mul,Matrix.mulVec_mulVec]
    _ = (Q*B)ᵀ *ᵥ frameVector Q v := by rw [hB]
    _ = Bᵀ *ᵥ v := by
      rw [Matrix.transpose_mul,← Matrix.mulVec_mulVec]
      change Bᵀ *ᵥ frameVector Qᵀ (frameVector Q v)=_
      rw [frameVector_inverse Q hQ]

theorem scalar_gradient_frame_transition (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F) (e' : LocalImmersionFrame G)
    (u v : Chart4 → ℝ) (x : Chart4) (hu : DifferentiableAt ℝ u (P.map x))
    (hP : DifferentiableAt ℝ P.map x) (hg : v =ᶠ[𝓝 x] u ∘ P.map)
    (Q : Matrix4) (hB : e'.coefficients x * coordinateJacobian P.map x=Q*e.coefficients (P.map x)) :
    immersionScalarGradient G e' v x=frameVector Q (immersionScalarGradient F e u (P.map x)) := by
  have hd (i : Fin 4) : fderiv ℝ P.map x (e'.coefficients x i) =
      ∑ r, Q i r • e.coefficients (P.map x) r := by
    rw [fderiv_eq_coordinateJacobian_mulVec,← matrix_row_mul,hB]
    funext a
    simp only [Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  funext i
  unfold immersionScalarGradient
  rw [hg.fderiv_eq,fderiv_comp x hu hP]
  change fderiv ℝ u (P.map x) (fderiv ℝ P.map x (e'.coefficients x i)) = _
  rw [hd i]
  simp only [map_sum,map_smul,smul_eq_mul,frameVector,Matrix.mulVec,dotProduct]

end
end SecondPinching
