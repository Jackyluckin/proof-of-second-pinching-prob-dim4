import SecondPinching.ImmersionDivergenceBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The coordinate components of a vector whose orthonormal components are v
are B^t v. This is the differentiated change-of-components identity. -/
theorem transpose_connection_vector_identity (B D C O : Matrix4) (v w : Vector4)
    (hB : O*B=D+B*C) (hO : Oᵀ = -O) :
    Dᵀ*ᵥv+Bᵀ*ᵥw+Cᵀ*ᵥ(Bᵀ*ᵥv)=Bᵀ*ᵥ(w-O*ᵥv) := by
  have hd : D=O*B-B*C := by rw [hB,add_sub_cancel_right]
  rw [hd]
  funext i
  simp only [Matrix.transpose_sub,Matrix.transpose_mul,hO,Matrix.mulVec,dotProduct,
    Matrix.mul_apply,Matrix.transpose_apply,Matrix.sub_apply,Matrix.neg_apply,Pi.add_apply,Pi.sub_apply,
    Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
  ring

/-- Reordering the coordinate-direction trace recovers the trace in the
orthonormal basis. No assumption about orientation enters. -/
theorem frame_divergence_sum_identity (B P : Matrix4) (O : Fin 4 → Matrix4) (v : Vector4) :
    (∑ i, (Bᵀ*ᵥ((fun r => P r i)-O i*ᵥv)) i) =
      ∑ r, ((∑ i, B r i*P r i)-∑ s, (∑ i, B r i*O i r s)*v s) := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.sub_apply,
    Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
  ring

theorem scalar_fderiv_coordinate_expansion (u : Chart4 → ℝ) (x v : Chart4) :
    fderiv ℝ u x v=∑ i, v i*fderiv ℝ u x (coordinateUnit i) := by
  conv_lhs => rw [chart4_coordinate_expansion v]
  simp only [map_sum,map_smul,smul_eq_mul]

end
end SecondPinching
