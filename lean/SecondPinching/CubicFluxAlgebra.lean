import SecondPinching.TracePowerContractions

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- Trace reversal for three symmetric matrices is used before any diagonalization. -/
theorem trace_symmetric_three_reverse (A U V : Matrix4)
    (hA : A.IsSymm) (hU : U.IsSymm) (hV : V.IsSymm) :
    Matrix.trace (U*A*V) = Matrix.trace (A*U*V) := by
  have ht := Matrix.trace_transpose (A*U*V)
  simp only [Matrix.transpose_mul,hA.eq,hU.eq,hV.eq,← Matrix.mul_assoc] at ht
  rw [Matrix.trace_mul_cycle U A V]
  exact ht

theorem matrixInner_squareVariation (A U V : Matrix4)
    (hA : A.IsSymm) (hU : U.IsSymm) (hV : V.IsSymm) :
    matrixInner (squareVariation A U) V = 2*matrixInner (A*U) V := by
  rw [matrixInner_eq_trace_mul _ _ hV,matrixInner_eq_trace_mul _ _ hV]
  simp only [squareVariation,add_mul,Matrix.trace_add]
  rw [trace_symmetric_three_reverse A U V hA hU hV]
  ring

/-- The contraction on the free derivative indices supplies the second h
factor in the manuscript's B contraction. -/
theorem weighted_slice_pairings (A : Matrix4) (T : Cubic4)
    (hA : A.IsSymm) (hT : CubicSymmetric T) :
    (∑ k, ∑ r, A k r*matrixInner (A*cubicLastSlice T k) (cubicLastSlice T r)) =
      intrinsicCubicB A T := by
  unfold intrinsicCubicB
  rw [← cubicInner_swap12_right T (cubicMatrixAction A T) hT]
  simp only [matrixInner,cubicLastSlice,Matrix.of_apply,Matrix.mul_apply,
    cubicInner,cubicMatrixAction,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro a _
  rw [hA.apply k r,cubicSymmetric_swap12 hT a j r]
  ring

theorem weighted_squareVariation_pairings (A : Matrix4) (T : Cubic4)
    (hA : A.IsSymm) (hT : CubicSymmetric T) :
    (∑ k, ∑ r, A k r*matrixInner (squareVariation A (cubicLastSlice T k)) (cubicLastSlice T r)) =
      2*intrinsicCubicB A T := by
  simp only [matrixInner_squareVariation _ _ _ hA
    (cubicLastSlice_symmetric T hT _) (cubicLastSlice_symmetric T hT _)]
  rw [← weighted_slice_pairings A T hA hT]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro r _; ring

theorem matrixInner_transposed_entries (A E : Matrix4) (hA : A.IsSymm) :
    (∑ k, ∑ r, A k r*E r k) = matrixInner A E := by
  unfold matrixInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro r _
  rw [hA.apply k r]

theorem cubic_trace_divergence_term (T : Cubic4) (v : Vector4)
    (hT : CubicSymmetric T) (htr : cubicTrace T=0) :
    (∑ k, (cubicLastSlice T k*ᵥv) k) = 0 := by
  simp only [Matrix.mulVec,dotProduct,cubicLastSlice,Matrix.of_apply]
  rw [Finset.sum_comm]
  have he (r : Fin 4) : (∑ k, T k r k*v r) = cubicTrace T r*v r := by
    unfold cubicTrace
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [cubicSymmetric_swap23 hT k r k]
  simp only [he,htr,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

end
end SecondPinching
