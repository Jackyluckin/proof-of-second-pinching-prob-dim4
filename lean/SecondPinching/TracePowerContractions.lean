import SecondPinching.ImmersionTracePowers

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- Fix the derivative index of the fully symmetric cubic tensor. -/
def cubicLastSlice (T : Cubic4) (k : Fin 4) : Matrix4 := Matrix.of (fun i j => T i j k)

theorem cubicLastSlice_symmetric (T : Cubic4) (hT : CubicSymmetric T) (k : Fin 4) :
    (cubicLastSlice T k).IsSymm := by
  ext i j; exact cubicSymmetric_swap12 hT j i k

theorem cubicLastSlice_eq_first (T : Cubic4) (hT : CubicSymmetric T) (k : Fin 4) :
    cubicLastSlice T k = Matrix.of (T k) := by
  ext i j
  exact (cubicSymmetric_swap23 hT i j k).trans (cubicSymmetric_swap12 hT i k j)

theorem cubicGramMatrix_eq_sum_squares (T : Cubic4) (hT : CubicSymmetric T) :
    cubicGramMatrix T = ∑ k, cubicLastSlice T k*cubicLastSlice T k := by
  ext i j
  simp only [cubicGramMatrix,Matrix.sum_apply,Matrix.mul_apply,cubicLastSlice,Matrix.of_apply]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  rw [cubicSymmetric_swap12 hT i l k,cubicSymmetric_swap23 hT l i k,
    cubicSymmetric_swap12 hT l k i,cubicSymmetric_swap12 hT l j k,
    cubicSymmetric_swap23 hT j l k,cubicSymmetric_swap12 hT j k l,
    cubicSymmetric_swap23 hT k l j]

theorem matrixInner_squareVariation_self (A U : Matrix4) (hU : U.IsSymm) :
    matrixInner (squareVariation A U) U = 2*Matrix.trace (A*(U*U)) := by
  rw [matrixInner_eq_trace_mul _ _ hU]
  simp only [squareVariation,add_mul,Matrix.trace_add]
  rw [Matrix.trace_mul_cycle U A U,Matrix.trace_mul_comm (U*U) A,Matrix.mul_assoc]
  ring

theorem matrixInner_cubeVariation_self (A U : Matrix4) (hU : U.IsSymm) :
    matrixInner (cubeVariation A U) U =
      2*Matrix.trace (A^2*(U*U))+matrixInner (A*U*A) U := by
  rw [matrixInner_eq_trace_mul _ _ hU,matrixInner_eq_trace_mul _ _ hU]
  simp only [cubeVariation,add_mul,Matrix.trace_add]
  rw [Matrix.trace_mul_cycle U (A^2) U,Matrix.trace_mul_comm (U*U) (A^2)]
  simp only [Matrix.mul_assoc]
  ring

theorem trace_sum_slice_squares (A : Matrix4) (T : Cubic4) (hT : CubicSymmetric T) :
    (∑ k, Matrix.trace (A*(cubicLastSlice T k*cubicLastSlice T k))) =
      Matrix.trace (A*cubicGramMatrix T) := by
  rw [cubicGramMatrix_eq_sum_squares T hT,Matrix.mul_sum,Matrix.trace_sum]

theorem sum_squareVariation_pairings (A : Matrix4) (T : Cubic4) (hT : CubicSymmetric T) :
    (∑ k, matrixInner (squareVariation A (cubicLastSlice T k)) (cubicLastSlice T k)) =
      2*intrinsicCubicC A T := by
  simp only [matrixInner_squareVariation_self _ _ (cubicLastSlice_symmetric T hT _),
    ← Finset.mul_sum,trace_sum_slice_squares A T hT,intrinsicCubicC]

theorem intrinsicCubicB_eq_last_slices (A : Matrix4) (T : Cubic4)
    (hA : A.IsSymm) (hT : CubicSymmetric T) :
    (∑ k, matrixInner (A*cubicLastSlice T k*A) (cubicLastSlice T k)) = intrinsicCubicB A T := by
  unfold intrinsicCubicB cubicInner
  apply Finset.sum_congr rfl; intro k _
  rw [cubicLastSlice_eq_first T hT k,matrixInner_comm]
  change matrixInner (Matrix.of (T k)) (A*Matrix.of (T k)*A) =
    matrixInner (Matrix.of (T k)) (A*Matrix.of (T k)*Aᵀ)
  rw [hA.eq]

theorem sum_cubeVariation_pairings (A : Matrix4) (T : Cubic4)
    (hA : A.IsSymm) (hT : CubicSymmetric T) :
    (∑ k, matrixInner (cubeVariation A (cubicLastSlice T k)) (cubicLastSlice T k)) =
      2*intrinsicCubicA A T+intrinsicCubicB A T := by
  simp only [matrixInner_cubeVariation_self _ _ (cubicLastSlice_symmetric T hT _),
    Finset.sum_add_distrib,← Finset.mul_sum]
  rw [trace_sum_slice_squares _ T hT,intrinsicCubicB_eq_last_slices A T hA hT]
  rfl

theorem matrixInner_power_self (A : Matrix4) (hA : A.IsSymm) (n : ℕ) :
    matrixInner (A^n) A = Matrix.trace (A^(n+1)) := by
  rw [matrixInner_eq_trace_mul _ _ hA,pow_succ]

end
end SecondPinching
