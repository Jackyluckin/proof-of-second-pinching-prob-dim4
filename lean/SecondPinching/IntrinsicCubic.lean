import SecondPinching.FrameQuantities
import SecondPinching.TrialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! General-frame expressions for eq:abc and eq:d. The contraction in b acts
on two tensor slots. All sums and pairings retain ordered indices. -/

/-- Apply A to the last two slots; the first slot is left unchanged. -/
def cubicMatrixAction (A : Matrix4) (τ : Cubic4) : Cubic4 :=
  fun i j k => (A * Matrix.of (τ i) * Aᵀ) j k

/-- The scalar a, expressed without a principal frame. -/
def intrinsicCubicA (A : Matrix4) (τ : Cubic4) : ℝ :=
  Matrix.trace (A^2 * cubicGramMatrix τ)

/-- The scalar b, expressed as the pairing with a two-slot action. -/
def intrinsicCubicB (A : Matrix4) (τ : Cubic4) : ℝ :=
  cubicInner τ (cubicMatrixAction A τ)

/-- The scalar c, expressed without a principal frame. -/
def intrinsicCubicC (A : Matrix4) (τ : Cubic4) : ℝ :=
  Matrix.trace (A * cubicGramMatrix τ)

/-- The vector d is the A-squared trace, not the A-weighted trace constraint. -/
def intrinsicCubicD (A : Matrix4) (τ : Cubic4) : Vector4 :=
  cubicWeightedTrace (A^2) τ

theorem frameMatrix_transpose (O A : Matrix4) :
    frameMatrix O Aᵀ = (frameMatrix O A)ᵀ := by
  simp only [frameMatrix_eq_conjugate, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

theorem frameMatrix_mulVec (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (v : Vector4) :
    frameMatrix O A *ᵥ frameVector O v = frameVector O (A *ᵥ v) := by
  simp only [frameMatrix_eq_conjugate, frameVector, Matrix.mulVec_mulVec]
  have he : O * A * Oᵀ * O = O * A := by
    calc
      O * A * Oᵀ * O = O * A * (Oᵀ * O) := by noncomm_ring
      _ = O * A := by rw [hO, mul_one]
  rw [he]

theorem frame_cubicMatrixAction (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    cubicMatrixAction (frameMatrix O A) (frameCubic O τ) =
      frameCubic O (cubicMatrixAction A τ) := by
  funext i
  change frameMatrix O A * Matrix.of (frameCubic O τ i) * (frameMatrix O A)ᵀ =
    frameCubic O (cubicMatrixAction A τ) i
  rw [frameCubic_slice, frameCubic_slice]
  change frameMatrix O A * (∑ a, O i a • frameMatrix O (τ a) : Matrix4) *
    (frameMatrix O A)ᵀ = ∑ a, O i a • frameMatrix O (cubicMatrixAction A τ a)
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  erw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  change _ = frameMatrix O (A * Matrix.of (τ a) * Aᵀ)
  rw [frameMatrix_mul O hO, frameMatrix_mul O hO, frameMatrix_transpose]
  rfl

theorem frame_intrinsicCubicA (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicA (frameMatrix O A) (frameCubic O τ) = intrinsicCubicA A τ := by
  unfold intrinsicCubicA
  rw [frame_cubicGramMatrix O hO, ← frameMatrix_pow O hO,
    ← frameMatrix_mul O hO, frameMatrix_trace O hO]

theorem frame_intrinsicCubicB (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicB (frameMatrix O A) (frameCubic O τ) = intrinsicCubicB A τ := by
  unfold intrinsicCubicB
  rw [frame_cubicMatrixAction O hO, frameCubic_inner O hO]

theorem frame_intrinsicCubicC (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicC (frameMatrix O A) (frameCubic O τ) = intrinsicCubicC A τ := by
  unfold intrinsicCubicC
  rw [frame_cubicGramMatrix O hO, ← frameMatrix_mul O hO, frameMatrix_trace O hO]

theorem frame_intrinsicCubicD (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicD (frameMatrix O A) (frameCubic O τ) =
      frameVector O (intrinsicCubicD A τ) :=
  frame_cubicD_intrinsic O hO A τ

theorem intrinsicCubicA_diagonal (μ : Vector4) (τ : Cubic4) (hτ : CubicSymmetric τ) :
    intrinsicCubicA (Matrix.diagonal μ) τ = cubicA μ τ := by
  simp [intrinsicCubicA, cubicA, Matrix.diagonal_pow, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.diagonal_apply, cubicGramMatrix, Fin.sum_univ_succ,
    cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
  ring

theorem intrinsicCubicB_diagonal (μ : Vector4) (τ : Cubic4) (hτ : CubicSymmetric τ) :
    intrinsicCubicB (Matrix.diagonal μ) τ = cubicB μ τ := by
  simp [intrinsicCubicB, cubicMatrixAction, cubicInner, cubicB, Matrix.mul_apply,
    Matrix.diagonal_apply, Fin.sum_univ_succ,
    cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
  ring

theorem intrinsicCubicC_diagonal (μ : Vector4) (τ : Cubic4) (hτ : CubicSymmetric τ) :
    intrinsicCubicC (Matrix.diagonal μ) τ = cubicC μ τ := by
  simp [intrinsicCubicC, cubicC, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.diagonal_apply, cubicGramMatrix, Fin.sum_univ_succ,
    cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
  ring

theorem intrinsicCubicD_diagonal (μ : Vector4) (τ : Cubic4) :
    intrinsicCubicD (Matrix.diagonal μ) τ = cubicD μ τ :=
  (cubicD_eq_weightedTrace μ τ).symm

end
end SecondPinching
