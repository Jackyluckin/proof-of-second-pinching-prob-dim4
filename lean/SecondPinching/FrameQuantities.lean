import SecondPinching.FrameProjection
import SecondPinching.HessianQuantities

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The actual matrix-valued quantities already defined in the manuscript.
These transport identities do not impose a principal frame. -/

theorem frameMatrix_mul (Q : Matrix4) (hQ : OrthogonalFrame Q) (A B : Matrix4) :
    frameMatrix Q (A*B) = frameMatrix Q A * frameMatrix Q B := by
  simp only [frameMatrix_eq_conjugate]
  calc
    Q * (A*B) * Qᵀ = Q * A * (Qᵀ*Q) * B * Qᵀ := by rw [hQ]; noncomm_ring
    _ = Q * A * Qᵀ * (Q * B * Qᵀ) := by noncomm_ring

theorem frameMatrix_pow (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) (n : ℕ) :
    frameMatrix Q (A^n) = (frameMatrix Q A)^n := by
  induction n with
  | zero => simpa only [pow_zero] using frameMatrix_one Q hQ
  | succ n ih => rw [pow_succ,frameMatrix_mul Q hQ,ih,pow_succ]

theorem frame_cubicMoment (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    cubicMoment (frameMatrix Q A) = cubicMoment A := by
  unfold cubicMoment
  rw [← frameMatrix_pow Q hQ,frameMatrix_trace Q hQ]

theorem frame_quarticMoment (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    quarticMoment (frameMatrix Q A) = quarticMoment A := by
  unfold quarticMoment
  rw [← frameMatrix_pow Q hQ,frameMatrix_trace Q hQ]

theorem frame_normalizedPhi (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    normalizedPhi (frameMatrix Q A) = frameMatrix Q (normalizedPhi A) := by
  unfold normalizedPhi
  change _ = frameMatrixLinear Q _
  rw [map_sub,map_sub,map_smul,map_smul]
  change _ = frameMatrix Q (A^2)-cubicMoment A • frameMatrix Q A-(1/4 : ℝ) • frameMatrix Q 1
  rw [frameMatrix_pow Q hQ,frame_cubicMoment Q hQ,frameMatrix_one Q hQ]

theorem frame_phiNormSq (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    phiNormSq (frameMatrix Q A) = phiNormSq A := by
  unfold phiNormSq
  rw [frame_normalizedPhi Q hQ,frameMatrix_normSq Q hQ]

theorem frame_cubicGramMatrix (Q : Matrix4) (hQ : OrthogonalFrame Q) (τ : Cubic4) :
    cubicGramMatrix (frameCubic Q τ) = frameMatrix Q (cubicGramMatrix τ) := by
  ext k l
  change matrixInner (frameMatrix Q (fun a b => ∑ c, Q k c * τ a b c))
    (frameMatrix Q (fun a b => ∑ d, Q l d * τ a b d)) = _
  erw [frameMatrix_inner Q hQ]
  simp only [matrixInner,frameMatrix,cubicGramMatrix,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frame_vectorGramOperator (Q : Matrix4) (hQ : OrthogonalFrame Q) (τ : Cubic4) :
    vectorGramOperator (frameCubic Q τ) = frameMatrix Q (vectorGramOperator τ) := by
  unfold vectorGramOperator
  change _ = frameMatrixLinear Q _
  rw [map_add,map_smul,map_smul]
  change _ = (1/4 : ℝ) • frameMatrix Q 1+(9/16 : ℝ) • frameMatrix Q (cubicGramMatrix τ)
  rw [frameMatrix_one Q hQ,frame_cubicGramMatrix Q hQ]

theorem frame_hessianPsi (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) (τ : Cubic4) :
    hessianPsi (frameMatrix Q A) (frameCubic Q τ) = frameMatrix Q (hessianPsi A τ) := by
  unfold hessianPsi
  change _ = frameMatrixLinear Q _
  rw [map_sub,map_add,map_smul,map_smul]
  change _ = (1/4 : ℝ) • frameMatrix Q (A^2)+(3/16 : ℝ) • frameMatrix Q 1-
    frameMatrix Q (cubicGramMatrix τ)
  rw [frameMatrix_pow Q hQ,frameMatrix_one Q hQ,frame_cubicGramMatrix Q hQ]

theorem frame_hessianE (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    hessianE (frameMatrix Q A) (frameCubic Q τ) t = frameMatrix Q (hessianE A τ t) := by
  unfold hessianE
  change _ = frameMatrixLinear Q _
  rw [map_add,map_smul,map_smul]
  change _ = (1/2 : ℝ) • frameMatrix Q (normalizedPhi A)+t • frameMatrix Q (hessianPsi A τ)
  rw [frame_normalizedPhi Q hQ,frame_hessianPsi Q hQ]

theorem frame_matrixGramOperator (Q : Matrix4) (hQ : OrthogonalFrame Q) (A Y : Matrix4) :
    matrixGramOperator (frameMatrix Q A) (frameMatrix Q Y) = frameMatrix Q (matrixGramOperator A Y) := by
  unfold matrixGramOperator
  change _ = frameMatrixLinear Q _
  simp only [map_add,map_sub,map_smul]
  change _ = (1/6 : ℝ) • frameMatrix Q Y+
    (1/4 : ℝ) • (frameMatrix Q (A^2*Y)+frameMatrix Q (Y*A^2))-
    (1/6 : ℝ) • frameMatrix Q (A*Y*A)+
    ((7/36 : ℝ)*Matrix.trace (A*Y)) • frameMatrix Q A-
    ((1/12 : ℝ)*Matrix.trace (A^2*Y)) • frameMatrix Q 1
  simp only [frameMatrix_mul Q hQ,frameMatrix_pow Q hQ,frameMatrix_one Q hQ]
  rw [← frameMatrix_mul Q hQ A Y,frameMatrix_trace Q hQ,
    ← frameMatrix_pow Q hQ A 2,← frameMatrix_mul Q hQ (A^2) Y,frameMatrix_trace Q hQ]

/-- d in a principal frame is the intrinsic A-squared weighted trace. -/
theorem cubicD_eq_weightedTrace (μ : Vector4) (τ : Cubic4) :
    cubicD μ τ = cubicWeightedTrace ((Matrix.diagonal μ)^2) τ := by
  funext k
  simp [cubicD,cubicWeightedTrace,Matrix.diagonal_pow,Matrix.diagonal_apply]

/-- Covariance of the actual vector d, without any assumption that it vanishes. -/
theorem frame_cubicD_intrinsic (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) (τ : Cubic4) :
    cubicWeightedTrace ((frameMatrix Q A)^2) (frameCubic Q τ) =
      frameVector Q (cubicWeightedTrace (A^2) τ) := by
  rw [← frameMatrix_pow Q hQ,frameCubic_weightedTrace Q hQ]

end
end SecondPinching
