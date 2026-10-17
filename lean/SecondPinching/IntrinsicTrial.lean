import SecondPinching.IntrinsicCubic
import SecondPinching.IntrinsicAdjoint

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The actual trial variables of eq:choice in any orthonormal frame. B is
always B_(1/2), independently of the real parameter in B_t and Y_t. -/

def intrinsicHessianB0 (A : Matrix4) (τ : Cubic4) : Vector4 :=
  -(3/2 : ℝ) • (A *ᵥ intrinsicCubicD A τ)

def intrinsicTrialVector (A : Matrix4) (τ : Cubic4) : Vector4 :=
  (-7 : ℝ) • (A *ᵥ intrinsicCubicD A τ)

def intrinsicTrialBt (A : Matrix4) (τ : Cubic4) (t : ℝ) : Matrix4 :=
  hessianE A τ t - intrinsicMixedGramAdjoint A τ (intrinsicTrialVector A τ)

def intrinsicTrialB (A : Matrix4) (τ : Cubic4) : Matrix4 :=
  intrinsicTrialBt A τ (1/2)

def intrinsicTrialY (A : Matrix4) (τ : Cubic4) (t : ℝ) : Matrix4 :=
  (8*t) • intrinsicTrialB A τ

def intrinsicTrialQ (A : Matrix4) (τ : Cubic4) (t : ℝ) : ℝ :=
  16*t*matrixInner (intrinsicTrialBt A τ t) (intrinsicTrialB A τ)-
    64*t^2*matrixInner (intrinsicTrialB A τ) (matrixGramOperator A (intrinsicTrialB A τ))+
    2*(intrinsicHessianB0 A τ ⬝ᵥ intrinsicTrialVector A τ)-
    intrinsicTrialVector A τ ⬝ᵥ (vectorGramOperator τ *ᵥ intrinsicTrialVector A τ)

theorem frameVector_smul (O : Matrix4) (s : ℝ) (v : Vector4) :
    frameVector O (s • v) = s • frameVector O v :=
  Matrix.mulVec_smul O s v

theorem frame_intrinsicHessianB0 (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    intrinsicHessianB0 (frameMatrix O A) (frameCubic O τ) =
      frameVector O (intrinsicHessianB0 A τ) := by
  unfold intrinsicHessianB0
  rw [frame_intrinsicCubicD O hO, frameMatrix_mulVec O hO, frameVector_smul]

theorem frame_intrinsicTrialVector (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) :
    intrinsicTrialVector (frameMatrix O A) (frameCubic O τ) =
      frameVector O (intrinsicTrialVector A τ) := by
  unfold intrinsicTrialVector
  rw [frame_intrinsicCubicD O hO, frameMatrix_mulVec O hO, frameVector_smul]

theorem frame_intrinsicTrialBt (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicTrialBt (frameMatrix O A) (frameCubic O τ) t =
      frameMatrix O (intrinsicTrialBt A τ t) := by
  unfold intrinsicTrialBt
  rw [frame_hessianE O hO, frame_intrinsicTrialVector O hO,
    frame_intrinsicMixedGramAdjoint O hO A τ hτ]
  exact ((frameMatrixLinear O).map_sub _ _).symm

theorem frame_intrinsicTrialB (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) :
    intrinsicTrialB (frameMatrix O A) (frameCubic O τ) =
      frameMatrix O (intrinsicTrialB A τ) :=
  frame_intrinsicTrialBt O hO A τ hτ (1/2)

theorem frame_intrinsicTrialY (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicTrialY (frameMatrix O A) (frameCubic O τ) t =
      frameMatrix O (intrinsicTrialY A τ t) := by
  unfold intrinsicTrialY
  rw [frame_intrinsicTrialB O hO A τ hτ]
  exact ((frameMatrixLinear O).map_smul _ _).symm

theorem frame_intrinsicTrialQ (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicTrialQ (frameMatrix O A) (frameCubic O τ) t = intrinsicTrialQ A τ t := by
  unfold intrinsicTrialQ
  rw [frame_intrinsicTrialBt O hO A τ hτ, frame_intrinsicTrialB O hO A τ hτ,
    frame_matrixGramOperator O hO, frameMatrix_inner O hO, frameMatrix_inner O hO,
    frame_intrinsicHessianB0 O hO, frame_intrinsicTrialVector O hO,
    frameVector_inner O hO, frame_vectorGramOperator O hO, frameMatrix_mulVec O hO,
    frameVector_inner O hO]

theorem intrinsicHessianB0_diagonal (μ : Vector4) (τ : Cubic4) :
    intrinsicHessianB0 (Matrix.diagonal μ) τ = hessianB0 μ τ := by
  rw [intrinsicHessianB0, intrinsicCubicD_diagonal, hessianB0_eq_matrix]

theorem intrinsicTrialVector_diagonal (μ : Vector4) (τ : Cubic4) :
    intrinsicTrialVector (Matrix.diagonal μ) τ = trialVector μ τ := by
  rw [intrinsicTrialVector, intrinsicCubicD_diagonal, trialVector]

theorem intrinsicTrialBt_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    intrinsicTrialBt (Matrix.diagonal μ) τ t = trialBt μ τ t := by
  rw [intrinsicTrialBt, intrinsicTrialVector_diagonal,
    intrinsicMixedGramAdjoint_diagonal μ τ had, trialBt]

theorem intrinsicTrialB_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    intrinsicTrialB (Matrix.diagonal μ) τ = trialB μ τ :=
  intrinsicTrialBt_diagonal μ τ had (1/2)

theorem intrinsicTrialY_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    intrinsicTrialY (Matrix.diagonal μ) τ t = trialY μ τ t := by
  rw [intrinsicTrialY, intrinsicTrialB_diagonal μ τ had, trialY]

theorem intrinsicTrialQ_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    intrinsicTrialQ (Matrix.diagonal μ) τ t = trialQ μ τ t := by
  rw [intrinsicTrialQ, intrinsicTrialBt_diagonal μ τ had t,
    intrinsicTrialB_diagonal μ τ had, intrinsicHessianB0_diagonal,
    intrinsicTrialVector_diagonal, trialQ]

theorem hessianE_codomain (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) (t : ℝ) :
    (hessianE A τ t).IsSymm ∧ Matrix.trace (hessianE A τ t) = 0 := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  have he := hessianE_codomain_diagonal μ (frameCubic O τ) ha t
  rw [← hdiag, frame_hessianE O hO] at he
  have hs := frameMatrix_symmetric Oᵀ _ he.1
  rw [frameMatrix_inverse O hO] at hs
  exact ⟨hs, by simpa only [frameMatrix_trace O hO] using he.2⟩

theorem intrinsicTrialBt_codomain (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (t : ℝ) :
    (intrinsicTrialBt A τ t).IsSymm ∧ Matrix.trace (intrinsicTrialBt A τ t) = 0 := by
  obtain ⟨he,het⟩ := hessianE_codomain A τ had t
  obtain ⟨hz,hzt⟩ := intrinsicMixedGramAdjoint_codomain A τ had.2.1 (intrinsicTrialVector A τ)
  exact ⟨he.sub hz, by simp [intrinsicTrialBt, Matrix.trace_sub, het, hzt]⟩

theorem intrinsicTrialB_codomain (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) :
    (intrinsicTrialB A τ).IsSymm ∧ Matrix.trace (intrinsicTrialB A τ) = 0 :=
  intrinsicTrialBt_codomain A τ had (1/2)

theorem intrinsicTrialY_codomain (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (t : ℝ) :
    (intrinsicTrialY A τ t).IsSymm ∧ Matrix.trace (intrinsicTrialY A τ t) = 0 := by
  obtain ⟨hB,hBt⟩ := intrinsicTrialB_codomain A τ had
  exact ⟨hB.smul _, by simp [intrinsicTrialY, Matrix.trace_smul, hBt]⟩

/-- Q_t is precisely the joint bound for the trial variables, now in any frame. -/
theorem intrinsicTrialQ_eq_joint (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (t : ℝ) :
    intrinsicTrialQ A τ t =
      2*matrixInner (hessianE A τ t) (intrinsicTrialY A τ t)+
      2*(intrinsicHessianB0 A τ ⬝ᵥ intrinsicTrialVector A τ)-
      matrixInner (intrinsicTrialY A τ t) (matrixGramOperator A (intrinsicTrialY A τ t))-
      2*(intrinsicTrialVector A τ ⬝ᵥ intrinsicMixedGram A τ (intrinsicTrialY A τ t))-
      intrinsicTrialVector A τ ⬝ᵥ (vectorGramOperator τ *ᵥ intrinsicTrialVector A τ) := by
  rw [← intrinsicMixedGramAdjoint_pairing A had.1 τ had.2.1 _ _
    (intrinsicTrialY_codomain A τ had t).1]
  simp only [intrinsicTrialQ, intrinsicTrialY, intrinsicTrialBt, matrixInner_sub_left,
    matrixInner_smul_right, matrixGramOperator_smul, matrixInner_smul_left]
  ring

/-- The pointwise remainder concerns |V|^2 - Q_t. The zero-average
corrections in W_t are not inserted into this identity. -/
theorem intrinsicTrialQ_remainder (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (t : ℝ) (V : Fourth4) (hV : TraceFreeFourth V)
    (hE : weightedTrace A V = hessianE A τ t)
    (hb : cubicContraction τ V = intrinsicHessianB0 A τ) :
    fourthNormSq V - intrinsicTrialQ A τ t =
      fourthNormSq (V - jointTrialTensor A (intrinsicTrialY A τ t) τ (intrinsicTrialVector A τ)) := by
  rw [intrinsicTrialQ_eq_joint A τ had t]
  exact joint_contraction_remainder A τ had _ _
    (intrinsicTrialY_codomain A τ had t).1 (intrinsicTrialY_codomain A τ had t).2 _ _ V hV hE hb

end
end SecondPinching
