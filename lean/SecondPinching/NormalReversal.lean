import SecondPinching.IntrinsicW

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Normal reversal is the simultaneous change (A,tau) -> (-A,-tau).
These are component identities; constructing the normal double cover and its
volume relation is a separate geometric obligation. -/

theorem cubicSymmetric_neg {τ : Cubic4} (hτ : CubicSymmetric τ) :
    CubicSymmetric (-τ) := by
  intro σ v
  exact congrArg Neg.neg (hτ σ v)

theorem paperAdmissible_normal_reversal (A : Matrix4) (τ : Cubic4) :
    PaperAdmissible (-A) (-τ) ↔ PaperAdmissible A τ := by
  have forward : ∀ (X : Matrix4) (T : Cubic4), PaperAdmissible X T →
      PaperAdmissible (-X) (-T) := by
    intro X T h
    rcases h with ⟨hX,hT,ht,hn,hTn,htr,hw⟩
    refine ⟨hX.neg, cubicSymmetric_neg hT, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Matrix.trace_neg, ht, neg_zero]
    · simpa [matrixNormSq] using hn
    · simpa [cubicNormSq] using hTn
    · intro k; simpa using congrArg Neg.neg (htr k)
    · intro k; simpa using hw k
  exact ⟨fun h => by simpa using forward (-A) (-τ) h, forward A τ⟩

theorem cubicMoment_neg (A : Matrix4) : cubicMoment (-A) = -cubicMoment A := by
  simp [cubicMoment, pow_succ]

theorem quarticMoment_neg (A : Matrix4) : quarticMoment (-A) = quarticMoment A := by
  simp [quarticMoment, pow_succ]

theorem normalizedPhi_neg (A : Matrix4) : normalizedPhi (-A) = normalizedPhi A := by
  simp [normalizedPhi, cubicMoment_neg]

theorem cubicGramMatrix_neg (τ : Cubic4) : cubicGramMatrix (-τ) = cubicGramMatrix τ := by
  ext k l
  simp [cubicGramMatrix]

theorem intrinsicCubicA_normal_reversal (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicA (-A) (-τ) = intrinsicCubicA A τ := by
  simp [intrinsicCubicA, cubicGramMatrix_neg]

theorem cubicMatrixAction_normal_reversal (A : Matrix4) (τ : Cubic4) :
    cubicMatrixAction (-A) (-τ) = -cubicMatrixAction A τ := by
  funext i j k
  change ((-A) * (-(Matrix.of (τ i))) * (-A)ᵀ) j k = -((A * Matrix.of (τ i) * Aᵀ) j k)
  simp only [Matrix.transpose_neg, neg_mul, mul_neg, neg_neg, Matrix.neg_apply]

theorem intrinsicCubicB_normal_reversal (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicB (-A) (-τ) = intrinsicCubicB A τ := by
  simp [intrinsicCubicB, cubicMatrixAction_normal_reversal, cubicInner]

theorem intrinsicCubicC_normal_reversal (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicC (-A) (-τ) = -intrinsicCubicC A τ := by
  simp [intrinsicCubicC, cubicGramMatrix_neg]

theorem intrinsicCubicD_normal_reversal (A : Matrix4) (τ : Cubic4) :
    intrinsicCubicD (-A) (-τ) = -intrinsicCubicD A τ := by
  funext k
  simp only [intrinsicCubicD, neg_sq, cubicWeightedTrace, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib]

theorem hessianE_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    hessianE (-A) (-τ) t = hessianE A τ t := by
  simp [hessianE, hessianPsi, normalizedPhi_neg, cubicGramMatrix_neg]

theorem intrinsicHessianB0_normal_reversal (A : Matrix4) (τ : Cubic4) :
    intrinsicHessianB0 (-A) (-τ) = intrinsicHessianB0 A τ := by
  simp [intrinsicHessianB0, intrinsicCubicD_normal_reversal, Matrix.neg_mulVec_neg]

theorem intrinsicTrialVector_normal_reversal (A : Matrix4) (τ : Cubic4) :
    intrinsicTrialVector (-A) (-τ) = intrinsicTrialVector A τ := by
  simp [intrinsicTrialVector, intrinsicCubicD_normal_reversal, Matrix.neg_mulVec_neg]

theorem cubicContractionAdjoint_neg_left (τ : Cubic4) (v : Vector4) :
    cubicContractionAdjoint (-τ) v = -cubicContractionAdjoint τ v := by
  funext i j k l
  simp only [cubicContractionAdjoint, Pi.neg_apply]
  ring

theorem weightedTraceAdjoint_neg_left (A Y : Matrix4) :
    weightedTraceAdjoint (-A) Y = -weightedTraceAdjoint A Y := by
  funext i j k l
  simp only [weightedTraceAdjoint, Matrix.neg_apply, Pi.neg_apply]
  ring

theorem weightedTrace_neg_neg (A : Matrix4) (U : Fourth4) :
    weightedTrace (-A) (-U) = weightedTrace A U := by
  ext k l
  simp [weightedTrace]

theorem intrinsicMixedGramAdjoint_normal_reversal (A : Matrix4) (τ : Cubic4) (v : Vector4) :
    intrinsicMixedGramAdjoint (-A) (-τ) v = intrinsicMixedGramAdjoint A τ v := by
  unfold intrinsicMixedGramAdjoint
  rw [cubicContractionAdjoint_neg_left,
    show ordinaryTraceFreeProjection (-cubicContractionAdjoint τ v) =
      -ordinaryTraceFreeProjection (cubicContractionAdjoint τ v) from
        ordinaryTraceFreeProjectionLinear.map_neg _, weightedTrace_neg_neg]

theorem intrinsicTrialBt_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicTrialBt (-A) (-τ) t = intrinsicTrialBt A τ t := by
  simp only [intrinsicTrialBt, hessianE_normal_reversal, intrinsicTrialVector_normal_reversal,
    intrinsicMixedGramAdjoint_normal_reversal]

theorem intrinsicTrialY_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicTrialY (-A) (-τ) t = intrinsicTrialY A τ t := by
  simp only [intrinsicTrialY, intrinsicTrialB, intrinsicTrialBt_normal_reversal]

theorem matrixGramOperator_neg (A Y : Matrix4) :
    matrixGramOperator (-A) Y = matrixGramOperator A Y := by
  simp [matrixGramOperator]

theorem intrinsicTrialQ_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicTrialQ (-A) (-τ) t = intrinsicTrialQ A τ t := by
  simp only [intrinsicTrialQ, intrinsicTrialB, intrinsicTrialBt_normal_reversal,
    intrinsicHessianB0_normal_reversal, intrinsicTrialVector_normal_reversal,
    matrixGramOperator_neg, vectorGramOperator, cubicGramMatrix_neg]

theorem intrinsicCorrections_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicCorrectionL4 (-A) (-τ) t = intrinsicCorrectionL4 A τ t ∧
    intrinsicCorrectionL3 (-A) (-τ) t = intrinsicCorrectionL3 A τ t ∧
    intrinsicCorrectionJ (-A) (-τ) t = intrinsicCorrectionJ A τ t := by
  simp [intrinsicCorrectionL4, intrinsicCorrectionL3, intrinsicCorrectionJ,
    intrinsicCubicA_normal_reversal, intrinsicCubicB_normal_reversal,
    intrinsicCubicC_normal_reversal, intrinsicCubicD_normal_reversal,
    cubicMoment_neg, quarticMoment_neg, phiNormSq, normalizedPhi_neg]

/-- The full W_t is unchanged by normal reversal, for all real t and even
before imposing admissibility. In particular d need not vanish. -/
theorem intrinsicPinchingW_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicPinchingW (-A) (-τ) t = intrinsicPinchingW A τ t := by
  obtain ⟨h4,h3,hJ⟩ := intrinsicCorrections_normal_reversal A τ t
  simp only [intrinsicPinchingW, intrinsicCubicA_normal_reversal,
    intrinsicCubicB_normal_reversal, phiNormSq, normalizedPhi_neg,
    intrinsicTrialQ_normal_reversal, h4, h3, hJ]

/-- Simultaneous changes of local tangent frame and unit normal give the
same scalar. This is a pointwise overlap identity, not a global field construction. -/
theorem intrinsicPinchingW_frame_normal (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicPinchingW (-frameMatrix O A) (-frameCubic O τ) t = intrinsicPinchingW A τ t := by
  rw [intrinsicPinchingW_normal_reversal, frame_intrinsicPinchingW O hO A τ hτ]

end
end SecondPinching
