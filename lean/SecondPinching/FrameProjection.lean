import SecondPinching.FrameContractions

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Transport of the actual projection and adjoints. Uniqueness uses the
ordered inner products, so no new coordinate formula for P_0 is assumed. -/

theorem frameFourth_projection (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (U : Fourth4) (hU : FourthSymmetric U) :
    frameFourth Q (ordinaryTraceFreeProjection U) = ordinaryTraceFreeProjection (frameFourth Q U) := by
  apply ordinaryTraceFreeProjection_unique _ (frameFourth_symmetric Q U hU)
  refine ⟨frameFourth_traceFree Q hQ _ (ordinaryTraceFreeProjection_mem U hU), ?_⟩
  intro W hW
  have hWi := frameFourth_traceFree Qᵀ (orthogonalFrame_transpose Q hQ) W hW
  have hr : frameFourth Q (frameFourth Qᵀ W) = W := by
    simpa only [Matrix.transpose_transpose] using
      frameFourth_inverse Qᵀ (orthogonalFrame_transpose Q hQ) W
  have hsub : frameFourth Q (U-ordinaryTraceFreeProjection U) =
      frameFourth Q U-frameFourth Q (ordinaryTraceFreeProjection U) :=
    (frameFourthLinear Q).map_sub _ _
  have hi := frameFourth_inner Q hQ (U-ordinaryTraceFreeProjection U) (frameFourth Qᵀ W)
  rw [hsub,hr] at hi
  rw [hi,ordinaryTraceFreeProjection_orthogonal U hU _ hWi]

theorem frameFourth_weightedTraceAdjoint (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm) :
    frameFourth Q (weightedTraceAdjoint A Y) = weightedTraceAdjoint (frameMatrix Q A) (frameMatrix Q Y) := by
  apply weightedTraceAdjoint_unique _ _ (frameMatrix_symmetric Q A hA) (frameMatrix_symmetric Q Y hY)
  refine ⟨frameFourth_symmetric Q _ (weightedTraceAdjoint_symmetric A Y hA hY), ?_⟩
  intro U hU
  have hUi := frameFourth_symmetric Qᵀ U hU
  have hr : frameFourth Q (frameFourth Qᵀ U) = U := by
    simpa only [Matrix.transpose_transpose] using
      frameFourth_inverse Qᵀ (orthogonalFrame_transpose Q hQ) U
  have hi := frameFourth_inner Q hQ (frameFourth Qᵀ U) (weightedTraceAdjoint A Y)
  rw [hr,weightedTrace_adjoint_pairing A Y hA hY _ hUi] at hi
  rw [hi]
  have hm := frameMatrix_inner Q hQ (weightedTrace A (frameFourth Qᵀ U)) Y
  rw [← frameFourth_weightedTrace Q hQ,hr] at hm
  exact hm.symm

theorem frameFourth_cubicContractionAdjoint (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4) :
    frameFourth Q (cubicContractionAdjoint τ v) =
      cubicContractionAdjoint (frameCubic Q τ) (frameVector Q v) := by
  apply cubicContractionAdjoint_unique _ (frameCubic_symmetric Q τ hτ)
  refine ⟨frameFourth_symmetric Q _ (cubicContractionAdjoint_symmetric τ hτ v), ?_⟩
  intro U hU
  have hUi := frameFourth_symmetric Qᵀ U hU
  have hr : frameFourth Q (frameFourth Qᵀ U) = U := by
    simpa only [Matrix.transpose_transpose] using
      frameFourth_inverse Qᵀ (orthogonalFrame_transpose Q hQ) U
  have hi := frameFourth_inner Q hQ (frameFourth Qᵀ U) (cubicContractionAdjoint τ v)
  rw [hr,cubicContraction_adjoint_pairing τ hτ v _ hUi] at hi
  rw [hi]
  have hv := frameVector_inner Q hQ (cubicContraction τ (frameFourth Qᵀ U)) v
  rw [← frameFourth_cubicContraction Q hQ,hr] at hv
  exact hv.symm

theorem frameFourth_jointTrialTensor (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4) :
    frameFourth Q (jointTrialTensor A Y τ v) =
      jointTrialTensor (frameMatrix Q A) (frameMatrix Q Y) (frameCubic Q τ) (frameVector Q v) := by
  unfold jointTrialTensor
  rw [frameFourth_projection Q hQ _ (fourthSymmetric_add
    (weightedTraceAdjoint_symmetric A Y hA hY) (cubicContractionAdjoint_symmetric τ hτ v))]
  have ha : frameFourth Q (weightedTraceAdjoint A Y+cubicContractionAdjoint τ v) =
      frameFourth Q (weightedTraceAdjoint A Y)+frameFourth Q (cubicContractionAdjoint τ v) :=
    (frameFourthLinear Q).map_add _ _
  rw [ha,frameFourth_weightedTraceAdjoint Q hQ A Y hA hY,
    frameFourth_cubicContractionAdjoint Q hQ τ hτ v]

theorem frame_jointSquareBound (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A Y E : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v b₀ : Vector4) :
    jointSquareBound (frameMatrix Q A) (frameMatrix Q Y) (frameMatrix Q E)
      (frameCubic Q τ) (frameVector Q v) (frameVector Q b₀) = jointSquareBound A Y E τ v b₀ := by
  unfold jointSquareBound
  rw [frameMatrix_inner Q hQ,frameVector_inner Q hQ,
    ← frameFourth_jointTrialTensor Q hQ A Y hA hY τ hτ v,frameFourth_normSq Q hQ]

end
end SecondPinching
