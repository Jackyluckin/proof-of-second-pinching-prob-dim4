import SecondPinching.NormalReversal

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- U_t=P_0(T_A^*Y_t+N_tau^*v), in the proof of prop:meanconvex. -/
def intrinsicPinchingTrialTensor (A : Matrix4) (τ : Cubic4) (t : ℝ) : Fourth4 :=
  jointTrialTensor A (intrinsicTrialY A τ t) τ (intrinsicTrialVector A τ)

/-- Here V is the reduced trace-free Hessian of prop:reduction, not the raw
second covariant derivative D. Its geometric origin is not part of this definition. -/
def intrinsicPinchingSquare (A : Matrix4) (τ : Cubic4) (t : ℝ) (V : Fourth4) : ℝ :=
  fourthNormSq (V - intrinsicPinchingTrialTensor A τ t)

theorem intrinsicPinchingSquare_nonneg (A : Matrix4) (τ : Cubic4) (t : ℝ) (V : Fourth4) :
    0 ≤ intrinsicPinchingSquare A τ t V := by
  simpa only [fourthInner_self, intrinsicPinchingSquare] using
    fourthInner_self_nonneg (V - intrinsicPinchingTrialTensor A τ t)

theorem intrinsicPinchingTrialTensor_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    intrinsicPinchingTrialTensor (Matrix.diagonal μ) τ t = pinchingTrialTensor μ τ t := by
  simp only [intrinsicPinchingTrialTensor, intrinsicTrialY_diagonal μ τ had,
    intrinsicTrialVector_diagonal, pinchingTrialTensor]

/-- Exact match with the older square, after supplying the same reduced V. -/
theorem intrinsicPinchingSquare_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) (D : Fourth4) :
    intrinsicPinchingSquare (Matrix.diagonal μ) τ t (hessianRemainder μ t D) =
      pinchingSquare μ τ t D := by
  simp only [intrinsicPinchingSquare, intrinsicPinchingTrialTensor_diagonal μ τ had,
    pinchingSquare]

theorem frame_intrinsicPinchingTrialTensor (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) (t : ℝ) :
    intrinsicPinchingTrialTensor (frameMatrix O A) (frameCubic O τ) t =
      frameFourth O (intrinsicPinchingTrialTensor A τ t) := by
  unfold intrinsicPinchingTrialTensor
  rw [frame_intrinsicTrialY O hO A τ had.2.1, frame_intrinsicTrialVector O hO]
  exact (frameFourth_jointTrialTensor O hO A _ had.1
    (intrinsicTrialY_codomain A τ had t).1 τ had.2.1 _).symm

theorem frame_intrinsicPinchingSquare (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) (t : ℝ) (V : Fourth4) :
    intrinsicPinchingSquare (frameMatrix O A) (frameCubic O τ) t (frameFourth O V) =
      intrinsicPinchingSquare A τ t V := by
  unfold intrinsicPinchingSquare
  rw [frame_intrinsicPinchingTrialTensor O hO A τ had]
  rw [← show frameFourth O (V - intrinsicPinchingTrialTensor A τ t) =
    frameFourth O V - frameFourth O (intrinsicPinchingTrialTensor A τ t) from
      (frameFourthLinear O).map_sub _ _, frameFourth_normSq O hO]

theorem intrinsicPinchingTrialTensor_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicPinchingTrialTensor (-A) (-τ) t = -intrinsicPinchingTrialTensor A τ t := by
  unfold intrinsicPinchingTrialTensor jointTrialTensor
  rw [intrinsicTrialY_normal_reversal, intrinsicTrialVector_normal_reversal,
    weightedTraceAdjoint_neg_left, cubicContractionAdjoint_neg_left, ← neg_add]
  exact ordinaryTraceFreeProjectionLinear.map_neg _

theorem intrinsicPinchingSquare_normal_reversal (A : Matrix4) (τ : Cubic4) (t : ℝ) (V : Fourth4) :
    intrinsicPinchingSquare (-A) (-τ) t (-V) = intrinsicPinchingSquare A τ t V := by
  unfold intrinsicPinchingSquare
  rw [intrinsicPinchingTrialTensor_normal_reversal]
  simp only [fourthNormSq, Pi.sub_apply, Pi.neg_apply]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

/-- The component conclusion of prop:reduction yields the exact pointwise
formula. The three correction terms are retained here; only their integrals vanish. -/
theorem intrinsicPinchingW_pointwise_remainder (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (t : ℝ) (V : Fourth4) (hV : TraceFreeFourth V)
    (hE : weightedTrace A V = hessianE A τ t)
    (hb : cubicContraction τ V = intrinsicHessianB0 A τ)
    (hn : fourthNormSq V = 3*t*(intrinsicCubicA A τ-2*intrinsicCubicB A τ)+
      t*(35*t-28)/16-(3/2 : ℝ)*phiNormSq A) :
    intrinsicPinchingW A τ t = intrinsicPinchingSquare A τ t V-
      (89/8 : ℝ)*intrinsicCorrectionL4 A τ t+16*intrinsicCorrectionL3 A τ t+
      (13/4 : ℝ)*intrinsicCorrectionJ A τ t := by
  have hr := intrinsicTrialQ_remainder A τ had t V hV hE hb
  change fourthNormSq V - intrinsicTrialQ A τ t = intrinsicPinchingSquare A τ t V at hr
  rw [hn] at hr
  unfold intrinsicPinchingW
  rw [hr]

end
end SecondPinching
