import SecondPinching.ReducedHessian

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- The component hypotheses of the existing Hessian proof now identify the
specific reduced tensor in every orthonormal frame. The Ricci and Peng--Terng
identities remain explicit inputs; this is not a theorem deriving them from an immersion. -/
theorem intrinsicHessianRemainder_spec (A : Matrix4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (had : PaperAdmissible A τ) (hD : FirstThreeSymmetric D)
    (Q : Matrix4) (hQ : OrthogonalFrame Q) (μ : Vector4)
    (hdiag : frameMatrix Q A = Matrix.diagonal μ)
    (hRicci : HasRicciCommutator μ ((1-t)/4) (frameFourth Q D))
    (htr : ordinaryTrace (frameFourth Q D) = 0)
    (hweighted : weightedTrace (Matrix.diagonal μ) (frameFourth Q D) =
      (-t) • cubicGramMatrix (frameCubic Q τ))
    (hcubic : cubicContraction (frameCubic Q τ) (frameFourth Q D) = 0)
    (hPT : fourthNormSq (frameFourth Q D) =
      3*t*(cubicA μ (frameCubic Q τ)-2*cubicB μ (frameCubic Q τ))+t*(11*t-7)/4) :
    TraceFreeFourth (intrinsicHessianRemainder A t D) ∧
    weightedTrace A (intrinsicHessianRemainder A t D) = hessianE A τ t ∧
    cubicContraction τ (intrinsicHessianRemainder A t D) = intrinsicHessianB0 A τ ∧
    fourthNormSq (intrinsicHessianRemainder A t D) =
      3*t*(intrinsicCubicA A τ-2*intrinsicCubicB A τ)+t*(35*t-28)/16-(3/2 : ℝ)*phiNormSq A := by
  have had' : PaperAdmissible (Matrix.diagonal μ) (frameCubic Q τ) := by
    rw [← hdiag]
    exact (paperAdmissible_frame_iff Q hQ A τ).mpr had
  obtain ⟨hs,hm,hn,_,ht,hw⟩ := (admissible_diagonal_iff μ _).mp
    ((admissible_iff_paper _ _).mpr had')
  have hD' := frameFourth_firstThree Q D hD
  have hv := hessianRemainder_mem μ t (frameFourth Q D) hm hn hD' hRicci htr
  have he := weightedTrace_hessianRemainder μ (frameCubic Q τ) t (frameFourth Q D)
    hm hn hD' hRicci hweighted
  have hb := cubicContraction_hessianRemainder μ (frameCubic Q τ) t (frameFourth Q D)
    hs ht hw hD' hRicci hcubic
  have hn' := hessianRemainder_norm μ (frameCubic Q τ) t (frameFourth Q D)
    hm hn hD' hRicci htr hPT
  have hrem : hessianRemainder μ t (frameFourth Q D) =
      frameFourth Q (intrinsicHessianRemainder A t D) := by
    rw [← intrinsicHessianRemainder_diagonal,← hdiag]
    exact frame_intrinsicHessianRemainder Q hQ A had.1 t D hD
  rw [hrem] at hv he hb hn'
  refine ⟨?_,?_,?_,?_⟩
  · have hh := frameFourth_traceFree Qᵀ (orthogonalFrame_transpose Q hQ) _ hv
    rwa [frameFourth_inverse Q hQ] at hh
  · rw [← hdiag,frameFourth_weightedTrace Q hQ,frame_hessianE Q hQ] at he
    have hh := congrArg (frameMatrix Qᵀ) he
    simpa only [frameMatrix_inverse Q hQ] using hh
  · rw [← intrinsicHessianB0_diagonal,← hdiag,
      frameFourth_cubicContraction Q hQ,frame_intrinsicHessianB0 Q hQ] at hb
    have hh := congrArg (frameVector Qᵀ) hb
    simpa only [frameVector_inverse Q hQ] using hh
  · rw [← intrinsicCubicA_diagonal μ (frameCubic Q τ) hs,
      ← intrinsicCubicB_diagonal μ (frameCubic Q τ) hs,← hdiag,
      frame_intrinsicCubicA Q hQ,frame_intrinsicCubicB Q hQ,
      frame_phiNormSq Q hQ,frameFourth_normSq Q hQ] at hn'
    exact hn'

/-- A raw Hessian transforms before symmetrization and trace removal. Thus
the signed overlap condition on V follows from that on the unnormalized data. -/
theorem normalized_reduced_signed_overlap (S : ℝ) (h h' : Matrix4)
    (T T' : Cubic4) (H H' : Fourth4) (hs : h.IsSymm)
    (hH : FirstThreeSymmetric H)
    (htrans : ∃ Q : Matrix4, OrthogonalFrame Q ∧
      ((h' = frameMatrix Q h ∧ T' = frameCubic Q T ∧ H' = frameFourth Q H) ∨
       (h' = -frameMatrix Q h ∧ T' = -frameCubic Q T ∧ H' = -frameFourth Q H))) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      ((normalizeSecond S h' = frameMatrix Q (normalizeSecond S h) ∧
        normalizeThird S T' = frameCubic Q (normalizeThird S T) ∧
        intrinsicHessianRemainder (normalizeSecond S h') (pinchingParameter S) (normalizeFourth S H') =
          frameFourth Q (intrinsicHessianRemainder (normalizeSecond S h) (pinchingParameter S) (normalizeFourth S H))) ∨
       (normalizeSecond S h' = -frameMatrix Q (normalizeSecond S h) ∧
        normalizeThird S T' = -frameCubic Q (normalizeThird S T) ∧
        intrinsicHessianRemainder (normalizeSecond S h') (pinchingParameter S) (normalizeFourth S H') =
          -frameFourth Q (intrinsicHessianRemainder (normalizeSecond S h) (pinchingParameter S) (normalizeFourth S H)))) := by
  have hs' : (normalizeSecond S h).IsSymm := by
    ext i j; simp only [normalizeSecond,Matrix.smul_apply,Matrix.transpose_apply,hs.apply]
  have hH' : FirstThreeSymmetric (normalizeFourth S H) := by
    constructor
    · intro i j k l; simp only [normalizeFourth,Pi.smul_apply,hH.1]
    · intro i j k l; simp only [normalizeFourth,Pi.smul_apply,hH.2]
  obtain ⟨Q,hQ,hq⟩ := htrans
  obtain ⟨ha,ht,hd⟩ := normalize_frame S Q h T H
  refine ⟨Q,hQ,?_⟩
  rcases hq with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · left
    rw [ha,ht,hd]
    exact ⟨rfl,rfl,frame_intrinsicHessianRemainder Q hQ _ hs' _ _ hH'⟩
  · right
    obtain ⟨ha',ht',hd'⟩ := normalize_normal_reversal S (frameMatrix Q h) (frameCubic Q T) (frameFourth Q H)
    rw [ha',ht',hd',ha,ht,hd,intrinsicHessianRemainder_normal_reversal,
      frame_intrinsicHessianRemainder Q hQ _ hs' _ _ hH']
    exact ⟨rfl,rfl,rfl⟩

end
end SecondPinching
