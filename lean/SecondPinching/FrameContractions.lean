import SecondPinching.OrthogonalFrames

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The two admissibility traces and the contractions of Section 3 commute
with changes of orthonormal frame. These identities hold for arbitrary arrays;
symmetry is imposed only when needed for the stated tensor spaces. -/

/-- The ordinary trace of a cubic, appearing in eq:admissible. -/
def cubicTrace (τ : Cubic4) : Vector4 := fun k => ∑ i, τ i i k

/-- The A-weighted trace of a cubic, appearing in eq:admissible. -/
def cubicWeightedTrace (A : Matrix4) (τ : Cubic4) : Vector4 :=
  fun k => ∑ i, ∑ j, A i j * τ i j k

theorem frameCubic_trace (Q : Matrix4) (hQ : OrthogonalFrame Q) (τ : Cubic4) :
    cubicTrace (frameCubic Q τ) = frameVector Q (cubicTrace τ) := by
  funext k
  change Matrix.trace (frameMatrix Q (fun a b => ∑ c, Q k c * τ a b c)) = _
  erw [frameMatrix_trace Q hQ]
  simp only [Matrix.trace, Matrix.diag, frameVector, Matrix.mulVec, dotProduct, cubicTrace,
    Finset.mul_sum]
  rw [Finset.sum_comm]

theorem frameCubic_weightedTrace (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A : Matrix4) (τ : Cubic4) :
    cubicWeightedTrace (frameMatrix Q A) (frameCubic Q τ) =
      frameVector Q (cubicWeightedTrace A τ) := by
  funext k
  change matrixInner (frameMatrix Q A) (frameMatrix Q (fun a b => ∑ c, Q k c * τ a b c)) = _
  erw [frameMatrix_inner Q hQ]
  simp only [matrixInner, frameVector, Matrix.mulVec, dotProduct, cubicWeightedTrace,
    Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frameFourth_ordinaryTrace (Q : Matrix4) (hQ : OrthogonalFrame Q) (U : Fourth4) :
    ordinaryTrace (frameFourth Q U) = frameMatrix Q (ordinaryTrace U) := by
  ext k l
  change Matrix.trace (frameMatrix Q (fun a b => frameMatrix Q (U a b) k l)) = _
  erw [frameMatrix_trace Q hQ]
  simp only [Matrix.trace, Matrix.diag, ordinaryTrace, frameMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]

theorem frameFourth_weightedTrace (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A : Matrix4) (U : Fourth4) :
    weightedTrace (frameMatrix Q A) (frameFourth Q U) = frameMatrix Q (weightedTrace A U) := by
  ext k l
  change matrixInner (frameMatrix Q A) (frameMatrix Q (fun a b => frameMatrix Q (U a b) k l)) = _
  erw [frameMatrix_inner Q hQ]
  simp only [matrixInner, frameMatrix, weightedTrace, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frameFourth_cubicContraction (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (τ : Cubic4) (U : Fourth4) :
    cubicContraction (frameCubic Q τ) (frameFourth Q U) = frameVector Q (cubicContraction τ U) := by
  funext l
  change cubicInner (frameCubic Q τ) (frameCubic Q (fun a b c => ∑ d, Q l d * U a b c d)) = _
  rw [frameCubic_inner Q hQ]
  simp only [cubicInner, frameVector, Matrix.mulVec, dotProduct, cubicContraction, Finset.mul_sum]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem frameFourth_traceFree (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (U : Fourth4) (hU : TraceFreeFourth U) : TraceFreeFourth (frameFourth Q U) := by
  refine ⟨frameFourth_symmetric Q U hU.1, ?_⟩
  rw [frameFourth_ordinaryTrace Q hQ, hU.2]
  exact (frameMatrixLinear Q).map_zero

theorem admissible_frame (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A : Matrix4) (τ : Cubic4) (had : Admissible A τ) :
    Admissible (frameMatrix Q A) (frameCubic Q τ) := by
  rcases had with ⟨hA,hτ,htr,hAn,hτn,ht0,htA⟩
  refine ⟨frameMatrix_symmetric Q A hA,frameCubic_symmetric Q τ hτ,?_,?_,?_,?_,?_⟩
  · rwa [frameMatrix_trace Q hQ]
  · rwa [frameMatrix_normSq Q hQ]
  · rwa [frameCubic_normSq Q hQ]
  · intro k
    have hz : cubicTrace τ = 0 := funext ht0
    have h := congrFun (frameCubic_trace Q hQ τ) k
    simpa only [hz,frameVector,Matrix.mulVec_zero,Pi.zero_apply,cubicTrace] using h
  · intro k
    have hz : cubicWeightedTrace A τ = 0 := funext htA
    have h := congrFun (frameCubic_weightedTrace Q hQ A τ) k
    simpa only [hz,frameVector,Matrix.mulVec_zero,Pi.zero_apply,cubicWeightedTrace] using h

/-- Exact equivalence with the manuscript definition, including its square-root norms. -/
theorem paperAdmissible_frame_iff (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A : Matrix4) (τ : Cubic4) :
    PaperAdmissible (frameMatrix Q A) (frameCubic Q τ) ↔ PaperAdmissible A τ := by
  simp only [← admissible_iff_paper]
  constructor
  · intro h
    have hi := admissible_frame Qᵀ (orthogonalFrame_transpose Q hQ) _ _ h
    simpa only [frameMatrix_inverse Q hQ, frameCubic_inverse Q hQ] using hi
  · exact admissible_frame Q hQ A τ

end
end SecondPinching
