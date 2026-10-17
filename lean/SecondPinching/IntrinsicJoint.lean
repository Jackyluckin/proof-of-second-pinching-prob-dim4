import SecondPinching.OrthogonalDiagonalization
import SecondPinching.FrameQuantities

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Section 3 in arbitrary orthonormal coordinates. Z is written as its actual
contraction composition, and its agreement with eq:ZH is proved below. -/

/-- Coordinate-free expression for Z on its stated symmetric trace-free domain. -/
def intrinsicMixedGram (A : Matrix4) (τ : Cubic4) (Y : Matrix4) : Vector4 :=
  cubicContraction τ (ordinaryTraceFreeProjection (weightedTraceAdjoint A Y))

theorem intrinsicMixedGram_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    intrinsicMixedGram (Matrix.diagonal μ) τ Y = mixedGramOperator μ τ Y := by
  exact (contraction_lemma_diagonal μ τ had Y hY htr 0).2.1

theorem frame_intrinsicMixedGram (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (hA : A.IsSymm) (τ : Cubic4) (Y : Matrix4) (hY : Y.IsSymm) :
    intrinsicMixedGram (frameMatrix O A) (frameCubic O τ) (frameMatrix O Y) =
      frameVector O (intrinsicMixedGram A τ Y) := by
  unfold intrinsicMixedGram
  rw [← frameFourth_weightedTraceAdjoint O hO A Y hA hY,
    ← frameFourth_projection O hO _ (weightedTraceAdjoint_symmetric A Y hA hY),
    frameFourth_cubicContraction O hO]

/-- The matrix lower bound in eq:Klower for any symmetric A. -/
theorem matrixGram_lower_bound (A Y : Matrix4) (hA : A.IsSymm)
    (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    (1/6 : ℝ) * matrixNormSq Y + (1/3 : ℝ) * Matrix.trace (A^2 * Y^2) ≤
      matrixInner Y (matrixGramOperator A Y) := by
  obtain ⟨O,μ,hO,hdiag⟩ := symmetric_orthogonal_diagonalization A hA
  have hYtr : Matrix.trace (frameMatrix O Y) = 0 := by rwa [frameMatrix_trace O hO]
  have hb := matrixGram_lower_bound_diagonal μ (frameMatrix O Y) (frameMatrix_symmetric O Y hY) hYtr
  rw [← hdiag,frame_matrixGramOperator O hO,frameMatrix_inner O hO,
    frameMatrix_normSq O hO,← frameMatrix_pow O hO,← frameMatrix_pow O hO,
    ← frameMatrix_mul O hO,frameMatrix_trace O hO] at hb
  exact hb

/-- The first Gram identity of eq:Grams in an arbitrary orthonormal frame. -/
theorem matrix_gram_identity (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    weightedTrace A (ordinaryTraceFreeProjection (weightedTraceAdjoint A Y)) = matrixGramOperator A Y := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  have hYtr : Matrix.trace (frameMatrix O Y) = 0 := by rwa [frameMatrix_trace O hO]
  have he := (contraction_lemma_diagonal μ (frameCubic O τ) ha (frameMatrix O Y)
    (frameMatrix_symmetric O Y hY) hYtr 0).1
  apply Function.LeftInverse.injective (frameMatrix_inverse O hO)
  rw [← frameFourth_weightedTrace O hO,
    frameFourth_projection O hO _ (weightedTraceAdjoint_symmetric A Y had.1 hY),
    frameFourth_weightedTraceAdjoint O hO A Y had.1 hY,← frame_matrixGramOperator O hO,hdiag]
  exact he

/-- All three terms in the projected norm, with Z expressed intrinsically. -/
theorem jointTrialTensor_norm (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) (v : Vector4) :
    fourthNormSq (jointTrialTensor A Y τ v) = matrixInner Y (matrixGramOperator A Y) +
      2 * (v ⬝ᵥ intrinsicMixedGram A τ Y) + v ⬝ᵥ (vectorGramOperator τ *ᵥ v) := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  obtain ⟨hτ,hμ,hn,hτn,ht,hw⟩ := (admissible_diagonal_iff μ (frameCubic O τ)).mp
    ((admissible_iff_paper _ _).mpr ha)
  have hYtr : Matrix.trace (frameMatrix O Y) = 0 := by rwa [frameMatrix_trace O hO]
  have he := jointTrialTensor_norm_diagonal μ hμ hn (frameCubic O τ) hτ ht hw hτn
    (frameMatrix O Y) (frameMatrix_symmetric O Y hY) hYtr (frameVector O v)
  rw [← intrinsicMixedGram_diagonal μ (frameCubic O τ) ha (frameMatrix O Y)
    (frameMatrix_symmetric O Y hY) hYtr,← hdiag,
    ← frameFourth_jointTrialTensor O hO A Y had.1 hY τ had.2.1 v,frameFourth_normSq O hO,
    frame_matrixGramOperator O hO,frameMatrix_inner O hO,
    frame_intrinsicMixedGram O hO A had.1 τ Y hY,frameVector_inner O hO,
    frame_vectorGramOperator O hO] at he
  have hmv : frameMatrix O (vectorGramOperator τ) *ᵥ frameVector O v =
      frameVector O (vectorGramOperator τ *ᵥ v) := by
    change _ = O *ᵥ (vectorGramOperator τ *ᵥ v)
    rw [frameMatrix_eq_conjugate]
    simp only [frameVector,Matrix.mulVec_mulVec]
    have hm : O * vectorGramOperator τ * Oᵀ * O = O * vectorGramOperator τ := by
      calc
        O * vectorGramOperator τ * Oᵀ * O = O * vectorGramOperator τ * (Oᵀ*O) := by noncomm_ring
        _ = O * vectorGramOperator τ := by rw [hO,mul_one]
    rw [hm]
  rw [hmv,frameVector_inner O hO] at he
  exact he

/-- Proposition prop:joint with the same domains and prescribed contractions,
using the proved intrinsic expression for Z. -/
theorem joint_contraction_estimate (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ)
    (E Y : Matrix4) (_hE : E.IsSymm) (_hEtr : Matrix.trace E = 0)
    (hY : Y.IsSymm) (hYtr : Matrix.trace Y = 0) (b₀ v : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V)
    (hTV : weightedTrace A V = E) (hNV : cubicContraction τ V = b₀) :
    2 * matrixInner E Y + 2 * (b₀ ⬝ᵥ v) - matrixInner Y (matrixGramOperator A Y) -
      2 * (v ⬝ᵥ intrinsicMixedGram A τ Y) - v ⬝ᵥ (vectorGramOperator τ *ᵥ v) ≤ fourthNormSq V := by
  have hb := joint_square_estimate A Y E had.1 hY τ had.2.1 v b₀ V hV hTV hNV
  unfold jointSquareBound at hb
  rw [jointTrialTensor_norm A τ had Y hY hYtr v] at hb
  linarith

/-- K_A has exactly the symmetric trace-free codomain stated in Section 3. -/
theorem matrixGram_traceFree (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    (matrixGramOperator A Y).IsSymm ∧ Matrix.trace (matrixGramOperator A Y) = 0 := by
  rw [← matrix_gram_identity A τ had Y hY htr]
  exact weightedTrace_traceFree _ _ (ordinaryTraceFreeProjection_mem _
    (weightedTraceAdjoint_symmetric A Y had.1 hY))

/-- The pointwise square remainder for the joint estimate, before the three
zero-average corrections defining W_t are added. -/
theorem joint_contraction_remainder (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ)
    (E Y : Matrix4) (hY : Y.IsSymm) (hYtr : Matrix.trace Y = 0) (b₀ v : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V)
    (hTV : weightedTrace A V = E) (hNV : cubicContraction τ V = b₀) :
    fourthNormSq V - (2 * matrixInner E Y + 2 * (b₀ ⬝ᵥ v) -
      matrixInner Y (matrixGramOperator A Y) - 2 * (v ⬝ᵥ intrinsicMixedGram A τ Y) -
      v ⬝ᵥ (vectorGramOperator τ *ᵥ v)) = fourthNormSq (V-jointTrialTensor A Y τ v) := by
  have he := joint_square_remainder A Y E had.1 hY τ had.2.1 v b₀ V hV hTV hNV
  unfold jointSquareBound at he
  rw [jointTrialTensor_norm A τ had Y hY hYtr v] at he
  convert he using 1 <;> ring

end
end SecondPinching
