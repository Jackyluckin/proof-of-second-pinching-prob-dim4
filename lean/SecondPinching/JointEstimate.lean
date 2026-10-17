import SecondPinching.GramOperators

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- Finite coordinate cases use a shared list of symmetry rewrites.
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- Pairing with K_A, retaining the trace term before restricting to Sym^2_0. -/
theorem matrixGram_pairing_identity_diagonal (μ : Vector4) (Y : Matrix4) (hY : Y.IsSymm) :
    matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) =
      (1/6 : ℝ) * matrixNormSq Y + (1/3 : ℝ) * Matrix.trace ((Matrix.diagonal μ)^2 * Y^2) +
      (1/12 : ℝ) * (∑ i, ∑ j, (μ i - μ j)^2 * (Y i j)^2) +
      (7/36 : ℝ) * (Matrix.trace (Matrix.diagonal μ * Y))^2 -
      (1/12 : ℝ) * Matrix.trace ((Matrix.diagonal μ)^2 * Y) * Matrix.trace Y := by
  simp [matrixInner, matrixGramOperator, matrixNormSq, pow_two, Matrix.mul_apply,
    Matrix.trace, Matrix.diag, Matrix.diagonal_apply, Matrix.one_apply,
    Fin.sum_univ_succ, hY.apply]
  simp only [hY.apply 0 1, hY.apply 0 2, hY.apply 0 3, hY.apply 1 2, hY.apply 1 3, hY.apply 2 3]
  ring

/-- The lower bound eq:Klower in the paper's principal-frame convention. -/
theorem matrixGram_lower_bound_diagonal (μ : Vector4) (Y : Matrix4)
    (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    (1/6 : ℝ) * matrixNormSq Y + (1/3 : ℝ) * Matrix.trace ((Matrix.diagonal μ)^2 * Y^2) ≤
      matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) := by
  rw [matrixGram_pairing_identity_diagonal μ Y hY, htr]
  have hs : 0 ≤ ∑ i, ∑ j, (μ i - μ j)^2 * (Y i j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [sq_nonneg (Matrix.trace (Matrix.diagonal μ * Y))]

theorem matrixInner_comm (X Y : Matrix4) : matrixInner X Y = matrixInner Y X := by
  simp only [matrixInner, mul_comm]

/-- The stated codomain of K_A in the principal frame is Sym^2_0. -/
theorem matrixGram_traceFree_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    (matrixGramOperator (Matrix.diagonal μ) Y).IsSymm ∧
      Matrix.trace (matrixGramOperator (Matrix.diagonal μ) Y) = 0 := by
  rw [← matrix_gram_identity_diagonal μ hμ hn Y hY htr]
  exact weightedTrace_traceFree _ _ (ordinaryTraceFreeProjection_mem _
    (weightedTraceAdjoint_symmetric _ _ (Matrix.isSymm_diagonal μ) hY))

theorem fourthInner_add_left (U V W : Fourth4) :
    fourthInner (U + V) W = fourthInner U W + fourthInner V W := by
  simp [fourthInner, add_mul, Finset.sum_add_distrib]

theorem ordinaryTraceFreeProjection_add (U V : Fourth4) :
    ordinaryTraceFreeProjection (U + V) =
      ordinaryTraceFreeProjection U + ordinaryTraceFreeProjection V :=
  (ordinaryTraceFreeProjectionLinear.map_add U V)

theorem traceFree_pairing_projection (V : Fourth4) (hV : TraceFreeFourth V)
    (U : Fourth4) (hU : FourthSymmetric U) :
    fourthInner V (ordinaryTraceFreeProjection U) = fourthInner V U := by
  have h := ordinaryTraceFreeProjection_orthogonal U hU V hV
  rw [fourthInner_comm, fourthInner_sub_right] at h
  linarith

/-- The norm of the actual projected trial tensor, evaluated using eq:Grams. -/
theorem jointTrialTensor_norm_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hw : ∀ k, ∑ i, μ i * τ i i k = 0)
    (hτn : cubicNormSq τ = 1) (Y : Matrix4) (hY : Y.IsSymm)
    (htr : Matrix.trace Y = 0) (v : Vector4) :
    fourthNormSq (jointTrialTensor (Matrix.diagonal μ) Y τ v) =
      matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) +
        2 * (v ⬝ᵥ mixedGramOperator μ τ Y) + v ⬝ᵥ (vectorGramOperator τ *ᵥ v) := by
  let F := weightedTraceAdjoint (Matrix.diagonal μ) Y
  let G := cubicContractionAdjoint τ v
  have hF : FourthSymmetric F := weightedTraceAdjoint_symmetric _ _ (Matrix.isSymm_diagonal μ) hY
  have hG : FourthSymmetric G := cubicContractionAdjoint_symmetric τ hτ v
  have hPF := ordinaryTraceFreeProjection_mem F hF
  have hPG := ordinaryTraceFreeProjection_mem G hG
  have hFF : fourthInner (ordinaryTraceFreeProjection F) (ordinaryTraceFreeProjection F) =
      matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) := by
    rw [traceFree_pairing_projection _ hPF F hF]
    rw [weightedTrace_adjoint_pairing _ Y (Matrix.isSymm_diagonal μ) hY _ hPF.1,
      matrix_gram_identity_diagonal μ hμ hn Y hY htr, matrixInner_comm]
  have hFG : fourthInner (ordinaryTraceFreeProjection F) (ordinaryTraceFreeProjection G) =
      v ⬝ᵥ mixedGramOperator μ τ Y := by
    rw [traceFree_pairing_projection _ hPF G hG]
    rw [cubicContraction_adjoint_pairing τ hτ v _ hPF.1,
      mixed_gram_identity_diagonal μ hμ τ hτ ht hw Y hY htr, dotProduct_comm]
  have hGG : fourthInner (ordinaryTraceFreeProjection G) (ordinaryTraceFreeProjection G) =
      v ⬝ᵥ (vectorGramOperator τ *ᵥ v) := by
    rw [traceFree_pairing_projection _ hPG G hG]
    rw [cubicContraction_adjoint_pairing τ hτ v _ hPG.1,
      vector_gram_identity τ hτ ht hτn v, dotProduct_comm]
  change fourthNormSq (ordinaryTraceFreeProjection (F + G)) = _
  rw [ordinaryTraceFreeProjection_add, ← fourthInner_self, fourthInner_add_left,
    fourthInner_add_right, fourthInner_add_right, fourthInner_comm (ordinaryTraceFreeProjection G),
    hFF, hFG, hGG]
  ring

/-- Exact component form of admissibility in a principal frame, including both traces. -/
theorem admissible_diagonal_iff (μ : Vector4) (τ : Cubic4) :
    Admissible (Matrix.diagonal μ) τ ↔
      CubicSymmetric τ ∧ (∑ i, μ i = 0) ∧ (∑ i, (μ i)^2 = 1) ∧
      cubicNormSq τ = 1 ∧ (∀ k, ∑ i, τ i i k = 0) ∧ (∀ k, ∑ i, μ i * τ i i k = 0) := by
  simp [Admissible, matrixNormSq, Matrix.trace, Matrix.diagonal_apply,
    Matrix.isSymm_diagonal]

/-- Lemma lem:Gram, including its lower bound, under the explicit
principal-frame convention immediately following Definition 2.2. -/
theorem contraction_lemma_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) (v : Vector4) :
    weightedTrace (Matrix.diagonal μ)
      (ordinaryTraceFreeProjection (weightedTraceAdjoint (Matrix.diagonal μ) Y)) =
        matrixGramOperator (Matrix.diagonal μ) Y ∧
    cubicContraction τ (ordinaryTraceFreeProjection (weightedTraceAdjoint (Matrix.diagonal μ) Y)) =
      mixedGramOperator μ τ Y ∧
    cubicContraction τ (ordinaryTraceFreeProjection (cubicContractionAdjoint τ v)) =
      vectorGramOperator τ *ᵥ v ∧
    (1/6 : ℝ) * matrixNormSq Y + (1/3 : ℝ) * Matrix.trace ((Matrix.diagonal μ)^2 * Y^2) ≤
      matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) := by
  obtain ⟨hτ, hμ, hn, hτn, ht, hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  exact ⟨matrix_gram_identity_diagonal μ hμ hn Y hY htr,
    mixed_gram_identity_diagonal μ hμ τ hτ ht hw Y hY htr,
    vector_gram_identity τ hτ ht hτn v, matrixGram_lower_bound_diagonal μ Y hY htr⟩

/-- Eq:joint with all its coordinate terms. The diagonal frame is explicit.
No assertion about the as-yet-unformalised orthogonal change of frame is used. -/
theorem joint_contraction_estimate_diagonal (μ : Vector4) (τ : Cubic4)
    (had : Admissible (Matrix.diagonal μ) τ)
    (E Y : Matrix4) (_hE : E.IsSymm) (_hEtr : Matrix.trace E = 0)
    (hY : Y.IsSymm) (hYtr : Matrix.trace Y = 0) (b₀ v : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V)
    (hTV : weightedTrace (Matrix.diagonal μ) V = E) (hNV : cubicContraction τ V = b₀) :
    2 * matrixInner E Y + 2 * (b₀ ⬝ᵥ v) -
      matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) -
      2 * (v ⬝ᵥ mixedGramOperator μ τ Y) - v ⬝ᵥ (vectorGramOperator τ *ᵥ v) ≤ fourthNormSq V := by
  obtain ⟨hτ, hμ, hn, hτn, ht, hw⟩ := (admissible_diagonal_iff μ τ).mp had
  have h := joint_square_estimate (Matrix.diagonal μ) Y E (Matrix.isSymm_diagonal μ)
    hY τ hτ v b₀ V hV hTV hNV
  unfold jointSquareBound at h
  rw [jointTrialTensor_norm_diagonal μ hμ hn τ hτ ht hw hτn Y hY hYtr v] at h
  linarith

/-- The exact square identity used later in the averaged integral identity. -/
theorem joint_contraction_remainder_diagonal (μ : Vector4) (τ : Cubic4)
    (had : Admissible (Matrix.diagonal μ) τ) (E Y : Matrix4)
    (hY : Y.IsSymm) (hYtr : Matrix.trace Y = 0) (b₀ v : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V)
    (hTV : weightedTrace (Matrix.diagonal μ) V = E) (hNV : cubicContraction τ V = b₀) :
    fourthNormSq V - (2 * matrixInner E Y + 2 * (b₀ ⬝ᵥ v) -
      matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) -
      2 * (v ⬝ᵥ mixedGramOperator μ τ Y) - v ⬝ᵥ (vectorGramOperator τ *ᵥ v)) =
        fourthNormSq (V - jointTrialTensor (Matrix.diagonal μ) Y τ v) := by
  obtain ⟨hτ, hμ, hn, hτn, ht, hw⟩ := (admissible_diagonal_iff μ τ).mp had
  have h := joint_square_remainder (Matrix.diagonal μ) Y E (Matrix.isSymm_diagonal μ)
    hY τ hτ v b₀ V hV hTV hNV
  unfold jointSquareBound at h
  rw [jointTrialTensor_norm_diagonal μ hμ hn τ hτ ht hw hτn Y hY hYtr v] at h
  linarith

end
end SecondPinching
