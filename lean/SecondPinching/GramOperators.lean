import SecondPinching.JointContractions

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- Finite coordinate cases use a shared list of symmetry rewrites.
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- K_A, with precisely the coefficients in eq:K. -/
def matrixGramOperator (A Y : Matrix4) : Matrix4 :=
  (1/6 : ℝ) • Y + (1/4 : ℝ) • (A^2 * Y + Y * A^2) -
    (1/6 : ℝ) • (A * Y * A) + ((7/36 : ℝ) * Matrix.trace (A * Y)) • A -
    ((1/12 : ℝ) * Matrix.trace (A^2 * Y)) • (1 : Matrix4)

/-- Z in a principal frame, eq:ZH. -/
def mixedGramOperator (μ : Vector4) (τ : Cubic4) (Y : Matrix4) : Vector4 :=
  fun l => (1/8 : ℝ) * ∑ i, ∑ j, (4 * μ l - μ i - μ j) * τ i j l * Y i j

/-- R, the ordered-index cubic Gram matrix, eq:Rmu. -/
def cubicGramMatrix (τ : Cubic4) : Matrix4 :=
  fun k l => ∑ i, ∑ j, τ i j k * τ i j l

/-- H_tau in eq:ZH. -/
def vectorGramOperator (τ : Cubic4) : Matrix4 :=
  (1/4 : ℝ) • (1 : Matrix4) + (9/16 : ℝ) • cubicGramMatrix τ

/-- Raw ordinary trace, before using either trace-zero condition. -/
theorem ordinaryTrace_weightedTraceAdjoint_diagonal (μ : Vector4) (Y : Matrix4)
    (hY : Y.IsSymm) :
    ordinaryTrace (weightedTraceAdjoint (Matrix.diagonal μ) Y) = fun k l =>
      ((∑ i, μ i) * Y k l + 2 * (μ k + μ l) * Y k l +
        (Matrix.diagonal μ) k l * Matrix.trace Y) / 6 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [ordinaryTrace, weightedTraceAdjoint, Matrix.diagonal_apply, Matrix.trace,
      Fin.sum_univ_succ, hY.apply] <;> (try simp only [hY.apply 0 1, hY.apply 0 2, hY.apply 0 3, hY.apply 1 2, hY.apply 1 3, hY.apply 2 3]) <;> ring

/-- Raw weighted Gram contraction, before imposing unit norm. -/
theorem weightedTrace_weightedTraceAdjoint_diagonal (μ : Vector4) (Y : Matrix4)
    (hY : Y.IsSymm) :
    weightedTrace (Matrix.diagonal μ) (weightedTraceAdjoint (Matrix.diagonal μ) Y) =
      fun k l => ((∑ i, (μ i)^2) * Y k l + 2 * ((μ k)^2 + (μ l)^2) * Y k l +
        (Matrix.diagonal μ) k l * (∑ i, μ i * Y i i)) / 6 := by
  rw [weightedTrace_diagonal]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [weightedTraceAdjoint, Matrix.diagonal_apply, Fin.sum_univ_succ, hY.apply] <;> (try simp only [hY.apply 0 1, hY.apply 0 2, hY.apply 0 3, hY.apply 1 2, hY.apply 1 3, hY.apply 2 3]) <;> ring

/-- The trace-removing matrix J T_0 T_A^*Y in the proof of lem:Gram. -/
theorem weightedTrace_traceCorrection_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    ordinaryTraceGramInverse (ordinaryTrace (weightedTraceAdjoint (Matrix.diagonal μ) Y)) =
      fun k l => (μ k + μ l) * Y k l / 4 -
        (1 : Matrix4) k l * (∑ i, μ i * Y i i) / 24 := by
  rw [ordinaryTrace_weightedTraceAdjoint_diagonal μ Y hY]
  simp only [hμ, htr, zero_mul, mul_zero, add_zero, zero_add]
  ext k l
  change (3/4 : ℝ) * (2 * (μ k + μ l) * Y k l / 6) -
    (Matrix.trace (fun a b => 2 * (μ a + μ b) * Y a b / 6) / 16) * (1 : Matrix4) k l = _
  fin_cases k <;> fin_cases l <;>
    simp [ordinaryTraceGramInverse, Matrix.trace, Matrix.diag, Matrix.smul_apply, Pi.smul_apply, Pi.smul_def, smul_eq_mul, Fin.sum_univ_succ] <;> ring

/-- T_A T_0^* applied to any symmetric matrix; sum(mu) is kept explicit. -/
theorem weightedTrace_ordinaryTraceAdjoint_diagonal (μ : Vector4) (X : Matrix4)
    (hX : X.IsSymm) :
    weightedTrace (Matrix.diagonal μ) (ordinaryTraceAdjoint X) = fun k l =>
      ((∑ i, μ i) * X k l + 2 * (μ k + μ l) * X k l +
        (1 : Matrix4) k l * (∑ i, μ i * X i i)) / 6 := by
  rw [weightedTrace_diagonal]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [ordinaryTraceAdjoint, Matrix.one_apply, Fin.sum_univ_succ, hX.apply] <;> (try simp only [hX.apply 0 1, hX.apply 0 2, hX.apply 0 3, hX.apply 1 2, hX.apply 1 3, hX.apply 2 3]) <;> ring

/-- The first Gram identity in eq:Grams, in the paper's principal frame. -/
theorem matrix_gram_identity_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    weightedTrace (Matrix.diagonal μ)
      (ordinaryTraceFreeProjection (weightedTraceAdjoint (Matrix.diagonal μ) Y)) =
        matrixGramOperator (Matrix.diagonal μ) Y := by
  have hJ := ordinaryTraceGramInverse_symmetric _
    (ordinaryTrace_symmetric (weightedTraceAdjoint_symmetric _ _ (Matrix.isSymm_diagonal μ) hY))
  change weightedTraceLinear (Matrix.diagonal μ) (_ - _) = _
  rw [map_sub]
  change weightedTrace _ _ - weightedTrace _ _ = _
  rw [weightedTrace_weightedTraceAdjoint_diagonal μ Y hY,
    weightedTrace_ordinaryTraceAdjoint_diagonal μ _ hJ,
    weightedTrace_traceCorrection_diagonal μ hμ Y hY htr]
  simp only [hn, hμ, zero_mul, zero_add, one_mul]
  ext k l
  change (Y k l + 2 * ((μ k)^2 + (μ l)^2) * Y k l +
    (Matrix.diagonal μ) k l * (∑ i, μ i * Y i i)) / 6 -
    (2 * (μ k + μ l) * ((μ k + μ l) * Y k l / 4 - (1 : Matrix4) k l * (∑ i, μ i * Y i i) / 24) +
      (1 : Matrix4) k l * (∑ i, μ i * ((μ i + μ i) * Y i i / 4 - (1 : Matrix4) i i * (∑ j, μ j * Y j j) / 24))) / 6 = _
  fin_cases k <;> fin_cases l <;>
    simp [matrixGramOperator, Pi.sub_apply, Pi.sub_def, Matrix.sub_apply, pow_two, Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.one_apply,
      Matrix.diagonal_apply, Fin.sum_univ_succ] <;> ring_nf
  all_goals simp [Fin.sum_univ_succ] at hμ
  all_goals linear_combination (1/144 : ℝ) * (μ 0 * Y 0 0 + μ 1 * Y 1 1 + μ 2 * Y 2 2 + μ 3 * Y 3 3) * hμ

/-- The raw mixed contraction, before the weighted trace constraint on tau. -/
theorem cubicContraction_weightedTraceAdjoint_diagonal (μ : Vector4)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (Y : Matrix4) (hY : Y.IsSymm) :
    cubicContraction τ (weightedTraceAdjoint (Matrix.diagonal μ) Y) = fun l =>
      ((∑ k, (∑ i, μ i * τ i i k) * Y k l) + μ l * (∑ i, ∑ j, τ i j l * Y i j)) / 2 := by
  funext l
  fin_cases l <;>
    simp [cubicContraction, weightedTraceAdjoint, Matrix.diagonal_apply, Fin.sum_univ_succ,
      cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ, hY.apply] <;> (try simp only [hY.apply 0 1, hY.apply 0 2, hY.apply 0 3, hY.apply 1 2, hY.apply 1 3, hY.apply 2 3]) <;> (try simp only [cubicSymmetric_swap12 hτ 0 1,
      cubicSymmetric_swap12 hτ 0 2,
      cubicSymmetric_swap12 hτ 0 3,
      cubicSymmetric_swap12 hτ 1 2,
      cubicSymmetric_swap12 hτ 1 3,
      cubicSymmetric_swap12 hτ 2 3,
      cubicSymmetric_swap23 hτ 0 0 1,
      cubicSymmetric_swap23 hτ 0 0 2,
      cubicSymmetric_swap23 hτ 0 0 3,
      cubicSymmetric_swap23 hτ 0 1 2,
      cubicSymmetric_swap23 hτ 0 1 3,
      cubicSymmetric_swap23 hτ 0 2 3,
      cubicSymmetric_swap23 hτ 1 0 1,
      cubicSymmetric_swap23 hτ 1 0 2,
      cubicSymmetric_swap23 hτ 1 0 3,
      cubicSymmetric_swap23 hτ 1 1 2,
      cubicSymmetric_swap23 hτ 1 1 3,
      cubicSymmetric_swap23 hτ 1 2 3,
      cubicSymmetric_swap23 hτ 2 0 1,
      cubicSymmetric_swap23 hτ 2 0 2,
      cubicSymmetric_swap23 hτ 2 0 3,
      cubicSymmetric_swap23 hτ 2 1 2,
      cubicSymmetric_swap23 hτ 2 1 3,
      cubicSymmetric_swap23 hτ 2 2 3,
      cubicSymmetric_swap23 hτ 3 0 1,
      cubicSymmetric_swap23 hτ 3 0 2,
      cubicSymmetric_swap23 hτ 3 0 3,
      cubicSymmetric_swap23 hτ 3 1 2,
      cubicSymmetric_swap23 hτ 3 1 3,
      cubicSymmetric_swap23 hτ 3 2 3]) <;> ring

/-- The trace correction contracted against tau, before its ordinary trace vanishes. -/
theorem cubicContraction_ordinaryTraceAdjoint (τ : Cubic4) (hτ : CubicSymmetric τ)
    (X : Matrix4) (hX : X.IsSymm) :
    cubicContraction τ (ordinaryTraceAdjoint X) = fun l =>
      ((∑ k, (∑ i, τ i i k) * X k l) + (∑ i, ∑ j, τ i j l * X i j)) / 2 := by
  funext l
  fin_cases l <;>
    simp [cubicContraction, ordinaryTraceAdjoint, Matrix.one_apply, Fin.sum_univ_succ,
      cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ, hX.apply] <;> (try simp only [hX.apply 0 1, hX.apply 0 2, hX.apply 0 3, hX.apply 1 2, hX.apply 1 3, hX.apply 2 3]) <;> (try simp only [cubicSymmetric_swap12 hτ 0 1,
      cubicSymmetric_swap12 hτ 0 2,
      cubicSymmetric_swap12 hτ 0 3,
      cubicSymmetric_swap12 hτ 1 2,
      cubicSymmetric_swap12 hτ 1 3,
      cubicSymmetric_swap12 hτ 2 3,
      cubicSymmetric_swap23 hτ 0 0 1,
      cubicSymmetric_swap23 hτ 0 0 2,
      cubicSymmetric_swap23 hτ 0 0 3,
      cubicSymmetric_swap23 hτ 0 1 2,
      cubicSymmetric_swap23 hτ 0 1 3,
      cubicSymmetric_swap23 hτ 0 2 3,
      cubicSymmetric_swap23 hτ 1 0 1,
      cubicSymmetric_swap23 hτ 1 0 2,
      cubicSymmetric_swap23 hτ 1 0 3,
      cubicSymmetric_swap23 hτ 1 1 2,
      cubicSymmetric_swap23 hτ 1 1 3,
      cubicSymmetric_swap23 hτ 1 2 3,
      cubicSymmetric_swap23 hτ 2 0 1,
      cubicSymmetric_swap23 hτ 2 0 2,
      cubicSymmetric_swap23 hτ 2 0 3,
      cubicSymmetric_swap23 hτ 2 1 2,
      cubicSymmetric_swap23 hτ 2 1 3,
      cubicSymmetric_swap23 hτ 2 2 3,
      cubicSymmetric_swap23 hτ 3 0 1,
      cubicSymmetric_swap23 hτ 3 0 2,
      cubicSymmetric_swap23 hτ 3 0 3,
      cubicSymmetric_swap23 hτ 3 1 2,
      cubicSymmetric_swap23 hτ 3 1 3,
      cubicSymmetric_swap23 hτ 3 2 3]) <;> ring

/-- The second Gram identity in eq:Grams; neither trace condition is strengthened. -/
theorem mixed_gram_identity_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (ht : ∀ k, ∑ i, τ i i k = 0)
    (hw : ∀ k, ∑ i, μ i * τ i i k = 0)
    (Y : Matrix4) (hY : Y.IsSymm) (htr : Matrix.trace Y = 0) :
    cubicContraction τ
      (ordinaryTraceFreeProjection (weightedTraceAdjoint (Matrix.diagonal μ) Y)) =
        mixedGramOperator μ τ Y := by
  have hJ := ordinaryTraceGramInverse_symmetric _
    (ordinaryTrace_symmetric (weightedTraceAdjoint_symmetric _ _ (Matrix.isSymm_diagonal μ) hY))
  change cubicContractionLinear τ (_ - _) = _
  rw [map_sub]
  change cubicContraction _ _ - cubicContraction _ _ = _
  rw [cubicContraction_weightedTraceAdjoint_diagonal μ τ hτ Y hY,
    cubicContraction_ordinaryTraceAdjoint τ hτ _ hJ,
    weightedTrace_traceCorrection_diagonal μ hμ Y hY htr]
  simp only [hw, ht, zero_mul, Finset.sum_const_zero, zero_add]
  funext l
  fin_cases l <;>
    simp [mixedGramOperator, Pi.sub_apply, Pi.sub_def, Matrix.one_apply, Fin.sum_univ_succ, cubicSymmetric_swap12 hτ,
      cubicSymmetric_swap23 hτ, hY.apply] <;> (try simp only [hY.apply 0 1, hY.apply 0 2, hY.apply 0 3, hY.apply 1 2, hY.apply 1 3, hY.apply 2 3]) <;> (try simp only [cubicSymmetric_swap12 hτ 0 1,
      cubicSymmetric_swap12 hτ 0 2,
      cubicSymmetric_swap12 hτ 0 3,
      cubicSymmetric_swap12 hτ 1 2,
      cubicSymmetric_swap12 hτ 1 3,
      cubicSymmetric_swap12 hτ 2 3,
      cubicSymmetric_swap23 hτ 0 0 1,
      cubicSymmetric_swap23 hτ 0 0 2,
      cubicSymmetric_swap23 hτ 0 0 3,
      cubicSymmetric_swap23 hτ 0 1 2,
      cubicSymmetric_swap23 hτ 0 1 3,
      cubicSymmetric_swap23 hτ 0 2 3,
      cubicSymmetric_swap23 hτ 1 0 1,
      cubicSymmetric_swap23 hτ 1 0 2,
      cubicSymmetric_swap23 hτ 1 0 3,
      cubicSymmetric_swap23 hτ 1 1 2,
      cubicSymmetric_swap23 hτ 1 1 3,
      cubicSymmetric_swap23 hτ 1 2 3,
      cubicSymmetric_swap23 hτ 2 0 1,
      cubicSymmetric_swap23 hτ 2 0 2,
      cubicSymmetric_swap23 hτ 2 0 3,
      cubicSymmetric_swap23 hτ 2 1 2,
      cubicSymmetric_swap23 hτ 2 1 3,
      cubicSymmetric_swap23 hτ 2 2 3,
      cubicSymmetric_swap23 hτ 3 0 1,
      cubicSymmetric_swap23 hτ 3 0 2,
      cubicSymmetric_swap23 hτ 3 0 3,
      cubicSymmetric_swap23 hτ 3 1 2,
      cubicSymmetric_swap23 hτ 3 1 3,
      cubicSymmetric_swap23 hτ 3 2 3]) <;> ring_nf
  all_goals
    have ht0 := ht 0
    have ht1 := ht 1
    have ht2 := ht 2
    have ht3 := ht 3
    simp [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ] at ht0 ht1 ht2 ht3
    try simp only [cubicSymmetric_swap12 hτ 0 1,
      cubicSymmetric_swap12 hτ 0 2,
      cubicSymmetric_swap12 hτ 0 3,
      cubicSymmetric_swap12 hτ 1 2,
      cubicSymmetric_swap12 hτ 1 3,
      cubicSymmetric_swap12 hτ 2 3,
      cubicSymmetric_swap23 hτ 0 0 1,
      cubicSymmetric_swap23 hτ 0 0 2,
      cubicSymmetric_swap23 hτ 0 0 3,
      cubicSymmetric_swap23 hτ 0 1 2,
      cubicSymmetric_swap23 hτ 0 1 3,
      cubicSymmetric_swap23 hτ 0 2 3,
      cubicSymmetric_swap23 hτ 1 0 1,
      cubicSymmetric_swap23 hτ 1 0 2,
      cubicSymmetric_swap23 hτ 1 0 3,
      cubicSymmetric_swap23 hτ 1 1 2,
      cubicSymmetric_swap23 hτ 1 1 3,
      cubicSymmetric_swap23 hτ 1 2 3,
      cubicSymmetric_swap23 hτ 2 0 1,
      cubicSymmetric_swap23 hτ 2 0 2,
      cubicSymmetric_swap23 hτ 2 0 3,
      cubicSymmetric_swap23 hτ 2 1 2,
      cubicSymmetric_swap23 hτ 2 1 3,
      cubicSymmetric_swap23 hτ 2 2 3,
      cubicSymmetric_swap23 hτ 3 0 1,
      cubicSymmetric_swap23 hτ 3 0 2,
      cubicSymmetric_swap23 hτ 3 0 3,
      cubicSymmetric_swap23 hτ 3 1 2,
      cubicSymmetric_swap23 hτ 3 1 3,
      cubicSymmetric_swap23 hτ 3 2 3] at ht0 ht1 ht2 ht3
    first
    | linear_combination (μ 0 * Y 0 0 + μ 1 * Y 1 1 + μ 2 * Y 2 2 + μ 3 * Y 3 3) / 48 * ht0
    | linear_combination (μ 0 * Y 0 0 + μ 1 * Y 1 1 + μ 2 * Y 2 2 + μ 3 * Y 3 3) / 48 * ht1
    | linear_combination (μ 0 * Y 0 0 + μ 1 * Y 1 1 + μ 2 * Y 2 2 + μ 3 * Y 3 3) / 48 * ht2
    | linear_combination (μ 0 * Y 0 0 + μ 1 * Y 1 1 + μ 2 * Y 2 2 + μ 3 * Y 3 3) / 48 * ht3

/-- Raw N_tau N_tau^*, with no trace or norm hypotheses. -/
theorem cubicContraction_cubicContractionAdjoint (τ : Cubic4) (hτ : CubicSymmetric τ)
    (v : Vector4) :
    cubicContraction τ (cubicContractionAdjoint τ v) = fun l =>
      (cubicNormSq τ * v l + 3 * (cubicGramMatrix τ *ᵥ v) l) / 4 := by
  funext l
  fin_cases l <;>
    simp [cubicContraction, cubicContractionAdjoint, cubicNormSq, cubicGramMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ] <;> ring

/-- Raw T_0 N_tau^*, with both ordinary trace contributions retained. -/
theorem ordinaryTrace_cubicContractionAdjoint (τ : Cubic4) (_hτ : CubicSymmetric τ)
    (v : Vector4) :
    ordinaryTrace (cubicContractionAdjoint τ v) = fun k l =>
      ((∑ i, τ i i k) * v l + (∑ i, τ i i l) * v k + 2 * (∑ i, τ i k l * v i)) / 4 := by
  ext k l
  simp [ordinaryTrace, cubicContractionAdjoint, Fin.sum_univ_succ]
  ring

/-- With the ordinary trace constraint, J T_0 N_tau^*v has coefficient 3/8. -/
theorem cubicContraction_traceCorrection (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (v : Vector4) :
    ordinaryTraceGramInverse (ordinaryTrace (cubicContractionAdjoint τ v)) =
      fun k l => (3/8 : ℝ) * ∑ i, τ i k l * v i := by
  rw [ordinaryTrace_cubicContractionAdjoint τ hτ v]
  simp only [ht, zero_mul, zero_add]
  have hz : Matrix.trace (fun k l => 2 * (∑ i, τ i k l * v i) / 4) = 0 := by
    calc
      _ = (1/2 : ℝ) * ∑ i, (∑ k, τ k k i) * v i := by
        simp [Matrix.trace, Matrix.diag, Fin.sum_univ_succ,
          cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
        ring
      _ = 0 := by simp [ht]

  ext k l
  change (3/4 : ℝ) * (2 * (∑ i, τ i k l * v i) / 4) -
    Matrix.trace (fun a b => 2 * (∑ i, τ i a b * v i) / 4) / 16 * (1 : Matrix4) k l = _
  rw [hz]
  simp [ordinaryTraceGramInverse, Matrix.smul_apply, Pi.smul_apply, Pi.smul_def, smul_eq_mul, hz]
  ring

/-- The third Gram identity in eq:Grams. The weighted trace is not needed here. -/
theorem vector_gram_identity (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hn : cubicNormSq τ = 1) (v : Vector4) :
    cubicContraction τ (ordinaryTraceFreeProjection (cubicContractionAdjoint τ v)) =
      vectorGramOperator τ *ᵥ v := by
  have hJ := ordinaryTraceGramInverse_symmetric _
    (ordinaryTrace_symmetric (cubicContractionAdjoint_symmetric τ hτ v))
  change cubicContractionLinear τ (_ - _) = _
  rw [map_sub]
  change cubicContraction _ _ - cubicContraction _ _ = _
  rw [cubicContraction_cubicContractionAdjoint τ hτ v,
    cubicContraction_ordinaryTraceAdjoint τ hτ _ hJ,
    cubicContraction_traceCorrection τ hτ ht v]
  simp only [hn, ht, zero_mul, Finset.sum_const_zero, zero_add, one_mul]
  funext l
  fin_cases l <;>
    simp [vectorGramOperator, Pi.sub_apply, Matrix.one_apply, cubicGramMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ] <;> ring

end
end SecondPinching
