import SecondPinching.ImmersionRicciSimonsBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem intrinsicCubicA_smul_both (a b : ℝ) (h : Matrix4) (T : Cubic4) :
    intrinsicCubicA (a • h) (b • T) = a^2*b^2*intrinsicCubicA h T := by
  simp only [intrinsicCubicA,pow_two,Matrix.smul_mul,Matrix.mul_smul,cubicGramMatrix_smul,
    smul_smul,Matrix.trace_smul,smul_eq_mul]
  ring

theorem intrinsicCubicB_smul_both (a b : ℝ) (h : Matrix4) (T : Cubic4) :
    intrinsicCubicB (a • h) (b • T) = a^2*b^2*intrinsicCubicB h T := by
  simp only [intrinsicCubicB,cubicInner,cubicMatrixAction,Matrix.smul_apply,Pi.smul_apply,
    smul_eq_mul,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro s _; ring

/-- Exact change of scale from the constant-S equation to eq:PTnorm. -/
theorem normalizeFourth_pengTerng (S : ℝ) (hS : 4 < S) (h : Matrix4) (T : Cubic4) (H : Fourth4)
    (hPT : fourthNormSq H = 3*(intrinsicCubicA h T-2*intrinsicCubicB h T)+(S-11)*S*(S-4)) :
    fourthNormSq (normalizeFourth S H) =
      3*pinchingParameter S*(intrinsicCubicA (normalizeSecond S h) (normalizeThird S T)-
        2*intrinsicCubicB (normalizeSecond S h) (normalizeThird S T))+
      pinchingParameter S*(11*pinchingParameter S-7)/4 := by
  obtain ⟨_,_,_,hsq,hdq⟩ := normalization_denominators hS
  have hs : S ≠ 0 := by linarith
  have hd : S-4 ≠ 0 := by linarith
  rw [normalizeFourth,fourthNormSq_smul,hPT,normalizeSecond,normalizeThird,
    intrinsicCubicA_smul_both,intrinsicCubicB_smul_both]
  simp only [inv_pow,mul_pow,hsq,hdq,pinchingParameter]
  field_simp
  ring

end
end SecondPinching
