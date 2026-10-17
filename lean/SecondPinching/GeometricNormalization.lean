import SecondPinching.LocalIntegral

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- The three scalings in eq:normalization and prop:reduction. The last
denominator is S sqrt S, i.e. S^(3/2) when S>0. -/
def normalizeSecond (S : ℝ) (h : Matrix4) : Matrix4 := (Real.sqrt S)⁻¹ • h
def normalizeThird (S : ℝ) (T : Cubic4) : Cubic4 :=
  (Real.sqrt (S*(S-4)))⁻¹ • T
def normalizeFourth (S : ℝ) (H : Fourth4) : Fourth4 := (S*Real.sqrt S)⁻¹ • H

theorem normalization_denominators {S : ℝ} (hS : 4 < S) :
    0 < Real.sqrt S ∧ 0 < Real.sqrt (S*(S-4)) ∧ 0 < S*Real.sqrt S ∧
    (Real.sqrt S)^2 = S ∧ (Real.sqrt (S*(S-4)))^2 = S*(S-4) := by
  have hs : 0 < S := by linarith
  have hd : 0 < S-4 := by linarith
  exact ⟨Real.sqrt_pos.2 hs,Real.sqrt_pos.2 (mul_pos hs hd),
    mul_pos hs (Real.sqrt_pos.2 hs),Real.sq_sqrt hs.le,
    Real.sq_sqrt (mul_pos hs hd).le⟩

theorem matrixNormSq_smul (c : ℝ) (h : Matrix4) :
    matrixNormSq (c • h) = c^2 * matrixNormSq h := by
  simp [matrixNormSq, mul_pow, Finset.mul_sum]

theorem cubicNormSq_smul (c : ℝ) (T : Cubic4) :
    cubicNormSq (c • T) = c^2 * cubicNormSq T := by
  simp [cubicNormSq, mul_pow, Finset.mul_sum]

theorem fourthNormSq_smul (c : ℝ) (H : Fourth4) :
    fourthNormSq (c • H) = c^2 * fourthNormSq H := by
  simp [fourthNormSq, mul_pow, Finset.mul_sum]

/-- The unnormalized minimality, Codazzi, Simons and differentiated trace
inputs imply the manuscript's literal admissibility statement. Their geometric
derivation is deliberately not packaged into the definition of a tensor. -/
theorem normalized_paperAdmissible (S : ℝ) (hS : 4 < S)
    (h : Matrix4) (T : Cubic4) (hsym : h.IsSymm) (hT : CubicSymmetric T)
    (htr : Matrix.trace h = 0) (hn : matrixNormSq h = S)
    (hSimons : cubicNormSq T = S*(S-4))
    (htrace : ∀ k, ∑ i, T i i k = 0)
    (hweighted : ∀ k, ∑ i, ∑ j, h i j * T i j k = 0) :
    PaperAdmissible (normalizeSecond S h) (normalizeThird S T) := by
  obtain ⟨hs,hd,_,hsq,hdq⟩ := normalization_denominators hS
  apply (admissible_iff_paper _ _).mp
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · ext i j
    simp only [normalizeSecond, Matrix.transpose_apply, Matrix.smul_apply, hsym.apply]
  · intro σ v
    simp only [normalizeThird, Pi.smul_apply, smul_eq_mul, hT σ v]
  · simp [normalizeSecond, Matrix.trace_smul, htr]
  · rw [normalizeSecond, matrixNormSq_smul, hn, inv_pow, hsq]
    exact inv_mul_cancel₀ (by linarith : S ≠ 0)
  · rw [normalizeThird, cubicNormSq_smul, hSimons, inv_pow, hdq]
    exact inv_mul_cancel₀ (mul_ne_zero (by linarith) (by linarith))
  · intro k
    simp [normalizeThird, ← Finset.mul_sum, htrace]
  · intro k
    have he : (∑ i, ∑ j, normalizeSecond S h i j * normalizeThird S T i j k) =
        (Real.sqrt S)⁻¹ * (Real.sqrt (S*(S-4)))⁻¹ * (∑ i, ∑ j, h i j * T i j k) := by
      simp [normalizeSecond,normalizeThird,Finset.mul_sum,mul_assoc,mul_left_comm]
    rw [he,hweighted k,mul_zero]

theorem normalize_frame (S : ℝ) (Q : Matrix4) (h : Matrix4) (T : Cubic4) (H : Fourth4) :
    normalizeSecond S (frameMatrix Q h) = frameMatrix Q (normalizeSecond S h) ∧
    normalizeThird S (frameCubic Q T) = frameCubic Q (normalizeThird S T) ∧
    normalizeFourth S (frameFourth Q H) = frameFourth Q (normalizeFourth S H) := by
  exact ⟨((frameMatrixLinear Q).map_smul _ _).symm,
    ((frameCubicLinear Q).map_smul _ _).symm,
    ((frameFourthLinear Q).map_smul _ _).symm⟩

theorem normalize_normal_reversal (S : ℝ) (h : Matrix4) (T : Cubic4) (H : Fourth4) :
    normalizeSecond S (-h) = -normalizeSecond S h ∧
    normalizeThird S (-T) = -normalizeThird S T ∧
    normalizeFourth S (-H) = -normalizeFourth S H := by
  simp [normalizeSecond,normalizeThird,normalizeFourth]

end
end SecondPinching
