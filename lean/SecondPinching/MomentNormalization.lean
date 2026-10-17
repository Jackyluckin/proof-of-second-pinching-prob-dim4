import SecondPinching.ImmersionTracePowers

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem cubicMoment_smul (a : ℝ) (A : Matrix4) : cubicMoment (a • A)=a^3*cubicMoment A := by
  simp only [cubicMoment,smul_pow,Matrix.trace_smul,smul_eq_mul]

theorem quarticMoment_smul (a : ℝ) (A : Matrix4) : quarticMoment (a • A)=a^4*quarticMoment A := by
  simp only [quarticMoment,smul_pow,Matrix.trace_smul,smul_eq_mul]

theorem intrinsicCubicC_smul_both (a b : ℝ) (A : Matrix4) (T : Cubic4) :
    intrinsicCubicC (a • A) (b • T) = a*b^2*intrinsicCubicC A T := by
  simp only [intrinsicCubicC,cubicGramMatrix_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,Matrix.trace_smul,smul_eq_mul]
  ring

theorem intrinsicCubicD_smul_both (a b : ℝ) (A : Matrix4) (T : Cubic4) :
    intrinsicCubicD (a • A) (b • T) = (a^2*b) • intrinsicCubicD A T := by
  funext k
  simp only [intrinsicCubicD,smul_pow,cubicWeightedTrace,Matrix.smul_apply,Pi.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem dotProduct_smul_both_real (a : ℝ) (v : Vector4) :
    (a • v) ⬝ᵥ (a • v)=a^2*(v ⬝ᵥ v) := by
  simp only [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; ring

/-- The p identity uses only the matrix hypotheses; no cubic constraint is needed. -/
theorem phiNormSq_eq_moments (A : Matrix4) (hA : A.IsSymm)
    (htr : Matrix.trace A=0) (hn : matrixNormSq A=1) :
    phiNormSq A=quarticMoment A-(cubicMoment A)^2-1/4 := by
  obtain ⟨Q,μ,hQ,hd⟩ := symmetric_orthogonal_diagonalization A hA
  have ht : ∑ i, μ i=0 := by rw [← Matrix.trace_diagonal,← hd,frameMatrix_trace Q hQ,htr]
  have hs : ∑ i, (μ i)^2=1 := by rw [← matrixNormSq_diagonal,← hd,frameMatrix_normSq Q hQ,hn]
  have he := phiNormSq_diagonal μ ht hs
  rw [← hd,frame_phiNormSq Q hQ,frame_quarticMoment Q hQ,frame_cubicMoment Q hQ] at he
  exact he

theorem normalizedSecond_trace_norm (S : ℝ) (hS : 4<S) (h : Matrix4)
    (htr : Matrix.trace h=0) (hn : matrixNormSq h=S) :
    Matrix.trace (normalizeSecond S h)=0 ∧ matrixNormSq (normalizeSecond S h)=1 := by
  have hs : S≠0 := by linarith
  obtain ⟨_,_,_,ha,_⟩ := normalization_denominators hS
  constructor
  · simp [normalizeSecond,Matrix.trace_smul,htr]
  · rw [normalizeSecond,matrixNormSq_smul,hn,inv_pow,ha,inv_mul_cancel₀ hs]

/-- Exact unnormalized expression for the existing L4 correction. -/
theorem normalizedCorrectionL4 (S : ℝ) (hS : 4<S) (h : Matrix4) (T : Cubic4) :
    intrinsicCorrectionL4 (normalizeSecond S h) (normalizeThird S T) (pinchingParameter S) =
      ((4-S)*quarticMoment h+2*intrinsicCubicA h T+intrinsicCubicB h T)/S^3 := by
  obtain ⟨_,_,_,ha,hb⟩ := normalization_denominators hS
  have hs : S≠0 := by linarith
  have hd : S-4≠0 := by linarith
  simp only [intrinsicCorrectionL4,normalizeSecond,normalizeThird,intrinsicCubicA_smul_both,
    intrinsicCubicB_smul_both,quarticMoment_smul,inv_pow,ha,hb,pinchingParameter]
  have h4 : (Real.sqrt S)^4=S^2 := by nlinarith [ha]
  rw [h4]
  field_simp
  ring

/-- Exact L3 scaling retains the nonzero cubic-trace gradient term. -/
theorem normalizedCorrectionL3 (S : ℝ) (hS : 4<S) (h : Matrix4) (T : Cubic4) :
    intrinsicCorrectionL3 (normalizeSecond S h) (normalizeThird S T) (pinchingParameter S) =
      ((4-S)*(cubicMoment h)^2+2*cubicMoment h*intrinsicCubicC h T+
        3*(intrinsicCubicD h T ⬝ᵥ intrinsicCubicD h T))/S^4 := by
  obtain ⟨ha0,hb0,_,ha,hb⟩ := normalization_denominators hS
  have hs : S≠0 := by linarith
  have hd : S-4≠0 := by linarith
  simp only [intrinsicCorrectionL3,normalizeSecond,normalizeThird,cubicMoment_smul,
    intrinsicCubicC_smul_both,intrinsicCubicD_smul_both,dotProduct_smul_both_real,
    pinchingParameter]
  have h6 : (Real.sqrt S)^6=S^3 := by
    calc
      _ = ((Real.sqrt S)^2)^3 := by ring
      _ = _ := by rw [ha]
  field_simp
  simp only [h6,ha,hb]
  ring

/-- Exact J scaling uses the unaltered matrix p=|Phi|^2. -/
theorem normalizedCorrectionJ (S : ℝ) (hS : 4<S) (h : Matrix4) (T : Cubic4)
    (hh : h.IsSymm) (htr : Matrix.trace h=0) (hn : matrixNormSq h=S) :
    intrinsicCorrectionJ (normalizeSecond S h) (normalizeThird S T) (pinchingParameter S) =
      -(2*intrinsicCubicB h T-intrinsicCubicA h T+S*quarticMoment h-(cubicMoment h)^2-S^2)/S^3 := by
  have hs : (normalizeSecond S h).IsSymm := by
    ext i j
    simp only [normalizeSecond,Matrix.transpose_apply,Matrix.smul_apply,hh.apply]
  have htn := normalizedSecond_trace_norm S hS h htr hn
  obtain ⟨ha0,hb0,_,ha,hb⟩ := normalization_denominators hS
  have hS0 : S≠0 := by linarith
  have hd : S-4≠0 := by linarith
  rw [intrinsicCorrectionJ,phiNormSq_eq_moments _ hs htn.1 htn.2]
  simp only [normalizeSecond,normalizeThird,intrinsicCubicA_smul_both,
    intrinsicCubicB_smul_both,cubicMoment_smul,quarticMoment_smul,pinchingParameter]
  have h4 : (Real.sqrt S)^4=S^2 := by
    calc
      _ = ((Real.sqrt S)^2)^2 := by ring
      _ = _ := by rw [ha]
  have h6 : (Real.sqrt S)^6=S^3 := by
    calc
      _ = ((Real.sqrt S)^2)^3 := by ring
      _ = _ := by rw [ha]
  field_simp
  simp only [h4,h6,ha,hb]
  ring

end
end SecondPinching
