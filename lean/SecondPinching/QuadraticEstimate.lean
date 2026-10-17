import SecondPinching.CubicOperatorBound
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- The positive Gram form, with its actual ordered contraction. -/
theorem cubicGramMatrix_quadratic (τ : Cubic4) (v : Vector4) :
    v ⬝ᵥ (cubicGramMatrix τ *ᵥ v) = matrixNormSq (directionalCubic τ v) := by
  simp [directionalCubic, matrixNormSq, cubicGramMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- The spectral scalar estimate used in lem:Ebound. -/
theorem bounded_probability_four_sq (ρ : Vector4) (h0 : ∀ i, 0 ≤ ρ i)
    (h2 : ∀ i, ρ i ≤ 2/3) (hs : ∑ i, ρ i = 1) : ∑ i, (ρ i)^2 ≤ 5/9 := by
  classical
  by_cases hhalf : ∀ i, ρ i ≤ 1/2
  · have he : ∑ i, (ρ i)^2 ≤ ∑ i, (1/2 : ℝ)*ρ i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_nonneg (h0 i) (sub_nonneg.mpr (hhalf i))]
    rw [← Finset.mul_sum, hs] at he
    linarith
  · push_neg at hhalf
    obtain ⟨k,hk⟩ := hhalf
    have he := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ.erase k) (f := ρ) (fun i _ => h0 i)
    have hlin := Finset.sum_erase_add Finset.univ ρ (Finset.mem_univ k)
    have hsq := Finset.sum_erase_add Finset.univ (fun i => (ρ i)^2) (Finset.mem_univ k)
    rw [hs] at hlin
    have hh : (∑ i ∈ Finset.univ.erase k, ρ i) = 1-ρ k := by linarith
    rw [hh] at he
    nlinarith [mul_nonneg (sub_nonneg.mpr (h2 k)) (show 0 ≤ ρ k-1/3 by linarith)]

/-- The ordered squared norm is the sum of squared real eigenvalues. -/
theorem symmetric_matrix_norm_spectral (R : Matrix4) (hR : R.IsSymm) :
    matrixNormSq R = ∑ i, ((Matrix.isHermitian_iff_isSymm.mpr hR).eigenvalues i)^2 := by
  let hH : R.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hR
  let Λ : Matrix4 := Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  calc
    matrixNormSq R = Matrix.trace (R^2) := by
      rw [← matrixInner_self, matrixInner_eq_trace_mul R R hR, pow_two]
    _ = Matrix.trace (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary (Λ^2)) := by
      rw [map_pow]
      congr 2
      exact hH.spectral_theorem
    _ = Matrix.trace (Λ^2) := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
      simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
    _ = ∑ i, (hH.eigenvalues i)^2 := by
      simp [Λ, Matrix.diagonal_pow, Matrix.trace_diagonal, Function.comp_def]

/-- Unit norm of each real spectral basis vector, in the paper's dot product. -/
theorem real_eigenvector_dot_self (R : Matrix4) (hR : R.IsHermitian) (i : Fin 4) :
    (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hR.eigenvectorBasis i).ofLp = 1 := by
  have h := real_inner_self_eq_norm_sq (hR.eigenvectorBasis i)
  rw [hR.eigenvectorBasis.orthonormal.1 i] at h
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa only [star_trivial, one_pow] using h

/-- The bound tr(R^2)<=5/9 from the eigenvalues in [0,2/3]. -/
theorem cubicGramMatrix_norm_bound (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hτn : cubicNormSq τ = 1) :
    matrixNormSq (cubicGramMatrix τ) ≤ 5/9 := by
  let hR : (cubicGramMatrix τ).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr (cubicGramMatrix_symmetric τ)
  have h0 : ∀ i, 0 ≤ hR.eigenvalues i := by
    intro i
    have he := hR.eigenvalues_eq i
    change hR.eigenvalues i = (hR.eigenvectorBasis i).ofLp ⬝ᵥ
      (cubicGramMatrix τ *ᵥ (hR.eigenvectorBasis i).ofLp) at he
    rw [he, cubicGramMatrix_quadratic]
    exact matrixNormSq_nonneg _
  have h2 : ∀ i, hR.eigenvalues i ≤ 2/3 := by
    intro i
    have hb := cubicGramMatrix_bound τ hτ ht hτn (hR.eigenvectorBasis i).ofLp
    rw [real_eigenvector_dot_self _ hR i, mul_one] at hb
    have he := hR.eigenvalues_eq i
    change hR.eigenvalues i = (hR.eigenvectorBasis i).ofLp ⬝ᵥ
      (cubicGramMatrix τ *ᵥ (hR.eigenvectorBasis i).ofLp) at he
    rwa [← he] at hb
  have hs : ∑ i, hR.eigenvalues i = 1 := by
    have he := hR.trace_eq_sum_eigenvalues
    change Matrix.trace (cubicGramMatrix τ) = ∑ i, hR.eigenvalues i at he
    rw [← he, trace_cubicGramMatrix, hτn]
  rw [symmetric_matrix_norm_spectral _ (cubicGramMatrix_symmetric τ)]
  exact bounded_probability_four_sq hR.eigenvalues h0 h2 hs

/-- Centering R at I/4 gives the constant used in the square completion. -/
theorem centered_cubicGramMatrix_bound (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hτn : cubicNormSq τ = 1) :
    matrixNormSq (cubicGramMatrix τ-(1/4 : ℝ) • (1 : Matrix4)) ≤ 11/36 := by
  have hnorm := cubicGramMatrix_norm_bound τ hτ ht hτn
  have he : matrixNormSq (cubicGramMatrix τ-(1/4 : ℝ) • (1 : Matrix4)) =
      matrixNormSq (cubicGramMatrix τ)-(1/2 : ℝ)*Matrix.trace (cubicGramMatrix τ)+1/4 := by
    simp [matrixNormSq, Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_succ]
    ring
  rw [he, trace_cubicGramMatrix, hτn]
  linarith

/-- Square completion after taking the trace against the positive diagonal A^2.
The remainder is a sum of weighted squares, so no order-preservation is assumed. -/
theorem weighted_matrix_square_bound (μ : Vector4) (hn : ∑ i, (μ i)^2 = 1)
    (X : Matrix4) (hX : X.IsSymm) :
    (1/2 : ℝ)*Matrix.trace ((Matrix.diagonal μ)^2*X)-
      (1/3 : ℝ)*Matrix.trace ((Matrix.diagonal μ)^2*X^2) ≤ 3/16 := by
  have he : (1/2 : ℝ)*Matrix.trace ((Matrix.diagonal μ)^2*X)-
      (1/3 : ℝ)*Matrix.trace ((Matrix.diagonal μ)^2*X^2) =
      (3/16 : ℝ)*(∑ i, (μ i)^2)-
      (1/3 : ℝ)*(∑ i, ∑ j, (μ i)^2*(X i j-(3/4 : ℝ)*(1 : Matrix4) i j)^2) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two, Matrix.diagonal_apply,
      Matrix.one_apply, Fin.sum_univ_succ, hX.apply]
    simp only [hX.apply 0 1, hX.apply 0 2, hX.apply 0 3, hX.apply 1 2, hX.apply 1 3, hX.apply 2 3]
    ring
  rw [he, hn]
  have hs : 0 ≤ ∑ i, ∑ j, (μ i)^2*(X i j-(3/4 : ℝ)*(1 : Matrix4) i j)^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

theorem matrix_square_completion_bound (D X : Matrix4) :
    -2*matrixInner D X-(1/6 : ℝ)*matrixNormSq X ≤ 6*matrixNormSq D := by
  have hn := matrixNormSq_nonneg (X+(6 : ℝ) • D)
  have he : matrixNormSq (X+(6 : ℝ) • D) =
      matrixNormSq X+12*matrixInner D X+36*matrixNormSq D := by
    simp [matrixNormSq, matrixInner, Fin.sum_univ_succ]
    ring
  rw [he] at hn
  linarith

/-- The full constant 97/48 in lem:Ebound, in the principal frame. -/
theorem hessianPsi_quadratic_bound (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (X : Matrix4)
    (hX : X.IsSymm) (htr : Matrix.trace X = 0) :
    2*matrixInner (hessianPsi (Matrix.diagonal μ) τ) X-
      matrixInner X (matrixGramOperator (Matrix.diagonal μ) X) ≤ 97/48 := by
  obtain ⟨hτ,_hμ,hn,hτn,ht,_hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  have hK := matrixGram_lower_bound_diagonal μ X hX htr
  have hR := centered_cubicGramMatrix_bound τ hτ ht hτn
  have hS := weighted_matrix_square_bound μ hn X hX
  have hC := matrix_square_completion_bound (cubicGramMatrix τ-(1/4 : ℝ) • (1 : Matrix4)) X
  have he : 2*matrixInner (hessianPsi (Matrix.diagonal μ) τ) X =
      -2*matrixInner (cubicGramMatrix τ-(1/4 : ℝ) • (1 : Matrix4)) X+
      (1/2 : ℝ)*Matrix.trace ((Matrix.diagonal μ)^2*X)-(1/8 : ℝ)*Matrix.trace X := by
    simp [matrixInner, hessianPsi, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]
    ring
  rw [he, htr]
  linarith

end
end SecondPinching
