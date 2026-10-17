import SecondPinching.TrialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- Ordered-index Cauchy--Schwarz for matrices. -/
theorem matrixInner_sq_le (X Y : Matrix4) :
    (matrixInner X Y)^2 ≤ matrixNormSq X*matrixNormSq Y := by
  simpa [matrixInner, matrixNormSq, Fintype.sum_prod_type] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : Fin 4 × Fin 4 => X p.1 p.2) (fun p => Y p.1 p.2)

/-- The trace-free symmetric representative of (X,v,w) -> w dot Xv. -/
def matrixVectorDual (v w : Vector4) : Matrix4 := fun i j =>
  (v i*w j+w i*v j)/2-(v ⬝ᵥ w)/4*(1 : Matrix4) i j

theorem matrixVectorDual_norm (v w : Vector4) :
    matrixNormSq (matrixVectorDual v w) =
      (1/2 : ℝ)*(v ⬝ᵥ v)*(w ⬝ᵥ w)+(1/4 : ℝ)*(v ⬝ᵥ w)^2 := by
  simp [matrixNormSq, matrixVectorDual, dotProduct, Matrix.one_apply, Fin.sum_univ_succ]
  ring

theorem matrixVectorDual_pairing (X : Matrix4) (hX : X.IsSymm)
    (htr : Matrix.trace X = 0) (v w : Vector4) :
    matrixInner X (matrixVectorDual v w) = w ⬝ᵥ (X *ᵥ v) := by
  have he : matrixInner X (matrixVectorDual v w) =
      w ⬝ᵥ (X *ᵥ v)-(v ⬝ᵥ w)/4*Matrix.trace X := by
    simp [matrixInner, matrixVectorDual, Matrix.trace, Matrix.diag, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_succ, hX.apply]
    simp only [hX.apply 0 1, hX.apply 0 2, hX.apply 0 3, hX.apply 1 2, hX.apply 1 3, hX.apply 2 3]
    ring
  simp [he, htr]

/-- A trace-free symmetric 4 by 4 matrix has operator norm squared at most
three quarters of its ordered squared norm. This proof needs no eigenbasis. -/
theorem traceFree_matrix_mulVec_bound (X : Matrix4) (hX : X.IsSymm)
    (htr : Matrix.trace X = 0) (v : Vector4) :
    (X *ᵥ v) ⬝ᵥ (X *ᵥ v) ≤ (3/4 : ℝ)*matrixNormSq X*(v ⬝ᵥ v) := by
  let w := X *ᵥ v
  have hcs := matrixInner_sq_le X (matrixVectorDual v w)
  rw [matrixVectorDual_pairing X hX htr, matrixVectorDual_norm] at hcs
  change (w ⬝ᵥ w)^2 ≤ _ at hcs
  have hvw : (v ⬝ᵥ w)^2 ≤ (v ⬝ᵥ v)*(w ⬝ᵥ w) := by
    simpa [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  have hXn := matrixNormSq_nonneg X
  have hmul := mul_le_mul_of_nonneg_left hvw hXn
  have hwn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  change w ⬝ᵥ w ≤ _
  by_cases hw : w ⬝ᵥ w = 0
  · rw [hw]
    exact mul_nonneg (mul_nonneg (by norm_num) hXn)
      (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  · have hwpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hwn (Ne.symm hw)
    nlinarith

/-- Contraction of the cubic in an arbitrary vector direction. -/
def directionalCubic (τ : Cubic4) (v : Vector4) : Matrix4 :=
  fun i j => ∑ k, τ i j k*v k

theorem directionalCubic_codomain (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (v : Vector4) :
    (directionalCubic τ v).IsSymm ∧ Matrix.trace (directionalCubic τ v) = 0 := by
  constructor
  · ext i j
    simp only [Matrix.transpose_apply, directionalCubic, cubicSymmetric_swap12 hτ j i]
  · have he : Matrix.trace (directionalCubic τ v) = ∑ k, (∑ i, τ i i k)*v k := by
      simp [directionalCubic, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
      ring
    simp [he, ht]

/-- The harmonic symmetric cubic representing the contraction functional. -/
def harmonicCubicDual (X : Matrix4) (v : Vector4) : Cubic4 := fun i j k =>
  (v i*X j k+v j*X i k+v k*X i j)/3-
    ((1 : Matrix4) i j*(X *ᵥ v) k+(1 : Matrix4) i k*(X *ᵥ v) j+
      (1 : Matrix4) j k*(X *ᵥ v) i)/9

/-- Norm of the trace-corrected dual tensor. The trace term is retained here
so that the identity is valid before imposing trace X=0. -/
theorem harmonicCubicDual_norm_raw (X : Matrix4) (hX : X.IsSymm) (v : Vector4) :
    cubicNormSq (harmonicCubicDual X v) =
      (1/3 : ℝ)*(v ⬝ᵥ v)*matrixNormSq X+
      (4/9 : ℝ)*((X *ᵥ v) ⬝ᵥ (X *ᵥ v))-
      (2/9 : ℝ)*Matrix.trace X*(v ⬝ᵥ (X *ᵥ v)) := by
  simp [cubicNormSq, harmonicCubicDual, matrixNormSq, Matrix.trace, Matrix.diag,
    Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_succ, hX.apply]
  simp only [hX.apply 0 1, hX.apply 0 2, hX.apply 0 3, hX.apply 1 2, hX.apply 1 3, hX.apply 2 3]
  ring

theorem harmonicCubicDual_pairing (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (X : Matrix4) (v : Vector4) :
    (∑ i, ∑ j, ∑ k, τ i j k*harmonicCubicDual X v i j k) =
      matrixInner (directionalCubic τ v) X := by
  have he : (∑ i, ∑ j, ∑ k, τ i j k*harmonicCubicDual X v i j k) =
      matrixInner (directionalCubic τ v) X-
        (1/3 : ℝ)*∑ k, (∑ i, τ i i k)*(X *ᵥ v) k := by
    simp [harmonicCubicDual, matrixInner, directionalCubic, Matrix.one_apply,
      Fin.sum_univ_succ, cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
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
      cubicSymmetric_swap23 hτ 3 2 3]
    ring
  simp [he, ht]

/-- The R bound in lem:bounds for every vector, without changing frame. -/
theorem cubicGramMatrix_bound (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hτn : cubicNormSq τ = 1) (v : Vector4) :
    v ⬝ᵥ (cubicGramMatrix τ *ᵥ v) ≤ (2/3 : ℝ)*(v ⬝ᵥ v) := by
  let X := directionalCubic τ v
  obtain ⟨hX,hXt⟩ := directionalCubic_codomain τ hτ ht v
  have hc : (∑ i, ∑ j, ∑ k, τ i j k*harmonicCubicDual X v i j k)^2 ≤
      cubicNormSq τ*cubicNormSq (harmonicCubicDual X v) := by
    simpa [cubicNormSq, Fintype.sum_prod_type] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun p : Fin 4 × Fin 4 × Fin 4 => τ p.1 p.2.1 p.2.2)
        (fun p => harmonicCubicDual X v p.1 p.2.1 p.2.2)
  rw [harmonicCubicDual_pairing τ hτ ht, matrixInner_self, hτn, one_mul,
    harmonicCubicDual_norm_raw X hX v, hXt] at hc
  have hb := traceFree_matrix_mulVec_bound X hX hXt v
  have he : v ⬝ᵥ (cubicGramMatrix τ *ᵥ v) = matrixNormSq X := by
    simp [X, directionalCubic, matrixNormSq, cubicGramMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  rw [he]
  have hXn := matrixNormSq_nonneg X
  by_cases hx : matrixNormSq X = 0
  · rw [hx]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  · have hp : 0 < matrixNormSq X := lt_of_le_of_ne hXn (Ne.symm hx)
    nlinarith

/-- The second matrix bound in eq:bounds, as a quadratic-form inequality. -/
theorem vectorGramOperator_bound (τ : Cubic4) (hτ : CubicSymmetric τ)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hτn : cubicNormSq τ = 1) (v : Vector4) :
    v ⬝ᵥ (vectorGramOperator τ *ᵥ v) ≤ (5/8 : ℝ)*(v ⬝ᵥ v) := by
  have hr := cubicGramMatrix_bound τ hτ ht hτn v
  have he : v ⬝ᵥ (vectorGramOperator τ *ᵥ v) =
      (1/4 : ℝ)*(v ⬝ᵥ v)+(9/16 : ℝ)*(v ⬝ᵥ (cubicGramMatrix τ *ᵥ v)) := by
    simp [vectorGramOperator, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_succ]
    ring
  rw [he]
  linarith

end
end SecondPinching
