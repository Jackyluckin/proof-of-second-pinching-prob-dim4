import SecondPinching.MovingFrameHessian

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The last slot remains a covector slot when the first two are contracted. -/
theorem cubicConnectionAction_last_slot (O : Matrix4) (T : Cubic4) (k : Fin 4) :
    Matrix.of (fun i j => cubicConnectionAction O T i j k) =
      O*Matrix.of (fun i j => T i j k) + Matrix.of (fun i j => T i j k)*Oᵀ +
        ∑ r, O k r • Matrix.of (fun i j => T i j r) := by
  ext i j
  simp only [cubicConnectionAction, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl; intro r _; ring

theorem skew_connection_pairing (O H K : Matrix4) (hO : Oᵀ = -O)
    (hH : H.IsSymm) (hK : K.IsSymm) :
    matrixInner (O*H + H*Oᵀ) K + matrixInner H (O*K + K*Oᵀ) = 0 := by
  rw [matrixInner_comm H, matrixInner_eq_trace_mul _ K hK,
    matrixInner_eq_trace_mul _ H hH, hO, mul_neg, mul_neg,
    ← sub_eq_add_neg, ← sub_eq_add_neg, sub_mul, sub_mul,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_cycle O H K,
    Matrix.trace_mul_cycle O K H]
  simp only [Matrix.mul_assoc]
  ring

theorem skew_matrix_sum (O K : Matrix4) (hO : Oᵀ = -O) (hK : K.IsSymm) :
    (∑ i, ∑ j, O i j * K i j) = 0 := by
  have ho (i j : Fin 4) : O j i = -O i j := congrFun (congrFun hO i) j
  have he : (∑ i, ∑ j, O i j*K i j) = -(∑ i, ∑ j, O i j*K i j) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [ho i j, hK.apply j i]; ring
  linarith

theorem fderiv_matrixInner (A B : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    fderiv ℝ (fun y => matrixInner (A y) (B y)) x v =
      matrixInner (matrixDerivative A x v) (B x) + matrixInner (A x) (matrixDerivative B x v) := by
  have ha (i j : Fin 4) : DifferentiableAt ℝ (fun y => A y i j) x := by fun_prop
  have hb (i j : Fin 4) : DifferentiableAt ℝ (fun y => B y i j) x := by fun_prop
  simp only [matrixInner]
  erw [fderiv_fun_sum (u := Finset.univ) (fun i _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => (ha i j).mul (hb i j)))]
  simp only [sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  erw [fderiv_fun_sum (u := Finset.univ) (fun j _ => (ha i j).mul (hb i j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl; intro j _
  erw [fderiv_fun_mul (ha i j) (hb i j)]
  simp only [add_apply, smul_apply, smul_eq_mul, matrixDerivative]
  ring

theorem fderiv_cubicNormSq (T : Chart4 → Cubic4) (x v : Chart4)
    (hT : DifferentiableAt ℝ T x) :
    fderiv ℝ (fun y => cubicNormSq (T y)) x v = 2*cubicInner (T x) (cubicDerivative T x v) := by
  have ht (i j k : Fin 4) : DifferentiableAt ℝ (fun y => T y i j k) x := by fun_prop
  simp only [cubicNormSq, pow_two]
  erw [fderiv_fun_sum (u := Finset.univ) (fun i _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ =>
      DifferentiableAt.fun_sum (u := Finset.univ) (fun k _ => (ht i j k).mul (ht i j k))))]
  simp only [sum_apply, cubicInner, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  erw [fderiv_fun_sum (u := Finset.univ) (fun j _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun k _ => (ht i j k).mul (ht i j k)))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl; intro j _
  erw [fderiv_fun_sum (u := Finset.univ) (fun k _ => (ht i j k).mul (ht i j k))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl; intro k _
  erw [fderiv_fun_mul (ht i j k) (ht i j k)]
  simp only [add_apply, smul_apply, smul_eq_mul, cubicDerivative]
  ring

/-- Cancellation of all three connection terms in the ordered cubic norm. -/
theorem skew_cubicConnectionAction_inner (O : Matrix4) (T : Cubic4)
    (hO : Oᵀ = -O) (hT : CubicSymmetric T) :
    cubicInner T (cubicConnectionAction O T) = 0 := by
  have hs (k : Fin 4) : (Matrix.of (fun i j => T i j k)).IsSymm := by
    ext i j
    exact cubicSymmetric_swap12 hT j i k
  have he : cubicInner T (cubicConnectionAction O T) =
      ∑ k, matrixInner (Matrix.of (fun i j => T i j k))
        (Matrix.of (fun i j => cubicConnectionAction O T i j k)) := by
    simp only [cubicInner, matrixInner, Matrix.of_apply]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [he]
  simp_rw [cubicConnectionAction_last_slot]
  have hp (k : Fin 4) : matrixInner (Matrix.of (fun i j => T i j k))
      (O*Matrix.of (fun i j => T i j k) + Matrix.of (fun i j => T i j k)*Oᵀ +
        ∑ r, O k r • Matrix.of (fun i j => T i j r)) =
      ∑ r, O k r * matrixInner (Matrix.of (fun i j => T i j k)) (Matrix.of (fun i j => T i j r)) := by
    rw [skew_connection_matrixInner _ _ _ hO (hs k)]
    simp only [matrixInner, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [hp]
  apply skew_matrix_sum O _ hO
  ext k r
  exact matrixInner_comm _ _


theorem matrixInner_sum_smul_right (H : Matrix4) (c : Fin 4 → ℝ) (K : Fin 4 → Matrix4) :
    matrixInner H (∑ r, c r • K r) = ∑ r, c r * matrixInner H (K r) := by
  simp only [matrixInner, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- Product rule after the two contracted connection slots cancel. -/
theorem weighted_connection_product (O H K L M : Matrix4) (T : Cubic4) (k : Fin 4)
    (hO : Oᵀ = -O) (hH : H.IsSymm) (hK : K.IsSymm)
    (hKdef : K = Matrix.of (fun i j => T i j k)) :
    matrixInner (O*H+H*Oᵀ+L) K +
      matrixInner H (Matrix.of (fun i j => cubicConnectionAction O T i j k)+M) =
      matrixInner L K + matrixInner H M + ∑ r, O k r*cubicWeightedTrace H T r := by
  rw [cubicConnectionAction_last_slot, ← hKdef]
  have hp := skew_connection_pairing O H K hO hH hK
  have hs := matrixInner_sum_smul_right H (O k) (fun r => Matrix.of (fun i j => T i j r))
  change matrixInner H (∑ r, O k r • Matrix.of (fun i j => T i j r)) =
    ∑ r, O k r*cubicWeightedTrace H T r at hs
  have ha (A B C : Matrix4) : matrixInner A (B+C) = matrixInner A B+matrixInner A C := by
    rw [matrixInner_comm, matrixInner_add_left, matrixInner_comm B, matrixInner_comm C]
  rw [matrixInner_add_left, ha, ha, ha, hs]
  rw [ha] at hp
  linarith

end
end SecondPinching
