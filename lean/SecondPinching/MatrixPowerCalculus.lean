import SecondPinching.ImmersionPengTerngBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem differentiableAt_matrix_mul (A B : Chart4 → Matrix4) (x : Chart4)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => A y*B y) x := by
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  apply DifferentiableAt.fun_sum; intro k _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) k).mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp hB k) j)

theorem differentiableAt_matrix_pow (A : Chart4 → Matrix4) (x : Chart4)
    (hA : DifferentiableAt ℝ A x) (n : ℕ) :
    DifferentiableAt ℝ (fun y => (A y)^n) x := by
  induction n with
  | zero => simpa only [pow_zero] using (differentiableAt_const (1 : Matrix4))
  | succ n ih =>
    simpa only [pow_succ] using differentiableAt_matrix_mul _ _ _ ih hA

/-- Ordinary derivative of a matrix square, without a commutativity assumption. -/
theorem matrixDerivative_square (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    matrixDerivative (fun y => (A y)^2) x v =
      matrixDerivative A x v*A x+A x*matrixDerivative A x v := by
  simpa only [pow_two] using matrixDerivative_mul A A x v hA hA

theorem matrixDerivative_cube (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    matrixDerivative (fun y => (A y)^3) x v =
      matrixDerivative A x v*(A x)^2+A x*matrixDerivative A x v*A x+
        (A x)^2*matrixDerivative A x v := by
  change matrixDerivative (fun y => (A y)^2*A y) x v = _
  rw [matrixDerivative_mul _ _ _ _ (differentiableAt_matrix_pow A x hA 2) hA,
    matrixDerivative_square A x v hA]
  noncomm_ring

theorem matrixDerivative_fourth (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    matrixDerivative (fun y => (A y)^4) x v =
      matrixDerivative A x v*(A x)^3+A x*matrixDerivative A x v*(A x)^2+
        (A x)^2*matrixDerivative A x v*A x+(A x)^3*matrixDerivative A x v := by
  change matrixDerivative (fun y => (A y)^3*A y) x v = _
  rw [matrixDerivative_mul _ _ _ _ (differentiableAt_matrix_pow A x hA 3) hA,
    matrixDerivative_cube A x v hA]
  noncomm_ring

theorem trace_cube_differential (A U : Matrix4) :
    Matrix.trace (U*A^2+A*U*A+A^2*U) = 3*Matrix.trace (A^2*U) := by
  simp only [Matrix.trace_add]
  have h1 := Matrix.trace_mul_comm U (A^2)
  have h2 : Matrix.trace (A*U*A) = Matrix.trace (A^2*U) := by
    rw [Matrix.trace_mul_cycle A U A,pow_two]
  rw [h1,h2]; ring

theorem trace_fourth_differential (A U : Matrix4) :
    Matrix.trace (U*A^3+A*U*A^2+A^2*U*A+A^3*U) = 4*Matrix.trace (A^3*U) := by
  simp only [Matrix.trace_add]
  have h1 := Matrix.trace_mul_comm U (A^3)
  have h2 : Matrix.trace (A*U*A^2) = Matrix.trace (A^3*U) := by
    rw [Matrix.trace_mul_cycle A U (A^2),← pow_succ]
  have h3 : Matrix.trace (A^2*U*A) = Matrix.trace (A^3*U) := by
    rw [Matrix.trace_mul_cycle (A^2) U A,← pow_succ']
  rw [h1,h2,h3]; ring

theorem fderiv_cubicMoment (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => cubicMoment (A y)) x v =
      3*Matrix.trace ((A x)^2*matrixDerivative A x v) := by
  unfold cubicMoment
  rw [fderiv_matrix_trace _ _ _ (differentiableAt_matrix_pow A x hA 3),
    matrixDerivative_cube A x v hA,trace_cube_differential]

theorem fderiv_quarticMoment (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => quarticMoment (A y)) x v =
      4*Matrix.trace ((A x)^3*matrixDerivative A x v) := by
  unfold quarticMoment
  rw [fderiv_matrix_trace _ _ _ (differentiableAt_matrix_pow A x hA 4),
    matrixDerivative_fourth A x v hA,trace_fourth_differential]

/-- Multiplication of endomorphisms preserves the commutator form of the
orthonormal-frame connection. The displayed residuals are the covariant parts. -/
theorem square_connection_derivative (O A U : Matrix4) (hO : Oᵀ = -O) :
    (O*A+A*Oᵀ+U)*A+A*(O*A+A*Oᵀ+U) =
      O*A^2+A^2*Oᵀ+(U*A+A*U) := by
  rw [hO]; noncomm_ring

theorem cube_connection_derivative (O A U : Matrix4) (hO : Oᵀ = -O) :
    (O*A+A*Oᵀ+U)*A^2+A*(O*A+A*Oᵀ+U)*A+A^2*(O*A+A*Oᵀ+U) =
      O*A^3+A^3*Oᵀ+(U*A^2+A*U*A+A^2*U) := by
  rw [hO]; noncomm_ring

theorem trace_power_connection (O A U : Matrix4) (hO : Oᵀ = -O) (n : ℕ) :
    Matrix.trace (A^n*(O*A+A*Oᵀ+U)) = Matrix.trace (A^n*U) := by
  simp only [hO,Matrix.mul_add,mul_neg,Matrix.trace_add,Matrix.trace_neg]
  have he : Matrix.trace (A^n*(O*A)) = Matrix.trace (A^n*(A*O)) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle (A^n) O A,
      ← pow_succ',← Matrix.mul_assoc,← pow_succ]
  rw [he]; ring

end
end SecondPinching
