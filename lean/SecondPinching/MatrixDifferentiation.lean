import SecondPinching.ImmersionConnection
import SecondPinching.ImmersionLocalData

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Componentwise ordinary derivative in a specified coordinate direction.
This is not a covariant derivative. -/
def matrixDerivative (A : Chart4 → Matrix4) (x v : Chart4) : Matrix4 :=
  fun i j => fderiv ℝ (fun y => A y i j) x v

theorem matrixDerivative_mul (A B : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    matrixDerivative (fun y => A y * B y) x v =
      matrixDerivative A x v * B x + A x * matrixDerivative B x v := by
  have ha (i j : Fin 4) : DifferentiableAt ℝ (fun y => A y i j) x := by fun_prop
  have hb (i j : Fin 4) : DifferentiableAt ℝ (fun y => B y i j) x := by fun_prop
  ext i j
  simp only [matrixDerivative, Matrix.mul_apply, Matrix.add_apply]
  erw [fderiv_fun_sum (u := Finset.univ) (fun k _ => (ha i k).mul (hb k j))]
  simp only [sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  erw [fderiv_fun_mul (ha i k) (hb k j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem matrixDerivative_transpose (A : Chart4 → Matrix4) (x v : Chart4) :
    matrixDerivative (fun y => (A y)ᵀ) x v = (matrixDerivative A x v)ᵀ := rfl

theorem matrixDerivative_frameMatrix (B A : Chart4 → Matrix4) (x v : Chart4)
    (hB : DifferentiableAt ℝ B x) (hA : DifferentiableAt ℝ A x) :
    matrixDerivative (fun y => frameMatrix (B y) (A y)) x v =
      matrixDerivative B x v * A x * (B x)ᵀ +
      B x * matrixDerivative A x v * (B x)ᵀ +
      B x * A x * (matrixDerivative B x v)ᵀ := by
  simp only [frameMatrix_eq_conjugate]
  have hab : DifferentiableAt ℝ (fun y => B y * A y) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    simp only [Matrix.mul_apply]
    fun_prop
  have hbt : DifferentiableAt ℝ (fun y => (B y)ᵀ) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    change DifferentiableAt ℝ (fun y => B y j i) x
    fun_prop
  rw [matrixDerivative_mul _ _ x v hab hbt, matrixDerivative_mul _ _ x v hB hA,
    matrixDerivative_transpose, add_mul]

theorem matrixDerivative_const_germ (A : Chart4 → Matrix4) (C : Matrix4)
    (x v : Chart4) (h : A =ᶠ[𝓝 x] fun _ => C) : matrixDerivative A x v = 0 := by
  ext i j
  have he : (fun y => A y i j) =ᶠ[𝓝 x] fun _ => C i j :=
    h.mono (fun y hy => congrFun (congrFun hy i) j)
  simp only [matrixDerivative, he.fderiv_eq, fderiv_const_apply, zero_apply, Matrix.zero_apply]

theorem fderiv_matrix_trace (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => Matrix.trace (A y)) x v = Matrix.trace (matrixDerivative A x v) := by
  have ha (i : Fin 4) : DifferentiableAt ℝ (fun y => A y i i) x := by fun_prop
  simp only [Matrix.trace, Matrix.diag]
  erw [fderiv_fun_sum (u := Finset.univ) (fun i _ => ha i)]
  rfl

theorem fderiv_matrixNormSq (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => matrixNormSq (A y)) x v =
      2 * matrixInner (A x) (matrixDerivative A x v) := by
  have ha (i j : Fin 4) : DifferentiableAt ℝ (fun y => A y i j) x := by fun_prop
  simp only [matrixNormSq, pow_two]
  erw [fderiv_fun_sum (u := Finset.univ) (fun i _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => (ha i j).mul (ha i j)))]
  simp only [sum_apply, matrixInner, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  erw [fderiv_fun_sum (u := Finset.univ) (fun j _ => (ha i j).mul (ha i j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl; intro j _
  erw [fderiv_fun_mul (ha i j) (ha i j)]
  simp only [add_apply, smul_apply, smul_eq_mul, matrixDerivative]
  ring

end
end SecondPinching
