import SecondPinching.ImmersionDivergenceBridge
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The usual determinant, bundled only to use its multilinear derivative.
The rows are coordinate covectors; no positivity or invertibility is built in. -/
def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Vector4) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := (continuous_id : Continuous (fun A : Matrix4 => A)).matrix_det

theorem determinantMultilinear_apply (A : Matrix4) : determinantMultilinear A=A.det := rfl

/-- A row replacement is evaluated by the adjugate without requiring A inverse. -/
theorem det_updateRow_eq_adjugate (A : Matrix4) (i : Fin 4) (v : Vector4) :
    (A.updateRow i v).det = ∑ j, A.adjugate j i*v j := by
  rw [← Matrix.cramer_transpose_apply,Matrix.cramer_eq_adjugate_mulVec,← Matrix.adjugate_transpose]
  rfl

theorem determinant_row_variation (A U : Matrix4) :
    (∑ i, (A.updateRow i (U i)).det)=Matrix.trace (A.adjugate*U) := by
  simp only [det_updateRow_eq_adjugate,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  rw [Finset.sum_comm]

theorem matrixDerivative_eq_fderiv (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) : matrixDerivative A x v=fderiv ℝ A x v := by
  ext i j
  have hi := differentiableAt_pi.mp hA i
  simp only [matrixDerivative,fderiv_apply hi j,fderiv_apply hA i,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  rfl

/-- Jacobi's formula in polynomial form, valid also at a singular matrix. -/
theorem fderiv_matrix_det (A : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) :
    fderiv ℝ (fun y => (A y).det) x v =
      Matrix.trace ((A x).adjugate*matrixDerivative A x v) := by
  have hd := (determinantMultilinear.hasFDerivAt (A x)).comp x hA.hasFDerivAt
  have he := congrArg (fun L : Chart4 →L[ℝ] ℝ => L v) hd.fderiv
  change fderiv ℝ (fun y => (A y).det) x v =
    determinantMultilinear.linearDeriv (A x) (fderiv ℝ A x v) at he
  erw [ContinuousMultilinearMap.linearDeriv_apply] at he
  rw [← matrixDerivative_eq_fderiv A x v hA] at he
  change _ = ∑ i, ((A x).updateRow i (matrixDerivative A x v i)).det at he
  rw [determinant_row_variation] at he
  exact he

/-- Metric compatibility doubles the connection trace in the determinant
variation. This algebraic identity itself does not need positive definiteness. -/
theorem determinant_metric_variation (g C : Matrix4) :
    Matrix.trace (g.adjugate*(C*g+g*Cᵀ))=2*g.det*Matrix.trace C := by
  rw [Matrix.mul_add,Matrix.trace_add]
  have h1 : Matrix.trace (g.adjugate*(C*g))=g.det*Matrix.trace C := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle g.adjugate C g,Matrix.mul_adjugate,
      Matrix.smul_mul,one_mul,Matrix.trace_smul,smul_eq_mul]
  have h2 : Matrix.trace (g.adjugate*(g*Cᵀ))=g.det*Matrix.trace C := by
    rw [← Matrix.mul_assoc,Matrix.adjugate_mul,Matrix.smul_mul,one_mul,Matrix.trace_smul,
      smul_eq_mul,Matrix.trace_transpose]
  rw [h1,h2]; ring

end
end SecondPinching
