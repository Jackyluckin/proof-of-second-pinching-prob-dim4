import SecondPinching.ImmersionTracePowers

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem contDiffOn_matrix_mul {U : Set Chart4} {A B : Chart4 → Matrix4}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun y => A y*B y) U := by
  apply contDiffOn_pi.mpr; intro i
  apply contDiffOn_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  fun_prop

theorem contDiffOn_matrix_pow {U : Set Chart4} {A : Chart4 → Matrix4}
    (hA : ContDiffOn ℝ ∞ A U) (n : ℕ) : ContDiffOn ℝ ∞ (fun y => (A y)^n) U := by
  induction n with
  | zero => simpa only [pow_zero] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Chart4 => (1 : Matrix4)) U)
  | succ n ih => simpa only [pow_succ] using contDiffOn_matrix_mul ih hA

theorem contDiffOn_matrix_trace {U : Set Chart4} {A : Chart4 → Matrix4}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun y => Matrix.trace (A y)) U := by
  unfold Matrix.trace Matrix.diag
  fun_prop

theorem contDiffOn_immersionCubicTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F) :
    ContDiffOn ℝ ∞ (immersionCubicTrace F e) F.domain :=
  contDiffOn_matrix_trace (contDiffOn_matrix_pow (contDiffOn_immersionFrameForms F e).1 3)

theorem contDiffOn_immersionQuarticTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F) :
    ContDiffOn ℝ ∞ (immersionQuarticTrace F e) F.domain :=
  contDiffOn_matrix_trace (contDiffOn_matrix_pow (contDiffOn_immersionFrameForms F e).1 4)

theorem differentiableAt_weightedTrace (Q : Chart4 → Matrix4) (T : Chart4 → Cubic4)
    (x : Chart4) (hQ : DifferentiableAt ℝ Q x) (hT : DifferentiableAt ℝ T x) (k : Fin 4) :
    DifferentiableAt ℝ (fun y => cubicWeightedTrace (Q y) (T y) k) x := by
  unfold cubicWeightedTrace
  apply DifferentiableAt.fun_sum; intro i _
  apply DifferentiableAt.fun_sum; intro j _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hQ i) j).mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hT i) j) k)

end
end SecondPinching
