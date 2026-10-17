import SecondPinching.MatrixDifferentiation

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The row i lists the coefficients of nabla_(partial_k) partial_i. -/
def coordinateConnectionMatrix (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Chart4) (k : Fin 4) : Matrix4 := fun i r => Γ x r i k

theorem coordinateCovariant2_matrix (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : Chart4 → Matrix4) (x : Chart4) (k : Fin 4) :
    matrixDerivative h x (coordinateUnit k) =
      Matrix.of (fun i j => coordinateCovariant2 Γ h x i j k) +
      coordinateConnectionMatrix Γ x k * h x + h x * (coordinateConnectionMatrix Γ x k)ᵀ := by
  ext i j
  simp only [matrixDerivative, coordinateCovariant2, coordinateConnectionMatrix,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_add_distrib]
  have he : (∑ r, Γ x r j k * h x i r) = ∑ r, h x i r * Γ x r j k := by
    apply Finset.sum_congr rfl; intro r _; ring
  rw [he]; ring

theorem immersionMetric_matrix_derivative (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (k : Fin 4) :
    matrixDerivative (immersionMetric F.map) x (coordinateUnit k) =
      coordinateConnectionMatrix (immersionChristoffel F.map) x k * immersionMetric F.map x +
      immersionMetric F.map x * (coordinateConnectionMatrix (immersionChristoffel F.map) x k)ᵀ := by
  ext i j
  rw [matrixDerivative, immersionChristoffel_metric F x hx i j k]
  simp only [coordinateConnectionMatrix, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  change inner ℝ (immersionTangent F.map x j) (immersionTangent F.map x r) * _ =
    _ * inner ℝ (immersionTangent F.map x r) (immersionTangent F.map x j)
  rw [real_inner_comm]; ring

/-- Ordinary differentiation of B h B^t, with all frame derivatives
absorbed into the moving-frame connection O. -/
theorem movingFrame_derivative_algebra (B D h T C O : Matrix4)
    (hO : O * B = D + B * C) :
    D * h * Bᵀ + B * (T + C*h + h*Cᵀ) * Bᵀ + B*h*Dᵀ =
      O * frameMatrix B h + frameMatrix B h * Oᵀ + frameMatrix B T := by
  have hot : Bᵀ * Oᵀ = Dᵀ + Cᵀ * Bᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_add] using congrArg Matrix.transpose hO
  simp only [frameMatrix_eq_conjugate]
  calc
    _ = (D+B*C)*h*Bᵀ + B*h*(Dᵀ+Cᵀ*Bᵀ) + B*T*Bᵀ := by noncomm_ring
    _ = (O*B)*h*Bᵀ + B*h*(Bᵀ*Oᵀ) + B*T*Bᵀ := by rw [hO, hot]
    _ = _ := by noncomm_ring

/-- Actual connection in the given smooth orthonormal frame, differentiated
in the coordinate direction partial_k (not yet in the frame direction e_k). -/
def immersionMovingConnection (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (k : Fin 4) : Matrix4 :=
  (matrixDerivative e.coefficients x (coordinateUnit k) +
    e.coefficients x * coordinateConnectionMatrix (immersionChristoffel F.map) x k) *
      (e.coefficients x)⁻¹

theorem immersionMovingConnection_action (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    immersionMovingConnection F e x k * e.coefficients x =
      matrixDerivative e.coefficients x (coordinateUnit k) +
        e.coefficients x * coordinateConnectionMatrix (immersionChristoffel F.map) x k := by
  unfold immersionMovingConnection
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (localImmersionFrame_det_ne_zero F e x hx)), mul_one]

/-- Metric compatibility and differentiated orthonormality force the
actual moving-frame connection to be skew. No parallel-frame choice is used. -/
theorem immersionMovingConnection_skew (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    (immersionMovingConnection F e x k)ᵀ = -immersionMovingConnection F e x k := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hg := ((contDiffOn_immersionMetric F.isOpen_domain F.smooth_map x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => frameMatrix (e.coefficients y) (immersionMetric F.map y)) =ᶠ[𝓝 x]
      fun _ => (1 : Matrix4) := Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
        (fun y hy => e.orthonormal y hy)
  have hz := matrixDerivative_const_germ _ 1 x (coordinateUnit k) he
  rw [matrixDerivative_frameMatrix _ _ x _ hb hg, immersionMetric_matrix_derivative F x hx k] at hz
  have halg := movingFrame_derivative_algebra (e.coefficients x)
    (matrixDerivative e.coefficients x (coordinateUnit k)) (immersionMetric F.map x) 0
    (coordinateConnectionMatrix (immersionChristoffel F.map) x k)
    (immersionMovingConnection F e x k) (immersionMovingConnection_action F e x hx k)
  simp only [zero_add] at halg
  rw [halg, e.orthonormal x hx] at hz
  simp only [frameMatrix_eq_conjugate, mul_zero, zero_mul, mul_one, one_mul, add_zero] at hz
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)

theorem immersionFrameSecond_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    matrixDerivative (immersionFrameSecond F e) x (coordinateUnit k) =
      immersionMovingConnection F e x k * immersionFrameSecond F e x +
      immersionFrameSecond F e x * (immersionMovingConnection F e x k)ᵀ +
      frameMatrix (e.coefficients x) (fun i j => immersionThirdForm F.map F.normal x i j k) := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hh := (((contDiffOn_immersionForms F).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  unfold immersionFrameSecond
  rw [matrixDerivative_frameMatrix _ _ x _ hb hh,
    coordinateCovariant2_matrix (immersionChristoffel F.map)
      (immersionSecondForm F.map F.normal) x k]
  exact movingFrame_derivative_algebra _ _ _ _ _ _ (immersionMovingConnection_action F e x hx k)

end
end SecondPinching
