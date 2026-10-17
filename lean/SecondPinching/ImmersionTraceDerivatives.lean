import SecondPinching.MovingFrameConnection
import SecondPinching.ImmersionCoordinateBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem skew_connection_trace (O H K : Matrix4) (hO : Oᵀ = -O) :
    Matrix.trace (O*H + H*Oᵀ + K) = Matrix.trace K := by
  rw [hO, mul_neg, ← sub_eq_add_neg, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_mul_comm O H]
  ring

/-- The pairing uses all ordered matrix entries. Symmetry of H and
skewness of O cancel the two frame-connection contributions. -/
theorem skew_connection_matrixInner (O H K : Matrix4)
    (hO : Oᵀ = -O) (hH : H.IsSymm) :
    matrixInner H (O*H + H*Oᵀ + K) = matrixInner H K := by
  rw [matrixInner_comm, matrixInner_add_left, matrixInner_eq_trace_mul _ H hH]
  rw [hO, mul_neg, ← sub_eq_add_neg, sub_mul, Matrix.trace_sub,
    Matrix.trace_mul_cycle O H H]
  simp only [Matrix.mul_assoc, sub_self, zero_add]
  exact matrixInner_comm K H

/-- The final tensor slot transforms too. This identity applies to an
arbitrary matrix B; orthogonality and tensor symmetry are not assumptions. -/
theorem frameCubic_last_slot (B : Matrix4) (T : Cubic4) (k : Fin 4) :
    (fun i j => frameCubic B T i j k : Matrix4) =
      ∑ c, B k c • frameMatrix B (fun a b => T a b c) := by
  ext i j
  simp only [frameCubic, frameMatrix, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem frameCubic_trace_last_slot (B : Matrix4) (T : Cubic4) (k : Fin 4) :
    (∑ i, frameCubic B T i i k) =
      ∑ c, B k c * Matrix.trace (frameMatrix B (fun a b => T a b c)) := by
  change Matrix.trace (fun i j => frameCubic B T i j k) = _
  rw [frameCubic_last_slot, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]

theorem frameCubic_weighted_last_slot (B H : Matrix4) (T : Cubic4) (k : Fin 4) :
    (∑ i, ∑ j, H i j * frameCubic B T i j k) =
      ∑ c, B k c * matrixInner H (frameMatrix B (fun a b => T a b c)) := by
  change matrixInner H (fun i j => frameCubic B T i j k) = _
  rw [frameCubic_last_slot]
  simp only [matrixInner, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem immersionFrameSecond_trace_coordinate_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    fderiv ℝ (fun y => Matrix.trace (immersionFrameSecond F e y)) x (coordinateUnit k) =
      Matrix.trace (frameMatrix (e.coefficients x)
        (fun a b => immersionThirdForm F.map F.normal x a b k)) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [fderiv_matrix_trace _ _ _ hh, immersionFrameSecond_derivative F e x hx k]
  exact skew_connection_trace _ _ _ (immersionMovingConnection_skew F e x hx k)

theorem immersionFrameSecond_norm_coordinate_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    fderiv ℝ (fun y => matrixNormSq (immersionFrameSecond F e y)) x (coordinateUnit k) =
      2 * matrixInner (immersionFrameSecond F e x) (frameMatrix (e.coefficients x)
        (fun a b => immersionThirdForm F.map F.normal x a b k)) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [fderiv_matrixNormSq _ _ _ hh, immersionFrameSecond_derivative F e x hx k,
    skew_connection_matrixInner _ _ _ (immersionMovingConnection_skew F e x hx k)
      (immersionFrameSecond_symmetric F e x hx)]

/-- Differentiation of the geometric trace in the actual frame direction e_k. -/
theorem immersionFrameSecond_trace_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    fderiv ℝ (fun y => Matrix.trace (immersionFrameSecond F e y)) x (e.coefficients x k) =
      ∑ i, immersionFrameThird F e x i i k := by
  conv_lhs => rw [chart4_coordinate_expansion (e.coefficients x k)]
  simp only [map_sum, map_smul, smul_eq_mul,
    immersionFrameSecond_trace_coordinate_derivative F e x hx]
  exact (frameCubic_trace_last_slot _ _ k).symm

/-- Differentiation of S=|h|^2, with the ordered-index norm and no f_3 assumption. -/
theorem immersionFrameSecond_norm_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    fderiv ℝ (fun y => matrixNormSq (immersionFrameSecond F e y)) x (e.coefficients x k) =
      2 * ∑ i, ∑ j, immersionFrameSecond F e x i j * immersionFrameThird F e x i j k := by
  conv_lhs => rw [chart4_coordinate_expansion (e.coefficients x k)]
  simp only [map_sum, map_smul, smul_eq_mul,
    immersionFrameSecond_norm_coordinate_derivative F e x hx]
  rw [show (∑ i, ∑ j, immersionFrameSecond F e x i j * immersionFrameThird F e x i j k) =
    ∑ c, e.coefficients x k c * matrixInner (immersionFrameSecond F e x)
      (frameMatrix (e.coefficients x) (fun a b => immersionThirdForm F.map F.normal x a b c)) from
        frameCubic_weighted_last_slot _ _ _ k]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _; ring

/-- A neighborhood hypothesis is necessary: the trace vanishing only at x
would not imply the vanishing of its derivative. -/
theorem immersionFrameThird_trace_of_minimal_germ (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain)
    (hminimal : (fun y => Matrix.trace (immersionFrameSecond F e y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) :
    ∀ k, ∑ i, immersionFrameThird F e x i i k = 0 := by
  intro k
  rw [← immersionFrameSecond_trace_derivative F e x hx k, hminimal.fderiv_eq]
  simp

theorem immersionFrameThird_weighted_of_norm_germ (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (S : ℝ) (x : Chart4) (hx : x ∈ F.domain)
    (hS : (fun y => matrixNormSq (immersionFrameSecond F e y)) =ᶠ[𝓝 x] fun _ => S) :
    ∀ k, ∑ i, ∑ j, immersionFrameSecond F e x i j * immersionFrameThird F e x i j k = 0 := by
  intro k
  have hd := immersionFrameSecond_norm_derivative F e x hx k
  rw [hS.fderiv_eq] at hd
  simp only [fderiv_const_apply, zero_apply] at hd
  linarith

end
end SecondPinching
