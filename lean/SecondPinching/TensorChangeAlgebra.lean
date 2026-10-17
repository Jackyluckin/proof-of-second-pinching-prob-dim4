import SecondPinching.ImmersionConnectionChange

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- Cancellation of the two differentiated Jacobian factors. This is an
algebraic lemma; its connection-law premise is derived for actual immersions. -/
theorem matrix_pullback_connection_algebra (J D h G : Matrix4) (Γ dh : Cubic4)
    (i j k : Fin 4)
    (hG : ∀ u a, (∑ r, G u r * J r a) =
      D u a + ∑ b, ∑ c, J u b * J k c * Γ a b c) :
    (∑ a, ∑ b, (D i a * J j b * h a b + J i a * D j b * h a b +
      J i a * J j b * ∑ c, J k c * dh a b c)) -
      (∑ r, (G i r * frameMatrix J h r j + G j r * frameMatrix J h i r)) =
    frameCubic J (fun a b c => dh a b c -
      ∑ r, (Γ r a c * h r b + Γ r b c * h a r)) i j k := by
  have h1 : (∑ r, G i r * frameMatrix J h r j) =
      ∑ a, ∑ b, (D i a + ∑ u, ∑ c, J i u * J k c * Γ a u c) * J j b * h a b := by
    calc
      _ = ∑ a, (∑ r, G i r * J r a) * ∑ b, J j b * h a b := by
        simp only [frameMatrix,Finset.mul_sum,Finset.sum_mul,mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
      _ = _ := by simp only [hG,Finset.mul_sum,mul_assoc]
  have h2 : (∑ r, G j r * frameMatrix J h i r) =
      ∑ a, ∑ b, J i a * (D j b + ∑ u, ∑ c, J j u * J k c * Γ b u c) * h a b := by
    calc
      _ = ∑ a, ∑ b, J i a * (∑ r, G j r * J r b) * h a b := by
        simp only [frameMatrix,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro r _
        ring
      _ = _ := by simp only [hG]
  have hc1 : (∑ a, ∑ b, (∑ u, ∑ c, J i u * J k c * Γ a u c) * J j b * h a b) =
      ∑ a, ∑ b, ∑ c, J i a * J j b * J k c * ∑ r, Γ r a c * h r b := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro r _
    ring
  have hc2 : (∑ a, ∑ b, J i a * (∑ u, ∑ c, J j u * J k c * Γ b u c) * h a b) =
      ∑ a, ∑ b, ∑ c, J i a * J j b * J k c * ∑ r, Γ r b c * h a r := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro r _
    ring
  rw [Finset.sum_add_distrib,h1,h2]
  simp only [add_mul,mul_add,Finset.sum_add_distrib]
  rw [hc1,hc2]
  simp only [frameCubic,frameMatrix,Finset.sum_add_distrib,Finset.mul_sum,
    mul_sub,mul_add,Finset.sum_sub_distrib,mul_assoc]
  ring

/-- After the last two tensor slots have been handled by the matrix lemma,
this identity cancels the connection term on the remaining first slot. -/
theorem cubic_pullback_connection_algebra (J D G : Matrix4) (Γ T : Cubic4)
    (K : Fourth4) (i j k l : Fin 4)
    (hG : ∀ u a, (∑ r, G u r * J r a) =
      D u a + ∑ b, ∑ c, J u b * J l c * Γ a b c) :
    (∑ a, (D i a * frameMatrix J (T a) j k + J i a * frameCubic J (K a) j k l)) -
      (∑ r, G i r * frameCubic J T r j k) =
    frameFourth J (fun a b c d => K a b c d - ∑ r, Γ r a d * T r b c) i j k l := by
  have hc : (∑ r, G i r * frameCubic J T r j k) =
      ∑ a, (D i a + ∑ b, ∑ c, J i b * J l c * Γ a b c) * frameMatrix J (T a) j k := by
    calc
      _ = ∑ a, (∑ r, G i r * J r a) * frameMatrix J (T a) j k := by
        simp only [frameCubic,Finset.mul_sum,Finset.sum_mul,mul_assoc]
        rw [Finset.sum_comm]
      _ = _ := by simp only [hG]
  have ho : (∑ r, (∑ a, ∑ d, J i a * J l d * Γ r a d) * frameMatrix J (T r) j k) =
      frameFourth J (fun a b c d => ∑ r, Γ r a d * T r b c) i j k l := by
    simp only [frameFourth,frameCubic,frameMatrix,Finset.mul_sum,Finset.sum_mul]
    conv_rhs =>
      rw [Finset.sum_comm]
      arg 2; ext b
      arg 2; ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext d; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    conv_lhs => arg 2; ext d; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro r _
    ring
  rw [hc]
  simp only [add_mul,Finset.sum_add_distrib]
  rw [ho]
  simp only [frameFourth,frameCubic,frameMatrix,mul_sub,Finset.sum_sub_distrib]
  ring

end
end SecondPinching
