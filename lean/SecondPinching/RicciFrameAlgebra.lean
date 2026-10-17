import SecondPinching.CoordinateRicci

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- The curvature action after the Gauss equation. In coordinates q=h g^{-1} h;
in an orthonormal frame q=h^2. Every index is covariant. -/
def ricciPolynomial (g h q : Matrix4) : Fourth4 := fun i j k l =>
  g i l*h j k-g i k*h j l+h i k*g j l-h i l*g j k +
  h i l*q j k-h i k*q j l+q i k*h j l-q i l*h j k

theorem frameFourth_product13 (B A C : Matrix4) :
    frameFourth B (fun i j k l => A i k*C j l) =
    fun i j k l => frameMatrix B A i k*frameMatrix B C j l := by
  funext i j k l
  simp only [frameFourth, frameCubic, frameMatrix, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

theorem frameFourth_product14 (B A C : Matrix4) :
    frameFourth B (fun i j k l => A i l*C j k) =
    fun i j k l => frameMatrix B A i l*frameMatrix B C j k := by
  rw [show (fun i j k l => A i l*C j k) =
      (fun i j k l => (fun a b c d => A a c*C b d) i j l k) from rfl,
    frameFourth_swap34, frameFourth_product13]

theorem frameFourth_ricciPolynomial (B g h q : Matrix4) :
    frameFourth B (ricciPolynomial g h q) =
      ricciPolynomial (frameMatrix B g) (frameMatrix B h) (frameMatrix B q) := by
  have he : ricciPolynomial g h q =
      (fun i j k l => g i l*h j k)-(fun i j k l => g i k*h j l)+
      (fun i j k l => h i k*g j l)-(fun i j k l => h i l*g j k)+
      (fun i j k l => h i l*q j k)-(fun i j k l => h i k*q j l)+
      (fun i j k l => q i k*h j l)-(fun i j k l => q i l*h j k) := rfl
  rw [he]
  change frameFourthLinear B _ = _
  simp only [map_add, map_sub]
  simp only [frameFourthLinear, LinearMap.coe_mk, AddHom.coe_mk,
    frameFourth_product13, frameFourth_product14]
  rfl

theorem frameMatrix_metric_square (B g h : Matrix4) (hB : B.det ≠ 0)
    (horth : frameMatrix B g = 1) :
    frameMatrix B (h*g⁻¹*h) = frameMatrix B h*frameMatrix B h := by
  have hi := isUnit_iff_ne_zero.mpr hB
  have hbg : B*g*Bᵀ = 1 := by simpa only [frameMatrix_eq_conjugate] using horth
  have hbg' : B*(g*Bᵀ) = 1 := by simpa only [Matrix.mul_assoc] using hbg
  have hgi : g*(Bᵀ*B) = 1 := by
    calc
      _ = B⁻¹*(B*g*Bᵀ)*B := by
        calc
          _ = (B⁻¹*B)*g*Bᵀ*B := by rw [Matrix.nonsing_inv_mul B hi,one_mul,Matrix.mul_assoc]
          _ = _ := by noncomm_ring
      _ = 1 := by rw [hbg, mul_one, Matrix.nonsing_inv_mul B hi]
  have hgdet := Matrix.det_ne_zero_of_right_inverse hgi
  have hgunit := isUnit_iff_ne_zero.mpr hgdet
  have he : g⁻¹ = Bᵀ*B := by
    calc
      g⁻¹ = g⁻¹*(g*(Bᵀ*B)) := by rw [hgi,mul_one]
      _ = Bᵀ*B := by rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul g hgunit,one_mul]
  simp only [frameMatrix_eq_conjugate, he, Matrix.mul_assoc]

/-- Multiplication by the inverse metric raises exactly the curvature output
index. Symmetry is used only for h and the resulting quadratic tensor. -/
theorem ricci_action_of_gauss (g h R : Matrix4) (hg : g.det ≠ 0) (hh : h.IsSymm)
    (hq : (h*g⁻¹*h).IsSymm) (k l : Fin 4)
    (hR : ∀ i s, (R*g) i s = g i l*g k s-g i k*g l s+h i l*h s k-h i k*h s l) :
    R*h+h*Rᵀ = Matrix.of (fun i j => ricciPolynomial g h (h*g⁻¹*h) i j k l) := by
  have he : R*h = (R*g)*(g⁻¹*h) := by
    rw [← Matrix.mul_assoc,Matrix.mul_assoc R g g⁻¹,
      Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.mpr hg),mul_one]
  have hr (i j : Fin 4) : (R*h) i j =
      g i l*h k j-g i k*h l j+h i l*(h*g⁻¹*h) k j-h i k*(h*g⁻¹*h) l j := by
    rw [he,Matrix.mul_apply]
    simp only [hR, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have hgh : g*(g⁻¹*h)=h := by
      rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.mpr hg),one_mul]
    have hhh : h*(g⁻¹*h)=h*g⁻¹*h := (Matrix.mul_assoc _ _ _).symm
    have hhk (a b : Fin 4) : (∑ r, h r a*(g⁻¹*h) r b) = (h*(g⁻¹*h)) a b := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro r _
      rw [hh.apply r a]
    rw [hhk, hhk]
    change g i l*(g*(g⁻¹*h)) k j-g i k*(g*(g⁻¹*h)) l j+
      h i l*(h*(g⁻¹*h)) k j-h i k*(h*(g⁻¹*h)) l j = _
    rw [hgh,hhh]
  have ht : h*Rᵀ=(R*h)ᵀ := by rw [Matrix.transpose_mul,hh.eq]
  ext i j
  simp only [Matrix.add_apply,ht,Matrix.transpose_apply,Matrix.of_apply,hr,ricciPolynomial]
  rw [hh.apply k j,hh.apply l j,hh.apply k i,hh.apply l i,
    hq.apply k j,hq.apply l j,hq.apply k i,hq.apply l i]
  ring

end
end SecondPinching
