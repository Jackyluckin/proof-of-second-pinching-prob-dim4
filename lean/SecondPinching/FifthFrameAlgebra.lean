import SecondPinching.MovingFrameFourth

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

def frameFifthLinear (B : Matrix4) : Fifth4 →ₗ[ℝ] Fifth4 where
  toFun := frameFifth B
  map_add' K L := by
    funext i j k l m
    simp only [frameFifth,frameFourth,frameCubic,frameMatrix,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c K := by
    funext i j k l m
    simp only [frameFifth,frameFourth,frameCubic,frameMatrix,Pi.smul_apply,smul_eq_mul,
      RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro r _; ring

theorem frameFifth_swap12 (B : Matrix4) (K : Fifth4) :
    frameFifth B (fun i j k l m => K j i k l m) = fun i j k l m => frameFifth B K j i k l m := by
  funext i j k l m
  simp only [frameFifth,frameFourth,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _; ring

theorem frameFifth_swap23 (B : Matrix4) (K : Fifth4) :
    frameFifth B (fun i j k l m => K i k j l m) = fun i j k l m => frameFifth B K i k j l m := by
  funext i j k l m
  simp only [frameFifth]
  apply Finset.sum_congr rfl; intro a _
  have h := congrFun (congrFun (congrFun (congrFun (frameFourth_swap12 B (K a)) j) k) l) m
  rw [h]

theorem frameFifth_swap45 (B : Matrix4) (K : Fifth4) :
    frameFifth B (fun i j k l m => K i j k m l) = fun i j k l m => frameFifth B K i j k m l := by
  funext i j k l m
  simp only [frameFifth]
  apply Finset.sum_congr rfl; intro a _
  have h := congrFun (congrFun (congrFun (congrFun (frameFourth_swap34 B (K a)) j) k) l) m
  rw [h]

/-- A two-tensor in slots two and three and a three-tensor in the complementary slots. -/
theorem frameFifth_product23 (B A : Matrix4) (T : Cubic4) :
    frameFifth B (fun i j k l m => A j k*T i l m) =
      fun i j k l m => frameMatrix B A j k*frameCubic B T i l m := by
  funext i j k l m
  simp only [frameFifth,frameFourth,frameCubic,frameMatrix,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => arg 2; ext a; arg 2; ext d; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext a; arg 2; ext b; arg 2; ext d; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro q _; ring

theorem matrix_gram_pairing (B : Matrix4) (u v : Vector4) :
    (∑ r, (∑ a, B r a*u a)*(∑ b, B r b*v b)) =
      ∑ a, ∑ b, (Bᵀ*B) a b*u a*v b := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro r _; ring

/-- The inverse metric is essential when a coordinate index is contracted. -/
theorem frameFifth_curvature_contraction (B ginv : Matrix4) (T : Cubic4) (R : Fourth4)
    (hi : ginv = Bᵀ*B) :
    frameFifth B (fun i j k l m => ∑ a, ∑ b, ginv a b*T a j k*R b i l m) =
      fun i j k l m => ∑ r, frameCubic B T r j k*frameFourth B R r i l m := by
  have hf : (fun i j k l m => ∑ a, ∑ b, ginv a b*T a j k*R b i l m : Fifth4) =
      ∑ a, ∑ b, ginv a b • (fun i j k l m => T a j k*R b i l m) := by
    funext i j k l m
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_assoc]
  have hsum (f : Fin 4 → Fifth4) : frameFifth B (∑ a, f a) = ∑ a, frameFifth B (f a) :=
    map_sum (frameFifthLinear B) f Finset.univ
  have hsmul (c : ℝ) (K : Fifth4) : frameFifth B (c • K) = c • frameFifth B K :=
    (frameFifthLinear B).map_smul c K
  have hl : frameFifth B (∑ a, ∑ b, ginv a b • (fun i j k l m => T a j k*R b i l m)) =
      ∑ a, ∑ b, ginv a b • frameFifth B (fun i j k l m => T a j k*R b i l m) := by
    rw [hsum]
    apply Finset.sum_congr rfl; intro a _
    rw [hsum]
    apply Finset.sum_congr rfl; intro b _
    exact hsmul (ginv a b) _
  rw [hf,hl]
  funext i j k l m
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,frameCubic,frameFourth]
  rw [matrix_gram_pairing]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [frameFifth_product23 B (T a) (R b),hi]
  exact (mul_assoc _ _ _).symm

def coordinateGaussTensor (g h : Matrix4) : Fourth4 := fun i j k l =>
  g i k*g j l-g i l*g j k+h i k*h j l-h i l*h j k

theorem frameFourth_coordinateGauss (B g h : Matrix4) :
    frameFourth B (coordinateGaussTensor g h) =
      coordinateGaussTensor (frameMatrix B g) (frameMatrix B h) := by
  have he : coordinateGaussTensor g h =
      (fun i j k l => g i k*g j l)-(fun i j k l => g i l*g j k)+
      (fun i j k l => h i k*h j l)-(fun i j k l => h i l*h j k) := rfl
  rw [he]
  change frameFourthLinear B _ = _
  simp only [map_add,map_sub,frameFourthLinear,LinearMap.coe_mk,AddHom.coe_mk,
    frameFourth_product13,frameFourth_product14]
  rfl

theorem inverse_metric_of_frame (B g : Matrix4) (hB : B.det ≠ 0)
    (horth : frameMatrix B g = 1) : g⁻¹ = Bᵀ*B := by
  have hi := isUnit_iff_ne_zero.mpr hB
  have hbg : B*g*Bᵀ = 1 := by simpa only [frameMatrix_eq_conjugate] using horth
  have hgi : g*(Bᵀ*B) = 1 := by
    calc
      _ = B⁻¹*(B*g*Bᵀ)*B := by
        calc
          _ = (B⁻¹*B)*g*Bᵀ*B := by rw [Matrix.nonsing_inv_mul B hi,one_mul,Matrix.mul_assoc]
          _ = _ := by noncomm_ring
      _ = 1 := by rw [hbg,mul_one,Matrix.nonsing_inv_mul B hi]
  have hgunit := isUnit_iff_ne_zero.mpr (Matrix.det_ne_zero_of_right_inverse hgi)
  calc
    g⁻¹ = g⁻¹*(g*(Bᵀ*B)) := by rw [hgi,mul_one]
    _ = Bᵀ*B := by rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul g hgunit,one_mul]

end
end SecondPinching
