import SecondPinching.TensorChangeAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The scalar chain rule in the row-Jacobian convention. -/
theorem coordinateScalar_comp_derivative (φ : Chart4 → Chart4) (f : Chart4 → ℝ)
    (x : Chart4) (hφ : DifferentiableAt ℝ φ x)
    (hf : DifferentiableAt ℝ f (φ x)) (k : Fin 4) :
    fderiv ℝ (fun y => f (φ y)) x (coordinateUnit k) =
      ∑ c, coordinateJacobian φ x k c * fderiv ℝ f (φ x) (coordinateUnit c) := by
  change fderiv ℝ (f ∘ φ) x _ = _
  rw [fderiv_comp x hf hφ]
  change fderiv ℝ f (φ x) (fderiv ℝ φ x (coordinateUnit k)) = _
  conv_lhs => rw [chart4_coordinate_expansion (fderiv ℝ φ x (coordinateUnit k))]
  simp only [map_sum,map_smul,smul_eq_mul,coordinateJacobian]

/-- Product and chain rules before any connection terms are subtracted. -/
theorem coordinateMatrix_pullback_derivative (φ : Chart4 → Chart4)
    (h : Chart4 → Matrix4) (x : Chart4)
    (hφ : DifferentiableAt ℝ φ x)
    (hJ : DifferentiableAt ℝ (coordinateJacobian φ) x)
    (hh : DifferentiableAt ℝ h (φ x)) (i j k : Fin 4) :
    fderiv ℝ (fun y => frameMatrix (coordinateJacobian φ y) (h (φ y)) i j)
      x (coordinateUnit k) =
      ∑ a, ∑ b,
        ((fderiv ℝ (fun y => coordinateJacobian φ y i a) x (coordinateUnit k)) *
          coordinateJacobian φ x j b * h (φ x) a b +
        coordinateJacobian φ x i a *
          (fderiv ℝ (fun y => coordinateJacobian φ y j b) x (coordinateUnit k)) * h (φ x) a b +
        coordinateJacobian φ x i a * coordinateJacobian φ x j b *
          ∑ c, coordinateJacobian φ x k c *
            fderiv ℝ (fun y => h y a b) (φ x) (coordinateUnit c)) := by
  have hji (u v : Fin 4) : DifferentiableAt ℝ (fun y => coordinateJacobian φ y u v) x := by fun_prop
  have hhab (a b : Fin 4) : DifferentiableAt ℝ (fun y => h y a b) (φ x) := by fun_prop
  have hhc (a b : Fin 4) : DifferentiableAt ℝ (fun y => h (φ y) a b) x := by fun_prop
  simp only [frameMatrix]
  erw [fderiv_fun_sum (u := Finset.univ) (fun a _ => (hji i a).mul
    (DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ => (hji j b).mul (hhc a b))))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  erw [fderiv_fun_mul (hji i a) (DifferentiableAt.fun_sum (u := Finset.univ)
    (fun b _ => (hji j b).mul (hhc a b)))]
  erw [fderiv_fun_sum (u := Finset.univ) (fun b _ => (hji j b).mul (hhc a b))]
  simp only [add_apply,smul_apply,smul_eq_mul,sum_apply,Finset.mul_sum,Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  erw [fderiv_fun_mul (hji j b) (hhc a b)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [coordinateScalar_comp_derivative φ (fun y => h y a b) x hφ (hhab a b)]
  simp only [Pi.mul_apply,← Finset.mul_sum]
  ring

/-- Naturality of covariant differentiation on a two-tensor, conditional
only on the displayed connection law and differentiability at this point. -/
theorem coordinateCovariant2_pullback (φ : Chart4 → Chart4)
    (h : Chart4 → Matrix4) (Γ Γ' : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Chart4) (hφ : DifferentiableAt ℝ φ x)
    (hJ : DifferentiableAt ℝ (coordinateJacobian φ) x)
    (hh : DifferentiableAt ℝ h (φ x))
    (hΓ : ∀ i k a, (∑ r, Γ' x r i k * coordinateJacobian φ x r a) =
      fderiv ℝ (fun y => coordinateJacobian φ y i a) x (coordinateUnit k) +
      ∑ b, ∑ c, coordinateJacobian φ x i b * coordinateJacobian φ x k c * Γ (φ x) a b c) :
    coordinateCovariant2 Γ' (fun y => frameMatrix (coordinateJacobian φ y) (h (φ y))) x =
      frameCubic (coordinateJacobian φ x) (coordinateCovariant2 Γ h (φ x)) := by
  funext i j k
  unfold coordinateCovariant2
  rw [coordinateMatrix_pullback_derivative φ h x hφ hJ hh]
  exact matrix_pullback_connection_algebra (coordinateJacobian φ x)
    (fun u a => fderiv ℝ (fun y => coordinateJacobian φ y u a) x (coordinateUnit k))
    (h (φ x)) (fun u r => Γ' x r u k) (Γ (φ x))
    (fun a b c => fderiv ℝ (fun y => h y a b) (φ x) (coordinateUnit c)) i j k
    (fun u a => hΓ u k a)

/-- The product rule for a finite sum of scalar multiples of two-tensors.
The connection is fixed; no derivative of its coefficients is assumed here. -/
theorem coordinateCovariant2_sum_mul
    (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (c : Fin 4 → Chart4 → ℝ) (h : Fin 4 → Chart4 → Matrix4) (x : Chart4)
    (hc : ∀ a, DifferentiableAt ℝ (c a) x)
    (hh : ∀ a, DifferentiableAt ℝ (h a) x) (i j k : Fin 4) :
    coordinateCovariant2 Γ (fun y => ∑ a, c a y • h a y) x i j k =
      ∑ a, (fderiv ℝ (c a) x (coordinateUnit k) * h a x i j +
        c a x * coordinateCovariant2 Γ (h a) x i j k) := by
  have hhij (a u v : Fin 4) : DifferentiableAt ℝ (fun y => h a y u v) x := by fun_prop
  have hd : fderiv ℝ (fun y => ∑ a, c a y * h a y i j) x (coordinateUnit k) =
      ∑ a, (fderiv ℝ (c a) x (coordinateUnit k) * h a x i j +
        c a x * fderiv ℝ (fun y => h a y i j) x (coordinateUnit k)) := by
    erw [fderiv_fun_sum (u := Finset.univ) (fun a _ => (hc a).mul (hhij a i j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl; intro a _
    erw [fderiv_fun_mul (hc a) (hhij a i j)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  simp only [coordinateCovariant2,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [hd]
  simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_sub,Finset.sum_sub_distrib]
  have h1 : (∑ r, ∑ a, Γ x r i k * (c a x * h a x r j)) =
      ∑ a, ∑ r, c a x * (Γ x r i k * h a x r j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro r _
    ring
  have h2 : (∑ r, ∑ a, Γ x r j k * (c a x * h a x i r)) =
      ∑ a, ∑ r, c a x * (Γ x r j k * h a x i r) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro r _
    ring
  rw [h1,h2]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  ring

/-- Separating the first-slot connection term exposes the two-tensor
covariant derivative in the remaining slots. -/
theorem coordinateCovariant3_slice
    (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) (x : Chart4) (i j k l : Fin 4) :
    coordinateCovariant3 Γ T x i j k l =
      coordinateCovariant2 Γ (fun y => T y i) x j k l - ∑ r, Γ x r i l * T x r j k := by
  simp only [coordinateCovariant3,coordinateCovariant2,Finset.sum_add_distrib]
  ring

/-- All three tensor slots, including the previous derivative slot, transform
before another covariant derivative is taken. No tensor symmetry is required. -/
theorem coordinateCovariant3_pullback (φ : Chart4 → Chart4)
    (T : Chart4 → Cubic4) (Γ Γ' : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Chart4) (hφ : DifferentiableAt ℝ φ x)
    (hJ : DifferentiableAt ℝ (coordinateJacobian φ) x)
    (hT : DifferentiableAt ℝ T (φ x))
    (hΓ : ∀ i k a, (∑ r, Γ' x r i k * coordinateJacobian φ x r a) =
      fderiv ℝ (fun y => coordinateJacobian φ y i a) x (coordinateUnit k) +
      ∑ b, ∑ c, coordinateJacobian φ x i b * coordinateJacobian φ x k c * Γ (φ x) a b c) :
    coordinateCovariant3 Γ' (fun y => frameCubic (coordinateJacobian φ y) (T (φ y))) x =
      frameFourth (coordinateJacobian φ x) (coordinateCovariant3 Γ T (φ x)) := by
  have hc (i a : Fin 4) : DifferentiableAt ℝ (fun y => coordinateJacobian φ y i a) x := by fun_prop
  have ht (a : Fin 4) : DifferentiableAt ℝ (fun y => T y a) (φ x) := by fun_prop
  have hm (a : Fin 4) : DifferentiableAt ℝ
      (fun y => frameMatrix (coordinateJacobian φ y) (T (φ y) a)) x := by
    unfold frameMatrix
    fun_prop
  have he (i : Fin 4) : (fun y => frameCubic (coordinateJacobian φ y) (T (φ y)) i) =
      (fun y => ∑ a, coordinateJacobian φ y i a • frameMatrix (coordinateJacobian φ y) (T (φ y) a)) := by
    funext y; exact frameCubic_slice _ _ i
  funext i j k l
  rw [coordinateCovariant3_slice,he i]
  rw [coordinateCovariant2_sum_mul Γ'
    (fun a y => coordinateJacobian φ y i a)
    (fun a y => frameMatrix (coordinateJacobian φ y) (T (φ y) a)) x (hc i) hm]
  simp_rw [coordinateCovariant2_pullback φ (fun y => T y _) Γ Γ' x hφ hJ (ht _) hΓ]
  have h := cubic_pullback_connection_algebra (coordinateJacobian φ x)
    (fun u a => fderiv ℝ (fun y => coordinateJacobian φ y u a) x (coordinateUnit l))
    (fun u r => Γ' x r u l) (Γ (φ x)) (T (φ x))
    (fun a => coordinateCovariant2 Γ (fun y => T y a) (φ x)) i j k l
    (fun u a => hΓ u l a)
  simpa only [← coordinateCovariant3_slice] using h

end
end SecondPinching
