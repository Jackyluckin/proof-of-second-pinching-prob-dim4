import SecondPinching.RicciFrameAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem ricciPolynomial_diagonal (μ : Vector4) (κ : ℝ) (i j k l : Fin 4) :
    ricciPolynomial (κ • (1 : Matrix4)) (Matrix.diagonal μ)
      (Matrix.diagonal μ*Matrix.diagonal μ) i j k l =
      (μ i-μ j)*(κ+μ i*μ j)*
        ((1 : Matrix4) i k*(1 : Matrix4) j l-(1 : Matrix4) i l*(1 : Matrix4) j k) := by
  simp only [ricciPolynomial, Matrix.diagonal_mul_diagonal, Matrix.smul_apply,
    smul_eq_mul, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> subst_vars <;> simp_all <;> ring

/-- The normalization preserves exactly the Ricci scale kappa=(1-t)/4=1/S. -/
theorem normalizeFourth_ricci (S : ℝ) (hS : 4 < S) (h : Matrix4) (H : Fourth4)
    (hr : ∀ i j k l, H i j k l-H i j l k = ricciPolynomial 1 h (h*h) i j k l)
    (i j k l : Fin 4) :
    normalizeFourth S H i j k l-normalizeFourth S H i j l k =
      ricciPolynomial (((1-pinchingParameter S)/4) • (1 : Matrix4))
        (normalizeSecond S h) (normalizeSecond S h*normalizeSecond S h) i j k l := by
  obtain ⟨ha,_,_,ha2,_⟩ := normalization_denominators hS
  simp only [normalizeFourth,Pi.smul_apply,smul_eq_mul,← mul_sub,hr,
    normalizeSecond,Matrix.smul_mul,Matrix.mul_smul,
    ricciPolynomial,Matrix.smul_apply,smul_eq_mul,pinchingParameter]
  conv_rhs => rw [← ha2]
  conv_lhs => rw [← ha2]
  simp only [Real.sqrt_sq ha.le]
  field_simp [ha.ne']
  ring

/-- A diagonalization of the normalized second form yields the literal
principal-frame predicate used by the existing Hessian decomposition. -/
theorem normalizeFourth_hasRicciCommutator (S : ℝ) (hS : 4 < S) (h : Matrix4)
    (H : Fourth4) (μ : Vector4) (hd : normalizeSecond S h = Matrix.diagonal μ)
    (hr : ∀ i j k l, H i j k l-H i j l k = ricciPolynomial 1 h (h*h) i j k l) :
    HasRicciCommutator μ ((1-pinchingParameter S)/4) (normalizeFourth S H) := by
  intro i j k l
  rw [normalizeFourth_ricci S hS h H hr,hd,ricciPolynomial_diagonal]

end
end SecondPinching
