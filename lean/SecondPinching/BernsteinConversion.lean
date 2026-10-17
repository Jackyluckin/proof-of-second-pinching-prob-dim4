import SecondPinching.BernsteinPositivity

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
namespace SecondPinching
noncomputable section

/-- The exact power-to-Bernstein coefficient of a degree at most 14 monomial. -/
def powerBernsteinFactor (i a : Fin 15) : ℝ :=
  (Nat.choose i.val a.val : ℝ) / (Nat.choose 14 a.val : ℝ)

/-- Every denominator in the degree-14 conversion is positive. -/
theorem powerBernsteinFactor_denominator_pos (a : Fin 15) :
    0 < (Nat.choose 14 a.val : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : a.val ≤ 14)

/-- Conversion coefficients are nonnegative, including the zero terms a>i. -/
theorem powerBernsteinFactor_nonneg (i a : Fin 15) :
    0 ≤ powerBernsteinFactor i a := by
  unfold powerBernsteinFactor
  positivity

/-- The constant coefficient contributes with weight one to every control. -/
theorem powerBernsteinFactor_zero (i : Fin 15) : powerBernsteinFactor i 0 = 1 := by
  simp [powerBernsteinFactor]

/-- The degree-14 conversion identity is a polynomial identity on all real s.
It does not depend on positivity, interior points, or sampled evaluation. -/
theorem power_to_bernstein_fourteen (a : Fin 15) (s : ℝ) :
    s ^ a.val = ∑ i : Fin 15, bernsteinWeight 14 i s * powerBernsteinFactor i a := by
  have hchoose : ∀ i a : Fin 15, Nat.choose i.val a.val =
      (![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 4, 6, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 5, 10, 10, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 6, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        ![1, 7, 21, 35, 35, 21, 7, 1, 0, 0, 0, 0, 0, 0, 0],
        ![1, 8, 28, 56, 70, 56, 28, 8, 1, 0, 0, 0, 0, 0, 0],
        ![1, 9, 36, 84, 126, 126, 84, 36, 9, 1, 0, 0, 0, 0, 0],
        ![1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1, 0, 0, 0, 0],
        ![1, 11, 55, 165, 330, 462, 462, 330, 165, 55, 11, 1, 0, 0, 0],
        ![1, 12, 66, 220, 495, 792, 924, 792, 495, 220, 66, 12, 1, 0, 0],
        ![1, 13, 78, 286, 715, 1287, 1716, 1716, 1287, 715, 286, 78, 13, 1, 0],
        ![1, 14, 91, 364, 1001, 2002, 3003, 3432, 3003, 2002, 1001, 364, 91, 14, 1]]) i a := by decide
  have hfourteen : ∀ a : Fin 15, Nat.choose 14 a.val =
      (![1, 14, 91, 364, 1001, 2002, 3003, 3432, 3003, 2002, 1001, 364, 91, 14, 1]) a := by decide
  simp only [bernsteinWeight, powerBernsteinFactor, hchoose, hfourteen]
  fin_cases a <;> norm_num [Fin.sum_univ_succ] <;> ring

/-- Tensor-product conversion of the bivariate power coefficients e_ab. -/
def bivariateBernsteinCoefficient (e : ControlIndex → ℝ) (ij : ControlIndex) : ℝ :=
  ∑ ab, e ab * powerBernsteinFactor ij.1 ab.1 * powerBernsteinFactor ij.2 ab.2

/-- The full bivariate conversion, with all 225 power slots present.
Coefficients beyond a lower degree are represented by zero. -/
theorem bivariate_power_to_bernstein (e : ControlIndex → ℝ) (s t : ℝ) :
    (∑ ab : ControlIndex, e ab * s ^ ab.1.val * t ^ ab.2.val) =
      ∑ ij : ControlIndex, bernsteinWeight 14 ij.1 s * bernsteinWeight 14 ij.2 t *
        bivariateBernsteinCoefficient e ij := by
  simp_rw [bivariateBernsteinCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab _
  simp only [Fintype.sum_prod_type]
  rw [power_to_bernstein_fourteen ab.1 s, power_to_bernstein_fourteen ab.2 t]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Nonnegative power coefficients and a positive constant coefficient give a
strictly positive Bernstein coefficient at every control, including boundaries. -/
theorem bivariateBernsteinCoefficient_pos (e : ControlIndex → ℝ)
    (he : ∀ ab, 0 ≤ e ab) (hzero : 0 < e (0,0)) (ij : ControlIndex) :
    0 < bivariateBernsteinCoefficient e ij := by
  unfold bivariateBernsteinCoefficient
  apply Finset.sum_pos'
  · intro ab _
    exact mul_nonneg (mul_nonneg (he ab) (powerBernsteinFactor_nonneg _ _))
      (powerBernsteinFactor_nonneg _ _)
  · refine ⟨(0,0), Finset.mem_univ _, ?_⟩
    simpa only [powerBernsteinFactor_zero, mul_one] using hzero

end
end SecondPinching
