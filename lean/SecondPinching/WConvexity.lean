import SecondPinching.QuadraticEstimate
import SecondPinching.CubicVectorBound
import SecondPinching.IntegralIdentity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Convex.Function

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Matrix
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The zero-endpoint estimate in prop:convex for every admissible pair,
including p=0. Zero is only the algebraic parameter here. -/
theorem pinchingW_zero_bound (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    pinchingW μ τ 0 ≤ -(75/32 : ℝ)*phiNormSq (Matrix.diagonal μ) ∧
      -(75/32 : ℝ)*phiNormSq (Matrix.diagonal μ) ≤ 0 := by
  obtain ⟨hτ,_hμ,_hn,hτn,ht,_hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  have hH := vectorGramOperator_bound τ hτ ht hτn (Matrix.diagonal μ *ᵥ cubicD μ τ)
  have hd := cubicD_weighted_norm_bound μ τ had
  have hp := phiNormSq_nonneg (Matrix.diagonal μ)
  rw [pinchingW_zero, wConstantCoeff]
  constructor <;> linarith

/-- The quadratic coefficient is at least 1/6; 97/48 is proved, not assumed. -/
theorem wQuadraticCoeff_lower_bound (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) : 1/6 ≤ wQuadraticCoeff μ τ := by
  obtain ⟨hB,hBt⟩ := trialB_codomain μ τ had
  have hx : Matrix.trace ((8 : ℝ) • trialB μ τ) = 0 := by
    rw [Matrix.trace_smul, hBt]
    simp
  have h := hessianPsi_quadratic_bound μ τ had ((8 : ℝ) • trialB μ τ) (hB.smul _) hx
  simp only [matrixGramOperator_smul, matrixInner_smul_left, matrixInner_smul_right] at h
  unfold wQuadraticCoeff
  linarith

/-- The ordinary real derivative, with A,tau and B fixed. -/
theorem pinchingW_hasDerivAt (μ : Vector4) (τ : Cubic4) (t : ℝ) :
    HasDerivAt (pinchingW μ τ) (2*wQuadraticCoeff μ τ*t+wLinearCoeff μ τ) t := by
  have h := (((hasDerivAt_pow 2 t).const_mul (wQuadraticCoeff μ τ)).add
    ((hasDerivAt_id t).const_mul (wLinearCoeff μ τ))).add_const (wConstantCoeff μ τ)
  have he : pinchingW μ τ = fun s =>
      wQuadraticCoeff μ τ*s^2+wLinearCoeff μ τ*s+wConstantCoeff μ τ := by
    funext s
    exact pinchingW_eq_quadratic μ τ s
  rw [he]
  simp only [Pi.add_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h
  convert h using 1 <;> ring

/-- Actual second derivative, rather than only a named quadratic coefficient. -/
theorem pinchingW_second_derivative (μ : Vector4) (τ : Cubic4) (t : ℝ) :
    deriv (deriv (pinchingW μ τ)) t = 2*wQuadraticCoeff μ τ := by
  have he : deriv (pinchingW μ τ) = fun s => 2*wQuadraticCoeff μ τ*s+wLinearCoeff μ τ := by
    funext s
    exact (pinchingW_hasDerivAt μ τ s).deriv
  rw [he]
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id t).const_mul (2*wQuadraticCoeff μ τ)).add_const
      (wLinearCoeff μ τ)).deriv

/-- The second inequality in eq:Wbounds for all real t. -/
theorem pinchingW_second_derivative_bound (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    (1/3 : ℝ) ≤ deriv (deriv (pinchingW μ τ)) t := by
  rw [pinchingW_second_derivative]
  linarith [wQuadraticCoeff_lower_bound μ τ had]

/-- Convexity on the full real parameter line. -/
theorem pinchingW_convex (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) : ConvexOn ℝ Set.univ (pinchingW μ τ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have he : a*pinchingW μ τ x+b*pinchingW μ τ y-pinchingW μ τ (a*x+b*y) =
      wQuadraticCoeff μ τ*a*b*(x-y)^2 := by
    simp only [pinchingW_eq_quadratic, quadratic]
    rw [show b = 1-a by linarith]
    ring
  have hn : 0 ≤ wQuadraticCoeff μ τ*a*b*(x-y)^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith [wQuadraticCoeff_lower_bound μ τ had]) ha) hb)
      (sq_nonneg _)
  linarith

/-- Scalar interpolation now applies to the actual W. The endpoint inequality
is an explicit pending certificate input, not an axiom or a proved endpoint here. -/
theorem pinchingW_interpolation_of_endpoint (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ)
    (hhalf : pinchingW μ τ (1/2) ≤ -(1/10000 : ℝ))
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ 1/2) : pinchingW μ τ t ≤ -t/5000 := by
  have hzero := (pinchingW_zero_bound μ τ had).1.trans (pinchingW_zero_bound μ τ had).2
  rw [pinchingW_eq_quadratic] at hhalf hzero ⊢
  exact quadratic_endpoint_interpolation _ _ _
    (by linarith [wQuadraticCoeff_lower_bound μ τ had]) hzero hhalf ht htop

/-- The final interval exclusion for scalar fields representing the actual W.
Admissibility, the endpoint input, integrability, and the nonnegative average
are explicit; this is not the theorem for a minimal immersion. -/
theorem pinching_interval_exclusion_of_W_inputs {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Ω → Vector4) (τ : Ω → Cubic4)
    (had : ∀ x, PaperAdmissible (Matrix.diagonal (μ x)) (τ x))
    (hhalf : ∀ x, pinchingW (μ x) (τ x) (1/2) ≤ -(1/10000 : ℝ))
    (S : ℝ) (hS : 4 < S)
    (hInt : Integrable (fun x => pinchingW (μ x) (τ x) (pinchingParameter S)) ν)
    (hmean : 0 ≤ ∫ x, pinchingW (μ x) (τ x) (pinchingParameter S) ∂ν) : 8 < S := by
  by_contra h8
  have htop := pinchingParameter_le_half hS (le_of_not_gt h8)
  have ht := pinchingParameter_pos hS
  have hbound : (∫ x, pinchingW (μ x) (τ x) (pinchingParameter S) ∂ν) ≤
      ∫ _ : Ω, -(pinchingParameter S)/5000 ∂ν :=
    integral_mono hInt (integrable_const _) (fun x =>
      pinchingW_interpolation_of_endpoint (μ x) (τ x) (had x) (hhalf x) _ ht.le htop)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbound
  linarith

end
end SecondPinching
