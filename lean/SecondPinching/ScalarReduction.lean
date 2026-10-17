import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Scalar steps in the final proof

These are the indicated scalar consequences in the proof of Theorem 1.3.
They do not assert the geometric identities or the endpoint certificate.
The coefficient `a` below is a generic quadratic coefficient, not the
cubic contraction called `a` in Definition 2.3 of the paper.
-/

open scoped BigOperators
open MeasureTheory

namespace SecondPinching
noncomputable section

/-- The parameter defined in equation (2.10). -/
def pinchingParameter (S : ℝ) : ℝ := (S-4)/S

theorem pinchingParameter_pos {S : ℝ} (hS : 4 < S) :
    0 < pinchingParameter S := by
  exact div_pos (sub_pos.mpr hS) (by linarith)

theorem pinchingParameter_le_half {S : ℝ} (hS : 4 < S) (h8 : S ≤ 8) :
    pinchingParameter S ≤ 1/2 := by
  unfold pinchingParameter
  apply (div_le_iff₀ (show 0 < S by linarith)).mpr
  linarith

/-- The elementary quadratic polynomial used in the scalar reduction. -/
def quadratic (a b c t : ℝ) : ℝ := a*t^2+b*t+c

/-- The chord inequality used in the last paragraph of the paper. -/
theorem quadratic_chord_bound (a b c : ℝ) (ha : 0 ≤ a)
    {t : ℝ} (ht : 0 ≤ t) (htop : t ≤ 1/2) :
    quadratic a b c t ≤
      (1-2*t)*quadratic a b c 0+2*t*quadratic a b c (1/2) := by
  have hnonneg : 0 ≤ a*t*(1/2-t) :=
    mul_nonneg (mul_nonneg ha ht) (sub_nonneg.mpr htop)
  dsimp only [quadratic]
  nlinarith

/-- Scalar interpolation with the paper's exact endpoint constant.
This is a consequence of Proposition 5.5 and Proposition 5.6, not a
replacement for either of those propositions. -/
theorem quadratic_endpoint_interpolation (a b c : ℝ) (ha : 0 ≤ a)
    (hzero : quadratic a b c 0 ≤ 0)
    (hhalf : quadratic a b c (1/2) ≤ -(1/10000 : ℝ))
    {t : ℝ} (ht : 0 ≤ t) (htop : t ≤ 1/2) :
    quadratic a b c t ≤ -t/5000 := by
  have hchord := quadratic_chord_bound a b c ha ht htop
  have hleft : (1-2*t)*quadratic a b c 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hzero
  have hright := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*t by linarith)
  linarith

/-- The integration contradiction in the final paragraph, after the
geometric volume is normalised to a probability measure. The required
integrability, coefficient bounds and endpoint inequalities are explicit. -/
theorem quadratic_integral_contradiction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a b c : Ω → ℝ) (t : ℝ)
    (hInt : Integrable (fun x => quadratic (a x) (b x) (c x) t) μ)
    (ha : ∀ x, 0 ≤ a x)
    (hzero : ∀ x, quadratic (a x) (b x) (c x) 0 ≤ 0)
    (hhalf : ∀ x, quadratic (a x) (b x) (c x) (1/2) ≤ -(1/10000 : ℝ))
    (ht : 0 < t) (htop : t ≤ 1/2)
    (hmean : 0 ≤ ∫ x, quadratic (a x) (b x) (c x) t ∂μ) : False := by
  have hbound : (∫ x, quadratic (a x) (b x) (c x) t ∂μ) ≤
      ∫ _ : Ω, -t/5000 ∂μ :=
    integral_mono hInt (integrable_const _) (fun x =>
      quadratic_endpoint_interpolation (a x) (b x) (c x) (ha x)
        (hzero x) (hhalf x) ht.le htop)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbound
  linarith

end
end SecondPinching
