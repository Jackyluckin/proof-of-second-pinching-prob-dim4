import SecondPinching.PengTerngAlgebra
import SecondPinching.PengTerngContractions

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem cubicInner_sub_right (T U V : Cubic4) :
    cubicInner T (U-V) = cubicInner T U-cubicInner T V := by
  simp only [cubicInner,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem cubicInner_smul_right (T U : Cubic4) (a : ℝ) :
    cubicInner T (a • U) = a*cubicInner T U := by
  simp only [cubicInner,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

theorem cubicInner_self (T : Cubic4) : cubicInner T T = cubicNormSq T := by
  simp only [cubicInner,cubicNormSq,pow_two]

theorem pengTerngReduced_inner (s : ℝ) (h : Matrix4) (T : Cubic4) (hT : CubicSymmetric T) :
    cubicInner T (pengTerngReduced s h (h*h) T (cubicWeightedTrace h T)) =
      (11-s)*cubicNormSq T-3*(intrinsicCubicA h T-2*intrinsicCubicB h T)-
        6*(cubicWeightedTrace h T ⬝ᵥ cubicWeightedTrace h T) := by
  have he : pengTerngReduced s h (h*h) T (cubicWeightedTrace h T) =
      (11-s) • T-cubicConnectionAction (h*h) T+(2 : ℝ) • cubicDoubleAction h T-
        (2 : ℝ) • cubicTraceProduct h (cubicWeightedTrace h T) := rfl
  rw [he,cubicInner_sub_right,cubicInner_add_right,cubicInner_sub_right,
    cubicInner_smul_right,cubicInner_smul_right,cubicInner_smul_right,cubicInner_self,
    cubicInner_connectionAction _ _ hT,cubicInner_doubleAction _ _ hT,
    cubicInner_traceProduct _ _ _ hT]
  simp only [intrinsicCubicA,pow_two]
  ring

/-- Scalar contraction of the derived cubic equation. The two trace
hypotheses here are minimality and its first derivative, not constant f3. -/
theorem pengTerngCubic_inner (h : Matrix4) (T : Cubic4) (hh : h.IsSymm)
    (hT : CubicSymmetric T) (htr : Matrix.trace h = 0) (hTtr : cubicTrace T = 0) :
    cubicInner T (pengTerngCubic h T) =
      (11-matrixNormSq h)*cubicNormSq T-3*(intrinsicCubicA h T-2*intrinsicCubicB h T)-
        6*(cubicWeightedTrace h T ⬝ᵥ cubicWeightedTrace h T) := by
  rw [pengTerngCubic_reduced h T hh hT htr hTtr,pengTerngReduced_inner _ _ _ hT]

end
end SecondPinching
