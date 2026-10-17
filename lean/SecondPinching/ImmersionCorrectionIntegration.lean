import SecondPinching.LocalDivergenceIntegration
import SecondPinching.VolumeDensityReparametrization

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem contDiffOn_immersionCubicFlux (F : LocalSphereImmersion) (e : LocalImmersionFrame F) :
    ContDiffOn ℝ ∞ (immersionCubicFlux F e) F.domain := by
  have hh := (contDiffOn_immersionFrameForms F e).1
  have ht := (contDiffOn_immersionFrameForms F e).2.1
  have hp := contDiffOn_matrix_pow hh 2
  unfold immersionCubicFlux intrinsicCubicD cubicWeightedTrace Matrix.mulVec dotProduct
  fun_prop

/-- The local cutoff version of the first zero-average identity. The extra
gradient term must be retained until the partition of unity is summed. -/
theorem integral_immersionL4_cutoff (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (χ : Chart4 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ F.domain) :
    (∫ x : Chart4, immersionVolumeDensity F x *
      (χ x * intrinsicCorrectionL4 (immersionNormalizedA F e S x)
          (immersionNormalizedTau F e S x) (pinchingParameter S) +
        (1/S^4) * (immersionScalarGradient F e χ x ⬝ᵥ
          immersionScalarGradient F e (immersionQuarticPotential F e S) x)))=0 := by
  apply integral_immersionCorrection_cutoff F e χ _
    (immersionScalarGradient F e (immersionQuarticPotential F e S)) (1/S^4) hχ
    (contDiffOn_immersionScalarGradient F e _ (contDiffOn_immersionQuarticPotential F e S)) hc hs
  intro x hx
  rw [immersionVectorDivergence_gradient,immersionL4_divergence_identity F e S hS hminimal hSnorm x hx]
  ring

theorem integral_immersionL3_cutoff (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (χ : Chart4 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ F.domain) :
    (∫ x : Chart4, immersionVolumeDensity F x *
      (χ x * intrinsicCorrectionL3 (immersionNormalizedA F e S x)
          (immersionNormalizedTau F e S x) (pinchingParameter S) +
        (1/S^4) * (immersionScalarGradient F e χ x ⬝ᵥ
          immersionScalarGradient F e (immersionCubicPotential F e) x)))=0 := by
  apply integral_immersionCorrection_cutoff F e χ _
    (immersionScalarGradient F e (immersionCubicPotential F e)) (1/S^4) hχ
    (contDiffOn_immersionScalarGradient F e _ (contDiffOn_immersionCubicPotential F e)) hc hs
  intro x hx
  rw [immersionVectorDivergence_gradient,immersionL3_divergence_identity F e S hS hminimal hSnorm x hx]
  ring

/-- The negative normalization for J is preserved from eq:divergences. -/
theorem integral_immersionJ_cutoff (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y)=0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y)=S)
    (χ : Chart4 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ F.domain) :
    (∫ x : Chart4, immersionVolumeDensity F x *
      (χ x * intrinsicCorrectionJ (immersionNormalizedA F e S x)
          (immersionNormalizedTau F e S x) (pinchingParameter S) +
        (-1/S^3) * (immersionScalarGradient F e χ x ⬝ᵥ immersionCubicFlux F e x)))=0 := by
  apply integral_immersionCorrection_cutoff F e χ _ (immersionCubicFlux F e) (-1/S^3)
    hχ (contDiffOn_immersionCubicFlux F e) hc hs
  intro x hx
  rw [immersionJ_divergence_identity F e S hS hminimal hSnorm x hx]
  ring

end
end SecondPinching
