import SecondPinching.GlobalPinchingAverages
import SecondPinching.IntrinsicIntegral

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    [MeasurableSpace M] [BorelSpace M]

/-- The full geometric and analytic chain to interval exclusion. The five
finite-check families remain the numerical boundary. Minimality and constant
S are expressed in the constructed actual local frames; no curvature identity,
Hessian condition, measure, Stokes, or zero-average premise remains. -/
theorem globalImmersion_interval_exclusion_of_finite_checks
    (poly : MvPolynomial (Fin 14) ℚ)
    (control : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (gram witness : Fin 24 → ControlIndex → (b : Fin 8) →
      Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ)
    (sigma : Fin 24 → ControlIndex → ℤ)
    (hpoly : exactCoefficientCheck 14 poly endpointPolynomial=true)
    (hexp : ∀ leaf, exactCoefficientCheck 14 poly (certificateExpansionPolynomial leaf (control leaf))=true)
    (hscale : ∀ leaf ij, 0 < sigma leaf ij)
    (hcoeff : ∀ leaf ij, exactCoefficientCheck 12 (control leaf ij)
      (integerBlockQuartic (gram leaf ij) ((compressedGramConstant : ℚ)*(sigma leaf ij : ℚ)))=true)
    (hblocks : ∀ leaf ij b, integerCertificateCheck (certificateBlockSize b)
      (gram leaf ij b) (witness leaf ij b)=true)
    (F : GlobalSphereImmersion M) (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ p y, y ∈ (globalImmersionLocal F p).domain →
      Matrix.trace (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y)=0)
    (hSnorm : ∀ p y, y ∈ (globalImmersionLocal F p).domain →
      matrixNormSq (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y)=S) :
    8 < S := by
  have := isProbabilityMeasure_normalizedInducedVolume F
  obtain ⟨H,hH,_⟩ := globalImmersion_mean_identity F S hS hminimal hSnorm
  rcases hH with ⟨_,hInt,hRep,_,_,_,_,_,_,hMean⟩
  let A : M → Matrix4 := fun x =>
    immersionNormalizedA (globalImmersionLocal F x) (globalImmersionLocalFrame F x) S (chartAt Chart4 x x)
  let τ : M → Cubic4 := fun x =>
    immersionNormalizedTau (globalImmersionLocal F x) (globalImmersionLocalFrame F x) S (chartAt Chart4 x x)
  have had (x : M) : PaperAdmissible (A x) (τ x) :=
    immersionLocalData_admissible_from_minimal_constant (globalImmersionLocal F x) (globalImmersionLocalFrame F x)
      S hS (hminimal x) (hSnorm x) (chartAt Chart4 x x) (globalImmersionLocal_center F x)
  have hW : (fun x => intrinsicPinchingW (A x) (τ x) (pinchingParameter S))=H.W := by
    funext x
    exact ((hRep x x (globalImmersionLocalSource_center F x)).1).symm
  apply intrinsic_interval_exclusion_of_finite_certificate poly control gram witness sigma
    hpoly hexp hscale hcoeff hblocks (normalizedInducedVolume F) A τ had S hS
  · rw [hW]
    exact hInt.1
  · rw [hW]
    exact hMean.2

end
end SecondPinching
