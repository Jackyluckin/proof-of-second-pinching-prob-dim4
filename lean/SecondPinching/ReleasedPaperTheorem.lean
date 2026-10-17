import SecondPinching.PaperTheorem
import SecondPinching.ReleasedCertificate

set_option autoImplicit false
open scoped ContDiff Manifold
namespace SecondPinching
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The manuscript's main theorem with the sole computational premise bound
to its exact released finite certificate. All geometric and analytic steps
are kernel-checked dependencies; external acceptance is visibly separate. -/
theorem secondPinching_dim4_of_released_certificate
    (hcertificate : FiniteEndpointAccepted releasedEndpointData)
    (F : SphereImmersion M) (S : ℝ)
    (hminimal : IsMinimalSphereImmersion (sphereImmersionToAmbient F))
    (hSnorm : HasConstantSecondFundamentalNorm (sphereImmersionToAmbient F) S)
    (hS : 4 < S) : 8 < S :=
  secondPinching_dim4_of_finite_data releasedEndpointData hcertificate F S hminimal hSnorm hS

end SecondPinching
