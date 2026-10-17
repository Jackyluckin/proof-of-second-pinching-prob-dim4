import SecondPinching.GlobalIntervalExclusion
import SecondPinching.GlobalCurvatureInvariants
import SecondPinching.NativeSphereImmersion
import SecondPinching.FiniteEndpointData

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- Both directions of the geometric-hypothesis correspondence. The global
conditions are expressed using the actual spherical second fundamental and
mean-curvature vectors; the local conditions are exactly those of the earlier
geometric/analytic exclusion theorem. -/
theorem paper_geometric_hypotheses_iff (F : SphereImmersion M) (S : ℝ) :
    (IsMinimalSphereImmersion (sphereImmersionToAmbient F) ∧
      HasConstantSecondFundamentalNorm (sphereImmersionToAmbient F) S) ↔
    ((∀ p y, y ∈ (globalImmersionLocal (sphereImmersionToAmbient F) p).domain →
      Matrix.trace (immersionFrameSecond (globalImmersionLocal (sphereImmersionToAmbient F) p)
        (globalImmersionLocalFrame (sphereImmersionToAmbient F) p) y)=0) ∧
     (∀ p y, y ∈ (globalImmersionLocal (sphereImmersionToAmbient F) p).domain →
      matrixNormSq (immersionFrameSecond (globalImmersionLocal (sphereImmersionToAmbient F) p)
        (globalImmersionLocalFrame (sphereImmersionToAmbient F) p) y)=S)) :=
  and_congr (isMinimalSphereImmersion_iff_local_trace _) (hasConstantSecondFundamentalNorm_iff_local_norm _ S)

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The manuscript's thm:main for a native S5-valued smooth immersion, with
its connectedness retained. ConnectedSpace supplies nonemptiness. The Borel
measurable structure and volume are constructed inside the proof. The sole
computational boundary is acceptance of the explicitly supplied finite data. -/
theorem secondPinching_dim4_of_finite_data (D : FiniteEndpointData) (hD : FiniteEndpointAccepted D)
    (F : SphereImmersion M) (S : ℝ)
    (hminimal : IsMinimalSphereImmersion (sphereImmersionToAmbient F))
    (hSnorm : HasConstantSecondFundamentalNorm (sphereImmersionToAmbient F) S)
    (hS : 4 < S) : 8 < S := by
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  obtain ⟨hm,hn⟩ := (paper_geometric_hypotheses_iff F S).mp ⟨hminimal,hSnorm⟩
  rcases hD with ⟨hP,he,hs,hc,hb⟩
  exact globalImmersion_interval_exclusion_of_finite_checks D.polynomial D.controls D.gramNumerator
    D.congruenceWitness D.bernsteinIntegerScale hP he hs hc hb
    (sphereImmersionToAmbient F) S hS hm hn

end
end SecondPinching
