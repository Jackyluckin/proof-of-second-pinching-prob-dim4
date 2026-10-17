import SecondPinching.ScalarLaplacianGerms

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The three zero averages follow from their actual local divergence
representations. No zero integral, orientation or constant cubic trace is an input. -/
theorem global_pinching_zero_averages (F : GlobalSphereImmersion M) (S : ℝ)
    (G : PinchingScalarFields M) (hcont : pinchingScalarsContinuous G)
    (hd : pinchingDivergencesRepresent G (globalImmersionLocal F) (globalImmersionLocalFrame F)
      (fun p => chartAt Chart4 p) S (globalImmersionLocalSource F)) :
    (∫ x, G.L4 x ∂normalizedInducedVolume F)=0 ∧
    (∫ x, G.L3 x ∂normalizedInducedVolume F)=0 ∧
    (∫ x, G.J x ∂normalizedInducedVolume F)=0 := by
  obtain ⟨P,hP,_⟩ := globalImmersionPotentials_smooth F S
  rcases hP with ⟨h4,h3,hr⟩
  refine ⟨?_,?_,?_⟩
  · apply integral_normalized_global_divergence_eq_zero F
      (scaleCoordinateVector F (1/S^4) (gradientCoordinateVector F P.1 h4)) G.L4 hcont.2.1
    intro p x hx
    rw [scaleCoordinateVector_divergence F (1/S^4) _ p _ hx.2,
      gradientCoordinateVector_divergence_of_representation F P.1 h4
        (fun p => immersionQuarticPotential (globalImmersionLocal F p) (globalImmersionLocalFrame F p) S)
        (fun p y hy => (hr p y hy).1) p _ hx.2,(hd p x hx).1]
    ring
  · apply integral_normalized_global_divergence_eq_zero F
      (scaleCoordinateVector F (1/S^4) (gradientCoordinateVector F P.2 h3)) G.L3 hcont.2.2.1
    intro p x hx
    rw [scaleCoordinateVector_divergence F (1/S^4) _ p _ hx.2,
      gradientCoordinateVector_divergence_of_representation F P.2 h3
        (fun p => immersionCubicPotential (globalImmersionLocal F p) (globalImmersionLocalFrame F p))
        (fun p y hy => (hr p y hy).2) p _ hx.2,(hd p x hx).2.1]
    ring
  · apply integral_normalized_global_divergence_eq_zero F
      (scaleCoordinateVector F (-1/S^3) (cubicFluxCoordinateVector F)) G.J hcont.2.2.2.1
    intro p x hx
    rw [scaleCoordinateVector_divergence F (-1/S^3) _ p _ hx.2,
      cubicFluxCoordinateVector_divergence F p _ hx.2,(hd p x hx).2.2]
    ring

section Mean
variable (F : GlobalSphereImmersion M) (S : ℝ)
local notation "FF" => globalImmersionLocal F
local notation "ee" => globalImmersionLocalFrame F
local notation "cc" => fun p => chartAt Chart4 p
local notation "UU" => globalImmersionLocalSource F
local notation "AA" => fun p x => immersionNormalizedA (FF p) (ee p) S (cc p x)
local notation "ttau" => fun p x => immersionNormalizedTau (FF p) (ee p) S (cc p x)
local notation "VV" => fun p x => immersionReducedV (FF p) (ee p) S (cc p x)
local notation "nu" => normalizedInducedVolume F

/-- The normalized induced-volume mean identity now has no Stokes or
zero-average premises. The pointwise corrected identity is retained separately
from the averaged square identity. -/
theorem globalImmersion_mean_identity [Nonempty M] (hS : 4 < S)
    (hminimal : ∀ p y, y ∈ (FF p).domain → Matrix.trace (immersionFrameSecond (FF p) (ee p) y)=0)
    (hSnorm : ∀ p y, y ∈ (FF p).domain → matrixNormSq (immersionFrameSecond (FF p) (ee p) y)=S) :
    ∃! G : PinchingScalarFields M, pinchingScalarsContinuous G ∧ pinchingScalarsIntegrable G nu ∧
      pinchingScalarsRepresent G UU AA ttau VV (pinchingParameter S) ∧
      pinchingDivergencesRepresent G FF ee cc S UU ∧
      (∀ x, G.W x=G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      (∫ x, G.L4 x ∂nu)=0 ∧ (∫ x, G.L3 x ∂nu)=0 ∧ (∫ x, G.J x ∂nu)=0 ∧
      ((∫ x, G.W x ∂nu)=(∫ x, G.square x ∂nu) ∧ 0 ≤ ∫ x, G.W x ∂nu) := by
  have := isProbabilityMeasure_normalizedInducedVolume F
  obtain ⟨G,hG,hu⟩ := globalImmersion_mean_identity_with_local_divergences F S nu hS hminimal hSnorm
  rcases hG with ⟨hc,hi,hr,hd,hp,hpos,hm⟩
  have hz := global_pinching_zero_averages F S G hc hd
  have hmean := hm hz.1 hz.2.1 hz.2.2
  refine ⟨G,⟨hc,hi,hr,hd,hp,hpos,hz.1,hz.2.1,hz.2.2,hmean⟩,?_⟩
  intro H hH
  rcases hH with ⟨hHc,hHi,hHr,hHd,hHp,hHpos,_,_,_,hHm⟩
  exact hu H ⟨hHc,hHi,hHr,hHd,hHp,hHpos,fun _ _ _ => hHm⟩

end Mean
end
end SecondPinching
