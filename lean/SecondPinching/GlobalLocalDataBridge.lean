import SecondPinching.GlobalImmersionAtlas
import SecondPinching.ConstructedImmersionFrame
import SecondPinching.ImmersionDivergenceBridge

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

def globalImmersionLocalFrame (F : GlobalSphereImmersion M) (p : M) :
    LocalImmersionFrame (globalImmersionLocal F p) := constructedImmersionFrame _

section Mean
variable (F : GlobalSphereImmersion M) (S : ℝ)
local notation "FF" => globalImmersionLocal F
local notation "ee" => globalImmersionLocalFrame F
local notation "cc" => fun p => chartAt Chart4 p
local notation "UU" => globalImmersionLocalSource F
local notation "AA" => fun p x => immersionNormalizedA (FF p) (ee p) S (cc p x)
local notation "ttau" => fun p x => immersionNormalizedTau (FF p) (ee p) S (cc p x)
local notation "VV" => fun p x => immersionReducedV (FF p) (ee p) S (cc p x)

/-- The earlier mean interface now uses charts, normals, frames and overlaps
constructed from one actual smooth manifold immersion. Minimality and constant
S are expressed in these local frames. The measure is still an arbitrary finite
measure and the three zero-integral antecedents are explicitly retained. -/
theorem globalImmersion_mean_identity_with_local_divergences
    [CompactSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    (ν : Measure M) [IsFiniteMeasure ν] (hS : 4 < S)
    (hminimal : ∀ p y, y ∈ (FF p).domain → Matrix.trace (immersionFrameSecond (FF p) (ee p) y)=0)
    (hSnorm : ∀ p y, y ∈ (FF p).domain → matrixNormSq (immersionFrameSecond (FF p) (ee p) y)=S) :
    ∃! G : PinchingScalarFields M, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G UU AA ttau VV (pinchingParameter S) ∧
      pinchingDivergencesRepresent G FF ee cc S UU ∧
      (∀ x, G.W x=G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν=0) → (∫ x, G.L3 x ∂ν=0) → (∫ x, G.J x ∂ν=0) →
        (∫ x, G.W x ∂ν)=(∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  exact immersionLocalData_mean_identity_with_divergences FF ee cc S ν hS UU
    (isOpen_globalImmersionLocalSource F) (globalImmersionLocalSource_cover F)
    (globalImmersionLocalSource_chart_continuous F) (fun _ _ hx => hx.2) hminimal hSnorm
    (globalImmersionLocal_coordinate_overlaps F)

end Mean
end
end SecondPinching
