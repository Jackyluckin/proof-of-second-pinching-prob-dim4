import SecondPinching.ImmersionOverlap
import SecondPinching.ImmersionGeometricBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- Coordinate compatibility of the actual immersion maps near each overlap
point. This contains no normal agreement, tensor transformation law, curvature
identity or assertion that such an atlas has already been constructed globally. -/
def ImmersionCoordinateOverlaps {Ω ι : Type*}
    (F : ι → LocalSphereImmersion) (chart : ι → Ω → Chart4) (U : ι → Set Ω) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j → ∃ P : ImmersionReparametrization (F i),
    chart j x ∈ P.domain ∧ P.map (chart j x) = chart i x ∧
    (F j).map =ᶠ[𝓝 (chart j x)] (F i).map ∘ P.map

/-- The previous raw tensor-overlap premise is discharged from coordinate
compatibility and actual immersion derivatives. -/
theorem immersionAtlas_raw_transitions {Ω ι : Type*}
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (U : ι → Set Ω)
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hcoordinates : ImmersionCoordinateOverlaps F chart U)
    (i j : ι) (x : Ω) (hi : x ∈ U i) (hj : x ∈ U j) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      ((immersionFrameSecond (F j) (e j) (chart j x) =
          frameMatrix Q (immersionFrameSecond (F i) (e i) (chart i x)) ∧
        immersionFrameThird (F j) (e j) (chart j x) =
          frameCubic Q (immersionFrameThird (F i) (e i) (chart i x)) ∧
        immersionFrameFourth (F j) (e j) (chart j x) =
          frameFourth Q (immersionFrameFourth (F i) (e i) (chart i x))) ∨
       (immersionFrameSecond (F j) (e j) (chart j x) =
          -frameMatrix Q (immersionFrameSecond (F i) (e i) (chart i x)) ∧
        immersionFrameThird (F j) (e j) (chart j x) =
          -frameCubic Q (immersionFrameThird (F i) (e i) (chart i x)) ∧
        immersionFrameFourth (F j) (e j) (chart j x) =
          -frameFourth Q (immersionFrameFourth (F i) (e i) (chart i x)))) := by
  obtain ⟨P,hp,hx,hf⟩ := hcoordinates i j x hi hj
  have h := immersionFrameForms_coordinate_transition (F i) (F j) P (e i) (e j)
    (chart j x) hp (hmaps j x hj) hf
  simpa only [hx] using h

section Atlas
variable {Ω ι : Type*} [TopologicalSpace Ω]
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)

local notation "hh" => fun i x => immersionFrameSecond (F i) (e i) (chart i x)
local notation "TT" => fun i x => immersionFrameThird (F i) (e i) (chart i x)
local notation "HH" => fun i x => immersionFrameFourth (F i) (e i) (chart i x)
local notation "AA" => fun i x => immersionNormalizedA (F i) (e i) S (chart i x)
local notation "ttau" => fun i x => immersionNormalizedTau (F i) (e i) S (chart i x)
local notation "DD" => fun i x => immersionNormalizedD (F i) (e i) S (chart i x)
local notation "VV" => fun i x => immersionReducedV (F i) (e i) S (chart i x)

/-- The five scalar fields and the conditional mean identity now follow
from actual coordinate overlaps. No raw h/T/H or A/tau/V transition premise
remains. The five raw curvature/trace conditions, principal Hessian identities,
finite measure and three zero integrals remain explicit, unproved inputs. -/
theorem immersionLocalData_mean_identity_from_coordinate_overlaps
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hgeom : ∀ i x, x ∈ U i →
      Matrix.trace (hh i x) = 0 ∧ matrixNormSq (hh i x) = S ∧
      cubicNormSq (TT i x) = S*(S-4) ∧
      (∀ k, ∑ a, TT i x a a k = 0) ∧
      (∀ k, ∑ a, ∑ b, hh i x a b * TT i x a b k = 0))
    (hcoordinates : ImmersionCoordinateOverlaps F chart U)
    (hprincipal : ∀ i x, x ∈ U i →
      PrincipalHessianIdentities (AA i x) (ttau i x) (pinchingParameter S) (DD i x)) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      (∀ x, G.W x = G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν = 0) → (∫ x, G.L3 x ∂ν = 0) → (∫ x, G.J x ∂ν = 0) →
        (∫ x, G.W x ∂ν) = (∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  exact immersionLocalData_mean_identity_of_geometric_inputs F e chart S ν hS U hU hcover
    hchart hmaps hgeom (immersionAtlas_raw_transitions F e chart U hmaps hcoordinates) hprincipal

end Atlas
end
end SecondPinching
