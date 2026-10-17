import SecondPinching.DivergencePotentials

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The existing global correction fields represented by actual local scalar
Laplacians and vector divergence. This predicate contains no zero-integral claim. -/
def pinchingDivergencesRepresent {Ω ι : Type*} (G : PinchingScalarFields Ω)
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ) (U : ι → Set Ω) : Prop :=
  ∀ i x, x ∈ U i →
    G.L4 x=immersionScalarLaplacian (F i) (e i) (immersionQuarticPotential (F i) (e i) S) (chart i x)/S^4 ∧
    G.L3 x=immersionScalarLaplacian (F i) (e i) (immersionCubicPotential (F i) (e i)) (chart i x)/S^4 ∧
    G.J x= -immersionVectorDivergence (F i) (e i) (immersionCubicFlux (F i) (e i)) (chart i x)/S^3

section Atlas
variable {Ω ι : Type*}
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)
local notation "AA" => fun i x => immersionNormalizedA (F i) (e i) S (chart i x)
local notation "ttau" => fun i x => immersionNormalizedTau (F i) (e i) S (chart i x)
local notation "VV" => fun i x => immersionReducedV (F i) (e i) S (chart i x)

theorem pinchingScalars_actual_divergences (G : PinchingScalarFields Ω)
    (hS : 4<S) (U : ι → Set Ω)
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y)=0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y)=S)
    (hr : pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S)) :
    pinchingDivergencesRepresent G F e chart S U := by
  intro i x hx
  obtain ⟨_,h4,h3,hJ,_⟩ := hr i x hx
  rw [h4,h3,hJ]
  exact ⟨immersionL4_divergence_identity (F i) (e i) S hS (hminimal i) (hSnorm i) (chart i x) (hmaps i x hx),
    immersionL3_divergence_identity (F i) (e i) S hS (hminimal i) (hSnorm i) (chart i x) (hmaps i x hx),
    immersionJ_divergence_identity (F i) (e i) S hS (hminimal i) (hSnorm i) (chart i x) (hmaps i x hx)⟩

/-- Adding the derived differential representations neither strengthens nor
weakens the old representation interface for the actual local geometric data. -/
theorem pinchingScalars_divergence_representation_iff (G : PinchingScalarFields Ω)
    (hS : 4<S) (U : ι → Set Ω)
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y)=0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y)=S) :
    (pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      pinchingDivergencesRepresent G F e chart S U) ↔
    pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) := by
  constructor
  · exact And.left
  · intro hr
    exact ⟨hr,pinchingScalars_actual_divergences F e chart S G hS U hmaps hminimal hSnorm hr⟩

/-- The mean interface now carries all three actual local divergence sources.
Global Stokes and the actual volume measure remain to be supplied: the three
zero integrals are explicitly retained in the conclusion. -/
theorem immersionLocalData_mean_identity_with_divergences
    [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y)=0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y)=S)
    (hcoordinates : ImmersionCoordinateOverlaps F chart U) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      pinchingDivergencesRepresent G F e chart S U ∧
      (∀ x, G.W x=G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν=0) → (∫ x, G.L3 x ∂ν=0) → (∫ x, G.J x ∂ν=0) →
        (∫ x, G.W x ∂ν)=(∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  obtain ⟨G,hG,hu⟩ := immersionLocalData_mean_identity_from_pengTerng F e chart S ν hS U hU hcover
    hchart hmaps hminimal hSnorm hcoordinates
  have hd := pinchingScalars_actual_divergences F e chart S G hS U hmaps hminimal hSnorm hG.2.2.1
  refine ⟨G,⟨hG.1,hG.2.1,hG.2.2.1,hd,hG.2.2.2⟩,?_⟩
  intro H hH
  exact hu H ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.2⟩

end Atlas
end
end SecondPinching
