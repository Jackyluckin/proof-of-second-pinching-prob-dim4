import SecondPinching.ImmersionTraceDerivatives

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- Both cubic traces follow from the original local geometric conditions.
The equalities hold on the coordinate domain, not merely at the evaluation point. -/
theorem immersionFrameThird_traces_of_local_constancy
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    (∀ k, ∑ i, immersionFrameThird F e x i i k = 0) ∧
    (∀ k, ∑ i, ∑ j, immersionFrameSecond F e x i j * immersionFrameThird F e x i j k = 0) := by
  exact ⟨immersionFrameThird_trace_of_minimal_germ F e x hx
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hminimal),
    immersionFrameThird_weighted_of_norm_germ F e S x hx
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hSnorm)⟩

/-- Admissibility with both trace constraints derived. Simons' norm identity
is still an explicit premise; its geometric derivation is not asserted here. -/
theorem immersionLocalData_admissible_of_constancy_germs
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (x : Chart4) (hx : x ∈ F.domain)
    (hminimal : (fun y => Matrix.trace (immersionFrameSecond F e y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ))
    (hSnorm : (fun y => matrixNormSq (immersionFrameSecond F e y)) =ᶠ[𝓝 x] fun _ => S)
    (hSimons : cubicNormSq (immersionFrameThird F e x) = S*(S-4)) :
    PaperAdmissible (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) := by
  exact immersionLocalData_admissible_of_geometric_inputs F e S hS x hx
    hminimal.self_of_nhds hSnorm.self_of_nhds hSimons
    (immersionFrameThird_trace_of_minimal_germ F e x hx hminimal)
    (immersionFrameThird_weighted_of_norm_germ F e S x hx hSnorm)

theorem immersionLocalData_admissible_of_local_constancy
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain)
    (hSimons : cubicNormSq (immersionFrameThird F e x) = S*(S-4)) :
    PaperAdmissible (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) := by
  exact immersionLocalData_admissible_of_constancy_germs F e S hS x hx
    (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hminimal)
    (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hSnorm) hSimons

section Atlas
variable {Ω ι : Type*} [TopologicalSpace Ω]
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)

local notation "AA" => fun i x => immersionNormalizedA (F i) (e i) S (chart i x)
local notation "ttau" => fun i x => immersionNormalizedTau (F i) (e i) S (chart i x)
local notation "DD" => fun i x => immersionNormalizedD (F i) (e i) S (chart i x)
local notation "VV" => fun i x => immersionReducedV (F i) (e i) S (chart i x)

/-- Both cubic trace inputs are removed from the conditional mean bridge.
Minimality and constant |h|^2 are required locally on the actual coordinate
domains. Simons, the principal Hessian identities, coordinate compatibility,
the finite measure and the three zero integrals remain explicit obligations. -/
theorem immersionLocalData_mean_identity_from_local_constancy
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y) = 0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y) = S)
    (hSimons : ∀ i x, x ∈ U i → cubicNormSq (immersionFrameThird (F i) (e i) (chart i x)) = S*(S-4))
    (hcoordinates : ImmersionCoordinateOverlaps F chart U)
    (hprincipal : ∀ i x, x ∈ U i →
      PrincipalHessianIdentities (AA i x) (ttau i x) (pinchingParameter S) (DD i x)) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      (∀ x, G.W x = G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν = 0) → (∫ x, G.L3 x ∂ν = 0) → (∫ x, G.J x ∂ν = 0) →
        (∫ x, G.W x ∂ν) = (∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  apply immersionLocalData_mean_identity_from_coordinate_overlaps F e chart S ν hS U hU hcover
    hchart hmaps _ hcoordinates hprincipal
  intro i x hx
  have hy := hmaps i x hx
  obtain ⟨ht,hw⟩ := immersionFrameThird_traces_of_local_constancy (F i) (e i) S
    (hminimal i) (hSnorm i) (chart i x) hy
  exact ⟨hminimal i _ hy, hSnorm i _ hy, hSimons i x hx, ht, hw⟩

end Atlas
end
end SecondPinching
