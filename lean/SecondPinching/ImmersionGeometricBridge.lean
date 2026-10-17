import SecondPinching.ImmersionIntegralBridge
import SecondPinching.ImmersionCodazzi
import SecondPinching.ImmersionReparametrization

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- Actual Codazzi and h symmetry discharge the former symmetry premises. -/
theorem immersionLocalData_admissible_of_geometric_inputs
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (x : Chart4) (hx : x ∈ F.domain)
    (hminimal : Matrix.trace (immersionFrameSecond F e x) = 0)
    (hSnorm : matrixNormSq (immersionFrameSecond F e x) = S)
    (hSimons : cubicNormSq (immersionFrameThird F e x) = S*(S-4))
    (htrace : ∀ k, ∑ i, immersionFrameThird F e x i i k = 0)
    (hweighted : ∀ k, ∑ i, ∑ j,
      immersionFrameSecond F e x i j * immersionFrameThird F e x i j k = 0) :
    PaperAdmissible (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) :=
  immersionLocalData_admissible F e S hS x (immersionFrameSecond_symmetric F e x hx)
    (immersionFrameThird_symmetric F e x hx) hminimal hSnorm hSimons htrace hweighted

/-- For one actual parametrization, transport of the concrete V no longer
needs an independent first-three-symmetry hypothesis. -/
theorem immersionLocalData_actual_frame_transition (F : LocalSphereImmersion)
    (e e' : LocalImmersionFrame F) (S : ℝ) (x : Chart4) (hx : x ∈ F.domain) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      immersionNormalizedA F e' S x = frameMatrix Q (immersionNormalizedA F e S x) ∧
      immersionNormalizedTau F e' S x = frameCubic Q (immersionNormalizedTau F e S x) ∧
      immersionReducedV F e' S x = frameFourth Q (immersionReducedV F e S x) :=
  immersionLocalData_frame_transition F e e' S x hx (immersionFrameFourth_firstThree F e x hx)

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

/-- The earlier mean bridge with Codazzi and first-three Hessian symmetry
derived from the actual immersion. The remaining raw geometric identities,
cross-coordinate h/T/H transitions and three zero integrals stay explicit. -/
theorem immersionLocalData_mean_identity_of_geometric_inputs
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
    (hrawtrans : ∀ i j x, x ∈ U i → x ∈ U j → ∃ Q : Matrix4, OrthogonalFrame Q ∧
      ((hh j x = frameMatrix Q (hh i x) ∧ TT j x = frameCubic Q (TT i x) ∧ HH j x = frameFourth Q (HH i x)) ∨
       (hh j x = -frameMatrix Q (hh i x) ∧ TT j x = -frameCubic Q (TT i x) ∧ HH j x = -frameFourth Q (HH i x))))
    (hprincipal : ∀ i x, x ∈ U i →
      PrincipalHessianIdentities (AA i x) (ttau i x) (pinchingParameter S) (DD i x)) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      (∀ x, G.W x = G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν = 0) → (∫ x, G.L3 x ∂ν = 0) → (∫ x, G.J x ∂ν = 0) →
        (∫ x, G.W x ∂ν) = (∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  apply immersionLocalData_mean_identity F e chart S ν hS U hU hcover hchart hmaps
  · intro i x hx
    obtain ⟨hm,hn,hs,ht,hw⟩ := hgeom i x hx
    exact ⟨immersionFrameThird_symmetric (F i) (e i) _ (hmaps i x hx),
      hm,hn,hs,ht,hw,immersionFrameFourth_firstThree (F i) (e i) _ (hmaps i x hx)⟩
  · exact hrawtrans
  · exact hprincipal

end Atlas
end
end SecondPinching
