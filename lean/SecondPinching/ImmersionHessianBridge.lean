import SecondPinching.HessianContractionNormalization

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The still-unproved Ricci and Peng--Terng inputs in one principal frame.
The three Hessian contractions are absent. Diagonalization is pointwise;
no smooth principal frame or condition on eigenvalue multiplicities is required. -/
def PrincipalHessianCurvatureIdentities (A : Matrix4) (τ : Cubic4) (t : ℝ) (D : Fourth4) : Prop :=
  ∃ (Q : Matrix4) (μ : Vector4), OrthogonalFrame Q ∧
    frameMatrix Q A = Matrix.diagonal μ ∧
    HasRicciCommutator μ ((1-t)/4) (frameFourth Q D) ∧
    fourthNormSq (frameFourth Q D) =
      3*t*(cubicA μ (frameCubic Q τ)-2*cubicB μ (frameCubic Q τ))+t*(11*t-7)/4

/-- Once the intrinsic contractions hold, this is an equivalence with the
previous exact component interface, not a replacement by a stronger predicate. -/
theorem principalHessianIdentities_iff_curvature_of_contractions (A : Matrix4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (htrace : ordinaryTrace D = 0)
    (hweighted : weightedTrace A D = (-t) • cubicGramMatrix τ)
    (hcubic : cubicContraction τ D = 0) :
    PrincipalHessianIdentities A τ t D ↔ PrincipalHessianCurvatureIdentities A τ t D := by
  constructor
  · rintro ⟨Q,μ,hQ,hd,hr,_,_,_,hn⟩
    exact ⟨Q,μ,hQ,hd,hr,hn⟩
  · rintro ⟨Q,μ,hQ,hd,hr,hn⟩
    refine ⟨Q,μ,hQ,hd,hr,?_,?_,?_,hn⟩
    · rw [frameFourth_ordinaryTrace Q hQ, htrace]
      exact (frameMatrixLinear Q).map_zero
    · rw [← hd, frameFourth_weightedTrace Q hQ, hweighted, frame_cubicGramMatrix Q hQ]
      exact (frameMatrixLinear Q).map_smul _ _
    · rw [frameFourth_cubicContraction Q hQ, hcubic]
      simp [frameVector]

/-- Actual local minimality and constant norms discharge all three contractions.
Only the two remaining curvature identities occur on the right side. -/
theorem immersionLocalData_principalHessianIdentities_iff (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (hSimons : ∀ y ∈ F.domain, cubicNormSq (immersionFrameThird F e y) = S*(S-4))
    (x : Chart4) (hx : x ∈ F.domain) :
    PrincipalHessianIdentities (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) ↔
    PrincipalHessianCurvatureIdentities (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) := by
  obtain ⟨ht,hw,hc⟩ := immersionNormalized_hessian_contractions F e S hS hminimal hSnorm hSimons x hx
  exact principalHessianIdentities_iff_curvature_of_contractions _ _ _ _ ht hw hc

section Atlas
variable {Ω ι : Type*} [TopologicalSpace Ω]
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)

local notation "AA" => fun i x => immersionNormalizedA (F i) (e i) S (chart i x)
local notation "ttau" => fun i x => immersionNormalizedTau (F i) (e i) S (chart i x)
local notation "DD" => fun i x => immersionNormalizedD (F i) (e i) S (chart i x)
local notation "VV" => fun i x => immersionReducedV (F i) (e i) S (chart i x)

/-- The latest mean bridge has no independent Hessian contraction premises.
Simons is now explicitly domain-local, because the third contraction differentiates
its norm consequence. Ricci, Peng--Terng, atlas/measure sources and zero integrals
are still obligations. The equality W=square is asserted only after integration. -/
theorem immersionLocalData_mean_identity_from_hessian_contractions
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y) = 0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y) = S)
    (hSimons : ∀ i y, y ∈ (F i).domain → cubicNormSq (immersionFrameThird (F i) (e i) y) = S*(S-4))
    (hcoordinates : ImmersionCoordinateOverlaps F chart U)
    (hcurvature : ∀ i x, x ∈ U i →
      PrincipalHessianCurvatureIdentities (AA i x) (ttau i x) (pinchingParameter S) (DD i x)) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      (∀ x, G.W x = G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν = 0) → (∫ x, G.L3 x ∂ν = 0) → (∫ x, G.J x ∂ν = 0) →
        (∫ x, G.W x ∂ν) = (∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  apply immersionLocalData_mean_identity_from_local_constancy F e chart S ν hS U hU hcover
    hchart hmaps hminimal hSnorm (fun i x hx => hSimons i _ (hmaps i x hx)) hcoordinates
  intro i x hx
  exact (immersionLocalData_principalHessianIdentities_iff (F i) (e i) S hS
    (hminimal i) (hSnorm i) (hSimons i) (chart i x) (hmaps i x hx)).mpr (hcurvature i x hx)

end Atlas
end
end SecondPinching
