import SecondPinching.ImmersionPengTerng
import SecondPinching.PengTerngNormalization

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The full intrinsic normalized Hessian norm, before any diagonalization. -/
theorem immersionNormalizedD_pengTerng (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    fourthNormSq (immersionNormalizedD F e S x) =
      3*pinchingParameter S*(intrinsicCubicA (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)-
        2*intrinsicCubicB (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x))+
      pinchingParameter S*(11*pinchingParameter S-7)/4 :=
  normalizeFourth_pengTerng S hS _ _ _
    (immersionFrameFourth_norm_of_minimal_constant F e S hminimal hSnorm x hx)

/-- Discharge the exact old Peng--Terng predicate. Diagonalization is pointwise;
repeated and zero principal curvatures require no separate assumption. -/
theorem immersionLocalData_principalPengTerng (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    PrincipalPengTerngIdentity (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) := by
  have had := immersionLocalData_admissible_from_minimal_constant F e S hS hminimal hSnorm x hx
  obtain ⟨Q,μ,hQ,hdiag⟩ := symmetric_orthogonal_diagonalization _ had.1
  refine ⟨Q,μ,hQ,hdiag,?_⟩
  have hτ := (paperAdmissible_frame_iff Q hQ _ _).mpr had
  rw [frameFourth_normSq Q hQ,
    ← intrinsicCubicA_diagonal μ _ hτ.2.1,← intrinsicCubicB_diagonal μ _ hτ.2.1,
    ← hdiag,frame_intrinsicCubicA Q hQ,frame_intrinsicCubicB Q hQ]
  exact immersionNormalizedD_pengTerng F e S hS hminimal hSnorm x hx

/-- The old complete Hessian interface is now obtained from local minimality
and constant squared norm; none of its equations is an independent premise. -/
theorem immersionLocalData_principalHessianIdentities_from_minimal_constant
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    PrincipalHessianIdentities (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) :=
  (immersionLocalData_principalHessianIdentities_iff_pengTerng F e S hS hminimal hSnorm x hx).mpr
    (immersionLocalData_principalPengTerng F e S hS hminimal hSnorm x hx)

section Atlas
variable {Ω ι : Type*} [TopologicalSpace Ω]
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)
local notation "AA" => fun i x => immersionNormalizedA (F i) (e i) S (chart i x)
local notation "ttau" => fun i x => immersionNormalizedTau (F i) (e i) S (chart i x)
local notation "DD" => fun i x => immersionNormalizedD (F i) (e i) S (chart i x)
local notation "VV" => fun i x => immersionReducedV (F i) (e i) S (chart i x)

/-- All local Hessian and Peng--Terng equations now follow from the actual
minimal immersion with constant S. Atlas, measure and the three zero-integral
sources remain explicit. W equals the square only after averaging. -/
theorem immersionLocalData_mean_identity_from_pengTerng
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y) = 0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y) = S)
    (hcoordinates : ImmersionCoordinateOverlaps F chart U) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      (∀ x, G.W x = G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν = 0) → (∫ x, G.L3 x ∂ν = 0) → (∫ x, G.J x ∂ν = 0) →
        (∫ x, G.W x ∂ν) = (∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  apply immersionLocalData_mean_identity_from_ricci_simons F e chart S ν hS U hU hcover
    hchart hmaps hminimal hSnorm hcoordinates
  intro i x hx
  exact immersionLocalData_principalPengTerng (F i) (e i) S hS
    (hminimal i) (hSnorm i) (chart i x) (hmaps i x hx)

end Atlas
end
end SecondPinching
