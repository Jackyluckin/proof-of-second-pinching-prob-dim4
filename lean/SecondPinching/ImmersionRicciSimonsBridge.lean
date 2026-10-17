import SecondPinching.ImmersionSimons
import SecondPinching.RicciNormalization

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The normalized Ricci predicate follows in every pointwise principal
frame. No existence of a smooth field of eigenvectors is assumed. -/
theorem immersionNormalizedD_hasRicciCommutator (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S) (x : Chart4) (hx : x ∈ F.domain)
    (Q : Matrix4) (hQ : OrthogonalFrame Q) (μ : Vector4)
    (hdiag : frameMatrix Q (immersionNormalizedA F e S x) = Matrix.diagonal μ) :
    HasRicciCommutator μ ((1-pinchingParameter S)/4) (frameFourth Q (immersionNormalizedD F e S x)) := by
  have hB : frameMatrix (Q*e.coefficients x) (immersionMetric F.map x) = 1 := by
    rw [frameMatrix_composition,e.orthonormal x hx,frameMatrix_one Q hQ]
  have hr := immersionFourthForm_ricci_in_frame F x hx (Q*e.coefficients x) hB
  simp only [frameFourth_composition,frameMatrix_composition] at hr
  change ∀ i j k l,
      frameFourth Q (immersionFrameFourth F e x) i j k l-frameFourth Q (immersionFrameFourth F e x) i j l k =
      ricciPolynomial 1 (frameMatrix Q (immersionFrameSecond F e x))
        (frameMatrix Q (immersionFrameSecond F e x)*frameMatrix Q (immersionFrameSecond F e x)) i j k l at hr
  obtain ⟨ha,_,hD⟩ := normalize_frame S Q (immersionFrameSecond F e x)
    (immersionFrameThird F e x) (immersionFrameFourth F e x)
  have hd : normalizeSecond S (frameMatrix Q (immersionFrameSecond F e x)) = Matrix.diagonal μ := by
    rw [ha]; exact hdiag
  have he := normalizeFourth_hasRicciCommutator S hS _ _ μ hd hr
  rw [hD] at he
  exact he

/-- Only the Peng--Terng norm equation remains of the old principal-frame
Hessian inputs. The same diagonalization witnesses are retained. -/
def PrincipalPengTerngIdentity (A : Matrix4) (τ : Cubic4) (t : ℝ) (D : Fourth4) : Prop :=
  ∃ (Q : Matrix4) (μ : Vector4), OrthogonalFrame Q ∧
    frameMatrix Q A = Matrix.diagonal μ ∧
    fourthNormSq (frameFourth Q D) =
      3*t*(cubicA μ (frameCubic Q τ)-2*cubicB μ (frameCubic Q τ))+t*(11*t-7)/4

/-- This equivalence removes the Ricci premise for the actual fields only;
it does not assert a new Ricci identity for arbitrary admissible tensors. -/
theorem immersionLocalData_curvature_iff_pengTerng (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S) (x : Chart4) (hx : x ∈ F.domain) :
    PrincipalHessianCurvatureIdentities (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) ↔
    PrincipalPengTerngIdentity (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) := by
  constructor
  · rintro ⟨Q,μ,hQ,hd,_,hPT⟩; exact ⟨Q,μ,hQ,hd,hPT⟩
  · rintro ⟨Q,μ,hQ,hd,hPT⟩
    exact ⟨Q,μ,hQ,hd,immersionNormalizedD_hasRicciCommutator F e S hS x hx Q hQ μ hd,hPT⟩

/-- Both cubic trace constraints and the Simons normalization now have
actual geometric sources: local minimality and constant |h|^2. -/
theorem immersionLocalData_admissible_from_minimal_constant
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    PaperAdmissible (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) :=
  immersionLocalData_admissible_of_local_constancy F e S hS hminimal hSnorm x hx
    (immersionFrameThird_norm_of_minimal_constant F e S hminimal hSnorm x hx)

theorem immersionNormalized_contractions_from_minimal_constant
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    ordinaryTrace (immersionNormalizedD F e S x) = 0 ∧
    weightedTrace (immersionNormalizedA F e S x) (immersionNormalizedD F e S x) =
      (-pinchingParameter S) • cubicGramMatrix (immersionNormalizedTau F e S x) ∧
    cubicContraction (immersionNormalizedTau F e S x) (immersionNormalizedD F e S x) = 0 :=
  immersionNormalized_hessian_contractions F e S hS hminimal hSnorm
    (immersionFrameThird_norm_of_minimal_constant F e S hminimal hSnorm) x hx

/-- Exact equivalence with the old full Hessian interface after discharging
Ricci, all three contractions and the Simons norm consequence. -/
theorem immersionLocalData_principalHessianIdentities_iff_pengTerng
    (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    PrincipalHessianIdentities (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) ↔
    PrincipalPengTerngIdentity (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)
      (pinchingParameter S) (immersionNormalizedD F e S x) :=
  (immersionLocalData_principalHessianIdentities_iff F e S hS hminimal hSnorm
    (immersionFrameThird_norm_of_minimal_constant F e S hminimal hSnorm) x hx).trans
    (immersionLocalData_curvature_iff_pengTerng F e S hS x hx)

section Atlas
variable {Ω ι : Type*} [TopologicalSpace Ω]
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)
local notation "AA" => fun i x => immersionNormalizedA (F i) (e i) S (chart i x)
local notation "ttau" => fun i x => immersionNormalizedTau (F i) (e i) S (chart i x)
local notation "DD" => fun i x => immersionNormalizedD (F i) (e i) S (chart i x)
local notation "VV" => fun i x => immersionReducedV (F i) (e i) S (chart i x)

/-- The latest mean bridge has no independent Ricci or Simons hypotheses.
Peng--Terng, the atlas/measure sources and the three zero integrals remain.
The square identity is still an averaged identity, not W=square pointwise. -/
theorem immersionLocalData_mean_identity_from_ricci_simons
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hminimal : ∀ i y, y ∈ (F i).domain → Matrix.trace (immersionFrameSecond (F i) (e i) y) = 0)
    (hSnorm : ∀ i y, y ∈ (F i).domain → matrixNormSq (immersionFrameSecond (F i) (e i) y) = S)
    (hcoordinates : ImmersionCoordinateOverlaps F chart U)
    (hPT : ∀ i x, x ∈ U i →
      PrincipalPengTerngIdentity (AA i x) (ttau i x) (pinchingParameter S) (DD i x)) :
    ∃! G : PinchingScalarFields Ω, pinchingScalarsContinuous G ∧
      pinchingScalarsIntegrable G ν ∧ pinchingScalarsRepresent G U AA ttau VV (pinchingParameter S) ∧
      (∀ x, G.W x = G.square x-(89/8 : ℝ)*G.L4 x+16*G.L3 x+(13/4 : ℝ)*G.J x) ∧
      (∀ x, 0 ≤ G.square x) ∧
      ((∫ x, G.L4 x ∂ν = 0) → (∫ x, G.L3 x ∂ν = 0) → (∫ x, G.J x ∂ν = 0) →
        (∫ x, G.W x ∂ν) = (∫ x, G.square x ∂ν) ∧ 0 ≤ ∫ x, G.W x ∂ν) := by
  apply immersionLocalData_mean_identity_from_hessian_contractions F e chart S ν hS U hU hcover
    hchart hmaps hminimal hSnorm
    (fun i => immersionFrameThird_norm_of_minimal_constant (F i) (e i) S (hminimal i) (hSnorm i)) hcoordinates
  intro i x hx
  exact (immersionLocalData_curvature_iff_pengTerng (F i) (e i) S hS
    (chart i x) (hmaps i x hx)).mpr (hPT i x hx)

end Atlas
end
end SecondPinching
