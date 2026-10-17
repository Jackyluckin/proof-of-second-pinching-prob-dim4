import SecondPinching.ImmersionRegularity
import SecondPinching.ReducedHessianBridge

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Rows are tangent vectors in the coordinate basis, orthonormal for the
induced metric. This is a local choice, not a global principal frame. -/
structure LocalImmersionFrame (F : LocalSphereImmersion) where
  coefficients : Chart4 → Matrix4
  smooth : ContDiffOn ℝ ∞ coefficients F.domain
  orthonormal : ∀ x ∈ F.domain,
    frameMatrix (coefficients x) (immersionMetric F.map x) = 1

/-- A chosen frame really is a basis: its coefficient matrix is nonsingular. -/
theorem localImmersionFrame_det_ne_zero (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) :
    (e.coefficients x).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_right_inverse
    (A := e.coefficients x) (B := immersionMetric F.map x * (e.coefficients x)ᵀ)
  simpa only [frameMatrix_eq_conjugate,Matrix.mul_assoc] using e.orthonormal x hx

def immersionFrameSecond (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) : Matrix4 :=
  frameMatrix (e.coefficients x) (immersionSecondForm F.map F.normal x)

def immersionFrameThird (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) : Cubic4 :=
  frameCubic (e.coefficients x) (immersionThirdForm F.map F.normal x)

def immersionFrameFourth (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) : Fourth4 :=
  frameFourth (e.coefficients x) (immersionFourthForm F.map F.normal x)

def immersionNormalizedA (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (x : Chart4) : Matrix4 := normalizeSecond S (immersionFrameSecond F e x)

def immersionNormalizedTau (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (x : Chart4) : Cubic4 := normalizeThird S (immersionFrameThird F e x)

def immersionNormalizedD (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (x : Chart4) : Fourth4 := normalizeFourth S (immersionFrameFourth F e x)

/-- V is constructed from f, its normal, its local frame and S. It is not an
independent fourth tensor chosen to satisfy the target equations. -/
def immersionReducedV (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (x : Chart4) : Fourth4 :=
  intrinsicHessianRemainder (immersionNormalizedA F e S x) (pinchingParameter S)
    (immersionNormalizedD F e S x)

theorem contDiffOn_immersionFrameForms (F : LocalSphereImmersion) (e : LocalImmersionFrame F) :
    ContDiffOn ℝ ∞ (immersionFrameSecond F e) F.domain ∧
    ContDiffOn ℝ ∞ (immersionFrameThird F e) F.domain ∧
    ContDiffOn ℝ ∞ (immersionFrameFourth F e) F.domain := by
  obtain ⟨hh,ht,hd⟩ := contDiffOn_immersionForms F
  have hp := e.smooth
  constructor
  · unfold immersionFrameSecond frameMatrix
    fun_prop
  constructor
  · unfold immersionFrameThird frameCubic frameMatrix
    fun_prop
  · unfold immersionFrameFourth frameFourth frameCubic frameMatrix
    fun_prop

theorem contDiffOn_immersionLocalData (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) :
    ContDiffOn ℝ ∞ (immersionNormalizedA F e S) F.domain ∧
    ContDiffOn ℝ ∞ (immersionNormalizedTau F e S) F.domain ∧
    ContDiffOn ℝ ∞ (immersionNormalizedD F e S) F.domain ∧
    ContDiffOn ℝ ∞ (immersionReducedV F e S) F.domain := by
  obtain ⟨hh,ht,hd⟩ := contDiffOn_immersionFrameForms F e
  have ha : ContDiffOn ℝ ∞ (immersionNormalizedA F e S) F.domain := by
    unfold immersionNormalizedA normalizeSecond
    fun_prop
  have hb : ContDiffOn ℝ ∞ (immersionNormalizedTau F e S) F.domain := by
    unfold immersionNormalizedTau normalizeThird
    fun_prop
  have hc : ContDiffOn ℝ ∞ (immersionNormalizedD F e S) F.domain := by
    unfold immersionNormalizedD normalizeFourth
    fun_prop
  refine ⟨ha,hb,hc,?_⟩
  unfold immersionReducedV intrinsicHessianRemainder intrinsicHessianTraceCorrection
    symmetrizeFourth ordinaryTraceAdjoint
  fun_prop

/-- Substitution of the actual component fields into the normalization lemma.
The remaining geometric identities occur here as explicit, unnormalized premises. -/
theorem immersionLocalData_admissible (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S) (x : Chart4)
    (hs : (immersionFrameSecond F e x).IsSymm)
    (hT : CubicSymmetric (immersionFrameThird F e x))
    (hminimal : Matrix.trace (immersionFrameSecond F e x) = 0)
    (hSnorm : matrixNormSq (immersionFrameSecond F e x) = S)
    (hSimons : cubicNormSq (immersionFrameThird F e x) = S*(S-4))
    (htrace : ∀ k, ∑ i, immersionFrameThird F e x i i k = 0)
    (hweighted : ∀ k, ∑ i, ∑ j,
      immersionFrameSecond F e x i j * immersionFrameThird F e x i j k = 0) :
    PaperAdmissible (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) :=
  normalized_paperAdmissible S hS _ _ hs hT hminimal hSnorm hSimons htrace hweighted

/-- The exact tensor constructed above satisfies the old local Hessian
interface when the remaining principal-frame curvature identities are supplied. -/
theorem immersionReducedV_spec (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (x : Chart4)
    (had : PaperAdmissible (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x))
    (hD : FirstThreeSymmetric (immersionNormalizedD F e S x))
    (Q : Matrix4) (hQ : OrthogonalFrame Q) (μ : Vector4)
    (hdiag : frameMatrix Q (immersionNormalizedA F e S x) = Matrix.diagonal μ)
    (hRicci : HasRicciCommutator μ ((1-pinchingParameter S)/4)
      (frameFourth Q (immersionNormalizedD F e S x)))
    (htr : ordinaryTrace (frameFourth Q (immersionNormalizedD F e S x)) = 0)
    (hweighted : weightedTrace (Matrix.diagonal μ) (frameFourth Q (immersionNormalizedD F e S x)) =
      (-pinchingParameter S) • cubicGramMatrix (frameCubic Q (immersionNormalizedTau F e S x)))
    (hcubic : cubicContraction (frameCubic Q (immersionNormalizedTau F e S x))
      (frameFourth Q (immersionNormalizedD F e S x)) = 0)
    (hPT : fourthNormSq (frameFourth Q (immersionNormalizedD F e S x)) =
      3*pinchingParameter S*(cubicA μ (frameCubic Q (immersionNormalizedTau F e S x))-
        2*cubicB μ (frameCubic Q (immersionNormalizedTau F e S x)))+
      pinchingParameter S*(11*pinchingParameter S-7)/4) :
    TraceFreeFourth (immersionReducedV F e S x) ∧
    weightedTrace (immersionNormalizedA F e S x) (immersionReducedV F e S x) =
      hessianE (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) (pinchingParameter S) ∧
    cubicContraction (immersionNormalizedTau F e S x) (immersionReducedV F e S x) =
      intrinsicHessianB0 (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x) ∧
    fourthNormSq (immersionReducedV F e S x) =
      3*pinchingParameter S*(intrinsicCubicA (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x)-
        2*intrinsicCubicB (immersionNormalizedA F e S x) (immersionNormalizedTau F e S x))+
      pinchingParameter S*(35*pinchingParameter S-28)/16-
      (3/2 : ℝ)*phiNormSq (immersionNormalizedA F e S x) :=
  intrinsicHessianRemainder_spec _ _ _ _ had hD Q hQ μ hdiag hRicci htr hweighted hcubic hPT

end
end SecondPinching
