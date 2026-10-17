import SecondPinching.ImmersionFrameChange

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The remaining principal-frame Ricci, differentiated-trace and Peng--Terng
inputs. All are the old component statements, now evaluated on the actual
normalized derivatives of the immersion. This predicate does not prove them. -/
def PrincipalHessianIdentities (A : Matrix4) (τ : Cubic4) (t : ℝ) (D : Fourth4) : Prop :=
  ∃ (Q : Matrix4) (μ : Vector4), OrthogonalFrame Q ∧
    frameMatrix Q A = Matrix.diagonal μ ∧
    HasRicciCommutator μ ((1-t)/4) (frameFourth Q D) ∧
    ordinaryTrace (frameFourth Q D) = 0 ∧
    weightedTrace (Matrix.diagonal μ) (frameFourth Q D) = (-t) • cubicGramMatrix (frameCubic Q τ) ∧
    cubicContraction (frameCubic Q τ) (frameFourth Q D) = 0 ∧
    fourthNormSq (frameFourth Q D) =
      3*t*(cubicA μ (frameCubic Q τ)-2*cubicB μ (frameCubic Q τ))+t*(11*t-7)/4

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

/-- Actual local immersion fields enter the stage-13 interface. The theorem
derives continuity, admissibility, V and its four local equations. The remaining
unnormalized geometric identities and transitions between different coordinate
parametrizations are explicit premises, as are the three zero integrals in the
conclusion. It does not assert an atlas-realization theorem for an arbitrary M. -/
theorem immersionLocalData_mean_identity
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (hS : 4 < S)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hgeom : ∀ i x, x ∈ U i →
      CubicSymmetric (TT i x) ∧ Matrix.trace (hh i x) = 0 ∧ matrixNormSq (hh i x) = S ∧
      cubicNormSq (TT i x) = S*(S-4) ∧
      (∀ k, ∑ a, TT i x a a k = 0) ∧
      (∀ k, ∑ a, ∑ b, hh i x a b * TT i x a b k = 0) ∧ FirstThreeSymmetric (HH i x))
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
  have had (i : ι) (x : Ω) (hx : x ∈ U i) : PaperAdmissible (AA i x) (ttau i x) := by
    obtain ⟨hT,hm,hn,hs,ht,hw,_⟩ := hgeom i x hx
    exact immersionLocalData_admissible (F i) (e i) S hS (chart i x)
      (immersionFrameSecond_symmetric (F i) (e i) _ (hmaps i x hx)) hT hm hn hs ht hw
  have hD (i : ι) (x : Ω) (hx : x ∈ U i) : FirstThreeSymmetric (DD i x) := by
    have h := (hgeom i x hx).2.2.2.2.2.2
    constructor
    · intro a b c d; simp only [immersionNormalizedD,normalizeFourth,Pi.smul_apply,h.1]
    · intro a b c d; simp only [immersionNormalizedD,normalizeFourth,Pi.smul_apply,h.2]
  have hs (i : ι) (x : Ω) (hx : x ∈ U i) :
      TraceFreeFourth (VV i x) ∧
      weightedTrace (AA i x) (VV i x) = hessianE (AA i x) (ttau i x) (pinchingParameter S) ∧
      cubicContraction (ttau i x) (VV i x) = intrinsicHessianB0 (AA i x) (ttau i x) ∧
      fourthNormSq (VV i x) =
        3*pinchingParameter S*(intrinsicCubicA (AA i x) (ttau i x)-2*intrinsicCubicB (AA i x) (ttau i x))+
        pinchingParameter S*(35*pinchingParameter S-28)/16-(3/2 : ℝ)*phiNormSq (AA i x) := by
    obtain ⟨Q,μ,hQ,hdiag,hr,htr,hw,hc,hp⟩ := hprincipal i x hx
    exact immersionReducedV_spec (F i) (e i) S (chart i x) (had i x hx) (hD i x hx)
      Q hQ μ hdiag hr htr hw hc hp
  apply localPinchingScalars_mean_identity ν U hU hcover AA ttau VV (pinchingParameter S)
  · intro i
    exact (contDiffOn_immersionLocalData (F i) (e i) S).1.continuousOn.comp (hchart i) (hmaps i)
  · intro i
    exact (contDiffOn_immersionLocalData (F i) (e i) S).2.1.continuousOn.comp (hchart i) (hmaps i)
  · intro i
    exact (contDiffOn_immersionLocalData (F i) (e i) S).2.2.2.continuousOn.comp (hchart i) (hmaps i)
  · exact had
  · intro i j x hi hj
    exact normalized_reduced_signed_overlap S (hh i x) (hh j x) (TT i x) (TT j x) (HH i x) (HH j x)
      (immersionFrameSecond_symmetric (F i) (e i) _ (hmaps i x hi))
      ((hgeom i x hi).2.2.2.2.2.2) (hrawtrans i j x hi hj)
  · exact fun i x hx => (hs i x hx).1
  · exact fun i x hx => (hs i x hx).2.1
  · exact fun i x hx => (hs i x hx).2.2.1
  · exact fun i x hx => (hs i x hx).2.2.2

end Atlas
end
end SecondPinching
