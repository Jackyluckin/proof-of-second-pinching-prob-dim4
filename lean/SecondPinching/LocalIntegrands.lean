import SecondPinching.IntrinsicGluing

set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The five global scalar fields used in eq:Wt and prop:meanconvex.
This is only a container of functions, not a geometric immersion. -/
structure PinchingScalarFields (Ω : Type*) where
  W : Ω → ℝ
  L4 : Ω → ℝ
  L3 : Ω → ℝ
  J : Ω → ℝ
  square : Ω → ℝ

theorem pinchingScalarFields_ext {Ω : Type*} (F G : PinchingScalarFields Ω)
    (hW : F.W = G.W) (h4 : F.L4 = G.L4) (h3 : F.L3 = G.L3)
    (hJ : F.J = G.J) (hs : F.square = G.square) : F = G := by
  cases F
  cases G
  simp_all

def pinchingScalarsContinuous {Ω : Type*} [TopologicalSpace Ω]
    (F : PinchingScalarFields Ω) : Prop :=
  Continuous F.W ∧ Continuous F.L4 ∧ Continuous F.L3 ∧
    Continuous F.J ∧ Continuous F.square

def pinchingScalarsIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) : Prop :=
  Integrable F.W ν ∧ Integrable F.L4 ν ∧ Integrable F.L3 ν ∧
    Integrable F.J ν ∧ Integrable F.square ν

/-- Each global scalar equals its actual component formula on every chart.
The fourth-order input V is the reduced, trace-free Hessian, not raw D. -/
def pinchingScalarsRepresent {Ω ι : Type*} (F : PinchingScalarFields Ω)
    (U : ι → Set Ω) (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4)
    (V : ι → Ω → Fourth4) (t : ℝ) : Prop :=
  ∀ i x, x ∈ U i →
    F.W x = intrinsicPinchingW (A i x) (τ i x) t ∧
    F.L4 x = intrinsicCorrectionL4 (A i x) (τ i x) t ∧
    F.L3 x = intrinsicCorrectionL3 (A i x) (τ i x) t ∧
    F.J x = intrinsicCorrectionJ (A i x) (τ i x) t ∧
    F.square x = intrinsicPinchingSquare (A i x) (τ i x) t (V i x)

theorem pinchingScalars_unique {Ω ι : Type*} (F G : PinchingScalarFields Ω)
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hF : pinchingScalarsRepresent F U A τ V t)
    (hG : pinchingScalarsRepresent G U A τ V t) : F = G := by
  apply pinchingScalarFields_ext
  all_goals
    funext x
    obtain ⟨i,hi⟩ := hcover x
    obtain ⟨hW,h4,h3,hJ,hs⟩ := hF i x hi
    obtain ⟨gW,g4,g3,gJ,gs⟩ := hG i x hi
    simp_all

/-- All five overlap identities use the same orthogonal matrix and the same
normal sign. In the negative branch V changes sign together with A and tau. -/
theorem intrinsicIntegrands_signed_overlap
    (A A' : Matrix4) (τ τ' : Cubic4) (V V' : Fourth4) (t : ℝ)
    (had : PaperAdmissible A τ)
    (htrans : ∃ O : Matrix4, OrthogonalFrame O ∧
      ((A' = frameMatrix O A ∧ τ' = frameCubic O τ ∧ V' = frameFourth O V) ∨
       (A' = -frameMatrix O A ∧ τ' = -frameCubic O τ ∧ V' = -frameFourth O V))) :
    intrinsicPinchingW A τ t = intrinsicPinchingW A' τ' t ∧
    intrinsicCorrectionL4 A τ t = intrinsicCorrectionL4 A' τ' t ∧
    intrinsicCorrectionL3 A τ t = intrinsicCorrectionL3 A' τ' t ∧
    intrinsicCorrectionJ A τ t = intrinsicCorrectionJ A' τ' t ∧
    intrinsicPinchingSquare A τ t V = intrinsicPinchingSquare A' τ' t V' := by
  obtain ⟨O,hO,ho⟩ := htrans
  rcases ho with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨(frame_intrinsicPinchingW O hO A τ had.2.1 t).symm,
      (frame_intrinsicCorrectionL4 O hO A τ t).symm,
      (frame_intrinsicCorrectionL3 O hO A τ t).symm,
      (frame_intrinsicCorrectionJ O hO A τ t).symm,
      (frame_intrinsicPinchingSquare O hO A τ had t V).symm⟩
  · obtain ⟨h4,h3,hJ⟩ := intrinsicCorrections_normal_reversal
      (frameMatrix O A) (frameCubic O τ) t
    rw [intrinsicPinchingW_normal_reversal, h4, h3, hJ,
      intrinsicPinchingSquare_normal_reversal]
    exact ⟨(frame_intrinsicPinchingW O hO A τ had.2.1 t).symm,
      (frame_intrinsicCorrectionL4 O hO A τ t).symm,
      (frame_intrinsicCorrectionL3 O hO A τ t).symm,
      (frame_intrinsicCorrectionJ O hO A τ t).symm,
      (frame_intrinsicPinchingSquare O hO A τ had t V).symm⟩

theorem continuousOn_intrinsicIntegrands {Ω : Type*} [TopologicalSpace Ω]
    (U : Set Ω) (A : Ω → Matrix4) (τ : Ω → Cubic4) (V : Ω → Fourth4) (t : ℝ)
    (hA : ContinuousOn A U) (hτ : ContinuousOn τ U) (hV : ContinuousOn V U) :
    ContinuousOn (fun x =>
      (intrinsicPinchingW (A x) (τ x) t,
       intrinsicCorrectionL4 (A x) (τ x) t,
       intrinsicCorrectionL3 (A x) (τ x) t,
       intrinsicCorrectionJ (A x) (τ x) t,
       intrinsicPinchingSquare (A x) (τ x) t (V x))) U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_intrinsicIntegrands (continuousOn_iff_continuous_domRestrict.mp hA)
    (continuousOn_iff_continuous_domRestrict.mp hτ) continuous_const
    (continuousOn_iff_continuous_domRestrict.mp hV)

/-- Local components on an open cover determine all five continuous global
scalars uniquely. No global component field or principal-frame selection is used. -/
theorem pinchingScalars_glue {Ω ι : Type*} [TopologicalSpace Ω]
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hA : ∀ i, ContinuousOn (A i) (U i)) (hτ : ∀ i, ContinuousOn (τ i) (U i))
    (hV : ∀ i, ContinuousOn (V i) (U i))
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (htrans : ∀ i j x, x ∈ U i → x ∈ U j → ∃ O : Matrix4, OrthogonalFrame O ∧
      ((A j x = frameMatrix O (A i x) ∧ τ j x = frameCubic O (τ i x) ∧
          V j x = frameFourth O (V i x)) ∨
       (A j x = -frameMatrix O (A i x) ∧ τ j x = -frameCubic O (τ i x) ∧
          V j x = -frameFourth O (V i x)))) :
    ∃! F : PinchingScalarFields Ω,
      pinchingScalarsContinuous F ∧ pinchingScalarsRepresent F U A τ V t := by
  have hc i := continuousOn_intrinsicIntegrands (U i) (A i) (τ i) (V i) t
    (hA i) (hτ i) (hV i)
  have he i j x hi hj := intrinsicIntegrands_signed_overlap
    (A i x) (A j x) (τ i x) (τ j x) (V i x) (V j x) t (had i x hi) (htrans i j x hi hj)
  obtain ⟨W,hW,_⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => intrinsicPinchingW (A i x) (τ i x) t)
    (fun i => (hc i).fst) (fun i j x hi hj => (he i j x hi hj).1)
  obtain ⟨L4,h4,_⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => intrinsicCorrectionL4 (A i x) (τ i x) t)
    (fun i => (hc i).snd.fst) (fun i j x hi hj => (he i j x hi hj).2.1)
  obtain ⟨L3,h3,_⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => intrinsicCorrectionL3 (A i x) (τ i x) t)
    (fun i => (hc i).snd.snd.fst) (fun i j x hi hj => (he i j x hi hj).2.2.1)
  obtain ⟨J,hJ,_⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => intrinsicCorrectionJ (A i x) (τ i x) t)
    (fun i => (hc i).snd.snd.snd.fst) (fun i j x hi hj => (he i j x hi hj).2.2.2.1)
  obtain ⟨sq,hs,_⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => intrinsicPinchingSquare (A i x) (τ i x) t (V i x))
    (fun i => (hc i).snd.snd.snd.snd) (fun i j x hi hj => (he i j x hi hj).2.2.2.2)
  let F : PinchingScalarFields Ω := ⟨W,L4,L3,J,sq⟩
  have hr : pinchingScalarsRepresent F U A τ V t := fun i x hi =>
    ⟨hW.2 i x hi,h4.2 i x hi,h3.2 i x hi,hJ.2 i x hi,hs.2 i x hi⟩
  refine ⟨F,⟨⟨hW.1,h4.1,h3.1,hJ.1,hs.1⟩,hr⟩,?_⟩
  intro G hG
  exact pinchingScalars_unique G F U hcover A τ V t hG.2 hr

theorem pinchingScalars_integrable_of_continuous {Ω : Type*} [TopologicalSpace Ω]
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) [IsFiniteMeasure ν]
    (hc : pinchingScalarsContinuous F) : pinchingScalarsIntegrable F ν := by
  exact ⟨hc.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    hc.2.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    hc.2.2.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    hc.2.2.2.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    hc.2.2.2.2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)⟩

/-- Compactness and finite measure discharge all five integrability obligations
for the same locally represented fields. -/
theorem pinchingScalars_glue_integrable {Ω ι : Type*} [TopologicalSpace Ω]
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hA : ∀ i, ContinuousOn (A i) (U i)) (hτ : ∀ i, ContinuousOn (τ i) (U i))
    (hV : ∀ i, ContinuousOn (V i) (U i))
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (htrans : ∀ i j x, x ∈ U i → x ∈ U j → ∃ O : Matrix4, OrthogonalFrame O ∧
      ((A j x = frameMatrix O (A i x) ∧ τ j x = frameCubic O (τ i x) ∧
          V j x = frameFourth O (V i x)) ∨
       (A j x = -frameMatrix O (A i x) ∧ τ j x = -frameCubic O (τ i x) ∧
          V j x = -frameFourth O (V i x)))) :
    ∃! F : PinchingScalarFields Ω, pinchingScalarsContinuous F ∧
      pinchingScalarsIntegrable F ν ∧ pinchingScalarsRepresent F U A τ V t := by
  obtain ⟨F,hF,hu⟩ := pinchingScalars_glue U hU hcover A τ V t hA hτ hV had htrans
  exact ⟨F,⟨hF.1,pinchingScalars_integrable_of_continuous F ν hF.1,hF.2⟩,
    fun G hG => hu G ⟨hG.1,hG.2.2⟩⟩

end
end SecondPinching
