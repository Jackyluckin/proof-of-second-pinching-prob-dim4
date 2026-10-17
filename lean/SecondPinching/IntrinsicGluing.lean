import SecondPinching.IntrinsicRegularity

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- Scalar gluing on an open cover, with its compatibility hypothesis explicit. -/
theorem existsUnique_continuous_scalar_of_cover {Ω ι : Type*} [TopologicalSpace Ω]
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (f : ι → Ω → ℝ) (hf : ∀ i, ContinuousOn (f i) (U i))
    (he : ∀ i j x, x ∈ U i → x ∈ U j → f i x = f j x) :
    ∃! F : Ω → ℝ, Continuous F ∧ ∀ i x, x ∈ U i → F x = f i x := by
  classical
  let F : Ω → ℝ := fun x => f (Classical.choose (hcover x)) x
  have hF : ∀ i x, x ∈ U i → F x = f i x := by
    intro i x hx
    exact he _ i x (Classical.choose_spec (hcover x)) hx
  have hc : Continuous F := by
    apply continuous_of_cover_nhds (s := U)
    · intro x
      obtain ⟨i,hi⟩ := hcover x
      exact ⟨i,(hU i).mem_nhds hi⟩
    · intro i
      exact (hf i).congr (fun x hx => hF i x hx)
  refine ⟨F,⟨hc,hF⟩,?_⟩
  intro G hG
  funext x
  obtain ⟨i,hi⟩ := hcover x
  exact (hG.2 i x hi).trans (hF i x hi).symm

/-- A scalar W exists uniquely and is continuous and integrable when supplied
with continuous local components and their actual signed orthogonal overlap
relations. The orthogonal matrix and sign may vary pointwise. No eigenframe,
global tangent frame, global normal, or regularity of the chosen transitions is
assumed. Construction of such data from an immersion remains separate. -/
theorem intrinsicPinchingW_glue_integrable {Ω ι : Type*} [TopologicalSpace Ω]
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (t : ℝ)
    (hA : ∀ i, ContinuousOn (A i) (U i)) (hτ : ∀ i, ContinuousOn (τ i) (U i))
    (hsym : ∀ i x, x ∈ U i → CubicSymmetric (τ i x))
    (htrans : ∀ i j x, x ∈ U i → x ∈ U j → ∃ O : Matrix4, OrthogonalFrame O ∧
      ((A j x = frameMatrix O (A i x) ∧ τ j x = frameCubic O (τ i x)) ∨
       (A j x = -frameMatrix O (A i x) ∧ τ j x = -frameCubic O (τ i x)))) :
    ∃! W : Ω → ℝ, Continuous W ∧ Integrable W ν ∧
      ∀ i x, x ∈ U i → W x = intrinsicPinchingW (A i x) (τ i x) t := by
  have hc : ∀ i, ContinuousOn (fun x => intrinsicPinchingW (A i x) (τ i x) t) (U i) := by
    intro i
    have hp : ContinuousOn (fun x => (A i x, τ i x, t)) (U i) :=
      (hA i).prodMk ((hτ i).prodMk (continuousOn_const : ContinuousOn (fun _ : Ω => t) (U i)))
    have hw := continuous_intrinsicPinchingW.comp_continuousOn hp
    exact hw
  have he : ∀ i j x, x ∈ U i → x ∈ U j →
      intrinsicPinchingW (A i x) (τ i x) t = intrinsicPinchingW (A j x) (τ j x) t := by
    intro i j x hi hj
    obtain ⟨O,hO,ho⟩ := htrans i j x hi hj
    rcases ho with ⟨ha,ht⟩ | ⟨ha,ht⟩
    · rw [ha,ht,frame_intrinsicPinchingW O hO _ _ (hsym i x hi)]
    · rw [ha,ht,intrinsicPinchingW_frame_normal O hO _ _ (hsym i x hi)]
  obtain ⟨W,hW,hunique⟩ := existsUnique_continuous_scalar_of_cover U hU hcover _ hc he
  refine ⟨W,⟨hW.1,?_,hW.2⟩,?_⟩
  · exact hW.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro W' hW'
    exact hunique W' ⟨hW'.1,hW'.2.2⟩

end
end SecondPinching
