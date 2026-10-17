import SecondPinching.ImmersionDivergences

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem frame_cubicTraceFlux (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) (T : Cubic4) :
    frameMatrix Q A*ᵥintrinsicCubicD (frameMatrix Q A) (frameCubic Q T) =
      frameVector Q (A*ᵥintrinsicCubicD A T) := by
  rw [frame_intrinsicCubicD Q hQ,frameMatrix_mulVec Q hQ]

theorem cubicTraceFlux_normal_reversal (A : Matrix4) (T : Cubic4) :
    (-A)*ᵥintrinsicCubicD (-A) (-T) = A*ᵥintrinsicCubicD A T := by
  rw [intrinsicCubicD_normal_reversal,Matrix.neg_mulVec_neg]

/-- Both scalar potentials and the flux have the parity needed on a
nonorientable hypersurface. This statement does not construct a global bundle. -/
theorem divergence_sources_signed_frame (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A A' : Matrix4) (T T' : Cubic4) (S : ℝ)
    (ht : (A'=frameMatrix Q A ∧ T'=frameCubic Q T) ∨
      (A'=-frameMatrix Q A ∧ T'=-frameCubic Q T)) :
    (S/4)*quarticMoment A'=(S/4)*quarticMoment A ∧
    (1/6 : ℝ)*(cubicMoment A')^2=(1/6 : ℝ)*(cubicMoment A)^2 ∧
    A'*ᵥintrinsicCubicD A' T'=frameVector Q (A*ᵥintrinsicCubicD A T) := by
  rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [frame_quarticMoment Q hQ,frame_cubicMoment Q hQ,frame_cubicTraceFlux Q hQ]
    exact ⟨rfl,rfl,rfl⟩
  · rw [quarticMoment_neg,cubicMoment_neg,neg_sq,cubicTraceFlux_normal_reversal,
      frame_quarticMoment Q hQ,frame_cubicMoment Q hQ,frame_cubicTraceFlux Q hQ]
    exact ⟨rfl,rfl,rfl⟩

theorem contDiffOn_immersionQuarticPotential (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (S : ℝ) :
    ContDiffOn ℝ ∞ (immersionQuarticPotential F e S) F.domain :=
  contDiffOn_const.mul (contDiffOn_immersionQuarticTrace F e)

theorem contDiffOn_immersionCubicPotential (F : LocalSphereImmersion) (e : LocalImmersionFrame F) :
    ContDiffOn ℝ ∞ (immersionCubicPotential F e) F.domain :=
  contDiffOn_const.mul ((contDiffOn_immersionCubicTrace F e).pow 2)

/-- Continuous scalar potentials descend from the actual signed tensor
transitions. Smooth global atlas realization and Stokes remain separate. -/
theorem immersionPotentials_glue {Ω ι : Type*} [TopologicalSpace Ω]
    (F : ι → LocalSphereImmersion) (e : ∀ i, LocalImmersionFrame (F i))
    (chart : ι → Ω → Chart4) (S : ℝ)
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hchart : ∀ i, ContinuousOn (chart i) (U i))
    (hmaps : ∀ i x, x ∈ U i → chart i x ∈ (F i).domain)
    (hcoordinates : ImmersionCoordinateOverlaps F chart U) :
    ∃! P : (Ω → ℝ) × (Ω → ℝ), Continuous P.1 ∧ Continuous P.2 ∧
      ∀ i x, x ∈ U i →
        P.1 x=immersionQuarticPotential (F i) (e i) S (chart i x) ∧
        P.2 x=immersionCubicPotential (F i) (e i) (chart i x) := by
  have hc4 i := (contDiffOn_immersionQuarticPotential (F i) (e i) S).continuousOn.comp (hchart i) (hmaps i)
  have hc3 i := (contDiffOn_immersionCubicPotential (F i) (e i)).continuousOn.comp (hchart i) (hmaps i)
  have he (i j : ι) (x : Ω) (hi : x ∈ U i) (hj : x ∈ U j) :
      immersionQuarticPotential (F i) (e i) S (chart i x)=immersionQuarticPotential (F j) (e j) S (chart j x) ∧
      immersionCubicPotential (F i) (e i) (chart i x)=immersionCubicPotential (F j) (e j) (chart j x) := by
    obtain ⟨Q,hQ,ht⟩ := immersionAtlas_raw_transitions F e chart U hmaps hcoordinates i j x hi hj
    have hs :
        (immersionFrameSecond (F j) (e j) (chart j x)=frameMatrix Q (immersionFrameSecond (F i) (e i) (chart i x)) ∧
         immersionFrameThird (F j) (e j) (chart j x)=frameCubic Q (immersionFrameThird (F i) (e i) (chart i x))) ∨
        (immersionFrameSecond (F j) (e j) (chart j x)=-frameMatrix Q (immersionFrameSecond (F i) (e i) (chart i x)) ∧
         immersionFrameThird (F j) (e j) (chart j x)=-frameCubic Q (immersionFrameThird (F i) (e i) (chart i x))) := by
      rcases ht with h|h
      · exact Or.inl ⟨h.1,h.2.1⟩
      · exact Or.inr ⟨h.1,h.2.1⟩
    have hd := divergence_sources_signed_frame Q hQ _ _ _ _ S hs
    exact ⟨hd.1.symm,hd.2.1.symm⟩
  obtain ⟨P4,h4,u4⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => immersionQuarticPotential (F i) (e i) S (chart i x)) hc4
    (fun i j x hi hj => (he i j x hi hj).1)
  obtain ⟨P3,h3,u3⟩ := existsUnique_continuous_scalar_of_cover U hU hcover
    (fun i x => immersionCubicPotential (F i) (e i) (chart i x)) hc3
    (fun i j x hi hj => (he i j x hi hj).2)
  refine ⟨(P4,P3),⟨h4.1,h3.1,fun i x hx => ⟨h4.2 i x hx,h3.2 i x hx⟩⟩,?_⟩
  intro P hP
  exact Prod.ext (u4 P.1 ⟨hP.1,fun i x hx => (hP.2.2 i x hx).1⟩)
    (u3 P.2 ⟨hP.2.1,fun i x hx => (hP.2.2 i x hx).2⟩)

end
end SecondPinching
