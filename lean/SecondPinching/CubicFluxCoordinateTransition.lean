import SecondPinching.VectorCoordinateAlgebra
import SecondPinching.DivergencePotentials

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Retain the actual change of tangent basis when comparing the even cubic
flux. The same normal sign occurs in h and nabla h, and cancels from h D. -/
theorem immersionCubicFlux_coordinate_components (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F) (e' : LocalImmersionFrame G)
    (x : Chart4) (hxP : x ∈ P.domain) (hxG : x ∈ G.domain)
    (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    (e.coefficients (P.map x))ᵀ *ᵥ immersionCubicFlux F e (P.map x) =
      fderiv ℝ P.map x ((e'.coefficients x)ᵀ *ᵥ immersionCubicFlux G e' x) := by
  obtain ⟨Q,hQ,hB⟩ := immersion_coordinate_frame_transition F G P e e' x hxP hxG hf
  have hflux : immersionCubicFlux G e' x=frameVector Q (immersionCubicFlux F e (P.map x)) := by
    rcases immersion_forms_reparametrization_germ F G P x hxP hxG hf with
      ⟨h2,h3,_⟩ | ⟨h2,h3,_⟩
    · have hh : immersionFrameSecond G e' x=frameMatrix Q (immersionFrameSecond F e (P.map x)) := by
        simp only [immersionFrameSecond,h2.self_of_nhds,← frameMatrix_composition,hB]
      have ht : immersionFrameThird G e' x=frameCubic Q (immersionFrameThird F e (P.map x)) := by
        simp only [immersionFrameThird,h3.self_of_nhds,← frameCubic_composition,hB]
      simp only [immersionCubicFlux,hh,ht,frame_cubicTraceFlux Q hQ]
    · have hn2 (A : Matrix4) : frameMatrix (e'.coefficients x) (-A) =
          -frameMatrix (e'.coefficients x) A := (frameMatrixLinear _).map_neg A
      have hn3 (T : Cubic4) : frameCubic (e'.coefficients x) (-T) =
          -frameCubic (e'.coefficients x) T := (frameCubicLinear _).map_neg T
      have hh : immersionFrameSecond G e' x= -frameMatrix Q (immersionFrameSecond F e (P.map x)) := by
        simp only [immersionFrameSecond,h2.self_of_nhds,hn2,← frameMatrix_composition,hB]
      have ht : immersionFrameThird G e' x= -frameCubic Q (immersionFrameThird F e (P.map x)) := by
        simp only [immersionFrameThird,h3.self_of_nhds,hn3,← frameCubic_composition,hB]
      simp only [immersionCubicFlux,hh,ht,cubicTraceFlux_normal_reversal,frame_cubicTraceFlux Q hQ]
  rw [hflux,fderiv_eq_coordinateJacobian_mulVec]
  exact vector_frame_to_coordinate_transition _ _ _ Q hQ hB _

end
end SecondPinching
