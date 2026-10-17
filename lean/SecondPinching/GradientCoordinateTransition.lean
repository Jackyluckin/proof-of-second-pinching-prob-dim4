import SecondPinching.VectorCoordinateAlgebra

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem immersionGradient_coordinate_components (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F) (e' : LocalImmersionFrame G)
    (u v : Chart4 → ℝ) (x : Chart4) (hxP : x ∈ P.domain) (hxG : x ∈ G.domain)
    (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) (hu : DifferentiableAt ℝ u (P.map x))
    (hg : v =ᶠ[𝓝 x] u ∘ P.map) :
    (e.coefficients (P.map x))ᵀ *ᵥ immersionScalarGradient F e u (P.map x) =
      fderiv ℝ P.map x ((e'.coefficients x)ᵀ *ᵥ immersionScalarGradient G e' v x) := by
  obtain ⟨Q,hQ,hB⟩ := immersion_coordinate_frame_transition F G P e e' x hxP hxG hf
  have hP := ((P.smooth_map x hxP).contDiffAt (P.isOpen_domain.mem_nhds hxP)).differentiableAt (by simp)
  rw [scalar_gradient_frame_transition F G P e e' u v x hu hP hg Q hB,fderiv_eq_coordinateJacobian_mulVec]
  exact vector_frame_to_coordinate_transition _ _ _ Q hQ hB _

end
end SecondPinching
