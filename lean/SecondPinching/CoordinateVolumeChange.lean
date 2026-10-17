import SecondPinching.GlobalImmersionAtlas
import SecondPinching.VolumeDensityReparametrization

set_option autoImplicit false
open scoped Matrix Topology ContDiff Manifold
namespace SecondPinching
noncomputable section

theorem coordinateJacobian_eq_transpose_toMatrix (φ : Chart4 → Chart4) (x : Chart4) :
    coordinateJacobian φ x=(LinearMap.toMatrix' (fderiv ℝ φ x).toLinearMap)ᵀ := by
  ext i j
  simp only [coordinateJacobian,Matrix.transpose_apply,LinearMap.toMatrix'_apply,coordinateUnit]
  rfl

/-- The row-Jacobian convention has the same determinant as the intrinsic
linear map used in the Euclidean change-of-variables theorem. -/
theorem coordinateJacobian_det (φ : Chart4 → Chart4) (x : Chart4) :
    (coordinateJacobian φ x).det=LinearMap.det (fderiv ℝ φ x).toLinearMap := by
  rw [coordinateJacobian_eq_transpose_toMatrix,Matrix.det_transpose,LinearMap.det_toMatrix']

theorem immersionVolumeDensity_coordinate_germ (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain)
    (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    immersionVolumeDensity G x=|(coordinateJacobian P.map x).det| * immersionVolumeDensity F (P.map x) := by
  have ht := (immersionTangent_congr_germ _ _ x hf).self_of_nhds
  have he : immersionVolumeDensity G x=immersionVolumeDensity (reparametrizedImmersion F P) x := by
    unfold immersionVolumeDensity immersionMetric
    rw [ht]
    rfl
  exact he.trans (immersionVolumeDensity_reparametrized F P x hx)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem globalImmersion_volume_density_transition (F : GlobalSphereImmersion M) (p q : M)
    (x : Chart4) (hx : x ∈ (globalImmersionReparametrization F p q).domain) :
    immersionVolumeDensity (globalImmersionLocal F q) x =
      |LinearMap.det (fderiv ℝ (globalImmersionReparametrization F p q).map x).toLinearMap| *
        immersionVolumeDensity (globalImmersionLocal F p) ((globalImmersionReparametrization F p q).map x) := by
  rw [immersionVolumeDensity_coordinate_germ _ _ _ x hx
    (globalImmersionReparametrization_germ F p q x hx),coordinateJacobian_det]

end
end SecondPinching
