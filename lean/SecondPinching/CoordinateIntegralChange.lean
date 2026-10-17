import SecondPinching.CoordinateVolumeChange
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section

/-- The density transformation and the Euclidean change-of-variables theorem
give the same weighted integral on every measurable subset of a chart overlap.
Injectivity on the set is required here, unlike the pointwise density law. -/
theorem integral_reparametrized_density (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (s : Set Chart4) (hs : MeasurableSet s)
    (hsP : s ⊆ P.domain) (hinj : Set.InjOn P.map s) (g : Chart4 → ℝ) :
    (∫ y in P.map '' s, immersionVolumeDensity F y * g y) =
      ∫ x in s, immersionVolumeDensity (reparametrizedImmersion F P) x * g (P.map x) := by
  have hd (x : Chart4) (hx : x ∈ s) : HasFDerivWithinAt P.map (fderiv ℝ P.map x) s x :=
    (((P.smooth_map x (hsP hx)).contDiffAt (P.isOpen_domain.mem_nhds (hsP hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hd hinj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [immersionVolumeDensity_reparametrized F P x (hsP hx),coordinateJacobian_det]
  change |LinearMap.det (fderiv ℝ P.map x).toLinearMap| *
      (immersionVolumeDensity F (P.map x) * g (P.map x)) =
    (|LinearMap.det (fderiv ℝ P.map x).toLinearMap| * immersionVolumeDensity F (P.map x)) * g (P.map x)
  ring

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem globalImmersionReparametrization_injOn (F : GlobalSphereImmersion M) (p q : M) :
    Set.InjOn (globalImmersionReparametrization F p q).map (globalImmersionReparametrization F p q).domain :=
  (globalChartTransition p q).injOn.mono (fun _ hx => hx.1)

theorem integral_globalImmersion_density_transition (F : GlobalSphereImmersion M) (p q : M)
    (s : Set Chart4) (hs : MeasurableSet s) (hsP : s ⊆ (globalImmersionReparametrization F p q).domain)
    (g : Chart4 → ℝ) :
    (∫ y in (globalImmersionReparametrization F p q).map '' s,
      immersionVolumeDensity (globalImmersionLocal F p) y * g y) =
      ∫ x in s, immersionVolumeDensity (globalImmersionLocal F q) x *
        g ((globalImmersionReparametrization F p q).map x) := by
  rw [integral_reparametrized_density _ _ s hs hsP
    ((globalImmersionReparametrization_injOn F p q).mono hsP)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [immersionVolumeDensity_reparametrized _ _ x (hsP hx),coordinateJacobian_det,
    globalImmersion_volume_density_transition F p q x (hsP hx)]

end
end SecondPinching
