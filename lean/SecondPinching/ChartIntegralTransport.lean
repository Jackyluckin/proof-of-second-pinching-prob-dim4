import SecondPinching.CoordinateIntegralChange
import SecondPinching.ChartCutoff

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]

theorem chartCutoff_nonzero_points (p : M) (g : M → ℝ) (x : Chart4)
    (hn : chartCutoff p g x ≠ 0) :
    ∃ y : M, g y ≠ 0 ∧ y ∈ (chartAt Chart4 p).source ∧ chartAt Chart4 p y=x := by
  have hx : x ∈ (chartAt Chart4 p).target := by
    by_contra h
    exact hn (by simp only [chartCutoff,ite_eq_right h])
  refine ⟨(chartAt Chart4 p).symm x,?_,(chartAt Chart4 p).map_target hx,(chartAt Chart4 p).right_inv hx⟩
  rwa [chartCutoff_on_target p g x hx] at hn

theorem chartCutoff_mul_right (p : M) (g h : M → ℝ) (x : Chart4) :
    chartCutoff p (fun y => g y*h y) x=chartCutoff p g x*h ((chartAt Chart4 p).symm x) := by
  by_cases hx : x ∈ (chartAt Chart4 p).target
  · simp only [chartCutoff,ite_eq_left hx]
  · simp only [chartCutoff,ite_eq_right hx,zero_mul]

variable [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem chartCutoff_transition (F : GlobalSphereImmersion M) (p q : M)
    (g : M → ℝ) (x : Chart4) (hx : x ∈ (globalImmersionReparametrization F p q).domain) :
    chartCutoff p g ((globalImmersionReparametrization F p q).map x)=chartCutoff q g x := by
  have hp : (globalImmersionReparametrization F p q).map x ∈ (chartAt Chart4 p).target :=
    globalImmersionLocal_domain_subset F p hx.2
  have hq : x ∈ (chartAt Chart4 q).target := hx.1.1
  rw [chartCutoff_on_target p g _ hp,chartCutoff_on_target q g x hq]
  change g ((chartAt Chart4 p).symm ((chartAt Chart4 p) ((chartAt Chart4 q).symm x))) =
    g ((chartAt Chart4 q).symm x)
  exact congrArg g ((chartAt Chart4 p).left_inv hx.1.2)

theorem chartCutoff_zero_off_transition_domain (F : GlobalSphereImmersion M) (p q : M)
    (g : M → ℝ) (hp : tsupport g ⊆ globalImmersionLocalSource F p)
    (hq : tsupport g ⊆ globalImmersionLocalSource F q) (x : Chart4)
    (hx : x ∉ (globalImmersionReparametrization F p q).domain) : chartCutoff q g x=0 := by
  by_contra hn
  obtain ⟨y,hy,_,he⟩ := chartCutoff_nonzero_points q g x hn
  have ht : y ∈ tsupport g := subset_closure hy
  have hd := (globalImmersionReparametrization_point F p q y (hp ht) (hq ht)).1
  exact hx (he ▸ hd)

theorem chartCutoff_zero_off_transition_image (F : GlobalSphereImmersion M) (p q : M)
    (g : M → ℝ) (hp : tsupport g ⊆ globalImmersionLocalSource F p)
    (hq : tsupport g ⊆ globalImmersionLocalSource F q) (x : Chart4)
    (hx : x ∉ (globalImmersionReparametrization F p q).map ''
      (globalImmersionReparametrization F p q).domain) : chartCutoff p g x=0 := by
  by_contra hn
  obtain ⟨y,hy,_,he⟩ := chartCutoff_nonzero_points p g x hn
  have ht : y ∈ tsupport g := subset_closure hy
  obtain ⟨hd,hm⟩ := globalImmersionReparametrization_point F p q y (hp ht) (hq ht)
  exact hx ⟨chartAt Chart4 q y,hd,hm.trans he⟩

/-- Coordinate integrals of a scalar supported in two local domains agree.
Only genuine chart transitions are used, so no global injectivity of the
immersion and no orientation is required. -/
theorem integral_chartCutoff_change (F : GlobalSphereImmersion M) (p q : M)
    (g : M → ℝ) (hp : tsupport g ⊆ globalImmersionLocalSource F p)
    (hq : tsupport g ⊆ globalImmersionLocalSource F q) :
    (∫ x : Chart4, immersionVolumeDensity (globalImmersionLocal F p) x * chartCutoff p g x) =
      ∫ x : Chart4, immersionVolumeDensity (globalImmersionLocal F q) x * chartCutoff q g x := by
  let P := globalImmersionReparametrization F p q
  calc
    _ = ∫ x in P.map '' P.domain,
        immersionVolumeDensity (globalImmersionLocal F p) x * chartCutoff p g x := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro x hx
      rw [chartCutoff_zero_off_transition_image F p q g hp hq x hx,mul_zero]
    _ = ∫ x in P.domain, immersionVolumeDensity (globalImmersionLocal F q) x *
        chartCutoff p g (P.map x) :=
      integral_globalImmersion_density_transition F p q P.domain P.isOpen_domain.measurableSet
        (fun _ hx => hx) (chartCutoff p g)
    _ = ∫ x in P.domain, immersionVolumeDensity (globalImmersionLocal F q) x * chartCutoff q g x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem P.isOpen_domain.measurableSet] with x hx
      rw [chartCutoff_transition F p q g x hx]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [chartCutoff_zero_off_transition_domain F p q g hp hq x hx,mul_zero]

end
end SecondPinching
