import SecondPinching.GlobalLocalDataBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- Smoothness is local in the actual chart cover, not an additional property
imposed on a glued scalar field. -/
theorem contMDiff_of_immersion_local_representation (F : GlobalSphereImmersion M)
    (u : M → ℝ) (v : M → Chart4 → ℝ)
    (hv : ∀ p, ContDiffOn ℝ ∞ (v p) (globalImmersionLocal F p).domain)
    (hr : ∀ p x, x ∈ globalImmersionLocalSource F p → u x=v p (chartAt Chart4 p x)) :
    ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u := by
  intro x
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℝ,Chart4)) (n:=∞) x) (mem_chart_source Chart4 x)
  have hd := ((hv x) _ (globalImmersionLocal_center F x)).contDiffAt
    ((globalImmersionLocal F x).isOpen_domain.mem_nhds (globalImmersionLocal_center F x))
  have hs := hd.contMDiffAt.comp x hc
  apply hs.congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem
    ((isOpen_globalImmersionLocalSource F x).mem_nhds (globalImmersionLocalSource_center F x))
    (fun y hy => hr x y hy)

/-- The two even potentials in eq:divergences are globally smooth without a
global unit normal. This statement does not invoke an integral or Stokes. -/
theorem globalImmersionPotentials_smooth (F : GlobalSphereImmersion M) (S : ℝ) :
    ∃! P : (M → ℝ) × (M → ℝ),
      ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ P.1 ∧ ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ P.2 ∧
      ∀ p x, x ∈ globalImmersionLocalSource F p →
        P.1 x=immersionQuarticPotential (globalImmersionLocal F p) (globalImmersionLocalFrame F p) S
          (chartAt Chart4 p x) ∧
        P.2 x=immersionCubicPotential (globalImmersionLocal F p) (globalImmersionLocalFrame F p)
          (chartAt Chart4 p x) := by
  obtain ⟨P,hP,hu⟩ := immersionPotentials_glue (globalImmersionLocal F) (globalImmersionLocalFrame F)
    (fun p => chartAt Chart4 p) S (globalImmersionLocalSource F)
    (isOpen_globalImmersionLocalSource F) (globalImmersionLocalSource_cover F)
    (globalImmersionLocalSource_chart_continuous F) (fun _ _ hx => hx.2)
    (globalImmersionLocal_coordinate_overlaps F)
  refine ⟨P,⟨?_,?_,hP.2.2⟩,?_⟩
  · exact contMDiff_of_immersion_local_representation F P.1
      (fun p => immersionQuarticPotential (globalImmersionLocal F p) (globalImmersionLocalFrame F p) S)
      (fun p => contDiffOn_immersionQuarticPotential _ _ S) (fun p x hx => (hP.2.2 p x hx).1)
  · exact contMDiff_of_immersion_local_representation F P.2
      (fun p => immersionCubicPotential (globalImmersionLocal F p) (globalImmersionLocalFrame F p))
      (fun p => contDiffOn_immersionCubicPotential _ _) (fun p x hx => (hP.2.2 p x hx).2)
  · intro Q hQ
    exact hu Q ⟨hQ.1.continuous,hQ.2.1.continuous,hQ.2.2⟩

end
end SecondPinching
