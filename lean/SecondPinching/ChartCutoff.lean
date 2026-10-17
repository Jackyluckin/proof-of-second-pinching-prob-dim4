import SecondPinching.GlobalImmersionPartition

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]

/-- Pull back a scalar to chart coordinates and extend it by zero outside
the chart target. Compact support strictly within the source ensures smoothness. -/
def chartCutoff (p : M) (u : M → ℝ) (x : Chart4) : ℝ := by
  classical
  exact if x ∈ (chartAt Chart4 p).target then u ((chartAt Chart4 p).symm x) else 0

theorem chartCutoff_on_target (p : M) (u : M → ℝ) (x : Chart4)
    (hx : x ∈ (chartAt Chart4 p).target) : chartCutoff p u x=u ((chartAt Chart4 p).symm x) := by
  simp only [chartCutoff,ite_eq_left hx]

theorem chartCutoff_on_source (p : M) (u : M → ℝ) (x : M)
    (hx : x ∈ (chartAt Chart4 p).source) : chartCutoff p u (chartAt Chart4 p x)=u x := by
  rw [chartCutoff_on_target p u _ ((chartAt Chart4 p).map_source hx),
    (chartAt Chart4 p).left_inv hx]

theorem tsupport_chartCutoff_subset (p : M) (u : M → ℝ) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ (chartAt Chart4 p).source) :
    tsupport (chartCutoff p u) ⊆ (chartAt Chart4 p) '' tsupport u := by
  have hk := hc.isCompact.image_of_continuousOn ((chartAt Chart4 p).continuousOn.mono hs)
  apply closure_minimal _ hk.isClosed
  intro x hx
  by_cases ht : x ∈ (chartAt Chart4 p).target
  · have hn : u ((chartAt Chart4 p).symm x) ≠ 0 := by
      simpa only [Function.mem_support,chartCutoff,ite_eq_left ht] using hx
    exact ⟨(chartAt Chart4 p).symm x,subset_closure hn,(chartAt Chart4 p).right_inv ht⟩
  · exact False.elim (hx (by simp only [chartCutoff,ite_eq_right ht]))

theorem hasCompactSupport_chartCutoff (p : M) (u : M → ℝ) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ (chartAt Chart4 p).source) : HasCompactSupport (chartCutoff p u) :=
  (hc.isCompact.image_of_continuousOn ((chartAt Chart4 p).continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_chartCutoff_subset p u hc hs)

variable [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem contDiff_chartCutoff (p : M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ (chartAt Chart4 p).source) : ContDiff ℝ ∞ (chartCutoff p u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ (chartAt Chart4 p).target
  · have hd := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℝ,Chart4)) (n:=∞) p) hx
    have hu' := (hu.contMDiffAt.comp x hd).contDiffAt
    apply hu'.congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem ((chartAt Chart4 p).open_target.mem_nhds hx)
      (fun y hy => chartCutoff_on_target p u y hy)
  · have hn : x ∉ tsupport (chartCutoff p u) := by
      intro h
      obtain ⟨y,hy,he⟩ := tsupport_chartCutoff_subset p u hc hs h
      exact hx (he ▸ (chartAt Chart4 p).map_source (hs hy))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

def globalImmersionPartitionCutoff (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) : Chart4 → ℝ := chartCutoff (P.center i) (P.weights i)

theorem globalImmersionPartitionCutoff_support [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    tsupport (globalImmersionPartitionCutoff F P i) ⊆ (globalImmersionLocal F (P.center i)).domain := by
  have hs := P.subordinate i
  have hc := HasCompactSupport.of_compactSpace (P.weights i : M → ℝ)
  intro x hx
  obtain ⟨y,hy,he⟩ := tsupport_chartCutoff_subset (P.center i) (P.weights i) hc
    (fun y hy => (hs hy).1) hx
  exact he ▸ (hs hy).2

theorem globalImmersionPartitionCutoff_smooth [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    ContDiff ℝ ∞ (globalImmersionPartitionCutoff F P i) :=
  contDiff_chartCutoff (P.center i) (P.weights i) (P.weights i).contMDiff
    (HasCompactSupport.of_compactSpace _) (fun _ hy => (P.subordinate i hy).1)

theorem globalImmersionPartitionCutoff_compact [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    HasCompactSupport (globalImmersionPartitionCutoff F P i) :=
  hasCompactSupport_chartCutoff (P.center i) (P.weights i)
    (HasCompactSupport.of_compactSpace _) (fun _ hy => (P.subordinate i hy).1)

end
end SecondPinching
