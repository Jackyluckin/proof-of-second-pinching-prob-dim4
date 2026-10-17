import SecondPinching.CoordinateCutoffIntegration
import SecondPinching.ImmersionCoordinateVector
import SecondPinching.InducedVolume

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

theorem inverse_coordinate_mem_localSource (F : GlobalSphereImmersion M) (p : M) (x : Chart4)
    (hx : x ∈ (globalImmersionLocal F p).domain) :
    (chartAt Chart4 p).symm x ∈ globalImmersionLocalSource F p ∧
      chartAt Chart4 p ((chartAt Chart4 p).symm x)=x := by
  have ht := globalImmersionLocal_domain_subset F p hx
  have he := (chartAt Chart4 p).right_inv ht
  refine ⟨⟨(chartAt Chart4 p).map_target ht,?_⟩,he⟩
  change chartAt Chart4 p ((chartAt Chart4 p).symm x) ∈ (globalImmersionLocal F p).domain
  rwa [he]

variable [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
theorem chartCutoff_globalVectorAction_partition (F : GlobalSphereImmersion M)
    (Y : ImmersionCoordinateVector F) (P : ImmersionPartition F) (i : P.index) (x : Chart4) :
    chartCutoff (P.center i) (globalVectorAction F Y (P.weights i)) x =
      fderiv ℝ (globalImmersionPartitionCutoff F P i) x (Y.components (P.center i) x) := by
  by_cases hx : x ∈ (globalImmersionLocal F (P.center i)).domain
  · have ht := globalImmersionLocal_domain_subset F (P.center i) hx
    obtain ⟨hy,he⟩ := inverse_coordinate_mem_localSource F (P.center i) x hx
    have hg : globalImmersionPartitionCutoff F P i =ᶠ[𝓝 x]
        scalarInImmersionChart (P.center i) (P.weights i) :=
      Filter.eventuallyEq_of_mem ((chartAt Chart4 (P.center i)).open_target.mem_nhds ht)
        (fun y hy => chartCutoff_on_target _ _ y hy)
    calc
      _ = globalVectorAction F Y (P.weights i) ((chartAt Chart4 (P.center i)).symm x) :=
        chartCutoff_on_target _ _ x ht
      _ = fderiv ℝ (scalarInImmersionChart (P.center i) (P.weights i))
          (chartAt Chart4 (P.center i) ((chartAt Chart4 (P.center i)).symm x))
          (Y.components (P.center i) (chartAt Chart4 (P.center i) ((chartAt Chart4 (P.center i)).symm x))) :=
        globalVectorAction_represent F Y _ (P.weights i).contMDiff _ _ hy
      _ = fderiv ℝ (scalarInImmersionChart (P.center i) (P.weights i)) x (Y.components (P.center i) x) := by rw [he]
      _ = _ := (congrArg (fun L : Chart4 →L[ℝ] ℝ => L (Y.components (P.center i) x)) hg.fderiv_eq).symm
  · have hn : x ∉ tsupport (globalImmersionPartitionCutoff F P i) :=
      fun h => hx (globalImmersionPartitionCutoff_support F P i h)
    have hz : chartCutoff (P.center i) (globalVectorAction F Y (P.weights i)) x=0 := by
      by_contra h
      obtain ⟨y,hy,_,he⟩ := chartCutoff_nonzero_points _ _ x h
      have hs := P.subordinate i (tsupport_globalVectorAction_subset F Y _ (subset_closure hy))
      exact hx (he ▸ hs.2)
    rw [hz,fderiv_of_notMem_tsupport ℝ hn]
    rfl

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
theorem partition_divergence_density_represent (F : GlobalSphereImmersion M)
    (Y : ImmersionCoordinateVector F) (D : M → ℝ)
    (hD : ∀ p y, y ∈ globalImmersionLocalSource F p →
      D y=immersionCoordinateDivergence (globalImmersionLocal F p) (Y.components p) (chartAt Chart4 p y))
    (P : ImmersionPartition F) (i : P.index) (x : Chart4) :
    partitionVolumeDensity F P i x * D ((chartAt Chart4 (P.center i)).symm x) =
      globalImmersionPartitionCutoff F P i x * (immersionVolumeDensity (globalImmersionLocal F (P.center i)) x *
        immersionCoordinateDivergence (globalImmersionLocal F (P.center i)) (Y.components (P.center i)) x) := by
  by_cases hx : x ∈ (globalImmersionLocal F (P.center i)).domain
  · obtain ⟨hy,he⟩ := inverse_coordinate_mem_localSource F (P.center i) x hx
    rw [hD _ _ hy,he]
    unfold partitionVolumeDensity
    ring
  · have hn : x ∉ tsupport (globalImmersionPartitionCutoff F P i) :=
      fun h => hx (globalImmersionPartitionCutoff_support F P i h)
    simp only [partitionVolumeDensity,image_eq_zero_of_notMem_tsupport hn,zero_mul]

theorem global_divergence_cutoff_balance (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (D : M → ℝ) (hcont : Continuous D)
    (hD : ∀ p y, y ∈ globalImmersionLocalSource F p →
      D y=immersionCoordinateDivergence (globalImmersionLocal F p) (Y.components p) (chartAt Chart4 p y))
    (P : ImmersionPartition F) (i : P.index) :
    (∫ y, D y ∂partitionChartMeasure F P i) +
      (∫ y, globalVectorAction F Y (P.weights i) y ∂inducedVolume F)=0 := by
  have hlocal := coordinate_cutoff_integrals (globalImmersionLocal F (P.center i))
    (globalImmersionPartitionCutoff F P i) (Y.components (P.center i))
    (globalImmersionPartitionCutoff_smooth F P i) (Y.smooth (P.center i))
    (globalImmersionPartitionCutoff_compact F P i) (globalImmersionPartitionCutoff_support F P i)
  have ha : (∫ y, D y ∂partitionChartMeasure F P i) =
      ∫ x : Chart4, globalImmersionPartitionCutoff F P i x *
        (immersionVolumeDensity (globalImmersionLocal F (P.center i)) x *
          immersionCoordinateDivergence (globalImmersionLocal F (P.center i)) (Y.components (P.center i)) x) := by
    rw [integral_partitionChartMeasure F P i D hcont]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (partition_divergence_density_represent F Y D hD P i)
  have hb : (∫ y, globalVectorAction F Y (P.weights i) y ∂inducedVolume F) =
      ∫ x : Chart4, immersionVolumeDensity (globalImmersionLocal F (P.center i)) x *
        fderiv ℝ (globalImmersionPartitionCutoff F P i) x (Y.components (P.center i) x) := by
    rw [integral_inducedVolume_local F (P.center i) _
      (contMDiff_globalVectorAction F Y _ (P.weights i).contMDiff).continuous
      ((tsupport_globalVectorAction_subset F Y _).trans (P.subordinate i))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    exact congrArg (fun z : ℝ => immersionVolumeDensity (globalImmersionLocal F (P.center i)) x*z)
      (chartCutoff_globalVectorAction_partition F Y P i x)
  rw [ha,hb]
  exact hlocal.2.2

/-- Stokes for the constructed induced-volume measure on a closed manifold.
The local divergence representation and the vector transition law are the
definitions of the represented divergence and tangent field; no zero integral
is an input. -/
theorem integral_global_divergence_eq_zero (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (D : M → ℝ) (hcont : Continuous D)
    (hD : ∀ p y, y ∈ globalImmersionLocalSource F p →
      D y=immersionCoordinateDivergence (globalImmersionLocal F p) (Y.components p) (chartAt Chart4 p y)) :
    (∫ y, D y ∂inducedVolume F)=0 := by
  let P := constructedImmersionPartition F
  let _ := P.finite_index
  have := isFiniteMeasure_inducedVolume F
  have hsum : (∑ i, ∫ y, D y ∂partitionChartMeasure F P i) +
      (∑ i, ∫ y, globalVectorAction F Y (P.weights i) y ∂inducedVolume F)=0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun i _ => global_divergence_cutoff_balance F Y D hcont hD P i)
  have ha : (∫ y, D y ∂inducedVolume F)=∑ i, ∫ y, D y ∂partitionChartMeasure F P i := by
    change (∫ y, D y ∂partitionVolumeMeasure F P)=_
    unfold partitionVolumeMeasure
    exact integral_finsetSum_measure (fun i _ => integrable_partitionChartMeasure F P i D hcont)
  have hb : (∑ i, ∫ y, globalVectorAction F Y (P.weights i) y ∂inducedVolume F)=0 := by
    have hi (i : P.index) : Integrable (globalVectorAction F Y (P.weights i)) (inducedVolume F) :=
      (contMDiff_globalVectorAction F Y _ (P.weights i).contMDiff).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
    have hz : (fun y => ∑ i, globalVectorAction F Y (P.weights i) y)=(fun _ => (0 : ℝ)) := by
      funext y
      exact globalVectorAction_partition_sum F Y P y
    rw [hz,integral_zero]
  rw [← ha,hb,add_zero] at hsum
  exact hsum

theorem integral_normalized_global_divergence_eq_zero (F : GlobalSphereImmersion M)
    (Y : ImmersionCoordinateVector F) (D : M → ℝ) (hcont : Continuous D)
    (hD : ∀ p y, y ∈ globalImmersionLocalSource F p →
      D y=immersionCoordinateDivergence (globalImmersionLocal F p) (Y.components p) (chartAt Chart4 p y)) :
    (∫ y, D y ∂normalizedInducedVolume F)=0 := by
  rw [integral_normalizedInducedVolume,integral_global_divergence_eq_zero F Y D hcont hD,mul_zero]

end
end SecondPinching
