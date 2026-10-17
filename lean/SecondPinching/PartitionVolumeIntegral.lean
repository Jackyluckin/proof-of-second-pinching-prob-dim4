import SecondPinching.PartitionVolumeMeasure

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem integrable_partitionChartMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (g : M → ℝ) (hg : Continuous g) : Integrable g (partitionChartMeasure F P i) := by
  have := isFiniteMeasure_partitionChartMeasure F P i
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

theorem integral_partitionChartMeasure_of_aestronglyMeasurable
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (g : M → ℝ) (hg : AEStronglyMeasurable g (partitionChartMeasure F P i)) :
    (∫ y : M, g y ∂partitionChartMeasure F P i) =
      ∫ x : Chart4, partitionVolumeDensity F P i x * g ((chartAt Chart4 (P.center i)).symm x) := by
  unfold partitionChartMeasure
  rw [integral_map (measurable_totalChartInverse _).aemeasurable hg,
    integral_withDensity_eq_integral_toReal_smul
      (contDiff_partitionVolumeDensity F P i).continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (ENNReal.ofReal (partitionVolumeDensity F P i x)).toReal *
    g (totalChartInverse (P.center i) x) =
    partitionVolumeDensity F P i x * g ((chartAt Chart4 (P.center i)).symm x)
  rw [ENNReal.toReal_ofReal (partitionVolumeDensity_nonneg F P i x)]
  by_cases hx : x ∈ (chartAt Chart4 (P.center i)).target
  · rw [totalChartInverse_on_target _ _ hx]
  · have hz : partitionVolumeDensity F P i x=0 := by
      simp only [partitionVolumeDensity,globalImmersionPartitionCutoff,chartCutoff,ite_eq_right hx,zero_mul]
    simp only [hz,zero_mul]

theorem integral_partitionChartMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (g : M → ℝ) (hg : Continuous g) :
    (∫ y : M, g y ∂partitionChartMeasure F P i) =
      ∫ x : Chart4, partitionVolumeDensity F P i x * g ((chartAt Chart4 (P.center i)).symm x) :=
  integral_partitionChartMeasure_of_aestronglyMeasurable F P i g hg.aestronglyMeasurable

theorem integrable_partitionVolumeMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (g : M → ℝ) (hg : Continuous g) : Integrable g (partitionVolumeMeasure F P) := by
  have := isFiniteMeasure_partitionVolumeMeasure F P
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

/-- The measure integral is precisely the finite coordinate partition formula.
This equality uses the measurable total inverse only where the density is nonzero. -/
theorem integral_partitionVolumeMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (g : M → ℝ) (hg : Continuous g) :
    (∫ y : M, g y ∂partitionVolumeMeasure F P) =
      ∑ i ∈ P.finite_index.elems, ∫ x : Chart4,
        partitionVolumeDensity F P i x * g ((chartAt Chart4 (P.center i)).symm x) := by
  unfold partitionVolumeMeasure
  rw [integral_finsetSum_measure (fun i _ => integrable_partitionChartMeasure F P i g hg)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_partitionChartMeasure F P i g hg

theorem integral_partitionProbabilityMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (g : M → ℝ) (hg : Continuous g) :
    (∫ y : M, g y ∂partitionProbabilityMeasure F P) =
      (partitionVolumeMeasure F P Set.univ).toReal⁻¹ *
        ∑ i ∈ P.finite_index.elems, ∫ x : Chart4,
          partitionVolumeDensity F P i x * g ((chartAt Chart4 (P.center i)).symm x) := by
  rw [partitionProbabilityMeasure,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,
    integral_partitionVolumeMeasure F P g hg]

end
end SecondPinching
