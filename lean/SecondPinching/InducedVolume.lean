import SecondPinching.PartitionMeasureComparison
import SecondPinching.AdaptedImmersionPartition

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- In a single chart the constructed measure has the actual density
sqrt(det g). The test function's support is contained in that local domain. -/
theorem integral_partitionVolumeMeasure_local (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (p : M) (g : M → ℝ) (hg : Continuous g) (hs : tsupport g ⊆ globalImmersionLocalSource F p) :
    (∫ y, g y ∂partitionVolumeMeasure F P)=
      ∫ x : Chart4, immersionVolumeDensity (globalImmersionLocal F p) x * chartCutoff p g x := by
  obtain ⟨Q,i,hcenter,hone,hzero⟩ := exists_immersionPartition_one_on F p (tsupport g) (isClosed_tsupport g) hs
  let _ := Q.finite_index
  have hz (j : Q.index) (hj : j≠i) : (fun y => Q.weights j y*g y)=(fun _ => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ tsupport g
    · rw [hzero j hj y hy,zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy,mul_zero]
  have ho : (fun y => Q.weights i y*g y)=g := by
    funext y
    by_cases hy : y ∈ tsupport g
    · rw [hone y hy,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy,mul_zero]
  calc
    _ = ∫ y, g y ∂partitionVolumeMeasure F Q := by rw [partitionVolumeMeasure_independent F P Q]
    _ = ∑ j ∈ Q.finite_index.elems, ∫ y, g y ∂partitionChartMeasure F Q j := by
      unfold partitionVolumeMeasure
      exact integral_finsetSum_measure (fun j _ => integrable_partitionChartMeasure F Q j g hg)
    _ = ∫ y, g y ∂partitionChartMeasure F Q i := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [integral_partitionChartMeasure_cutoff F Q j g hg.measurable,hz j hj]
        simp only [chartCutoff,ite_self,mul_zero,integral_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    _ = _ := by
      rw [integral_partitionChartMeasure_cutoff F Q i g hg.measurable,ho,hcenter]

/-- The induced volume measure, constructed from the actual coordinate
metrics. The preceding comparison proves that the partition choice is immaterial. -/
def inducedVolume (F : GlobalSphereImmersion M) : Measure M :=
  partitionVolumeMeasure F (constructedImmersionPartition F)

theorem inducedVolume_eq_partition (F : GlobalSphereImmersion M) (P : ImmersionPartition F) :
    inducedVolume F=partitionVolumeMeasure F P :=
  partitionVolumeMeasure_independent F _ P

theorem isFiniteMeasure_inducedVolume (F : GlobalSphereImmersion M) : IsFiniteMeasure (inducedVolume F) :=
  isFiniteMeasure_partitionVolumeMeasure F _

theorem inducedVolume_univ_pos [Nonempty M] (F : GlobalSphereImmersion M) : 0 < inducedVolume F univ :=
  partitionVolumeMeasure_univ_pos F _

theorem integral_inducedVolume_local (F : GlobalSphereImmersion M) (p : M) (g : M → ℝ)
    (hg : Continuous g) (hs : tsupport g ⊆ globalImmersionLocalSource F p) :
    (∫ y, g y ∂inducedVolume F)=
      ∫ x : Chart4, immersionVolumeDensity (globalImmersionLocal F p) x * chartCutoff p g x :=
  integral_partitionVolumeMeasure_local F _ p g hg hs

def normalizedInducedVolume (F : GlobalSphereImmersion M) : Measure M :=
  (inducedVolume F univ)⁻¹ • inducedVolume F

theorem isProbabilityMeasure_normalizedInducedVolume [Nonempty M] (F : GlobalSphereImmersion M) :
    IsProbabilityMeasure (normalizedInducedVolume F) :=
  isProbabilityMeasure_partitionProbabilityMeasure F _

omit [BorelSpace M] in
theorem integral_normalizedInducedVolume (F : GlobalSphereImmersion M) (g : M → ℝ) :
    (∫ y, g y ∂normalizedInducedVolume F)=
      (inducedVolume F univ).toReal⁻¹ * ∫ y, g y ∂inducedVolume F := by
  rw [normalizedInducedVolume,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]

end
end SecondPinching
