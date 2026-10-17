import SecondPinching.PartitionVolumeDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]

/-- A measurable total inverse chart. Its arbitrary value outside the target
is multiplied by a density that vanishes there. -/
def totalChartInverse (p : M) (x : Chart4) : M := by
  classical
  exact if x ∈ (chartAt Chart4 p).target then (chartAt Chart4 p).symm x else p

theorem totalChartInverse_on_target (p : M) (x : Chart4)
    (hx : x ∈ (chartAt Chart4 p).target) : totalChartInverse p x=(chartAt Chart4 p).symm x := by
  simp only [totalChartInverse,ite_eq_left hx]

variable [MeasurableSpace M] [BorelSpace M]

theorem measurable_totalChartInverse (p : M) : Measurable (totalChartInverse p) := by
  classical
  exact (chartAt Chart4 p).continuousOn_symm.measurable_piecewise continuousOn_const
    (chartAt Chart4 p).open_target.measurableSet

variable [IsManifold 𝓘(ℝ,Chart4) ∞ M]

def partitionChartMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) : Measure M :=
  Measure.map (totalChartInverse (P.center i))
    (volume.withDensity (fun x => ENNReal.ofReal (partitionVolumeDensity F P i x)))

/-- The usual finite partition formula for volume. Independence from the
partition and its local coordinate characterization are proved separately. -/
def partitionVolumeMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F) : Measure M := by
  classical
  let _ := P.finite_index
  exact ∑ i, partitionChartMeasure F P i

theorem partitionChartMeasure_univ [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    partitionChartMeasure F P i Set.univ=ENNReal.ofReal (∫ x : Chart4, partitionVolumeDensity F P i x) := by
  unfold partitionChartMeasure
  rw [Measure.map_apply (measurable_totalChartInverse _) MeasurableSet.univ,Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_partitionVolumeDensity F P i)
    (Filter.Eventually.of_forall (partitionVolumeDensity_nonneg F P i))).symm

theorem isFiniteMeasure_partitionChartMeasure [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    IsFiniteMeasure (partitionChartMeasure F P i) := by
  constructor
  rw [partitionChartMeasure_univ]
  exact ENNReal.ofReal_lt_top

theorem isFiniteMeasure_partitionVolumeMeasure [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) :
    IsFiniteMeasure (partitionVolumeMeasure F P) := by
  let _ := P.finite_index
  have (i : P.index) : IsFiniteMeasure (partitionChartMeasure F P i) :=
    isFiniteMeasure_partitionChartMeasure F P i
  unfold partitionVolumeMeasure
  infer_instance

theorem partitionVolumeMeasure_univ_pos [CompactSpace M] [Nonempty M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) :
    0 < partitionVolumeMeasure F P Set.univ := by
  let _ := P.finite_index
  obtain ⟨i,hi⟩ := partitionVolumeDensity_exists_positive_integral F P
  have hp : 0 < partitionChartMeasure F P i Set.univ := by
    rw [partitionChartMeasure_univ]
    exact ENNReal.ofReal_pos.mpr hi
  have hle : partitionChartMeasure F P i ≤ partitionVolumeMeasure F P := by
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hp.trans_le ((Measure.le_iff'.mp hle) Set.univ)

def partitionProbabilityMeasure (F : GlobalSphereImmersion M) (P : ImmersionPartition F) : Measure M :=
  (partitionVolumeMeasure F P Set.univ)⁻¹ • partitionVolumeMeasure F P

theorem isProbabilityMeasure_partitionProbabilityMeasure [CompactSpace M] [Nonempty M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) :
    IsProbabilityMeasure (partitionProbabilityMeasure F P) := by
  have := isFiniteMeasure_partitionVolumeMeasure F P
  constructor
  change ((partitionVolumeMeasure F P Set.univ)⁻¹ • partitionVolumeMeasure F P) Set.univ=1
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (partitionVolumeMeasure_univ_pos F P).ne' (measure_ne_top _ _)

end
end SecondPinching
