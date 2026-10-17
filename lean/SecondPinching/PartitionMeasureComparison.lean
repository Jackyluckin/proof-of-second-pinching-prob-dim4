import SecondPinching.PartitionVolumeIntegral
import SecondPinching.ChartIntegralTransport

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem immersionPartition_sum_weights (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (x : M) :
    (∑ i ∈ P.finite_index.elems, P.weights i x)=1 := by
  let _ := P.finite_index
  have he := P.weights.sum_eq_one (mem_univ x)
  rw [finsum_eq_sum_of_fintype] at he
  exact he

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem immersionPartition_weight_mul_bound (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (g : M → ℝ) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) (x : M) :
    ‖P.weights i x*g x‖ ≤ C := by
  calc
    _ = P.weights i x * ‖g x‖ := by rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (P.weights.nonneg i x)]
    _ ≤ 1*‖g x‖ := mul_le_mul_of_nonneg_right (P.weights.le_one i x) (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hC x

omit [CompactSpace M] in
theorem integrable_partition_weight_mul (ν : Measure M) [IsFiniteMeasure ν]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index)
    (g : M → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => P.weights i x*g x) ν :=
  Integrable.of_bound (((P.weights i).contMDiff.continuous.measurable).mul hg).aestronglyMeasurable C
    (Filter.Eventually.of_forall (immersionPartition_weight_mul_bound F P i g C hC))

omit [CompactSpace M] in
theorem integral_partition_decomposition (ν : Measure M) [IsFiniteMeasure ν]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (g : M → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) :
    (∫ x, g x ∂ν)=∑ i ∈ P.finite_index.elems, ∫ x, P.weights i x*g x ∂ν := by
  calc
    _ = ∫ x, (∑ i ∈ P.finite_index.elems, P.weights i x)*g x ∂ν := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change g x=(∑ i ∈ P.finite_index.elems, P.weights i x)*g x
      rw [immersionPartition_sum_weights F P x,one_mul]
    _ = ∫ x, ∑ i ∈ P.finite_index.elems, P.weights i x*g x ∂ν := by simp only [Finset.sum_mul]
    _ = _ := integral_finsetSum _ (fun i _ => integrable_partition_weight_mul ν F P i g hg C hC)

theorem integral_partition_measure_sum (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (g : M → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) :
    (∫ x, g x ∂partitionVolumeMeasure F P)=
      ∑ i ∈ P.finite_index.elems, ∫ x, g x ∂partitionChartMeasure F P i := by
  unfold partitionVolumeMeasure
  apply integral_finsetSum_measure
  intro i _
  have := isFiniteMeasure_partitionChartMeasure F P i
  exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem integral_partitionChartMeasure_cutoff (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (g : M → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂partitionChartMeasure F P i)=
      ∫ x : Chart4, immersionVolumeDensity (globalImmersionLocal F (P.center i)) x *
        chartCutoff (P.center i) (fun y => P.weights i y*g y) x := by
  rw [integral_partitionChartMeasure_of_aestronglyMeasurable F P i g hg.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change partitionVolumeDensity F P i x * g ((chartAt Chart4 (P.center i)).symm x) =
    immersionVolumeDensity (globalImmersionLocal F (P.center i)) x *
      chartCutoff (P.center i) (fun y => P.weights i y*g y) x
  rw [chartCutoff_mul_right]
  change (chartCutoff (P.center i) (P.weights i) x *
    immersionVolumeDensity (globalImmersionLocal F (P.center i)) x)*g ((chartAt Chart4 (P.center i)).symm x) = _
  ring

/-- A term weighted by two partitions may be integrated in either of their
coordinate charts. The support lies in their genuine overlap. -/
theorem partitionChartMeasure_pair_balance (F : GlobalSphereImmersion M) (P Q : ImmersionPartition F)
    (i : P.index) (j : Q.index) (g : M → ℝ) (hg : Measurable g) :
    (∫ x, Q.weights j x*g x ∂partitionChartMeasure F P i)=
      ∫ x, P.weights i x*g x ∂partitionChartMeasure F Q j := by
  erw [integral_partitionChartMeasure_cutoff F P i (fun x => Q.weights j x*g x)
      ((Q.weights j).contMDiff.continuous.measurable.mul hg),
    integral_partitionChartMeasure_cutoff F Q j (fun x => P.weights i x*g x)
      ((P.weights i).contMDiff.continuous.measurable.mul hg)]
  have he : (fun x => Q.weights j x*(P.weights i x*g x)) =
      (fun x => P.weights i x*(Q.weights j x*g x)) := by funext x; ring
  rw [he]
  apply integral_chartCutoff_change
  · exact tsupport_mul_subset_left.trans (P.subordinate i)
  · exact tsupport_mul_subset_right.trans (tsupport_mul_subset_left.trans (Q.subordinate j))

theorem integral_partitionVolumeMeasure_independent (F : GlobalSphereImmersion M)
    (P Q : ImmersionPartition F) (g : M → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) :
    (∫ x, g x ∂partitionVolumeMeasure F P)=(∫ x, g x ∂partitionVolumeMeasure F Q) := by
  have := isFiniteMeasure_partitionVolumeMeasure F P
  have (j : Q.index) := isFiniteMeasure_partitionChartMeasure F Q j
  calc
    _ = ∑ j ∈ Q.finite_index.elems, ∫ x, Q.weights j x*g x ∂partitionVolumeMeasure F P :=
      integral_partition_decomposition _ F Q g hg C hC
    _ = ∑ j ∈ Q.finite_index.elems, ∑ i ∈ P.finite_index.elems,
        ∫ x, Q.weights j x*g x ∂partitionChartMeasure F P i := by
      apply Finset.sum_congr rfl; intro j _
      exact integral_partition_measure_sum F P _ ((Q.weights j).contMDiff.continuous.measurable.mul hg) C
        (immersionPartition_weight_mul_bound F Q j g C hC)
    _ = ∑ j ∈ Q.finite_index.elems, ∑ i ∈ P.finite_index.elems,
        ∫ x, P.weights i x*g x ∂partitionChartMeasure F Q j := by
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _
      exact partitionChartMeasure_pair_balance F P Q i j g hg
    _ = ∑ j ∈ Q.finite_index.elems, ∫ x, g x ∂partitionChartMeasure F Q j := by
      apply Finset.sum_congr rfl; intro j _
      exact (integral_partition_decomposition _ F P g hg C hC).symm
    _ = _ := (integral_partition_measure_sum F Q g hg C hC).symm

/-- Equality on bounded measurable test functions proves equality of the
finite measures, so the construction is independent of the partition. -/
theorem partitionVolumeMeasure_independent (F : GlobalSphereImmersion M) (P Q : ImmersionPartition F) :
    partitionVolumeMeasure F P=partitionVolumeMeasure F Q := by
  have := isFiniteMeasure_partitionVolumeMeasure F P
  have := isFiniteMeasure_partitionVolumeMeasure F Q
  apply Measure.ext
  intro s hs
  have hi := integral_partitionVolumeMeasure_independent F P Q (s.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hs) 1 (fun x => by by_cases hx : x ∈ s <;> simp [Set.indicator,hx])
  erw [integral_indicator_one hs,integral_indicator_one hs] at hi
  have he := congrArg ENNReal.ofReal hi
  change ENNReal.ofReal ((partitionVolumeMeasure F P s).toReal)=
    ENNReal.ofReal ((partitionVolumeMeasure F Q s).toReal) at he
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he

end
end SecondPinching
