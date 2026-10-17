import SecondPinching.ChartCutoff
import SecondPinching.ImmersionVolumeDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- Nonnegative coordinate density for one term of the partition formula
for induced volume. It has compact support in the actual immersion domain. -/
def partitionVolumeDensity (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (x : Chart4) : ℝ :=
  globalImmersionPartitionCutoff F P i x * immersionVolumeDensity (globalImmersionLocal F (P.center i)) x

theorem partitionVolumeDensity_nonneg (F : GlobalSphereImmersion M) (P : ImmersionPartition F)
    (i : P.index) (x : Chart4) : 0 ≤ partitionVolumeDensity F P i x := by
  have hc : 0 ≤ globalImmersionPartitionCutoff F P i x := by
    unfold globalImmersionPartitionCutoff chartCutoff
    split_ifs
    · exact P.weights.nonneg i _
    · exact le_refl _
  exact mul_nonneg hc (Real.sqrt_nonneg _)

theorem hasCompactSupport_partitionVolumeDensity [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    HasCompactSupport (partitionVolumeDensity F P i) := by
  apply (globalImmersionPartitionCutoff_compact F P i).mono'
  intro x hx
  by_contra hn
  exact hx (by simp only [partitionVolumeDensity,image_eq_zero_of_notMem_tsupport hn,zero_mul])

theorem contDiff_partitionVolumeDensity [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    ContDiff ℝ ∞ (partitionVolumeDensity F P i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (globalImmersionPartitionCutoff F P i)
  · have hu := globalImmersionPartitionCutoff_support F P i hx
    exact (globalImmersionPartitionCutoff_smooth F P i).contDiffAt.mul
      (((contDiffOn_immersionVolumeDensity _) x hu).contDiffAt
        ((globalImmersionLocal F (P.center i)).isOpen_domain.mem_nhds hu))
  · have he : partitionVolumeDensity F P i =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).mono
        (fun y hy => by simp only [partitionVolumeDensity,hy,Pi.zero_apply,zero_mul])
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem integrable_partitionVolumeDensity [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    Integrable (partitionVolumeDensity F P i) :=
  (contDiff_partitionVolumeDensity F P i).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_partitionVolumeDensity F P i)

theorem partitionVolumeDensity_integral_nonneg [CompactSpace M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) (i : P.index) :
    0 ≤ ∫ x : Chart4, partitionVolumeDensity F P i x :=
  integral_nonneg (partitionVolumeDensity_nonneg F P i)

theorem immersionPartition_exists_positive_weight (F : GlobalSphereImmersion M)
    (P : ImmersionPartition F) (x : M) : ∃ i, 0 < P.weights i x := by
  by_contra! h
  have hz (i : P.index) : P.weights i x=0 := le_antisymm (h i) (P.weights.nonneg i x)
  have hs := P.weights.sum_eq_one (Set.mem_univ x)
  simp_rw [hz] at hs
  norm_num at hs

theorem partitionVolumeDensity_exists_positive [CompactSpace M] [Nonempty M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) :
    ∃ i, ∃ x : Chart4, 0 < partitionVolumeDensity F P i x := by
  let x : M := Classical.choice inferInstance
  obtain ⟨i,hi⟩ := immersionPartition_exists_positive_weight F P x
  have ht : x ∈ tsupport (P.weights i : M → ℝ) := subset_closure hi.ne'
  have hx := P.subordinate i ht
  refine ⟨i,chartAt Chart4 (P.center i) x,?_⟩
  have hc : globalImmersionPartitionCutoff F P i (chartAt Chart4 (P.center i) x)=P.weights i x :=
    chartCutoff_on_source _ _ _ hx.1
  change 0 < globalImmersionPartitionCutoff F P i (chartAt Chart4 (P.center i) x) * _
  rw [hc]
  exact mul_pos hi (immersionVolumeDensity_pos _ _ hx.2)

theorem partitionVolumeDensity_exists_positive_integral [CompactSpace M] [Nonempty M]
    (F : GlobalSphereImmersion M) (P : ImmersionPartition F) :
    ∃ i, 0 < ∫ x : Chart4, partitionVolumeDensity F P i x := by
  obtain ⟨i,x,hx⟩ := partitionVolumeDensity_exists_positive F P
  exact ⟨i,integral_pos_of_integrable_nonneg_nonzero
    (contDiff_partitionVolumeDensity F P i).continuous (integrable_partitionVolumeDensity F P i)
    (partitionVolumeDensity_nonneg F P i) hx.ne'⟩

end
end SecondPinching
