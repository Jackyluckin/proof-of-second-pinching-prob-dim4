import SecondPinching.GlobalImmersionAtlas
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
open scoped Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- A finite smooth partition subordinate to the constructed local immersion
domains. This structure includes no integration or volume assertion. -/
structure ImmersionPartition (F : GlobalSphereImmersion M) where
  index : Type u
  finite_index : Fintype index
  center : index → M
  weights : SmoothPartitionOfUnity index 𝓘(ℝ,Chart4) M Set.univ
  subordinate : weights.IsSubordinate (fun i => globalImmersionLocalSource F (center i))

theorem exists_immersionPartition [T2Space M] [CompactSpace M] (F : GlobalSphereImmersion M) :
    Nonempty (ImmersionPartition F) := by
  obtain ⟨ι,fs,hfs⟩ := SmoothBumpCovering.exists_isSubordinate 𝓘(ℝ,Chart4) isClosed_univ
    (fun p _ => (isOpen_globalImmersionLocalSource F p).mem_nhds (globalImmersionLocalSource_center F p))
  exact ⟨⟨ι,fs.fintype,fs.c,fs.toSmoothPartitionOfUnity,hfs.toSmoothPartitionOfUnity⟩⟩

def constructedImmersionPartition [T2Space M] [CompactSpace M] (F : GlobalSphereImmersion M) :
    ImmersionPartition F := Classical.choice (exists_immersionPartition F)

end
end SecondPinching
