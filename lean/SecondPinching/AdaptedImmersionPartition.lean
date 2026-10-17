import SecondPinching.PartitionVolumeDensity

set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
open scoped BigOperators Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M] [T2Space M] [CompactSpace M]

/-- A closed set contained in one local domain admits a finite subordinate
partition with one weight equal to one on it and all other weights zero there. -/
theorem exists_immersionPartition_one_on (F : GlobalSphereImmersion M) (p : M)
    (K : Set M) (hK : IsClosed K) (hKU : K ⊆ globalImmersionLocalSource F p) :
    ∃ Q : ImmersionPartition F, ∃ i : Q.index,
      Q.center i=p ∧ (∀ x ∈ K, Q.weights i x=1) ∧
        ∀ j, j≠i → ∀ x ∈ K, Q.weights j x=0 := by
  classical
  let P := constructedImmersionPartition F
  let _ := P.finite_index
  let U : Option P.index → Set M := fun i => match i with
    | none => globalImmersionLocalSource F p
    | some j => globalImmersionLocalSource F (P.center j) ∩ Kᶜ
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none => exact isOpen_globalImmersionLocalSource F p
    | some j => exact (isOpen_globalImmersionLocalSource F (P.center j)).inter hK.isOpen_compl
  have hcover : univ ⊆ ⋃ i, U i := by
    intro x _
    by_cases hx : x ∈ K
    · exact mem_iUnion.mpr ⟨none,hKU hx⟩
    · obtain ⟨i,hi⟩ := immersionPartition_exists_positive_weight F P x
      exact mem_iUnion.mpr ⟨some i,⟨P.subordinate i (subset_closure hi.ne'),hx⟩⟩
  obtain ⟨w,hw⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Chart4) isClosed_univ U hU hcover
  let c : Option P.index → M := fun i => match i with
    | none => p
    | some j => P.center j
  have hsub : w.IsSubordinate (fun i => globalImmersionLocalSource F (c i)) := by
    intro i x hx
    cases i with
    | none => exact hw none hx
    | some j => exact (hw (some j) hx).1
  let Q : ImmersionPartition F := ⟨Option P.index,inferInstance,c,w,hsub⟩
  have hz (j : P.index) (x : M) (hx : x ∈ K) : w (some j) x=0 := by
    by_contra hn
    exact (hw (some j) (subset_closure hn)).2 hx
  have ho (x : M) (hx : x ∈ K) : w none x=1 := by
    have he := w.sum_eq_one (mem_univ x)
    simpa only [finsum_eq_sum_of_fintype,Fintype.sum_option,hz _ x hx,
      Finset.sum_const_zero,add_zero,zero_add] using he
  refine ⟨Q,none,rfl,ho,?_⟩
  intro j hj x hx
  cases j with
  | none => exact (hj rfl).elim
  | some j => exact hz j x hx

end
end SecondPinching
