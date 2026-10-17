import SecondPinching.GlobalDivergencePotentials
import SecondPinching.GlobalImmersionPartition

set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

def scalarInImmersionChart (p : M) (u : M → ℝ) : Chart4 → ℝ := u ∘ (chartAt Chart4 p).symm

theorem scalarInImmersionChart_smooth (F : GlobalSphereImmersion M) (p : M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) :
    ContDiffOn ℝ ∞ (scalarInImmersionChart p u) (globalImmersionLocal F p).domain :=
  (hu.comp_contMDiffOn (contMDiffOn_chart_symm (I:=𝓘(ℝ,Chart4)) (x:=p))).contDiffOn.mono
    (globalImmersionLocal_domain_subset F p)

theorem scalarInImmersionChart_transition_germ (F : GlobalSphereImmersion M) (p q : M)
    (u : M → ℝ) (x : Chart4) (hx : x ∈ (globalImmersionReparametrization F p q).domain) :
    scalarInImmersionChart q u =ᶠ[𝓝 x]
      scalarInImmersionChart p u ∘ (globalImmersionReparametrization F p q).map := by
  apply Filter.eventuallyEq_of_mem ((globalImmersionReparametrization F p q).isOpen_domain.mem_nhds hx)
  intro y hy
  change u ((chartAt Chart4 q).symm y)=
    u ((chartAt Chart4 p).symm ((chartAt Chart4 p) ((chartAt Chart4 q).symm y)))
  have he : (chartAt Chart4 p).symm ((chartAt Chart4 p) ((chartAt Chart4 q).symm y)) =
      (chartAt Chart4 q).symm y := (chartAt Chart4 p).left_inv hy.1.2
  exact (congrArg u he).symm

/-- Smooth contravariant vector components in the constructed atlas, with
the usual tangent-vector transition law. No divergence or integral is a field. -/
structure ImmersionCoordinateVector (F : GlobalSphereImmersion M) where
  components : M → Chart4 → Vector4
  smooth : ∀ p, ContDiffOn ℝ ∞ (components p) (globalImmersionLocal F p).domain
  transition : ∀ p q x, x ∈ globalImmersionLocalSource F p → x ∈ globalImmersionLocalSource F q →
    components p (chartAt Chart4 p x)=
      fderiv ℝ (globalImmersionReparametrization F p q).map (chartAt Chart4 q x)
        (components q (chartAt Chart4 q x))

def globalVectorAction (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) (x : M) : ℝ :=
  fderiv ℝ (scalarInImmersionChart x u) (chartAt Chart4 x x) (Y.components x (chartAt Chart4 x x))

theorem coordinateVectorAction_compatibility (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) (p q x : M)
    (hp : x ∈ globalImmersionLocalSource F p) (hq : x ∈ globalImmersionLocalSource F q) :
    fderiv ℝ (scalarInImmersionChart p u) (chartAt Chart4 p x) (Y.components p (chartAt Chart4 p x)) =
      fderiv ℝ (scalarInImmersionChart q u) (chartAt Chart4 q x) (Y.components q (chartAt Chart4 q x)) := by
  let P := globalImmersionReparametrization F p q
  obtain ⟨hx,he⟩ := globalImmersionReparametrization_point F p q x hp hq
  have huP := (((scalarInImmersionChart_smooth F p u hu) _ (P.mapsTo hx)).contDiffAt
    ((globalImmersionLocal F p).isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
  have hP := ((P.smooth_map _ hx).contDiffAt (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hg := scalarInImmersionChart_transition_germ F p q u (chartAt Chart4 q x) hx
  rw [hg.fderiv_eq,fderiv_comp _ huP hP]
  change _ = fderiv ℝ (scalarInImmersionChart p u) (P.map (chartAt Chart4 q x))
    (fderiv ℝ P.map (chartAt Chart4 q x) (Y.components q (chartAt Chart4 q x)))
  rw [he,← Y.transition p q x hp hq]

theorem globalVectorAction_represent (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) (p x : M)
    (hx : x ∈ globalImmersionLocalSource F p) :
    globalVectorAction F Y u x =
      fderiv ℝ (scalarInImmersionChart p u) (chartAt Chart4 p x) (Y.components p (chartAt Chart4 p x)) :=
  coordinateVectorAction_compatibility F Y u hu x p x (globalImmersionLocalSource_center F x) hx

theorem contDiffOn_coordinateVectorAction (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) (p : M) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ (scalarInImmersionChart p u) x (Y.components p x))
      (globalImmersionLocal F p).domain :=
  ((scalarInImmersionChart_smooth F p u hu).fderiv_of_isOpen (globalImmersionLocal F p).isOpen_domain
    (m:=∞) (by simp)).clm_apply (Y.smooth p)

theorem contMDiff_globalVectorAction (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ u) :
    ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ (globalVectorAction F Y u) :=
  contMDiff_of_immersion_local_representation F _ _ (contDiffOn_coordinateVectorAction F Y u hu)
    (globalVectorAction_represent F Y u hu)

theorem globalVectorAction_eq_zero_off_tsupport (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) (x : M) (hx : x ∉ tsupport u) : globalVectorAction F Y u x=0 := by
  have hi : Filter.Tendsto (chartAt Chart4 x).symm (𝓝 (chartAt Chart4 x x)) (𝓝 x) := by
    have h := ((chartAt Chart4 x).symm.continuousAt (mem_chart_target Chart4 x)).tendsto
    simpa only [(chartAt Chart4 x).left_inv (mem_chart_source Chart4 x)] using h
  have hz : scalarInImmersionChart x u =ᶠ[𝓝 (chartAt Chart4 x x)] fun _ => (0 : ℝ) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hi
  unfold globalVectorAction
  rw [hz.fderiv_eq]
  simp

theorem tsupport_globalVectorAction_subset (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (u : M → ℝ) : tsupport (globalVectorAction F Y u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  exact hx (globalVectorAction_eq_zero_off_tsupport F Y u x hn)

theorem globalVectorAction_partition_sum (F : GlobalSphereImmersion M) (Y : ImmersionCoordinateVector F)
    (P : ImmersionPartition F) (x : M) :
    (∑ i ∈ P.finite_index.elems, globalVectorAction F Y (P.weights i) x)=0 := by
  let _ := P.finite_index
  have hs : (fun y : Chart4 => ∑ i, scalarInImmersionChart x (P.weights i) y) = fun _ => (1 : ℝ) := by
    funext y
    have he := P.weights.sum_eq_one (mem_univ ((chartAt Chart4 x).symm y))
    rw [finsum_eq_sum_of_fintype] at he
    exact he
  have hi (i : P.index) : DifferentiableAt ℝ (scalarInImmersionChart x (P.weights i)) (chartAt Chart4 x x) :=
    (((scalarInImmersionChart_smooth F x _ (P.weights i).contMDiff) _ (globalImmersionLocal_center F x)).contDiffAt
      ((globalImmersionLocal F x).isOpen_domain.mem_nhds (globalImmersionLocal_center F x))).differentiableAt (by simp)
  have hd := congrArg (fun f : Chart4 → ℝ =>
    fderiv ℝ f (chartAt Chart4 x x) (Y.components x (chartAt Chart4 x x))) hs
  rw [fderiv_fun_sum (u:=Finset.univ) (fun i _ => hi i)] at hd
  simp only [sum_apply,fderiv_const_apply,zero_apply] at hd
  exact hd

end
end SecondPinching
